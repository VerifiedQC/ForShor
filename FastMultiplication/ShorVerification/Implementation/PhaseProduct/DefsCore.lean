import FastMultiplication.ShorVerification.Framework.AbstractMachine.Gates
import FastMultiplication.ShorVerification.Framework.AbstractMachine.LowGate
import FastMultiplication.ShorVerification.Framework.Semantics.GateSemantics
import FastMultiplication.ShorVerification.Framework.Semantics.LowerGate
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Toom_Cook_formula
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Core.Coverage
import Mathlib.Tactic

/-!
# Phase-Product Public Definitions

This file owns the definition-level API for the phase-product implementation.
It intentionally imports no module from `PhaseProduct.Proofs`; proof-only files
import this module instead.
-/




/-!
# Generic basis-clean linear closure (implementation proof-support)

`CleanClosure P` is the linear subspace spanned by basis kets satisfying a
per-basis cleanliness predicate `P`.  It is used only inside the lowering /
correctness proofs, so it lives on the implementation side.
-/

namespace Shor


/-- The set of states reachable from `P`-clean basis kets by `+` and `•`:
    a `zero/ket/add/smul` linear closure parameterized by the per-basis
    predicate `P`. -/
inductive CleanClosure {qs : QSemantics} [RegEncoding qs.Basis]
    (P : qs.Basis → Prop) : qs.State → Prop
  | zero : CleanClosure P 0
  | ket (b : qs.Basis) (h : P b) : CleanClosure P (qs.ket b)
  | add {ψ φ : qs.State} (hψ : CleanClosure P ψ) (hφ : CleanClosure P φ) :
      CleanClosure P (ψ + φ)
  | smul (a : ℂ) {ψ : qs.State} (hψ : CleanClosure P ψ) :
      CleanClosure P (a • ψ)

end Shor




/-!
# Phase-Product Compiler Core
This file contains the definition-level core of the recursive phase-product compiler.
It is grouped by role: chunk layouts, width scans, interpolation data, compiler
syntax, semantic invariants, and the concrete register-splitting construction that
realizes the abstract layouts. The lower `LowGate` target syntax lives elsewhere;
this module describes the higher-level gates and proofs they need.
-/

namespace Shor
open Gate
open Operations
open scoped BigOperators

/-! =========================================================
    Section 1: Layout states and width bookkeeping
========================================================= -/

/-- Current chunk-to-register assignment for the paired `x` and `z` work arrays. -/
structure LayoutState (k : ℕ) where
  xslot : Fin k → ExtReg
  zslot : Fin k → ExtReg

/-- Every slot has enough reserve to grow to common target width `W`. -/
def LayoutState.CanGrowTo {k : ℕ} (st : LayoutState k) (W : ℕ) : Prop :=
  (∀ i, (st.xslot i).CanGrow (W - (st.xslot i).width)) ∧ (∀ i, (st.zslot i).CanGrow (W - (st.zslot i).width))

/-- All owned qubits in the layout are pairwise separated across `x`, `z`, and cross slots. -/
def LayoutState.OwnedPairwiseDisjoint {k : ℕ} (st : LayoutState k) : Prop :=
  (∀ i j, i ≠ j → ExtReg.OwnedDisjoint (st.xslot i) (st.xslot j)) ∧
  (∀ i j, i ≠ j → ExtReg.OwnedDisjoint (st.zslot i) (st.zslot j)) ∧
  (∀ i j, ExtReg.OwnedDisjoint (st.xslot i) (st.zslot j))

/-- Width bookkeeping only: current logical widths of each chunk. -/
structure WidthState (k : ℕ) where
  xw : Fin k → ℕ
  zw : Fin k → ℕ

/-- Symbolic width transition for one source operation. -/
def updateWidthState {k : ℕ} (st : WidthState k) : valid_ops k → WidthState k
  | .shiftL i n =>
      { xw := Function.update st.xw i (st.xw i + n)
        zw := Function.update st.zw i (st.zw i + n) }
  | .shiftR i n =>
      { xw := Function.update st.xw i (st.xw i - n)
        zw := Function.update st.zw i (st.zw i - n) }
  | .negate i =>
      { xw := Function.update st.xw i (st.xw i + 1)
        zw := Function.update st.zw i (st.zw i + 1) }
  | .addScaled dst src _negsrc sh =>
      let newX := 1 + max (st.xw dst) (st.xw src + sh)
      let newZ := 1 + max (st.zw dst) (st.zw src + sh)
      { xw := Function.update st.xw dst newX
        zw := Function.update st.zw dst newZ }
  | .phaseProduct _ =>
      st

/-- Per-slot maximum widths discovered by scanning the source program. -/
structure NeededWidths (k : ℕ) where
  xneed : Fin k → ℕ
  zneed : Fin k → ℕ

/-- Pointwise maximum of two width-demand records. -/
def mergeNeededWidths {k : ℕ} (a b : NeededWidths k) : NeededWidths k where
  xneed := fun i => max (a.xneed i) (b.xneed i)
  zneed := fun i => max (a.zneed i) (b.zneed i)

/-- Regard current widths as the current lower bound on needed widths. -/
def widthsOfState {k : ℕ} (st : WidthState k) : NeededWidths k where
  xneed := st.xw
  zneed := st.zw

/--
Lower-limb width for the top-heavy phase layout.
This deliberately uses floor division. The lower `k - 1` limbs have width `w / k`,
and the most significant limb absorbs all remaining bits.
For example, `w = 5`, `k = 4` gives widths `1, 1, 1, 2`.
-/

def phaseLimbWidthOfWidth (w k : ℕ) : ℕ := w / k

/--
Common radix width for decomposing both operands.
Use `min`, not `max`: the lower limbs must fit inside both operands.
The larger operand simply gets a larger top chunk.
-/

def phaseLimbWidth (x z : ExtReg) (k : ℕ) : ℕ :=
  min (phaseLimbWidthOfWidth x.width k) (phaseLimbWidthOfWidth z.width k)

/-! =========================================================
    Section 2: Top-heavy phase splitting parameters
========================================================= -/

/-- The most significant chunk is the last chunk. -/
def isTopChunk {k : ℕ} (i : Fin k) : Prop := i.1 + 1 = k
instance {k : ℕ} (i : Fin k) : Decidable (isTopChunk i) := by
  unfold isTopChunk
  infer_instance

/-- Logical width of chunk `i`; the last chunk absorbs the remainder. -/
def phaseSplitLogicalWidth (w W k : ℕ) (i : Fin k) : ℕ := if isTopChunk i then w - i.1 * W else W

/-- Starting bit offset of chunk `i` in the parent active register. -/
def phaseChunkStart {k : ℕ} (W : ℕ) (i : Fin k) : ℕ := i.1 * W

/-- Concrete active register slice corresponding to chunk `i`. -/
def phaseChunkActive (e : ExtReg) (k W : ℕ) (i : Fin k) : Reg :=
  (e.active.drop (phaseChunkStart W i)).take (phaseSplitLogicalWidth e.width W k i)

/-! =========================================================
    Section 3: Abstract `ExtReg` split interface
========================================================= -/

/-- Validity conditions for the top-heavy split of `parent` into `k` chunks of lower width `W`. -/
def ValidPhaseSplit (e : ExtReg) (k W : ℕ) : Prop :=
  0 < k ∧ (k - 1) * W ≤ e.width ∧ (e.width = 0 ∨ (k - 1) * W < e.width)

/-- Abstract split of one extendable register into active chunks plus a reserve partition. -/
structure PhaseSplitLayout (parent : ExtReg) (k W : ℕ) where
  valid : ValidPhaseSplit parent k W

  reserve : Fin k → Reg

  active_reserve_disjoint :
    ∀ i, Disjoint (phaseChunkActive parent k W i) (reserve i)

  reserve_partition :
    (List.ofFn fun i => (reserve i).qubits).flatten
      =
    parent.reserve.qubits

  child_owned_pairwise :
    ∀ i j, i ≠ j →
      List.Disjoint
        ((phaseChunkActive parent k W i).qubits ++ (reserve i).qubits)
        ((phaseChunkActive parent k W j).qubits ++ (reserve j).qubits)

/-- The `i`th child extendable register induced by a split layout. -/
def PhaseSplitLayout.child
  {parent : ExtReg} {k W : ℕ}
  (layout : PhaseSplitLayout parent k W)
  (i : Fin k) : ExtReg :=
  ExtReg.withReserve (phaseChunkActive parent k W i)
    (layout.reserve i) (layout.active_reserve_disjoint i)

theorem PhaseSplitLayout.child_owned_disjoint
    {parent : ExtReg}
    {k W : ℕ}
    (layout : PhaseSplitLayout parent k W)
    {i j : Fin k}
    (hij : i ≠ j) :
    ExtReg.OwnedDisjoint (layout.child i) (layout.child j) := by
  simpa [PhaseSplitLayout.child, ExtReg.OwnedDisjoint, ExtReg.ownedQubits]
    using layout.child_owned_pairwise i j hij

/-- Pair of compatible split layouts for the two operands of a phase product. -/
structure Gate.PhaseProductLayout (x z : ExtReg) (k : ℕ) where
  xSplit : PhaseSplitLayout x k (phaseLimbWidth x z k)

  zSplit : PhaseSplitLayout z k (phaseLimbWidth x z k)

  cross_owned_disjoint :
    ∀ i j,
      ExtReg.OwnedDisjoint (xSplit.child i) (zSplit.child j)

/-- Interpret a child chunk as unsigned, except for the top chunk, which is signed. -/
def splitChunkInt
    {Basis : Type u} [RegEncoding Basis]
    {parent : ExtReg} {k W : ℕ}
  (layout : PhaseSplitLayout parent k W) (i : Fin k) (b : Basis) : ℤ :=
  if i.1 + 1 = k
    then tcDecodeWidth (parent.width - i.1 * W) ((layout.child i).toNat b)
    else (layout.child i).toNat b

/-! =========================================================
    Section 4: Width scanning and target-width definitions
========================================================= -/

/-- Initial width bookkeeping now uses the uniform lower-limb phase layout. -/
def initWidthState (x z : ExtReg) (k : ℕ) : WidthState k :=
  let W := phaseLimbWidth x z k
  { xw := fun i => phaseSplitLogicalWidth (ExtReg.width x) W k i
    zw := fun i => phaseSplitLogicalWidth (ExtReg.width z) W k i }

/-- Pull the recursion in `scanNeededWidths` out to a top-level helper. -/
def scanNeededWidthsAux {k : ℕ} (cur : WidthState k) (mx : NeededWidths k) : List (valid_ops k) → NeededWidths k
  | [] => mx
  | op :: rest =>
      let cur' := updateWidthState cur op
      let mx' := mergeNeededWidths mx (widthsOfState cur')
      scanNeededWidthsAux cur' mx' rest

/-- Scan needed widths using the new initial width state. -/
def scanNeededWidths {k : ℕ} (x z : ExtReg) (ops : List (valid_ops k)) : NeededWidths k :=
  scanNeededWidthsAux (initWidthState x z k) (widthsOfState (initWidthState x z k)) ops

/-- Uniform target width chosen to dominate every scanned `x` and `z` need, plus a sign bit. -/
def commonNeededWidth {k : ℕ} (need : NeededWidths k) : ℕ :=
  1 + Finset.univ.sup (fun i : Fin k => max (need.xneed i) (need.zneed i))

/-! =========================================================
    Section 5: Interpolation and phase coefficients
========================================================= -/

/-- Number of interpolation points used for radix-`k` phase decomposition. -/
def q (k : ℕ) : ℕ := 2 * k - 1

/-- One entry of the interpolation matrix. -/
def interpEntry (k : ℕ) (p : Point) (j : Fin (q k)) : ℚ :=
  match p with
  | .int z =>
      (z : ℚ) ^ (j : ℕ)
  | .frac c =>
      (c : ℚ) ^ (q k - 1 - (j : ℕ))

/-- Interpolation matrix built from the chosen point set. -/
def interpMatrix (k : ℕ) (pts : Fin (q k) → Point) : Matrix (Fin (q k)) (Fin (q k)) ℚ :=
  fun i j => interpEntry k (pts i) j

/-- Row vector `[1, b, b^2, ...]` used for interpolation evaluation. -/
def radixRow (k : ℕ) (b : ℚ) : Matrix (Fin 1) (Fin (q k)) ℚ := fun _ j => b ^ (j : ℕ)

/-- Coefficients obtained by multiplying the radix row by the inverse interpolation matrix. -/
noncomputable def phaseCoeffFromPts (k : ℕ) (pts : Fin (q k) → Point) (b : ℚ) : Fin (q k) → ℚ :=
  let B : Matrix (Fin (q k)) (Fin (q k)) ℚ := interpMatrix k pts
  let v : Matrix (Fin 1) (Fin (q k)) ℚ := radixRow k b * B⁻¹
  fun i => v 0 i

/-- Convert a point list of the right length into a `Fin`-indexed family. -/
def ptsToFin (k : ℕ) (pts : List Point) (hpts : pts.length = q k) : Fin (q k) → Point :=
  fun i => pts.get ⟨i.val, by have hi : i.val < q k := i.is_lt; simp [hpts]⟩

/-- Radix used for chunked phase decomposition. -/
def phaseRadix (x : Reg) (k : ℕ) : ℚ := (2 : ℚ) ^ (regSize x / k)

/-- Radix determined directly by an operand width. -/
def phaseRadixWidth (w k : ℕ) : ℚ := (2 : ℚ) ^ (w / k)

/-- Radix for an already chosen chunk width. -/
def chunkRadix (W : ℕ) : ℚ := (2 : ℚ) ^ W

/-- Phase coefficients for a fixed chunk width. -/
noncomputable def phaseCoeffFromPtsWidth (k W : ℕ) (pts : List Point) (hpts : pts.length = q k) : Fin (q k) → ℚ :=
  phaseCoeffFromPts k (ptsToFin k pts hpts) ((2 : ℚ) ^ W)

/-- Phase coefficients selected from the common limb width of two operands. -/
noncomputable def phaseCoeffFromPtsForRegs (k : ℕ) (x z : ExtReg) (pts : List Point) (hpts : pts.length = q k) : Fin (q k) → ℚ :=
  phaseCoeffFromPtsWidth k (phaseLimbWidth x z k) pts hpts

/-- The size parameter used when deciding whether a signed phase product
    should recurse again. -/

def phaseInputSize (x z : ExtReg) : ℕ := max x.width z.width

/-- The actual width of the recursively compiled chunk phase products. -/
def nextSignedWidth {k : ℕ} (x z : ExtReg) (ops : Prog k) : ℕ := commonNeededWidth (scanNeededWidths x z ops)

/-! =========================================================
    Section 6: Annotated operations and phase-product counting
========================================================= -/

/-- A source operation plus the interpolation term assigned to a phase-product leaf, if any. -/
structure AnnotatedOp (k : ℕ) where
  op : valid_ops k
  phaseTerm? : Option (Fin (q k))

/-- Attach interpolation-term indices to phase-product operations in source order. -/
def annotatePhaseTermsAux (k n : ℕ) (ops : List (valid_ops k)) : List (AnnotatedOp k) :=
  match ops with
  | [] => []
  | op :: rest =>
      match op with
      | .phaseProduct _i =>
          let ann : Option (Fin (q k)) :=
            if h : n < q k then some ⟨n, h⟩ else none
          ⟨op, ann⟩ :: annotatePhaseTermsAux k (n+1) rest
      | _ =>
          ⟨op, none⟩ :: annotatePhaseTermsAux k n rest

/-- Number of recursive phase-product leaves in a source program. -/
def phaseProductCount {k : ℕ} : List (valid_ops k) → ℕ
  | [] => 0
  | op :: ops =>
      match op with
      | .phaseProduct _ => phaseProductCount ops + 1
      | _               => phaseProductCount ops

/-! =========================================================
    Section 7: Signed layout construction and allocation/deallocation gates
========================================================= -/

/-- Number of high bits added when growing `src` into `dst`. -/
def extraDelta (src dst : ExtReg) : ℕ := dst.width - src.width

/-- Grow an extendable register just enough to reach target width `W`. -/
def growExtRegTo (e : ExtReg) (W : ℕ) : ExtReg := e.grow (W - e.width)

/-- The reserve has enough bits for `growExtRegTo e W`. -/
def ExtReg.CanGrowTo (e : ExtReg) (W : ℕ) : Prop := e.CanGrow (W - e.width)

theorem width_growExtRegTo
    (e : ExtReg)
    (W : ℕ)
    (hle : e.width ≤ W)
    (hcap : e.CanGrowTo W) :
    (growExtRegTo e W).width = W := by
  unfold growExtRegTo ExtReg.CanGrowTo at *
  rw [ExtReg.width_grow e (W - e.width) hcap]
  omega

/-- Initial signed compiler layout obtained by taking the split children as slots. -/
def initSignedLayoutState {x z : ExtReg} {k : ℕ} (layout : Gate.PhaseProductLayout x z k) : LayoutState k :=
  { xslot := fun i => layout.xSplit.child i, zslot := fun i => layout.zSplit.child i }

theorem initSignedLayoutState_owned_disjoint
    {x z : ExtReg}
    {k : ℕ}
    (layout : Gate.PhaseProductLayout x z k) :
    (initSignedLayoutState layout).OwnedPairwiseDisjoint := by
  constructor
  · intro i j hij
    exact layout.xSplit.child_owned_disjoint hij
  constructor
  · intro i j hij
    exact layout.zSplit.child_owned_disjoint hij
  · intro i j
    exact layout.cross_owned_disjoint i j

/-- Final widened chunk views for the compiled signed body.
Each final slot is obtained by widening the corresponding abstract initial
split chunk. No concrete register splitting is used here.
-/

def targetSignedLayoutState {k : ℕ} (src : LayoutState k) (need : NeededWidths k) : LayoutState k :=
  let Wwork := commonNeededWidth need
  { xslot := fun i => growExtRegTo (src.xslot i) Wwork, zslot := fun i => growExtRegTo (src.zslot i) Wwork }

/-- `src` has enough reserve to realize all scanned width needs. -/
def LayoutState.CanGrowToNeeds {k : ℕ} (src : LayoutState k) (need : NeededWidths k) : Prop := src.CanGrowTo (commonNeededWidth need)

/-- Allocation gate for a single chunk. Lower chunks are zero-extended;
    the top chunk is sign-extended. -/

def allocChunkGate {k : ℕ} (i : Fin k) (src dst : ExtReg) : Gate :=
  let n := extraDelta src dst
  if _h0 : n = 0 then
    Gate.id
  else if _htop : isTopChunk i then
    Gate.signExtend src n
  else
    Gate.zeroExtend src n

/-- Matching deallocation gate for a single chunk. -/
def deallocChunkGate {k : ℕ} (i : Fin k) (src dst : ExtReg) : Gate :=
  let n := extraDelta src dst
  if _h0 : n = 0 then
    Gate.id
  else if _htop : isTopChunk i then
    Gate.signDealloc src n
  else
    Gate.zeroDealloc src n

/-- Allocation program for the first `n` chunks, in increasing order `0,1,...,n-1`. -/
def compileSignedAllocationsAux {k : ℕ} (src dst : LayoutState k) :
    ∀ (n : ℕ), n ≤ k → Gate
  | 0, _ => Gate.id
  | n + 1, hn =>
      let hk' : n ≤ k := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn
      let i : Fin k := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
      compileSignedAllocationsAux src dst n hk' ;;
      allocChunkGate i (src.xslot i) (dst.xslot i) ;;
      allocChunkGate i (src.zslot i) (dst.zslot i)

/-- Emit all chunk allocations before the signed arithmetic body. -/
def compileSignedAllocations (k : ℕ) (src dst : LayoutState k) : Gate :=
  compileSignedAllocationsAux src dst k (le_rfl)

/-- Deallocation program for the first `n` chunks, in decreasing order `n-1,...,1,0`. -/
def compileSignedDeallocationsAux {k : ℕ} (src dst : LayoutState k) :
    ∀ (n : ℕ), n ≤ k → Gate
  | 0, _ => Gate.id
  | n + 1, hn =>
      let hk' : n ≤ k := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn
      let i : Fin k := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
      deallocChunkGate i (src.zslot i) (dst.zslot i) ;;
      deallocChunkGate i (src.xslot i) (dst.xslot i) ;;
      compileSignedDeallocationsAux src dst n hk'

/-- Emit all chunk deallocations after the signed arithmetic body. -/
def compileSignedDeallocations (k : ℕ) (src dst : LayoutState k) : Gate :=
  compileSignedDeallocationsAux src dst k (le_rfl)

/-! =========================================================
    Section 8: Compilation from `valid_ops` to `Gate`
========================================================= -/

/-- Signed compiler for annotated ops.  The layout state already contains
    enough extra width in each slot, so compilation only emits gates and does
    not resize the state further. -/

def compileAnnotatedOpsToSignedGateAux
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ)
  (phaseCoeff : Fin (q k) → ℚ)
  (st : LayoutState k)
  (ops : List (AnnotatedOp k)) : Gate :=
  match ops with
  | [] => Gate.id
  | ⟨op, term?⟩ :: rest =>
      let tail := compileAnnotatedOpsToSignedGateAux k hk phi phaseCoeff st rest
      match op with
      | .shiftL i n =>
          Gate.ShiftL (st.xslot i) n ;;
          Gate.ShiftL (st.zslot i) n ;; tail
      | .shiftR i n =>
          Gate.ShiftR (st.xslot i) n ;;
          Gate.ShiftR (st.zslot i) n ;; tail
      | .negate i =>
          Gate.Negate (st.xslot i) ;;
          Gate.Negate (st.zslot i) ;; tail
      | .addScaled dst src negsrc sh =>
          Gate.AddScaled (st.xslot dst) (st.xslot src) negsrc sh ;;
          Gate.AddScaled (st.zslot dst) (st.zslot src) negsrc sh ;; tail
      | .phaseProduct i =>
          match term? with
          | some l =>
              Gate.SignedPhaseProd
                (phi * ((phaseCoeff l : ℚ) : ℝ))
                (st.xslot i)
                (st.zslot i) ;; tail
          | none =>
              tail

/-- Full signed phase-product lowering: allocate widths, compile the annotated body, then deallocate. -/
noncomputable def compileOpsToSignedGate
  (k : ℕ) (hk : 1 < k) (phi : ℝ) (x z : ExtReg) (layout : Gate.PhaseProductLayout x z k)
  (phaseCoeff : Fin (q k) → ℚ) (ops : List (valid_ops k)) : Gate :=
  let annOps : List (AnnotatedOp k) :=
    annotatePhaseTermsAux k 0 ops
  let need : NeededWidths k :=
    scanNeededWidths x z ops
  let stInit : LayoutState k :=
    initSignedLayoutState layout
  let stFinal : LayoutState k :=
    targetSignedLayoutState stInit need
  let allocs : Gate :=
    compileSignedAllocations k stInit stFinal
  let body : Gate :=
    compileAnnotatedOpsToSignedGateAux k hk phi phaseCoeff stFinal annOps
  let deallocs : Gate :=
    compileSignedDeallocations k stInit stFinal
  allocs ;; body ;; deallocs

/-- Add a shared control to phase-product leaves while leaving structural and arithmetic gates unchanged. -/
def controlPhaseLeaves (ctrl : ℕ) : Gate → Gate
  | .id => .id
  | .seq U V => controlPhaseLeaves ctrl U ;; controlPhaseLeaves ctrl V
  | .SignedPhaseProd phi x z => .CSignedPhaseProd ctrl phi x z
  | .ShiftL r n => .ShiftL r n
  | .ShiftR r n => .ShiftR r n
  | .Negate r => .Negate r
  | .AddScaled dst src negSrc sh => .AddScaled dst src negSrc sh
  | .zeroExtend r n => .zeroExtend r n
  | .signExtend r n => .signExtend r n
  | .zeroDealloc r n => .zeroDealloc r n
  | .signDealloc r n => .signDealloc r n
  | U => U

/-- Controlled signed lowering obtained by compiling first and controlling phase leaves. -/
noncomputable def compileOpsToCSignedGate
    (k : ℕ) (hk : 1 < k) (ctrl : ℕ) (phi : ℝ) (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z k) (coeff : Fin (q k) → ℚ) (ops : Prog k) : Gate :=
  controlPhaseLeaves ctrl (compileOpsToSignedGate k hk phi x z layout coeff ops)

/-- The control qubit is outside every child register touched by a phase-product layout. -/
def Gate.PhaseProductLayout.ControlDisjoint {x z : ExtReg} {k : ℕ} (layout : Gate.PhaseProductLayout x z k) (ctrl : ℕ) : Prop :=
  (∀ i, ctrl ∉ (layout.xSplit.child i).ownedQubits) ∧ (∀ i, ctrl ∉ (layout.zSplit.child i).ownedQubits)

/-- Partition of a parent reserve into `k` child reserve sizes. -/
structure ReserveBudget (parent : ExtReg) (k : ℕ) where
  size : Fin k → ℕ
  total : (List.ofFn size).sum = parent.capacity

/-- Starting reserve offset for child `i`. -/
def ReserveBudget.offset {parent : ExtReg} {k : ℕ} (budget : ReserveBudget parent k) (i : Fin k) : ℕ :=
  ((List.ofFn budget.size).take i.1).sum

/-- Concrete reserve slice assigned to child `i`. -/
def ReserveBudget.childReserve {parent : ExtReg} {k : ℕ} (budget : ReserveBudget parent k) (i : Fin k) : Reg :=
  (parent.reserve.drop (budget.offset i)).take (budget.size i)

end Shor


/-!
# Phase-Product Compiler Support Lemmas
This file is the reusable proof layer above `PhaseProduct.Core`. It groups the
small but frequently used facts needed by larger correctness proofs: annotation
bookkeeping, signed-width safety, source-row arithmetic, width-scan consequences,
layout extensionality, and the canonical interpolation-point bridge to the pure
Toom-Cook math file.
-/
namespace Shor
open Gate
open Operations
open scoped BigOperators

/-! =========================================================
    Section 1: Annotation and phase-product counting
    These lemmas are pure program-bookkeeping facts. They keep phase-product
    term indices stable under append and prove that local arithmetic helper
    programs do not introduce recursive phase-product leaves.
========================================================= -/

/-- Compatibility alias for older files: every concrete `Reg` already carries `Nodup`. -/

@[simp] lemma compileSignedAllocationsAux_zero {k : ℕ} (src dst : LayoutState k) (h : 0 ≤ k) :
  compileSignedAllocationsAux src dst 0 h = Gate.id := rfl

@[simp] lemma compileSignedAllocationsAux_succ {k : ℕ} (src dst : LayoutState k)
  (n : ℕ) (hn : n + 1 ≤ k) :
  compileSignedAllocationsAux src dst (n + 1) hn
    =
  let hk' : n ≤ k := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn
  let i : Fin k := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
  compileSignedAllocationsAux src dst n hk' ;;
  allocChunkGate i (src.xslot i) (dst.xslot i) ;;
  allocChunkGate i (src.zslot i) (dst.zslot i) := rfl

@[simp] lemma compileSignedDeallocationsAux_zero {k : ℕ} (src dst : LayoutState k) (h : 0 ≤ k) :
  compileSignedDeallocationsAux src dst 0 h = Gate.id := rfl

@[simp] lemma compileSignedDeallocationsAux_succ {k : ℕ} (src dst : LayoutState k)
  (n : ℕ) (hn : n + 1 ≤ k) :
  compileSignedDeallocationsAux src dst (n + 1) hn
    =
  let hk' : n ≤ k := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn
  let i : Fin k := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
  deallocChunkGate i (src.zslot i) (dst.zslot i) ;;
  deallocChunkGate i (src.xslot i) (dst.xslot i) ;;
  compileSignedDeallocationsAux src dst n hk' := rfl

variable (qs : QSemantics) [RegEncoding qs.Basis]

/-! =========================================================
    Section 2: Width scans and signed-fit safety
    This section turns symbolic width scans into usable signed-fit obligations.
    It also packages the arithmetic safety facts for shift, negate, and add-scaled
    source rows.
========================================================= -/

/-- The scan result dominates the incoming `x` width lower bound. -/
lemma scanNeededWidthsAux_x_ge
  {k : ℕ} (i : Fin k) :
  ∀ (ops : List (valid_ops k)) (cur : WidthState k) (mx : NeededWidths k),
    mx.xneed i ≤ (scanNeededWidthsAux cur mx ops).xneed i
  | [], cur, mx => by
      simp [scanNeededWidthsAux]
  | op :: rest, cur, mx => by
      simp [scanNeededWidthsAux]
      have htail :
          (mergeNeededWidths mx (widthsOfState (updateWidthState cur op))).xneed i
            ≤
          (scanNeededWidthsAux
              (updateWidthState cur op)
              (mergeNeededWidths mx (widthsOfState (updateWidthState cur op)))
              rest).xneed i :=
        scanNeededWidthsAux_x_ge
          (i := i)
          rest
          (updateWidthState cur op)
          (mergeNeededWidths mx (widthsOfState (updateWidthState cur op)))
      exact le_trans (le_max_left _ _) htail

/-- The scan result dominates the incoming `z` width lower bound. -/
lemma scanNeededWidthsAux_z_ge
  {k : ℕ} (i : Fin k) :
  ∀ (ops : List (valid_ops k)) (cur : WidthState k) (mx : NeededWidths k),
    mx.zneed i ≤ (scanNeededWidthsAux cur mx ops).zneed i
  | [], cur, mx => by
      simp [scanNeededWidthsAux]
  | op :: rest, cur, mx => by
      simp [scanNeededWidthsAux]
      have htail :
          (mergeNeededWidths mx (widthsOfState (updateWidthState cur op))).zneed i
            ≤
          (scanNeededWidthsAux
              (updateWidthState cur op)
              (mergeNeededWidths mx (widthsOfState (updateWidthState cur op)))
              rest).zneed i :=
        scanNeededWidthsAux_z_ge
          (i := i)
          rest
          (updateWidthState cur op)
          (mergeNeededWidths mx (widthsOfState (updateWidthState cur op)))
      exact le_trans (le_max_left _ _) htail

/-- The top chunk of a valid top-heavy split has positive width when the parent does. -/
lemma phaseLimbWidth_top_nonempty
    (w other k : ℕ)
    (hk : 0 < k) :
    w = 0 ∨
      (k - 1) * min (w / k) (other / k) < w := by
  by_cases hw : w = 0
  · exact Or.inl hw
  right
  have hwpos : 0 < w := Nat.pos_of_ne_zero hw
  let q := w / k
  have hW :
      min (w / k) (other / k) ≤ q := by
    exact Nat.min_le_left _ _
  have hleft :
      (k - 1) * min (w / k) (other / k)
        ≤
      (k - 1) * q :=
    Nat.mul_le_mul_left _ hW
  have hkpred : k - 1 < k := by
    omega
  by_cases hq : q = 0
  · have hmin_zero :
        min (w / k) (other / k) = 0 :=
      Nat.eq_zero_of_le_zero (by simpa [hq] using hW)
    simp [hmin_zero]
    exact hwpos
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
    have hstrict :
        (k - 1) * q < k * q :=
      Nat.mul_lt_mul_of_pos_right hkpred hqpos
    have hdiv :
        k * q ≤ w := by
      dsimp [q]
      simpa [Nat.mul_comm] using Nat.div_mul_le_self w k
    exact lt_of_le_of_lt hleft
      (lt_of_lt_of_le hstrict hdiv)

lemma phaseLimbWidth_valid_left
    (x z : ExtReg)
    {k : ℕ}
    (hk : 0 < k) :
    ValidPhaseSplit x k (phaseLimbWidth x z k) := by
  refine ⟨hk, ?_, ?_⟩
  · unfold phaseLimbWidth phaseLimbWidthOfWidth
    have hW :
        min (x.width / k) (z.width / k)
          ≤ x.width / k :=
      Nat.min_le_left _ _
    have h₁ :
        (k - 1) * min (x.width / k) (z.width / k)
          ≤
        (k - 1) * (x.width / k) :=
      Nat.mul_le_mul_left _ hW
    have h₂ :
        (k - 1) * (x.width / k)
          ≤
        k * (x.width / k) := by
      exact Nat.mul_le_mul_right _
        (Nat.sub_le k 1)
    have h₃ :
        k * (x.width / k) ≤ x.width := by
      simpa [Nat.mul_comm] using
        Nat.div_mul_le_self x.width k
    exact h₁.trans (h₂.trans h₃)
  · unfold phaseLimbWidth phaseLimbWidthOfWidth
    exact phaseLimbWidth_top_nonempty
      x.width z.width k hk

lemma phaseLimbWidth_valid_right
    (x z : ExtReg)
    {k : ℕ}
    (hk : 0 < k) :
    ValidPhaseSplit z k (phaseLimbWidth x z k) := by
  refine ⟨hk, ?_, ?_⟩
  · unfold phaseLimbWidth phaseLimbWidthOfWidth
    have hW :
        min (x.width / k) (z.width / k)
          ≤ z.width / k :=
      Nat.min_le_right _ _
    have h₁ :
        (k - 1) * min (x.width / k) (z.width / k)
          ≤
        (k - 1) * (z.width / k) :=
      Nat.mul_le_mul_left _ hW
    have h₂ :
        (k - 1) * (z.width / k)
          ≤
        k * (z.width / k) := by
      exact Nat.mul_le_mul_right _
        (Nat.sub_le k 1)
    have h₃ :
        k * (z.width / k) ≤ z.width := by
      simpa [Nat.mul_comm] using
        Nat.div_mul_le_self z.width k
    exact h₁.trans (h₂.trans h₃)
  · unfold phaseLimbWidth phaseLimbWidthOfWidth
    simpa [Nat.min_comm] using
      phaseLimbWidth_top_nonempty
        z.width x.width k hk

/-! ---------------------------------------------------------
    Chunk width, reconstruction, and disjointness proofs
--------------------------------------------------------- -/

/-- Length of a concrete `drop`/`take` slice that lies inside a register. -/
lemma regSize_drop_take_of_add_le
    (r : Reg)
    (start len : ℕ)
    (h : start + len ≤ regSize r) :
    regSize ((r.drop start).take len) = len := by
  change ((r.qubits.drop start).take len).length = len
  rw [List.length_take, List.length_drop]
  apply Nat.min_eq_left
  unfold regSize Reg.width at h
  omega

lemma phaseChunkActive_width
    (e : ExtReg)
    (k W : ℕ)
    (i : Fin k)
    (hvalid : ValidPhaseSplit e k W) :
    regSize (phaseChunkActive e k W i) =
      phaseSplitLogicalWidth e.width W k i := by
  obtain ⟨_hk, hbound, _htopNonempty⟩ := hvalid
  unfold phaseChunkActive
  by_cases htop : isTopChunk i
  · have hik : k - 1 = i.1 := by
      unfold isTopChunk at htop
      omega
    have hstart : i.1 * W ≤ e.width := by
      simpa [hik] using hbound
    apply regSize_drop_take_of_add_le
    simp only [phaseChunkStart, phaseSplitLogicalWidth, htop, if_pos]
    exact le_of_eq <| by
      calc
        i.1 * W + (e.width - i.1 * W) = e.width :=
          Nat.add_sub_of_le hstart
        _ = regSize e.active := rfl
  · have hi : i.1 + 1 ≤ k - 1 := by
      unfold isTopChunk at htop
      have hle : i.1 + 1 ≤ k :=
        Nat.succ_le_of_lt i.2
      omega
    have hmul :
        (i.1 + 1) * W ≤ (k - 1) * W :=
      Nat.mul_le_mul_right W hi
    have hfit :
        i.1 * W + W ≤ e.width := by
      calc
        i.1 * W + W = (i.1 + 1) * W := by
          rw [Nat.add_mul]
          simp
        _ ≤ (k - 1) * W := hmul
        _ ≤ e.width := hbound
    apply regSize_drop_take_of_add_le
    simpa [phaseChunkStart, phaseSplitLogicalWidth, htop] using hfit

lemma PhaseSplitLayout.child_width
    {parent : ExtReg}
    {k W : ℕ}
    (layout : PhaseSplitLayout parent k W)
    (i : Fin k) :
    (layout.child i).width =
      phaseSplitLogicalWidth parent.width W k i := by
  unfold PhaseSplitLayout.child ExtReg.width
  exact phaseChunkActive_width
    parent k W i layout.valid

/-- Two consecutive-block slices of a `Nodup` list are disjoint whenever the
    first block ends no later than the second one starts. -/
theorem slice_disjoint {L : List ℕ} (hL : L.Nodup) {a b c d : ℕ} (h : b + a ≤ d) :
    (List.take a (List.drop b L)).Disjoint (List.take c (List.drop d L)) := by
  have e1 : List.take a (List.drop b L) = List.drop b (List.take (b + a) L) := by
    rw [List.drop_take]; congr 1; omega
  have sub1 : (List.take a (List.drop b L)).Sublist (List.take (b + a) L) := by
    rw [e1]; exact List.drop_sublist _ _
  have sub2 : (List.take c (List.drop d L)).Sublist (List.drop d L) :=
    List.take_sublist _ _
  have hdisj : (List.take (b + a) L).Disjoint (List.drop d L) :=
    List.disjoint_take_drop hL h
  exact List.disjoint_of_subset_left sub1.subset
    (List.disjoint_of_subset_right sub2.subset hdisj)

/-- Flattening `n` consecutive width-`W` blocks recovers the length-`n·W` prefix. -/
theorem flatten_blocks (L : List ℕ) (W : ℕ) : ∀ n : ℕ,
    (List.ofFn (n := n) fun i : Fin n => List.take W (List.drop (i.1 * W) L)).flatten
      = List.take (n * W) L := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.flatten_append]
    simp only [Fin.val_castSucc, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [ih]
    have hmul : (n + 1) * W = n * W + W := by ring
    have hlast : (Fin.last n).1 = n := rfl
    rw [hlast, hmul, List.take_add]

theorem phaseChunkActive_pairwise_disjoint
    (e : ExtReg)
    (k W : ℕ)
    (hvalid : ValidPhaseSplit e k W)
    {i j : Fin k}
    (hij : i ≠ j) :
    Disjoint
      (phaseChunkActive e k W i)
      (phaseChunkActive e k W j) := by
  obtain ⟨hk, hcap⟩ := hvalid
  have hL : e.active.qubits.Nodup := e.active.nodup
  have hijn : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
  have hik := i.2; have hjk := j.2
  rcases Nat.lt_or_gt_of_ne hijn with hlt | hgt
  · have hnotop : ¬ isTopChunk i := by unfold isTopChunk; omega
    have hsi : phaseSplitLogicalWidth e.width W k i = W := by
      simp [phaseSplitLogicalWidth, hnotop]
    have hexp : ((i : ℕ) + 1) * W = (i : ℕ) * W + W := by ring
    have h1 : ((i : ℕ) + 1) * W ≤ (j : ℕ) * W := Nat.mul_le_mul_right W (by omega)
    have key : (i : ℕ) * W + W ≤ (j : ℕ) * W := by omega
    simp only [Disjoint, phaseChunkActive, phaseChunkStart, Reg.take, Reg.drop, hsi]
    exact slice_disjoint hL key
  · have hnotop : ¬ isTopChunk j := by unfold isTopChunk; omega
    have hsj : phaseSplitLogicalWidth e.width W k j = W := by
      simp [phaseSplitLogicalWidth, hnotop]
    have hexp : ((j : ℕ) + 1) * W = (j : ℕ) * W + W := by ring
    have h1 : ((j : ℕ) + 1) * W ≤ (i : ℕ) * W := Nat.mul_le_mul_right W (by omega)
    have key : (j : ℕ) * W + W ≤ (i : ℕ) * W := by omega
    simp only [Disjoint, phaseChunkActive, phaseChunkStart, Reg.take, Reg.drop, hsj]
    exact (slice_disjoint hL key).symm

/-! ---------------------------------------------------------
    Workspace preservation and reserve-budget construction
--------------------------------------------------------- -/

/-- Growing every slot to the target width preserves control disjointness. -/
theorem controlDisjoint_target
    {x z : ExtReg}
    {k : ℕ}
    (layout : Gate.PhaseProductLayout x z k)
    (ctrl : ℕ)
    (need : NeededWidths k)
    (hctrl : layout.ControlDisjoint ctrl) :
    let src := initSignedLayoutState layout
    let dst := targetSignedLayoutState src need
    (∀ i, ctrl ∉ (dst.xslot i).ownedQubits) ∧
    (∀ i, ctrl ∉ (dst.zslot i).ownedQubits) := by
  intro src dst
  obtain ⟨hx, hz⟩ := hctrl
  refine ⟨?_, ?_⟩
  · intro i
    simpa [dst, targetSignedLayoutState, growExtRegTo, src, initSignedLayoutState, ExtReg.ownedQubits_grow] using hx i
  · intro i
    simpa [dst, targetSignedLayoutState, growExtRegTo, src, initSignedLayoutState, ExtReg.ownedQubits_grow] using hz i

/-- Growing an extendable register only moves qubits from reserve to active; ownership is unchanged. -/

@[simp]
theorem ExtReg.ownedQubits_grow
    (e : ExtReg)
    (n : ℕ) :
    (e.grow n).ownedQubits = e.ownedQubits := by
  simp [ExtReg.ownedQubits, ExtReg.grow, Reg.append, ExtReg.newBits, Reg.take, ExtReg.remainingReserve, Reg.drop, List.append_assoc, List.take_append_drop]

/-- Target widening preserves pairwise owned-disjointness of all slots. -/
theorem targetSignedLayoutState_owned_disjoint
    {x z : ExtReg}
    {k : ℕ}
    (layout : Gate.PhaseProductLayout x z k)
    (need : NeededWidths k) :
    (targetSignedLayoutState
      (initSignedLayoutState layout)
      need).OwnedPairwiseDisjoint := by
  obtain ⟨hx, hz, hxz⟩ := initSignedLayoutState_owned_disjoint layout
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    simpa [targetSignedLayoutState, growExtRegTo, ExtReg.OwnedDisjoint, ExtReg.ownedQubits_grow] using hx i j hij
  · intro i j hij
    simpa [targetSignedLayoutState, growExtRegTo, ExtReg.OwnedDisjoint, ExtReg.ownedQubits_grow] using hz i j hij
  · intro i j
    simpa [targetSignedLayoutState, growExtRegTo, ExtReg.OwnedDisjoint, ExtReg.ownedQubits_grow] using hxz i j

/-- Consecutive variable-width slices reconstruct the corresponding prefix. -/
private theorem flatten_consecutive_slices
    (L : List ℕ) :
    ∀ (k : ℕ) (size : Fin k → ℕ),
      (List.ofFn fun i =>
        List.take (size i)
          (List.drop
            (((List.ofFn size).take i.1).sum)
            L)).flatten
        =
      List.take ((List.ofFn size).sum) L := by
  intro k
  induction k with
  | zero =>
      intro size
      simp
  | succ k ih =>
      intro size
      let size' : Fin k → ℕ :=
        fun i => size i.castSucc
      have htake (i : Fin k) :
          (List.ofFn size).take i.1
            =
              (List.ofFn size').take i.1 := by
        rw [List.ofFn_succ', List.concat_eq_append]
        simp [size', List.take_append_of_le_length]
      have htakeLast :
          (List.ofFn size).take k
            =
          List.ofFn size' := by
        rw [List.ofFn_succ', List.concat_eq_append]
        simp [size']
      have hsum :
          (List.ofFn size).sum
            =
          (List.ofFn size').sum
            + size (Fin.last k) := by
        rw [List.ofFn_succ']
        simp [size']
      rw [List.ofFn_succ', List.concat_eq_append, List.flatten_append]
      simp only [Fin.val_castSucc, List.flatten_cons, List.flatten_nil, List.append_nil]
      have hlastVal : (Fin.last k).1 = k := rfl
      rw [hlastVal]
      simp_rw [htake]
      change
        (List.ofFn fun i : Fin k =>
          List.take (size' i)
            (List.drop
              (((List.ofFn size').take i.1).sum)
              L)).flatten
          ++
        List.take (size (Fin.last k))
          (List.drop
            (((List.ofFn size).take k).sum)
            L)
          =
        List.take ((List.ofFn size).sum) L
      rw [ih size', htakeLast, hsum, List.take_add]

theorem ReserveBudget.flatten_childReserve
    {parent : ExtReg}
    {k : ℕ}
    (budget : ReserveBudget parent k) :
    (List.ofFn fun i =>
      (budget.childReserve i).qubits).flatten
      =
    parent.reserve.qubits := by
  simp only [ReserveBudget.childReserve, ReserveBudget.offset, Reg.take, Reg.drop]
  rw [flatten_consecutive_slices]
  rw [budget.total]
  simp [ExtReg.capacity, regSize, Reg.width]

private theorem phaseChunkActive_sublist
    (parent : ExtReg)
    (k W : ℕ)
    (i : Fin k) :
    (phaseChunkActive parent k W i).qubits.Sublist
      parent.active.qubits := by
  simp only [phaseChunkActive, phaseChunkStart, Reg.take, Reg.drop]
  exact (List.take_sublist _ _).trans (List.drop_sublist _ _)

private theorem ReserveBudget.childReserve_sublist
    {parent : ExtReg}
    {k : ℕ}
    (budget : ReserveBudget parent k)
    (i : Fin k) :
    (budget.childReserve i).qubits.Sublist
      parent.reserve.qubits := by
  simp only [ReserveBudget.childReserve, ReserveBudget.offset, Reg.take, Reg.drop]
  exact
    (List.take_sublist _ _).trans
      (List.drop_sublist _ _)

private theorem phaseChunkActive_childReserve_disjoint
    {parent : ExtReg}
    {k W : ℕ}
    (budget : ReserveBudget parent k)
    (i j : Fin k) :
    List.Disjoint
      (phaseChunkActive parent k W i).qubits
      (budget.childReserve j).qubits := by
  have hactive :=
    phaseChunkActive_sublist parent k W i
  have hreserve :=
    budget.childReserve_sublist j
  have hparent :
      parent.active.qubits.Disjoint
        parent.reserve.qubits := by
    simpa [Disjoint] using
      parent.active_reserve_disjoint
  exact
    List.disjoint_of_subset_left hactive.subset
      (List.disjoint_of_subset_right
        hreserve.subset
        hparent)

private theorem pairwise_disjoint_ofFn
    {α : Type*}
    {k : ℕ}
    {f : Fin k → List α}
    (hpair : (List.ofFn f).Pairwise List.Disjoint)
    {i j : Fin k}
    (hij : i ≠ j) :
    (f i).Disjoint (f j) := by
  have hval : i.1 ≠ j.1 := by
    intro h
    apply hij
    exact Fin.ext h
  rcases Nat.lt_or_gt_of_ne hval with hijlt | hjilt
  ·
    have h := (List.pairwise_iff_getElem.mp hpair)  i.1 j.1 (by simp) (by simp) hijlt
    simpa using h
  ·
    have h :=
      (List.pairwise_iff_getElem.mp hpair)
        j.1
        i.1
        (by simp)
        (by simp)
        hjilt
    simpa using h.symm

/-- Build an abstract split layout from concrete active slices and a reserve budget. -/
def PhaseSplitLayout.ofBudget
    (parent : ExtReg)
    (k W : ℕ)
    (hvalid : ValidPhaseSplit parent k W)
    (budget : ReserveBudget parent k) :
    PhaseSplitLayout parent k W :=
  {
    valid := hvalid
    reserve := budget.childReserve
    active_reserve_disjoint := by
      intro i
      simpa [Disjoint] using
        phaseChunkActive_childReserve_disjoint
          (W := W)
          budget i i
    reserve_partition := by
      exact budget.flatten_childReserve
    child_owned_pairwise := by
      intro i j hij
      have hAA :
          List.Disjoint
            (phaseChunkActive parent k W i).qubits
            (phaseChunkActive parent k W j).qubits := by
        simpa [Disjoint] using
          phaseChunkActive_pairwise_disjoint
            parent k W hvalid hij
      have hAR :
          List.Disjoint
            (phaseChunkActive parent k W i).qubits
            (budget.childReserve j).qubits :=
        phaseChunkActive_childReserve_disjoint
          (W := W)
          budget i j
      have hRA :
          List.Disjoint
            (budget.childReserve i).qubits
            (phaseChunkActive parent k W j).qubits :=
        (phaseChunkActive_childReserve_disjoint
          (W := W)
          budget j i).symm
      have hflatNodup :
          ((List.ofFn fun t : Fin k =>
            (budget.childReserve t).qubits).flatten).Nodup := by
        rw [budget.flatten_childReserve]
        exact parent.reserve.nodup
      have hreservePairwise :
          (List.ofFn fun t : Fin k =>
            (budget.childReserve t).qubits).Pairwise
              List.Disjoint :=
        (List.nodup_flatten.mp hflatNodup).2
      have hRR :
          List.Disjoint
            (budget.childReserve i).qubits
            (budget.childReserve j).qubits :=
        pairwise_disjoint_ofFn
          (f := fun t : Fin k =>
            (budget.childReserve t).qubits)
          hreservePairwise
          hij
      intro q hqLeft hqRight
      rcases List.mem_append.mp hqLeft with hqAi | hqRi
      · rcases List.mem_append.mp hqRight with hqAj | hqRj
        · exact hAA hqAi hqAj
        · exact hAR hqAi hqRj
      · rcases List.mem_append.mp hqRight with hqAj | hqRj
        · exact hRA hqRi hqAj
        · exact hRR hqRi hqRj
  }

/-- Initial `x` slot width agrees with the symbolic initial width state. -/
lemma stInit_xslot_width
    {x z : ExtReg}
    {k : ℕ}
    (layout : Gate.PhaseProductLayout x z k)
    (i : Fin k) :
    ((initSignedLayoutState layout).xslot i).width
      =
    (initWidthState x z k).xw i := by
  change
    (layout.xSplit.child i).width
      =
    phaseSplitLogicalWidth
      x.width
      (phaseLimbWidth x z k)
      k i
  exact layout.xSplit.child_width i

/-- Initial `z` slot width agrees with the symbolic initial width state. -/
lemma stInit_zslot_width
    {x z : ExtReg}
    {k : ℕ}
    (layout : Gate.PhaseProductLayout x z k)
    (i : Fin k) :
    ((initSignedLayoutState layout).zslot i).width
      =
    (initWidthState x z k).zw i := by
  change
    (layout.zSplit.child i).width
      =
    phaseSplitLogicalWidth
      z.width
      (phaseLimbWidth x z k)
      k i
  exact layout.zSplit.child_width i

/-- The common target width dominates every scanned `x` need. -/
lemma commonNeededWidth_ge_xneed {k : ℕ} (need : NeededWidths k) (i : Fin k) :
  need.xneed i + 1 ≤ commonNeededWidth need := by
  unfold commonNeededWidth
  have h :
      max (need.xneed i) (need.zneed i)
        ≤ Finset.univ.sup (fun j : Fin k => max (need.xneed j) (need.zneed j)) :=
    Finset.le_sup (f := fun j : Fin k => max (need.xneed j) (need.zneed j))
      (Finset.mem_univ i)
  have h' : need.xneed i ≤ _ := le_trans (le_max_left _ _) h
  omega

/-- The common target width dominates every scanned `z` need. -/
lemma commonNeededWidth_ge_zneed {k : ℕ} (need : NeededWidths k) (i : Fin k) :
  need.zneed i + 1 ≤ commonNeededWidth need := by
  unfold commonNeededWidth
  have h :
      max (need.xneed i) (need.zneed i)
        ≤ Finset.univ.sup (fun j : Fin k => max (need.xneed j) (need.zneed j)) :=
    Finset.le_sup (f := fun j : Fin k => max (need.xneed j) (need.zneed j))
      (Finset.mem_univ i)
  have h' : need.zneed i ≤ _ := le_trans (le_max_right _ _) h
  omega

/-! =========================================================
    Section 6: Scan consequences for target layouts
========================================================= -/

/-- The initial `x` width is included in the full width scan. -/
lemma scanNeededWidths_x_ge_init
    {k : ℕ} (x z : ExtReg) (ops : List (valid_ops k)) (i : Fin k) :
    (initWidthState x z k).xw i ≤ (scanNeededWidths x z ops).xneed i := by
  simp [scanNeededWidths]
  exact
    scanNeededWidthsAux_x_ge
      (i := i)
      ops
      (initWidthState x z k)
      (widthsOfState (initWidthState x z k))

/-- The initial z width is included in the full width scan. -/
lemma scanNeededWidths_z_ge_init
    {k : ℕ} (x z : ExtReg) (ops : List (valid_ops k)) (i : Fin k) :
    (initWidthState x z k).zw i ≤ (scanNeededWidths x z ops).zneed i := by
  simp [scanNeededWidths]
  exact
    scanNeededWidthsAux_z_ge
      (i := i)
      ops
      (initWidthState x z k)
      (widthsOfState (initWidthState x z k))

/-- A grown target `x` slot has exactly the common scanned width. -/
lemma targetSignedLayoutState_xslot_width_scan
    {x z : ExtReg}
    {k : ℕ}
    (layout : Gate.PhaseProductLayout x z k)
    (ops : Prog k)
    (i : Fin k)
    (hcap :
      (initSignedLayoutState layout).CanGrowToNeeds
        (scanNeededWidths x z ops)) :
    ((targetSignedLayoutState
      (initSignedLayoutState layout)
      (scanNeededWidths x z ops)).xslot i).width
      =
    commonNeededWidth (scanNeededWidths x z ops) := by
  let stInit := initSignedLayoutState layout
  let need := scanNeededWidths x z ops
  let Wwork := commonNeededWidth need
  have hinit :
      (stInit.xslot i).width =
        (initWidthState x z k).xw i := by
    simpa [stInit] using stInit_xslot_width layout i
  have hscan :
      (initWidthState x z k).xw i ≤ need.xneed i := by
    simpa [need] using
      scanNeededWidths_x_ge_init x z ops i
  have hneed :
      need.xneed i + 1 ≤ Wwork :=
    commonNeededWidth_ge_xneed need i
  have hle : (stInit.xslot i).width ≤ Wwork := by
    rw [hinit]
    omega
  have hgrow :
      (stInit.xslot i).CanGrow
        (Wwork - (stInit.xslot i).width) := by
    exact hcap.1 i
  simpa [stInit, need, Wwork, targetSignedLayoutState] using
    width_growExtRegTo
      (stInit.xslot i) Wwork hle hgrow

/-- A grown target `z` slot has exactly the common scanned width. -/
lemma targetSignedLayoutState_zslot_width_scan
    {x z : ExtReg}
    {k : ℕ}
    (layout : Gate.PhaseProductLayout x z k)
    (ops : Prog k)
    (i : Fin k)
    (hcap :
      (initSignedLayoutState layout).CanGrowToNeeds
        (scanNeededWidths x z ops)) :
    ((targetSignedLayoutState
      (initSignedLayoutState layout)
      (scanNeededWidths x z ops)).zslot i).width
      =
    commonNeededWidth (scanNeededWidths x z ops) := by
  let stInit := initSignedLayoutState layout
  let need := scanNeededWidths x z ops
  let Wwork := commonNeededWidth need
  have hinit :
      (stInit.zslot i).width =
        (initWidthState x z k).zw i := by
    simpa [stInit] using stInit_zslot_width layout i
  have hscan :
      (initWidthState x z k).zw i ≤ need.zneed i := by
    simpa [need] using
      scanNeededWidths_z_ge_init x z ops i
  have hneed :
      need.zneed i + 1 ≤ Wwork :=
    commonNeededWidth_ge_zneed need i
  have hle : (stInit.zslot i).width ≤ Wwork := by
    rw [hinit]
    omega
  have hgrow :
      (stInit.zslot i).CanGrow
        (Wwork - (stInit.zslot i).width) := by
    exact hcap.2 i
  simpa [stInit, need, Wwork, targetSignedLayoutState] using
    width_growExtRegTo
      (stInit.zslot i) Wwork hle hgrow

/-! =========================================================
    Section 8: Canonical interpolation points
    The compiler uses its own `Point` type, while the algebraic Toom-Cook proof
    lives in `Toom_Cook_formula`. This section bridges the two representations.
========================================================= -/

/-- Alternating integer interpolation points around zero. -/
def alternatingPoint (i : ℕ) : Point :=
  if i % 2 == 0 then Point.int (i / 2 : ℤ) else Point.int (-((i + 1) / 2 : ℤ))

/-- Generate the canonical `2k - 1` interpolation points. -/
def genInterpolationPoints (k : ℕ) : List Point := (List.range (2 * k - 1)).map alternatingPoint

end Shor

namespace Shor
open Gate
open Operations

/-! =========================================================
    Control wrappers for allocation and deallocation

    These structural lemmas are needed to define the controlled recursive
    lowering plan without importing proof modules.
========================================================= -/

/-- Control-phase wrapping leaves allocation gates unchanged. -/
lemma controlPhaseLeaves_allocChunkGate
  {k : ℕ} (ctrl : ℕ) (i : Fin k) (src dst : ExtReg) :
  controlPhaseLeaves ctrl (allocChunkGate i src dst) = allocChunkGate i src dst := by
  unfold allocChunkGate
  by_cases htop : isTopChunk i <;>
    by_cases hδ : extraDelta src dst = 0 <;>
    simp [htop, hδ, controlPhaseLeaves]

/-- Control-phase wrapping leaves deallocation gates unchanged. -/
lemma controlPhaseLeaves_deallocChunkGate
  {k : ℕ} (ctrl : ℕ) (i : Fin k) (src dst : ExtReg) :
  controlPhaseLeaves ctrl (deallocChunkGate i src dst) = deallocChunkGate i src dst := by
  unfold deallocChunkGate
  by_cases htop : isTopChunk i <;>
    by_cases hδ : extraDelta src dst = 0 <;>
    simp [htop, hδ, controlPhaseLeaves]

/-- Control-phase wrapping leaves allocation prefixes unchanged. -/
lemma controlPhaseLeaves_compileSignedAllocationsAux
  {k : ℕ} (ctrl : ℕ) (src dst : LayoutState k) :
  ∀ (n : ℕ) (hn : n ≤ k),
    controlPhaseLeaves ctrl (compileSignedAllocationsAux src dst n hn) =
      compileSignedAllocationsAux src dst n hn := by
  intro n hn
  induction n with
  | zero =>
      simp [compileSignedAllocationsAux_zero, controlPhaseLeaves]
  | succ n ih =>
      rw [compileSignedAllocationsAux_succ (src := src) (dst := dst) (n := n) (hn := hn)]
      let hk' : n ≤ k := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn
      let i : Fin k := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
      simp [controlPhaseLeaves, ih hk',
        controlPhaseLeaves_allocChunkGate]

/-- Control-phase wrapping leaves full allocation unchanged. -/
lemma controlPhaseLeaves_compileSignedAllocations
  {k : ℕ} (ctrl : ℕ) (src dst : LayoutState k) :
  controlPhaseLeaves ctrl (compileSignedAllocations k src dst) =
    compileSignedAllocations k src dst := by
  exact controlPhaseLeaves_compileSignedAllocationsAux ctrl src dst k le_rfl

/-- Control-phase wrapping leaves deallocation prefixes unchanged. -/
lemma controlPhaseLeaves_compileSignedDeallocationsAux
  {k : ℕ} (ctrl : ℕ) (src dst : LayoutState k) :
  ∀ (n : ℕ) (hn : n ≤ k),
    controlPhaseLeaves ctrl (compileSignedDeallocationsAux src dst n hn) =
      compileSignedDeallocationsAux src dst n hn := by
  intro n hn
  induction n with
  | zero =>
      simp [compileSignedDeallocationsAux_zero, controlPhaseLeaves]
  | succ n ih =>
      rw [compileSignedDeallocationsAux_succ (src := src) (dst := dst) (n := n) (hn := hn)]
      let hk' : n ≤ k := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn
      let i : Fin k := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
      simp [controlPhaseLeaves, ih hk',
        controlPhaseLeaves_deallocChunkGate]

/-- Control-phase wrapping leaves full deallocation unchanged. -/
lemma controlPhaseLeaves_compileSignedDeallocations
  {k : ℕ} (ctrl : ℕ) (src dst : LayoutState k) :
  controlPhaseLeaves ctrl (compileSignedDeallocations k src dst) =
    compileSignedDeallocations k src dst := by
  exact controlPhaseLeaves_compileSignedDeallocationsAux ctrl src dst k le_rfl

end Shor


namespace Shor
open Gate
open Operations
open scoped BigOperators

/-! =========================================================
    Section 4: Recursive workspace size model
    The recursive compiler needs reserve space for current-level chunk growth and
    for each descendant phase-product call. These width-only definitions compute
    conservative reserve requirements from logical operand widths.
========================================================= -/

namespace RecursivePhaseWorkspace

/--
A canonical extendable register used only for width calculations.
It has the requested active width and no reserve. Its physical qubit locations
are irrelevant because `scanNeededWidths` and `phaseLimbWidth` depend only on
the active widths.
-/
def widthModelX (wx : ℕ) : ExtReg := ExtReg.ofReg (Reg.interval 0 wx)

/--
A second width-model register placed after `widthModelX`, so the two model
active registers are physically disjoint.
-/
def widthModelZ (wx wz : ℕ) : ExtReg := ExtReg.ofReg (Reg.interval wx wz)

/-- The phase-limb width determined by a pair of logical operand widths. -/
def limbWidth (k wx wz : ℕ) : ℕ := phaseLimbWidth (widthModelX wx) (widthModelZ wx wz) k

/--
The common width required after compiling one level of the operation program.
-/
def nextWidth {k : ℕ} (ops : Prog k) (wx wz : ℕ) : ℕ := nextSignedWidth (widthModelX wx) (widthModelZ wx wz) ops

/--
The two operand sides of a recursive phase-product workspace.
Several reserve formulas are identical except for whether they inspect the
`x` width/component or the `z` width/component. This index lets the common
formula be stated once.
-/
inductive PhaseSide where
  | x
  | z

namespace PhaseSide

/-- Select the logical width for one operand side. -/
def width
    (side : PhaseSide)
    (wx wz : ℕ) :
    ℕ :=
  match side with
  | .x => wx
  | .z => wz

/-- Select the corresponding component from an `(x, z)` reserve pair. -/
def reserveComponent
    (side : PhaseSide)
    (need : ℕ × ℕ) :
    ℕ :=
  match side with
  | .x => need.1
  | .z => need.2

end PhaseSide

/--
The reserve needed merely to grow all chunks on one side at the current
level.
This does not include the reserves needed by descendant recursive calls.
-/
def immediateNeed
    {k : ℕ}
    (side : PhaseSide)
    (ops : Prog k)
    (wx wz : ℕ) :
    ℕ :=
  let Wphase := limbWidth k wx wz
  let Wnext := nextWidth ops wx wz
  ∑ i : Fin k,
    (Wnext - phaseSplitLogicalWidth (side.width wx wz) Wphase k i)

/-- The reserve needed merely to grow all `x` chunks at this level. -/
abbrev immediateXNeed
    {k : ℕ}
    (ops : Prog k)
    (wx wz : ℕ) :
    ℕ :=
  immediateNeed PhaseSide.x ops wx wz

/-- The reserve needed merely to grow all `z` chunks at this level. -/
abbrev immediateZNeed
    {k : ℕ}
    (ops : Prog k)
    (wx wz : ℕ) :
    ℕ :=
  immediateNeed PhaseSide.z ops wx wz

/--
A conservative reserve requirement for the complete recursive compilation.
The result is:
* `.1`: reserve required on the `x` side;
* `.2`: reserve required on the `z` side.
When the next recursive width is not smaller, lowering uses the base
phase-product implementation, so no reserve is required.
Otherwise, every one of the `k` chunks receives:
1. enough reserve for its immediate growth;
2. enough remaining reserve for a complete descendant recursive call.
This bound is intentionally conservative: it provisions recursive workspace
for every child, even if a particular operation program does not invoke a
phase product on every child.
-/
def reserveNeed
    {k : ℕ}
    (ops : Prog k)
    (wx wz : ℕ) :
    ℕ × ℕ :=
  let Wnext := nextWidth ops wx wz
  if _hrec : Wnext < max wx wz then
    let childNeed :=
      reserveNeed ops Wnext Wnext
    (
      immediateXNeed ops wx wz + k * childNeed.1,
      immediateZNeed ops wx wz + k * childNeed.2
    )
  else
    (0, 0)
termination_by max wx wz
decreasing_by
  simpa using _hrec
/-- First projection of `reserveNeed`, exposing the recursive branch for simplification. -/
@[simp] theorem reserveNeed_fst
    {k : ℕ}
    (ops : Prog k)
    (wx wz : ℕ) :
    (reserveNeed ops wx wz).1 =
      if _hrec : nextWidth ops wx wz < max wx wz then
        immediateXNeed ops wx wz + k * (reserveNeed ops (nextWidth ops wx wz) (nextWidth ops wx wz)).1
      else 0 := by
  rw [reserveNeed]
  split_ifs with h <;> rfl
/-- Second projection of `reserveNeed`, exposing the recursive branch for simplification. -/
@[simp] theorem reserveNeed_snd
    {k : ℕ}
    (ops : Prog k)
    (wx wz : ℕ) :
    (reserveNeed ops wx wz).2 =
      if _hrec : nextWidth ops wx wz < max wx wz then
        immediateZNeed ops wx wz + k * (reserveNeed ops (nextWidth ops wx wz) (nextWidth ops wx wz)).2
      else 0 := by
  rw [reserveNeed]
  split_ifs with h <;> rfl

end RecursivePhaseWorkspace

/-! =========================================================
    Section 5: Static workspace-sufficiency predicates
========================================================= -/

/--
Static workspace requirements for an uncontrolled recursive signed phase
product.
This predicate contains only physical-layout and capacity information. It
does not refer to a basis state or quantum state.
-/
structure SignedRecursiveWorkspaceOK
    {k : ℕ}
    (ops : Prog k)
    (x z : ExtReg) :
    Prop where
  /-- The complete owned regions of `x` and `z` do not overlap. -/
  owned_disjoint : ExtReg.OwnedDisjoint x z
  /-- `x.reserve` is large enough for the complete recursive compilation. -/
  x_reserve_sufficient :
    (RecursivePhaseWorkspace.reserveNeed ops x.width z.width).1 ≤ x.capacity
  /-- `z.reserve` is large enough for the complete recursive compilation. -/
  z_reserve_sufficient :
    (RecursivePhaseWorkspace.reserveNeed ops x.width z.width).2 ≤ z.capacity

/-! =========================================================
    Section 6: Canonical recursive step construction
    The canonical step builds a phase-product layout whose child chunks have
    exactly the next recursive width and enough reserve for all descendant calls.
========================================================= -/

namespace RecursivePhaseWorkspace

/--
Reserve required by the `i`th child on one operand side.
The first summand is consumed by the current compilation level. The second
summand remains available to the recursive child.
-/
def requiredChildReserve
    {k : ℕ}
    (side : PhaseSide)
    (ops : Prog k)
    (wx wz : ℕ)
    (i : Fin k) : ℕ :=
  let Wphase := limbWidth k wx wz
  let Wnext := nextWidth ops wx wz
  let childNeed := side.reserveComponent (reserveNeed ops Wnext Wnext)
  (Wnext - phaseSplitLogicalWidth (side.width wx wz) Wphase k i) + childNeed

/-- Reserve required by the `i`th `x` child. -/
abbrev requiredXChildReserve
    {k : ℕ}
    (ops : Prog k)
    (wx wz : ℕ)
    (i : Fin k) : ℕ :=
  requiredChildReserve PhaseSide.x ops wx wz i

/-- Reserve required by the `i`th `z` child. -/
abbrev requiredZChildReserve
    {k : ℕ}
    (ops : Prog k)
    (wx wz : ℕ)
    (i : Fin k) : ℕ :=
  requiredChildReserve PhaseSide.z ops wx wz i

/-- Summing child requirements gives immediate need plus one descendant reserve for each child. -/
lemma requiredChildReserve_sum
    {k : ℕ}
    (side : PhaseSide)
    (ops : Prog k)
    (wx wz : ℕ) :
    (List.ofFn (requiredChildReserve side ops wx wz)).sum =
    immediateNeed side ops wx wz + k * side.reserveComponent (reserveNeed ops (nextWidth ops wx wz) (nextWidth ops wx wz)) := by
  rw [List.sum_ofFn]
  simp only [requiredChildReserve, immediateNeed]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

/-- Sum formula for `x` child reserve requirements. -/
lemma requiredXChildReserve_sum
    {k : ℕ}
    (ops : Prog k)
    (wx wz : ℕ) :
    (List.ofFn (requiredXChildReserve ops wx wz)).sum =
    immediateXNeed ops wx wz + k * (reserveNeed ops (nextWidth ops wx wz) (nextWidth ops wx wz)).1 := by
  exact requiredChildReserve_sum (side := PhaseSide.x) ops wx wz

/-- Sum formula for `z` child reserve requirements. -/
lemma requiredZChildReserve_sum
    {k : ℕ}
    (ops : Prog k)
    (wx wz : ℕ) :
    (List.ofFn (requiredZChildReserve ops wx wz)).sum =
    immediateZNeed ops wx wz + k * (reserveNeed ops (nextWidth ops wx wz) (nextWidth ops wx wz)).2 := by
  exact requiredChildReserve_sum (side := PhaseSide.z) ops wx wz

end RecursivePhaseWorkspace

namespace ReserveBudget

/-- Last child index, used as the deterministic recipient for reserve slack. -/
def topIndex {k : ℕ} (hk : 0 < k) : Fin k := ⟨k - 1, by omega⟩

/-- Add all unused parent reserve to the top child while keeping other child requirements fixed. -/
def fillSlack
    {k : ℕ}
    (hk : 0 < k)
    (capacity : ℕ)
    (required : Fin k → ℕ) :
    Fin k → ℕ :=
  let top := topIndex hk
  let used := (List.ofFn required).sum
  Function.update
    required
    top
    (required top + (capacity - used))

/-- The slack-filled child reserve sizes sum exactly to the parent capacity. -/
lemma fillSlack_sum
    {k : ℕ}
    (hk : 0 < k)
    (capacity : ℕ)
    (required : Fin k → ℕ)
    (hfit :
      (List.ofFn required).sum ≤ capacity) :
    (List.ofFn
      (fillSlack hk capacity required)).sum
      =
    capacity := by
  have hused : (List.ofFn required).sum = ∑ x : Fin k, required x := List.sum_ofFn
  simp only [fillSlack, List.sum_ofFn]
  rw [Finset.sum_update_of_mem (Finset.mem_univ (topIndex hk)),
    ← Finset.erase_eq]
  have hAT : required (topIndex hk) + ∑ x ∈ Finset.univ.erase (topIndex hk), required x = ∑ x : Fin k, required x :=
    Finset.add_sum_erase _ _ (Finset.mem_univ _)
  have hSle : ∑ x : Fin k, required x ≤ capacity := by
    rw [← hused]; exact hfit
  omega

/-- Every child receives at least its required reserve after slack filling. -/
lemma required_le_fillSlack
    {k : ℕ}
    (hk : 0 < k)
    (capacity : ℕ)
    (required : Fin k → ℕ)
    (i : Fin k) :
    required i ≤ fillSlack hk capacity required i := by
  simp only [fillSlack, Function.update_apply]
  by_cases h : i = topIndex hk
  · rw [if_pos h, h]; exact Nat.le_add_right _ _
  · rw [if_neg h]

/-- Build a concrete reserve budget from per-child requirements that fit in the parent reserve. -/
def ofRequirements
    {parent : ExtReg}
    {k : ℕ}
    (hk : 0 < k)
    (required : Fin k → ℕ)
    (hfit : (List.ofFn required).sum ≤ parent.capacity) :
    ReserveBudget parent k :=
  {
    size := fillSlack hk parent.capacity required
    total := by exact fillSlack_sum hk parent.capacity required hfit
  }

/-- Each concrete child-reserve slice has at least the requested size. -/
theorem required_le_childReserve_size
    {parent : ExtReg}
    {k : ℕ}
    (hk : 0 < k)
    (required : Fin k → ℕ)
    (hfit :
      (List.ofFn required).sum
        ≤ parent.capacity)
    (i : Fin k) :
    required i ≤
      regSize ((ofRequirements hk required hfit).childReserve i) := by
  set budget := ofRequirements hk required hfit with hbudget
  -- `budget.size i` is exactly the slack-filled requirement, ≥ `required i`.
  have h1 : required i ≤ budget.size i := by
    show required i ≤ fillSlack hk parent.capacity required i
    exact required_le_fillSlack hk parent.capacity required i
  -- The `i`th slice starts at `offset i` and has room for `size i`.
  have hbound : budget.offset i + budget.size i ≤ parent.capacity := by
    have hi : i.1 < (List.ofFn budget.size).length := by rw [List.length_ofFn]; exact i.2
    have hstep : ((List.ofFn budget.size).take (i.1 + 1)).sum = budget.offset i + budget.size i := by
      unfold ReserveBudget.offset; rw [List.sum_take_succ _ _ hi, List.getElem_ofFn]
    have hle : ((List.ofFn budget.size).take (i.1 + 1)).sum ≤ (List.ofFn budget.size).sum := by
      conv_rhs =>
        rw [← List.take_append_drop (i.1 + 1) (List.ofFn budget.size)]
      rw [List.sum_append]; exact Nat.le_add_right _ _
    have htot : (List.ofFn budget.size).sum = parent.capacity := budget.total
    omega
  -- Hence the physical `take` does not truncate: the slice has size `size i`.
  have h2 : regSize (budget.childReserve i) = budget.size i := by
    have hcap : parent.reserve.qubits.length = parent.capacity := rfl
    simp only [regSize, Reg.width, ReserveBudget.childReserve, Reg.take,
      Reg.drop, List.length_take, List.length_drop]
    omega
  rw [h2]; exact h1

end ReserveBudget

/--
The information produced at one deterministic recursive signed phase-product
step.
-/
structure CanonicalSignedStep
    {k : ℕ}
    (ops : Prog k)
    (x z : ExtReg) where
  layout : Gate.PhaseProductLayout x z k
  capacity : (initSignedLayoutState layout).CanGrowToNeeds (scanNeededWidths x z ops)
  /--
  After current-level growth, every paired child has enough remaining
  workspace for the complete descendant recursion.
  -/
  childWorkspace :
    let src :=
      initSignedLayoutState layout
    let dst :=
      targetSignedLayoutState src (scanNeededWidths x z ops)
    ∀ i : Fin k,
      SignedRecursiveWorkspaceOK ops (dst.xslot i) (dst.zslot i)
  /--
  Every phase-product leaf emitted by this level has the recursive width
  `nextSignedWidth x z ops`.
  -/
  childInputSize :
    let src :=
      initSignedLayoutState layout
    let dst :=
      targetSignedLayoutState src (scanNeededWidths x z ops)
    ∀ i : Fin k,
      phaseInputSize
        (dst.xslot i)
        (dst.zslot i)
        =
      nextSignedWidth x z ops

/-- Canonical deterministic construction of one recursive signed phase-product step. -/
noncomputable def canonicalSignedStep
    {k : ℕ}
    (hk : 1 < k)
    (ops : Prog k)
    (x z : ExtReg)
    (hrec : nextSignedWidth x z ops < phaseInputSize x z)
    (hworkspace : SignedRecursiveWorkspaceOK ops x z) :
    CanonicalSignedStep ops x z := by
  let reqX : Fin k → ℕ :=
    RecursivePhaseWorkspace.requiredXChildReserve
      ops x.width z.width
  let reqZ : Fin k → ℕ :=
    RecursivePhaseWorkspace.requiredZChildReserve
      ops x.width z.width
  have hkpos : 0 < k := by omega
  -- The width-model registers reproduce the operands' active widths.
  have hwmX :
      (RecursivePhaseWorkspace.widthModelX x.width).width = x.width := by
    simp [RecursivePhaseWorkspace.widthModelX, ExtReg.width, ExtReg.ofReg,
      regSize, Reg.width, Reg.interval]
  have hwmZ :
      (RecursivePhaseWorkspace.widthModelZ x.width z.width).width = z.width := by
    simp [RecursivePhaseWorkspace.widthModelZ, ExtReg.width, ExtReg.ofReg,
      regSize, Reg.width, Reg.interval]
  -- Consequently every width-only quantity matches the concrete operands.
  have hlimb :
      phaseLimbWidth
        (RecursivePhaseWorkspace.widthModelX x.width)
        (RecursivePhaseWorkspace.widthModelZ x.width z.width) k
        = phaseLimbWidth x z k := by
    simp only [phaseLimbWidth, hwmX, hwmZ]
  have hinit :
      initWidthState
        (RecursivePhaseWorkspace.widthModelX x.width)
        (RecursivePhaseWorkspace.widthModelZ x.width z.width) k
        = initWidthState x z k := by
    simp only [initWidthState, hwmX, hwmZ, hlimb]
  have hnext :
      RecursivePhaseWorkspace.nextWidth ops x.width z.width
        = nextSignedWidth x z ops := by
    simp only [RecursivePhaseWorkspace.nextWidth, nextSignedWidth,
      scanNeededWidths, hinit]
  -- The recursion guard `hrec` transfers to the width-model formulation.
  have hrec' :
      RecursivePhaseWorkspace.nextWidth ops x.width z.width
        < max x.width z.width := by
    rw [hnext]; exact hrec
  have hxfit :
      (List.ofFn reqX).sum ≤ x.capacity := by
    show (List.ofFn
      (RecursivePhaseWorkspace.requiredXChildReserve
        ops x.width z.width)).sum ≤ x.capacity
    rw [RecursivePhaseWorkspace.requiredXChildReserve_sum]
    have hres := hworkspace.x_reserve_sufficient
    rw [RecursivePhaseWorkspace.reserveNeed_fst, dif_pos hrec'] at hres
    exact hres
  have hzfit :
      (List.ofFn reqZ).sum ≤ z.capacity := by
    show (List.ofFn
      (RecursivePhaseWorkspace.requiredZChildReserve
        ops x.width z.width)).sum ≤ z.capacity
    rw [RecursivePhaseWorkspace.requiredZChildReserve_sum]
    have hres := hworkspace.z_reserve_sufficient
    rw [RecursivePhaseWorkspace.reserveNeed_snd, dif_pos hrec'] at hres
    exact hres
  let xBudget : ReserveBudget x k := ReserveBudget.ofRequirements hkpos reqX hxfit
  let zBudget : ReserveBudget z k := ReserveBudget.ofRequirements hkpos reqZ hzfit
  let xSplit : PhaseSplitLayout x k (phaseLimbWidth x z k) :=
    PhaseSplitLayout.ofBudget x k (phaseLimbWidth x z k) (phaseLimbWidth_valid_left x z hkpos) xBudget
  let zSplit : PhaseSplitLayout z k (phaseLimbWidth x z k) :=
    PhaseSplitLayout.ofBudget z k (phaseLimbWidth x z k) (phaseLimbWidth_valid_right x z hkpos) zBudget
  have hlimb' : RecursivePhaseWorkspace.limbWidth k x.width z.width = phaseLimbWidth x z k := hlimb
  have child_owned_subset :
      ∀ {parent : ExtReg} {W : ℕ} (split : PhaseSplitLayout parent k W) (i : Fin k),
        (split.child i).ownedQubits ⊆ parent.ownedQubits := by
    intro parent W split i qbit hq
    change
      qbit ∈ (phaseChunkActive parent k W i).qubits ++ (split.reserve i).qubits at hq
    change qbit ∈ parent.active.qubits ++ parent.reserve.qubits
    rw [List.mem_append] at hq ⊢
    rcases hq with hqActive | hqReserve
    · left
      simp only [phaseChunkActive, Reg.take, Reg.drop] at hqActive
      exact List.mem_of_mem_drop (List.mem_of_mem_take hqActive)
    · right
      have hqFlatten :
          qbit ∈
            (List.ofFn fun j : Fin k =>
              (split.reserve j).qubits).flatten := by
        rw [List.mem_flatten]
        refine ⟨(split.reserve i).qubits, ?_, hqReserve⟩
        simp
      rw [split.reserve_partition] at hqFlatten
      exact hqFlatten
  let layout :
      Gate.PhaseProductLayout x z k :=
    {
      xSplit := xSplit
      zSplit := zSplit
      cross_owned_disjoint := by
        intro i j; unfold ExtReg.OwnedDisjoint
        exact List.disjoint_of_subset_left (child_owned_subset xSplit i)
          (List.disjoint_of_subset_right (child_owned_subset zSplit j) hworkspace.owned_disjoint)
    }
  have hreqX_formula
      (i : Fin k) :
      reqX i = (nextSignedWidth x z ops - (xSplit.child i).width) +
        (RecursivePhaseWorkspace.reserveNeed ops (nextSignedWidth x z ops) (nextSignedWidth x z ops)).1 := by
    dsimp [
      reqX,
      RecursivePhaseWorkspace.requiredXChildReserve,
      RecursivePhaseWorkspace.requiredChildReserve,
      RecursivePhaseWorkspace.PhaseSide.width,
      RecursivePhaseWorkspace.PhaseSide.reserveComponent
    ]
    rw [hlimb', hnext, xSplit.child_width]
  have hreqZ_formula
      (i : Fin k) :
      reqZ i = (nextSignedWidth x z ops - (zSplit.child i).width) +
        (RecursivePhaseWorkspace.reserveNeed ops (nextSignedWidth x z ops) (nextSignedWidth x z ops)).2 := by
    dsimp [
      reqZ,
      RecursivePhaseWorkspace.requiredZChildReserve,
      RecursivePhaseWorkspace.requiredChildReserve,
      RecursivePhaseWorkspace.PhaseSide.width,
      RecursivePhaseWorkspace.PhaseSide.reserveComponent
    ]
    rw [hlimb', hnext, zSplit.child_width]
  have hxChildCapacity
      (i : Fin k) :
      reqX i ≤ (xSplit.child i).capacity := by
    have h := ReserveBudget.required_le_childReserve_size (parent := x) hkpos reqX hxfit i
    simpa [
      xSplit,
      PhaseSplitLayout.ofBudget,
      PhaseSplitLayout.child,
      ExtReg.withReserve,
      ExtReg.capacity
    ] using h
  have hzChildCapacity
      (i : Fin k) :
      reqZ i ≤ (zSplit.child i).capacity := by
    have h := ReserveBudget.required_le_childReserve_size (parent := z) hkpos reqZ hzfit i
    simpa [
      zSplit,
      PhaseSplitLayout.ofBudget,
      PhaseSplitLayout.child,
      ExtReg.withReserve,
      ExtReg.capacity
    ] using h
  have hcapacity :
      (initSignedLayoutState layout).CanGrowToNeeds
        (scanNeededWidths x z ops) := by
    change
      LayoutState.CanGrowTo
        (initSignedLayoutState layout)
        (nextSignedWidth x z ops)
    constructor
    · intro i
      change nextSignedWidth x z ops - (xSplit.child i).width ≤ (xSplit.child i).capacity
      have hsize := hxChildCapacity i
      rw [hreqX_formula i] at hsize
      omega
    · intro i
      change nextSignedWidth x z ops - (zSplit.child i).width ≤ (zSplit.child i).capacity
      have hsize := hzChildCapacity i
      rw [hreqZ_formula i] at hsize
      omega
  refine
    {
      layout := layout
      capacity := hcapacity
      childWorkspace := ?_
      childInputSize := ?_
    }
  · dsimp only
    intro i
    let src : LayoutState k := initSignedLayoutState layout
    let dst : LayoutState k := targetSignedLayoutState src (scanNeededWidths x z ops)
    have howned :
        ExtReg.OwnedDisjoint
          (dst.xslot i)
          (dst.zslot i) := by
      have hpair := targetSignedLayoutState_owned_disjoint layout (scanNeededWidths x z ops)
      simpa [src, dst] using hpair.2.2 i i
    have hxgrow :
        (xSplit.child i).CanGrow
          (nextSignedWidth x z ops -
            (xSplit.child i).width) := by
      have h := hcapacity.1 i
      change (xSplit.child i).CanGrow (nextSignedWidth x z ops - (xSplit.child i).width) at h
      exact h
    have hzgrow :
        (zSplit.child i).CanGrow
          (nextSignedWidth x z ops -
            (zSplit.child i).width) := by
      have h := hcapacity.2 i
      change (zSplit.child i).CanGrow (nextSignedWidth x z ops - (zSplit.child i).width) at h
      exact h
    have hxcapacity :
        (dst.xslot i).capacity
          =
        (xSplit.child i).capacity -
          (nextSignedWidth x z ops -
            (xSplit.child i).width) := by
      change
        ((xSplit.child i).grow
          (nextSignedWidth x z ops -
            (xSplit.child i).width)).capacity
          =
        (xSplit.child i).capacity -
          (nextSignedWidth x z ops -
            (xSplit.child i).width)
      exact
        ExtReg.capacity_grow
          (xSplit.child i)
          (nextSignedWidth x z ops -
            (xSplit.child i).width)
          hxgrow
    have hzcapacity :
        (dst.zslot i).capacity
          =
        (zSplit.child i).capacity -
          (nextSignedWidth x z ops -
            (zSplit.child i).width) := by
      change
        ((zSplit.child i).grow
          (nextSignedWidth x z ops -
            (zSplit.child i).width)).capacity
          =
        (zSplit.child i).capacity -
          (nextSignedWidth x z ops -
            (zSplit.child i).width)
      exact
        ExtReg.capacity_grow
          (zSplit.child i)
          (nextSignedWidth x z ops -
            (zSplit.child i).width)
          hzgrow
    have hxwidth :
        (dst.xslot i).width =
          nextSignedWidth x z ops := by
      simpa [src, dst, nextSignedWidth] using targetSignedLayoutState_xslot_width_scan layout ops i hcapacity
    have hzwidth :
        (dst.zslot i).width =
          nextSignedWidth x z ops := by
      simpa [src, dst, nextSignedWidth] using targetSignedLayoutState_zslot_width_scan layout ops i hcapacity
    refine
      {
        owned_disjoint := howned
        x_reserve_sufficient := ?_
        z_reserve_sufficient := ?_
      }
    · rw [hxwidth, hzwidth, hxcapacity]
      have hsize := hxChildCapacity i
      rw [hreqX_formula i] at hsize
      omega
    · rw [hxwidth, hzwidth, hzcapacity]
      have hsize := hzChildCapacity i
      rw [hreqZ_formula i] at hsize
      omega
  · dsimp only
    intro i
    let src : LayoutState k := initSignedLayoutState layout
    let dst : LayoutState k := targetSignedLayoutState src (scanNeededWidths x z ops)
    have hxwidth :
        (dst.xslot i).width =
          nextSignedWidth x z ops := by
      simpa [src, dst, nextSignedWidth] using targetSignedLayoutState_xslot_width_scan layout ops i hcapacity
    have hzwidth :
        (dst.zslot i).width =
          nextSignedWidth x z ops := by
      simpa [src, dst, nextSignedWidth] using targetSignedLayoutState_zslot_width_scan layout ops i hcapacity
    unfold phaseInputSize
    rw [hxwidth, hzwidth, max_self]


/-- Every child register selected by a phase split is physically owned by its parent. -/
lemma PhaseSplitLayout.child_owned_subset_parent
    {parent : ExtReg}
    {k W : ℕ}
    (split : PhaseSplitLayout parent k W)
    (i : Fin k) :
    (split.child i).ownedQubits ⊆ parent.ownedQubits := by
  intro qbit hq
  change qbit ∈ (phaseChunkActive parent k W i).qubits ++ (split.reserve i).qubits at hq
  change qbit ∈ parent.active.qubits ++ parent.reserve.qubits
  rw [List.mem_append] at hq ⊢
  rcases hq with hqActive | hqReserve
  · left
    simp only [phaseChunkActive, Reg.take, Reg.drop] at hqActive
    exact List.mem_of_mem_drop (List.mem_of_mem_take hqActive)
  · right
    have hqFlatten :
        qbit ∈ (List.ofFn fun j : Fin k => (split.reserve j).qubits).flatten := by
      rw [List.mem_flatten]
      refine ⟨(split.reserve i).qubits, ?_, hqReserve⟩
      simp
    rw [split.reserve_partition] at hqFlatten
    exact hqFlatten

/-- If a control qubit is outside the parent operands, it is outside every layout child. -/
lemma Gate.PhaseProductLayout.controlDisjoint_of_ctrlDisjoint
    {x z : ExtReg}
    {k : ℕ}
    (layout : Gate.PhaseProductLayout x z k)
    {ctrl : ℕ}
    (hctrl : ExtReg.CtrlDisjoint ctrl x z) :
    layout.ControlDisjoint ctrl := by
  constructor
  · intro i hmem
    exact hctrl.1 (PhaseSplitLayout.child_owned_subset_parent layout.xSplit i hmem)
  · intro i hmem
    exact hctrl.2 (PhaseSplitLayout.child_owned_subset_parent layout.zSplit i hmem)

/--
Static workspace requirements for a controlled recursive signed phase
product.
In addition to the uncontrolled conditions, the control qubit must be outside
both operands' complete owned regions, including their future workspace.
-/
structure CSignedRecursiveWorkspaceOK
    {k : ℕ}
    (ops : Prog k)
    (ctrl : ℕ)
    (x z : ExtReg) :
    Prop extends SignedRecursiveWorkspaceOK ops x z where
  control_disjoint : ExtReg.CtrlDisjoint ctrl x z

/-! =========================================================
    Section 7: Cleanliness of the complete reserves
========================================================= -/

/--
Both complete reserve registers are zero in a basis state.
Using `x.capacity` and `z.capacity` means that `FreshFor` covers all of each
reserve, rather than only the bits needed by the first compilation level.
-/
def RecursiveWorkspaceCleanBasis
    {Basis : Type u}
    [RegEncoding Basis]
    (x z : ExtReg)
    (b : Basis) :
    Prop :=
  ExtReg.FreshFor x x.capacity b ∧ ExtReg.FreshFor z z.capacity b

/--
An arbitrary quantum state supported on basis states whose entire `x` and `z`
reserves are zero.
The active data registers may be in an arbitrary superposition. Only the
reserve qubits are constrained.
-/
abbrev RecursiveWorkspaceCleanState
    (qs : QSemantics) [RegEncoding qs.Basis] (x z : ExtReg) : qs.State → Prop :=
  CleanClosure (fun b => RecursiveWorkspaceCleanBasis x z b)

/-! =========================================================
    Section 8: Combined public workspace preconditions
========================================================= -/

/--
The complete public workspace precondition for an uncontrolled signed phase
product.
-/
structure SignedRecursiveWorkspaceStateOK
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {k : ℕ}
    (ops : Prog k)
    (x z : ExtReg)
    (ψ : qs.State) :
    Prop where
  static : SignedRecursiveWorkspaceOK ops x z
  clean : RecursiveWorkspaceCleanState qs x z ψ

/--
The complete public workspace precondition for a controlled signed phase
product.
-/
structure CSignedRecursiveWorkspaceStateOK
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {k : ℕ}
    (ops : Prog k)
    (ctrl : ℕ)
    (x z : ExtReg)
    (ψ : qs.State) :
    Prop where
  static :
    CSignedRecursiveWorkspaceOK
      ops ctrl x z
  clean :
    RecursiveWorkspaceCleanState
      qs x z ψ

end Shor


