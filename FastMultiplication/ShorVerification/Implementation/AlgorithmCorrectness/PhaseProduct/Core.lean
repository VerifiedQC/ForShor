import FastMultiplication.ShorVerification.Framework.Semantics.GateSemantics
import FastMultiplication.ShorVerification.Implementation.MathBackbone.Table_Generation.Core.Coverage
import Mathlib.Data.Finset.Basic

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

/-! =========================================================
    Section 9: Legacy ordinary-register modular helpers
========================================================= -/

/-- Ordinary-register modular reduction retained for legacy arithmetic gate statements. -/
def tcMod (r : Reg) (z : ℤ) : ℕ := Int.toNat (z % (ASize r : ℤ))

/-- Two's-complement negation value for an ordinary register. -/
def tcNegVal (r : Reg) (x : ℕ) : ℕ := tcMod r (-(x : ℤ))

/-- Ordinary-register value update for an add-scaled arithmetic step. -/
def tcAddScaledVal
    {β : Type} [RegEncoding β]
    (dst src : Reg) (negSrc : Bool) (sh : ℕ) (b : β) : ℕ :=
  let sgn : ℤ := if negSrc then -1 else 1
  tcMod dst
    ((RegEncoding.toNat dst b : ℤ) +
      sgn * (RegEncoding.toNat src b : ℤ) * ((2 : ℤ) ^ sh))
variable (qs : QSemantics) [RegEncoding qs.Basis]

/-! =========================================================
    Section 10: Source-row semantics
========================================================= -/

/-- How the original source basis should be read when forming chunk rows:
    lower chunks are ordinary radix digits, while the top chunk is signed. -/

def sourceChunkXInt
  (st : LayoutState k) (i : Fin k) (b : qs.Basis) : ℤ :=
  if isTopChunk i then
    extToInt (st.xslot i) b
  else
    (ExtReg.toNat (st.xslot i) b : ℤ)

/-- Same mixed source interpretation for the `z` slots. -/
def sourceChunkZInt
  (st : LayoutState k) (i : Fin k) (b : qs.Basis) : ℤ :=
  if isTopChunk i then
    extToInt (st.zslot i) b
  else
    (ExtReg.toNat (st.zslot i) b : ℤ)

/-- Row evaluation of `x` against the original basis:
    lower chunks contribute as unsigned digits, top chunk as signed. -/

def evalRowX
  (st : LayoutState k) (r : Register k) (b : qs.Basis) : ℤ :=
  ∑ j : Fin k, r j * sourceChunkXInt (qs := qs) st j b

/-- Row evaluation of `z` against the original basis:
    lower chunks contribute as unsigned digits, top chunk as signed. -/

def evalRowZ
  (st : LayoutState k) (r : Register k) (b : qs.Basis) : ℤ :=
  ∑ j : Fin k, r j * sourceChunkZInt (qs := qs) st j b

/-! =========================================================
    Section 10: Encoding invariants
========================================================= -/

/-- Two-layout version: the current widened machine state is read signed on `dst`,
    while the original basis is interpreted using the mixed chunk semantics on `src`. -/

def EncodesStateFrom
  (src dst : LayoutState k) (σ : State k) (b0 b : qs.Basis) : Prop :=
  (∀ i : Fin k,
    extToInt (dst.xslot i) b
      = evalRowX (qs := qs) src (σ i) b0) ∧
  (∀ i : Fin k,
    extToInt (dst.zslot i) b
      = evalRowZ (qs := qs) src (σ i) b0)

/-- `EncodesStateFrom` plus signed-fit obligations for every widened destination slot. -/
def EncodesStateFromFits
  (qs : QSemantics) [RegEncoding qs.Basis] {k : ℕ}
  (src dst : LayoutState k) (σ : State k) (b0 b : qs.Basis) : Prop :=
  EncodesStateFrom (qs := qs) src dst σ b0 b ∧
  (∀ i : Fin k,
    FitsSignedWidth (ExtReg.width (dst.xslot i))
      (evalRowX (qs := qs) src (σ i) b0)) ∧
  (∀ i : Fin k,
    FitsSignedWidth (ExtReg.width (dst.zslot i))
      (evalRowZ (qs := qs) src (σ i) b0))

/-- Current symbolic row values fit one sign bit beyond the scanned unsigned widths. -/
def WidthStateSoundPlus
    (qs : QSemantics) [RegEncoding qs.Basis] {k : ℕ}
    (src : LayoutState k) (cur : WidthState k) (σ : State k) (b0 : qs.Basis) : Prop :=
  (∀ i : Fin k,
    FitsSignedWidth (cur.xw i + 1) (evalRowX (qs := qs) src (σ i) b0))
    ∧
  (∀ i : Fin k,
    FitsSignedWidth (cur.zw i + 1) (evalRowZ (qs := qs) src (σ i) b0))

/-- The concrete destination layout is at least as wide as the symbolic scan says. -/
def WidthStateDominatedByLayout {k : ℕ} (cur : WidthState k) (dst : LayoutState k) : Prop :=
  (∀ i : Fin k, cur.xw i + 1 ≤ (dst.xslot i).width) ∧ (∀ i : Fin k, cur.zw i + 1 ≤ (dst.zslot i).width)

/-- Main body invariant: encoded rows, symbolic fit bounds, and layout domination. -/
def EncodesStateFromWithWidths
  (qs : QSemantics) [RegEncoding qs.Basis] {k : ℕ}
  (src dst : LayoutState k) (cur : WidthState k) (σ : State k) (b0 b : qs.Basis) : Prop :=
  EncodesStateFrom (qs := qs) src dst σ b0 b ∧
  WidthStateSoundPlus (qs := qs) src cur σ b0 ∧
  WidthStateDominatedByLayout cur dst

/-! =========================================================
    Section 11: Phase scalar
========================================================= -/

/-- The accumulated scalar now uses the same mixed source-row semantics as
    `EncodesStateFrom`, so the body lemma stays aligned with the invariant. -/
noncomputable def phaseScalarFrom
  (k : ℕ) (phi : ℝ) (coeff : Fin (q k) → ℚ)
  (st : LayoutState k) (b0 : qs.Basis) :
  (pts : List Point) → (n : ℕ) → (hn : n + pts.length = q k) → ℂ
| [], n, hn => 1
| pt :: pts, n, hn =>
    let l : Fin (q k) := ⟨n, by
      have hlt : n < n + (pt :: pts).length := by
        simp
      aesop
    ⟩
    let hn' : n + 1 + pts.length = q k := by
      simp at hn
      omega
    Complex.exp
      ((phi * ((coeff l : ℚ) : ℝ)) * Complex.I *
        (((evalRowX (qs := qs) st (expectedRow (k := k) pt) b0 : ℤ) : ℂ) *
         (((evalRowZ (qs := qs) st (expectedRow (k := k) pt) b0 : ℤ) : ℂ))))
    * phaseScalarFrom k phi coeff st b0 pts (n + 1) hn'

/-- All reserve bits that would be activated when growing to `W` are zero in basis `b`. -/
def LayoutState.CleanForGrowth {Basis : Type u} [RegEncoding Basis] {k : ℕ} (src : LayoutState k) (W : ℕ) (b : Basis) : Prop :=
  (∀ i, ExtReg.FreshFor (src.xslot i) (W - (src.xslot i).width) b) ∧
  (∀ i, ExtReg.FreshFor (src.zslot i) (W - (src.zslot i).width) b)

/-- Concrete workspace hypothesis for running allocation gates from `src` to the scanned width. -/
def CompilerWorkspaceOK {Basis : Type u} [RegEncoding Basis] {k : ℕ} (src : LayoutState k) (need : NeededWidths k) (b : Basis) : Prop :=
  let Wwork := commonNeededWidth need
  src.CanGrowTo Wwork ∧ src.CleanForGrowth Wwork b

/-- Linear closure of basis states whose relevant compiler workspace is clean
(`CleanClosure` at the compiler-workspace-clean predicate). -/
abbrev CleanWorkspaceState (qs : QSemantics) [RegEncoding qs.Basis] {k : ℕ}
    (src : LayoutState k) (need : NeededWidths k) : qs.State → Prop :=
  CleanClosure (fun b => CompilerWorkspaceOK src need b)

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
