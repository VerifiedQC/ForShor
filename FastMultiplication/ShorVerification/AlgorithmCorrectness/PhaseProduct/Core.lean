import FastMultiplication.ShorVerification.Basic
import FastMultiplication.ShorVerification.MathBackbone.Table_Generation.Table_Blocks
import Mathlib.Data.Finset.Basic

/-!
# Phase-Product Compiler Core

This file defines the bookkeeping used by the phase-product compiler: layouts,
width scans, annotated source operations, allocation/deallocation gates, and
encoded-state predicates.  The low-level `LowGate` target syntax lives in
`AbstractMachine/LowGate.lean`.
-/

namespace Shor
open Gate
open Operations
open scoped BigOperators

/-! =========================================================
    Section 1: Layout states and width bookkeeping
========================================================= -/
/-- Mutable slot assignment state for both `x` and `z` blocks. -/
structure LayoutState (k : ℕ) where
  xslot : Fin k → ExtReg
  zslot : Fin k → ExtReg

/-- Width bookkeeping only: current logical widths of each chunk. -/
structure WidthState (k : ℕ) where
  xw : Fin k → ℕ
  zw : Fin k → ℕ

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

structure NeededWidths (k : ℕ) where
  xneed : Fin k → ℕ
  zneed : Fin k → ℕ

def mergeNeededWidths {k : ℕ} (a b : NeededWidths k) : NeededWidths k where
  xneed := fun i => max (a.xneed i) (b.xneed i)
  zneed := fun i => max (a.zneed i) (b.zneed i)

def widthsOfState {k : ℕ} (st : WidthState k) : NeededWidths k where
  xneed := st.xw
  zneed := st.zw


/--
Lower-limb width for the top-heavy phase layout.

This deliberately uses floor division. The lower `k - 1` limbs have width `w / k`,
and the most significant limb absorbs all remaining bits.
For example, `w = 5`, `k = 4` gives widths `1, 1, 1, 2`.
-/
def phaseLimbWidthOfWidth (w k : ℕ) : ℕ :=
  w / k

/--
Common radix width for decomposing both operands.

Use `min`, not `max`: the lower limbs must fit inside both operands.
The larger operand simply gets a larger top chunk.
-/
def phaseLimbWidth (x z : ExtReg) (k : ℕ) : ℕ :=
  min (phaseLimbWidthOfWidth (ExtReg.width x) k)
      (phaseLimbWidthOfWidth (ExtReg.width z) k)

/-! =========================================================
    Section 2: Top-heavy phase splitting parameters
========================================================= -/

/-- The most significant chunk is the last chunk. -/
def isTopChunk {k : ℕ} (i : Fin k) : Prop :=
  i.1 + 1 = k

instance {k : ℕ} (i : Fin k) : Decidable (isTopChunk i) := by
  unfold isTopChunk
  infer_instance

def phaseSplitLogicalWidth (w W k : ℕ) (i : Fin k) : ℕ :=
  if isTopChunk i then
    w - i.1 * W
  else
    W


/-! =========================================================
    Section 3: Abstract `ExtReg` split interface
========================================================= -/
def ValidPhaseSplit (e : ExtReg) (k W : ℕ) : Prop :=
  0 < k ∧ (k - 1) * W ≤ ExtReg.width e

class ExtRegSplitSemantics
    (Basis : Type u)
    [RegEncoding Basis]
    [ExtRegEncoding Basis] where
  split : ExtReg → (k W : ℕ) → Fin k → ExtReg

  split_width :
    ∀ (e : ExtReg) (k W : ℕ) (i : Fin k),
      ValidPhaseSplit e k W →
      ExtReg.width (split e k W i)
        =
      phaseSplitLogicalWidth (ExtReg.width e) W k i

  split_disjoint :
    ∀ (e : ExtReg) (k W : ℕ) (i j : Fin k),
      i ≠ j →
      Disjoint (split e k W i).base (split e k W j).base

  split_disjoint_of_disjoint :
    ∀ (x z : ExtReg) (k W : ℕ) (i j : Fin k),
      Disjoint x.base z.base →
      Disjoint (split x k W i).base (split z k W j).base

  split_disjoint_reg_of_disjoint :
    ∀ (e : ExtReg) (r : Reg) (k W : ℕ) (i : Fin k),
      Disjoint e.base r →
      Disjoint (split e k W i).base r

  split_reconstruct_int :
    ∀ (e : ExtReg) (k W : ℕ) (b : Basis),
      ValidPhaseSplit e k W →
      ((ExtRegEncoding.extToInt e b : ℤ) : ℚ)
        =
      ∑ i : Fin k,
        ((if isTopChunk i then
            ExtRegEncoding.extToInt (split e k W i) b
          else
            (ExtReg.toNat (split e k W i) b : ℤ)) : ℚ)
          * ((2 : ℚ) ^ W) ^ (i : ℕ)

/-- Convenient wrapper for the abstract split operation. -/
def splitExtReg
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (e : ExtReg) (k W : ℕ) (i : Fin k) : ExtReg :=
  ExtRegSplitSemantics.split (Basis:=Basis) e k W i

/--
Integer value of one split chunk.

Lower chunks are unsigned radix digits.
The top chunk is signed.
-/
def splitChunkInt
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    {k : ℕ}
    (e : ExtReg) (W : ℕ) (i : Fin k) (b : Basis) : ℤ :=
  if isTopChunk i then
    ExtRegEncoding.extToInt (splitExtReg (Basis:=Basis) e k W i) b
  else
    (ExtReg.toNat (splitExtReg (Basis:=Basis) e k W i) b : ℤ)


/-! =========================================================
    Section 4: Width scanning and target-width definitions
========================================================= -/

/-- Initial width bookkeeping now uses the uniform lower-limb phase layout. -/
def initWidthState (x z : ExtReg) (k : ℕ) : WidthState k :=
  let W := phaseLimbWidth x z k
  { xw := fun i => phaseSplitLogicalWidth (ExtReg.width x) W k i
    zw := fun i => phaseSplitLogicalWidth (ExtReg.width z) W k i }

/-- Pull the recursion in `scanNeededWidths` out to a top-level helper. -/
def scanNeededWidthsAux {k : ℕ} (cur : WidthState k) (mx : NeededWidths k) :
    List (valid_ops k) → NeededWidths k
  | [] => mx
  | op :: rest =>
      let cur' := updateWidthState cur op
      let mx' := mergeNeededWidths mx (widthsOfState cur')
      scanNeededWidthsAux cur' mx' rest

/-- Scan needed widths using the new initial width state. -/
def scanNeededWidths {k : ℕ} (x z : ExtReg) (ops : List (valid_ops k)) :
    NeededWidths k :=
  scanNeededWidthsAux
    (initWidthState x z k)
    (widthsOfState (initWidthState x z k))
    ops


/-- Common target width so that all chunks are widened to the same size. -/
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
def interpMatrix
  (k : ℕ)
  (pts : Fin (q k) → Point) :
  Matrix (Fin (q k)) (Fin (q k)) ℚ :=
  fun i j => interpEntry k (pts i) j

/-- Row vector `[1, b, b^2, ...]` used for interpolation evaluation. -/
def radixRow (k : ℕ) (b : ℚ) :
  Matrix (Fin 1) (Fin (q k)) ℚ :=
  fun _ j => b ^ (j : ℕ)

/-- Interpolated phase coefficients evaluated at radix `b`. -/
noncomputable def phaseCoeffFromPts
  (k : ℕ)
  (pts : Fin (q k) → Point)
  (b : ℚ) :
  Fin (q k) → ℚ :=
  let B : Matrix (Fin (q k)) (Fin (q k)) ℚ := interpMatrix k pts
  let v : Matrix (Fin 1) (Fin (q k)) ℚ := radixRow k b * B⁻¹
  fun i => v 0 i


/-- Convert a point list of the right length into a `Fin`-indexed family. -/
def ptsToFin
  (k : ℕ)
  (pts : List Point)
  (hpts : pts.length = q k) :
  Fin (q k) → Point :=
  fun i =>
    pts.get
      ⟨
        i.val,
        by
          have hi : i.val < q k := i.is_lt
          simp [hpts]
      ⟩

/-- Radix used for chunked phase decomposition. -/
def phaseRadix (x : Reg) (k : ℕ) : ℚ :=
  (2 : ℚ) ^ ((regSize x) / k)

def phaseRadixWidth (w k : ℕ) : ℚ :=
  (2 : ℚ) ^ (w / k)

def chunkRadix (W : ℕ) : ℚ :=
  (2 : ℚ) ^ W

noncomputable def phaseCoeffFromPtsWidth
  (k : ℕ) (W : ℕ)
  (pts : List Point) (hpts : pts.length = q k) :
  Fin (q k) → ℚ :=
  phaseCoeffFromPts k (ptsToFin k pts hpts) ((2 : ℚ) ^ W)

noncomputable def phaseCoeffFromPtsForRegs
  (k : ℕ) (x z : ExtReg)
  (pts : List Point) (hpts : pts.length = q k) :
  Fin (q k) → ℚ :=
  phaseCoeffFromPtsWidth k (phaseLimbWidth x z k) pts hpts


/-- The size parameter used when deciding whether a signed phase product
    should recurse again. -/
def phaseInputSize (x z : ExtReg) : ℕ :=
  max (ExtReg.width x) (ExtReg.width z)

/-- The actual width of the recursively compiled chunk phase products. -/
def nextSignedWidth {k : ℕ} (x z : ExtReg) (ops : Prog k) : ℕ :=
  commonNeededWidth (scanNeededWidths x z ops)

/-! =========================================================
    Section 6: Annotated operations and phase-product counting
========================================================= -/


structure AnnotatedOp (k : ℕ) where
  op : valid_ops k
  phaseTerm? : Option (Fin (q k))

def annotatePhaseTermsAux
  (k : ℕ)
  (n : ℕ)
  (ops : List (valid_ops k)) :
  List (AnnotatedOp k) :=
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

def phaseProductCount {k : ℕ} : List (valid_ops k) → ℕ
  | [] => 0
  | op :: ops =>
      match op with
      | .phaseProduct _ => phaseProductCount ops + 1
      | _               => phaseProductCount ops


/-! =========================================================
    Section 7: Signed layout construction and allocation/deallocation gates
========================================================= -/

/-- Number of additional high bits needed to go from `src` to `dst`. -/
def extraDelta (src dst : ExtReg) : ℕ :=
  dst.extra - src.extra



/-- Widen an abstract chunk to at least logical width `W`.
This keeps the same abstract base chunk and only adds semantic high bits.
-/
def widenExtRegTo (e : ExtReg) (W : ℕ) : ExtReg :=
  ExtReg.addExtra e (W - ExtReg.width e)

@[simp] lemma widenExtRegTo_base (e : ExtReg) (W : ℕ) :
    (widenExtRegTo e W).base = e.base := by
  rfl

lemma widenExtRegTo_eq_addExtra (e : ExtReg) (W : ℕ) :
    widenExtRegTo e W =
      ExtReg.addExtra e (extraDelta e (widenExtRegTo e W)) := by
  cases e with
  | mk base extra =>
      simp [widenExtRegTo, extraDelta, ExtReg.addExtra, ExtReg.width]

lemma extraDelta_widenExtRegTo_pos
    (e : ExtReg) (W : ℕ)
    (h : ExtReg.width e < W) :
    0 < extraDelta e (widenExtRegTo e W) := by
  cases e with
  | mk base extra =>
      simp [widenExtRegTo, extraDelta, ExtReg.addExtra, ExtReg.width] at *
      omega

/-- Initial chunk views for the uniform-radix phase decomposition. -/
def initSignedLayoutState
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (x z : ExtReg) (k : ℕ) : LayoutState k :=
  let W := phaseLimbWidth x z k
  { xslot := fun i => splitExtReg (Basis := Basis) x k W i
    zslot := fun i => splitExtReg (Basis := Basis) z k W i }

/-- Final widened chunk views for the compiled signed body.

Each final slot is obtained by widening the corresponding abstract initial
split chunk. No concrete register splitting is used here.
-/
def targetSignedLayoutState
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (x z : ExtReg) (k : ℕ) (need : NeededWidths k) : LayoutState k :=
  let stInit := initSignedLayoutState (Basis := Basis) x z k
  let Wwork := commonNeededWidth need
  { xslot := fun i => widenExtRegTo (stInit.xslot i) Wwork
    zslot := fun i => widenExtRegTo (stInit.zslot i) Wwork }

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

noncomputable def compileOpsToSignedGate
  {Basis : Type u}
  [RegEncoding Basis]
  [ExtRegEncoding Basis]
  [ExtRegSplitSemantics Basis]
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ)
  (x z : ExtReg)
  (phaseCoeff : Fin (q k) → ℚ)
  (ops : List (valid_ops k)) : Gate :=
  let annOps : List (AnnotatedOp k) :=
    annotatePhaseTermsAux k 0 ops
  let need : NeededWidths k :=
    scanNeededWidths x z ops
  let stInit : LayoutState k :=
    initSignedLayoutState (Basis := Basis) x z k
  let stFinal : LayoutState k :=
    targetSignedLayoutState (Basis := Basis) x z k need
  let allocs : Gate :=
    compileSignedAllocations k stInit stFinal
  let body : Gate :=
    compileAnnotatedOpsToSignedGateAux k hk phi phaseCoeff stFinal annOps
  let deallocs : Gate :=
    compileSignedDeallocations k stInit stFinal
  allocs ;; body ;; deallocs

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

noncomputable def compileOpsToCSignedGate
    {Basis : Type u} [RegEncoding Basis] [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (k : ℕ) (hk : 1 < k)
    (ctrl : ℕ) (phi : ℝ) (x z : ExtReg)
    (coeff : Fin (q k) → ℚ) (ops : Prog k) : Gate :=
  controlPhaseLeaves ctrl
    (compileOpsToSignedGate (Basis := Basis) k hk phi x z coeff ops)
/-! =========================================================
    Section 9: Legacy ordinary-register modular helpers
========================================================= -/

def tcMod (r : Reg) (z : ℤ) : ℕ :=
  Int.toNat (z % (ASize r : ℤ))

def tcNegVal (r : Reg) (x : ℕ) : ℕ :=
  tcMod r (-(x : ℤ))

def tcAddScaledVal
    {β : Type} [RegEncoding β]
    (dst src : Reg) (negSrc : Bool) (sh : ℕ) (b : β) : ℕ :=
  let sgn : ℤ := if negSrc then -1 else 1
  tcMod dst
    ((RegEncoding.toNat dst b : ℤ) +
      sgn * (RegEncoding.toNat src b : ℤ) * ((2 : ℤ) ^ sh))

variable (qs : QSemantics) [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
variable [GateSemanticsFacts qs]

/-! =========================================================
    Section 10: Source-row semantics
========================================================= -/

open ExtRegEncoding

/-- How the original source basis should be read when forming chunk rows:
    lower chunks are ordinary radix digits, while the top chunk is signed. -/
def sourceChunkXInt
  (st : LayoutState k) (i : Fin k) (b : qs.Basis) : ℤ :=
  if isTopChunk i then
    ExtRegEncoding.extToInt (st.xslot i) b
  else
    (ExtReg.toNat (st.xslot i) b : ℤ)

/-- Same mixed source interpretation for the `z` slots. -/
def sourceChunkZInt
  (st : LayoutState k) (i : Fin k) (b : qs.Basis) : ℤ :=
  if isTopChunk i then
    ExtRegEncoding.extToInt (st.zslot i) b
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
    Section 11: Encoding invariants
========================================================= -/

/-- Two-layout version: the current widened machine state is read signed on `dst`,
    while the original basis is interpreted using the mixed chunk semantics on `src`. -/
def EncodesStateFrom
  (src dst : LayoutState k) (σ : State k) (b0 b : qs.Basis) : Prop :=
  (∀ i : Fin k,
    ExtRegEncoding.extToInt (dst.xslot i) b
      = evalRowX (qs := qs) src (σ i) b0) ∧
  (∀ i : Fin k,
    ExtRegEncoding.extToInt (dst.zslot i) b
      = evalRowZ (qs := qs) src (σ i) b0)

def EncodesStateFromFits
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ}
  (src dst : LayoutState k) (σ : State k) (b0 b : qs.Basis) : Prop :=
  EncodesStateFrom (qs := qs) src dst σ b0 b ∧
  (∀ i : Fin k,
    FitsSignedWidth (ExtReg.width (dst.xslot i))
      (evalRowX (qs := qs) src (σ i) b0)) ∧
  (∀ i : Fin k,
    FitsSignedWidth (ExtReg.width (dst.zslot i))
      (evalRowZ (qs := qs) src (σ i) b0))

def WidthStateSound
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k) (cur : WidthState k) (σ : State k) (b0 : qs.Basis) : Prop :=
  (∀ i : Fin k,
    FitsSignedWidth (cur.xw i)
      (evalRowX (qs := qs) src (σ i) b0)) ∧
  (∀ i : Fin k,
    FitsSignedWidth (cur.zw i)
      (evalRowZ (qs := qs) src (σ i) b0))

def WidthStateDominatedByLayout
  {k : ℕ} (cur : WidthState k) (dst : LayoutState k) : Prop :=
  (∀ i : Fin k, cur.xw i ≤ ExtReg.width (dst.xslot i)) ∧
  (∀ i : Fin k, cur.zw i ≤ ExtReg.width (dst.zslot i))

def EncodesStateFromWithWidths
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ}
  (src dst : LayoutState k) (cur : WidthState k)
  (σ : State k) (b0 b : qs.Basis) : Prop :=
  EncodesStateFrom (qs := qs) src dst σ b0 b ∧
  WidthStateSound (qs := qs) src cur σ b0 ∧
  WidthStateDominatedByLayout cur dst

/-! =========================================================
    Section 12: Phase scalar
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


/-! =========================================================
    Section 13: Width-state invariant and signed-width arithmetic lemmas
========================================================= -/

/-- Proof-only width invariant: the symbolic value fits in the tracked width
    plus one extra sign bit. This matches `commonNeededWidth = 1 + sup ...`. -/
def WidthStateSoundPlus
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k) (cur : WidthState k) (σ : State k) (b0 : qs.Basis) : Prop :=
  (∀ i : Fin k,
    FitsSignedWidth (cur.xw i + 1)
      (evalRowX (qs := qs) src (σ i) b0)) ∧
  (∀ i : Fin k,
    FitsSignedWidth (cur.zw i + 1)
      (evalRowZ (qs := qs) src (σ i) b0))

end Shor
