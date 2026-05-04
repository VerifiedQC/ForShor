import FastMultiplication.ShorVerification.Basic
import FastMultiplication.Table_Blocks
import Mathlib.Data.Finset.Basic

namespace Shor
open Gate
open Operations
open scoped BigOperators

/-!
This file organizes the abstract layout/width bookkeeping for signed chunked
compilation, the lowering from valid operations to target gates, and the proof
stack ending in `allocated_widths_sound`.
-/

/-! =========================================================
    Section 3: Optional low-level gate language
========================================================= -/

/-- Low-level target gate language for lowering. -/
inductive LowGate : Type
  | id : LowGate
  | seq : LowGate → LowGate → LowGate
  | adj : LowGate → LowGate
  | H : ℕ → LowGate
  | X : ℕ → LowGate
  | Prim : String → List ℕ → LowGate
  | ShiftL    : (r : ExtReg) → (n : ℕ) → LowGate
  | ShiftR    : (r : ExtReg) → (n : ℕ) → LowGate
  | Negate    : (r : ExtReg) → LowGate
  | AddScaled : (dst src : ExtReg) → (negSrc : Bool) → (shift : ℕ) → LowGate
  | Naive_SignedPhaseProd : (phi : Real) → (x z : ExtReg) → LowGate
  | Naive_CSignedPhaseProd : (ctrl : ℕ) → (phi : Real) → (x z : ExtReg) → LowGate
  | zeroExtend : (r : ExtReg) → (n : ℕ) → LowGate
  | signExtend : (r : ExtReg) → (n : ℕ) → LowGate
  | zeroDealloc : (r : ExtReg) → (n : ℕ) → LowGate
  | signDealloc : (r : ExtReg) → (n : ℕ) → LowGate
  | RadixReverse : (r : Reg) → (m : ℕ) → LowGate
deriving Inhabited

namespace LowGate

/-- Sequential composition notation for low gates. -/
infixr:80 " ;; " => LowGate.seq

/-- Adjoint notation for low gates. -/
prefix:90 "†" => LowGate.adj

end LowGate


/-! =========================================================
    Section 4: Layout states and width bookkeeping
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
    Section 5: Top-heavy phase splitting parameters
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
    Section 6: Abstract `ExtReg` split interface
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

lemma phaseLimbWidth_valid_left
    (x z : ExtReg) {k : ℕ} (hk : 0 < k) :
    ValidPhaseSplit x k (phaseLimbWidth x z k) := by
  unfold ValidPhaseSplit phaseLimbWidth phaseLimbWidthOfWidth
  constructor
  · exact hk
  ·
    have hW :
        min (ExtReg.width x / k) (ExtReg.width z / k) ≤ ExtReg.width x / k :=
      Nat.min_le_left _ _
    have hmul₁ :
        (k - 1) * min (ExtReg.width x / k) (ExtReg.width z / k)
          ≤ (k - 1) * (ExtReg.width x / k) :=
      Nat.mul_le_mul_left _ hW
    have hmul₂ :
        (k - 1) * (ExtReg.width x / k)
          ≤ k * (ExtReg.width x / k) := by
      exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    have hmul₃ :
        k * (ExtReg.width x / k) ≤ ExtReg.width x := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self (ExtReg.width x) k
    exact le_trans hmul₁ (le_trans hmul₂ hmul₃)

lemma phaseLimbWidth_valid_right
    (x z : ExtReg) {k : ℕ} (hk : 0 < k) :
    ValidPhaseSplit z k (phaseLimbWidth x z k) := by
  unfold ValidPhaseSplit phaseLimbWidth phaseLimbWidthOfWidth
  constructor
  · exact hk
  ·
    have hW :
        min (ExtReg.width x / k) (ExtReg.width z / k) ≤ ExtReg.width z / k :=
      Nat.min_le_right _ _
    have hmul₁ :
        (k - 1) * min (ExtReg.width x / k) (ExtReg.width z / k)
          ≤ (k - 1) * (ExtReg.width z / k) :=
      Nat.mul_le_mul_left _ hW
    have hmul₂ :
        (k - 1) * (ExtReg.width z / k)
          ≤ k * (ExtReg.width z / k) := by
      exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    have hmul₃ :
        k * (ExtReg.width z / k) ≤ ExtReg.width z := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self (ExtReg.width z) k
    exact le_trans hmul₁ (le_trans hmul₂ hmul₃)

/-- Convenient wrapper for the abstract split operation. -/
def splitExtReg
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (e : ExtReg) (k W : ℕ) (i : Fin k) : ExtReg :=
  ExtRegSplitSemantics.split (Basis:=Basis) e k W i

lemma splitExtReg_disjoint
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (e : ExtReg) (k W : ℕ) (i j : Fin k)
    (hij : i ≠ j) :
    Disjoint (splitExtReg (Basis:=Basis) e k W i).base
             (splitExtReg (Basis:=Basis) e k W j).base := by
  simpa [splitExtReg] using
    ExtRegSplitSemantics.split_disjoint e k W i j hij

lemma splitExtReg_disjoint_of_disjoint
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (x z : ExtReg) (k W : ℕ) (i j : Fin k)
    (hxz : Disjoint x.base z.base) :
    Disjoint (splitExtReg (Basis:=Basis) x k W i).base
             (splitExtReg (Basis:=Basis) z k W j).base := by
  simpa [splitExtReg] using
    ExtRegSplitSemantics.split_disjoint_of_disjoint x z k W i j hxz

lemma splitExtReg_disjoint_reg_of_disjoint
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (e : ExtReg) (r : Reg) (k W : ℕ) (i : Fin k)
    (her : Disjoint e.base r) :
    Disjoint (splitExtReg (Basis:=Basis) e k W i).base r := by
  simpa [splitExtReg] using
    ExtRegSplitSemantics.split_disjoint_reg_of_disjoint e r k W i her

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

lemma splitExtReg_reconstruct_int
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (e : ExtReg) (k W : ℕ) (b : Basis)
    (hValid : ValidPhaseSplit e k W) :
    ((ExtRegEncoding.extToInt e b : ℤ) : ℚ)
      =
    ∑ i : Fin k,
      ((splitChunkInt e W i b : ℤ) : ℚ)
        * ((2 : ℚ) ^ W) ^ (i : ℕ) := by
  unfold splitChunkInt splitExtReg
  simpa using
    ExtRegSplitSemantics.split_reconstruct_int
      (Basis := Basis) e k W b hValid

/-! =========================================================
    Section 7: Width scanning and target-width definitions
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
    Section 8: Interpolation and phase coefficients
========================================================= -/

/-- Number of interpolation points used for radix-`k` phase decomposition. -/
def q (k : ℕ) : ℕ := 2 * k - 1

/-- One entry of the interpolation matrix. -/
def interpEntry (k : ℕ) (p : Point) (j : Fin (q k)) : ℚ :=
  match p with
  | .int z => (z : ℚ) ^ (j : ℕ)
  | .inf   => if (j : ℕ) = q k - 1 then 1 else 0

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
    Section 9: Annotated operations and phase-product counting
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

lemma annotatePhaseTermsAux_append
  (k : ℕ) (n : ℕ)
  (ops₁ ops₂ : List (valid_ops k)) :
  annotatePhaseTermsAux k n (ops₁ ++ ops₂) =
    annotatePhaseTermsAux k n ops₁ ++
      annotatePhaseTermsAux k (n + phaseProductCount ops₁) ops₂ := by
  induction ops₁ generalizing n with
  | nil =>
      simp [annotatePhaseTermsAux, phaseProductCount]
  | cons op ops₁ ih =>
      cases op <;>simp [annotatePhaseTermsAux, phaseProductCount, ih, Nat.add_assoc, Nat.add_comm]

lemma annotatePhaseTermsAux_append_zero
  (k : ℕ) (ops₁ ops₂ : List (valid_ops k)) :
  annotatePhaseTermsAux k 0 (ops₁ ++ ops₂) =
    annotatePhaseTermsAux k 0 ops₁ ++
      annotatePhaseTermsAux k (phaseProductCount ops₁) ops₂ := by
  simpa using annotatePhaseTermsAux_append k 0 ops₁ ops₂

@[simp] lemma phaseProductCount_addConstAux
  {k : ℕ} (dst src : Fin k) (neg' : Bool) (n sh : ℕ) :
  phaseProductCount (addConstAux (k := k) dst src neg' n sh) = 0 := by
  rw [addConstAux_eq_shifts (k := k) (dst := dst) (src := src) (neg' := neg') n sh]
  induction shiftsOfAux n sh with
  | nil =>
      simp [phaseProductCount]
  | cons s ss ih =>
      simp [phaseProductCount, ih]

@[simp] lemma phaseProductCount_addConstFrom
  {k : ℕ} (dst src : Fin k) (c : Int) :
  phaseProductCount (addConstFrom (k := k) dst src c) = 0 := by
  by_cases hc : c = 0
  · simp [addConstFrom, hc, phaseProductCount]
  · simp [addConstFrom, hc, phaseProductCount_addConstAux]

@[simp] lemma phaseProductCount_append
  {k : ℕ} (xs ys : List (valid_ops k)) :
  phaseProductCount (xs ++ ys) =
    phaseProductCount xs + phaseProductCount ys := by
  induction xs with
  | nil =>
      simp [phaseProductCount]
  | cons op xs ih =>
      cases op <;> simp [phaseProductCount, ih,  Nat.add_comm, Nat.add_left_comm]

@[simp] lemma phaseProductCount_computeLocalAux
  {k : ℕ} (hk : 0 < k) (z : Int) :
  ∀ js : List (Fin k), phaseProductCount (computeLocalAux (k := k) hk z js) = 0
  | [] => by
      simp [computeLocalAux, phaseProductCount]
  | j :: js => by
      simp [computeLocalAux, phaseProductCount_append,
            phaseProductCount_addConstFrom,
            phaseProductCount_computeLocalAux]

@[simp] lemma phaseProductCount_computeLocal2
  {k : ℕ} (hk : 0 < k) (z : Int) :
  phaseProductCount (computeLocal2 (k := k) hk z) = 0 := by
  simp [computeLocal2, phaseProductCount_computeLocalAux]

/-! =========================================================
    Section 10: Signed layout construction and allocation/deallocation gates
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
/-! =========================================================
    Section 11: Compilation from `valid_ops` to `Gate`
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

/-! =========================================================
    Section 12: Legacy ordinary-register modular helpers
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
    Section 13: Semantic variables and general semantic helper
========================================================= -/

omit [RegEncoding QSemantics.Basis] in
lemma gate_eq_of_ket_eq
  {U V : Gate}
  (hket : ∀ b : qs.Basis, qs.eval U (qs.ket b) = qs.eval V (qs.ket b)) :
  ∀ ψ : qs.State, qs.eval U ψ = qs.eval V ψ := by
  intro ψ
  let P : qs.State → Prop := fun ψ => qs.eval U ψ = qs.eval V ψ
  have h0 : P 0 := by
    dsimp [P]
    rw [qs.eval_zero, qs.eval_zero]
  have hadd : ∀ ψ φ, P ψ → P φ → P (ψ + φ) := by
    intro ψ φ hψ hφ
    dsimp [P] at *
    rw [qs.eval_add, qs.eval_add, hψ, hφ]
  have hsmul : ∀ (a : ℂ) ψ, P ψ → P (a • ψ) := by
    intro a ψ hψ
    dsimp [P] at *
    rw [qs.eval_smul, qs.eval_smul, hψ]
  have hbasis : ∀ b : qs.Basis, P (qs.ket b) := by
    intro b
    dsimp [P]
    exact hket b
  exact qs.state_induction P h0 hadd hsmul hbasis ψ

/-! =========================================================
    Section 14: Source-row semantics
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
    Section 15: Encoding invariants
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

lemma EncodesStateFromWithWidths.toFits
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ}
  {src dst : LayoutState k} {cur : WidthState k}
  {σ : State k} {b0 b : qs.Basis}
  (h : EncodesStateFromWithWidths
    (qs := qs) src dst cur σ b0 b) :
  EncodesStateFromFits (qs := qs) src dst σ b0 b := by
  rcases h with ⟨hEnc, hSoundX, hDom⟩
  rcases hSoundX with ⟨hSoundX, hSoundZ⟩
  rcases hDom with ⟨hDomX, hDomZ⟩
  refine ⟨hEnc, ?_, ?_⟩
  ·
    intro i
    exact FitsSignedWidth_mono (hDomX i) (hSoundX i)
  ·
    intro i
    exact FitsSignedWidth_mono (hDomZ i) (hSoundZ i)

/-! =========================================================
    Section 16: Phase scalar
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
    Section 17: Scan monotonicity lemmas
========================================================= -/

/-- I recommend replacing the original `scanNeededWidths` body by this exact helper call. -/
lemma scanNeededWidths_eq_aux {k : ℕ} (x z : ExtReg) (ops : List (valid_ops k)) :
  scanNeededWidths x z ops =
    scanNeededWidthsAux (initWidthState x z k) (widthsOfState (initWidthState x z k)) ops := by
  simp[scanNeededWidths]


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

/-! =========================================================
    Section 18: Width-state invariant and signed-width arithmetic lemmas
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

lemma FitsSignedWidth_of_nonneg_lt_pow
  {w : ℕ} {n : ℕ}
  (h : n < 2 ^ w) :
  FitsSignedWidth (w + 1) (n : ℤ) := by
  unfold FitsSignedWidth signedMin signedMax
  constructor <;> simp
  constructor
  have hn0 : (0 : ℤ) ≤ (n : ℤ) := by
    exact_mod_cast Nat.zero_le n
  have hneg : (-(2 : ℤ) ^ (w + 1)) ≤ 0 := by
    have hpow0 : (0 : ℤ) ≤ (2 : ℤ) ^ (w + 1) := by positivity
    omega
  omega
  norm_cast

lemma tcDecodeWidth_fits_succ
  {w n : ℕ}
  (h : n < 2 ^ w) :
  FitsSignedWidth (w + 1) (tcDecodeWidth w n) := by
  unfold FitsSignedWidth signedMin signedMax tcDecodeWidth
  by_cases hs : n < 2 ^ (w - 1)
  · simp
    constructor <;>
    split
    next x x_1 =>
      simp_all only [pow_zero, Nat.lt_one_iff, zero_tsub, zero_lt_one, Int.reduceNeg, Left.neg_nonpos_iff,
        zero_le_one]
    next x x_1 w =>
      simp_all only [Nat.succ_eq_add_one, add_tsub_cancel_right, ↓reduceIte]
      have hn0 : (0 : ℤ) ≤ (n : ℤ) := by
        exact_mod_cast Nat.zero_le n
      have hneg : (-(2 : ℤ) ^ (w + 1)) ≤ 0 := by
        have hpow0 : (0 : ℤ) ≤ (2 : ℤ) ^ (w + 1) := by positivity
        omega
      omega
    simp
    simp_all only [Nat.succ_eq_add_one, add_tsub_cancel_right, ↓reduceIte]
    norm_cast
  · simp
    constructor <;>
    split
    next x x_1 =>
      simp_all only [pow_zero, Nat.lt_one_iff, zero_tsub, zero_lt_one, Int.reduceNeg, Left.neg_nonpos_iff,
        zero_le_one]
      simp at hs
    next x x_1 w =>
      simp_all only [Nat.succ_eq_add_one, add_tsub_cancel_right, ↓reduceIte]
      have hge : 2 ^ w ≤ n := Nat.le_of_not_lt hs
      have hn0 : (0 : ℤ) ≤ (n : ℤ) := by
        exact_mod_cast Nat.zero_le n
      omega
    simp
    simp_all only [Nat.succ_eq_add_one, add_tsub_cancel_right, not_lt]
    split
    next h_1 => norm_cast
    next h_1 =>
      simp_all only [not_lt]; rename_i x1 x w
      have hlt : (n : ℤ) < (2 : ℤ) ^ (w + 1) := by
        exact_mod_cast h
      omega

lemma extToInt_fits_width_succ
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  (e : ExtReg) (b : qs.Basis) :
  FitsSignedWidth (ExtReg.width e + 1) (ExtRegEncoding.extToInt e b) := by
  unfold ExtRegEncoding.extToInt
  have hlt : ExtRegEncoding.extToNat e b < 2 ^ ExtReg.width e := by
    simpa using
      (ExtRegEncoding.extToNat_lt
        (Basis := qs.Basis) (e := e) (b := b))
  exact tcDecodeWidth_fits_succ hlt


/-- If `z` fits signed width `w+1`, then `(2^n) * z` fits signed width `w+n+1`. -/
lemma FitsSignedWidth_shiftL_raw
  {w n : ℕ} {z : ℤ}
  (hfit : FitsSignedWidth (w + 1) z) :
  FitsSignedWidth (w + n + 1) (((2 : ℤ)^n) * z) := by
  unfold FitsSignedWidth signedMin signedMax at hfit ⊢
  rcases hfit with ⟨hlo, hhi⟩
  have hp0 : (0 : ℤ) ≤ (2 : ℤ)^n := by positivity
  have hp : (0 : ℤ) < (2 : ℤ)^n := by positivity

  have hpow :
      ((2 : ℤ)^n) * (((2 ^ w : ℕ) : ℤ))
        = (((2 ^ (w + n) : ℕ) : ℤ)) := by
    calc
      ((2 : ℤ)^n) * (((2 ^ w : ℕ) : ℤ))
          = (((2 ^ n : ℕ) : ℤ)) * (((2 ^ w : ℕ) : ℤ)) := by norm_num
      _ = (((2 ^ n * 2 ^ w : ℕ) : ℤ)) := by norm_num
      _ = (((2 ^ (n + w) : ℕ) : ℤ)) := by
            exact_mod_cast (pow_add 2 n w).symm
      _ = (((2 ^ (w + n) : ℕ) : ℤ)) := by rw [Nat.add_comm]

  have hpow_neg :
      ((2 : ℤ)^n) * (-(((2 ^ w : ℕ) : ℤ)))
        = -(((2 ^ (w + n) : ℕ) : ℤ)) := by
    simp
    rw[pow_add,mul_comm]

  have hL :
      ((2 : ℤ)^n) * (-(((2 ^ w : ℕ) : ℤ)))
        ≤
      ((2 : ℤ)^n) * z := by
    exact mul_le_mul_of_nonneg_left (by simp_all) hp0

  have hU :
      ((2 : ℤ)^n) * z
        <
      ((2 : ℤ)^n) * (((2 ^ w : ℕ) : ℤ)) := by
    exact mul_lt_mul_of_pos_left (by simp_all) hp

  constructor
  · simp
  · aesop

/-- If `z = 2^n * q` and `z` fits signed width `w+1`, then the exact quotient
    fits signed width `(w - n) + 1`. -/
lemma FitsSignedWidth_shiftR_of_mul
  {w n : ℕ} {z q : ℤ}
  (hfit : FitsSignedWidth (w + 1) z)
  (hz : z = ((2 : ℤ)^n) * q) :
  FitsSignedWidth (w - n + 1) q := by
  unfold FitsSignedWidth signedMin signedMax at hfit ⊢
  rcases hfit with ⟨hlo, hhi⟩
  by_cases hnw : n ≤ w
  · have hpos : (0 : ℤ) < (2 : ℤ)^n := by positivity

    have hpow :
        ((2 : ℤ)^n) * (((2 ^ (w - n) : ℕ) : ℤ))
          = (((2 ^ w : ℕ) : ℤ)) := by
      calc
        ((2 : ℤ)^n) * (((2 ^ (w - n) : ℕ) : ℤ))
            = (((2 ^ n : ℕ) : ℤ)) * (((2 ^ (w - n) : ℕ) : ℤ)) := by norm_num
        _ = (((2 ^ n * 2 ^ (w - n) : ℕ) : ℤ)) := by norm_num
        _ = (((2 ^ (n + (w - n)) : ℕ) : ℤ)) := by
              exact_mod_cast (pow_add 2 n (w - n)).symm
        _ = (((2 ^ w : ℕ) : ℤ)) := by rw [Nat.add_sub_of_le hnw]

    have hupper :
        ((2 : ℤ)^n) * q
          <
        ((2 : ℤ)^n) * (((2 ^ (w - n) : ℕ) : ℤ)) := by
      simp_all
    have hlower :
        ((2 : ℤ)^n) * (-(((2 ^ (w - n) : ℕ) : ℤ)))
          ≤
        ((2 : ℤ)^n) * q := by
      have : -(((2 ^ w : ℕ) : ℤ)) ≤ ((2 : ℤ)^n) * q := by
        simp_all
      simp_all

    constructor
    · simp_all
    · simp_all
      constructor
      · have h1 : -(2 ^ n * 2 ^ (w - n) : ℤ) ≤ 2 ^ n * q := by
          rw [hpow]; exact hhi.1
        have h2 : (2 ^ n : ℤ) * -(2 ^ (w - n)) ≤ 2 ^ n * q := by
          rw [mul_neg]; exact h1
        exact le_of_mul_le_mul_left h2 (by positivity)
      · have h1 : (2 ^ n * q : ℤ) < 2 ^ n * 2 ^ (w - n) := by
          rw [hpow]; exact hhi.2
        exact lt_of_mul_lt_mul_left h1 (by positivity)


  · have hwn : w < n := lt_of_not_ge hnw
    have hpowNat : 2 ^ w < 2 ^ n := by
      exact Nat.pow_lt_pow_right (by decide : 1 < 2) hwn
    have hpowInt : (((2 ^ w : ℕ) : ℤ)) < ((2 : ℤ)^n) := by
      exact_mod_cast hpowNat

    have hq0 : q = 0 := by
      by_cases hq : q = 0
      · exact hq
      · rcases lt_or_gt_of_ne hq with hqneg | hqpos
        · have hqle : q ≤ -1 := by omega
          have hmul : ((2 : ℤ)^n) * q ≤ -((2 : ℤ)^n) := by
            calc
              ((2 : ℤ)^n) * q ≤ ((2 : ℤ)^n) * (-1) := by
                gcongr
              _ = -((2 : ℤ)^n) := by ring
          have hzlt : z < -(((2 ^ w : ℕ) : ℤ)) := by
            rw [hz]
            have hnegpow : -((2 : ℤ)^n) < -(((2 ^ w : ℕ) : ℤ)) := by
              omega
            exact lt_of_le_of_lt hmul hnegpow
          simp_all
          rcases hhi with ⟨hlo, hhi⟩
          omega
        · have hqge : (1 : ℤ) ≤ q := by omega
          have hmul : ((2 : ℤ)^n) ≤ ((2 : ℤ)^n) * q := by
            calc
              ((2 : ℤ)^n) = ((2 : ℤ)^n) * 1 := by ring
              _ ≤ ((2 : ℤ)^n) * q := by
                gcongr
          have hzgt : (((2 ^ w : ℕ) : ℤ)) < z := by
            rw [hz]
            exact lt_of_lt_of_le hpowInt hmul
          simp_all
          rcases hhi with ⟨hlo, hhi⟩
          omega

    subst hq0
    have hw0 : w - n = 0 := by omega
    rw [hw0]
    constructor <;> norm_num [signedMin, signedMax]

/-- Negation is always safe if we widen by one additional bit. -/
lemma FitsSignedWidth_neg_widen
  {w : ℕ} {z : ℤ}
  (hfit : FitsSignedWidth (w + 1) z) :
  FitsSignedWidth (w + 2) (-z) := by
  unfold FitsSignedWidth signedMin signedMax at hfit ⊢
  rcases hfit with ⟨hlo, hhi⟩
  have hpow : (((2 ^ w : ℕ) : ℤ)) ≤ (((2 ^ (w + 1) : ℕ) : ℤ)) := by
    exact_mod_cast
      (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (Nat.le_succ w))
  constructor <;> simp_all
  refine ⟨?_, ?_⟩
  · linarith [hhi.2, hpow]
  · have hpos : (0 : ℤ) < 2 ^ w := by positivity
    omega

/-- Adding a shifted source into a destination is safe in the width prescribed
    by `updateWidthState` (plus the proof-only extra sign bit). -/
lemma FitsSignedWidth_addScaled_widen
  {wd ws sh : ℕ} {dstv srcv : ℤ} (negSrc : Bool)
  (hdst : FitsSignedWidth (wd + 1) dstv)
  (hsrc : FitsSignedWidth (ws + 1) srcv) :
  FitsSignedWidth (max wd (ws + sh) + 2)
    (dstv + (if negSrc then (-1 : ℤ) else 1) * ((2 : ℤ)^sh) * srcv) := by
  have hscaled :
      FitsSignedWidth (ws + sh + 1) (((2 : ℤ)^sh) * srcv) := by
    exact FitsSignedWidth_shiftL_raw (w := ws) (n := sh) (z := srcv) hsrc

  unfold FitsSignedWidth signedMin signedMax at hdst hscaled ⊢
  rcases hdst with ⟨hdlo, hdhi⟩
  rcases hscaled with ⟨hslo, hshi⟩

  set M : ℕ := max wd (ws + sh)

  have hwdM : (((2 ^ wd : ℕ) : ℤ)) ≤ (((2 ^ M : ℕ) : ℤ)) := by
    dsimp [M]
    exact_mod_cast
      (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (le_max_left wd (ws + sh)))

  have hwsM : (((2 ^ (ws + sh) : ℕ) : ℤ)) ≤ (((2 ^ M : ℕ) : ℤ)) := by
    dsimp [M]
    exact_mod_cast
      (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (le_max_right wd (ws + sh)))

  cases hsgn : negSrc <;> simp_all
  · constructor <;> omega
  · constructor <;> omega

/-! =========================================================
    Section 19: Start-state and layout-width lemmas
========================================================= -/

/-- Start-state row evaluation picks out the requested x-slot. -/
lemma evalRowX_start_state
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ} (st : LayoutState k) (i : Fin k) (b : qs.Basis) :
  evalRowX (qs := qs) st (State.start_state i) b = sourceChunkXInt (qs := qs) st i b := by
  unfold evalRowX State.start_state
  simp

/-- Start-state row evaluation picks out the requested z-slot. -/
lemma evalRowZ_start_state
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ} (st : LayoutState k) (i : Fin k) (b : qs.Basis) :
  evalRowZ (qs := qs) st (State.start_state i) b = sourceChunkZInt (qs := qs) st i b := by
  unfold evalRowZ State.start_state
  simp

lemma splitExtReg_width_of_valid
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (e : ExtReg) (k W : ℕ) (i : Fin k)
    (hValid : ValidPhaseSplit e k W) :
    ExtReg.width (splitExtReg (Basis := Basis) e k W i)
      =
    phaseSplitLogicalWidth (ExtReg.width e) W k i := by
  simpa [splitExtReg] using
    ExtRegSplitSemantics.split_width
      (Basis := Basis) e k W i hValid

lemma stInit_xslot_width
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    {k : ℕ} (x z : ExtReg) (i : Fin k) :
    ExtReg.width ((initSignedLayoutState (Basis := Basis) x z k).xslot i)
      =
    (initWidthState x z k).xw i := by
  have hk : 0 < k := lt_of_le_of_lt (Nat.zero_le i.1) i.2
  have hValidX : ValidPhaseSplit x k (phaseLimbWidth x z k) :=
    phaseLimbWidth_valid_left x z hk
  unfold initSignedLayoutState initWidthState
  dsimp
  exact
    splitExtReg_width_of_valid
      (Basis := Basis)
      x k (phaseLimbWidth x z k) i hValidX

lemma stInit_zslot_width
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    {k : ℕ} (x z : ExtReg) (i : Fin k) :
    ExtReg.width ((initSignedLayoutState (Basis := Basis) x z k).zslot i)
      =
    (initWidthState x z k).zw i := by
  have hk : 0 < k := lt_of_le_of_lt (Nat.zero_le i.1) i.2
  have hValidZ : ValidPhaseSplit z k (phaseLimbWidth x z k) :=
    phaseLimbWidth_valid_right x z hk
  unfold initSignedLayoutState initWidthState
  dsimp
  exact
    splitExtReg_width_of_valid
      (Basis := Basis)
      z k (phaseLimbWidth x z k) i hValidZ

lemma stFinal_xslot_eq_addExtra
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    {k : ℕ} (x z : ExtReg) (ops : Prog k) (i : Fin k) :
    let stInit := initSignedLayoutState (Basis := Basis) x z k
    let stFinal := targetSignedLayoutState (Basis := Basis) x z k
      (scanNeededWidths x z ops)
    stFinal.xslot i =
      ExtReg.addExtra (stInit.xslot i)
        (extraDelta (stInit.xslot i) (stFinal.xslot i)) := by
  dsimp [targetSignedLayoutState]
  exact widenExtRegTo_eq_addExtra _ _

lemma stFinal_zslot_eq_addExtra
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    {k : ℕ} (x z : ExtReg) (ops : Prog k) (i : Fin k) :
    let stInit := initSignedLayoutState (Basis := Basis) x z k
    let stFinal := targetSignedLayoutState (Basis := Basis) x z k
      (scanNeededWidths x z ops)
    stFinal.zslot i =
      ExtReg.addExtra (stInit.zslot i)
        (extraDelta (stInit.zslot i) (stFinal.zslot i)) := by
  dsimp [targetSignedLayoutState]
  exact widenExtRegTo_eq_addExtra _ _

/-! =========================================================
    Section 20: Row-evaluation arithmetic lemmas
========================================================= -/


lemma evalRowX_shiftL_raw
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k)
  (r : Register k)
  (m : ℕ)
  (b : qs.Basis) :
  evalRowX (qs := qs) src (r.shiftL m) b
    =
  ((2 : ℤ)^m) * evalRowX (qs := qs) src r b := by
  unfold evalRowX Register.shiftL
  calc
    (∑ j : Fin k, (r j * (2 : ℤ)^m) * sourceChunkXInt (qs := qs) src j b)
      =
    ∑ j : Fin k, ((2 : ℤ)^m) * (r j * sourceChunkXInt (qs := qs) src j b) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
    _ = ((2 : ℤ)^m) * ∑ j : Fin k, r j * sourceChunkXInt (qs := qs) src j b := by
        rw [Finset.mul_sum]

lemma evalRowZ_shiftL_raw
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k)
  (r : Register k)
  (m : ℕ)
  (b : qs.Basis) :
  evalRowZ (qs := qs) src (r.shiftL m) b
    =
  ((2 : ℤ)^m) * evalRowZ (qs := qs) src r b := by
  unfold evalRowZ Register.shiftL
  calc
    (∑ j : Fin k, (r j * (2 : ℤ)^m) * sourceChunkZInt (qs := qs) src j b)
      =
    ∑ j : Fin k, ((2 : ℤ)^m) * (r j * sourceChunkZInt (qs := qs) src j b) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
    _ = ((2 : ℤ)^m) * ∑ j : Fin k, r j * sourceChunkZInt (qs := qs) src j b := by
        rw [Finset.mul_sum]

lemma evalRowX_negate_raw
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k)
  (r : Register k)
  (b : qs.Basis) :
  evalRowX (qs := qs) src (Register.negate r) b
    =
  - evalRowX (qs := qs) src r b := by
  unfold evalRowX Register.negate
  calc
    (∑ j : Fin k, (-r j) * sourceChunkXInt (qs := qs) src j b)
      =
    ∑ j : Fin k, -(r j * sourceChunkXInt (qs := qs) src j b) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
    _ = - ∑ j : Fin k, r j * sourceChunkXInt (qs := qs) src j b := by
        rw [Finset.sum_neg_distrib]

lemma evalRowZ_negate_raw
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k)
  (r : Register k)
  (b : qs.Basis) :
  evalRowZ (qs := qs) src (Register.negate r) b
    =
  - evalRowZ (qs := qs) src r b := by
  unfold evalRowZ Register.negate
  calc
    (∑ j : Fin k, (-r j) * sourceChunkZInt (qs := qs) src j b)
      =
    ∑ j : Fin k, -(r j * sourceChunkZInt (qs := qs) src j b) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
    _ = - ∑ j : Fin k, r j * sourceChunkZInt (qs := qs) src j b := by
        rw [Finset.sum_neg_distrib]

lemma evalRowX_shiftR_exact
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k)
  (r r' : Register k)
  (m : ℕ)
  (b : qs.Basis)
  (hshift : Register.shiftR? r m = some r') :
  evalRowX (qs := qs) src r b
    =
  ((2 : ℤ)^m) * evalRowX (qs := qs) src r' b := by
  have hdiv := Register.shiftR?_some_divisible hshift
  have hval := Register.shiftR?_some_value hshift
  unfold evalRowX
  calc
    (∑ j : Fin k, r j * sourceChunkXInt (qs := qs) src j b)
      =
    ∑ j : Fin k, (((2 : ℤ)^m) * r' j) * sourceChunkXInt (qs := qs) src j b := by
        apply Finset.sum_congr rfl
        intro j hj
        have hdvd : ((2 : ℤ)^m) ∣ r j := Int.dvd_of_emod_eq_zero (hdiv j)
        have hrj : r j = ((2 : ℤ)^m) * r' j := by
          calc
            r j = ((2 : ℤ)^m) * (r j / ((2 : ℤ)^m)) := by
              symm
              exact Int.mul_ediv_cancel' hdvd
            _ = ((2 : ℤ)^m) * r' j := by
              rw [hval j]
        rw [hrj]
    _ =
    ∑ j : Fin k, ((2 : ℤ)^m) * (r' j * sourceChunkXInt (qs := qs) src j b) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
    _ = ((2 : ℤ)^m) * ∑ j : Fin k, r' j * sourceChunkXInt (qs := qs) src j b := by
        rw [Finset.mul_sum]

lemma evalRowZ_shiftR_exact
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k)
  (r r' : Register k)
  (m : ℕ)
  (b : qs.Basis)
  (hshift : Register.shiftR? r m = some r') :
  evalRowZ (qs := qs) src r b
    =
  ((2 : ℤ)^m) * evalRowZ (qs := qs) src r' b := by
  have hdiv := Register.shiftR?_some_divisible hshift
  have hval := Register.shiftR?_some_value hshift
  unfold evalRowZ
  calc
    (∑ j : Fin k, r j * sourceChunkZInt (qs := qs) src j b)
      =
    ∑ j : Fin k, (((2 : ℤ)^m) * r' j) * sourceChunkZInt (qs := qs) src j b := by
        apply Finset.sum_congr rfl
        intro j hj
        have hdvd : ((2 : ℤ)^m) ∣ r j := Int.dvd_of_emod_eq_zero (hdiv j)
        have hrj : r j = ((2 : ℤ)^m) * r' j := by
          calc
            r j = ((2 : ℤ)^m) * (r j / ((2 : ℤ)^m)) := by
              symm
              exact Int.mul_ediv_cancel' hdvd
            _ = ((2 : ℤ)^m) * r' j := by
              rw [hval j]
        rw [hrj]
    _ =
    ∑ j : Fin k, ((2 : ℤ)^m) * (r' j * sourceChunkZInt (qs := qs) src j b) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
    _ = ((2 : ℤ)^m) * ∑ j : Fin k, r' j * sourceChunkZInt (qs := qs) src j b := by
        rw [Finset.mul_sum]

lemma evalRowX_addScaled_raw
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k)
  (dstReg srcReg : Register k)
  (negSrc : Bool)
  (sh : ℕ)
  (b : qs.Basis) :
  evalRowX (qs := qs) src (Register.addScaled dstReg srcReg negSrc sh) b
    =
  evalRowX (qs := qs) src dstReg b
    + (if negSrc then (-1 : ℤ) else 1)
        * ((2 : ℤ)^sh)
        * evalRowX (qs := qs) src srcReg b := by
  unfold evalRowX Register.addScaled
  calc
    (∑ j : Fin k,
        (dstReg j + (if negSrc then (-1 : ℤ) else 1) * srcReg j * (2 : ℤ) ^ sh)
          * sourceChunkXInt (qs := qs) src j b)
        =
    (∑ j : Fin k,
      (dstReg j * sourceChunkXInt (qs := qs) src j b
        +
      ((if negSrc then (-1 : ℤ) else 1) * ((2 : ℤ) ^ sh))
        * (srcReg j * sourceChunkXInt (qs := qs) src j b))) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ =
    (∑ j : Fin k, dstReg j * sourceChunkXInt (qs := qs) src j b)
      +
    ∑ j : Fin k,
      ((if negSrc then (-1 : ℤ) else 1) * ((2 : ℤ) ^ sh))
        * (srcReg j * sourceChunkXInt (qs := qs) src j b) := by
          rw [Finset.sum_add_distrib]
    _ =
    (∑ j : Fin k, dstReg j * sourceChunkXInt (qs := qs) src j b)
      +
    ((if negSrc then (-1 : ℤ) else 1) * ((2 : ℤ) ^ sh))
      * ∑ j : Fin k, srcReg j * sourceChunkXInt (qs := qs) src j b := by
          rw [Finset.mul_sum]

lemma evalRowZ_addScaled_raw
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k)
  (dstReg srcReg : Register k)
  (negSrc : Bool)
  (sh : ℕ)
  (b : qs.Basis) :
  evalRowZ (qs := qs) src (Register.addScaled dstReg srcReg negSrc sh) b
    =
  evalRowZ (qs := qs) src dstReg b
    + (if negSrc then (-1 : ℤ) else 1)
        * ((2 : ℤ)^sh)
        * evalRowZ (qs := qs) src srcReg b := by
  unfold evalRowZ Register.addScaled
  calc
    (∑ j : Fin k,
        (dstReg j + (if negSrc then (-1 : ℤ) else 1) * srcReg j * (2 : ℤ) ^ sh)
          * sourceChunkZInt (qs := qs) src j b)
        =
    (∑ j : Fin k,
      (dstReg j * sourceChunkZInt (qs := qs) src j b
        +
      ((if negSrc then (-1 : ℤ) else 1) * ((2 : ℤ) ^ sh))
        * (srcReg j * sourceChunkZInt (qs := qs) src j b))) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ =
    (∑ j : Fin k, dstReg j * sourceChunkZInt (qs := qs) src j b)
      +
    ∑ j : Fin k,
      ((if negSrc then (-1 : ℤ) else 1) * ((2 : ℤ) ^ sh))
        * (srcReg j * sourceChunkZInt (qs := qs) src j b) := by
          rw [Finset.sum_add_distrib]
    _ =
    (∑ j : Fin k, dstReg j * sourceChunkZInt (qs := qs) src j b)
      +
    ((if negSrc then (-1 : ℤ) else 1) * ((2 : ℤ) ^ sh))
      * ∑ j : Fin k, srcReg j * sourceChunkZInt (qs := qs) src j b := by
          rw [Finset.mul_sum]

/-! =========================================================
    Section 21: Width-state preservation through symbolic execution
========================================================= -/

lemma widthStateSoundPlus_step
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k)
  (cur : WidthState k)
  (σ σ1 : State k)
  (op : valid_ops k)
  (b : qs.Basis)
  (hstep : applyOp? σ op = some σ1)
  (hfit : WidthStateSoundPlus (qs := qs) src cur σ b) :
  WidthStateSoundPlus
    (qs := qs) src (updateWidthState cur op) σ1 b := by
  rcases hfit with ⟨hx, hz⟩
  cases op with
  | shiftL i n =>
      have hσ1 : σ1 = State.shiftLReg σ i n := by
        simp [applyOp?] at  hstep
        simp[hstep]
      subst hσ1
      constructor
      · intro j
        by_cases hji : i = j
        · subst hji
          have hrow :
              evalRowX (qs := qs) src ((σ i).shiftL n) b
                =
              ((2 : ℤ)^n) * evalRowX (qs := qs) src (σ i) b := by
            simpa using
              (evalRowX_shiftL_raw
                (qs := qs) (src := src) (r := σ i) (m := n) (b := b))
          have hnew :
              FitsSignedWidth (cur.xw i + n + 1)
                (((2 : ℤ)^n) * evalRowX (qs := qs) src (σ i) b) := by
            exact FitsSignedWidth_shiftL_raw (w := cur.xw i) (n := n) (hfit := hx i)
          simpa [updateWidthState, State.shiftLReg, State.setReg, hrow]
            using hnew
        · have hji' : j ≠ i := by omega
          simpa [updateWidthState, State.shiftLReg, State.setReg, hji', Function.update]
            using hx j
      · intro j
        by_cases hji : i = j
        · subst hji
          have hrow :
              evalRowZ (qs := qs) src ((σ i).shiftL n) b
                =
              ((2 : ℤ)^n) * evalRowZ (qs := qs) src (σ i) b := by
            simpa using
              (evalRowZ_shiftL_raw
                (qs := qs) (src := src) (r := σ i) (m := n) (b := b))
          have hnew :
              FitsSignedWidth (cur.zw i + n + 1)
                (((2 : ℤ)^n) * evalRowZ (qs := qs) src (σ i) b) := by
            exact FitsSignedWidth_shiftL_raw (w := cur.zw i) (n := n) (hfit := hz i)
          simpa [updateWidthState, State.shiftLReg, State.setReg, hrow]
            using hnew
        · have hji' : j ≠ i := by omega
          simpa [updateWidthState, State.shiftLReg, State.setReg, hji', Function.update]
            using hz j

  | shiftR i n =>
      cases hreg : Register.shiftR? (σ i) n with
      | none =>
          simp [applyOp?, State.shiftRReg?, hreg] at hstep
      | some r' =>
          have hσ1 : σ1 = State.setReg σ i r' := by
            have:σ.setReg i r' = σ1:=by simpa [applyOp?, State.shiftRReg?, hreg] using hstep
            rw[this]
          subst hσ1
          constructor
          · intro j
            by_cases hji : i = j
            · subst hji
              have hrow :
                  evalRowX (qs := qs) src (σ i) b
                    =
                  ((2 : ℤ)^n) * evalRowX (qs := qs) src r' b := by
                simpa using
                  (evalRowX_shiftR_exact
                    (qs := qs) (src := src) (r := σ i) (r' := r')
                    (m := n) (b := b) hreg)
              have hnew :
                  FitsSignedWidth (cur.xw i - n + 1)
                    (evalRowX (qs := qs) src r' b) := by
                exact FitsSignedWidth_shiftR_of_mul
                  (w := cur.xw i) (n := n)
                  (z := evalRowX (qs := qs) src (σ i) b)
                  (q := evalRowX (qs := qs) src r' b)
                  (hfit := hx i) hrow
              simpa [updateWidthState, State.setReg, Function.update]
                using hnew
            · have hji' : j ≠ i := by omega
              simpa [updateWidthState, State.setReg, hji', Function.update]
                using hx j
          · intro j
            by_cases hji : i = j
            · subst hji
              have hrow :
                  evalRowZ (qs := qs) src (σ i) b
                    =
                  ((2 : ℤ)^n) * evalRowZ (qs := qs) src r' b := by
                simpa using
                  (evalRowZ_shiftR_exact
                    (qs := qs) (src := src) (r := σ i) (r' := r')
                    (m := n) (b := b) hreg)
              have hnew :
                  FitsSignedWidth (cur.zw i - n + 1)
                    (evalRowZ (qs := qs) src r' b) := by
                exact FitsSignedWidth_shiftR_of_mul
                  (w := cur.zw i) (n := n)
                  (z := evalRowZ (qs := qs) src (σ i) b)
                  (q := evalRowZ (qs := qs) src r' b)
                  (hfit := hz i) hrow
              simpa [updateWidthState, State.setReg, Function.update]
                using hnew
            · have hji' : j ≠ i := by omega
              simpa [updateWidthState, State.setReg, hji', Function.update]
                using hz j

  | negate i =>
      have hσ1 : σ1 = State.negateReg σ i := by
        simp [applyOp?] at hstep
        simp[hstep]
      subst hσ1
      constructor
      · intro j
        by_cases hji : i=j
        · subst hji
          have hrow :
              evalRowX (qs := qs) src (Register.negate (σ i)) b
                =
              - evalRowX (qs := qs) src (σ i) b := by
            simpa using
              (evalRowX_negate_raw
                (qs := qs) (src := src) (r := σ i) (b := b))
          have hnew :
              FitsSignedWidth (cur.xw i + 2)
                (- evalRowX (qs := qs) src (σ i) b) := by
            exact FitsSignedWidth_neg_widen (w := cur.xw i) (hfit := hx i)
          simpa [updateWidthState, State.negateReg, State.setReg, Function.update, hrow]
            using hnew
        · have hji' : j ≠ i := by omega
          simpa [updateWidthState, State.negateReg, State.setReg, hji', Function.update]
            using hx j
      · intro j
        by_cases hji : i=j
        · subst hji
          have hrow :
              evalRowZ (qs := qs) src (Register.negate (σ i)) b
                =
              - evalRowZ (qs := qs) src (σ i) b := by
            simpa using
              (evalRowZ_negate_raw
                (qs := qs) (src := src) (r := σ i) (b := b))
          have hnew :
              FitsSignedWidth (cur.zw i + 2)
                (- evalRowZ (qs := qs) src (σ i) b) := by
            exact FitsSignedWidth_neg_widen (w := cur.zw i) (hfit := hz i)
          simpa [updateWidthState, State.negateReg, State.setReg, Function.update, hrow]
            using hnew
        · have hji' : j ≠ i := by omega
          simpa [updateWidthState, State.negateReg, State.setReg, hji', Function.update]
            using hz j

  | addScaled dsti srci negSrc sh =>
      have hσ1 : σ1 = State.addScaledReg σ dsti srci negSrc sh := by
        simp [applyOp?] at hstep
        simp[hstep]
      subst hσ1
      constructor
      · intro j
        by_cases hjd : dsti = j
        · subst hjd
          have hrow :
              evalRowX (qs := qs) src
                (Register.addScaled (σ dsti) (σ srci) negSrc sh) b
                  =
              evalRowX (qs := qs) src (σ dsti) b
                + (if negSrc then (-1 : ℤ) else 1)
                    * ((2 : ℤ)^sh)
                    * evalRowX (qs := qs) src (σ srci) b := by
            simpa using
              (evalRowX_addScaled_raw
                (qs := qs) (src := src)
                (dstReg := σ dsti) (srcReg := σ srci)
                (negSrc := negSrc) (sh := sh) (b := b))
          have hnew :
              FitsSignedWidth (max (cur.xw dsti) (cur.xw srci + sh) + 2)
                (evalRowX (qs := qs) src (σ dsti) b
                  + (if negSrc then (-1 : ℤ) else 1)
                      * ((2 : ℤ)^sh)
                      * evalRowX (qs := qs) src (σ srci) b) := by
            exact FitsSignedWidth_addScaled_widen
              (wd := cur.xw dsti) (ws := cur.xw srci) (sh := sh)
              (negSrc := negSrc) (hdst := hx dsti) (hsrc := hx srci)
          simp [updateWidthState, State.addScaledReg, State.setReg, Function.update, hrow] at *
          rw[add_comm,← add_assoc, add_comm];simp[hnew]
        · have hjd' : j ≠ dsti := by omega
          simpa [updateWidthState, State.addScaledReg, State.setReg, hjd', Function.update]
            using hx j
      · intro j
        by_cases hjd : dsti = j
        · subst hjd
          have hrow :
              evalRowZ (qs := qs) src
                (Register.addScaled (σ dsti) (σ srci) negSrc sh) b
                  =
              evalRowZ (qs := qs) src (σ dsti) b
                + (if negSrc then (-1 : ℤ) else 1)
                    * ((2 : ℤ)^sh)
                    * evalRowZ (qs := qs) src (σ srci) b := by
            simpa using
              (evalRowZ_addScaled_raw
                (qs := qs) (src := src)
                (dstReg := σ dsti) (srcReg := σ srci)
                (negSrc := negSrc) (sh := sh) (b := b))
          have hnew :
              FitsSignedWidth (max (cur.zw dsti) (cur.zw srci + sh) + 2)
                (evalRowZ (qs := qs) src (σ dsti) b
                  + (if negSrc then (-1 : ℤ) else 1)
                      * ((2 : ℤ)^sh)
                      * evalRowZ (qs := qs) src (σ srci) b) := by
            exact FitsSignedWidth_addScaled_widen
              (wd := cur.zw dsti) (ws := cur.zw srci) (sh := sh)
              (negSrc := negSrc) (hdst := hz dsti) (hsrc := hz srci)
          simp [updateWidthState, State.addScaledReg, State.setReg, Function.update, hrow] at *
          rw[add_comm,← add_assoc, add_comm];simp[hnew]
        · have hjd' : j ≠ dsti := by omega
          simpa [updateWidthState, State.addScaledReg, State.setReg, hjd', Function.update]
            using hz j

  | phaseProduct i =>
      have hσ1 : σ1 = σ := by
        simp [applyOp?] at hstep
        simp[hstep]
      subst hσ1
      simp [updateWidthState,WidthStateSoundPlus] at *
      simp_all

/-- Folded run preservation of the proof-only invariant. -/
lemma widthStateSoundPlus_run
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k)
  (cur : WidthState k)
  (σ σf : State k)
  (ops : Prog k)
  (b : qs.Basis)
  (hrun : run? ops σ = some σf)
  (hfit : WidthStateSoundPlus (qs := qs) src cur σ b) :
  WidthStateSoundPlus
    (qs := qs)
    src
    (ops.foldl updateWidthState cur)
    σf
    b := by
  induction ops generalizing cur σ σf with
  | nil =>
      simp
      simp at hrun;aesop
  | cons op ops ih =>
      cases hstep : applyOp? σ op with
      | none =>
          simp [run?, hstep] at hrun
      | some σ1 =>
          have hrunTail : run? ops σ1 = some σf := by
            simpa [run?, hstep] using hrun
          have hfit1 :
              WidthStateSoundPlus (qs := qs) src (updateWidthState cur op) σ1 b := by
            exact widthStateSoundPlus_step
              (qs := qs) (src := src) (cur := cur)
              (σ := σ) (σ1 := σ1) (op := op) (b := b)
              hstep hfit
          simpa [List.foldl] using
            ih (cur := updateWidthState cur op) (σ := σ1) (σf := σf) hrunTail hfit1

/-! =========================================================
    Section 22: Prefix/scan bound lemmas
========================================================= -/

/-- Prefix-folded x-widths are bounded by the full scan result. -/
lemma prefix_foldl_updateWidthState_x_le_scanAux
  {k : ℕ} (i : Fin k) :
  ∀ (pre rest : List (valid_ops k)) (cur : WidthState k) (mx : NeededWidths k),
    cur.xw i ≤ mx.xneed i →
    (pre.foldl updateWidthState cur).xw i
      ≤
    (scanNeededWidthsAux cur mx (pre ++ rest)).xneed i
  | [], rest, cur, mx, hcur => by
      exact le_trans hcur (scanNeededWidthsAux_x_ge (i := i) rest cur mx)
  | op :: pre, rest, cur, mx, hcur => by
      let cur' := updateWidthState cur op
      let mx' := mergeNeededWidths mx (widthsOfState cur')
      have hcur' : cur'.xw i ≤ mx'.xneed i := by
        simp [cur', mx', mergeNeededWidths, widthsOfState]
      simpa [scanNeededWidthsAux, cur', mx'] using
        prefix_foldl_updateWidthState_x_le_scanAux
          (i := i) pre rest cur' mx' hcur'

/-- Prefix-folded z-widths are bounded by the full scan result. -/
lemma prefix_foldl_updateWidthState_z_le_scanAux
  {k : ℕ} (i : Fin k) :
  ∀ (pre rest : List (valid_ops k)) (cur : WidthState k) (mx : NeededWidths k),
    cur.zw i ≤ mx.zneed i →
    (pre.foldl updateWidthState cur).zw i
      ≤
    (scanNeededWidthsAux cur mx (pre ++ rest)).zneed i
  | [], rest, cur, mx, hcur => by
      exact le_trans hcur (scanNeededWidthsAux_z_ge (i := i) rest cur mx)
  | op :: pre, rest, cur, mx, hcur => by
      let cur' := updateWidthState cur op
      let mx' := mergeNeededWidths mx (widthsOfState cur')
      have hcur' : cur'.zw i ≤ mx'.zneed i := by
        simp [cur', mx', mergeNeededWidths, widthsOfState]
      simpa [scanNeededWidthsAux, cur', mx'] using
        prefix_foldl_updateWidthState_z_le_scanAux
          (i := i) pre rest cur' mx' hcur'

lemma prefix_foldl_updateWidthState_x_le_scanNeeded
  {k : ℕ}
  (x z : ExtReg) (ops pre rest : Prog k) (i : Fin k)
  (hops : ops = pre ++ rest) :
  (pre.foldl updateWidthState (initWidthState x z k)).xw i
    ≤
  (scanNeededWidths x z ops).xneed i := by
  rw [hops, scanNeededWidths_eq_aux]
  exact prefix_foldl_updateWidthState_x_le_scanAux
    (i := i)
    pre rest
    (initWidthState x z k)
    (widthsOfState (initWidthState x z k))
    (by simp [widthsOfState])

lemma prefix_foldl_updateWidthState_z_le_scanNeeded
  {k : ℕ}
  (x z : ExtReg) (ops pre rest : Prog k) (i : Fin k)
  (hops : ops = pre ++ rest) :
  (pre.foldl updateWidthState (initWidthState x z k)).zw i
    ≤
  (scanNeededWidths x z ops).zneed i := by
  rw [hops, scanNeededWidths_eq_aux]
  exact prefix_foldl_updateWidthState_z_le_scanAux
    (i := i)
    pre rest
    (initWidthState x z k)
    (widthsOfState (initWidthState x z k))
    (by simp [widthsOfState])

/-! =========================================================
    Section 23: Final target layout width lemmas
========================================================= -/

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

lemma widenExtRegTo_width_of_le
    (e : ExtReg) (W : ℕ)
    (h : ExtReg.width e ≤ W) :
    ExtReg.width (widenExtRegTo e W) = W := by
  simp [widenExtRegTo, ExtReg.width, ExtReg.addExtra]
  have : regSize e.base + e.extra ≤ W := by
    simp [ExtReg.width] at h
    exact h
  omega

lemma targetSignedLayoutState_xslot_width_scan
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    {k : ℕ} (x z : ExtReg) (ops : Prog k) (i : Fin k) :
    ExtReg.width
      ((targetSignedLayoutState
        (Basis := Basis) x z k (scanNeededWidths x z ops)).xslot i)
      =
    commonNeededWidth (scanNeededWidths x z ops) := by
  apply widenExtRegTo_width_of_le
  have hinit :
      ExtReg.width ((initSignedLayoutState (Basis := Basis) x z k).xslot i)
        =
      (initWidthState x z k).xw i :=
    stInit_xslot_width (Basis := Basis) x z i
  have hscan :
      (initWidthState x z k).xw i
        ≤
      (scanNeededWidths x z ops).xneed i := by
    rw [scanNeededWidths_eq_aux]
    simpa [widthsOfState] using
      scanNeededWidthsAux_x_ge
        (i := i)
        ops
        (initWidthState x z k)
        (widthsOfState (initWidthState x z k))
  have hW :
      (scanNeededWidths x z ops).xneed i + 1
        ≤
      commonNeededWidth (scanNeededWidths x z ops) :=
    commonNeededWidth_ge_xneed (scanNeededWidths x z ops) i
  rw [hinit]
  omega

lemma targetSignedLayoutState_zslot_width_scan
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    {k : ℕ} (x z : ExtReg) (ops : Prog k) (i : Fin k) :
    ExtReg.width
      ((targetSignedLayoutState
        (Basis := Basis) x z k (scanNeededWidths x z ops)).zslot i)
      =
    commonNeededWidth (scanNeededWidths x z ops) := by
  apply widenExtRegTo_width_of_le
  have hinit :
      ExtReg.width ((initSignedLayoutState (Basis := Basis) x z k).zslot i)
        =
      (initWidthState x z k).zw i :=
    stInit_zslot_width (Basis := Basis) x z i
  have hscan :
      (initWidthState x z k).zw i
        ≤
      (scanNeededWidths x z ops).zneed i := by
    rw [scanNeededWidths_eq_aux]
    simpa [widthsOfState] using
      scanNeededWidthsAux_z_ge
        (i := i)
        ops
        (initWidthState x z k)
        (widthsOfState (initWidthState x z k))
  have hW :
      (scanNeededWidths x z ops).zneed i + 1
        ≤
      commonNeededWidth (scanNeededWidths x z ops) :=
    commonNeededWidth_ge_zneed (scanNeededWidths x z ops) i
  rw [hinit]
  omega

/-! =========================================================
    Section 24: Source chunk fit and initial soundness
========================================================= -/

lemma sourceChunkXInt_fits_width_succ
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [ExtRegEncoding qs.Basis]
  [GateSemanticsFacts qs]
  {k : ℕ}
  (st : LayoutState k)
  (i : Fin k)
  (b : qs.Basis) :
  FitsSignedWidth (ExtReg.width (st.xslot i) + 1)
    (sourceChunkXInt (qs := qs) st i b) := by
  unfold sourceChunkXInt
  by_cases htop : isTopChunk i
  · simp [htop]
    exact extToInt_fits_width_succ qs (st.xslot i) b
  · simp [htop]
    apply FitsSignedWidth_of_nonneg_lt_pow
    simpa [ExtReg.toNat] using
      (ExtRegEncoding.extToNat_lt (e := st.xslot i) (b := b))

lemma sourceChunkZInt_fits_width_succ
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [ExtRegEncoding qs.Basis]
  [GateSemanticsFacts qs]
  {k : ℕ}
  (st : LayoutState k)
  (i : Fin k)
  (b : qs.Basis) :
  FitsSignedWidth (ExtReg.width (st.zslot i) + 1)
    (sourceChunkZInt (qs := qs) st i b) := by
  unfold sourceChunkZInt
  by_cases htop : isTopChunk i
  · simp [htop]
    exact extToInt_fits_width_succ qs (st.zslot i) b
  · simp [htop]
    apply FitsSignedWidth_of_nonneg_lt_pow
    simpa [ExtReg.toNat] using
      (ExtRegEncoding.extToNat_lt (e := st.zslot i) (b := b))

lemma widthStateSoundPlus_start_state
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [ExtRegEncoding qs.Basis]
  [ExtRegSplitSemantics qs.Basis]
  [GateSemanticsFacts qs]
  {k : ℕ}
  (x z : ExtReg)
  (b : qs.Basis) :
  WidthStateSoundPlus
    (qs := qs)
    (initSignedLayoutState (Basis := qs.Basis) x z k)
    (initWidthState x z k)
    State.start_state
    b := by
  constructor
  · intro i
    let st : LayoutState k :=
      initSignedLayoutState (Basis := qs.Basis) x z k

    have hfit :
        FitsSignedWidth (ExtReg.width (st.xslot i) + 1)
          (sourceChunkXInt (qs := qs) st i b) :=
      sourceChunkXInt_fits_width_succ qs st i b

    have hwidth :
        ExtReg.width (st.xslot i) =
          (initWidthState x z k).xw i := by
      simpa [st] using
        stInit_xslot_width
          (Basis := qs.Basis) x z i

    have hrow :
        evalRowX (qs := qs) st (State.start_state i) b =
          sourceChunkXInt (qs := qs) st i b := by
      simpa using
        evalRowX_start_state
          (qs := qs) st i b

    rw [hwidth] at hfit
    rw [← hrow] at hfit
    simpa [st] using hfit

  · intro i
    let st : LayoutState k :=
      initSignedLayoutState (Basis := qs.Basis) x z k

    have hfit :
        FitsSignedWidth (ExtReg.width (st.zslot i) + 1)
          (sourceChunkZInt (qs := qs) st i b) :=
      sourceChunkZInt_fits_width_succ qs st i b

    have hwidth :
        ExtReg.width (st.zslot i) =
          (initWidthState x z k).zw i := by
      simpa [st] using
        stInit_zslot_width
          (Basis := qs.Basis) x z i

    have hrow :
        evalRowZ (qs := qs) st (State.start_state i) b =
          sourceChunkZInt (qs := qs) st i b := by
      simpa using
        evalRowZ_start_state
          (qs := qs) st i b

    rw [hwidth] at hfit
    rw [← hrow] at hfit
    simpa [st] using hfit

/-! =========================================================
    Section 25: Final theorem
========================================================= -/

lemma allocated_widths_sound
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [ExtRegEncoding qs.Basis]
  [ExtRegSplitSemantics qs.Basis]
  [GateSemanticsFacts qs]
  {k : ℕ}
  (x z : ExtReg)
  (ops : Prog k)
  (b : qs.Basis) :
  let src := initSignedLayoutState (Basis := qs.Basis) x z k
  let dst := targetSignedLayoutState
    (Basis := qs.Basis) x z k (scanNeededWidths x z ops)
  ∀ {σ : State k},
    (∃ pre rest,
      ops = pre ++ rest ∧
      run? pre State.start_state = some σ) →
    (∀ i : Fin k,
      FitsSignedWidth (ExtReg.width (dst.xslot i))
        (evalRowX (qs := qs) src (σ i) b)) ∧
    (∀ i : Fin k,
      FitsSignedWidth (ExtReg.width (dst.zslot i))
        (evalRowZ (qs := qs) src (σ i) b)) := by
  dsimp
  intro σ hprefix
  rcases hprefix with ⟨pre, rest, hops, hrun⟩

  let src : LayoutState k :=
    initSignedLayoutState (Basis := qs.Basis) x z k
  let dst : LayoutState k :=
    targetSignedLayoutState
      (Basis := qs.Basis) x z k (scanNeededWidths x z ops)

  let cur0 : WidthState k := initWidthState x z k
  let curPre : WidthState k := pre.foldl updateWidthState cur0

  have hstart :
      WidthStateSoundPlus
        (qs := qs)
        src
        cur0
        State.start_state
        b := by
    simpa [src, cur0] using
      widthStateSoundPlus_start_state
        (qs := qs) (x := x) (z := z) (b := b)

  have hpre :
      WidthStateSoundPlus
        (qs := qs)
        src
        curPre
        σ
        b := by
    simpa [src, cur0, curPre] using
      widthStateSoundPlus_run
        (qs := qs)
        (src := src)
        (cur := cur0)
        (σ := State.start_state)
        (σf := σ)
        (ops := pre)
        (b := b)
        hrun
        hstart

  rcases hpre with ⟨hpreX, hpreZ⟩

  constructor
  · intro i
    have hcur :
        curPre.xw i + 1
          ≤ commonNeededWidth (scanNeededWidths x z ops) := by
      have hprefix_le :
          curPre.xw i ≤ (scanNeededWidths x z ops).xneed i := by
        simpa [curPre, cur0] using
          prefix_foldl_updateWidthState_x_le_scanNeeded
            (x := x) (z := z)
            (ops := ops) (pre := pre) (rest := rest)
            (i := i) hops
      have hW :
          (scanNeededWidths x z ops).xneed i + 1
            ≤ commonNeededWidth (scanNeededWidths x z ops) :=
        commonNeededWidth_ge_xneed (scanNeededWidths x z ops) i
      omega

    have hdst :
        ExtReg.width (dst.xslot i)
          =
        commonNeededWidth (scanNeededWidths x z ops) := by
      simpa [dst] using
        targetSignedLayoutState_xslot_width_scan
          (Basis := qs.Basis) x z ops i

    exact FitsSignedWidth_mono
      (by rw [hdst]; exact hcur)
      (hpreX i)

  · intro i
    have hcur :
        curPre.zw i + 1
          ≤ commonNeededWidth (scanNeededWidths x z ops) := by
      have hprefix_le :
          curPre.zw i ≤ (scanNeededWidths x z ops).zneed i := by
        simpa [curPre, cur0] using
          prefix_foldl_updateWidthState_z_le_scanNeeded
            (x := x) (z := z)
            (ops := ops) (pre := pre) (rest := rest)
            (i := i) hops
      have hW :
          (scanNeededWidths x z ops).zneed i + 1
            ≤ commonNeededWidth (scanNeededWidths x z ops) :=
        commonNeededWidth_ge_zneed (scanNeededWidths x z ops) i
      omega

    have hdst :
        ExtReg.width (dst.zslot i)
          =
        commonNeededWidth (scanNeededWidths x z ops) := by
      simpa [dst] using
        targetSignedLayoutState_zslot_width_scan
          (Basis := qs.Basis) x z ops i

    exact FitsSignedWidth_mono
      (by rw [hdst]; exact hcur)
      (hpreZ i)
