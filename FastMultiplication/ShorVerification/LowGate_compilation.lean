import FastMultiplication.ShorVerification.Basic
import FastMultiplication.one_reg_synth_proof_2
import Mathlib.Data.Finset.Basic

namespace Shor
open Gate
open Operations

/-! =========================================================
    Section 1: Core QFT phase definitions
========================================================= -/

/-- A 1-qubit register at index `q`. -/
def qubitReg (q : ℕ) : Reg := ⟨q, q + 1⟩

/-- Standard QFT phase schedule. -/
noncomputable def qftPhi (m : ℕ) : ℝ := (2 * Real.pi) / (2^m)

/-- Primitive `N`-th root of unity `exp(2πi/N)`. -/
noncomputable def ω (N : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))

/-- Power of the primitive root `ω N`. -/
noncomputable def ωPow (N k : ℕ) : ℂ :=
  (ω N) ^ k

/-- QFT phase factor `ω_N^(x*y)`. -/
noncomputable def qftPhase (N x y : ℕ) : ℂ :=
  ωPow N (x * y)

/-! =========================================================
    Section 2: Finite reindexing equivalence
========================================================= -/

/-- Equivalence between `Fin A × Fin B` and `Fin (A * B)`. -/
noncomputable def finMulAddEquiv (A B : ℕ) :
    (Fin A × Fin B) ≃ Fin (A * B) where
  toFun p :=
    let i : Fin A := p.1
    let j : Fin B := p.2
    ⟨i.1 + A * j.1, by
      rcases i with ⟨i, hi⟩
      rcases j with ⟨j, hj⟩
      calc
        i + A * j < A + A * j := Nat.add_lt_add_right hi _
        _ = A * (j + 1)       := by
              simp [Nat.mul_add, Nat.add_comm]
        _ ≤ A * B             := by
              exact Nat.mul_le_mul_left A (Nat.succ_le_of_lt hj)
    ⟩

  invFun n :=
    if hA : 0 < A then
      (⟨n.1 % A, Nat.mod_lt _ hA⟩,
       ⟨n.1 / A, by
          exact Nat.div_lt_of_lt_mul (by
            simp)⟩)
    else
      by
        have : False := by
          have hA0 : A = 0 := Nat.eq_zero_of_not_pos hA
          subst hA0
          simp_all
          simp at n
          simpa using n.elim0
        exact False.elim this

  left_inv := by
    intro p
    rcases p with ⟨i, j⟩
    cases A with
    | zero =>
        exact i.elim0
    | succ A =>
        have hA : 0 < A.succ := Nat.succ_pos _
        simp
        constructor
        · apply Fin.ext
          have hi_lt : (i.1) < (A + 1) := i.2
          simp [Nat.mod_eq_of_lt hi_lt]
        · apply Fin.ext
          have hi_lt : (i.1) < (A + 1) := i.2
          have hi_div : (i.1 / (A + 1)) = 0 := by
            exact Nat.div_eq_of_lt hi_lt
          calc
            (i.1 + (A + 1) * j.1) / (A + 1)
                = j.1 + (i.1 / (A + 1)) := by
                    simpa [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
                      using (Nat.add_mul_div_right i.1 j.1 (Nat.succ_pos A))
            _   = j.1 := by simp [hi_div]

  right_inv := by
    intro n
    cases A with
    | zero =>
        simp at n
        exact n.elim0
    | succ A =>
        have hA : 0 < A.succ := Nat.succ_pos _
        ext
        simp
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (Nat.mod_add_div (n.1) (A + 1))

/-! =========================================================
    Section 3: Low-level gate language
========================================================= -/

/-- Low-level target gate language for lowering. -/
inductive LowGate : Type
  | id : LowGate
  | seq : LowGate → LowGate → LowGate
  | adj : LowGate → LowGate
  | H : ℕ → LowGate
  | X : ℕ → LowGate
  | Prim : String → List ℕ → LowGate
  | ShiftL    : (r : Reg) → (n : ℕ) → LowGate
  | ShiftR    : (r : Reg) → (n : ℕ) → LowGate
  | Negate    : (r : Reg) → LowGate
  | AddScaled : (dst src : Reg) → (negSrc : Bool) → (shift : ℕ) → LowGate
  | Naive_PhaseProd : (phi : Real) → (x z : Reg) → LowGate
  | Naive_CPhaseProd : (ctrl : ℕ) → (phi : Real) → (x z : Reg) → LowGate
deriving Inhabited

namespace LowGate

/-- Sequential composition notation for low gates. -/
infixr:80 " ;; " => LowGate.seq

/-- Adjoint notation for low gates. -/
prefix:90 "†" => LowGate.adj

end LowGate

/-! =========================================================
    Section 4: Register layouts and slot geometry
========================================================= -/

/-- A `k`-slot register layout with pairwise disjoint slots. -/
structure Layout (k : ℕ) where
  slot : Fin k → Reg
  disjoint : ∀ i j, i ≠ j → Disjoint (slot i) (slot j)

/-- Size of chunk `i` when splitting a register into `k` parts. -/
def chunkSize (n k : ℕ) (i : Fin k) : ℕ :=
  let q := n / k
  let rem := n % k
  q + if i.1 < rem then 1 else 0

/-- Starting offset of chunk `i` in an even split into `k` parts. -/
def chunkStart (n k : ℕ) (i : Fin k) : ℕ :=
  let q := n / k
  let rem := n % k
  i.1 * q + Nat.min i.1 rem

/-- Contiguous near-even splitting of a register into `k` chunks. -/
def layoutOfReg (r : Reg) (k : ℕ) : Layout k where
  slot := fun i =>
    let n := regSize r
    let s := chunkStart n k i
    let m := chunkSize n k i
    ⟨r.lo + s, r.lo + s + m⟩
  disjoint := by
    intro i j hij
    wlog hlt : i.1 < j.1 generalizing i j
    · have hji : j.1 < i.1 := by
        have hne : j.1 ≠ i.1 := by
          intro h
          apply hij
          apply Fin.ext
          rw [h]
        omega
      simp [Disjoint] at *
      have h_not_eq : j ≠ i := by omega
      have final_or := this j i h_not_eq hji
      omega
    left
    simp [chunkStart, chunkSize, regSize]
    have hmain :
      chunkStart (regSize r) k i + chunkSize (regSize r) k i
        ≤ chunkStart (regSize r) k j := by
      unfold chunkStart chunkSize regSize
      simp
      split_ifs
      have h_le : i.val + 1 ≤ j.val := Nat.succ_le_of_lt hlt
      set N := r.hi - r.lo
      set Q := N / k
      set R := N % k
      by_cases hj : ↑j < R
      · have hi : i.val < R := by omega
        have h1 : (j.val).min R = ↑j := Nat.min_eq_left (Nat.le_of_lt hj)
        have : (i.val).min R = ↑i := Nat.min_eq_left (Nat.le_of_lt hi)
        rw [this, h1]
        have hQ : i.1 * Q + i.1 + (Q + 1) = (i.1 + 1) * (Q + 1) := by
          ring
        have hJ : j.1 * Q + j.1 = j.1 * (Q + 1) := by
          ring
        rw [hQ, hJ]
        gcongr
      · have hi : i.val < R := by omega
        have hi_min : (i.1).min R = i.1 := Nat.min_eq_left (Nat.le_of_lt hi)
        have hj_min : (j.1).min R = R := Nat.min_eq_right (Nat.le_of_not_gt hj)
        have h_le : i.1 + 1 ≤ j.1 := Nat.succ_le_of_lt hlt
        rw [hi_min, hj_min]
        have hiR : i.1 + 1 ≤ R := Nat.succ_le_of_lt hi
        have hmul : Q * (i.1 + 1) ≤ Q * j.1 :=
          Nat.mul_le_mul_left Q h_le
        have hsum : Q * (i.1 + 1) + (i.1 + 1) ≤ Q * j.1 + R :=
          Nat.add_le_add hmul hiR
        have hrewriteL : i.1 * Q + i.1 + (Q + 1) = Q * (i.1 + 1) + (i.1 + 1) := by
          ring
        have hrewriteR : j.1 * Q + R = Q * j.1 + R := by
          ring
        rw [hrewriteL, hrewriteR]
        exact hsum
      · set N : ℕ := r.hi - r.lo
        set Q : ℕ := N / k
        set R : ℕ := N % k
        have hi : ¬ i.val < R := by omega
        have hi_ge : R ≤ i.1 := Nat.le_of_not_gt hi
        have hj_ge : R ≤ j.1 := le_trans hi_ge (Nat.le_of_lt hlt)
        have hi_min : (i.1).min R = R := Nat.min_eq_right hi_ge
        have hj_min : (j.1).min R = R := Nat.min_eq_right hj_ge
        have hle : i.1 + 1 ≤ j.1 := Nat.succ_le_of_lt hlt
        rw [hi_min, hj_min]
        have hmul : (i.1 + 1) * Q ≤ j.1 * Q := Nat.mul_le_mul_right Q hle
        have hrewrite : i.1 * Q + R + (Q + 0) = (i.1 + 1) * Q + R := by
          ring
        rw [hrewrite]
        exact Nat.add_le_add_right hmul R
    have := Nat.add_le_add_left hmain r.lo
    simpa [chunkStart, chunkSize, regSize, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this

/-- Each slot in a split layout has size at most the original register. -/
lemma slot_size_le (x : Reg) (k : ℕ) (hk : 1 ≤ k) (i : Fin k) :
  regSize ((layoutOfReg x k).slot i) ≤ regSize x := by
  dsimp [layoutOfReg]
  simp [regSize]
  generalize (x.hi - x.lo) = n
  unfold chunkSize
  have hk : 1 ≤ k := by omega
  have hdiv : n / k * k + n % k = n := by
    rw [mul_comm]
    exact Nat.div_add_mod n k
  have hmul : n / k ≤ n / k * k := by
    calc
      n / k = n / k * 1 := by rw [Nat.mul_one]
      _ ≤ n / k * k := Nat.mul_le_mul_left (n / k) hk
  simp
  split_ifs with h
  · have hrem : 1 ≤ n % k := by omega
    omega
  · omega

/-- If `k > 1` and the register is nontrivial, each slot is strictly smaller. -/
lemma slot_size_lt (x : Reg) {k : ℕ} (hk : 1 < k) (hx : 1 < regSize x) (i : Fin k) :
  regSize ((layoutOfReg x k).slot i) < regSize x := by
  dsimp [layoutOfReg] at *
  simp [regSize] at *
  generalize h_n : (x.hi - x.lo) = n at *
  unfold chunkSize
  have hdiv : n / k * k + n % k = n := by
    rw [mul_comm]
    exact Nat.div_add_mod n k
  simp
  split_ifs with h
  ·
    by_cases hq : n / k = 0
    · omega
    · have hq_pos : 1 ≤ n / k := by
        have hq_pos : 0 < n / k := Nat.pos_of_ne_zero hq
        omega
      have hmul : n / k * 2 ≤ n / k * k := Nat.mul_le_mul_left (n / k) hk
      omega
  ·
    by_cases hq : n / k = 0
    · omega
    · have hq_pos : 1 ≤ n / k := by
        have hq_pos : 0 < n / k := Nat.pos_of_ne_zero hq
        omega
      have hmul : n / k * 2 ≤ n / k * k := Nat.mul_le_mul_left (n / k) hk
      have hrem : 0 ≤ n % k := by omega
      omega

/-! =========================================================
    Section 5: Layout-state evolution under valid ops
========================================================= -/

/-- Mutable slot assignment state for both `x` and `z` blocks. -/
structure LayoutState (k : ℕ) where
  xslot : Fin k → Reg
  zslot : Fin k → Reg

/-- Initial slot assignment state from input registers `x` and `z`. -/
def initLayoutState (x z : Reg) (k : ℕ) : LayoutState k where
  xslot := (layoutOfReg x k).slot
  zslot := (layoutOfReg z k).slot

/-- Extend a register to the right by `n`. -/
def growRight (r : Reg) (n : ℕ) : Reg :=
  { lo := r.lo, hi := r.hi + n }

/-- Shrink a register on the right by `n`. -/
def shrinkRight (r : Reg) (n : ℕ) : Reg :=
  { lo := r.lo, hi := r.hi - n }

/-- Update one `x`-slot in a layout state. -/
def updateXSlot {k : ℕ} (st : LayoutState k) (i : Fin k) (r : Reg) : LayoutState k :=
  { st with xslot := Function.update st.xslot i r }

/-- Update one `z`-slot in a layout state. -/
def updateZSlot {k : ℕ} (st : LayoutState k) (i : Fin k) (r : Reg) : LayoutState k :=
  { st with zslot := Function.update st.zslot i r }

/-- Update both `x`- and `z`-slots at the same index. -/
def updateBothSlots {k : ℕ} (st : LayoutState k) (i : Fin k) (rx rz : Reg) : LayoutState k :=
  { xslot := Function.update st.xslot i rx
    zslot := Function.update st.zslot i rz }

/-- Apply a left shift to the selected slot pair. -/
def applyShiftL {k : ℕ} (st : LayoutState k) (i : Fin k) (n : ℕ) : LayoutState k :=
  let rx := st.xslot i
  let rz := st.zslot i
  updateBothSlots st i (growRight rx n) (growRight rz n)

/-- Apply a right shift to the selected slot pair. -/
def applyShiftR {k : ℕ} (st : LayoutState k) (i : Fin k) (n : ℕ) : LayoutState k :=
  let rx := st.xslot i
  let rz := st.zslot i
  updateBothSlots st i (shrinkRight rx n) (shrinkRight rz n)

/-- Target size for the destination `x`-slot after `AddScaled`. -/
def addScaledTargetX {k : ℕ} (st : LayoutState k) (dst src : Fin k) (sh : ℕ) : ℕ :=
  let lenDst := regSize (st.xslot dst)
  let lenSrc := regSize (st.xslot src) + sh
  1 + max lenDst lenSrc

/-- Target size for the destination `z`-slot after `AddScaled`. -/
def addScaledTargetZ {k : ℕ} (st : LayoutState k) (dst src : Fin k) (sh : ℕ) : ℕ :=
  let lenDst := regSize (st.zslot dst)
  let lenSrc := regSize (st.zslot src) + sh
  1 + max lenDst lenSrc

/-- Resize a register to a new size while preserving the lower endpoint. -/
def resizeTo (r : Reg) (newSize : ℕ) : Reg :=
  { lo := r.lo, hi := r.lo + newSize }

/-- Apply an `AddScaled` op to the layout state. -/
def applyAddScaled {k : ℕ} (st : LayoutState k) (dst src : Fin k) (sh : ℕ) : LayoutState k :=
  let rxDst := st.xslot dst
  let rzDst := st.zslot dst
  let newX := resizeTo rxDst (addScaledTargetX st dst src sh)
  let newZ := resizeTo rzDst (addScaledTargetZ st dst src sh)
  updateBothSlots st dst newX newZ

/-- Evolve layout state according to a single valid synthesized operation. -/
def updateLayoutState {k : ℕ} (st : LayoutState k) : valid_ops k → LayoutState k
  | .shiftL i n => applyShiftL st i n
  | .shiftR i n => applyShiftR st i n
  | .negate _i => st
  | .addScaled dst src _negsrc sh => applyAddScaled st dst src sh
  | .phaseProduct _ => st

/-! =========================================================
    Section 6: Interpolation and phase coefficients
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

/-- Coefficient function induced by the interpolation points. -/
noncomputable def phaseCoeffOfPts
  (k : ℕ) (x : Reg)
  (pts : List Point) (hpts : pts.length = q k) :
  Fin (q k) → ℚ :=
  phaseCoeffFromPts k (ptsToFin k pts hpts) (phaseRadix x k)
-- /-- Slot-indexed phase coefficients derived from interpolation points. -/
-- noncomputable def slotPhaseCoeffFromPts
--   (k : ℕ) (hk : 1 < k)
--   (x : Reg)
--   (pts : List Point)
--   (hpts : pts.length = q k) :
--   Fin k → ℚ :=
--   let ptsF : Fin (q k) → Point := ptsToFin k pts hpts
--   let coeffF : Fin (q k) → ℚ := phaseCoeffFromPts k ptsF (phaseRadix x k)
--   fun i => coeffF (slotToEvalIdx k hk i)

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
/-! =========================================================
    Section 7: Compilation from valid ops to `Gate`
========================================================= -/

def compileAnnotatedOpsToGateAux
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ)
  (phaseCoeff : Fin (q k) → ℚ)
  (st : LayoutState k)
  (ops : List (AnnotatedOp k)) : Gate :=
  match ops with
  | [] => Gate.id
  | ⟨op, term?⟩ :: rest =>
      let st' := updateLayoutState st op
      let tail := compileAnnotatedOpsToGateAux k hk phi phaseCoeff st' rest
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
              Gate.PhaseProd
                (phi * ((phaseCoeff l : ℚ) : ℝ))
                (st.xslot i)
                (st.zslot i) ;; tail
          | none =>
              tail


noncomputable def compileOpsToGate
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ)
  (x z : Reg)
  (phaseCoeff : Fin (q k) → ℚ)
  (ops : List (valid_ops k)) : Gate :=
  let annOps : List (AnnotatedOp k) :=
    annotatePhaseTermsAux k 0 ops
  compileAnnotatedOpsToGateAux
    k hk phi phaseCoeff (initLayoutState x z k) annOps


def annotatedPointBlock
  (k : ℕ)
  (hk : 0 < k)
  (ptsF : Fin (q k) → Point)
  (l : Fin (q k)) : List (AnnotatedOp k) :=
  annotatePhaseTermsAux k l.1 (opsForPointWithProduct hk (ptsF l))


def updateLayoutStateList {k : ℕ}
  (st : LayoutState k) (ops : List (AnnotatedOp k)) : LayoutState k :=
  ops.foldl (fun st a => updateLayoutState st a.op) st

-- def nextStateAfterPoint
--   (k : ℕ) (hk: 0 < k)
--   (st : LayoutState k)
--   (l : Fin (q k))
--   (pt : Point) : LayoutState k :=
--   updateLayoutStateList st
--     (annotatePhaseTermsAux k l.1 (opsForPointWithProduct hk pt))

def annotatedPointBlockFromList
  (k : ℕ)
  (hk0 : 0 < k)
  (n : ℕ)
  (pt : Point) : List (AnnotatedOp k) :=
  annotatePhaseTermsAux k n (opsForPointWithProduct hk0 pt)

-- /-- The layout state after one point-block. -/
-- def nextStateAfterPointBlock
--   (k : ℕ)
--   (hk0 : 0 < k)
--   (st : LayoutState k)
--   (n : ℕ)
--   (pt : Point) : LayoutState k :=
--   updateLayoutStateList st (annotatedPointBlockFromList k hk0 n pt)

/-- Compile exactly one point-block from the current layout state. -/
noncomputable def compilePointBlock
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ)
  (phaseCoeff : Fin (q k) → ℚ)
  (st : LayoutState k)
  (n : ℕ)
  (pt : Point) : Gate :=
  compileAnnotatedOpsToGateAux
    k hk phi phaseCoeff st
    (annotatedPointBlockFromList k (by omega) n pt)

/--
Recursive point-structured compiler.

This is the version whose recursion matches the syntax of `pts`.
-/
noncomputable def compilePointsAux
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ)
  (phaseCoeff : Fin (q k) → ℚ) :
  LayoutState k → ℕ → List Point → Gate
  | _st, _, [] => Gate.id
  | st, n, pt :: pts =>
      let block :=
        compilePointBlock k hk phi phaseCoeff st n pt
      -- let st' :=
      --   nextStateAfterPointBlock k (by omega) st n pt
      Gate.seq block (compilePointsAux k hk phi phaseCoeff st (n + 1) pts)


/-- Top-level point-structured compiler for `genOpsWithProduct`. -/
noncomputable def compileGenOpsToGate
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ)
  (x z : Reg)
  (phaseCoeff : Fin (q k) → ℚ)
  (pts : List Point) : Gate :=
  compilePointsAux
    k hk phi phaseCoeff
    (initLayoutState x z k) 0 pts



/-! =========================================================
    Section 10: Small register arithmetic lemmas
========================================================= -/

/-- Removing the leftmost qubit decreases register size by one. -/
@[simp] lemma regSize_rest (r : Reg) :
    regSize (⟨r.lo + 1, r.hi⟩ : Reg) = regSize r - 1 := by
  simp [regSize, Nat.sub_sub]

/-! =========================================================
    Section 11: Semantics for low-level gates
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

class GateSemanticsFacts (qs : QSemantics) [RegEncoding qs.Basis] : Type where
  eval_QFT_size0 :
    ∀ (r : Reg) (ψ : qs.State),
      regSize r = 0 →
      qs.eval (Gate.QFT r) ψ = qs.eval Gate.id ψ

  eval_QFT_size1 :
    ∀ (r : Reg) (ψ : qs.State),
      regSize r = 1 →
      qs.eval (Gate.QFT r) ψ = qs.eval (Gate.H r.lo) ψ

  eval_QFT_ket :
    ∀ (r : Reg) (b : qs.Basis),
      qs.eval (Gate.QFT r) (qs.ket b)
        =
      ((1 / Real.sqrt ((2^(regSize r) : ℕ) : ℝ) : ℂ)) •
        ∑ y : Fin (2^(regSize r)),
          (qftPhase (2^(regSize r)) (RegEncoding.toNat r b) y.1) •
            qs.ket (RegEncoding.writeNat r y.1 b)

  eval_PhaseProd_ket :
    ∀ (phi : ℝ) (x z : Reg) (b : qs.Basis),
      qs.eval (Gate.PhaseProd phi x z) (qs.ket b)
        =
      (Complex.exp (phi * Complex.I *
          ((RegEncoding.toNat x b : ℂ) * (RegEncoding.toNat z b : ℂ)))) •
        qs.ket b

  eval_ShiftL_pair_ket :
    ∀ {k : ℕ} (st : LayoutState k) (i : Fin k) (n : ℕ) (b : qs.Basis),
      ∃ b' : qs.Basis,
        qs.eval
          (Gate.seq
            (Gate.ShiftL (st.xslot i) n)
            (Gate.ShiftL (st.zslot i) n))
          (qs.ket b)
          = qs.ket b' ∧
        RegEncoding.toNat ((applyShiftL st i n).xslot i) b'
          =
        RegEncoding.toNat (st.xslot i) b * 2^n ∧
        RegEncoding.toNat ((applyShiftL st i n).zslot i) b'
          =
        RegEncoding.toNat (st.zslot i) b * 2^n

  eval_ShiftR_pair_ket :
    ∀ {k : ℕ} (st : LayoutState k) (i : Fin k) (n : ℕ) (b : qs.Basis),
      RegEncoding.toNat (st.xslot i) b % 2^n = 0 →
      RegEncoding.toNat (st.zslot i) b % 2^n = 0 →
      ∃ b' : qs.Basis,
        qs.eval
          (Gate.seq
            (Gate.ShiftR (st.xslot i) n)
            (Gate.ShiftR (st.zslot i) n))
          (qs.ket b)
          = qs.ket b' ∧
        RegEncoding.toNat ((applyShiftR st i n).xslot i) b'
          =
        RegEncoding.toNat (st.xslot i) b / 2^n ∧
        RegEncoding.toNat ((applyShiftR st i n).zslot i) b'
          =
        RegEncoding.toNat (st.zslot i) b / 2^n

  eval_Negate_pair_ket :
    ∀ {k : ℕ} (st : LayoutState k) (i : Fin k) (b : qs.Basis),
      ∃ b' : qs.Basis,
        qs.eval
          (Gate.seq
            (Gate.Negate (st.xslot i))
            (Gate.Negate (st.zslot i)))
          (qs.ket b)
          = qs.ket b' ∧
        RegEncoding.toNat (st.xslot i) b'
          =
        tcNegVal (st.xslot i) (RegEncoding.toNat (st.xslot i) b) ∧
        RegEncoding.toNat (st.zslot i) b'
          =
        tcNegVal (st.zslot i) (RegEncoding.toNat (st.zslot i) b)

  eval_AddScaled_pair_ket :
    ∀ {k : ℕ} (st : LayoutState k) (dst src : Fin k) (negSrc : Bool) (sh : ℕ)
      (b : qs.Basis),
      ∃ b' : qs.Basis,
        qs.eval
          (Gate.seq
            (Gate.AddScaled (st.xslot dst) (st.xslot src) negSrc sh)
            (Gate.AddScaled (st.zslot dst) (st.zslot src) negSrc sh))
          (qs.ket b)
          = qs.ket b' ∧
        RegEncoding.toNat ((applyAddScaled st dst src sh).xslot dst) b'
          =
        tcAddScaledVal ((applyAddScaled st dst src sh).xslot dst)
          (st.xslot src) negSrc sh b ∧
        RegEncoding.toNat ((applyAddScaled st dst src sh).zslot dst) b'
          =
        tcAddScaledVal ((applyAddScaled st dst src sh).zslot dst)
          (st.zslot src) negSrc sh b


variable (qs : QSemantics) [RegEncoding qs.Basis]
variable [GateSemanticsFacts qs]

/-! =========================================================
    Section 13: Extensionality from basis states
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

open scoped BigOperators

open scoped BigOperators

/-- Mathematically exact polynomial evaluation of a register's chunks at a point.
    (No sorry here, purely constructive). -/
noncomputable def pointEval {qs : QSemantics} [RegEncoding qs.Basis]
  (r : Reg) (k : ℕ) (hk : 0 < k) (b : qs.Basis) (pt : Point) : ℝ :=
  match pt with
  | .int z => ∑ i : Fin k,
      (RegEncoding.toNat ((layoutOfReg r k).slot i) b : ℝ) * (z : ℝ) ^ (i.val)
  | .inf   =>
      RegEncoding.toNat ((layoutOfReg r k).slot ⟨k - 1, Nat.sub_lt hk (by decide)⟩) b



/-- The mathematical Toom-Cook phase decomposition theorem. -/
lemma toom_cook_decomposition
  {qs : QSemantics} [RegEncoding qs.Basis]
  (k : ℕ) (hk : 1 < k) (x z : Reg) (b : qs.Basis)
  (pts : List Point) (hpts : pts.length = q k)
  (coeff : Fin (q k) → ℚ)
  (hcoeff : coeff = phaseCoeffFromPts k (ptsToFin k pts hpts) (phaseRadix x k)) :
  (∑ i : Fin pts.length, (coeff ⟨i.val, by rw [←hpts]; exact i.is_lt⟩ : ℝ) *
    pointEval x k (by omega) b (pts.get i) *
    pointEval z k (by omega) b (pts.get i))
  = (RegEncoding.toNat x b : ℝ) * (RegEncoding.toNat z b : ℝ) := by sorry

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
    Section 14: Compiler correctness theorems
========================================================= -/
def slotVal
  (x : Reg) (k : ℕ) (j : Fin k) (b : qs.Basis) : ℕ :=
  RegEncoding.toNat ((layoutOfReg x k).slot j) b

def pointValue
  (k : ℕ) (pt : Point) (x : Reg) (b : qs.Basis) : ℤ :=
  ∑ j : Fin k, (expectedRow (k := k) pt j) * (slotVal (qs := qs) x k j b : ℤ)


/-- Expand the new annotated `compileOpsToGate` into its auxiliary compiler. -/
lemma compileOpsToGate_eq_aux
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ) (x z : Reg)
  (phaseCoeff : Fin (q k) → ℚ)
  (ops : List (valid_ops k)) :
  compileOpsToGate k hk phi x z phaseCoeff ops
    =
  let annOps : List (AnnotatedOp k) :=
    annotatePhaseTermsAux k 0 ops
  compileAnnotatedOpsToGateAux
    k hk phi phaseCoeff (initLayoutState x z k) annOps := by
  rfl

/-- The annotated auxiliary compiler sends the empty op list to the identity gate. -/
lemma compileAnnotatedOpsToGateAux_nil
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ)
  (phaseCoeff : Fin (q k) → ℚ)
  (st : LayoutState k) :
  compileAnnotatedOpsToGateAux k hk phi phaseCoeff st [] = Gate.id := by
  simp [compileAnnotatedOpsToGateAux]

/-- Unfold the annotated auxiliary compiler on a leading `shiftL`. -/
lemma compileAnnotatedOpsToGateAux_cons_shiftL
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ)
  (phaseCoeff : Fin (q k) → ℚ)
  (st : LayoutState k)
  (i : Fin k) (n : ℕ)
  (term? : Option (Fin (q k)))
  (rest : List (AnnotatedOp k)) :
  compileAnnotatedOpsToGateAux k hk phi phaseCoeff st
      ({ op := .shiftL i n, phaseTerm? := term? } :: rest)
    =
  Gate.ShiftL (st.xslot i) n ;;
  Gate.ShiftL (st.zslot i) n ;;
  compileAnnotatedOpsToGateAux
    k hk phi phaseCoeff
    (updateLayoutState st (.shiftL i n)) rest := by
  simp [compileAnnotatedOpsToGateAux, updateLayoutState]

/-- Unfold the annotated auxiliary compiler on a leading `shiftR`. -/
lemma compileAnnotatedOpsToGateAux_cons_shiftR
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ)
  (phaseCoeff : Fin (q k) → ℚ)
  (st : LayoutState k)
  (i : Fin k) (n : ℕ)
  (term? : Option (Fin (q k)))
  (rest : List (AnnotatedOp k)) :
  compileAnnotatedOpsToGateAux k hk phi phaseCoeff st
      ({ op := .shiftR i n, phaseTerm? := term? } :: rest)
    =
  Gate.ShiftR (st.xslot i) n ;;
  Gate.ShiftR (st.zslot i) n ;;
  compileAnnotatedOpsToGateAux
    k hk phi phaseCoeff
    (updateLayoutState st (.shiftR i n)) rest := by
  simp [compileAnnotatedOpsToGateAux, updateLayoutState]

/-- Unfold the annotated auxiliary compiler on a leading `negate`. -/
lemma compileAnnotatedOpsToGateAux_cons_negate
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ)
  (phaseCoeff : Fin (q k) → ℚ)
  (st : LayoutState k)
  (i : Fin k)
  (term? : Option (Fin (q k)))
  (rest : List (AnnotatedOp k)) :
  compileAnnotatedOpsToGateAux k hk phi phaseCoeff st
      ({ op := .negate i, phaseTerm? := term? } :: rest)
    =
  Gate.Negate (st.xslot i) ;;
  Gate.Negate (st.zslot i) ;;
  compileAnnotatedOpsToGateAux
    k hk phi phaseCoeff
    (updateLayoutState st (.negate i)) rest := by
  simp [compileAnnotatedOpsToGateAux, updateLayoutState]

/-- Unfold the annotated auxiliary compiler on a leading `addScaled`. -/
lemma compileAnnotatedOpsToGateAux_cons_addScaled
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ)
  (phaseCoeff : Fin (q k) → ℚ)
  (st : LayoutState k)
  (dst src : Fin k) (negsrc : Bool) (sh : ℕ)
  (term? : Option (Fin (q k)))
  (rest : List (AnnotatedOp k)) :
  compileAnnotatedOpsToGateAux k hk phi phaseCoeff st
      ({ op := .addScaled dst src negsrc sh, phaseTerm? := term? } :: rest)
    =
  Gate.AddScaled (st.xslot dst) (st.xslot src) negsrc sh ;;
  Gate.AddScaled (st.zslot dst) (st.zslot src) negsrc sh ;;
  compileAnnotatedOpsToGateAux
    k hk phi phaseCoeff
    (updateLayoutState st (.addScaled dst src negsrc sh)) rest := by
  simp [compileAnnotatedOpsToGateAux, updateLayoutState]

/-- Unfold the annotated auxiliary compiler on a leading `phaseProduct` with an assigned phase term. -/
lemma compileAnnotatedOpsToGateAux_cons_phaseProduct_some
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ)
  (phaseCoeff : Fin (q k) → ℚ)
  (st : LayoutState k)
  (i : Fin k)
  (l : Fin (q k))
  (rest : List (AnnotatedOp k)) :
  compileAnnotatedOpsToGateAux k hk phi phaseCoeff st
      ({ op := .phaseProduct i, phaseTerm? := some l } :: rest)
    =
  Gate.PhaseProd
      (phi * ((phaseCoeff l : ℚ) : ℝ))
      (st.xslot i)
      (st.zslot i) ;;
  compileAnnotatedOpsToGateAux
    k hk phi phaseCoeff
    (updateLayoutState st (.phaseProduct i)) rest := by
  simp [compileAnnotatedOpsToGateAux, updateLayoutState]

/-- Unfold the annotated auxiliary compiler on a leading `phaseProduct` with no assigned phase term. -/
lemma compileAnnotatedOpsToGateAux_cons_phaseProduct_none
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ)
  (phaseCoeff : Fin (q k) → ℚ)
  (st : LayoutState k)
  (i : Fin k)
  (rest : List (AnnotatedOp k)) :
  compileAnnotatedOpsToGateAux k hk phi phaseCoeff st
      ({ op := .phaseProduct i, phaseTerm? := none } :: rest)
    =
  compileAnnotatedOpsToGateAux
    k hk phi phaseCoeff
    (updateLayoutState st (.phaseProduct i)) rest := by
  simp [compileAnnotatedOpsToGateAux, updateLayoutState]

lemma eval_compileAnnotatedOpsToGateAux_cons
  (qs : QSemantics) [RegEncoding qs.Basis]
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ)
  (phaseCoeff : Fin (q k) → ℚ)
  (st : LayoutState k)
  (a : AnnotatedOp k)
  (rest : List (AnnotatedOp k))
  (ψ : qs.State) :
  qs.eval (compileAnnotatedOpsToGateAux k hk phi phaseCoeff st (a :: rest)) ψ
    =
  qs.eval
    ((compileAnnotatedOpsToGateAux k hk phi phaseCoeff st [a]) ;;
     (compileAnnotatedOpsToGateAux k hk phi phaseCoeff (updateLayoutState st a.op) rest))
    ψ := by
  rcases a with ⟨op, term?⟩
  cases op with
  | shiftL i n =>
      cases term? with
      | none =>
          rw [compileAnnotatedOpsToGateAux_cons_shiftL]
          simp [compileAnnotatedOpsToGateAux, updateLayoutState, qs.eval_seq, qs.eval_id]
      | some l =>
          rw [compileAnnotatedOpsToGateAux_cons_shiftL]
          simp [compileAnnotatedOpsToGateAux, updateLayoutState, qs.eval_seq, qs.eval_id]

  | shiftR i n =>
      cases term? with
      | none =>
          rw [compileAnnotatedOpsToGateAux_cons_shiftR]
          simp [compileAnnotatedOpsToGateAux, updateLayoutState, qs.eval_seq, qs.eval_id]
      | some l =>
          rw [compileAnnotatedOpsToGateAux_cons_shiftR]
          simp [compileAnnotatedOpsToGateAux, updateLayoutState, qs.eval_seq, qs.eval_id]

  | negate i =>
      cases term? with
      | none =>
          rw [compileAnnotatedOpsToGateAux_cons_negate]
          simp [compileAnnotatedOpsToGateAux, updateLayoutState, qs.eval_seq, qs.eval_id]
      | some l =>
          rw [compileAnnotatedOpsToGateAux_cons_negate]
          simp [compileAnnotatedOpsToGateAux, updateLayoutState, qs.eval_seq, qs.eval_id]

  | addScaled dst src negsrc sh =>
      cases term? with
      | none =>
          rw [compileAnnotatedOpsToGateAux_cons_addScaled]
          simp [compileAnnotatedOpsToGateAux, updateLayoutState, qs.eval_seq, qs.eval_id]
      | some l =>
          rw [compileAnnotatedOpsToGateAux_cons_addScaled]
          simp [compileAnnotatedOpsToGateAux, updateLayoutState, qs.eval_seq, qs.eval_id]

  | phaseProduct i =>
      cases term? with
      | none =>
          rw [compileAnnotatedOpsToGateAux_cons_phaseProduct_none]
          simp [compileAnnotatedOpsToGateAux, updateLayoutState, qs.eval_seq, qs.eval_id]
      | some l =>
          rw [compileAnnotatedOpsToGateAux_cons_phaseProduct_some]
          simp [compileAnnotatedOpsToGateAux, updateLayoutState, qs.eval_seq, qs.eval_id]



lemma eval_compileAnnotatedOpsToGateAux_append
  (qs : QSemantics) [RegEncoding qs.Basis]
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ)
  (phaseCoeff : Fin (q k) → ℚ)
  (st : LayoutState k)
  (ops₁ ops₂ : List (AnnotatedOp k))
  (ψ : qs.State) :
  qs.eval (compileAnnotatedOpsToGateAux k hk phi phaseCoeff st (ops₁ ++ ops₂)) ψ
    =
  qs.eval
    ((compileAnnotatedOpsToGateAux k hk phi phaseCoeff st ops₁) ;;
     (compileAnnotatedOpsToGateAux k hk phi phaseCoeff
        (updateLayoutStateList st ops₁) ops₂))
    ψ := by
  induction ops₁ generalizing st ψ with
  | nil =>
      simp [compileAnnotatedOpsToGateAux_nil, updateLayoutStateList, qs.eval_seq, qs.eval_id]
  | cons a rest ih =>
    rw [List.cons_append]
    rw [eval_compileAnnotatedOpsToGateAux_cons]
    simp [updateLayoutStateList, qs.eval_seq]
    rw [ih (st := updateLayoutState st a.op)
           (ψ := qs.eval (compileAnnotatedOpsToGateAux k hk phi phaseCoeff st [a]) ψ)]
    simp [updateLayoutStateList, qs.eval_seq]
    have hcons :=
      (eval_compileAnnotatedOpsToGateAux_cons
        (qs := qs) (k := k) (hk := hk) (phi := phi)
        (phaseCoeff := phaseCoeff) (st := st)
        (a := a) (rest := rest) (ψ := ψ))
    rw [qs.eval_seq] at hcons
    aesop



/-- This is the version that matches the actual type of `pointEval` in your file. -/
lemma computeLocal2_zero_slot_spec
  {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs]
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ) (coeff : Fin (q k) → ℚ)
  (x z : Reg) (n : ℕ) (c : Int) (b : qs.Basis) :
  ∃ b' : qs.Basis,
    qs.eval
      (compileAnnotatedOpsToGateAux k hk phi coeff
        (initLayoutState x z k)
        (annotatePhaseTermsAux k n (computeLocal2 (k := k) (by omega) c)))
      (qs.ket b)
    =
    qs.ket b'
    ∧
    (RegEncoding.toNat
      ((updateLayoutStateList
          (initLayoutState x z k)
          (annotatePhaseTermsAux k n (computeLocal2 (k := k) (by omega) c))).xslot
        (finZero (by omega))) b' : ℝ)
      =
      pointEval x k (by omega) b (Point.int c)
    ∧
    (RegEncoding.toNat
      ((updateLayoutStateList
          (initLayoutState x z k)
          (annotatePhaseTermsAux k n (computeLocal2 (k := k) (by omega) c))).zslot
        (finZero (by omega))) b' : ℝ)
      =
      pointEval z k (by omega) b (Point.int c) := by
  sorry



-- lemma computeLocal2_zero_slot_spec
--   {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs]
--   (k : ℕ) (hk : 1 < k)
--   (phi : ℝ) (coeff : Fin (q k) → ℚ)
--   (x z : Reg) (n : ℕ) (c : Int) (b : qs.Basis) :
--   ∃ b' : qs.Basis,
--     qs.eval
--       (compileAnnotatedOpsToGateAux k hk phi coeff
--         (initLayoutState x z k)
--         (annotatePhaseTermsAux k n (computeLocal2 (k := k) (by omega) c)))
--       (qs.ket b)
--     =
--     qs.ket b'
--     ∧
--     RegEncoding.toNat
--       ((updateLayoutStateList
--           (initLayoutState x z k)
--           (annotatePhaseTermsAux k n (computeLocal2 (k := k) (by omega) c))).xslot
--         (finZero (by omega))) b'
--       =
--       pointEval x k (by omega) b (Point.int c)
--     ∧
--     RegEncoding.toNat
--       ((updateLayoutStateList
--           (initLayoutState x z k)
--           (annotatePhaseTermsAux k n (computeLocal2 (k := k) (by omega) c))).zslot
--         (finZero (by omega))) b'
--       =
--       pointEval z k (by omega) b (Point.int c) := by


--   sorry

lemma eval_apply_inverse_computeLocal2_ket
  (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs]
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ) (coeff : Fin (q k) → ℚ)
  (x z : Reg) (b : qs.Basis) (n : ℕ) (c : Int)
  (b' : qs.Basis)
  (hb' :
    qs.eval
      (compileAnnotatedOpsToGateAux k hk phi coeff
        (initLayoutState x z k)
        (annotatePhaseTermsAux k n (computeLocal2 (k := k) (by omega) c)))
      (qs.ket b)
    =
    qs.ket b') :
  qs.eval
    (compileAnnotatedOpsToGateAux k hk phi coeff
      (updateLayoutStateList (initLayoutState x z k)
        (annotatePhaseTermsAux k n (computeLocal2 (k := k) (by omega) c)))
      (annotatePhaseTermsAux k (n + 1)
        (apply_Op_inverse (computeLocal2 (k := k) (by omega) c))))
    (qs.ket b')
  =
  qs.ket b := by
  sorry

/-- Compiling one point block applies the exact phase for that point.
    Because we uncompute, the basis state `b` remains untouched. -/
lemma eval_compilePointBlock_ket
  (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs]
  (k : ℕ) (hk : 1 < k) (phi : ℝ) (coeff : Fin (q k) → ℚ)
  (x z : Reg) (b : qs.Basis) (n : ℕ) (pt : Point)
  (hn : n < q k) :
  qs.eval (compilePointBlock k hk phi coeff (initLayoutState x z k) n pt) (qs.ket b) =
  (Complex.exp (phi * Complex.I * (coeff ⟨n, hn⟩ : ℝ) *
    pointEval x k (by omega) b pt * pointEval z k (by omega) b pt)) • qs.ket b := by
    unfold compilePointBlock annotatedPointBlockFromList opsForPointWithProduct
    by_cases hpt: pt = Point.inf <;> simp[hpt]
    · unfold annotatePhaseTermsAux
      simp[hn,annotatePhaseTermsAux,compileAnnotatedOpsToGateAux]
      rw[qs.eval_id]
      rw[GateSemanticsFacts.eval_PhaseProd_ket]
      congr 2;simp[mul_assoc,mul_comm]
      simp[pointEval,initLayoutState]

    · cases pt with
      |inf=> simp at hpt
      |int c =>
        clear hpt
        simp
        simp[annotatePhaseTermsAux_append]
        simp[eval_compileAnnotatedOpsToGateAux_append]
        set st0 := initLayoutState x z k
        set annC := annotatePhaseTermsAux k n (computeLocal2 (k := k) (by omega) c)
        set st1 := updateLayoutStateList st0 annC
        rcases computeLocal2_zero_slot_spec
            (qs := qs) (k := k) (hk := hk) (phi := phi) (coeff := coeff)
            (x := x) (z := z) (n := n) (c := c) (b := b)
          with ⟨b', hb', hx', hz'⟩

        rw [hb']
        have hcons :
          annotatePhaseTermsAux k n
            (valid_ops.phaseProduct (finZero (by omega))
              :: apply_Op_inverse (computeLocal2 (k := k) (by omega) c))
          =
          ⟨valid_ops.phaseProduct (finZero (by omega)), some ⟨n, hn⟩⟩
            :: annotatePhaseTermsAux k (n+1)
                (apply_Op_inverse (computeLocal2 (k := k) (by omega) c)) := by
          simp [annotatePhaseTermsAux, hn]


        rw [hcons]
        simp [compileAnnotatedOpsToGateAux]

        rw [GateSemanticsFacts.eval_PhaseProd_ket]

        set s1:=↑(RegEncoding.toNat ((updateLayoutStateList (initLayoutState x z k) (annotatePhaseTermsAux k n (computeLocal2 (by omega) c))).xslot (finZero (by omega))) b')
        set s2:=↑(RegEncoding.toNat ((updateLayoutStateList (initLayoutState x z k) (annotatePhaseTermsAux k n (computeLocal2 (by omega) c))).zslot (finZero (by omega))) b')
        rw[← hx', ← hz']
        norm_cast
        simp[mul_assoc, mul_comm]
        rw[qs.eval_smul]
        congr
        have huncompute :=
          eval_apply_inverse_computeLocal2_ket
            (qs := qs) (k := k) (hk := hk)
            (phi := phi) (coeff := coeff)
            (x := x) (z := z) (b := b) (n := n) (c := c)
            (b' := b') hb'

        simpa [st0, annC, st1] using huncompute


/-- Full structural induction proving that the loop accumulates phases point-by-point. -/
lemma eval_compilePointsAux_accumulate
  (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs]
  (k : ℕ) (hk : 1 < k) (phi : ℝ) (coeff : Fin (q k) → ℚ)
  (x z : Reg) (b : qs.Basis)
  (pts_sub : List Point) :
  ∀ (n : ℕ) (h_bound : n + pts_sub.length ≤ q k),
  qs.eval (compilePointsAux k hk phi coeff (initLayoutState x z k) n pts_sub) (qs.ket b) =
  (Complex.exp (phi * Complex.I * ((∑ i : Fin pts_sub.length,
    (coeff ⟨n + i.val, by omega⟩ : ℝ) *
    pointEval x k (by omega) b (pts_sub.get i) *
    pointEval z k (by omega) b (pts_sub.get i)) : ℂ))) • qs.ket b := by
  induction pts_sub with
  | nil =>
    intro n h_bound
    unfold compilePointsAux
    rw [qs.eval_id]
    simp
  | cons pt pts ih =>
    intro n h_bound
    unfold compilePointsAux
    rw [qs.eval_seq]
    have hn : n < q k := by simp at h_bound; omega
    rw [eval_compilePointBlock_ket qs k hk phi coeff x z b n pt hn]

    rw [qs.eval_smul]

    have h_bound' : n + 1 + pts.length ≤ q k := by simp at h_bound;omega
    have := ih (n+1) h_bound'
    rw [ih (n + 1) h_bound']

    -- Combine the scalar multiplications (a • b • v = (a * b) • v)
    rw [smul_smul];rw [← Complex.exp_add];congr 1;congr 1
    simp only [List.length_cons]; rw [Fin.sum_univ_succ]

    rw [mul_add];simp only [Fin.val_zero, add_zero, Fin.val_succ,List.get_cons_zero]
    congr 1
    ring
    congr 1;apply Finset.sum_congr rfl
    intro i _;simp;left;left;congr 1
    simp
    linarith

lemma eval_compileGenOpsToGate_ket
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ)
  (x z : Reg)
  (pts : List Point)
  (hpts : List.length pts = q k)
  (b : qs.Basis) :
  let coeff : Fin (q k) → ℚ :=
    phaseCoeffFromPts k (ptsToFin k pts hpts) (phaseRadix x k)
  qs.eval
      (compileGenOpsToGate k hk phi x z coeff pts) (qs.ket b)
    =
  qs.eval (Gate.PhaseProd phi x z) (qs.ket b) := by
  intro coeff
  unfold compileGenOpsToGate

  have h_accum := eval_compilePointsAux_accumulate qs k hk phi coeff x z b pts 0 (by omega)
  rw [h_accum]

  rw [GateSemanticsFacts.eval_PhaseProd_ket]

  congr 1
  congr 1

  have h_sum_eq :
    (∑ i : Fin (List.length pts), (coeff ⟨0 + i.val, by omega⟩ : ℝ) * pointEval x k (by omega) b (pts.get i) * pointEval z k (by omega) b (pts.get i))
    =
    (∑ i : Fin (List.length pts), (coeff ⟨i.val, by rw [←hpts]; exact i.is_lt⟩ : ℝ) * pointEval x k (by omega) b (pts.get i) * pointEval z k (by omega) b (pts.get i)) := by
    apply Finset.sum_congr rfl
    simp
  have h_decomp := toom_cook_decomposition k hk x z b pts hpts coeff rfl

  norm_cast at *
  rw[h_sum_eq]
  rw [h_decomp]
  push_cast
  congr 1


lemma eval_compileGenOpsToGate
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ)
  (x z : Reg)
  (pts : List Point)
  (hpts : List.length pts = q k)
  (ψ : qs.State) :
  let coeff : Fin (q k) → ℚ :=
    phaseCoeffFromPts k (ptsToFin k pts hpts) (phaseRadix x k)
  qs.eval
      (compileGenOpsToGate k hk phi x z coeff pts) ψ
    =
  qs.eval (Gate.PhaseProd phi x z) ψ := by
  apply gate_eq_of_ket_eq (qs := qs)
  intro b
  apply eval_compileGenOpsToGate_ket

















/-! =========================================================
    Section 12: Compiler unfolding lemmas
========================================================= -/
variable (qs : QSemantics) [RegEncoding qs.Basis]























-- /-- Paper decomposition: φ x z = Σℓ φℓ (Ax)ℓ (Az)ℓ. -/
-- lemma phaseProd_decomposition
--   (k : ℕ) (hk : 1 < k)
--   (phi : ℝ) (x z : Reg)
--   (pts : List Point) (hpts : pts.length = q k)
--   (b : qs.Basis) :
--   phi * (RegEncoding.toNat x b : ℝ) * (RegEncoding.toNat z b : ℝ)
--     =
--   ∑ ℓ : Fin (q k),
--     phi
--       * (((phaseCoeffFromPts k (ptsToFin k pts hpts) (phaseRadix x k) ℓ : ℚ) : ℝ))
--       * (pointValue (qs := qs) k (ptsToFin k pts hpts ℓ) x b : ℝ)
--       * (pointValue (qs := qs) k (ptsToFin k pts hpts ℓ) z b : ℝ) := by
--   sorry

-- lemma eval_compile_opsForPointWithProduct_ket
--   (k : ℕ) (hk : 1 < k)
--   (phi : ℝ) (x z : Reg)
--   (pts : List Point) (hpts : pts.length = q k)
--   (l : Fin (q k))
--   (b : qs.Basis) :
--   let pt := ptsToFin k pts hpts l
--   qs.eval
--     (compileAnnotatedOpsToGateAux
--       k hk phi
--       (phaseCoeffFromPts k (ptsToFin k pts hpts) (phaseRadix x k))
--       (initLayoutState x z k)
--       (annotatePhaseTermsAux k l.1 (opsForPointWithProduct (by omega) pt)))
--     (qs.ket b)
--   =
--   (Complex.exp
--       (phi * Complex.I *
--         ((((phaseCoeffFromPts k (ptsToFin k pts hpts) (phaseRadix x k) l : ℚ) : ℝ) : ℂ)
--           * (pointValue (qs := qs) k pt x b : ℂ)
--           * (pointValue (qs := qs) k pt z b : ℂ)))) •
--     (qs.ket b) := by
--   sorry


variable [GateSemanticsFacts qs]


-- lemma eval_compileOpsToGate_genOpsWithProduct_as_sum_ket
--   (k : ℕ) (hk : 1 < k)
--   (phi : ℝ)
--   (x z : Reg)
--   (pts : List Point)
--   (hpts : pts.length = q k)
--   (b : qs.Basis) :
--   let coeff : Fin (q k) → ℚ :=
--     phaseCoeffFromPts k (ptsToFin k pts hpts) (phaseRadix x k)
--   let summand : Fin (q k) → ℝ :=
--     fun l =>
--       phi
--         * (((coeff l : ℚ) : ℝ))
--         * (pointValue (qs := qs) k (ptsToFin k pts hpts l) x b : ℝ)
--         * (pointValue (qs := qs) k (ptsToFin k pts hpts l) z b : ℝ)
--   qs.eval
--     (compileOpsToGate k hk phi x z coeff (genOpsWithProduct (by omega) pts))
--     (qs.ket b)
--     =
--   (Complex.exp (Complex.I * (((∑ l : Fin (q k), summand l) : ℝ) : ℂ))) •
--     (qs.ket b) := by
--   simp
--   unfold compileOpsToGate
--   simp
--   set etb:=(phaseCoeffFromPts k (ptsToFin k pts hpts) (phaseRadix x k))
--   set st:=(initLayoutState x z k)

--   sorry
#check pointValue

lemma compileOpsToGate_ofPts_eq_aux
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ) (x z : Reg)
  (pts : List Point)
  (hpts : pts.length = q k)
  (ops : List (valid_ops k)) :
  compileOpsToGate k hk phi x z (phaseCoeffOfPts k x pts hpts) ops
    =
  let annOps : List (AnnotatedOp k) :=
    annotatePhaseTermsAux k 0 ops
  compileAnnotatedOpsToGateAux
    k hk phi (phaseCoeffOfPts k x pts hpts) (initLayoutState x z k) annOps := by
  rfl


-- lemma eval_compileOpsToGate_genOpsWithProduct_ket
--   (k : ℕ) (hk : 1 < k)
--   (phi : ℝ)
--   (x z : Reg)
--   (pts : List Point)
--   (hpts : pts.length = q k)
--   (b : qs.Basis) :
--   let coeff : Fin (q k) → ℚ :=
--     phaseCoeffFromPts k (ptsToFin k pts hpts) (phaseRadix x k)
--   qs.eval
--       (compileOpsToGate k hk phi x z coeff (genOpsWithProduct (by omega) pts))
--       (qs.ket b)
--     =
--   qs.eval (Gate.PhaseProd phi x z) (qs.ket b) := by
--   let coeff : Fin (q k) → ℚ :=
--     phaseCoeffFromPts k (ptsToFin k pts hpts) (phaseRadix x k)

--   let summand : Fin (q k) → ℝ :=
--     fun ℓ =>
--       phi
--         * (((coeff ℓ : ℚ) : ℝ))
--         * (pointValue (qs := qs) k (ptsToFin k pts hpts ℓ) x b : ℝ)
--         * (pointValue (qs := qs) k (ptsToFin k pts hpts ℓ) z b : ℝ)

--   have hblocks :
--       qs.eval
--         (compileOpsToGate k hk phi x z coeff (genOpsWithProduct (by omega) pts))
--         (qs.ket b)
--       =
--       (Complex.exp (Complex.I * (((∑ ℓ : Fin (q k), summand ℓ) : ℝ) : ℂ))) •
--         (qs.ket b) := by
--     simpa [coeff, summand] using
--       (eval_compileOpsToGate_genOpsWithProduct_as_sum_ket
--         (qs := qs) k hk phi x z pts hpts b)

--   have hdecomp :
--       phi * (RegEncoding.toNat x b : ℝ) * (RegEncoding.toNat z b : ℝ)
--         =
--       ∑ ℓ : Fin (q k), summand ℓ := by
--     simpa [summand, coeff] using
--       phaseProd_decomposition (qs := qs) k hk phi x z pts hpts b

--   have hexp :
--       Complex.exp (Complex.I * (((∑ ℓ : Fin (q k), summand ℓ) : ℝ) : ℂ))
--         =
--       Complex.exp
--         (phi * Complex.I *
--           ((RegEncoding.toNat x b : ℂ) * (RegEncoding.toNat z b : ℂ))) := by
--     have hdecompC :
--         ((((∑ ℓ : Fin (q k), summand ℓ) : ℝ) : ℂ))
--           =
--         ((phi * (RegEncoding.toNat x b : ℝ) * (RegEncoding.toNat z b : ℝ) : ℝ) : ℂ) := by
--       exact congrArg (fun t : ℝ => (t : ℂ)) hdecomp.symm
--     rw [hdecompC]
--     congr 1
--     norm_num
--     ring
--   unfold coeff at *
--   simp
--   rw [hblocks, GateSemanticsFacts.eval_PhaseProd_ket]
--   rw [hexp]


/-! =========================================================
    Induction over the point list
========================================================= -/


-- /-- Full-state compiler correctness for the generated op list. -/
-- lemma eval_compileOpsToGate_genOpsWithProduct
--   (k : ℕ) (hk : 1 < k)
--   (phi : ℝ)
--   (x z : Reg)
--   (pts : List Point)
--   (hpts : List.length pts = q k)
--   (ψ : qs.State) :
--   let coeff : Fin (q k) → ℚ :=
--     phaseCoeffFromPts k (ptsToFin k pts hpts) (phaseRadix x k)
--   qs.eval
--       (compileOpsToGate k hk phi x z coeff (genOpsWithProduct (by omega) pts)) ψ
--     =
--   qs.eval (Gate.PhaseProd phi x z) ψ := by
--   apply gate_eq_of_ket_eq (qs := qs)
--   intro b
--   simpa using
--     (eval_compileOpsToGate_genOpsWithProduct_ket
--       (qs := qs) k hk phi x z pts hpts b)
