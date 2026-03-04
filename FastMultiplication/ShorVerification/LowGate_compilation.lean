import FastMultiplication.ShorVerification.Basic
import Mathlib.Data.Finset.Basic

namespace Shor
open Gate

/-! ## Core QFT phase definitions -/

/-- A 1-qubit register at index `q`. -/
def qubitReg (q : ℕ) : Reg := ⟨q, q + 1⟩

/-- Standard QFT phase schedule. -/
noncomputable def qftPhi (m : ℕ) : ℝ := (2 * Real.pi) / (2^m)

/-- `ω N = exp(2π i / N)` (a primitive `N`-th root of unity, when `N ≠ 0`). -/
noncomputable def ω (N : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))

/-- `ωPow N k = (ω N)^k`. -/
noncomputable def ωPow (N k : ℕ) : ℂ :=
  (ω N) ^ k

/-- QFT phase `ω_N^(x*y)` for natural `x,y`. -/
noncomputable def qftPhase (N x y : ℕ) : ℂ :=
  ωPow N (x * y)

/-! ## Fin reindexing equivalence (product ↔ single Fin) -/

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
              simp [Nat.mul_add,  Nat.add_comm]
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
          simp[Nat.mod_eq_of_lt hi_lt]

        · apply Fin.ext
          have hi_lt : (i.1) < (A + 1) := i.2
          have hi_div : (i.1 / (A + 1)) = 0 := by
            exact Nat.div_eq_of_lt hi_lt
          calc
            (i.1 + (A + 1) * j.1) / (A + 1)
                = j.1 + (i.1 / (A + 1)) := by
                    simpa [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
                      using (Nat.add_mul_div_right i.1 j.1 (Nat.succ_pos A))
            _   = j.1 := by simp[hi_div]

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
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using (Nat.mod_add_div (n.1) (A + 1))

/-! ## Low-level gate language and lowering skeleton -/

inductive LowGate : Type
  | id : LowGate
  | seq : LowGate → LowGate → LowGate
  | adj : LowGate → LowGate
  | H : ℕ → LowGate
  | X : ℕ → LowGate
  | Prim : String → List ℕ → LowGate
deriving Inhabited

namespace LowGate
infixr:80 " ;; " => LowGate.seq
prefix:90 "†" => LowGate.adj
end LowGate

opaque lowerPhaseProd  : (phi : ℝ) → (x z : Reg) → LowGate
opaque lowerCPhaseProd : (ctrl : ℕ) → (phi : ℝ) → (x z : Reg) → LowGate

noncomputable def lowerQFTAux : ℕ → Reg → LowGate
  | 0,   _ => .id
  | 1,   r => .H r.lo
  | n+2, r =>
      let nTot : ℕ := n + 2
      let m : ℕ := nTot / 2
      let left  : Reg := ⟨r.lo, r.lo + m⟩
      let right : Reg := ⟨r.lo + m, r.hi⟩
      (lowerQFTAux m left) ;;
      (lowerPhaseProd (qftPhi nTot) left right) ;;
      (lowerQFTAux (nTot - m) right)

noncomputable def lowerQFT (r : Reg) : LowGate :=
  lowerQFTAux (regSize r) r

noncomputable def lowerGate : Gate → LowGate
  | .id => .id
  | .seq U V => (lowerGate U) ;; (lowerGate V)
  | .adj U => †(lowerGate U)
  | .H q => .H q
  | .X q => .X q
  | .QFT r => lowerQFT r
  | .PhaseProd p x z => lowerPhaseProd p x z
  | .CPhaseProd c p x z => lowerCPhaseProd c p x z
  | .Prim tag args => .Prim tag args

namespace LowGate
@[simp] lemma lowerGate_id : lowerGate Gate.id = (LowGate.id) := rfl
@[simp] lemma lowerGate_seq (U V : Gate) :
    lowerGate (U ;; V) = (lowerGate U) ;; (lowerGate V) := by
  simp [lowerGate]
@[simp] lemma lowerGate_adj (U : Gate) :
    lowerGate (†U) = †(lowerGate U) := rfl
@[simp] lemma lowerGate_QFT (r : Reg) :
    lowerGate (Gate.QFT r) = lowerQFT r := rfl
@[simp] lemma lowerGate_PP (p : ℝ) (x z : Reg) :
    lowerGate (Gate.PhaseProd p x z) = lowerPhaseProd p x z := rfl
@[simp] lemma lowerGate_CPP (c : ℕ) (p : ℝ) (x z : Reg) :
    lowerGate (Gate.CPhaseProd c p x z) = lowerCPhaseProd c p x z := rfl
end LowGate

@[simp] lemma regSize_rest (r : Reg) :
    regSize (⟨r.lo + 1, r.hi⟩ : Reg) = regSize r - 1 := by
  simp [regSize, Nat.sub_sub]

/-! ## LowerGate semantics interface -/

class LowerGateClass (qs : QSemantics) [RegEncoding qs.Basis]: Type where
  evalL : LowGate → qs.State → qs.State
  evalL_id  : ∀ ψ, evalL LowGate.id ψ = ψ
  evalL_seq : ∀ (U V : LowGate) (ψ : qs.State),
      evalL (U ;; V) ψ = evalL V (evalL U ψ)

  evalL_H :
    ∀ (q : ℕ) (ψ : qs.State),
      evalL (.H q) ψ = qs.eval (.H q) ψ

  evalL_X :
    ∀ (q : ℕ) (ψ : qs.State),
      evalL (.X q) ψ = qs.eval (.X q) ψ

  evalL_Prim :
    ∀ (tag : String) (args : List ℕ) (ψ : qs.State),
      evalL (.Prim tag args) ψ = qs.eval (Gate.Prim tag args) ψ

  evalL_lowerPhaseProd :
    ∀ (p : ℝ) (x z : Reg) (ψ : qs.State),
      evalL (lowerPhaseProd p x z) ψ = qs.eval (Gate.PhaseProd p x z) ψ

  evalL_lowerCPhaseProd :
    ∀ (c : ℕ) (p : ℝ) (x z : Reg) (ψ : qs.State),
      evalL (lowerCPhaseProd c p x z) ψ = qs.eval (Gate.CPhaseProd c p x z) ψ

  evalL_adj_of_lowered :
    ∀ (U : Gate) (ψ : qs.State),
      evalL (†(lowerGate U)) ψ = qs.eval (†U) ψ

  eval_QFT_size0 :
    ∀ (r : Reg) (ψ : qs.State),
      regSize r = 0 → qs.eval (Gate.QFT r) ψ = qs.eval Gate.id ψ

  eval_QFT_size1 :
    ∀ (r : Reg) (ψ : qs.State),
      regSize r = 1 → qs.eval (Gate.QFT r) ψ = qs.eval (Gate.H r.lo) ψ

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

attribute [simp] LowerGateClass.evalL_id
attribute [simp] LowerGateClass.evalL_seq

/-! ## Register arithmetic and split helpers -/

@[simp] lemma regSize_mk (a m : ℕ) :
    regSize (⟨a, a + m⟩ : Reg) = m := by
  simp [regSize]

@[simp] lemma regSize_right_of_split (r : Reg) (m : ℕ) :
    regSize (⟨r.lo + m, r.hi⟩ : Reg) = regSize r - m := by
  simp [regSize, Nat.sub_sub]

variable (qs : QSemantics) [RegEncoding qs.Basis] [LowerGateClass qs]

def nTot (r : Reg) : ℕ := regSize r
def mHalf (r : Reg) : ℕ := (nTot r) / 2

lemma qft_norm_split (nTot m : ℕ) (hm : m ≤ nTot) :
    ((1 / Real.sqrt ((2^nTot : ℕ) : ℝ) : ℂ))
      =
    ((1 / Real.sqrt ((2^m : ℕ) : ℝ) : ℂ))
      * ((1 / Real.sqrt ((2^(nTot - m) : ℕ) : ℝ) : ℂ)) := by
  have hpow_nat : (2^nTot : ℕ) = (2^m : ℕ) * (2^(nTot - m) : ℕ) := by
    have hn : nTot = m + (nTot - m) := by
      simpa using (Nat.add_sub_of_le hm).symm
    calc
      (2^nTot : ℕ) = 2^(m + (nTot - m)) := by rw[← hn]
      _ = (2^m : ℕ) * (2^(nTot - m) : ℕ) := by
            simp [Nat.pow_add]

  have hpow_real :
      ((2^nTot : ℕ) : ℝ) = ((2^m : ℕ) : ℝ) * ((2^(nTot - m) : ℕ) : ℝ) := by
    exact_mod_cast hpow_nat

  have hsqrt :
      Real.sqrt ((2^nTot : ℕ) : ℝ)
        =
      Real.sqrt ((2^m : ℕ) : ℝ) * Real.sqrt ((2^(nTot - m) : ℕ) : ℝ) := by
    have ha : 0 ≤ ((2^m : ℕ) : ℝ) := by positivity
    have hb : 0 ≤ ((2^(nTot - m) : ℕ) : ℝ) := by positivity
    calc
      Real.sqrt ((2^nTot : ℕ) : ℝ)
          = Real.sqrt ( ((2^m : ℕ) : ℝ) * ((2^(nTot - m) : ℕ) : ℝ) ) := by
              simp [hpow_real]
      _   = Real.sqrt ((2^m : ℕ) : ℝ) * Real.sqrt ((2^(nTot - m) : ℕ) : ℝ) := by
              simp

  have : ((1 / Real.sqrt ((2^nTot : ℕ) : ℝ) : ℝ) : ℂ)
        =
        ((1 / Real.sqrt ((2^m : ℕ) : ℝ) : ℝ) : ℂ)
          * ((1 / Real.sqrt ((2^(nTot - m) : ℕ) : ℝ) : ℝ) : ℂ) := by
    simp [div_eq_mul_inv]
    norm_cast
    rw [hsqrt]
    simp[mul_comm]
  simpa using this

def ASize (r : Reg) : ℕ := 2^(regSize r)

def splitM (r : Reg) : ℕ := (regSize r) / 2
def leftReg  (r : Reg) : Reg := ⟨r.lo, r.lo + splitM r⟩
def rightReg (r : Reg) : Reg := ⟨r.lo + splitM r, r.hi⟩

def j0 (r : Reg) (b : qs.Basis) : ℕ := RegEncoding.toNat (leftReg r) b
def j1 (r : Reg) (b : qs.Basis) : ℕ := RegEncoding.toNat (rightReg r) b

lemma step1_QFT_left_ket
  (r : Reg) (b : qs.Basis) :
  let left : Reg := leftReg r
  let A    : ℕ  := ASize left
  qs.eval (Gate.QFT left) (qs.ket b)
    =
  ((1 / Real.sqrt ((A : ℕ) : ℝ) : ℂ)) •
    ∑ k1 : Fin A,
      (qftPhase A (RegEncoding.toNat left b) k1.1) •
        qs.ket (RegEncoding.writeNat left k1.1 b) := by
  simpa [ASize, leftReg] using (LowerGateClass.eval_QFT_ket (qs := qs) (r := leftReg r) (b := b))

lemma disjoint_left_right (r : Reg) :
  Disjoint (leftReg r) (rightReg r) := by
  left
  simp [leftReg, rightReg]


/-! ## Encoding-only lemmas (no LowerGateClass needed) -/

section EncodingOnly
variable (qs : QSemantics) [RegEncoding qs.Basis]

lemma toNat_right_after_write_left
  (r : Reg) (b : qs.Basis) (yL : ℕ) :
  RegEncoding.toNat (rightReg r) (RegEncoding.writeNat (leftReg r) yL b)
    =
  RegEncoding.toNat (rightReg r) b := by
  simpa [leftReg, rightReg] using
    (RegEncoding.toNat_right_write_left
      (Basis := qs.Basis)
      (left := leftReg r) (right := rightReg r)
      (_h := disjoint_left_right r)
      (b := b) (yL := yL))
end EncodingOnly

/-! ## Exponential / qftPhase bridge lemmas -/

lemma exp_phaseProd_eq_qftPhase (N x y : ℕ) :
    Complex.exp
        (2 * (Real.pi : ℂ) / (N : ℂ) * Complex.I * ((x : ℂ) * (y : ℂ)))
      =
    qftPhase N x y := by
  simp [qftPhase, ωPow, ω, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma exp_phaseProd_eq_qftPhase_of_casts
  (A B : ℕ) (k1 jR : ℕ) :
    Complex.exp
      (2 * (Real.pi : ℂ) / ((A : ℂ) * (B : ℂ)) * Complex.I * ((k1 : ℂ) * (jR : ℂ)))
    =
    qftPhase (A * B) k1 jR := by
  simpa [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using
    (exp_phaseProd_eq_qftPhase (N := A * B) (x := k1) (y := jR))

/-! ## Sum pushing lemmas -/

lemma eval_sum_univ_qs
  (qs : QSemantics)
  (U : Gate)
  {α : Type} [Fintype α]
  (f : α → qs.State) :
  qs.eval U (∑ a : α, f a) = ∑ a : α, qs.eval U (f a) := by
  classical
  simpa using (by
    refine Finset.induction_on (s := (Finset.univ : Finset α)) ?h0 ?hs
    · simp [qs.eval_zero]
    · intro a s ha hs
      simp [Finset.sum_insert ha, qs.eval_add, hs])

/-! ## toNat/writeNat helper lemmas for split registers -/

lemma Complex.exp_mul_eq_pow (z : ℂ) (n : ℕ) :
    Complex.exp ((n : ℂ) * z) = (Complex.exp z) ^ n := by
  simpa [mul_comm] using (Complex.exp_nat_mul z n)

lemma toNat_mul_after_write_left_eq
  (qs : QSemantics) [RegEncoding qs.Basis] (r : Reg) (b : qs.Basis)
  (k1 : Fin (ASize (leftReg r))) :
  ((RegEncoding.toNat (leftReg r) (RegEncoding.writeNat (leftReg r) k1.1 b) : ℕ) : ℂ)
    *
    ((RegEncoding.toNat (rightReg r) (RegEncoding.writeNat (leftReg r) k1.1 b) : ℕ) : ℂ)
  =
  ((RegEncoding.toNat (rightReg r) b : ℕ) : ℂ) * (k1.1 : ℂ) := by
  classical
  have hL :
      RegEncoding.toNat (leftReg r)
          (RegEncoding.writeNat (leftReg r) k1.1 b) = k1.1 := by
    simpa using (RegEncoding.toNat_writeNat (r := (leftReg r)) (v := k1.1) (b := b))

  have hdisj : Disjoint (leftReg r) (rightReg r) := disjoint_left_right (r := r)
  have hR :
      RegEncoding.toNat (rightReg r)
          (RegEncoding.writeNat (leftReg r) k1.1 b)
        =
      RegEncoding.toNat (rightReg r) b := by
    simpa using
      (RegEncoding.toNat_right_write_left (Basis := qs.Basis)
        (left := leftReg r) (right := rightReg r)
        (_h := hdisj) (b := b) (yL := k1.1))

  simp [hL, hR, mul_comm]

/-! ## Step 2 and Step 3 of the split QFT proof -/

lemma step2_PhaseProd_after_step1
  (r : Reg) (b : qs.Basis) :
  let left  : Reg := leftReg r
  let right : Reg := rightReg r
  let A     : ℕ  := ASize left
  let B     : ℕ  := ASize right
  qs.eval (Gate.PhaseProd ((2 * Real.pi) / (A*B : ℝ)) left right) (qs.eval (Gate.QFT left) (qs.ket b))
    =
  ((1 / Real.sqrt ((A : ℕ) : ℝ) : ℂ)) •
    ∑ k1 : Fin A,
      ((qftPhase A (RegEncoding.toNat left b) k1.1)
        *
        (qftPhase (A*B) (k1.1) (RegEncoding.toNat right b)))
        • qs.ket (RegEncoding.writeNat left k1.1 b) := by
  classical
  set left  : Reg := leftReg r
  set right : Reg := rightReg r
  set A : ℕ := ASize left
  set B : ℕ := ASize right

  have hQFTleft :
      qs.eval (Gate.QFT left) (qs.ket b)
        =
      ((1 / Real.sqrt ((A : ℕ) : ℝ) : ℂ)) •
        ∑ k1 : Fin A,
          (qftPhase A (RegEncoding.toNat left b) k1.1) •
            qs.ket (RegEncoding.writeNat left k1.1 b) := by
    simpa [ASize, A, left] using
      (LowerGateClass.eval_QFT_ket (qs := qs) (r := left) (b := b))

  have phase_scalar_eq (k1 : Fin A) :
      (Complex.exp (((2 * Real.pi) / (A * B : ℝ)) * Complex.I *
          ((RegEncoding.toNat left (RegEncoding.writeNat left k1.1 b) : ℂ) *
            (RegEncoding.toNat right (RegEncoding.writeNat left k1.1 b) : ℂ))))
        =
      qftPhase (A*B) k1.1 (RegEncoding.toNat right b) := by
    have hL : RegEncoding.toNat left (RegEncoding.writeNat left k1.1 b) = k1.1 := by
      simpa using (RegEncoding.toNat_writeNat left k1.1 b)

    have hR : RegEncoding.toNat right (RegEncoding.writeNat left k1.1 b) = RegEncoding.toNat right b := by
      have hdisj : Disjoint left right := by
        simpa [left, right] using (disjoint_left_right (r := r))
      simpa using
        (RegEncoding.toNat_right_write_left (Basis := qs.Basis)
          (left := left) (right := right) (_h := hdisj) (b := b) (yL := k1.1))
    simp[exp_phaseProd_eq_qftPhase_of_casts]
    aesop
  classical
  calc
    QSemantics.eval (PhaseProd (2 * Real.pi / (↑A * ↑B)) left right)
        (QSemantics.eval (QFT left) (QSemantics.ket b))
        =
      QSemantics.eval (PhaseProd (2 * Real.pi / (↑A * ↑B)) left right)
        ((1 / (Real.sqrt ((A : ℕ) : ℝ)) : ℂ) •
          ∑ k1 : Fin A,
            (qftPhase A (RegEncoding.toNat left b) k1.1) •
              QSemantics.ket (RegEncoding.writeNat left k1.1 b)) := by
        simp [hQFTleft]
    _ =
      ((1 / (Real.sqrt ((A : ℕ) : ℝ)) : ℂ)) •
        QSemantics.eval (PhaseProd (2 * Real.pi / (↑A * ↑B)) left right)
          (∑ k1 : Fin A,
            (qftPhase A (RegEncoding.toNat left b) k1.1) •
              QSemantics.ket (RegEncoding.writeNat left k1.1 b)) := by
        simp [QSemantics.eval_smul]
    _ =
      ((1 / (Real.sqrt ((A : ℕ) : ℝ)) : ℂ)) •
        ∑ k1 : Fin A,
          QSemantics.eval (PhaseProd (2 * Real.pi / (↑A * ↑B)) left right)
            ((qftPhase A (RegEncoding.toNat left b) k1.1) •
              QSemantics.ket (RegEncoding.writeNat left k1.1 b)) := by
              simp[eval_sum_univ_qs]
    _ =
      ((1 / (Real.sqrt ((A : ℕ) : ℝ)) : ℂ)) •
        ∑ k1 : Fin A,
          (qftPhase A (RegEncoding.toNat left b) k1.1) •
            QSemantics.eval (PhaseProd (2 * Real.pi / (↑A * ↑B)) left right)
              (QSemantics.ket (RegEncoding.writeNat left k1.1 b)) := by
        simp [QSemantics.eval_smul]
    _ =
      ((1 / (Real.sqrt ((A : ℕ) : ℝ)) : ℂ)) •
        ∑ k1 : Fin A,
          (qftPhase A (RegEncoding.toNat left b) k1.1) •
            (Complex.exp ((2 * Real.pi / (↑A * ↑B)) * Complex.I *
                ((RegEncoding.toNat left (RegEncoding.writeNat left k1.1 b) : ℂ) *
                  (RegEncoding.toNat right (RegEncoding.writeNat left k1.1 b) : ℂ))))
              • QSemantics.ket (RegEncoding.writeNat left k1.1 b) := by
        simp [LowerGateClass.eval_PhaseProd_ket]
    _ =
      ((1 / (Real.sqrt ((A : ℕ) : ℝ)) : ℂ)) •
        ∑ k1 : Fin A,
          ((qftPhase A (RegEncoding.toNat left b) k1.1)
            *
            (qftPhase (A * B) k1.1 (RegEncoding.toNat right b)))
            • QSemantics.ket (RegEncoding.writeNat left k1.1 b) := by
        refine congrArg (fun t => ((1 / (Real.sqrt ((A : ℕ) : ℝ)) : ℂ) • t)) ?_
        refine Finset.sum_congr rfl ?_
        intro k1 hk1
        have h := phase_scalar_eq k1
        simp [smul_smul]
        congr 2
        simp [qftPhase,ωPow,ω,mul_assoc]
        set n : ℕ := (↑k1) * RegEncoding.toNat right b
        set z : ℂ := (2 * (↑Real.pi * Complex.I) / (↑A * ↑B))
        have hLHS :
              Complex.exp
                (2 * ↑Real.pi / (↑A * ↑B) *
                  (Complex.I *
                    (↑(RegEncoding.toNat left (RegEncoding.writeNat left (↑k1) b)) *
                      ↑(RegEncoding.toNat right (RegEncoding.writeNat left (↑k1) b)))))
                =
              Complex.exp ((n : ℂ) * z) := by
            simp [n, z, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv, Nat.cast_mul]
            congr 3
            conv=>
              rhs
              rw[mul_comm]
            simp[mul_assoc]
            left
            left
            have := toNat_mul_after_write_left_eq (qs := qs) (r := r) (b := b)
            have hL : RegEncoding.toNat left (RegEncoding.writeNat left (↑k1) b) = (↑k1) := by
              simpa using (RegEncoding.toNat_writeNat (r := left) (v := (↑k1)) (b := b))
            have hdisj : Disjoint left right := by
              simpa [left, right] using (disjoint_left_right (r := r))
            have hR : RegEncoding.toNat right (RegEncoding.writeNat left (↑k1) b) = RegEncoding.toNat right b := by
              simpa using
                (RegEncoding.toNat_right_write_left (Basis := qs.Basis)
                  (left := left) (right := right) (_h := hdisj) (b := b) (yL := (↑k1)))
            simp [hL, hR, mul_comm]
        simpa [hLHS, n, z] using (Complex.exp_mul_eq_pow z n)

lemma step3_QFT_right_after_step2
  (r : Reg) (b : qs.Basis) :
  let left  : Reg := leftReg r
  let right : Reg := rightReg r
  let A     : ℕ  := ASize left
  let B     : ℕ  := ASize right
  qs.eval (Gate.QFT right)
    (qs.eval (Gate.PhaseProd ((2 * Real.pi) / (A*B : ℝ)) left right) (qs.eval (Gate.QFT left) (qs.ket b)))
    =
  (((1 / Real.sqrt ((A : ℕ) : ℝ) : ℂ)) * ((1 / Real.sqrt ((B : ℕ) : ℝ) : ℂ))) •
    ∑ k1 : Fin A,
      ∑ k0 : Fin B,
        ((qftPhase A (RegEncoding.toNat left b) k1.1)
          *
          (qftPhase (A*B) (k1.1) (RegEncoding.toNat right b))
          *
          (qftPhase B (RegEncoding.toNat right b) k0.1))
          • qs.ket (RegEncoding.writeNat right k0.1 (RegEncoding.writeNat left k1.1 b)) := by
  classical
  set left  : Reg := leftReg r
  set right : Reg := rightReg r
  set A : ℕ := ASize left
  set B : ℕ := ASize right

  have eval_sum_univ_qs {α : Type} [Fintype α] (U : Gate) (f : α → qs.State) :
      qs.eval U (∑ a : α, f a) = ∑ a : α, qs.eval U (f a) := by
    classical
    simpa using (by
      refine Finset.induction_on (s := (Finset.univ : Finset α)) ?h0 ?hs
      · simp [qs.eval_zero]
      · intro a s ha hs
        simp [Finset.sum_insert ha, qs.eval_add, hs])

  have hstep2 :
      qs.eval (Gate.PhaseProd ((2 * Real.pi) / (A*B : ℝ)) left right)
          (qs.eval (Gate.QFT left) (qs.ket b))
        =
      ((1 / Real.sqrt ((A : ℕ) : ℝ) : ℂ)) •
        ∑ k1 : Fin A,
          ((qftPhase A (RegEncoding.toNat left b) k1.1)
            *
            (qftPhase (A*B) (k1.1) (RegEncoding.toNat right b)))
            • qs.ket (RegEncoding.writeNat left k1.1 b) := by
    simpa [left, right, A, B] using (step2_PhaseProd_after_step1 (qs := qs) (r := r) (b := b))

  calc
    qs.eval (Gate.QFT right)
        (qs.eval (Gate.PhaseProd ((2 * Real.pi) / (A*B : ℝ)) left right)
          (qs.eval (Gate.QFT left) (qs.ket b)))
        =
      qs.eval (Gate.QFT right)
        ( ((1 / Real.sqrt ((A : ℕ) : ℝ) : ℂ)) •
            ∑ k1 : Fin A,
              ((qftPhase A (RegEncoding.toNat left b) k1.1)
                *
                (qftPhase (A*B) (k1.1) (RegEncoding.toNat right b)))
                • qs.ket (RegEncoding.writeNat left k1.1 b) ) := by
          simp[hstep2]
    _ =
      ((1 / Real.sqrt ((A : ℕ) : ℝ) : ℂ)) •
        qs.eval (Gate.QFT right)
          (∑ k1 : Fin A,
            ((qftPhase A (RegEncoding.toNat left b) k1.1)
              *
              (qftPhase (A*B) (k1.1) (RegEncoding.toNat right b)))
              • qs.ket (RegEncoding.writeNat left k1.1 b)) := by
          simp [qs.eval_smul]
    _ =
      ((1 / Real.sqrt ((A : ℕ) : ℝ) : ℂ)) •
        ∑ k1 : Fin A,
          qs.eval (Gate.QFT right)
            ( ((qftPhase A (RegEncoding.toNat left b) k1.1)
                *
                (qftPhase (A*B) (k1.1) (RegEncoding.toNat right b)))
              • qs.ket (RegEncoding.writeNat left k1.1 b)) := by
          simp [eval_sum_univ_qs]
    _ =
      ((1 / Real.sqrt ((A : ℕ) : ℝ) : ℂ)) •
        ∑ k1 : Fin A,
          ((qftPhase A (RegEncoding.toNat left b) k1.1)
              *
            (qftPhase (A*B) (k1.1) (RegEncoding.toNat right b))) •
          (qs.eval (Gate.QFT right) (qs.ket (RegEncoding.writeNat left k1.1 b))) := by
          simp [qs.eval_smul, mul_smul]
    _ =
      ((1 / Real.sqrt ((A : ℕ) : ℝ) : ℂ)) •
        ∑ k1 : Fin A,
          ((qftPhase A (RegEncoding.toNat left b) k1.1)
              *
            (qftPhase (A*B) (k1.1) (RegEncoding.toNat right b))) •
          ( ((1 / Real.sqrt ((B : ℕ) : ℝ) : ℂ)) •
              ∑ k0 : Fin B,
                (qftPhase B (RegEncoding.toNat right (RegEncoding.writeNat left k1.1 b)) k0.1) •
                  qs.ket (RegEncoding.writeNat right k0.1 (RegEncoding.writeNat left k1.1 b)) ) := by
          congr 2; funext x; congr 1
          simpa [ASize, B] using
            (LowerGateClass.eval_QFT_ket (qs := qs) (r := right)
              (b := RegEncoding.writeNat left (↑x) b))
    _ =
      (((1 / Real.sqrt ((A : ℕ) : ℝ) : ℂ)) * ((1 / Real.sqrt ((B : ℕ) : ℝ) : ℂ))) •
        ∑ k1 : Fin A,
          ∑ k0 : Fin B,
            ((qftPhase A (RegEncoding.toNat left b) k1.1)
              *
             (qftPhase (A*B) (k1.1) (RegEncoding.toNat right b))
              *
             (qftPhase B (RegEncoding.toNat right b) k0.1))
              • qs.ket (RegEncoding.writeNat right k0.1 (RegEncoding.writeNat left k1.1 b)) := by
          simp [Finset.smul_sum,  mul_left_comm, mul_comm,
                toNat_right_after_write_left (qs := qs) (r := r) (b := b),
                left, right, A, B]
          congr; funext x; congr; funext y; simp[mul_smul]; congr 1;
          simp [smul_smul, mul_assoc, mul_left_comm, mul_comm]

/-! ## Phase-combination lemma for reindexing -/

lemma exp_helper_lemma(A B : ℕ) (hA : 0 < A) (hB : 0 < B) :
    Complex.exp ((A : ℂ) * ((B : ℂ) * (Complex.I * ((Real.pi : ℂ) * 2) / ((A : ℂ) * (B : ℂ))))) = 1 := by
  have hA0 : (A : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hA)
  have hB0 : (B : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hB)
  have hexp :
      (A : ℂ) * ((B : ℂ) * (Complex.I * ((Real.pi : ℂ) * 2) / ((A : ℂ) * (B : ℂ))))
        =
      2 * (Real.pi : ℂ) * Complex.I := by
    field_simp [hA0, hB0, mul_assoc, mul_left_comm, mul_comm]
  simpa [hexp, mul_assoc, mul_left_comm, mul_comm] using (Complex.exp_two_pi_mul_I)

lemma step4_phase_combine
  (A B j0 j1 k1 k0 : ℕ)
  (hA : 0 < A) (hB : 0 < B) :
  (qftPhase A j0 k1)
    * (qftPhase (A*B) k1 j1)
    * (qftPhase B j1 k0)
  =
  qftPhase (A*B) (j0*B + j1) (k1 + A*k0) := by
  classical
  set N : ℕ := A * B

  have hωA : ω A = (ω N) ^ B := by
    have hN : (N : ℂ) ≠ 0 := by
      have : N ≠ 0 := by
        exact Nat.ne_of_gt (Nat.mul_pos hA hB)
      exact_mod_cast this
    unfold ω
    have : (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))) ^ B
            =
           Complex.exp ((B : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))) := by
      simpa [mul_comm] using (Complex.exp_nat_mul
        (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) B).symm
    rw [this]
    have : ((B : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)))
            =
           (2 * (Real.pi : ℂ) * Complex.I / (A : ℂ)) := by
      field_simp [N, hN, mul_assoc, mul_left_comm, mul_comm]
      have hA0 : (A : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hA)
      apply (eq_div_iff hA0).2
      simp [N, Nat.cast_mul, mul_comm]
    congr
    simp[N, mul_comm]
    have hA0 : (A : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hA)
    have hB0 : (B : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hB)
    field_simp [hA0, hB0, mul_assoc, mul_left_comm, mul_comm]

  have hωB : ω B = (ω N) ^ A := by
    have hN : (N : ℂ) ≠ 0 := by
      have : N ≠ 0 := by
        exact Nat.ne_of_gt (Nat.mul_pos hA hB)
      exact_mod_cast this
    unfold ω
    have : (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))) ^ A
            =
           Complex.exp ((A : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))) := by
      simpa [mul_comm] using (Complex.exp_nat_mul
        (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) A).symm
    rw [this]
    have : ((A : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)))
            =
           (2 * (Real.pi : ℂ) * Complex.I / (B : ℂ)) := by
      field_simp [N, hN, mul_assoc, mul_left_comm, mul_comm]
      have hA0 : (B : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hB)
      apply (eq_div_iff hA0).2
      simp [N, Nat.cast_mul]
    simp[N, mul_comm]
    have hA0 : (A : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hA)
    have hB0 : (B : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hB)
    field_simp [hA0, hB0, mul_assoc, mul_left_comm, mul_comm]

  have hωN_mul_self (t : ℕ) : (ω N) ^ (N * t) = 1 := by
    have hNpos : 0 < N := Nat.mul_pos hA hB
    have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hNpos)
    have hpowN : (ω N) ^ N = 1 := by
      unfold ω
      have : (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))) ^ N
              =
             Complex.exp ((N : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))) := by
        simpa [mul_comm] using (Complex.exp_nat_mul
          (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) N).symm
      rw [this]
      have : ((N : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)))
              =
             (2 * (Real.pi : ℂ) * Complex.I) := by
        field_simp [hN0, mul_assoc, mul_left_comm, mul_comm]
      have:= (Complex.exp_two_pi_mul_I)
      simp[N,mul_assoc,  mul_comm]
      simp[exp_helper_lemma A B hA hB]
    simp[pow_mul, hpowN]

  unfold qftPhase ωPow
  have hLHS :
      ( (ω A) ^ (j0 * k1) ) * ( (ω N) ^ (k1 * j1) ) * ( (ω B) ^ (j1 * k0) )
        =
      (ω N) ^ (B * (j0 * k1) + (k1 * j1) + A * (j1 * k0)) := by
    simp [hωA, hωB, pow_mul, pow_add, mul_assoc, mul_left_comm, mul_comm, Nat.add_assoc]

  have hRHS_exp :
      (ω N) ^ ((j0*B + j1) * (k1 + A*k0))
        =
      (ω N) ^ (B * (j0 * k1) + (k1 * j1) + A * (j1 * k0)) := by
    have : (j0*B + j1) * (k1 + A*k0)
            =
           (B * (j0 * k1) + (k1 * j1) + A * (j1 * k0)) + N * (j0 * k0) := by
      calc
        (j0*B + j1) * (k1 + A*k0)
            = (j0*B)*k1 + (j0*B)*(A*k0) + j1*k1 + j1*(A*k0) := by
                ring
        _ = (B*(j0*k1) + (k1*j1) + A*(j1*k0)) + (A*B)*(j0*k0) := by
                ring
        _ = (B*(j0*k1) + (k1*j1) + A*(j1*k0)) + N*(j0*k0) := by
                simp [N, Nat.mul_left_comm, Nat.mul_comm]
    rw [this]
    simp [pow_add,  N,  Nat.mul_left_comm, Nat.mul_comm,
          Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    left
    have hpow : ω (A * B) ^ (A * (B * (j0 * k0))) = 1 := by
      have hexp :
          A * (B * (j0 * k0)) = (A * B) * (j0 * k0) := by
        simp [ Nat.mul_left_comm, Nat.mul_comm]
      have:=(hωN_mul_self (t := j0 * k0))
      simp[N,mul_assoc] at *
      apply this
    simp [hpow]

  calc
    (qftPhase A j0 k1) * (qftPhase (A*B) k1 j1) * (qftPhase B j1 k0)
        =
      (ω N) ^ (B * (j0 * k1) + (k1 * j1) + A * (j1 * k0)) := by
        simpa [N] using hLHS
    _ =
      (ω N) ^ ((j0*B + j1) * (k1 + A*k0)) := by
        symm
        simpa [N] using hRHS_exp
    _ =
      qftPhase (A*B) (j0*B + j1) (k1 + A*k0) := by
        simp [qftPhase, ωPow, N]

/-! ## Reindexing sums and cast utilities -/

lemma step5_reindex_sum
  {α : Type} [AddCommMonoid α]
  (NR NL : ℕ)
  (f : Fin (NR * NL) → α) :
  (∑ p : Fin NR × Fin NL, f ((finMulAddEquiv NR NL) p))
    =
  ∑ k : Fin (NR * NL), f k := by
  classical
  exact (finMulAddEquiv NR NL).sum_comp f

lemma Asize_eq_lr (hm:m≤regSize r):
  let left  : Reg := ⟨r.lo, r.lo + m⟩
  let right : Reg := ⟨r.lo + m, r.hi⟩
  ASize left * ASize right = ASize r :=by
  simp[ASize]
  rw[← pow_add]
  congr
  rw[← Nat.add_sub_assoc]
  rw[add_comm]
  rw[Nat.add_sub_cancel]
  simp[hm]

open scoped BigOperators

lemma qft_summand_rewrite
  (qs : QSemantics) [RegEncoding qs.Basis]
  (r left right : Reg) (b : qs.Basis)
  (A : ℕ)
  (e : (Fin A × Fin (2^(regSize right))) ≃ Fin (2^(regSize r)))
  (h_toNat : RegEncoding.toNat r b
      = RegEncoding.toNat left b * (2^(regSize right)) + RegEncoding.toNat right b)
  (h_write : ∀ k1 k0 : ℕ,
      RegEncoding.writeNat r (k1 + A*k0) b
        = RegEncoding.writeNat right k0 (RegEncoding.writeNat left k1 b))
  (h_idx : ∀ x : Fin (2^(regSize r)),
      x.1 = (e.symm x).1.1 + A * (e.symm x).2.1)
  :
  (fun y : Fin (2^(regSize r)) =>
      qftPhase (2^(regSize r)) (RegEncoding.toNat r b) y.1 •
        qs.ket (RegEncoding.writeNat r y.1 b))
  =
  (fun x : Fin (2^(regSize r)) =>
      qftPhase (2^(regSize r))
        (RegEncoding.toNat left b * (2^(regSize right)) + RegEncoding.toNat right b)
        ((e.symm x).1.1 + A * (e.symm x).2.1) •
      qs.ket (RegEncoding.writeNat right (e.symm x).2.1
        (RegEncoding.writeNat left (e.symm x).1.1 b))) := by
  funext x
  simp [h_toNat, h_idx, h_write]

lemma cast_arrow_apply
  {α β : Sort _} {γ : Sort _}
  (h : α = β) (f : α → γ) (x : β) :
  (cast (congrArg (fun T => T → γ) h) f) x = f (cast h.symm x) := by
  cases h
  rfl

lemma cast_app
  {α β γ : Sort _}
  (h : α = β) (f : α → γ) (x : β) :
  (cast (congrArg (fun T => T → γ) h) f) x = f (cast h.symm x) := by
  cases h
  rfl

lemma fin_cast_eq_symm_formula
  {A B N : ℕ}
  (hFin : Fin (A * B) = Fin N)
  (y : Fin N) :
  let e := finMulAddEquiv A B
  ((cast hFin.symm y : Fin (A * B)) : ℕ)
    =
  (e.symm (cast hFin.symm y)).1.1 + A * (e.symm (cast hFin.symm y)).2.1 := by
  classical
  set y' : Fin (A * B) := cast hFin.symm y
  simp
  have h :=
    congrArg (fun t : Fin (A * B) => (t : ℕ))
      ((finMulAddEquiv A B).apply_symm_apply y')
  simpa [y', finMulAddEquiv] using h.symm

lemma fin_cast_eq_finMulAdd_formula
  (A B N : ℕ)
  (hFin : Fin (A * B) = Fin N)
  (y : Fin N) :
  ((cast hFin.symm y : Fin (A * B)) : ℕ)
    =
  ((finMulAddEquiv A B).symm (cast hFin.symm y)).1.1
    + A * ((finMulAddEquiv A B).symm (cast hFin.symm y)).2.1 := by
  classical
  set y' : Fin (A * B) := cast hFin.symm y
  cases A with
  | zero =>
      simp at y'
      nomatch y'
  | succ A =>
      have hA : 0 < Nat.succ A := Nat.succ_pos _
      simp [y', finMulAddEquiv, hA, Nat.mod_add_div]

lemma Fin.coe_cast_typeEq
  {n m : ℕ} (h : Fin n = Fin m) (y : Fin n) :
  ((cast h y : Fin m) : ℕ) = (y : ℕ) := by
  have h_nat : n = m := by
    have hc : Fintype.card (Fin n) = Fintype.card (Fin m) :=
      Fintype.card_congr (Equiv.cast h)
    simpa using hc
  subst h_nat
  rfl

/-! ## QFT split on basis kets and general states -/

lemma eval_QFT_split_ket
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [LowerGateClass qs]
  :
  ∀ (r : Reg) (b : qs.Basis),
    regSize r ≥ 2 →
    let nTot  : ℕ := regSize r
    let m     : ℕ := nTot / 2
    let left  : Reg := ⟨r.lo, r.lo + m⟩
    let right : Reg := ⟨r.lo + m, r.hi⟩
    let phi :ℝ := (2 * Real.pi / (↑(ASize left) * ↑(ASize right)))
    qs.eval (Gate.QFT r) (qs.ket b)
      =
    qs.eval ((Gate.QFT left) ;;
             (Gate.PhaseProd (phi) left right) ;;
             (Gate.QFT right)) (qs.ket b) := by
  intro r b hr
  simp
  have:=step3_QFT_right_after_step2 qs r b
  set nTot  : ℕ := regSize r
  set m     : ℕ := nTot / 2
  set left  : Reg := ⟨r.lo, r.lo + m⟩
  set right : Reg := ⟨r.lo + m, r.hi⟩
  set phi :ℝ := (2 * Real.pi / (↑(ASize left) * ↑(ASize right)))
  simp_all
  have hr: rightReg r = right:= by simp[rightReg,right,m,splitM,nTot]
  have hl: leftReg r = left:= by simp[leftReg,left,m,splitM,nTot]
  rw[hr,hl] at this
  rw[this]
  have:=step4_phase_combine (A:=(ASize left)) (B:=(ASize right)) (j0:=(RegEncoding.toNat left b)) (hA:=by simp[ASize]) (hB:= by simp[ASize])
  simp_rw [this (j1 := RegEncoding.toNat right b)]
  classical
  set A : ℕ := ASize left
  set B : ℕ := ASize right
  set F : Fin A → Fin B → qs.State := fun x x1 =>
    (qftPhase (A*B)
        (RegEncoding.toNat left b * B + RegEncoding.toNat right b)
        (x.1 + A * x1.1)) •
      qs.ket (RegEncoding.writeNat right x1.1 (RegEncoding.writeNat left x.1 b))

  have hF :
    (∑ x : Fin A, ∑ x_1 : Fin B,
        qftPhase (A * B) (RegEncoding.toNat left b * B + RegEncoding.toNat right b) (↑x + A * ↑x_1) •
          qs.ket (RegEncoding.writeNat right (↑x_1) (RegEncoding.writeNat left (↑x) b)))
      =
    ∑ x : Fin A, ∑ x_1 : Fin B, F x x_1 := by
    simp [F]

  rw [hF]
  have h_prod :
    (∑ x : Fin A, ∑ x_1 : Fin B, F x x_1)
      =
    ∑ p : (Fin A × Fin B), F p.1 p.2 := by
      change
          (Finset.univ.sum (fun x : Fin A =>
            Finset.univ.sum (fun x_1 : Fin B => F x x_1)))
        =
          (Finset.univ.sum (fun p : Fin A × Fin B => F p.1 p.2))
      rw [Fintype.sum_prod_type]
  rw [h_prod]

  let e := finMulAddEquiv A B
  have h_reindex :
    (∑ p : Fin A × Fin B, F p.1 p.2)
      =
    ∑ y : Fin (A*B), F ( (e.symm y).1 ) ( (e.symm y).2 ) := by
    have:=(Equiv.sum_comp e (fun y => F ((e.symm y).1) ((e.symm y).2))).symm
    aesop
  rw [h_reindex]
  simp[F]
  norm_cast
  rw[← mul_inv, ← Real.sqrt_mul]
  unfold A B
  norm_cast
  have:ASize left * ASize right = ASize r :=by
    simp[ASize]
    rw[← pow_add]
    congr
    simp[left,right]
    rw[← Nat.add_sub_assoc]
    rw[add_comm]
    rw[Nat.add_sub_cancel]
    simp[m,nTot];omega

  conv=>
    rhs;arg 1;arg 1;arg 1;arg 1
    rw[this]

  rw[LowerGateClass.eval_QFT_ket]
  simp[ASize]
  norm_cast
  congr 1
  congr<;>unfold ASize at this<;> try simp[this]
  apply heq_of_eq_cast (by simp[this])
  ext y
  revert this
  intro h_eq
  have hFin : Fin (A * B) = Fin (2 ^ regSize r) := by
    exact congrArg Fin (by
      simpa [A, B, ASize] using h_eq)

  have hx :
      cast (of_eq_true
  (Eq.trans
    (congrFun' (congrArg Eq (implies_congr (congrArg Fin h_eq) (Eq.refl QSemantics.State)))
      (Fin (2 ^ regSize r) → QSemantics.State))
    (eq_self (Fin (2 ^ regSize r) → QSemantics.State))) : (Fin (2 ^ regSize left * 2 ^ regSize right) → QSemantics.State) = (Fin (2 ^ regSize r) → QSemantics.State))
        (fun x =>
          qftPhase (2 ^ regSize r)
            (RegEncoding.toNat left b * 2 ^ regSize right + RegEncoding.toNat right b)
            ((e.symm x).1.1 + 2 ^ regSize left * (e.symm x).2.1) •
          QSemantics.ket
            (RegEncoding.writeNat right (e.symm x).2.1
              (RegEncoding.writeNat left (e.symm x).1.1 b)))
        y
      =
      (fun x =>
          qftPhase (2 ^ regSize r)
            (RegEncoding.toNat left b * 2 ^ regSize right + RegEncoding.toNat right b)
            ((e.symm x).1.1 + 2 ^ regSize left * (e.symm x).2.1) •
          QSemantics.ket
            (RegEncoding.writeNat right (e.symm x).2.1
              (RegEncoding.writeNat left (e.symm x).1.1 b)))
        (cast hFin.symm y) := by
    simpa using (cast_arrow_apply (γ := QSemantics.State) (h := hFin)
      (f := (fun x =>
        qftPhase (2 ^ regSize r)
          (RegEncoding.toNat left b * 2 ^ regSize right + RegEncoding.toNat right b)
          ((e.symm x).1.1 + 2 ^ regSize left * (e.symm x).2.1) •
        QSemantics.ket
          (RegEncoding.writeNat right (e.symm x).2.1
            (RegEncoding.writeNat left (e.symm x).1.1 b))))
      (x := y))
  set func:=(fun x ↦
      qftPhase (2 ^ regSize r) (RegEncoding.toNat left b * 2 ^ regSize right + RegEncoding.toNat right b)
          (↑(e.symm x).1 + 2 ^ regSize left * ↑(e.symm x).2) •
        QSemantics.ket (RegEncoding.writeNat right (↑(e.symm x).2) (RegEncoding.writeNat left (↑(e.symm x).1) b)))
  set func2:=(fun (x:Fin (2 ^ regSize left * 2 ^ regSize right)) ↦
      qftPhase (2 ^ regSize r) (RegEncoding.toNat left b * 2 ^ regSize right + RegEncoding.toNat right b)
          (↑(e.symm x).1 + 2 ^ regSize left * ↑(e.symm x).2) •
        QSemantics.ket (RegEncoding.writeNat right (↑(e.symm x).2) (RegEncoding.writeNat left (↑(e.symm x).1) b)))
  rw [cast_app (γ := qs.State)]
  set y' : Fin (A * B) := cast hFin.symm y

  have hy_idx :
      (y' : ℕ) = (e.symm y').1.1 + A * (e.symm y').2.1 := by
    simpa [y'] using fin_cast_eq_symm_formula (hFin := rfl) (y := y')
  have hy_idx' :
    (↑(e.symm y').1 + 2 ^ regSize left * ↑(e.symm y').2) = (y' : ℕ) := by
    simpa using hy_idx.symm
  unfold A ASize at hy_idx
  have hy : (y : ℕ) = (y' : ℕ) := by
    simp [y']
    have : ((cast (Eq.symm hFin) y : Fin (A * B)) : ℕ) = (y : ℕ) := by
      simpa using (Fin.coe_cast_typeEq (h := Eq.symm hFin) (y := y))
    exact this.symm
  simp[hy]
  rw[hy_idx]
  clear hy_idx hy_idx'
  set k1 : ℕ := (e.symm y').1.1
  set k0 : ℕ := (e.symm y').2.1
  set K  : ℕ := k1 + (2 ^ regSize left) * k0

  have h_toNat :
      RegEncoding.toNat r b
        =
      RegEncoding.toNat left b * (2 ^ regSize right) + RegEncoding.toNat right b := by
    simpa [left, right] using (RegEncoding.toNat_split (r := r) (left := left) (right := right) (b := b))

  have h_write :
      RegEncoding.writeNat r K b
        =
      RegEncoding.writeNat right k0 (RegEncoding.writeNat left k1 b) := by
    simpa [K, k0, k1] using
      (RegEncoding.writeNat_split (r := r) (left := left) (right := right) (b := b)
        (k1 := k1) (k0 := k0))
  have hK : (↑((e.symm y')).1 + 2 ^ regSize left * ↑(e.symm y').2) = K := by
    simp [K, k0, k1]
  simp [A, B, ASize] at *
  simp_rw [hK]
  rw[h_toNat,h_write]
  congr
  have:(2 ^ regSize left * 2 ^ regSize right)=(2 ^ regSize r):=by
    rw[← pow_add];simp[regSize, right, left]
    rw[← Nat.sub_sub]
    rw[Nat.add_sub_cancel']
    simp[m,nTot,regSize]
    omega
  simp[this]
  simp[A]

theorem eval_QFT_split
  (qs : QSemantics) [RegEncoding qs.Basis] [LowerGateClass qs] :
    ∀ (r : Reg) (ψ : qs.State),
      regSize r ≥ 2 →
      let nTot  : ℕ := regSize r
      let m     : ℕ := nTot / 2
      let left  : Reg := ⟨r.lo, r.lo + m⟩
      let right : Reg := ⟨r.lo + m, r.hi⟩
      qs.eval (Gate.QFT r) ψ
        =
      qs.eval ((Gate.QFT left) ;;
               (Gate.PhaseProd (qftPhi nTot) left right) ;;
               (Gate.QFT right)) ψ := by
  intro r ψ hsz
  classical

  let nTot : ℕ := regSize r
  let m    : ℕ := nTot / 2
  let left : Reg := ⟨r.lo, r.lo + m⟩
  let right: Reg := ⟨r.lo + m, r.hi⟩

  let P : qs.State → Prop :=
    fun ψ =>
      qs.eval (Gate.QFT r) ψ =
      qs.eval ((Gate.QFT left) ;;
               (Gate.PhaseProd (qftPhi nTot) left right) ;;
               (Gate.QFT right)) ψ

  have hP : ∀ ψ, P ψ := by
    refine qs.state_induction (P := P) ?h0 ?hadd ?hsmul ?hket
    ·
      simp [P, qs.eval_zero]
    ·
      intro ψ φ hψ hφ
      simp [P, qs.eval_add, hψ, hφ]
    ·
      intro a ψ hψ
      simp [P, qs.eval_smul, hψ]
    ·
      intro b
      have hk :=
        (eval_QFT_split_ket (qs := qs) (r := r) (b := b) hsz)

      unfold P
      rw[hk]
      congr 1
      unfold left right m nTot
      congr 1;congr 1;congr 1
      unfold qftPhi
      clear hk
      norm_cast
      simp[ASize]
      rw[← pow_add]
      congr
      rw[← Nat.add_sub_assoc]
      rw[add_comm]
      rw[Nat.add_sub_cancel]
      omega

  have := hP ψ
  simpa [P] using this

/-! ## Correctness of lowered QFT (aux, main) -/

lemma eval_lowerQFTAux_strong
  (qs : QSemantics) (RE : RegEncoding qs.Basis) [LowerGateClass qs] :
  ∀ n : ℕ, ∀ (r : Reg) (ψ : qs.State),
    regSize r = n →
    (LowerGateClass.evalL (qs := qs) (lowerQFTAux n r) ψ) = qs.eval (Gate.QFT r) ψ := by
  classical
  letI : RegEncoding qs.Basis := RE

  let P : ℕ → Prop :=
    fun n =>
      ∀ (r : Reg) (ψ : qs.State),
        regSize r = n →
        (LowerGateClass.evalL (qs := qs) (lowerQFTAux n r) ψ) = qs.eval (Gate.QFT r) ψ
  intro n
  change P n

  induction n using Nat.strong_induction_on with
  | _ n IH =>
      intro r ψ hsz
      cases n with
      | zero =>
          simp [lowerQFTAux]
          have h0 := LowerGateClass.eval_QFT_size0 (qs := qs) (r := r) (ψ := ψ) hsz
          simpa [qs.eval_id] using h0.symm
      | succ n1 =>
          cases n1 with
          | zero =>
              simp [lowerQFTAux]
              have h1 := LowerGateClass.eval_QFT_size1 (qs := qs) (r := r) (ψ := ψ) hsz
              simpa [LowerGateClass.evalL_H] using h1.symm
          | succ n2 =>
              let nTot : ℕ := n2 + 2
              have hnTot : nTot = Nat.succ (Nat.succ n2) := rfl

              let m : ℕ := nTot / 2
              let left  : Reg := ⟨r.lo, r.lo + m⟩
              let right : Reg := ⟨r.lo + m, r.hi⟩

              have hleft : regSize left = m := by simp [left, regSize]
              have hright : regSize right = nTot - m := by
                simp [right, regSize]
                simp at hsz; unfold nTot; rw[← hsz]
                simp[regSize]
                omega

              have hm_lt : m < nTot := by
                have hnpos : 0 < nTot := by exact Nat.succ_pos _
                simpa [m] using (Nat.div_lt_self hnpos (by decide : 1 < 2))

              have hm_pos : 0 < m := by
                have : 1 ≤ nTot / 2 := by
                  have : 2 ≤ nTot := by simp [nTot]
                  exact Nat.succ_le_iff.mp (by
                    have : 0 < nTot / 2 := Nat.div_pos this (by decide : 0 < 2)
                    exact Nat.succ_le_iff.mp this)
                exact lt_of_lt_of_le (Nat.zero_lt_one) this

              have hnm_lt : nTot - m < nTot := by
                exact Nat.sub_lt (by omega) hm_pos

              have hsz' : regSize r = nTot := by simpa [nTot] using hsz

              have ihL :
                  LowerGateClass.evalL (qs := qs) (lowerQFTAux m left) ψ
                    = qs.eval (Gate.QFT left) ψ := by
                have := IH m (by omega)
                simpa [P] using this left ψ hleft

              have ihR :
                  ∀ χ : qs.State,
                    LowerGateClass.evalL (qs := qs) (lowerQFTAux (nTot - m) right) χ
                      = qs.eval (Gate.QFT right) χ := by
                intro χ
                have := IH (nTot - m) (by omega)
                simpa [P] using this right χ hright
              have hSplit :
                  QSemantics.eval (QFT r) ψ
                    =
                  QSemantics.eval
                    ((QFT left) ;; (PhaseProd (qftPhi nTot) left right) ;; (QFT right)) ψ := by
                have hge : regSize r ≥ 2 := by
                  have : (2 : ℕ) ≤ nTot := by simp [nTot]
                  simpa [hsz'] using this
                have:=(eval_QFT_split (qs := qs) (r := r) (ψ := ψ) hge)
                rw[this]
                simp_all[left,right,m]
              have hSplit' :
                  QSemantics.eval (QFT left ;; PhaseProd (qftPhi nTot) left right ;; QFT right) ψ
                    =
                  QSemantics.eval (QFT r) ψ := by
                simpa using hSplit.symm

              calc
                LowerGateClass.evalL (qs := qs) (lowerQFTAux (n2 + 1 + 1) r) ψ
                    =
                  LowerGateClass.evalL (qs := qs)
                    ((lowerQFTAux m left) ;;
                    (lowerPhaseProd (qftPhi nTot) left right) ;;
                    (lowerQFTAux (nTot - m) right)) ψ := by
                      simp [lowerQFTAux, nTot, m, left, right]
                _ =
                  LowerGateClass.evalL (qs := qs) (lowerQFTAux (nTot - m) right)
                    (LowerGateClass.evalL (qs := qs) (lowerPhaseProd (qftPhi nTot) left right)
                      (LowerGateClass.evalL (qs := qs) (lowerQFTAux m left) ψ)) := by
                      simp [LowerGateClass.evalL_seq]
                _ =
                  QSemantics.eval (QFT right)
                    (QSemantics.eval (PhaseProd (qftPhi nTot) left right)
                      (QSemantics.eval (QFT left) ψ)) := by
                      simp [ihL, ihR, LowerGateClass.evalL_lowerPhaseProd]
                _ =
                  QSemantics.eval (QFT left ;; PhaseProd (qftPhi nTot) left right ;; QFT right) ψ := by
                      simp
                _ =
                  QSemantics.eval (QFT r) ψ := by
                      exact hSplit'

lemma eval_lowerQFT
  (qs : QSemantics) (RE:RegEncoding qs.Basis) [LowerGateClass qs] :
  ∀ (r : Reg) (ψ : qs.State),
    (LowerGateClass.evalL (qs := qs) (lowerQFT r) ψ) = qs.eval (Gate.QFT r) ψ := by
  intro r ψ
  have main :
    ∀ (n : ℕ) (r : Reg) (ψ : qs.State),
      regSize r = n →
      (LowerGateClass.evalL (qs := qs) (lowerQFTAux n r) ψ) = qs.eval (Gate.QFT r) ψ := by
    intro n
    induction n with
    | zero =>
        intro r ψ hsz
        have hQ := LowerGateClass.eval_QFT_size0 (qs := qs) r ψ hsz
        simpa [lowerQFTAux, QSemantics.eval_id] using hQ.symm
    | succ n ih =>
        cases n with
        | zero =>
            intro r ψ hsz
            have hQ := LowerGateClass.eval_QFT_size1 (qs := qs) r ψ hsz
            simpa [lowerQFTAux, LowerGateClass.evalL_H (qs := qs)] using hQ.symm
        | succ n =>
            intro r ψ hsz
            simpa using (eval_lowerQFTAux_strong (qs := qs) (RE := RE) (n + 2) r ψ hsz)

  simpa [lowerQFT] using main (regSize r) r ψ rfl

/-! ## Whole-program lowering correctness -/

theorem lowerGate_correctness (G : Gate) (qs : QSemantics) (RE:RegEncoding qs.Basis) [LowerGateClass qs] :
  ∀ ψ, (LowerGateClass.evalL (qs := qs) (lowerGate G) ψ) = qs.eval G ψ := by
  intro ψ
  induction G generalizing ψ with
  | id =>
      simp [lowerGate, QSemantics.eval_id]
  | H q =>
      simp [lowerGate, LowerGateClass.evalL_H (qs := qs)]
  | X q =>
      simp [lowerGate, LowerGateClass.evalL_X (qs := qs) q]
  | PhaseProd p x z =>
      simpa [lowerGate] using (LowerGateClass.evalL_lowerPhaseProd (qs := qs) p x z ψ)
  | CPhaseProd c p x z =>
      simpa [lowerGate] using (LowerGateClass.evalL_lowerCPhaseProd (qs := qs) c p x z ψ)
  | QFT r =>
      simpa [lowerGate] using (eval_lowerQFT (qs := qs) RE r ψ)
  | seq U V ihU ihV =>
      calc
        LowerGateClass.evalL (qs := qs) (lowerGate (U ;; V)) ψ
            =
        LowerGateClass.evalL (qs := qs) (lowerGate V)
          (LowerGateClass.evalL (qs := qs) (lowerGate U) ψ) := by
              simp [lowerGate, LowerGateClass.evalL_seq (qs := qs)]
        _ =
        LowerGateClass.evalL (qs := qs) (lowerGate V) (qs.eval U ψ) := by
              simpa using congrArg
                (fun t => LowerGateClass.evalL (qs := qs) (lowerGate V) t) (ihU ψ)
        _ =
        qs.eval V (qs.eval U ψ) := by
              simpa using (ihV (qs.eval U ψ))
        _ =
        qs.eval (U ;; V) ψ := by
              simp
  | adj U ih =>
      simpa [lowerGate] using (LowerGateClass.evalL_adj_of_lowered (qs := qs) U ψ)
  | Prim tag args =>
      simp[lowerGate, LowerGateClass.evalL_Prim (qs := qs) tag args ψ]

end Shor
