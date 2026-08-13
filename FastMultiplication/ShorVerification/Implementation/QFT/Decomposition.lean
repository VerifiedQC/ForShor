import FastMultiplication.ShorVerification.Framework.Semantics.GateSemantics
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.GateConstructions
import FastMultiplication.ShorVerification.Implementation.GateSemanticsLemmas
import FastMultiplication.ShorVerification.Implementation.CleanClosure
namespace Shor
open Gate

universe u


/-!
# QFT Decomposition

This file proves the high-level circuit identity that splits QFT into recursive
QFTs, a phase product, and radix reversal.  Low-level lowering correctness is
proved separately in `AbstractMachine/QFTLoweringCorrectness/PlanSemantics.lean`.

The organization :

1. Register-split helpers and normalization facts.
2. QFT phase and sum-manipulation lemmas.
3. Stepwise split-QFT derivation.
4. Reindexing and radix-reversal lemmas.
5. Exact QFT split on basis states and arbitrary states.
-/


/-! =========================================================
    Section 1: Register arithmetic and split helpers
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

variable (qs : QSemantics)
  [RegEncoding qs.Basis]

  [GateSemanticsFacts qs]

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


def splitM (r : Reg) : ℕ := (regSize r) / 2
def halfSplitPoint (r : Reg) : SplitPoint r :=
  ⟨splitM r, by
    simpa [splitM] using Nat.div_le_self (regSize r) 2⟩

def leftReg  (r : Reg) : Reg := splitLeft r (halfSplitPoint r)
def rightReg (r : Reg) : Reg := splitRight r (halfSplitPoint r)

lemma leftReg_mem_parent
    (r : Reg)
    {q : ℕ}
    (hq : q ∈ (leftReg r).qubits) :
    q ∈ r.qubits := by
  simpa [
    leftReg,
    halfSplitPoint,
    splitM,
    splitLeft,
    Reg.take
  ] using List.mem_of_mem_take hq

lemma rightReg_mem_parent
    (r : Reg)
    {q : ℕ}
    (hq : q ∈ (rightReg r).qubits) :
    q ∈ r.qubits := by
  simpa [
    rightReg,
    halfSplitPoint,
    splitM,
    splitRight,
    Reg.drop
  ] using List.mem_of_mem_drop hq

/--
The left recursive QFT acts on the left half of the active register and
temporarily owns the same reserve as its parent.

The two recursive QFTs are sequential, so they may reuse this reserve.  Each
lowered QFT is required to restore it before returning.
-/
def leftQFTReg (r : ExtReg) : ExtReg :=
  {
    active := leftReg r.active
    reserve := r.reserve
    active_reserve_disjoint := by
      rw [Disjoint, List.disjoint_left]
      intro q hqLeft hqReserve

      have hqActive :
          q ∈ r.active.qubits :=
        leftReg_mem_parent r.active hqLeft

      have hdisjoint :=
        r.active_reserve_disjoint

      rw [Disjoint, List.disjoint_left] at hdisjoint
      exact hdisjoint hqActive hqReserve
  }

/--
The right recursive QFT acts on the right half of the active register and
temporarily owns the same reserve as its parent.
-/
def rightQFTReg (r : ExtReg) : ExtReg :=
  {
    active := rightReg r.active
    reserve := r.reserve
    active_reserve_disjoint := by
      rw [Disjoint, List.disjoint_left]
      intro q hqRight hqReserve

      have hqActive :
          q ∈ r.active.qubits :=
        rightReg_mem_parent r.active hqRight

      have hdisjoint :=
        r.active_reserve_disjoint

      rw [Disjoint, List.disjoint_left] at hdisjoint
      exact hdisjoint hqActive hqReserve
  }

@[simp] lemma leftQFTReg_active
    (r : ExtReg) :
    (leftQFTReg r).active = leftReg r.active := by
  rfl

@[simp] lemma rightQFTReg_active
    (r : ExtReg) :
    (rightQFTReg r).active = rightReg r.active := by
  rfl

@[simp] lemma leftQFTReg_reserve
    (r : ExtReg) :
    (leftQFTReg r).reserve = r.reserve := by
  rfl

@[simp] lemma rightQFTReg_reserve
    (r : ExtReg) :
    (rightQFTReg r).reserve = r.reserve := by
  rfl

@[simp] lemma leftQFTReg_width
    (r : ExtReg) :
    (leftQFTReg r).width =
      regSize (leftReg r.active) := by
  rfl

@[simp] lemma rightQFTReg_width
    (r : ExtReg) :
    (rightQFTReg r).width =
      regSize (rightReg r.active) := by
  rfl

namespace Gate.PhaseProdWorkspace

/--
The linear subspace in which both physical workspace qubits of an unsigned
phase-product macro are clean.
-/
abbrev CleanState
    (qs : QSemantics) [RegEncoding qs.Basis] {x z : Reg} (ws : Gate.PhaseProdWorkspace x z) : qs.State → Prop :=
  CleanClosure (fun b => ws.Clean b)

omit  [GateSemanticsFacts qs] in
/--
Writing the right input register does not change either workspace qubit.
-/
lemma Clean.writeRight
    {x z : Reg}
    (ws : Gate.PhaseProdWorkspace x z)
    (b : qs.Basis)
    (value : ℕ)
    (hclean : ws.Clean b) :
    ws.Clean (RegEncoding.writeNat z value b) := by
  constructor
  · apply FreshZero.of_eq_on_bits
      (r := ws.xExt.newBits 1)
      (b₁ := b)
      (b₂ := RegEncoding.writeNat z value b)
    · intro q hq
      rw [RegEncoding.bit_writeNat_out]
      have hqReserve : q ∈ ws.xReserve.qubits := by
        exact List.mem_of_mem_take hq
      exact ws.xReserve_not_z hqReserve
    · exact hclean.1
  · apply FreshZero.of_eq_on_bits
      (r := ws.zExt.newBits 1)
      (b₁ := b)
      (b₂ := RegEncoding.writeNat z value b)
    · intro q hq
      rw [RegEncoding.bit_writeNat_out]
      have hqReserve : q ∈ ws.zReserve.qubits := by
        exact List.mem_of_mem_take hq
      exact (Disjoint.symm ws.z_reserve_disjoint) hqReserve
    · exact hclean.2

end Gate.PhaseProdWorkspace

theorem eval_QFT_eq_of_active_eq
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (x y : ExtReg)
    (hactive : x.active = y.active)
    (ψ : qs.State) :
    qs.eval (Gate.QFT x) ψ =
      qs.eval (Gate.QFT y) ψ := by
  refine
    qs.state_induction
      (P := fun ψ =>
        qs.eval (Gate.QFT x) ψ =
          qs.eval (Gate.QFT y) ψ)
      ?_ ?_ ?_ ?_ ψ

  · simp [qs.eval_zero]

  · intro ψ₁ ψ₂ hψ₁ hψ₂
    simp [qs.eval_add, hψ₁, hψ₂]

  · intro a ψ hψ
    simp [qs.eval_smul, hψ]

  · intro b
    cases x with
    | mk xActive xReserve xDisjoint =>
      cases y with
      | mk yActive yReserve yDisjoint =>
        dsimp at hactive
        cases hactive
        simp [QFTSemantics.eval_QFT_ket, ExtReg.width, ExtReg.toNat]

def j0 (r : Reg) (b : qs.Basis) : ℕ := RegEncoding.toNat (leftReg r) b
def j1 (r : Reg) (b : qs.Basis) : ℕ := RegEncoding.toNat (rightReg r) b

lemma step1_QFT_right_ket
  (r : Reg) (b : qs.Basis) :
  let right : Reg := rightReg r
  let B   : ℕ  := ASize right
  qs.eval (Gate.QFT (ExtReg.ofReg right)) (qs.ket b)
    =
  ((1 / Real.sqrt (B : ℝ) : ℂ)) •
    ∑ kH : Fin B,
      qftPhase B (RegEncoding.toNat right b) kH.1 •
        qs.ket (RegEncoding.writeNat right kH.1 b) := by
  simpa [ASize, leftReg, rightReg, ExtReg.ofReg, ExtReg.width, ExtReg.toNat, regSize] using
    (QFTSemantics.eval_QFT_ket (qs := qs) (r := ExtReg.ofReg (rightReg r)) (b := b))

lemma disjoint_left_right (r : Reg) :
  Disjoint (leftReg r) (rightReg r) := by
  simpa [leftReg, rightReg] using
    (splitLeft_splitRight_disjoint (r := r) (m := halfSplitPoint r))


/-! =========================================================
    Section 2: Encoding-only split-register lemmas
========================================================= -/

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
      (disjoint_left_right r)
      (b := b) (yL := yL))
end EncodingOnly

/-! =========================================================
    Section 3: Exponential and qftPhase bridge lemmas
========================================================= -/

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

/-! =========================================================
    Section 4: Sum-pushing and scalar helper lemmas
========================================================= -/

lemma eval_sum_univ_qs
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [GateSemanticsCore qs]
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
    simpa using (RegEncoding.toNat_writeNat_of_lt (r := (leftReg r)) (v := k1.1) (b := b))

  have hdisj : Disjoint (leftReg r) (rightReg r) := disjoint_left_right (r := r)
  have hR :
      RegEncoding.toNat (rightReg r)
          (RegEncoding.writeNat (leftReg r) k1.1 b)
        =
      RegEncoding.toNat (rightReg r) b := by
    simpa using
      (RegEncoding.toNat_right_write_left (Basis := qs.Basis)
        (left := leftReg r) (right := rightReg r)
        hdisj (b := b) (yL := k1.1))

  simp [hL, hR, mul_comm]


lemma toNat_left_after_write_right
  (qs : QSemantics) [RegEncoding qs.Basis]
  (r : Reg) (b : qs.Basis) (yR : ℕ) :
  RegEncoding.toNat (leftReg r) (RegEncoding.writeNat (rightReg r) yR b)
    =
  RegEncoding.toNat (leftReg r) b := by
  have hdisj : Disjoint (leftReg r) (rightReg r) :=
    disjoint_left_right r
  simpa [leftReg, rightReg] using
    (RegEncoding.toNat_left_write_right
      (Basis := qs.Basis)
      (left := leftReg r) (right := rightReg r)
      hdisj
      (b := b) (yR := yR))

/-! =========================================================
    Section 5: First split-QFT steps
========================================================= -/

lemma step2_PhaseProdUsing_after_QFT_right
  (r : Reg)
  (ws : Gate.PhaseProdWorkspace (leftReg r) (rightReg r))
  (b : qs.Basis)
  (hclean : ws.Clean b) :
  let left  : Reg := leftReg r
  let right : Reg := rightReg r
  let A     : ℕ  := ASize left
  let B     : ℕ  := ASize right
  qs.eval
    (Gate.PhaseProdUsing
      ((2 * Real.pi) / (A*B : ℝ))
      left right ws)
    (qs.eval (Gate.QFT (ExtReg.ofReg right)) (qs.ket b))
    =
  ((1 / Real.sqrt ((B : ℕ) : ℝ) : ℂ)) •
    ∑ kH : Fin B,
      ((qftPhase B (RegEncoding.toNat right b) kH.1)
        *
        (qftPhase (A*B) (RegEncoding.toNat left b) kH.1))
        • qs.ket (RegEncoding.writeNat right kH.1 b) := by
  dsimp only
  classical
  let left  : Reg := leftReg r
  let right : Reg := rightReg r
  let A : ℕ := ASize left
  let B : ℕ := ASize right

  have hQFTright :
      qs.eval (Gate.QFT (ExtReg.ofReg right)) (qs.ket b)
        =
      ((1 / Real.sqrt ((B : ℕ) : ℝ) : ℂ)) •
        ∑ kH : Fin B,
          (qftPhase B (RegEncoding.toNat right b) kH.1) •
            qs.ket (RegEncoding.writeNat right kH.1 b) := by
    simpa [ASize, B, right] using
      (QFTSemantics.eval_QFT_ket (qs := qs) (r := ExtReg.ofReg right) (b := b))

  have phase_scalar_eq (kH : Fin B) :
      Complex.exp
        (((2 * Real.pi) / (A * B : ℝ)) * Complex.I *
          ((RegEncoding.toNat left (RegEncoding.writeNat right kH.1 b) : ℂ) *
            (RegEncoding.toNat right (RegEncoding.writeNat right kH.1 b) : ℂ)))
        =
      qftPhase (A*B) (RegEncoding.toNat left b) kH.1 := by
    have hdisj : Disjoint left right := by
      simpa [left, right] using (disjoint_left_right (r := r))

    have hL :
        RegEncoding.toNat left (RegEncoding.writeNat right kH.1 b)
          =
        RegEncoding.toNat left b := by
      simpa using
        (RegEncoding.toNat_left_write_right
          (Basis := qs.Basis)
          (left := left) (right := right)
          hdisj (b := b) (yR := kH.1))

    have hR :
        RegEncoding.toNat right (RegEncoding.writeNat right kH.1 b)
          =
        kH.1 := by
      simpa using
        (RegEncoding.toNat_writeNat_of_lt
          (r := right) (v := kH.1) (b := b)
          (by
            subst B
            simp [ASize]))

    have hmain :=
      exp_phaseProd_eq_qftPhase_of_casts
        (A := A) (B := B)
        (k1 := RegEncoding.toNat left b)
        (jR := kH.1)

    simpa [hL, hR, mul_assoc, mul_left_comm, mul_comm] using hmain

  calc
    qs.eval (Gate.PhaseProdUsing (2 * Real.pi / (↑A * ↑B)) left right ws)
        (qs.eval (Gate.QFT (ExtReg.ofReg right)) (qs.ket b))
        =
      qs.eval (Gate.PhaseProdUsing (2 * Real.pi / (↑A * ↑B)) left right ws)
        (((1 / Real.sqrt ((B : ℕ) : ℝ) : ℂ)) •
          ∑ kH : Fin B,
            (qftPhase B (RegEncoding.toNat right b) kH.1) •
              qs.ket (RegEncoding.writeNat right kH.1 b)) := by
        simp [hQFTright]
    _ =
      ((1 / Real.sqrt ((B : ℕ) : ℝ) : ℂ)) •
        qs.eval (Gate.PhaseProdUsing (2 * Real.pi / (↑A * ↑B)) left right ws)
          (∑ kH : Fin B,
            (qftPhase B (RegEncoding.toNat right b) kH.1) •
              qs.ket (RegEncoding.writeNat right kH.1 b)) := by
        simp [qs.eval_smul]
    _ =
      ((1 / Real.sqrt ((B : ℕ) : ℝ) : ℂ)) •
        ∑ kH : Fin B,
          qs.eval (Gate.PhaseProdUsing (2 * Real.pi / (↑A * ↑B)) left right ws)
            ((qftPhase B (RegEncoding.toNat right b) kH.1) •
              qs.ket (RegEncoding.writeNat right kH.1 b)) := by
        simp [eval_sum_univ_qs]
    _ =
      ((1 / Real.sqrt ((B : ℕ) : ℝ) : ℂ)) •
        ∑ kH : Fin B,
          (qftPhase B (RegEncoding.toNat right b) kH.1) •
            qs.eval (Gate.PhaseProdUsing (2 * Real.pi / (↑A * ↑B)) left right ws)
              (qs.ket (RegEncoding.writeNat right kH.1 b)) := by
        simp [qs.eval_smul]
    _ =
      ((1 / Real.sqrt ((B : ℕ) : ℝ) : ℂ)) •
        ∑ kH : Fin B,
          (qftPhase B (RegEncoding.toNat right b) kH.1) •
            (Complex.exp
              ((2 * Real.pi / (↑A * ↑B)) * Complex.I *
                ((RegEncoding.toNat left (RegEncoding.writeNat right kH.1 b) : ℂ) *
                  (RegEncoding.toNat right (RegEncoding.writeNat right kH.1 b) : ℂ))))
              • qs.ket (RegEncoding.writeNat right kH.1 b) := by
        congr
        funext kH
        have hcleanWrite :
            ws.Clean
              (RegEncoding.writeNat right kH.1 b) := by
          exact
            Gate.PhaseProdWorkspace.Clean.writeRight
              (qs := qs) ws b kH.1 hclean
        rw [GateSemanticsFacts.eval_PhaseProdUsing_ket
          qs
          (2 * Real.pi / (↑A * ↑B))
          left right ws
          (RegEncoding.writeNat right kH.1 b)
          hcleanWrite]
        simp
    _ =
      ((1 / Real.sqrt ((B : ℕ) : ℝ) : ℂ)) •
        ∑ kH : Fin B,
          ((qftPhase B (RegEncoding.toNat right b) kH.1)
            *
            (qftPhase (A * B) (RegEncoding.toNat left b) kH.1))
            • qs.ket (RegEncoding.writeNat right kH.1 b) := by
        refine congrArg (fun t => ((1 / Real.sqrt ((B : ℕ) : ℝ) : ℂ) • t)) ?_
        refine Finset.sum_congr rfl ?_
        intro kH hkH
        have h := phase_scalar_eq kH
        simp [smul_smul, mul_assoc]
        have h' :
            Complex.exp
              (2 * ↑Real.pi / (↑A * ↑B) *
                (Complex.I *
                  (↑(RegEncoding.toNat left (RegEncoding.writeNat right (↑kH) b)) *
                    ↑(RegEncoding.toNat right (RegEncoding.writeNat right (↑kH) b)))))
              =
            qftPhase (A * B) (RegEncoding.toNat left b) ↑kH := by
          simpa [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using h

        simp [h']

lemma step3_QFT_left_after_step2
  (r : Reg)
  (ws : Gate.PhaseProdWorkspace (leftReg r) (rightReg r))
  (b : qs.Basis)
  (hclean : ws.Clean b) :
  let left  : Reg := leftReg r
  let right : Reg := rightReg r
  let A     : ℕ  := ASize left
  let B     : ℕ  := ASize right
  qs.eval (Gate.QFT (ExtReg.ofReg left))
    (qs.eval
      (Gate.PhaseProdUsing
        ((2 * Real.pi) / (A*B : ℝ))
        left right ws)
      (qs.eval (Gate.QFT (ExtReg.ofReg right)) (qs.ket b)))
    =
  (((1 / Real.sqrt ((B : ℕ) : ℝ) : ℂ)) *
   ((1 / Real.sqrt ((A : ℕ) : ℝ) : ℂ))) •
    ∑ kH : Fin B,
      ∑ kL : Fin A,
        ((qftPhase B (RegEncoding.toNat right b) kH.1)
          *
          (qftPhase (A*B) (RegEncoding.toNat left b) kH.1)
          *
          (qftPhase A (RegEncoding.toNat left b) kL.1))
          • qs.ket
              (RegEncoding.writeNat left kL.1
                (RegEncoding.writeNat right kH.1 b)) := by
  dsimp only
  classical
  let left  : Reg := leftReg r
  let right : Reg := rightReg r
  let A : ℕ := ASize left
  let B : ℕ := ASize right

  have eval_sum_univ_qs {α : Type} [Fintype α] (U : Gate) (f : α → qs.State) :
      qs.eval U (∑ a : α, f a) = ∑ a : α, qs.eval U (f a) := by
    classical
    simpa using (by
      refine Finset.induction_on (s := (Finset.univ : Finset α)) ?h0 ?hs
      · simp [qs.eval_zero]
      · intro a s ha hs
        simp [Finset.sum_insert ha, qs.eval_add, hs])

  have hstep2 :
      qs.eval
        (Gate.PhaseProdUsing
          ((2 * Real.pi) / (A*B : ℝ))
          left right ws)
          (qs.eval (Gate.QFT (ExtReg.ofReg right)) (qs.ket b))
        =
      ((1 / Real.sqrt ((B : ℕ) : ℝ) : ℂ)) •
        ∑ kH : Fin B,
          ((qftPhase B (RegEncoding.toNat right b) kH.1)
            *
            (qftPhase (A*B) (RegEncoding.toNat left b) kH.1))
            • qs.ket (RegEncoding.writeNat right kH.1 b) := by
    simpa [left, right, A, B] using
      (step2_PhaseProdUsing_after_QFT_right
        (qs := qs) (r := r) (ws := ws) (b := b) hclean)

  calc
    qs.eval (Gate.QFT (ExtReg.ofReg left))
        (qs.eval
          (Gate.PhaseProdUsing
            ((2 * Real.pi) / (A*B : ℝ))
            left right ws)
          (qs.eval (Gate.QFT (ExtReg.ofReg right)) (qs.ket b)))
        =
      qs.eval (Gate.QFT (ExtReg.ofReg left))
        (((1 / Real.sqrt ((B : ℕ) : ℝ) : ℂ)) •
          ∑ kH : Fin B,
            ((qftPhase B (RegEncoding.toNat right b) kH.1)
              *
              (qftPhase (A*B) (RegEncoding.toNat left b) kH.1))
              • qs.ket (RegEncoding.writeNat right kH.1 b)) := by
        simp [hstep2]
    _ =
      ((1 / Real.sqrt ((B : ℕ) : ℝ) : ℂ)) •
        qs.eval (Gate.QFT (ExtReg.ofReg left))
          (∑ kH : Fin B,
            ((qftPhase B (RegEncoding.toNat right b) kH.1)
              *
              (qftPhase (A*B) (RegEncoding.toNat left b) kH.1))
              • qs.ket (RegEncoding.writeNat right kH.1 b)) := by
        simp [qs.eval_smul]
    _ =
      ((1 / Real.sqrt ((B : ℕ) : ℝ) : ℂ)) •
        ∑ kH : Fin B,
          qs.eval (Gate.QFT (ExtReg.ofReg left))
            (((qftPhase B (RegEncoding.toNat right b) kH.1)
              *
              (qftPhase (A*B) (RegEncoding.toNat left b) kH.1))
              • qs.ket (RegEncoding.writeNat right kH.1 b)) := by
        simp [eval_sum_univ_qs]
    _ =
      ((1 / Real.sqrt ((B : ℕ) : ℝ) : ℂ)) •
        ∑ kH : Fin B,
          ((qftPhase B (RegEncoding.toNat right b) kH.1)
            *
            (qftPhase (A*B) (RegEncoding.toNat left b) kH.1)) •
          (qs.eval (Gate.QFT (ExtReg.ofReg left))
            (qs.ket (RegEncoding.writeNat right kH.1 b))) := by
        simp [qs.eval_smul, mul_smul]
    _ =
      ((1 / Real.sqrt ((B : ℕ) : ℝ) : ℂ)) •
        ∑ kH : Fin B,
          ((qftPhase B (RegEncoding.toNat right b) kH.1)
            *
            (qftPhase (A*B) (RegEncoding.toNat left b) kH.1)) •
          (((1 / Real.sqrt ((A : ℕ) : ℝ) : ℂ)) •
            ∑ kL : Fin A,
              (qftPhase A
                (RegEncoding.toNat left
                  (RegEncoding.writeNat right kH.1 b))
                kL.1) •
              qs.ket
                (RegEncoding.writeNat left kL.1
                  (RegEncoding.writeNat right kH.1 b))) := by
        congr 2
        funext kH
        congr 1
        simpa [ASize, A] using
          (QFTSemantics.eval_QFT_ket (qs := qs) (r := ExtReg.ofReg left)
            (b := RegEncoding.writeNat right kH.1 b))
    _ =
      (((1 / Real.sqrt ((B : ℕ) : ℝ) : ℂ)) *
       ((1 / Real.sqrt ((A : ℕ) : ℝ) : ℂ))) •
        ∑ kH : Fin B,
          ∑ kL : Fin A,
            ((qftPhase B (RegEncoding.toNat right b) kH.1)
              *
              (qftPhase (A*B) (RegEncoding.toNat left b) kH.1)
              *
              (qftPhase A (RegEncoding.toNat left b) kL.1))
              • qs.ket
                  (RegEncoding.writeNat left kL.1
                    (RegEncoding.writeNat right kH.1 b)) := by
        simp [Finset.smul_sum,
              toNat_left_after_write_right (qs := qs) (r := r) (b := b),
              left, right, A, B,
              smul_smul, mul_assoc, mul_left_comm, mul_comm]

/-! =========================================================
    Section 6: Phase-combination lemmas
========================================================= -/

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

lemma step4_phase_combine_lowLeft
  (A B jL jH kL kH : ℕ)
  (hA : 0 < A) (hB : 0 < B) :
  (qftPhase B jH kH)
    * (qftPhase (A*B) jL kH)
    * (qftPhase A jL kL)
  =
  qftPhase (A*B) (jL + A*jH) (B*kL + kH) := by
  classical

  have h :=
    step4_phase_combine
      (A := B) (B := A)
      (j0 := jH) (j1 := jL)
      (k1 := kH) (k0 := kL)
      hB hA

  simpa [qftPhase, ωPow,
    Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

/-! =========================================================
    Section 7: Reindexing sums and cast utilities
========================================================= -/

lemma step5_reindex_sum
  {α : Type u} [AddCommMonoid α]
  (NR NL : ℕ)
  (f : Fin (NR * NL) → α) :
  (∑ p : Fin NR × Fin NL, f ((finMulAddEquiv NR NL) p))
    =
  ∑ k : Fin (NR * NL), f k := by
  classical
  exact (finMulAddEquiv NR NL).sum_comp f

lemma Asize_eq_lr (r : Reg) (m : ℕ) (hm : m ≤ regSize r) :
  let split : SplitPoint r := ⟨m, hm⟩
  let left  : Reg := splitLeft r split
  let right : Reg := splitRight r split
  ASize left * ASize right = ASize r := by
  dsimp only
  simp only [ASize, splitLeft_size, splitRight_size]
  rw [← Nat.pow_add]
  congr
  exact Nat.add_sub_of_le hm

open scoped BigOperators


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

/-! =========================================================
    Section 8: QFT split on basis kets
========================================================= -/

lemma eval_QFT_split_lowLeft_digitRev_ket
  (qs : QSemantics)
  [RegEncoding qs.Basis]

  [GateSemanticsFacts qs] :
  ∀ (r : Reg)
    (ws : Gate.PhaseProdWorkspace (leftReg r) (rightReg r))
    (b : qs.Basis),
    ws.Clean b →
    regSize r ≥ 2 →
    let left  : Reg := leftReg r
    let right : Reg := rightReg r
    let A     : ℕ := ASize left
    let B     : ℕ := ASize right
    let phi   : ℝ := (2 * Real.pi) / ((A * B : ℕ) : ℝ)
    qs.eval ((Gate.QFT (ExtReg.ofReg right)) ;;
             (Gate.PhaseProdUsing phi left right ws) ;;
             (Gate.QFT (ExtReg.ofReg left))) (qs.ket b)
      =
    (((1 / Real.sqrt ((B : ℕ) : ℝ) : ℂ)) *
     ((1 / Real.sqrt ((A : ℕ) : ℝ) : ℂ))) •
      ∑ kH : Fin B,
        ∑ kL : Fin A,
          qftPhase (A * B)
            (RegEncoding.toNat left b + A * RegEncoding.toNat right b)
            (B * kL.1 + kH.1)
            • qs.ket
                (RegEncoding.writeNat left kL.1
                  (RegEncoding.writeNat right kH.1 b)) := by
  intro r ws b hclean hr
  dsimp only
  classical

  let left  : Reg := leftReg r
  let right : Reg := rightReg r
  let A     : ℕ := ASize left
  let B     : ℕ := ASize right
  let phi   : ℝ := (2 * Real.pi) / ((A * B : ℕ) : ℝ)

  have hstep :=
    step3_QFT_left_after_step2
      (qs := qs) (r := r) (ws := ws) (b := b) hclean

  calc
    qs.eval ((Gate.QFT (ExtReg.ofReg right)) ;;
             (Gate.PhaseProdUsing phi left right ws) ;;
             (Gate.QFT (ExtReg.ofReg left))) (qs.ket b)
        =
      qs.eval (Gate.QFT (ExtReg.ofReg left))
        (qs.eval (Gate.PhaseProdUsing phi left right ws)
          (qs.eval (Gate.QFT (ExtReg.ofReg right)) (qs.ket b))) := by
        simp [qs.eval_seq]
    _ =
      (((1 / Real.sqrt ((B : ℕ) : ℝ) : ℂ)) *
       ((1 / Real.sqrt ((A : ℕ) : ℝ) : ℂ))) •
        ∑ kH : Fin B,
          ∑ kL : Fin A,
            ((qftPhase B (RegEncoding.toNat right b) kH.1)
              *
              (qftPhase (A * B) (RegEncoding.toNat left b) kH.1)
              *
              (qftPhase A (RegEncoding.toNat left b) kL.1))
              • qs.ket
                  (RegEncoding.writeNat left kL.1
                    (RegEncoding.writeNat right kH.1 b)) := by
        simpa [A, B, phi, Nat.cast_mul] using hstep
    _ =
      (((1 / Real.sqrt ((B : ℕ) : ℝ) : ℂ)) *
       ((1 / Real.sqrt ((A : ℕ) : ℝ) : ℂ))) •
        ∑ kH : Fin B,
          ∑ kL : Fin A,
            qftPhase (A * B)
              (RegEncoding.toNat left b + A * RegEncoding.toNat right b)
              (B * kL.1 + kH.1)
              • qs.ket
                  (RegEncoding.writeNat left kL.1
                    (RegEncoding.writeNat right kH.1 b)) := by
        refine congrArg
          (fun t =>
            (((1 / Real.sqrt ((B : ℕ) : ℝ) : ℂ)) *
             ((1 / Real.sqrt ((A : ℕ) : ℝ) : ℂ))) • t) ?_
        refine Finset.sum_congr rfl ?_
        intro kH hkH
        refine Finset.sum_congr rfl ?_
        intro kL hkL
        have hphase :
            (qftPhase B (RegEncoding.toNat right b) kH.1)
              *
              (qftPhase (A * B) (RegEncoding.toNat left b) kH.1)
              *
              (qftPhase A (RegEncoding.toNat left b) kL.1)
            =
            qftPhase (A * B)
              (RegEncoding.toNat left b + A * RegEncoding.toNat right b)
              (B * kL.1 + kH.1) := by
          exact
            step4_phase_combine_lowLeft
              (A := A) (B := B)
              (jL := RegEncoding.toNat left b)
              (jH := RegEncoding.toNat right b)
              (kL := kL.1)
              (kH := kH.1)
              (by
                subst A
                simp [ASize])
              (by
                subst B
                simp [ASize])
        simp [hphase]

/-! =========================================================
    Section 9: Radix reversal and exact QFT split
========================================================= -/

lemma radix_reverse_reindex_sum
  {α : Type u} [AddCommMonoid α]
  (A B : ℕ) (hB : 0 < B)
  (F : ℕ → α) :
  (∑ kH : Fin B, ∑ kL : Fin A, F (B * kL.1 + kH.1))
    =
  ∑ y : Fin (A * B), F y.1 := by
  classical

  have hprod :
      (∑ kH : Fin B, ∑ kL : Fin A, F (B * kL.1 + kH.1))
        =
      ∑ p : Fin B × Fin A, F (B * p.2.1 + p.1.1) := by
    change
      (Finset.univ.sum
        (fun kH : Fin B =>
          Finset.univ.sum
            (fun kL : Fin A => F (B * kL.1 + kH.1))))
      =
      Finset.univ.sum
        (fun p : Fin B × Fin A => F (B * p.2.1 + p.1.1))
    rw [Fintype.sum_prod_type]

  rw [hprod]

  have hBA :
      (∑ p : Fin B × Fin A, F (B * p.2.1 + p.1.1))
        =
      ∑ y : Fin (B * A), F y.1 := by
    have h :=
      step5_reindex_sum
        (NR := B) (NL := A)
        (f := fun y : Fin (B * A) => F y.1)
    simpa [finMulAddEquiv, hB,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

  rw [hBA]

  let e : Fin (B * A) ≃ Fin (A * B) :=
    Equiv.cast (congrArg Fin (Nat.mul_comm B A))

  have hcast :
      (∑ y : Fin (B * A), F y.1)
        =
      ∑ y : Fin (A * B), F y.1 := by
    have hsum :=
      Equiv.sum_comp e (fun y : Fin (A * B) => F y.1)

    calc
      (∑ y : Fin (B * A), F y.1)
          =
        ∑ y : Fin (B * A), F ((e y : Fin (A * B)) : ℕ) := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          have hval :
              ((e y : Fin (A * B)) : ℕ) = y.1 := by
            dsimp [e]
            simpa using
              (Fin.coe_cast_typeEq
                (h := congrArg Fin (Nat.mul_comm B A))
                (y := y))
          simp [hval]
      _ =
        ∑ y : Fin (A * B), F y.1 := by
          simpa using hsum

  exact hcast

lemma eval_RadixReverse_digitRev_sum
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [GateSemanticsFacts qs]
  (r : Reg) (m : ℕ) (b : qs.Basis)
  (left right : Reg)
  (A B : ℕ)
  (C : ℂ)
  (hm : m ≤ regSize r)
  (hleft : left = splitLeft r ⟨m, hm⟩)
  (hright : right = splitRight r ⟨m, hm⟩)
  (hA : A = ASize left)
  (hB : B = ASize right) :
  qs.eval (Gate.RadixReverse r m)
    (C •
      ∑ kH : Fin B,
        ∑ kL : Fin A,
          qftPhase (A * B)
            (RegEncoding.toNat left b + A * RegEncoding.toNat right b)
            (B * kL.1 + kH.1)
            • qs.ket
                (RegEncoding.writeNat left kL.1
                  (RegEncoding.writeNat right kH.1 b)))
    =
  C •
      ∑ kH : Fin B,
        ∑ kL : Fin A,
          qftPhase (A * B)
            (RegEncoding.toNat left b + A * RegEncoding.toNat right b)
            (B * kL.1 + kH.1)
            • qs.ket
                (RegEncoding.writeNat r
                  (B * kL.1 + kH.1)
                  b) := by
  classical
  rw [qs.eval_smul]
  congr 1

  rw [eval_sum_univ_qs]
  refine Finset.sum_congr rfl ?_
  intro kH hkH

  rw [eval_sum_univ_qs]
  refine Finset.sum_congr rfl ?_
  intro kL hkL

  rw [qs.eval_smul]
  congr 1

  have hkL_lt : kL.1 < ASize (splitLeft r ⟨m, hm⟩) := by
    simp [← hleft, ← hA]

  have hkH_lt : kH.1 < ASize (splitRight r ⟨m, hm⟩) := by
    simp [← hright, ← hB]

  have hsem :=
    RadixReverseSemantics.eval_RadixReverse_ket
      (qs := qs)
      (r := r) (m := m) (b := b)
      (kL := kL.1) (kH := kH.1)
      hm hkL_lt hkH_lt

  simpa [← hleft, ← hright,
    radixReverseIndex, ← hB,
    Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hsem

lemma eval_QFT_ket_as_split_sum
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [GateSemanticsFacts qs]
  (r : Reg) (b : qs.Basis)
  (m : ℕ)
  (left right : Reg)
  (A B : ℕ)
  (hm : m ≤ regSize r)
  (hleft : left = splitLeft r ⟨m, hm⟩)
  (hright : right = splitRight r ⟨m, hm⟩)
  (hA : A = ASize left)
  (hB : B = ASize right) :
  qs.eval (Gate.QFT (ExtReg.ofReg r)) (qs.ket b)
    =
  (((1 / Real.sqrt ((B : ℕ) : ℝ) : ℂ)) *
   ((1 / Real.sqrt ((A : ℕ) : ℝ) : ℂ))) •
    ∑ y : Fin (A * B),
      qftPhase (A * B)
        (RegEncoding.toNat left b + A * RegEncoding.toNat right b)
        y.1
        • qs.ket (RegEncoding.writeNat r y.1 b) := by
  classical

  have hAB : A * B = ASize r := by
    calc
      A * B =
          ASize (splitLeft r ⟨m, hm⟩) *
            ASize (splitRight r ⟨m, hm⟩) := by
              rw [hA, hB, hleft, hright]
      _ = ASize r := Asize_eq_lr (r := r) (m := m) hm

  have hAB_pow : A * B = 2 ^ regSize r := by
    simpa [ASize] using hAB

  have hToNat :
      RegEncoding.toNat r b =
        RegEncoding.toNat left b + A * RegEncoding.toNat right b := by
    have h := RegEncoding.toNat_split (r := r) (b := b) (m := ⟨m, hm⟩)
    subst A
    subst left
    subst right
    simpa [ASize] using h

  have hNorm :
      ((1 / Real.sqrt ((2 ^ regSize r : ℕ) : ℝ) : ℂ))
        =
      (((1 / Real.sqrt ((B : ℕ) : ℝ) : ℂ)) *
       ((1 / Real.sqrt ((A : ℕ) : ℝ) : ℂ))) := by
    have hsplit :=
      qft_norm_split
        (nTot := regSize r)
        (m := m)
        hm
    subst A
    subst B
    subst left
    subst right
    simp[ASize]
    rw [mul_comm]
    simp_rw [← one_div]
    aesop

  rw [QFTSemantics.eval_QFT_ket]
  simp [ExtReg.ofReg, ExtReg.width, ExtReg.toNat, regSize]
  rw [show 2 ^ r.width = A * B by
    simpa [regSize] using hAB_pow.symm]
  rw [hToNat]
  simp_rw [← one_div]
  congr 1
  · simpa [regSize] using hNorm

lemma eval_QFT_split_ket_ofReg
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs] :
    ∀ (r : Reg)
      (ws :
        Gate.PhaseProdWorkspace
          (leftReg r)
          (rightReg r))
      (b : qs.Basis),
      ws.Clean b →
      regSize r ≥ 2 →
      let nTot  : ℕ := regSize r
      let m     : ℕ := nTot / 2
      let left  : Reg := leftReg r
      let right : Reg := rightReg r
      let phi : ℝ := qftPhi nTot
      qs.eval
          (Gate.QFT (ExtReg.ofReg r))
          (qs.ket b)
        =
      qs.eval
        ((Gate.QFT (ExtReg.ofReg right)) ;;
         Gate.PhaseProdUsing phi left right ws ;;
         (Gate.QFT (ExtReg.ofReg left)) ;;
         Gate.RadixReverse r m)
        (qs.ket b) := by
  intro r ws b hclean hsz
  dsimp only
  classical

  let nTot : ℕ := regSize r
  let m : ℕ := nTot / 2
  let left : Reg := leftReg r
  let right : Reg := rightReg r
  let A : ℕ := ASize left
  let B : ℕ := ASize right
  let phi : ℝ := qftPhi nTot

  have hm : m ≤ regSize r := by
    unfold m nTot
    exact Nat.div_le_self _ _

  have hleft_split : left = splitLeft r ⟨m, hm⟩ := by
    simp [left, leftReg, halfSplitPoint, splitM, m, nTot]

  have hright_split : right = splitRight r ⟨m, hm⟩ := by
    simp [right, rightReg, halfSplitPoint, splitM, m, nTot]

  have hA : A = ASize left := rfl
  have hB : B = ASize right := rfl

  have hAB : A * B = ASize r := by
    calc
      A * B =
          ASize (splitLeft r ⟨m, hm⟩) *
            ASize (splitRight r ⟨m, hm⟩) := by
              rw [hA, hB, hleft_split, hright_split]
      _ = ASize r := Asize_eq_lr (r := r) (m := m) hm

  have hAB_pow : A * B = 2 ^ regSize r := by
    simpa [ASize] using hAB

  have hPhi :
      phi = (2 * Real.pi) / ((A * B : ℕ) : ℝ) := by
    unfold phi qftPhi
    simp_all
    rfl

  let C : ℂ :=
    (((1 / Real.sqrt ((B : ℕ) : ℝ) : ℂ)) *
     ((1 / Real.sqrt ((A : ℕ) : ℝ) : ℂ)))

  have hDigit :
    qs.eval
        ((Gate.QFT (ExtReg.ofReg right)) ;;
         (Gate.PhaseProdUsing phi left right ws) ;;
         (Gate.QFT (ExtReg.ofReg left)))
        (qs.ket b)
        =
      C •
        ∑ kH : Fin B,
          ∑ kL : Fin A,
            qftPhase (A * B)
              (RegEncoding.toNat left b + A * RegEncoding.toNat right b)
              (B * kL.1 + kH.1)
              • qs.ket
                  (RegEncoding.writeNat left kL.1
                    (RegEncoding.writeNat right kH.1 b)) := by
    have h :=
      eval_QFT_split_lowLeft_digitRev_ket
        (qs := qs) (r := r) (ws := ws) (b := b) hclean hsz
    simpa [nTot, m, left, right, A, B, phi, hPhi, C] using h

  have hAfterRev :
      qs.eval (Gate.RadixReverse r m)
        (qs.eval
          ((Gate.QFT (ExtReg.ofReg right)) ;;
           (Gate.PhaseProdUsing phi left right ws) ;;
           (Gate.QFT (ExtReg.ofReg left)))
          (qs.ket b))
        =
      C •
        ∑ kH : Fin B,
          ∑ kL : Fin A,
            qftPhase (A * B)
              (RegEncoding.toNat left b + A * RegEncoding.toNat right b)
              (B * kL.1 + kH.1)
              • qs.ket
                  (RegEncoding.writeNat r
                    (B * kL.1 + kH.1)
                    b) := by
    rw [hDigit]
    exact
      eval_RadixReverse_digitRev_sum
        (qs := qs)
        (r := r) (m := m) (b := b)
        (left := left) (right := right)
        (A := A) (B := B)
        (C := C)
        hm hleft_split hright_split hA hB

  have hReindex :
      (∑ kH : Fin B,
          ∑ kL : Fin A,
            qftPhase (A * B)
              (RegEncoding.toNat left b + A * RegEncoding.toNat right b)
              (B * kL.1 + kH.1)
              • qs.ket
                  (RegEncoding.writeNat r
                    (B * kL.1 + kH.1)
                    b))
        =
      ∑ y : Fin (A * B),
        qftPhase (A * B)
          (RegEncoding.toNat left b + A * RegEncoding.toNat right b)
          y.1
          • qs.ket (RegEncoding.writeNat r y.1 b) := by
    exact
      radix_reverse_reindex_sum
        (α := qs.State)
        (A := A) (B := B)
        (by
          subst B
          simp [ASize])
        (fun y : ℕ =>
          qftPhase (A * B)
            (RegEncoding.toNat left b + A * RegEncoding.toNat right b)
            y
            • qs.ket (RegEncoding.writeNat r y b))

  have hStandard :
      qs.eval (Gate.QFT (ExtReg.ofReg r)) (qs.ket b)
        =
      C •
        ∑ y : Fin (A * B),
          qftPhase (A * B)
            (RegEncoding.toNat left b + A * RegEncoding.toNat right b)
            y.1
            • qs.ket (RegEncoding.writeNat r y.1 b) := by
    exact
      eval_QFT_ket_as_split_sum
        (qs := qs)
        (r := r) (b := b)
        (m := m)
        (left := left) (right := right)
        (A := A) (B := B)
        hm hleft_split hright_split hA hB

  calc
    qs.eval (Gate.QFT (ExtReg.ofReg r)) (qs.ket b)
        =
      C •
        ∑ y : Fin (A * B),
          qftPhase (A * B)
            (RegEncoding.toNat left b + A * RegEncoding.toNat right b)
            y.1
            • qs.ket (RegEncoding.writeNat r y.1 b) := hStandard
    _ =
      C •
        ∑ kH : Fin B,
          ∑ kL : Fin A,
            qftPhase (A * B)
              (RegEncoding.toNat left b + A * RegEncoding.toNat right b)
              (B * kL.1 + kH.1)
              • qs.ket
                  (RegEncoding.writeNat r
                    (B * kL.1 + kH.1)
                    b) := by
        rw [hReindex]
    _ =
      qs.eval (Gate.RadixReverse r m)
        (qs.eval
          ((Gate.QFT (ExtReg.ofReg right)) ;;
           (Gate.PhaseProdUsing phi left right ws) ;;
           (Gate.QFT (ExtReg.ofReg left)))
          (qs.ket b)) := by
        exact hAfterRev.symm
    _ =
      qs.eval
        ((Gate.QFT (ExtReg.ofReg right)) ;;
         (Gate.PhaseProdUsing phi left right ws) ;;
         (Gate.QFT (ExtReg.ofReg left)) ;;
         (Gate.RadixReverse r m))
        (qs.ket b) := by
        simp [qs.eval_seq]

theorem eval_QFT_split_ofReg
  (qs : QSemantics)
  [RegEncoding qs.Basis]

  [GateSemanticsFacts qs] :
    ∀ (r : Reg)
      (ws : Gate.PhaseProdWorkspace (leftReg r) (rightReg r))
      (ψ : qs.State),
      Gate.PhaseProdWorkspace.CleanState qs ws ψ →
      regSize r ≥ 2 →
      let nTot  : ℕ := regSize r
      let m     : ℕ := nTot / 2
      let left  : Reg := leftReg r
      let right : Reg := rightReg r
      qs.eval (Gate.QFT (ExtReg.ofReg r)) ψ
        =
      qs.eval
        ((Gate.QFT (ExtReg.ofReg right)) ;;
         (Gate.PhaseProdUsing
            (qftPhi nTot) left right ws) ;;
         (Gate.QFT (ExtReg.ofReg left)) ;;
         (Gate.RadixReverse r m)) ψ := by
  intro r ws ψ hclean hsz
  induction hclean with
  | zero =>
      simp [qs.eval_zero]
  | ket b hcleanBasis =>
      exact
        eval_QFT_split_ket_ofReg
          (qs := qs)
          (r := r)
          (ws := ws)
          (b := b)
          hcleanBasis
          hsz
  | add hψ hφ ihψ ihφ =>
      simp [qs.eval_add, ihψ, ihφ]
  | smul a hψ ihψ =>
      simp [qs.eval_smul, ihψ]

/--
Reserve-aware QFT decomposition.

The mathematical transform acts only on `r.active`.  Both recursive QFTs
reuse `r.reserve`; the phase-product workspace may also be selected from that
reserve by the lowering layer.  Correctness relies on each component restoring
the workspace before the following component executes.
-/
theorem eval_QFT_split
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs] :
    ∀ (r : ExtReg)
      (ws : Gate.PhaseProdWorkspace (leftReg r.active) (rightReg r.active))
      (ψ : qs.State),
      Gate.PhaseProdWorkspace.CleanState qs ws ψ →
      r.width ≥ 2 →
      let nTot  : ℕ := r.width
      let m     : ℕ := nTot / 2
      let left  : Reg := leftReg r.active
      let right : Reg := rightReg r.active
      qs.eval (Gate.QFT r) ψ
        =
      qs.eval
        ((Gate.QFT (rightQFTReg r)) ;;
         (Gate.PhaseProdUsing
            (qftPhi nTot) left right ws) ;;
         (Gate.QFT (leftQFTReg r)) ;;
         (Gate.RadixReverse r.active m))
        ψ := by
  intro r ws ψ hclean hsize
  dsimp only

  have hsizeActive :
      regSize r.active ≥ 2 := by
    simpa [ExtReg.width] using hsize

  have hcore :=
    eval_QFT_split_ofReg
      (qs := qs)
      (r := r.active)
      (ws := ws)
      (ψ := ψ)
      hclean
      hsizeActive

  have hroot :
      qs.eval (Gate.QFT r) ψ =
        qs.eval
          (Gate.QFT (ExtReg.ofReg r.active))
          ψ := by
    exact
      eval_QFT_eq_of_active_eq
        (qs := qs)
        r
        (ExtReg.ofReg r.active)
        rfl
        ψ

  have hright :
      ∀ φ : qs.State,
        qs.eval
            (Gate.QFT
              (ExtReg.ofReg (rightReg r.active)))
            φ
          =
        qs.eval
            (Gate.QFT (rightQFTReg r))
            φ := by
    intro φ
    exact
      eval_QFT_eq_of_active_eq
        (qs := qs)
        (ExtReg.ofReg (rightReg r.active))
        (rightQFTReg r)
        rfl
        φ

  have hleft :
      ∀ φ : qs.State,
        qs.eval
            (Gate.QFT
              (ExtReg.ofReg (leftReg r.active)))
            φ
          =
        qs.eval
            (Gate.QFT (leftQFTReg r))
            φ := by
    intro φ
    exact
      eval_QFT_eq_of_active_eq
        (qs := qs)
        (ExtReg.ofReg (leftReg r.active))
        (leftQFTReg r)
        rfl
        φ

  calc
    qs.eval (Gate.QFT r) ψ
        =
      qs.eval
        (Gate.QFT (ExtReg.ofReg r.active))
        ψ := hroot

    _ =
      qs.eval
        ((Gate.QFT
            (ExtReg.ofReg (rightReg r.active))) ;;
         (Gate.PhaseProdUsing
            (qftPhi r.width)
            (leftReg r.active)
            (rightReg r.active)
            ws) ;;
         (Gate.QFT
            (ExtReg.ofReg (leftReg r.active))) ;;
         (Gate.RadixReverse
            r.active
            (r.width / 2)))
        ψ := by
      simpa [ExtReg.width] using hcore

    _ =
      qs.eval
        ((Gate.QFT (rightQFTReg r)) ;;
         (Gate.PhaseProdUsing
            (qftPhi r.width)
            (leftReg r.active)
            (rightReg r.active)
            ws) ;;
         (Gate.QFT (leftQFTReg r)) ;;
         (Gate.RadixReverse
            r.active
            (r.width / 2)))
        ψ := by
      simp only [qs.eval_seq]
      rw [hright, hleft]
