import ForShor.ShorVerification.Implementation.Shor.Proofs.NaiveShor.GoodOutcomeMassLowerBound
import ForShor.ShorVerification.Implementation.Shor.Statement
import ForShor.ShorVerification.Implementation.Shor.Proofs.Math.Factoring_Reduction.ProbabilityBound
import ForShor.ShorVerification.Implementation.Shor.Proofs.Math.Factoring_Reduction.Reduction

/-!
# Naive Shor Correctness
-/

namespace Shor

variable {qs : QSemantics}
variable [RegEncoding qs.Basis]
variable [MeasureClass qs]

/-- Public assertion for `Shor_correct`. -/
def ShorCorrect
    [GateSemanticsFacts qs]
    (T : ℕ → ℕ)
    (_hT : ContinuedFractionSearchComplete T)
    (inst : ShorOrderFindingInstance)
    (x y : ExtReg)
    (b0 : qs.Basis)
    (_hm : regSize x.active = Nat.log2 (2 * inst.N^2))
    (_hn : regSize y.active = Nat.log2 (2 * inst.N))
    (_hinput : IdealOrderFindingInput qs x y b0) : Prop :=
  probability_of_success
        (qs := qs) (T := T)
        (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
        (x := x.active)
        (r := ord inst.a inst.N inst.coprime)
        (Q := ASize x.active)
        (evalC := qs.eval)
        (C := orderFindingIdeal (qs := qs) inst.a inst.N x y)
        (ψ := qs.ket b0)
      ≥
    κ / Real.log ((Nat.log2 inst.N : ℝ) + 1)

/-! =========================================================
    Ideal Order-Finding Correctness
========================================================= -/

/-- Ideal order-finding success probability for Shor's algorithm. -/
theorem Shor_correct
    [GateSemanticsFacts qs]
    (T : ℕ → ℕ)
    (hT : ContinuedFractionSearchComplete T)
    (inst : ShorOrderFindingInstance)
    (x y : ExtReg)
    (b0 : qs.Basis)
    (hm : regSize x.active = Nat.log2 (2 * inst.N^2))
    (hn : regSize y.active = Nat.log2 (2 * inst.N))
    (hinput : IdealOrderFindingInput qs x y b0) :
    ShorCorrect T hT inst x y b0 hm hn hinput := by

  unfold ShorCorrect

  have hsetting :
      BasicSetting
        inst.a
        (ord inst.a inst.N inst.coprime)
        inst.N
        (regSize x.active)
        (regSize y.active) :=
    basicSetting_of_shor_instance
      inst
      (regSize x.active)
      (regSize y.active)
      hm
      hn

  calc
    κ / Real.log ((Nat.log2 inst.N : ℝ) + 1)
        ≤
      ∑ o : Fin (ASize x.active),
        goodOutcomeIndicator
          o.1
          (ASize x.active)
          (ord inst.a inst.N inst.coprime) *
        MeasureClass.probMeas
          (qs := qs)
          x.active
          o.1
          (qs.eval
          (orderFindingIdeal
            (qs := qs) inst.a inst.N x y)
          (qs.ket b0)) :=
      ideal_orderFinding_goodOutcome_mass_lower_bound
        inst x y b0 hsetting hinput

    _ ≤
      probability_of_success
        (qs := qs)
        (T := T)
        (verify :=
          fun d =>
            decide ((inst.a ^ d) % inst.N = 1))
        (x := x.active)
        (r := ord inst.a inst.N inst.coprime)
        (Q := ASize x.active)
        (evalC := qs.eval)
        (C :=
          orderFindingIdeal
            (qs := qs)
            inst.a inst.N x y)
        (ψ := qs.ket b0) :=
      goodOutcome_mass_le_probability_of_success
        T hT inst
        qs.eval
        x.active
        (ASize x.active)
        (orderFindingIdeal
          (qs := qs)
          inst.a inst.N x y)
        (qs.ket b0)

/-- At least half of the bases are good, and the ideal circuit finds the order
of a good base with probability at least `κ / log(log₂ N + 1)`, from which a
nontrivial factor follows. -/
def ShorEndToEndFactoring [GateSemanticsFacts qs] (T : ℕ → ℕ)
    (_hT : ContinuedFractionSearchComplete T) (fact : ShorFactoringInstance) (x y : ExtReg)
    (b0 : qs.Basis) (_hinput : IdealOrderFindingInput qs x y b0)
    (_hm : regSize x.active = Nat.log2 (2 * fact.N^2))
    (_hn : regSize y.active = Nat.log2 (2 * fact.N)) : Prop :=
  (2 * (successful_choices fact.N).card ≥ (valid_choices fact.N).card) ∧
  (∀ a ∈ successful_choices fact.N, ∃ (hgcd : Nat.gcd a fact.N = 1),
    (probability_of_success (qs := qs) (T := T)
      (verify := fun d => decide ((a ^ d) % fact.N = 1))
      (x := x.active) (r := ord a fact.N hgcd) (Q := ASize x.active)
      (evalC := qs.eval) (C := orderFindingIdeal (qs := qs) a fact.N x y) (ψ := qs.ket b0)
    ≥ κ / Real.log ((Nat.log2 fact.N : ℝ) + 1)) ∧
    (is_nontrivial_factor (Nat.gcd ((a ^ (ord a fact.N hgcd / 2)) - 1) fact.N) fact.N ∨
     is_nontrivial_factor (Nat.gcd ((a ^ (ord a fact.N hgcd / 2)) + 1) fact.N) fact.N))

/-- End-to-end statement combining the classical choice probability, ideal
quantum order-finding, and the classical factor extraction theorem. -/
theorem Shor_end_to_end_factoring
    [GateSemanticsFacts qs]
    (T : ℕ → ℕ)
    (hT : ContinuedFractionSearchComplete T)
    (fact : ShorFactoringInstance)
    (x y : ExtReg)
    (b0 : qs.Basis)
    (hinput : IdealOrderFindingInput qs x y b0)
    (hm : regSize x.active = Nat.log2 (2 * fact.N^2))
    (hn : regSize y.active = Nat.log2 (2 * fact.N)) :
    ShorEndToEndFactoring T hT fact x y b0 hinput hm hn := by {
  let N := fact.N
  have h_odd : Odd N := fact.odd
  have h_N : N > 2 := fact.gt_two
  have h_not_prime_power : ∀ (p k : ℕ), Nat.Prime p → N ≠ p ^ k :=
    fact.not_prime_power
  constructor
  { exact shors_probability_bound N h_odd (by omega) h_not_prime_power }
  {
    intro a h_a_in_successful
    obtain ⟨⟨ha1, ha2⟩, hgcd⟩ := success_eq_conditions a N h_a_in_successful
    have hvalid_N : a ∈ valid_choices N := by
      simp [valid_choices, ha1, ha2, hgcd]
    have hvalid_fact : a ∈ valid_choices fact.N := by
      simpa [N] using hvalid_N

    have h_succ : shor_success_conditions a (ord a N hgcd) N := by {
      have h_a_in_successful_N : a ∈ successful_choices N := by
        simpa [N] using h_a_in_successful
      have h_a_is_succ : is_successful_choice a N := by {
        unfold successful_choices at h_a_in_successful_N
        simp_all
      }
      unfold is_successful_choice is_period at h_a_is_succ
      obtain ⟨r, h_per, h_cond⟩ := h_a_is_succ
      have h_r_eq : r = ord a N hgcd := by {
        have h_bridge := is_period_ord a N hgcd
        subst h_per
        simpa
      }
      rwa [h_r_eq] at h_cond
    }

    exists hgcd
    let inst : ShorOrderFindingInstance :=
      { a := a
        N := N
        range := ⟨by omega, ha2⟩
        coprime := hgcd
        }
    exact ⟨
      by
        simpa [N, inst] using!
          (Shor_correct (qs := qs) T hT inst x y b0 hm hn hinput),
      shors_classical_reduction
        a
        (ord a N hgcd)
        N
        h_N
        ⟨ha1, ha2⟩
        hgcd
        (is_period_ord a N hgcd)
        h_succ
    ⟩
  }
}

end Shor
