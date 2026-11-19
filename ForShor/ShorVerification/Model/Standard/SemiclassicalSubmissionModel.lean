import ForShor.ShorVerification.Model.Standard.LowGates
import ForShor.ShorVerification.Submission.CorrectSemiclassical

/-!
# The semiclassical submission certificate in the standard model

`Submission/CorrectSemiclassical.lean` proves, for every `qs : QSemantics.{0}` with the
framework's classes, that the semiclassical program of any accepted submission meets the
coherent declared bound `referenceSuccessProbabilityAt submissionPrecision N`. This file shows
the statement is about something real:

* `model_policy_submission_correct_semiclassical`: the certificate at the concrete model
  `Model.qs` (so the universe restriction `QSemantics.{0}` and the instance arguments are
  satisfiable);
* `exists_continuedFractionSearchComplete`: some continued-fraction search bound `T` is
  complete (the continued fraction of a rational terminates), so the `T` hypothesis the
  certificate shares with the coherent one is satisfiable;
* `exists_2048Bit_instance`: some order-finding instance has a 2048-bit modulus;
* `model_semiclassical_submission_headline`: at `Model.qs`, for every policy submission,
  every complete `T` and every 2048-bit instance, the semiclassical program succeeds with
  probability at least `99/100 · κ / log 2048`, a positive number;
* `model_semiclassical_submission_nonvacuous`: all of this at once, for a concrete
  submission (the standard arity-2 table) and a concrete 2048-bit instance.
-/

namespace Shor
namespace Model

open Reference Readout

/-- **The semiclassical certificate in the standard model.** `policy_submission_correct_semiclassical`
at `Model.qs`. -/
theorem model_policy_submission_correct_semiclassical (s : ShorPolicySubmission) :
    ∀ (T : ℕ → ℕ), ContinuedFractionSearchComplete T →
    ∀ inst : ShorOrderFindingInstance,
      referenceSuccessProbabilityAt submissionPrecision inst.N ≤
        probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
          (referenceSemiclassicalProgramAt s.policy s.policy_admissible
            submissionPrecision inst).rounds
          (ord inst.a inst.N inst.coprime)
          (2 ^ (referenceSemiclassicalProgramAt s.policy s.policy_admissible
            submissionPrecision inst).rounds)
          ((referenceSemiclassicalProgramAt s.policy s.policy_admissible
              submissionPrecision inst).circuit.eval
            (MState.init (qs.ket (RegEncoding.zero (Basis := qs.Basis))))) :=
  policy_submission_correct_semiclassical (qs := qs) s

/-- A complete continued-fraction search bound exists: for every `Q`, take one more than the
sum over `o < Q` of a termination index of the continued fraction of `o / Q` (which is
rational, so its continued fraction terminates). -/
theorem exists_continuedFractionSearchComplete :
    ∃ T : ℕ → ℕ, ContinuedFractionSearchComplete T := by
  have h : ∀ Q o : ℕ, ∃ n, (GenContFract.of ((o : ℝ) / (Q : ℝ))).TerminatedAt n := fun Q o =>
    (GenContFract.terminates_iff_rat ((o : ℝ) / (Q : ℝ))).mpr
      ⟨(o : ℚ) / (Q : ℚ), by push_cast; rfl⟩
  classical
  refine ⟨fun Q => ∑ o ∈ Finset.range Q, (Classical.choose (h Q o) + 1), ?_⟩
  intro Q o ho
  refine ⟨Classical.choose (h Q o), ?_, Classical.choose_spec (h Q o)⟩
  have hle : Classical.choose (h Q o) + 1 ≤
      ∑ o' ∈ Finset.range Q, (Classical.choose (h Q o') + 1) :=
    Finset.single_le_sum (f := fun o' => Classical.choose (h Q o') + 1)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr ho)
  exact lt_of_lt_of_le (Nat.lt_succ_self _) hle

private theorem two_lt_two_pow_add_one (k : ℕ) (hk : 2 ≤ k) : 2 < 2 ^ k + 1 := by
  have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  omega

private theorem gcd_two_two_pow_add_one (k : ℕ) (hk : k ≠ 0) : Nat.gcd 2 (2 ^ k + 1) = 1 :=
  Nat.coprime_two_left.mpr (Nat.even_pow.mpr ⟨even_two, hk⟩).add_one

private theorem two_pow_add_one_lt (k : ℕ) (hk : k ≠ 0) : 2 ^ k + 1 < 2 ^ (k + 1) := by
  have h1 : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hk)
  rw [pow_succ]
  omega

/-- The order-finding instance `a = 2`, `N = 2^k + 1` (odd, so coprime to `2`), for `k ≥ 2`. -/
def instTwoPowAddOne (k : ℕ) (hk : 2 ≤ k) : ShorOrderFindingInstance where
  a := 2
  N := 2 ^ k + 1
  range := ⟨Nat.two_pos, two_lt_two_pow_add_one k hk⟩
  coprime := gcd_two_two_pow_add_one k (by omega)

/-- A concrete 2048-bit order-finding instance: `a = 2`, `N = 2^2047 + 1`. -/
def inst2048 : ShorOrderFindingInstance := instTwoPowAddOne 2047 (by decide)

theorem inst2048_is2048Bit : Is2048Bit inst2048.N := by
  have h := two_pow_add_one_lt 2047 (by decide)
  rw [show 2047 + 1 = 2048 from rfl] at h
  exact ⟨Nat.le_add_right _ _, h⟩

/-- Some order-finding instance has a 2048-bit modulus. -/
theorem exists_2048Bit_instance : ∃ inst : ShorOrderFindingInstance, Is2048Bit inst.N :=
  ⟨inst2048, inst2048_is2048Bit⟩

/-- **The semiclassical program of every submission keeps 99% of the ideal 2048-bit
baseline, in the standard model.** For every policy submission, every complete
continued-fraction search and every instance with a 2048-bit modulus, the semiclassical
program at `submissionPrecision`, run in `Model.qs` from the all-zero ket, finds the order
with probability at least `99/100 · κ / log 2048`, and that number is positive. This is
`model_policy_submission_correct_semiclassical` composed with the coherent headline
arithmetic `headline_success_bound`; it is the same number the coherent circuit is held to. -/
theorem model_semiclassical_submission_headline (s : ShorPolicySubmission) (T : ℕ → ℕ)
    (hT : ContinuedFractionSearchComplete T) (inst : ShorOrderFindingInstance)
    (hN : Is2048Bit inst.N) :
    (99 / 100 : ℝ) * (κ / Real.log (2048 : ℝ)) ≤
        probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
          (referenceSemiclassicalProgramAt s.policy s.policy_admissible
            submissionPrecision inst).rounds
          (ord inst.a inst.N inst.coprime)
          (2 ^ (referenceSemiclassicalProgramAt s.policy s.policy_admissible
            submissionPrecision inst).rounds)
          ((referenceSemiclassicalProgramAt s.policy s.policy_admissible
              submissionPrecision inst).circuit.eval
            (MState.init (qs.ket (RegEncoding.zero (Basis := qs.Basis))))) ∧
      0 < (99 / 100 : ℝ) * (κ / Real.log (2048 : ℝ)) := by
  refine ⟨(headline_success_bound hN).trans
    (model_policy_submission_correct_semiclassical s T hT inst), ?_⟩
  have hκ := κ_pos
  have hlog : 0 < Real.log (2048 : ℝ) := Real.log_pos (by norm_num)
  positivity

/-- **Non-vacuity, concretely.** There is a complete continued-fraction search `T` such that,
for the standard arity-2 table submitted as a policy and the 2048-bit instance `inst2048`,
the semiclassical certificate's conclusion holds in `Model.qs` with a positive left-hand side:
the declared bound `referenceSuccessProbabilityAt submissionPrecision N` is at least
`99/100 · κ / log 2048 > 0` and the semiclassical program meets it. -/
theorem model_semiclassical_submission_nonvacuous :
    ∃ T : ℕ → ℕ, ContinuedFractionSearchComplete T ∧
      0 < referenceSuccessProbabilityAt submissionPrecision inst2048.N ∧
      referenceSuccessProbabilityAt submissionPrecision inst2048.N ≤
        probability_of_success_M T (fun d => decide ((inst2048.a ^ d) % inst2048.N = 1))
          (referenceSemiclassicalProgramAt
            (ShorPolicySubmission.ofSetup (standardLoweringSetup 2 (by norm_num))).policy
            (ShorPolicySubmission.ofSetup (standardLoweringSetup 2 (by norm_num))).policy_admissible
            submissionPrecision inst2048).rounds
          (ord inst2048.a inst2048.N inst2048.coprime)
          (2 ^ (referenceSemiclassicalProgramAt
            (ShorPolicySubmission.ofSetup (standardLoweringSetup 2 (by norm_num))).policy
            (ShorPolicySubmission.ofSetup (standardLoweringSetup 2 (by norm_num))).policy_admissible
            submissionPrecision inst2048).rounds)
          ((referenceSemiclassicalProgramAt
              (ShorPolicySubmission.ofSetup (standardLoweringSetup 2 (by norm_num))).policy
              (ShorPolicySubmission.ofSetup (standardLoweringSetup 2 (by norm_num))).policy_admissible
              submissionPrecision inst2048).circuit.eval
            (MState.init (qs.ket (RegEncoding.zero (Basis := qs.Basis))))) := by
  obtain ⟨T, hT⟩ := exists_continuedFractionSearchComplete
  refine ⟨T, hT, ?_, model_policy_submission_correct_semiclassical _ T hT inst2048⟩
  obtain ⟨-, hpos⟩ := model_semiclassical_submission_headline
    (ShorPolicySubmission.ofSetup (standardLoweringSetup 2 (by norm_num))) T hT inst2048
    inst2048_is2048Bit
  exact hpos.trans_le (headline_success_bound inst2048_is2048Bit)

end Model
end Shor

/-! ## Axiom checks -/

#print axioms Shor.policy_submission_correct_semiclassical
#print axioms Shor.submission_correct_semiclassical
#print axioms Shor.policy_submission_correct_semiclassical_balanced
#print axioms Shor.policy_submission_correct_semiclassical_balancedU
#print axioms Shor.policy_submissionSuccessBound_le_success_semiclassical
#print axioms Shor.Readout.referenceSemiclassicalProgramAt_success
#print axioms Shor.Readout.balancedSemiclassicalProgramAt_success
#print axioms Shor.Readout.balancedUSemiclassicalProgramAt_success
#print axioms Shor.Model.model_policy_submission_correct_semiclassical
#print axioms Shor.Model.exists_continuedFractionSearchComplete
#print axioms Shor.Model.model_semiclassical_submission_headline
#print axioms Shor.Model.model_semiclassical_submission_nonvacuous
