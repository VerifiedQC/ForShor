import ForShor.ShorVerification.Implementation.Shor.Statement
import ForShor.ShorVerification.Implementation.Shor.Proofs.Correctness
import ForShor.ShorVerification.Implementation.Shor.Proofs.Workspace
import ForShor.ShorVerification.Implementation.Shor.Proofs.GateCount

/-!
# Shor Main Theorems

The Shor theorems, each typed by its named proposition from `Statement.lean`
and proven here: correctness of the lowered circuit, and its `O(n^(2 + ε))`
gate count. All supporting lemmas live under `Shor.Proofs`.
-/

namespace Shor

variable {qs : QSemantics}
variable [RegEncoding qs.Basis]
variable [MeasureClass qs]

/--
Correctness of the fully lowered approximate Shor order-finding circuit.
-/
theorem Shor_correct_approx_lowered_uniform
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T) :
    ShorCorrectApproxLoweredUniform T hT := by
  refine ⟨1600, by norm_num, le_refl _, ?_⟩
  intro inst P hP x y work scratch flag b0 hm hn η hready _hws
  exact Shor_correct_approx_lowered_of_modExp_bound (qs := qs) 1600
    (modExpApprox_valid_dist_1600 (qs := qs)) T hT
    inst P hP x y work scratch flag b0 hm hn η hready

/--
Correctness of the fully lowered approximate Shor order-finding circuit at a
precision chosen from `N`.
-/
theorem Shor_correct_approx_lowered
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T) :
    ShorCorrectApproxLowered T hT :=
  Shor_correct_approx_lowered_at_shorPrecision T hT

/-! =========================================================
    Gate count
========================================================= -/

section GateCount
open Operations

variable (qs : QSemantics) [RegEncoding qs.Basis]

/-- **The `O(n^(2 + ε))` gate count for an arbitrary submitted table.** The
hypotheses are the submission conditions (a `ShorLoweringSetup` carries C1–C4)
and that the table's exponent `log_k (2k - 1)` is at most `1 + ε`: a `k = 2`
table admits `ε ≥ log 3 / log 2 - 1 ≈ 0.585`, larger `k` smaller `ε`.
(`ShorGateCountBoundOfSetup`.) -/
theorem shorGateCountBound_of_setup
    (s : ShorLoweringSetup)
    (ε : ℝ) :
    ShorGateCountBoundOfSetup qs s ε :=
  fun hExponent =>
    shorGateCountBound_of_programOK
      qs ε s.k s.hk hExponent s.ops s.pts s.hpts s.programOK

/-- **The gate count of the circuit whose correctness is proved**: at the
precision `shorPrecision N x` of `ShorCorrectApproxLowered`, for any submitted
table whose exponent `log_k (2k - 1)` is at most `1 + ε`, the lowered
order-finding circuit has `O(n^(2 + ε))` gates.
(`ShorGateCountBoundAtShorPrecisionOfSetup`.) -/
theorem shorGateCountBoundAtShorPrecision_of_setup
    (s : ShorLoweringSetup)
    (ε : ℝ) :
    ShorGateCountBoundAtShorPrecisionOfSetup qs s ε :=
  fun hExponent =>
    shorGateCountBoundAtShorPrecision_of_bound qs ε s.k s.hk s.ops s.pts s.hpts
      (shorGateCountBound_of_setup qs s ε hExponent)

/-- **For every `ε > 0` there is an arity `k`** such that every program
satisfying C1–C4 at that arity gives the `O(n^(2 + ε))` bound.
(`ExistsKShorGateCountBoundOfProgramOK`.) -/
theorem exists_k_shorGateCountBound_of_programOK
    (ε : ℝ) :
    ExistsKShorGateCountBoundOfProgramOK qs ε := by
  intro hε
  rcases exists_k_phaseProductExponent_le ε hε with ⟨k, hk, hExponent⟩
  exact ⟨k, hk, shorGateCountBound_of_programOK qs ε k hk hExponent⟩

/-- **For every `ε > 0`, some table satisfying C1–C4** gives the
`O(n^(2 + ε))` bound. (`ExistsShorGateCountBound`.) -/
theorem exists_shorGateCountBound
    (ε : ℝ) :
    ExistsShorGateCountBound qs ε := by
  intro hε
  obtain ⟨k, hk, ops, hops, hbound⟩ := exists_shorGateCountBound_generated qs ε hε
  exact ⟨k, hk, ops, _, _, hops, hbound⟩

/-- **The `O(n^(2 + ε))` gate count under a policy.** (`Policy.ShorGateCountBound`.) -/
theorem Policy.shorGateCountBound (ε : ℝ) (P : ShorLoweringPolicy) :
    Policy.ShorGateCountBound qs ε P :=
  fun hP hExponent => Policy.shorGateCountBoundFor_of_admissible P.negation qs ε P hP hExponent

/-- **The gate count of the circuit whose correctness is proved, under a
policy.** (`Policy.ShorGateCountBoundAtShorPrecision`.) -/
theorem Policy.shorGateCountBoundAtShorPrecision (ε : ℝ) (P : ShorLoweringPolicy) :
    Policy.ShorGateCountBoundAtShorPrecision qs ε P :=
  fun hP hExponent =>
    Policy.shorGateCountBoundAtShorPrecisionFor_of_bound P.negation qs ε P
      (Policy.shorGateCountBoundFor_of_admissible P.negation qs ε P hP hExponent)

end GateCount

end Shor
