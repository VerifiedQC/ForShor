import ForShor.ShorVerification.Model.Standard.LowGates
import ForShor.ShorVerification.Implementation.Shor.Main
import ForShor.ShorVerification.Implementation.GateCount.Shor_GateCount
import ForShor.ShorVerification.Submission.Correct

/-!
# The headline theorems, specialised to the model

The point of the whole folder.

Every headline theorem in the development is stated over a stack of typeclass
parameters — `qs : QSemantics`, `[RegEncoding qs.Basis]`, `[MeasureClass qs]`,
`[GateSemanticsFacts qs]`, `[LowerGateClass qs]`,
`[IdealCtrlModMulExactSemantics qs]` — and nothing outside this folder
instantiates any of them. `#print axioms` cannot see that: if one law were
contradictory, every theorem would hold vacuously and the axiom check would
still report only `propext`, `Classical.choice` and `Quot.sound`.

The declarations below are the acceptance test. They fail to elaborate unless
every instance resolves at `Model.qs`, so the development is known to be about
something.

This is the one file in `Model/` that reaches into `Implementation/` and
`Submission/`. Nothing outside `Model/` may import anything in it.
-/

namespace Shor
namespace Model

/-! ## Correctness of the fully lowered approximate circuit -/

theorem model_Shor_correct_approx_lowered
    (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T) :
    ShorCorrectApproxLowered (qs := qs) T hT :=
  Shor_correct_approx_lowered (qs := qs) T hT

/-! ## The `O(n^(2+ε))` gate-count bounds -/

theorem model_exists_shorGateCountBound (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, ∃ hk : 1 < k, ∃ ops : Prog k,
      PhaseProductProgramOK k hk
          (genInterpolationPoints k) (generatedInterpolationPoints_length k) ops ∧
        ShorGateCountBound qs ε k hk ops
          (genInterpolationPoints k) (generatedInterpolationPoints_length k) :=
  exists_shorGateCountBound qs ε hε

theorem model_shorGateCountBound_of_setup
    (s : ShorLoweringSetup) (ε : ℝ) (hExponent : phaseProductExponent s.k ≤ 1 + ε) :
    ShorGateCountBound qs ε s.k s.hk s.ops s.pts s.hpts :=
  shorGateCountBound_of_setup qs s ε hExponent

/-! ## The submission certificates -/

example (s : ShorSubmission) := submission_correct (qs := qs) s

example (s : ShorPolicySubmission) := policy_submission_correct (qs := qs) s

/-!
## Axioms

```
#print axioms model_Shor_correct_approx_lowered
-- 'Shor.Model.model_Shor_correct_approx_lowered' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
```
-/

end Model
end Shor
