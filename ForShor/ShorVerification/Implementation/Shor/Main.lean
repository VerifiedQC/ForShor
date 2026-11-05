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
table admits `ε ≥ log 3 / log 2 - 1 ≈ 0.585`, larger `k` smaller `ε`. -/
theorem shorGateCountBound_of_setup
    (s : ShorLoweringSetup)
    (ε : ℝ)
    (hExponent : Real.log (q s.k : ℝ) / Real.log (s.k : ℝ) ≤ 1 + ε) :
    ShorGateCountBound qs ε s.k s.hk s.ops s.pts s.hpts :=
  shorGateCountBound_of_programOK
    qs ε s.k s.hk hExponent s.ops s.pts s.hpts s.programOK

/-- **The gate count of the circuit whose correctness is proved**: at the
precision `shorPrecision N x` of `ShorCorrectApproxLowered`, for any submitted
table whose exponent `log_k (2k - 1)` is at most `1 + ε`, the lowered
order-finding circuit has `O(n^(2 + ε))` gates. -/
theorem shorGateCountBoundAtShorPrecision_of_setup
    (s : ShorLoweringSetup)
    (ε : ℝ)
    (hExponent : Real.log (q s.k : ℝ) / Real.log (s.k : ℝ) ≤ 1 + ε) :
    ShorGateCountBoundAtShorPrecision qs ε s.k s.hk s.ops s.pts s.hpts :=
  shorGateCountBoundAtShorPrecision_of_bound qs ε s.k s.hk s.ops s.pts s.hpts
    (shorGateCountBound_of_setup qs s ε hExponent)

/-- **For every `ε > 0` there is an arity `k`** such that every program
satisfying C1–C4 at that arity gives the `O(n^(2 + ε))` bound. -/
theorem exists_k_shorGateCountBound_of_programOK
    (ε : ℝ)
    (hε : 0 < ε) :
    ∃ (k : ℕ) (hk : 1 < k),
      ∀ (ops : Prog k) (pts : List Point) (hpts : pts.length = q k),
        PhaseProductProgramOK k hk pts hpts ops →
        ShorGateCountBound qs ε k hk ops pts hpts := by
  rcases exists_k_phaseProductExponent_le ε hε with ⟨k, hk, hExponent⟩
  exact ⟨k, hk, shorGateCountBound_of_programOK qs ε k hk hExponent⟩

/-- **For every `ε > 0`, a generated table at some arity** gives the
`O(n^(2 + ε))` bound. -/
theorem exists_shorGateCountBound
    (ε : ℝ)
    (hε : 0 < ε) :
    ∃ k : ℕ,
    ∃ hk : 1 < k,
    ∃ ops : Prog k,
      PhaseProductProgramOK k hk
          (genInterpolationPoints k) (generatedInterpolationPoints_length k) ops ∧
      ShorGateCountBound qs ε k hk ops
        (genInterpolationPoints k) (generatedInterpolationPoints_length k) := by
  rcases exists_k_phaseProductExponent_le ε hε with ⟨k, hk, hExponent⟩
  rcases exists_phaseProductProgramOK k hk with ⟨ops, hops⟩
  exact ⟨k, hk, ops, hops,
    shorGateCountBound_of_programOK qs ε k hk hExponent ops
      (genInterpolationPoints k) (generatedInterpolationPoints_length k) hops⟩

end GateCount

end Shor
