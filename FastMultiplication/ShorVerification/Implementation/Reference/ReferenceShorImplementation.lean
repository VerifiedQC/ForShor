import FastMultiplication.ShorVerification.Implementation.Reference.ShorProgram
import FastMultiplication.ShorVerification.Implementation.Shor.Main
import FastMultiplication.ShorVerification.Framework.Submission

namespace Shor
namespace Reference

noncomputable section

/-!
# Reference `ShorImplementation`

This file discharges the framework interface for the reference LowGate program:
it packages `referenceShorProg` into a concrete `ShorImplementation` and proves
the construction-free correctness obligation in full.

The correctness proof works as follows.  The framework asks for
`∀ ε > 0, ∃ m, prob(prog inst m) ≥ κ/log⁴N − ε` from the fixed clean-zero
initial state.  We:

* take the single hoisted constant `K` from `Shor_correct_approx_lowered_uniform`
  (it depends only on `qs`, not on the layout);
* pick a precision level `m` with `2·tbits·√(2·K·referencePrecision m) ≤ ε`,
  which is possible because `referencePrecision m = 1/(m+3) → 0`;
* apply the lowered-correctness theorem at the reference layout for level `m`,
  whose readiness is `referenceLayout_ready`, and whose circuit is definitionally
  `referenceShorProg lowering inst m`.

The gate-count field is left as `sorry` for now (per plan); everything else is
proven.
-/

variable {qs : QSemantics}
variable [RegEncoding qs.Basis]
variable [Spec]
variable [ContinuedFractionPost]
variable [MeasureClass qs]
variable [GateSemanticsFacts qs]
variable [LowerGateClass qs]
variable [LowerGateGateBridge qs]
variable [IdealCtrlModMulExactSemantics qs]
variable [ModMulPrimitiveGateSemantics qs]

/-! =========================================================
    Section 1: ε-from-precision packaging
========================================================= -/

/-- The reference error term `2·t·√(2·K·referencePrecision m)` can be driven
below any positive `ε` by choosing a large enough precision level `m`, because
`referencePrecision m = 1/(m+3) → 0`. -/
theorem exists_precision_error_le
    (t : ℕ) (K : ℝ) (hK : 0 ≤ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ,
      2 * (t : ℝ) * Real.sqrt (2 * (K * referencePrecision m)) ≤ ε := by
  have h2t1 : (0 : ℝ) < 2 * (t : ℝ) + 1 := by positivity
  set D : ℝ := ε / (2 * (t : ℝ) + 1) with hD
  have hD_pos : 0 < D := by rw [hD]; positivity
  have hDsq_pos : 0 < D ^ 2 := by positivity
  obtain ⟨m, hm⟩ := exists_nat_ge (2 * K / D ^ 2)
  refine ⟨m, ?_⟩
  have hm3 : (0 : ℝ) < (m : ℝ) + 3 := by positivity
  -- 2·K·referencePrecision m ≤ D²
  have hkey : 2 * (K * referencePrecision m) ≤ D ^ 2 := by
    have hval : 2 * (K * referencePrecision m) = 2 * K / ((m : ℝ) + 3) := by
      unfold referencePrecision; ring
    rw [hval, div_le_iff₀ hm3]
    have hle : 2 * K / D ^ 2 ≤ (m : ℝ) + 3 := le_trans hm (by linarith)
    rw [div_le_iff₀ hDsq_pos] at hle
    nlinarith [hle]
  -- √(2·K·referencePrecision m) ≤ D
  have hsqrt : Real.sqrt (2 * (K * referencePrecision m)) ≤ D := by
    calc Real.sqrt (2 * (K * referencePrecision m))
        ≤ Real.sqrt (D ^ 2) := Real.sqrt_le_sqrt hkey
      _ = D := Real.sqrt_sq hD_pos.le
  calc 2 * (t : ℝ) * Real.sqrt (2 * (K * referencePrecision m))
      ≤ 2 * (t : ℝ) * D :=
        mul_le_mul_of_nonneg_left hsqrt (by positivity)
    _ ≤ ε := by
        rw [hD, mul_div_assoc', div_le_iff₀ h2t1]
        nlinarith [hε]

/-! =========================================================
    Section 2: Correctness of the reference program
========================================================= -/

/-- The reference LowGate program satisfies the framework's construction-free
order-finding correctness obligation. -/
theorem referenceShorProg_correct
    (lowering : ShorLoweringSetup) :
    ShorImplementsOrderFinding (qs := qs) (referenceShorProg (qs := qs) lowering) := by
  intro T hT inst ε hε
  -- one hoisted K for every layout
  obtain ⟨K, hK, hbound⟩ :=
    Shor_correct_approx_lowered_uniform (qs := qs) T hT
  -- pick the precision level that meets the ε target
  obtain ⟨m, hm⟩ :=
    exists_precision_error_le (tbits inst.x.active) K hK hε
  refine ⟨m, ?_⟩
  set η : ℝ := referencePrecision m with hη
  have hη_pos := referencePrecision_pos m
  have hη_half := referencePrecision_lt_half m
  have hready :=
    referenceLayout_ready (qs := qs) lowering inst η hη_pos hη_half
  have hb :=
    hbound
      (allocatedOrderFindingInstance lowering.ops inst η)
      lowering
      (allocateReferenceLayout lowering.ops inst η).work
      (allocateReferenceLayout lowering.ops inst η).flag
      (RegEncoding.zero (Basis := qs.Basis))
      η
      hready
  -- `hb` bounds the probability for exactly `referenceShorProg lowering inst m`
  -- (definitionally the same circuit), with the allocated instance's `a`/`N`/`x`
  -- all definitionally equal to `inst`'s.  Close by the ε-choice.
  simp only [allocatedOrderFindingInstance_a, allocatedOrderFindingInstance_N,
    allocatedOrderFindingInstance_x_active, allocatedOrderFindingInstance_coprime] at hb
  have hgoal :
      probability_of_success (qs := qs) (T := T)
          (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
          (x := inst.x.active) (r := ord inst.a inst.N inst.coprime)
          (Q := ASize inst.x.active) (evalC := LowerGateClass.evalL (qs := qs))
          (C := referenceShorProg (qs := qs) lowering inst m)
          (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis)))
        ≥ κ / (Nat.log2 inst.N : ℝ) ^ 4
          - 2 * (tbits inst.x.active : ℝ) * Real.sqrt (2 * (K * η)) := hb
  have := hgoal
  linarith [hm, hgoal]

/-! =========================================================
    Section 3: The concrete `ShorImplementation`
========================================================= -/

/-- The reference implementation packaged as a framework `ShorImplementation`.

`prog` and `correct` are the fully-proven reference program and its correctness;
the gate-count `gateBound`/`counted` pair is a placeholder pending the concrete
gate-count function (`counted` is the single outstanding `sorry`). -/
noncomputable def referenceShorImplementation
    (lowering : ShorLoweringSetup) :
    ShorImplementation (qs := qs) where
  prog := referenceShorProg (qs := qs) lowering
  correct := referenceShorProg_correct (qs := qs) lowering
  gateBound := fun _ _ => 0
  counted := by
    intro inst m
    sorry

end
end Reference
end Shor
