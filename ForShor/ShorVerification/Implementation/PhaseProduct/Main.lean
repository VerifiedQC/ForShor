import ForShor.ShorVerification.Implementation.PhaseProduct.Statement
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Lowering.Lower
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Spec.Cleanliness
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Lowering.Correctness
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.GateCount.Lemmas
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.GateCount.Policy

/-!
# Phase-Product Main Theorems

This module proves the public assertions for the phase-product implementation.
All supporting lemmas are kept under `PhaseProduct.Proofs`.
-/

namespace Shor
open Gate
open Operations

/-- Main signed phase-product lowering theorem, packaged as the public assertion. -/
theorem lowerSignedPhaseProduct_correct
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (k : ℕ)
    (hk : 1 < k)
    (phi : Angle)
    (x z : ExtReg)
    (ops : Prog k) :
    LowerSignedPhaseProductCorrect qs k hk phi x z ops := by
  intro ψ pts hpts hworkspace hInterp hC hRun
  let plan :
      StandardPhaseLoweringPlan k hk pts hpts ops (phaseInputSize x z) (Gate.SignedPhaseProd phi x z) :=
    standardSignedPhaseLoweringPlan k hk phi x z ops pts hpts
  have hready : PhaseLoweringReady qs plan ψ := by
    simpa [plan] using
      standardSignedPhaseLoweringPlan_ready_of_workspace qs k hk phi x z ops ψ
        (pts := pts) (hpts := hpts) hworkspace hInterp hC hRun
  have hcorrect :=
    evalL_lowerSignedPhaseProd_of_plan
      (qs := qs) (k := k) (hk := hk) (phi := phi) (x := x) (z := z) (ops := ops)
      (pts := pts) (hpts := hpts) (plan := plan)
      (ψ := ψ) (hready := hready) (hInterp := hInterp) (hC := hC) (hRun := hRun)
  simpa [lowerSignedPhaseProd, plan] using hcorrect

/-- Main controlled signed phase-product lowering theorem, packaged as the public assertion. -/
theorem lowerCSignedPhaseProduct_correct
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (k : ℕ)
    (hk : 1 < k)
    (ctrl : ℕ)
    (phi : Angle)
    (x z : ExtReg)
    (ops : Prog k) :
    LowerCSignedPhaseProductCorrect qs k hk ctrl phi x z ops := by
  intro ψ pts hpts hworkspace hInterp hC hRun
  let plan :
      StandardPhaseLoweringPlan k hk pts hpts ops (phaseInputSize x z)
        (Gate.CSignedPhaseProd ctrl phi x z) :=
    standardCSignedPhaseLoweringPlan k hk ctrl phi x z ops pts hpts
  have hready : PhaseLoweringReady qs plan ψ := by
    simpa [plan] using
      standardCSignedPhaseLoweringPlan_ready_of_workspace
        qs k hk ctrl phi x z ops ψ (pts := pts) (hpts := hpts) hworkspace hInterp hC hRun
  have hcorrect :=
    evalL_lowerGateRec_correct (qs := qs)
      (ShorLoweringPolicy.constPolicy_admissible (T := ⟨k, hk, pts, hpts, ops⟩)
        ⟨hInterp, hC, hRun⟩) plan ψ hready
  simpa [lowerCSignedPhaseProd, plan] using hcorrect

/-! =========================================================
    The policy forms

    The claim a policy submission receives. The fixed-table theorems above
    are the same statements at the constant policy.
========================================================= -/

/-- Main signed phase-product lowering theorem under a policy. -/
theorem Policy.lowerSignedPhaseProduct_correct
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (P : ShorLoweringPolicy)
    (phi : Angle)
    (x z : ExtReg) :
    Policy.LowerSignedPhaseProductCorrect qs P phi x z := by
  intro ψ hworkspace hP
  have hready : PhaseLoweringReady qs (Policy.signedPlan P phi x z) ψ :=
    Policy.signedPlan_ready qs P hP phi x z ψ hworkspace.static hworkspace.clean
  exact evalL_lowerGateRec_correct (qs := qs) hP (Policy.signedPlan P phi x z)
    ψ hready

/-- Main controlled signed phase-product lowering theorem under a policy. -/
theorem Policy.lowerCSignedPhaseProduct_correct
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (P : ShorLoweringPolicy)
    (ctrl : ℕ)
    (phi : Angle)
    (x z : ExtReg) :
    Policy.LowerCSignedPhaseProductCorrect qs P ctrl phi x z := by
  intro ψ hworkspace hP
  have hready :
      PhaseLoweringReady qs (Policy.cSignedPlan P ctrl phi x z) ψ :=
    Policy.cSignedPlan_ready qs P hP ctrl phi x z ψ hworkspace.static hworkspace.clean
  exact evalL_lowerGateRec_correct (qs := qs) hP
    (Policy.cSignedPlan P ctrl phi x z) ψ hready

/-! =========================================================
    Gate count
========================================================= -/

/-- **The signed phase-product gate count** for a table satisfying C1–C4:
above some width, at most a constant times `n^(log_k (2k - 1))`.
(`SignedPhaseProductGateCountBoundOfProgramOK`.) -/
theorem signedPhaseProductGateCountBound_of_programOK
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (pts : List Point)
    (hpts : pts.length = q k) :
    SignedPhaseProductGateCountBoundOfProgramOK (Basis := Basis) k hk ops pts hpts := by
  intro hops
  obtain ⟨C', hC', n₀, hn₀, hshift⟩ :=
    signedPhaseProductGateCount_shifted_bound_of_programOK (Basis := Basis) k hk ops pts hpts hops
  refine ⟨C', hC', n₀ + 1, by omega, ?_⟩
  intro φ x z hws hx hz
  dsimp only
  intro hn
  have hb := hshift φ x z (ExtReg.width x - 1) (ExtReg.width z - 1) (by omega) (by omega) hws
    (by omega)
  have hexp : 0 ≤ Real.log (q k : ℝ) / Real.log (k : ℝ) :=
    le_of_lt (lt_trans zero_lt_one (one_lt_phaseProductExponent k hk))
  have hmono :
      Real.rpow ((max (ExtReg.width x - 1) (ExtReg.width z - 1) : ℕ) : ℝ)
          (phaseProductExponent k)
        ≤ Real.rpow ((max (ExtReg.width x) (ExtReg.width z) : ℕ) : ℝ)
          (Real.log (q k : ℝ) / Real.log (k : ℝ)) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast (by omega)) hexp
  exact hb.trans (mul_le_mul_of_nonneg_left hmono hC'.le)

/-- **The controlled signed phase-product gate count**: at most five times the
uncontrolled count, so the same rate.
(`CSignedPhaseProductGateCountBoundOfProgramOK`.) -/
theorem cSignedPhaseProductGateCountBound_of_programOK
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (pts : List Point)
    (hpts : pts.length = q k) :
    CSignedPhaseProductGateCountBoundOfProgramOK (Basis := Basis) k hk ops pts hpts := by
  intro hops
  obtain ⟨C, hC, n₀, hn₀, hbound⟩ :=
    signedPhaseProductGateCountBound_of_programOK (Basis := Basis) k hk ops pts hpts hops
  refine ⟨5 * C, by positivity, n₀, hn₀, ?_⟩
  intro ctrl φ x z hws hx hz
  dsimp only
  intro hn
  have hb := hbound φ x z hws.toSignedRecursiveWorkspaceOK hx hz hn
  have h5 : (cSignedPhaseProductGateCount (Basis := Basis) k hk ops pts hpts ctrl φ x z : ℝ)
      ≤ 5 * (signedPhaseProductGateCount (Basis := Basis) k hk ops pts hpts φ x z : ℝ) := by
    exact_mod_cast CPhaseProductReduction.cSignedPhaseProductGateCount_le_five_signed
      (Basis := Basis) k hk ops pts hpts ctrl φ x z hws
  calc _ ≤ 5 * (signedPhaseProductGateCount (Basis := Basis) k hk ops pts hpts φ x z : ℝ) := h5
    _ ≤ 5 * (C * Real.rpow ((max (ExtReg.width x) (ExtReg.width z) : ℕ) : ℝ)
          (Real.log (q k : ℝ) / Real.log (k : ℝ))) :=
        mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = _ := by ring

/-! =========================================================
    Gate count under a policy
========================================================= -/

/-- **The signed phase-product gate count under a policy.**
(`Policy.SignedPhaseProductGateCountBound`.) -/
theorem Policy.signedPhaseProductGateCountBound (P : ShorLoweringPolicy) :
    Policy.SignedPhaseProductGateCountBound P := by
  intro hP
  obtain ⟨C, hC, n₀, hn₀, hbound⟩ :=
    Policy.signedPhaseProductGateCountFor_gateExponent_bound P.negation P hP
  exact ⟨C, hC, n₀, hn₀, fun φ x z hws hn => hbound φ x z hws hn⟩

/-- **The controlled signed phase-product gate count under a policy**: at most
five times the uncontrolled count, so the same rate.
(`Policy.CSignedPhaseProductGateCountBound`.) -/
theorem Policy.cSignedPhaseProductGateCountBound (P : ShorLoweringPolicy) :
    Policy.CSignedPhaseProductGateCountBound P := by
  intro hP
  obtain ⟨C, hC, n₀, hn₀, hbound⟩ :=
    Policy.signedPhaseProductGateCountFor_gateExponent_bound P.negation P hP
  refine ⟨5 * C, by positivity, n₀, hn₀, ?_⟩
  intro ctrl φ x z hws
  dsimp only
  intro hn
  have hb5 := hbound φ x z hws.toWorkspaceOK hn
  have h5 : (Policy.cSignedPhaseProductGateCount P ctrl φ x z : ℝ)
      ≤ 5 * (Policy.signedPhaseProductGateCountFor P.negation P φ x z : ℝ) := by
    exact_mod_cast Policy.cSignedPhaseProductGateCountFor_le_five_signed P.negation P ctrl φ x z hws
  calc _ ≤ 5 * (Policy.signedPhaseProductGateCountFor P.negation P φ x z : ℝ) := h5
    _ ≤ 5 * (C * Real.rpow ((max (ExtReg.width x) (ExtReg.width z) : ℕ) : ℝ) P.gateExponent) :=
        mul_le_mul_of_nonneg_left hb5 (by norm_num)
    _ = _ := by ring

end Shor
