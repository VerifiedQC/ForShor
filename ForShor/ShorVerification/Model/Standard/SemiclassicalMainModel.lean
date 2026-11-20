import ForShor.ShorVerification.Model.Standard.SemiclassicalLoweredModel
import ForShor.ShorVerification.Implementation.Readout.BalancedShor
import ForShor.ShorVerification.Implementation.Reference.Balanced.Main

/-!
# Semiclassical order finding in the standard model: success AND peak, on one circuit

For each of the three lowerings of the real semiclassical circuit (plain `lowerM`,
balanced `lowerMBalanced P R`, every site split `lowerMBalancedU P R`), one theorem at
`Model.qs` conjoins, for the SAME lowered circuit term at the SAME reference layout
(`allocateReferenceLayout P inst ℓ`, control `referenceControl P inst ℓ` = the first
exponent qubit, `m = regSize x.active = log₂(2N²)` rounds, all-zero start ket):

* `referencePrecision ℓ ≤ shorPrecision N x` (the precision the success theorem needs);
* the success probability of that program, run by `MLowGate.eval`, is at least
  `κ / (2 log(log₂ N + 1))`;
* its proved peak (`MLowGate.peakQubitsFor P.negation` from `orderFindingBaseSetSC`) is
  exactly the formula of `Cost.lean` (`Policy.orderFindingQubitsSC`, `…BalancedSC`, `…USC`);
* the bound is positive.

The layout is existentially quantified through the level `ℓ` (the layout is
`allocateReferenceLayout P inst ℓ`); it holds for every admissible policy and instance
(for every rule `R` in the balanced case; for every rule the reference layout fits,
`Balanced.ReferenceFits P R`, in the `U` case, e.g. `Balanced.defaultRule`).

## Scope (as in the parts)

* The feed-forward phases are the exact `LowGate.Phase c (ffAngle j r)` (ρ = 0).
* The reference register `x` is a ghost: the circuit never touches it except through
  the control `c = x.active[0]`; it fixes `m` and serves the comparison with the
  textbook circuit.
* The peak is the walk of `Readout/Lowering.lean`: `LowGate.Phase` is a primitive with
  zero scratch (rotation-synthesis ancillas are not modelled), negation scratch is counted
  as a number, and the lowered QFT and phase-product blocks of the multipliers are counted by the existing
  proved walk exactly as in the coherent circuit (`QubitCount.lower_walk` via `qft_block` /
  `signed_block` / `csigned_block`): every named qubit they touch is counted in
  `semiclassical_peak_formula`, and their scratch is counted as a number. What is not proved
  is a syntactic list of the names those blocks reach (`MGate.qftPhaseReach`), which the qubit
  count does not need. Negation scratch and rotation-synthesis ancillas are counted as numbers
  or not modelled.
-/

namespace Shor
namespace Model

open Reference Readout

-- `RL` abbreviates the reference layout `allocateReferenceLayout P inst ℓ`.
set_option hygiene false in
local notation "RL" => allocateReferenceLayout P inst ℓ

/-- The semiclassical circuit at the reference layout fits a rule the reference layout
fits (`Balanced.ReferenceFits`), for every number of rounds, on the setup's workspace fields:
`Readout.referenceSemiclassicalFits` (`Readout/Proofs/ReferenceLayout.lean`). -/
theorem referenceSemiclassicalFits (P : ShorLoweringPolicy) (R : Balanced.Rule)
    (hfits : Balanced.ReferenceFits P R) (inst : ShorOrderFindingInstance) (ℓ m : ℕ) :
    MGate.Fits P R (orderFindingSemiclassical inst.a inst.N (referenceControl P inst ℓ) m
      (RL).data (RL).work (RL).scratch (RL).flag
      (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
      (referenceSemiclassicalSetup P inst ℓ).step4_workspace) :=
  Readout.referenceSemiclassicalFits P R hfits inst ℓ m

/-- **Plain lowering: success and peak of one circuit, in the model.** -/
theorem model_semiclassical_lowered_success_and_peak (P : ShorLoweringPolicy) (hP : P.Admissible)
    (inst : ShorOrderFindingInstance) (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T) :
    ∃ ℓ : ℕ, referencePrecision ℓ ≤ shorPrecision inst.N (RL).x.active ∧
      probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
          (regSize (RL).x.active) (ord inst.a inst.N inst.coprime) (ASize (RL).x.active)
          ((orderFindingSemiclassicalLow P inst.a inst.N (referenceControl P inst ℓ)
              (regSize (RL).x.active) (RL).data (RL).work (RL).scratch (RL).flag
              (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
              (referenceSemiclassicalSetup P inst ℓ).step4_workspace
              (referenceSemiclassicalWorkspaceOK P inst ℓ _)).eval
            (MState.init (qs.ket RegEncoding.zero)))
        ≥ κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1)) ∧
      (orderFindingSemiclassicalLow P inst.a inst.N (referenceControl P inst ℓ)
          (regSize (RL).x.active) (RL).data (RL).work (RL).scratch (RL).flag
          (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
          (referenceSemiclassicalSetup P inst ℓ).step4_workspace
          (referenceSemiclassicalWorkspaceOK P inst ℓ _)).peakQubitsFor P.negation
          (orderFindingBaseSetSC (referenceControl P inst ℓ) (RL).data (RL).work (RL).scratch
            (RL).flag)
        = Policy.orderFindingQubitsSC P (referenceDataWidth inst) (referenceWorkWidth inst ℓ)
            (referenceScratchWidth inst ℓ) ∧
      0 < κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1)) := by
  obtain ⟨ℓ, hprec, hsucc, hpos⟩ :=
    model_Shor_correct_semiclassical_lowered_at_shorPrecision P hP inst T hT
  refine ⟨ℓ, hprec, hsucc, ?_, hpos⟩
  rw [semiclassical_peak_formula P hP _ _ _ _ _ _ _ _ _ _ _
    (referenceSemiclassicalSetup P inst ℓ).layout (referenceX_pos P inst ℓ), referenceLayout_data_width',
    referenceLayout_work_width', referenceLayout_scratch_width']

/-- **Balanced lowering: success and peak of one circuit, in the model**, for every rule. -/
theorem model_semiclassical_lowered_balanced_success_and_peak (P : ShorLoweringPolicy)
    (hP : P.Admissible) (R : Balanced.Rule) (inst : ShorOrderFindingInstance) (T : ℕ → ℕ)
    (hT : ContinuedFractionSearchComplete T) :
    ∃ ℓ : ℕ, referencePrecision ℓ ≤ shorPrecision inst.N (RL).x.active ∧
      probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
          (regSize (RL).x.active) (ord inst.a inst.N inst.coprime) (ASize (RL).x.active)
          ((orderFindingSemiclassicalLowBalanced P R inst.a inst.N (referenceControl P inst ℓ)
              (regSize (RL).x.active) (RL).data (RL).work (RL).scratch (RL).flag
              (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
              (referenceSemiclassicalSetup P inst ℓ).step4_workspace
              (referenceSemiclassicalWorkspaceOK P inst ℓ _)).eval
            (MState.init (qs.ket RegEncoding.zero)))
        ≥ κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1)) ∧
      (orderFindingSemiclassicalLowBalanced P R inst.a inst.N (referenceControl P inst ℓ)
          (regSize (RL).x.active) (RL).data (RL).work (RL).scratch (RL).flag
          (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
          (referenceSemiclassicalSetup P inst ℓ).step4_workspace
          (referenceSemiclassicalWorkspaceOK P inst ℓ _)).peakQubitsFor P.negation
          (orderFindingBaseSetSC (referenceControl P inst ℓ) (RL).data (RL).work (RL).scratch
            (RL).flag)
        = Policy.orderFindingQubitsBalancedSC P R (referenceDataWidth inst) (RL).data.capacity
            (referenceWorkWidth inst ℓ) (RL).work.capacity
            (referenceScratchWidth inst ℓ) (RL).scratch.capacity ∧
      0 < κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1)) := by
  obtain ⟨ℓ, hprec, -, hpos⟩ := model_Shor_correct_semiclassical_at_shorPrecision P inst T hT
  refine ⟨ℓ, hprec, ?_, ?_, hpos⟩
  · exact Shor_correct_semiclassical_lowered_balanced_at_shorPrecision R T hT inst P hP _ _ _ _ _ _
      _ (allocateReferenceLayout_x_width P inst ℓ) (allocateReferenceLayout_data_width P inst ℓ) _
      hprec (referenceSemiclassicalSetup P inst ℓ) (referenceSemiclassicalCleanInput P inst ℓ) _
  · rw [semiclassical_peak_formula_balanced P R hP _ _ _ _ _ _ _ _ _ _ _
      (referenceSemiclassicalSetup P inst ℓ).layout (referenceX_pos P inst ℓ), referenceLayout_data_width',
    referenceLayout_work_width', referenceLayout_scratch_width']

/-- **Every site split: success and peak of one circuit, in the model**, for every rule
the reference layout fits (`Balanced.ReferenceFits P R`). -/
theorem model_semiclassical_lowered_balancedU_success_and_peak (P : ShorLoweringPolicy)
    (hP : P.Admissible) (R : Balanced.Rule) (hfits : Balanced.ReferenceFits P R)
    (inst : ShorOrderFindingInstance) (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T) :
    ∃ ℓ : ℕ, referencePrecision ℓ ≤ shorPrecision inst.N (RL).x.active ∧
      probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
          (regSize (RL).x.active) (ord inst.a inst.N inst.coprime) (ASize (RL).x.active)
          ((orderFindingSemiclassicalLowBalancedU P R inst.a inst.N (referenceControl P inst ℓ)
              (regSize (RL).x.active) (RL).data (RL).work (RL).scratch (RL).flag
              (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
              (referenceSemiclassicalSetup P inst ℓ).step4_workspace
              (referenceSemiclassicalWorkspaceOK P inst ℓ _)
              (referenceSemiclassicalFits P R hfits inst ℓ _)).eval
            (MState.init (qs.ket RegEncoding.zero)))
        ≥ κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1)) ∧
      (orderFindingSemiclassicalLowBalancedU P R inst.a inst.N (referenceControl P inst ℓ)
          (regSize (RL).x.active) (RL).data (RL).work (RL).scratch (RL).flag
          (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
          (referenceSemiclassicalSetup P inst ℓ).step4_workspace
          (referenceSemiclassicalWorkspaceOK P inst ℓ _)
          (referenceSemiclassicalFits P R hfits inst ℓ _)).peakQubitsFor P.negation
          (orderFindingBaseSetSC (referenceControl P inst ℓ) (RL).data (RL).work (RL).scratch
            (RL).flag)
        = Policy.orderFindingQubitsUSC P R (referenceDataWidth inst) (referenceWorkWidth inst ℓ)
            (referenceScratchWidth inst ℓ) ∧
      0 < κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1)) := by
  obtain ⟨ℓ, hprec, -, hpos⟩ := model_Shor_correct_semiclassical_at_shorPrecision P inst T hT
  refine ⟨ℓ, hprec, ?_, ?_, hpos⟩
  · exact Shor_correct_semiclassical_lowered_balancedU_at_shorPrecision R T hT inst P hP _ _ _ _ _ _
      _ (allocateReferenceLayout_x_width P inst ℓ) (allocateReferenceLayout_data_width P inst ℓ) _
      hprec (referenceSemiclassicalSetup P inst ℓ) (referenceSemiclassicalCleanInput P inst ℓ) _ _
  · rw [semiclassical_peak_formula_balanced_u P R hP _ _ _ _ _ _ _ _ _ _ _ _
      (referenceSemiclassicalSetup P inst ℓ).layout (referenceX_pos P inst ℓ), referenceLayout_data_width',
    referenceLayout_work_width', referenceLayout_scratch_width']

/-- The `U` statement at the default rule (which every reference layout fits,
`Balanced.referenceFits_default`): the configuration of `Balanced.balancedUShorImplementation`. -/
theorem model_semiclassical_lowered_balancedU_default_success_and_peak (P : ShorLoweringPolicy)
    (hP : P.Admissible) (inst : ShorOrderFindingInstance) (T : ℕ → ℕ)
    (hT : ContinuedFractionSearchComplete T) :
    ∃ ℓ : ℕ, referencePrecision ℓ ≤ shorPrecision inst.N (RL).x.active ∧
      probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
          (regSize (RL).x.active) (ord inst.a inst.N inst.coprime) (ASize (RL).x.active)
          ((orderFindingSemiclassicalLowBalancedU P Balanced.defaultRule inst.a inst.N
              (referenceControl P inst ℓ)
              (regSize (RL).x.active) (RL).data (RL).work (RL).scratch (RL).flag
              (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
              (referenceSemiclassicalSetup P inst ℓ).step4_workspace
              (referenceSemiclassicalWorkspaceOK P inst ℓ _)
              (referenceSemiclassicalFits P _ (Balanced.referenceFits_default P) inst ℓ _)).eval
            (MState.init (qs.ket RegEncoding.zero)))
        ≥ κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1)) ∧
      (orderFindingSemiclassicalLowBalancedU P Balanced.defaultRule inst.a inst.N
          (referenceControl P inst ℓ)
          (regSize (RL).x.active) (RL).data (RL).work (RL).scratch (RL).flag
          (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
          (referenceSemiclassicalSetup P inst ℓ).step4_workspace
          (referenceSemiclassicalWorkspaceOK P inst ℓ _)
          (referenceSemiclassicalFits P _ (Balanced.referenceFits_default P) inst ℓ _)).peakQubitsFor
          P.negation
          (orderFindingBaseSetSC (referenceControl P inst ℓ) (RL).data (RL).work (RL).scratch
            (RL).flag)
        = Policy.orderFindingQubitsUSC P Balanced.defaultRule (referenceDataWidth inst)
            (referenceWorkWidth inst ℓ) (referenceScratchWidth inst ℓ) ∧
      0 < κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1)) := by
  exact model_semiclassical_lowered_balancedU_success_and_peak P hP _
    (Balanced.referenceFits_default P) inst T hT

end Model
end Shor
