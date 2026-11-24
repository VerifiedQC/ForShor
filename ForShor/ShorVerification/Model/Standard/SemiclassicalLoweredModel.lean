import ForShor.ShorVerification.Model.Standard.SemiclassicalShorModel
import ForShor.ShorVerification.Implementation.Readout.LoweredShor
import ForShor.ShorVerification.Implementation.Readout.Proofs.SemiclassicalHyps

/-!
# The LOWERED semiclassical order finding in the standard model

Non-vacuity of `Shor_correct_semiclassical_lowered_at_shorPrecision` at the concrete
model `Model.qs`: for EVERY admissible lowering policy `P` and order-finding instance,
at the reference layout of `Implementation/Reference/` (all-zero start ket, control
`referenceControl` = the first exponent qubit, `log₂(2N²)` rounds) every hypothesis
holds: the semiclassical setup (`referenceSemiclassicalSetup`), the zero reserves
(from the coherent `allocatedReferenceWorkspaceCleanInput`), and the lowering workspace
(`referenceSemiclassicalWorkspaceOK`, from the coherent `reference_gateWorkspaceOK` by
`semiclassical_hyps_of_coherent`). So:

* `model_semiclassical_lowerM_eval`: there the lowered program evaluates exactly as the
  high-level one, branch by branch;
* `model_Shor_correct_semiclassical_lowered_at_shorPrecision`: some level `ℓ` has
  `η = referencePrecision ℓ ≤ shorPrecision N x`, and there the LOWERED program succeeds
  with probability at least `κ / (2 log(log₂ N + 1))`, a positive number.
-/

namespace Shor
namespace Model

open Reference Readout

/-- **The lowering workspace at the reference layout**, for every number of rounds `m`, on
the setup's workspace fields: `Readout.referenceSemiclassicalWorkspaceOK`
(`Readout/Proofs/ReferenceLayout.lean`). -/
theorem referenceSemiclassicalWorkspaceOK (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (ℓ m : ℕ) :
    MGate.WorkspaceOK P (orderFindingSemiclassical inst.a inst.N (referenceControl P inst ℓ) m
      (allocateReferenceLayout P inst ℓ).data (allocateReferenceLayout P inst ℓ).work
      (allocateReferenceLayout P inst ℓ).scratch (allocateReferenceLayout P inst ℓ).flag
      (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
      (referenceSemiclassicalSetup P inst ℓ).step4_workspace) :=
  Readout.referenceSemiclassicalWorkspaceOK P inst ℓ m

/-- The data, work and scratch reserves of the reference layout are zero in the all-zero
ket. -/
theorem referenceSemiclassicalCleanInput (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (ℓ : ℕ) :
    SemiclassicalWorkspaceCleanInput (allocateReferenceLayout P inst ℓ).data
      (allocateReferenceLayout P inst ℓ).work (allocateReferenceLayout P inst ℓ).scratch
      (RegEncoding.zero (Basis := qs.Basis)) :=
  SemiclassicalWorkspaceCleanInput.of_shor (allocatedReferenceWorkspaceCleanInput (qs := qs) P inst ℓ)

/-- **The lowered program evaluates as the program, in the model**, at the reference
layout, for every admissible policy, instance, level and number of rounds. -/
theorem model_semiclassical_lowerM_eval (P : ShorLoweringPolicy) (hP : P.Admissible)
    (inst : ShorOrderFindingInstance) (ℓ m : ℕ) :
    (orderFindingSemiclassicalLow P inst.a inst.N (referenceControl P inst ℓ) m
        (allocateReferenceLayout P inst ℓ).data (allocateReferenceLayout P inst ℓ).work
        (allocateReferenceLayout P inst ℓ).scratch (allocateReferenceLayout P inst ℓ).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace
        (referenceSemiclassicalWorkspaceOK P inst ℓ m)).eval
        (MState.init (qs.ket RegEncoding.zero))
      = (orderFindingSemiclassical inst.a inst.N (referenceControl P inst ℓ) m
          (allocateReferenceLayout P inst ℓ).data (allocateReferenceLayout P inst ℓ).work
          (allocateReferenceLayout P inst ℓ).scratch (allocateReferenceLayout P inst ℓ).flag
          (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
          (referenceSemiclassicalSetup P inst ℓ).step4_workspace).eval
        (MState.init (qs.ket RegEncoding.zero)) :=
  semiclassical_lowerM_eval hP _ _ _ _ _ _ _ _ _ _ _ (referenceSemiclassicalSetup P inst ℓ).layout _
    (referenceSemiclassicalCleanInput P inst ℓ)
    (referenceSemiclassicalSetup P inst ℓ).clean_input.2.2.2.2.2.1

/-- **The LOWERED program at `shorPrecision`, in the model.** For every admissible policy
and instance there is a level `ℓ` with `referencePrecision ℓ ≤ shorPrecision N x`, and
at it the lowered semiclassical program on the reference layout, run by `MLowGate.eval`
from the all-zero ket, succeeds with probability at least `κ / (2 log(log₂ N + 1))`,
which is positive. -/
theorem model_Shor_correct_semiclassical_lowered_at_shorPrecision (P : ShorLoweringPolicy)
    (hP : P.Admissible) (inst : ShorOrderFindingInstance) (T : ℕ → ℕ)
    (hT : ContinuedFractionSearchComplete T) :
    ∃ ℓ : ℕ, referencePrecision ℓ ≤ shorPrecision inst.N (allocateReferenceLayout P inst ℓ).x.active ∧
      probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
          (regSize (allocateReferenceLayout P inst ℓ).x.active) (ord inst.a inst.N inst.coprime)
          (ASize (allocateReferenceLayout P inst ℓ).x.active)
          ((orderFindingSemiclassicalLow P inst.a inst.N (referenceControl P inst ℓ)
              (regSize (allocateReferenceLayout P inst ℓ).x.active)
              (allocateReferenceLayout P inst ℓ).data (allocateReferenceLayout P inst ℓ).work
              (allocateReferenceLayout P inst ℓ).scratch (allocateReferenceLayout P inst ℓ).flag
              (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
              (referenceSemiclassicalSetup P inst ℓ).step4_workspace
              (referenceSemiclassicalWorkspaceOK P inst ℓ _)).eval
            (MState.init (qs.ket RegEncoding.zero)))
        ≥ κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1)) ∧
      0 < κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1)) := by
  obtain ⟨ℓ, hprec, -, hpos⟩ :=
    model_Shor_correct_semiclassical_at_shorPrecision P inst T hT
  refine ⟨ℓ, hprec, ?_, hpos⟩
  exact Shor_correct_semiclassical_lowered_at_shorPrecision T hT inst P hP _ _ _ _ _ _ _
    (allocateReferenceLayout_x_width P inst ℓ) (allocateReferenceLayout_data_width P inst ℓ) _
    hprec (referenceSemiclassicalSetup P inst ℓ) (referenceSemiclassicalCleanInput P inst ℓ) _

end Model
end Shor
