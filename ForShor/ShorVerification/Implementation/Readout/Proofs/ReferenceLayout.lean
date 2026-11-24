import ForShor.ShorVerification.Implementation.Readout.Proofs.SemiclassicalHyps
import ForShor.ShorVerification.Implementation.Reference.Standard.Proofs.Readiness
import ForShor.ShorVerification.Implementation.Reference.Balanced.Main

/-!
# Readout: the semiclassical circuit at the reference layout (no semantics)

Static facts about `orderFindingSemiclassical` at the reference layout
`Reference.allocateReferenceLayout P inst ℓ` of `Implementation/Reference/`, with the control
`referenceControl P inst ℓ` = the layout's first exponent qubit. Nothing here mentions a
quantum semantics, so both the standard-model checks (`Model/Standard/Semiclassical*Model.lean`)
and the kernel numerals (`Readout/Proofs/PolicyNumeralsSC/`) import this file, and no
`Implementation/` file imports `Model/`.

* `referenceX_pos`, `referenceControl`, `referenceX_qubits_eq`: the exponent register is
  nonempty and starts with the control;
* `referenceLayout_data_width'` (and `work`, `scratch`): the reference widths as `ExtReg.width`;
* `referenceSemiclassicalWorkspaceOK`, `referenceSemiclassicalLayout`: the lowering workspace
  and the semiclassical layout, from the coherent circuit's (`reference_gateWorkspaceOK`) by
  `semiclassical_hyps_of_coherent`;
* `semiclassical_fits_of_coherent` and its reference instance `referenceSemiclassicalFits`:
  the coherent `Balanced.Fits` gives the semiclassical `MGate.Fits`.

The circuit's workspace arguments are the layout's own (`referenceCircuitWorkspace`,
`referenceStep4Workspace`: `reference_modMulCircuitWorkspaceOK`, `reference_step4Workspace`
restated on `allocateReferenceLayout`'s registers). They are, by unfolding, the ones every
reference setup carries (`Reference.referenceApproxSetup`); the model files restate
`referenceSemiclassicalWorkspaceOK` and `referenceSemiclassicalFits` on their setup's
workspace fields as one-line corollaries of the ones here.
-/

namespace Shor
namespace Readout

open Reference

-- `RL` abbreviates the reference layout `allocateReferenceLayout P inst ℓ`.
set_option hygiene false in
local notation "RL" => allocateReferenceLayout P inst ℓ

/-- The reference exponent register is nonempty (`N ≥ 2`). -/
theorem referenceX_pos (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (ℓ : ℕ) :
    0 < regSize (RL).x.active := by
  rw [allocateReferenceLayout_x_width, Nat.log2_eq_log_two]
  have := inst.range
  exact Nat.log_pos Nat.one_lt_two (by nlinarith)

/-- The control qubit: the reference layout's first exponent qubit. -/
def referenceControl (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (ℓ : ℕ) : ℕ :=
  (RL).x.active.get ⟨0, referenceX_pos P inst ℓ⟩

/-- The reference exponent register starts with the control `referenceControl`. -/
theorem referenceX_qubits_eq (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (ℓ : ℕ) :
    (RL).x.active.qubits = referenceControl P inst ℓ :: (RL).x.active.qubits.tail := by
  have key : ∀ (r : Reg) (h : 0 < regSize r), r.qubits = r.get ⟨0, h⟩ :: r.qubits.tail := by
    rintro ⟨l, hnd⟩ h
    cases l with
    | nil => simp [regSize, Reg.width] at h
    | cons q rest => rfl
  exact key _ (referenceX_pos P inst ℓ)

/-- The reference widths, as `ExtReg.width`. -/
theorem referenceLayout_data_width' (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (ℓ : ℕ) : (RL).data.width = referenceDataWidth inst :=
  allocateReferenceLayout_data_width P inst ℓ

/-- The reference widths, as `ExtReg.width`. -/
theorem referenceLayout_work_width' (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (ℓ : ℕ) : (RL).work.width = referenceWorkWidth inst ℓ :=
  allocateReferenceLayout_work_width P inst ℓ

/-- The reference widths, as `ExtReg.width`. -/
theorem referenceLayout_scratch_width' (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (ℓ : ℕ) : (RL).scratch.width = referenceScratchWidth inst ℓ :=
  allocateReferenceLayout_scratch_width P inst ℓ

/-- The coherent order-finding layout facts of the reference layout. -/
theorem referenceOrderFindingSpaceLayout (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (ℓ : ℕ) :
    OrderFindingSpaceLayout (RL).x (RL).data (RL).work (RL).scratch (RL).flag :=
  ⟨reference_exponent_data_disjoint P inst ℓ, reference_exponent_work_disjoint P inst ℓ,
   reference_exponent_scratch_disjoint P inst ℓ, reference_flag_outside_exponent P inst ℓ⟩

/-- The modular multiplier's workspace fact of the reference layout
(`reference_modMulCircuitWorkspaceOK`), stated on the layout's own registers. -/
theorem referenceCircuitWorkspace (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (ℓ : ℕ) : ModMulCircuitWorkspaceOK (RL).data (RL).work :=
  reference_modMulCircuitWorkspaceOK P inst ℓ

/-- The comparator's workspace of the reference layout (`reference_step4Workspace`), stated on
the layout's own registers. -/
def referenceStep4Workspace (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (ℓ : ℕ) :
    CmpLtNWWorkspace inst.N ((RL).data.grow 1) (RL).work (RL).scratch (RL).flag :=
  reference_step4Workspace P inst ℓ

/-- **The lowering workspace at the reference layout**, for every number of rounds `m`:
from the coherent circuit's (`reference_gateWorkspaceOK`) by
`semiclassical_hyps_of_coherent`. -/
theorem referenceSemiclassicalWorkspaceOK (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (ℓ m : ℕ) :
    MGate.WorkspaceOK P (orderFindingSemiclassical inst.a inst.N (referenceControl P inst ℓ) m
      (RL).data (RL).work (RL).scratch (RL).flag
      (referenceCircuitWorkspace P inst ℓ) (referenceStep4Workspace P inst ℓ)) :=
  (semiclassical_hyps_of_coherent (referenceX_qubits_eq P inst ℓ)
    (reference_gateWorkspaceOK P inst ℓ) (referenceOrderFindingSpaceLayout P inst ℓ)).1 m

/-- **The semiclassical layout at the reference layout** (the control lies outside the data,
work and scratch registers and is not the flag). -/
theorem referenceSemiclassicalLayout (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (ℓ : ℕ) :
    SemiclassicalLayout (referenceControl P inst ℓ) (RL).data (RL).work (RL).scratch (RL).flag :=
  (semiclassical_hyps_of_coherent (referenceX_qubits_eq P inst ℓ)
    (reference_gateWorkspaceOK P inst ℓ) (referenceOrderFindingSpaceLayout P inst ℓ)).2

/-- **The coherent circuit's `Balanced.Fits` gives the semiclassical `MGate.Fits`**
(control its first exponent qubit), so the hypothesis of
`semiclassical_peak_formula_balanced_u` holds wherever the existing
`OrderFindingPeakFormulaBalancedU`'s does. -/
theorem semiclassical_fits_of_coherent {P : ShorLoweringPolicy} {R : Balanced.Rule} {a N : ℕ}
    {x y work scratch : ExtReg} {flag : ℕ} {hw : ModMulCircuitWorkspaceOK y work}
    {hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag} {c : ℕ} {rest : List ℕ}
    (hc : x.active.qubits = c :: rest)
    (hf : Balanced.Fits P R (orderFindingApprox a N x y work scratch flag hw hs4)) (m : ℕ) :
    MGate.Fits P R (orderFindingSemiclassical a N c m y work scratch flag hw hs4) := by
  have hcore : Balanced.Fits P R
      (CmodMulInPlaceCore ((a ^ (2 ^ 0)) % N) N c y work scratch flag hw hs4) := by
    have h3 := hf.2.2.1
    unfold modExpApproxValid at h3
    rw [hc] at h3
    exact h3.1
  have hr : ∀ k, MGate.Fits P R
      (readoutRounds (semiclassicalMultipliers a N c m y work scratch flag hw hs4) c k) := by
    intro k
    induction k with
    | zero => exact trivial
    | succ k ih => exact ⟨ih, trivial, hcore, trivial, trivial, trivial⟩
  exact ⟨hf.2.1, hr m⟩

/-- The semiclassical circuit at the reference layout fits a rule the reference layout
fits (`Balanced.ReferenceFits`), for every number of rounds: `semiclassical_fits_of_coherent`
at the reference layout. -/
theorem referenceSemiclassicalFits (P : ShorLoweringPolicy) (R : Balanced.Rule)
    (hfits : Balanced.ReferenceFits P R) (inst : ShorOrderFindingInstance) (ℓ m : ℕ) :
    MGate.Fits P R (orderFindingSemiclassical inst.a inst.N (referenceControl P inst ℓ) m
      (RL).data (RL).work (RL).scratch (RL).flag
      (referenceCircuitWorkspace P inst ℓ) (referenceStep4Workspace P inst ℓ)) :=
  semiclassical_fits_of_coherent (referenceX_qubits_eq P inst ℓ) (hfits.on inst ℓ) m

end Readout
end Shor
