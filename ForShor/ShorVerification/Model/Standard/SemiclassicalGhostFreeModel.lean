import ForShor.ShorVerification.Model.Standard.SemiclassicalMainModel
import ForShor.ShorVerification.Implementation.Readout.GhostFree
import ForShor.ShorVerification.Implementation.Readout.Proofs.LowerSupport

/-!
# Semiclassical order finding WITHOUT an exponent register, in the standard model

* `successMass_ge`: the PURE statement (no `QSemantics`, no register): for every `T`
  making the continued-fraction search complete and every order-finding instance,
  `successMass T verify a N (log₂(2N²)) (ord a N) ≥ κ / log(log₂ N + 1)`. Proved at the
  concrete model `Model.qs` by `successMass_ge_of_semantics`.
* `referenceGhostFreeSetup`: the hypotheses `SemiclassicalGhostFreeSetup` hold at the
  reference layout, from the all-zero ket (non-vacuity), with the control `c` =
  `referenceControl P inst ℓ`.
* `model_Shor_correct_semiclassical_ghostfree_at_shorPrecision` (high-level circuit) and
  `model_semiclassical_lowered_ghostfree_success_and_peak`, `…_balanced_…`,
  `…_balancedU_…`, `…_balancedU_default_…`: for the SAME lowered circuit term, some level
  `ℓ` has `referencePrecision ℓ ≤ shorPrecisionRounds N (log₂(2N²))`, the success
  probability with `m = log₂(2N²)` rounds and `Q = 2^m` is `≥ κ / (2 log(log₂ N + 1))`, the
  proved peak is the formula of `Cost.lean`, and the bound is positive.

## No exponent register in the statements

The statements name the data, work, scratch registers and the flag of the reference layout
`allocateReferenceLayout P inst ℓ` and the control qubit `referenceControl P inst ℓ`; the
number of rounds is `Nat.log2 (2 * inst.N ^ 2)`, the precision `shorPrecisionRounds`. They
do not mention the layout's exponent register `x`, and no hypothesis does.

Which qubit is the control: `referenceControl P inst ℓ` is, physically, the FIRST qubit
of the reference layout's exponent slot (`(allocateReferenceLayout P inst ℓ).x.active[0]`,
the layout of `Implementation/Reference/` allocates that slot for the coherent circuit).
It lies outside the data, work, scratch registers and the flag (`referenceGhostFreeSetup`'s
`layout`). The other `log₂(2N²) - 1` qubits of the slot are never touched
(`model_semiclassical_avoids_exponent`); the proofs here use the slot only to obtain the
precision level and the clean-input facts of the existing reference layout.

## Scope

Lean ρ = 0 (the exact phases); synthesis error outside Lean. The peak is the walk of
`Readout/Lowering.lean`: the lowered QFT and phase-product blocks of the multipliers are counted by the existing
proved walk exactly as in the coherent circuit (`QubitCount.lower_walk` via `qft_block` /
`signed_block` / `csigned_block`): every named qubit they touch is counted in
`semiclassical_peak_formula`, and their scratch is counted as a number. What is not proved
is a syntactic list of the names those blocks reach (`MGate.qftPhaseReach`), which the qubit
count does not need. Negation scratch and rotation-synthesis ancillas are counted as numbers
or not modelled. The ghost-register versions remain in `SemiclassicalMainModel.lean`.
-/

namespace Shor

/-- **The ideal Shor bound on the model-independent success mass.** For every `T` making
the continued-fraction search complete and every order-finding instance `(a, N)`, with
`m = log₂(2N²)`: `successMass T (d ↦ a^d mod N = 1) a N m (ord a N) ≥ κ / log(log₂ N + 1)`.
A statement about real numbers only. -/
theorem successMass_ge (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T)
    (inst : ShorOrderFindingInstance) :
    successMass T (fun d => decide ((inst.a ^ d) % inst.N = 1)) inst.a inst.N
        (Nat.log2 (2 * inst.N ^ 2)) (ord inst.a inst.N inst.coprime)
      ≥ κ / Real.log ((Nat.log2 inst.N : ℝ) + 1) := by
  exact successMass_ge_of_semantics Model.qs T hT inst

namespace Model

open Reference Readout

-- `RL` abbreviates the reference layout `allocateReferenceLayout P inst ℓ`.
set_option hygiene false in
local notation "RL" => allocateReferenceLayout P inst ℓ

/-- **The ghost-free hypotheses hold at the reference layout** in the model, from the
all-zero ket, with the control `c = referenceControl P inst ℓ`. -/
noncomputable def referenceGhostFreeSetup (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (ℓ : ℕ) :
    SemiclassicalGhostFreeSetup qs (referencePrecision ℓ) inst.N (referenceControl P inst ℓ)
      (RL).data (RL).work (RL).scratch (RL).flag (RegEncoding.zero (Basis := qs.Basis)) :=
  SemiclassicalGhostFreeSetup.of_ghost (referenceSemiclassicalSetup P inst ℓ)

/-- `log₂(2N²) > 0`. -/
theorem shorRounds_pos (inst : ShorOrderFindingInstance) : 0 < Nat.log2 (2 * inst.N ^ 2) := by
  rw [Nat.log2_eq_log_two]
  have := inst.range
  exact Nat.log_pos Nat.one_lt_two (by nlinarith)

/-- Some precision level reaches `shorPrecisionRounds N (log₂(2N²))`, a positive number. -/
theorem exists_level_le_shorPrecisionRounds (inst : ShorOrderFindingInstance) :
    ∃ ℓ : ℕ, referencePrecision ℓ ≤ shorPrecisionRounds inst.N (Nat.log2 (2 * inst.N ^ 2)) := by
  have hN : 2 ≤ inst.N := by have := inst.range; omega
  set s := shorPrecisionRounds inst.N (Nat.log2 (2 * inst.N ^ 2)) with hs
  have hspos : 0 < s := by
    have := shorPrecision_pos inst.N hN (Reg.interval 0 (Nat.log2 (2 * inst.N ^ 2)))
      (by rw [regSize_interval]; exact shorRounds_pos inst)
    rwa [shorPrecision_eq_rounds, regSize_interval] at this
  obtain ⟨ℓ, hℓ⟩ := exists_nat_gt (1 / s)
  refine ⟨ℓ, ?_⟩
  unfold referencePrecision
  rw [div_le_iff₀ (by positivity)]
  rw [div_lt_iff₀ hspos] at hℓ
  nlinarith

/-- The bound `κ / (2 log(log₂ N + 1))` is positive. -/
theorem bound_pos (inst : ShorOrderFindingInstance) :
    0 < κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1)) := by
  have hN : 2 ≤ inst.N := by have := inst.range; omega
  have hlog : 0 < Nat.log2 inst.N := by
    rw [Nat.log2_eq_log_two]; exact Nat.log_pos Nat.one_lt_two hN
  have hL : (0 : ℝ) < Real.log ((Nat.log2 inst.N : ℝ) + 1) := by
    apply Real.log_pos
    have : (0 : ℝ) < (Nat.log2 inst.N : ℝ) := by exact_mod_cast hlog
    linarith
  have := κ_pos
  positivity

/-- **High-level circuit, no exponent register, in the model.** Some level `ℓ` has
`referencePrecision ℓ ≤ shorPrecisionRounds N (log₂(2N²))`, and there
`orderFindingSemiclassical` with `log₂(2N²)` rounds at the reference layout (control
`referenceControl`), from the all-zero ket, succeeds with probability
`≥ κ / (2 log(log₂ N + 1))`, a positive number. -/
theorem model_Shor_correct_semiclassical_ghostfree_at_shorPrecision (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T) :
    ∃ ℓ : ℕ, referencePrecision ℓ ≤ shorPrecisionRounds inst.N (Nat.log2 (2 * inst.N ^ 2)) ∧
      probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
          (Nat.log2 (2 * inst.N ^ 2)) (ord inst.a inst.N inst.coprime)
          (2 ^ Nat.log2 (2 * inst.N ^ 2))
          ((orderFindingSemiclassical inst.a inst.N (referenceControl P inst ℓ)
              (Nat.log2 (2 * inst.N ^ 2)) (RL).data (RL).work (RL).scratch (RL).flag
              (referenceGhostFreeSetup P inst ℓ).circuit_workspace
              (referenceGhostFreeSetup P inst ℓ).step4_workspace).eval
            (MState.init (qs.ket RegEncoding.zero)))
        ≥ κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1)) ∧
      0 < κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1)) := by
  obtain ⟨ℓ, hprec⟩ := exists_level_le_shorPrecisionRounds inst
  refine ⟨ℓ, hprec, ?_, bound_pos inst⟩
  exact Shor_correct_semiclassical_ghostfree_at_shorPrecision T hT inst _ _ _ _ _ _
    (allocateReferenceLayout_data_width P inst ℓ) _ hprec (referenceGhostFreeSetup P inst ℓ)

/-- **Plain lowering, no exponent register: success and peak of one circuit, in the
model.** -/
theorem model_semiclassical_lowered_ghostfree_success_and_peak (P : ShorLoweringPolicy)
    (hP : P.Admissible) (inst : ShorOrderFindingInstance) (T : ℕ → ℕ)
    (hT : ContinuedFractionSearchComplete T) :
    ∃ ℓ : ℕ, referencePrecision ℓ ≤ shorPrecisionRounds inst.N (Nat.log2 (2 * inst.N ^ 2)) ∧
      probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
          (Nat.log2 (2 * inst.N ^ 2)) (ord inst.a inst.N inst.coprime)
          (2 ^ Nat.log2 (2 * inst.N ^ 2))
          ((orderFindingSemiclassicalLow P inst.a inst.N (referenceControl P inst ℓ)
              (Nat.log2 (2 * inst.N ^ 2)) (RL).data (RL).work (RL).scratch (RL).flag
              (referenceGhostFreeSetup P inst ℓ).circuit_workspace
              (referenceGhostFreeSetup P inst ℓ).step4_workspace
              (referenceSemiclassicalWorkspaceOK P inst ℓ _)).eval
            (MState.init (qs.ket RegEncoding.zero)))
        ≥ κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1)) ∧
      (orderFindingSemiclassicalLow P inst.a inst.N (referenceControl P inst ℓ)
          (Nat.log2 (2 * inst.N ^ 2)) (RL).data (RL).work (RL).scratch (RL).flag
          (referenceGhostFreeSetup P inst ℓ).circuit_workspace
          (referenceGhostFreeSetup P inst ℓ).step4_workspace
          (referenceSemiclassicalWorkspaceOK P inst ℓ _)).peakQubitsFor P.negation
          (orderFindingBaseSetSC (referenceControl P inst ℓ) (RL).data (RL).work (RL).scratch
            (RL).flag)
        = Policy.orderFindingQubitsSC P (referenceDataWidth inst) (referenceWorkWidth inst ℓ)
            (referenceScratchWidth inst ℓ) ∧
      0 < κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1)) := by
  obtain ⟨ℓ, hprec⟩ := exists_level_le_shorPrecisionRounds inst
  refine ⟨ℓ, hprec, ?_, ?_, bound_pos inst⟩
  · exact Shor_correct_semiclassical_lowered_ghostfree_at_shorPrecision T hT inst P hP _ _ _ _ _ _
      (allocateReferenceLayout_data_width P inst ℓ) _ hprec (referenceGhostFreeSetup P inst ℓ)
      (referenceSemiclassicalCleanInput P inst ℓ) _
  · refine Eq.trans (semiclassical_peak_formula P hP _ _ _ _ _ _ _ _ _ _ _
      (referenceGhostFreeSetup P inst ℓ).layout (shorRounds_pos inst)) ?_
    rw [referenceLayout_data_width', referenceLayout_work_width', referenceLayout_scratch_width']

/-- **Balanced lowering, no exponent register: success and peak of one circuit, in the
model**, for every rule. -/
theorem model_semiclassical_lowered_balanced_ghostfree_success_and_peak (P : ShorLoweringPolicy)
    (hP : P.Admissible) (R : Balanced.Rule) (inst : ShorOrderFindingInstance) (T : ℕ → ℕ)
    (hT : ContinuedFractionSearchComplete T) :
    ∃ ℓ : ℕ, referencePrecision ℓ ≤ shorPrecisionRounds inst.N (Nat.log2 (2 * inst.N ^ 2)) ∧
      probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
          (Nat.log2 (2 * inst.N ^ 2)) (ord inst.a inst.N inst.coprime)
          (2 ^ Nat.log2 (2 * inst.N ^ 2))
          ((orderFindingSemiclassicalLowBalanced P R inst.a inst.N (referenceControl P inst ℓ)
              (Nat.log2 (2 * inst.N ^ 2)) (RL).data (RL).work (RL).scratch (RL).flag
              (referenceGhostFreeSetup P inst ℓ).circuit_workspace
              (referenceGhostFreeSetup P inst ℓ).step4_workspace
              (referenceSemiclassicalWorkspaceOK P inst ℓ _)).eval
            (MState.init (qs.ket RegEncoding.zero)))
        ≥ κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1)) ∧
      (orderFindingSemiclassicalLowBalanced P R inst.a inst.N (referenceControl P inst ℓ)
          (Nat.log2 (2 * inst.N ^ 2)) (RL).data (RL).work (RL).scratch (RL).flag
          (referenceGhostFreeSetup P inst ℓ).circuit_workspace
          (referenceGhostFreeSetup P inst ℓ).step4_workspace
          (referenceSemiclassicalWorkspaceOK P inst ℓ _)).peakQubitsFor P.negation
          (orderFindingBaseSetSC (referenceControl P inst ℓ) (RL).data (RL).work (RL).scratch
            (RL).flag)
        = Policy.orderFindingQubitsBalancedSC P R (referenceDataWidth inst) (RL).data.capacity
            (referenceWorkWidth inst ℓ) (RL).work.capacity
            (referenceScratchWidth inst ℓ) (RL).scratch.capacity ∧
      0 < κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1)) := by
  obtain ⟨ℓ, hprec⟩ := exists_level_le_shorPrecisionRounds inst
  refine ⟨ℓ, hprec, ?_, ?_, bound_pos inst⟩
  · exact Shor_correct_semiclassical_lowered_balanced_ghostfree_at_shorPrecision R T hT inst P hP
      _ _ _ _ _ _ (allocateReferenceLayout_data_width P inst ℓ) _ hprec
      (referenceGhostFreeSetup P inst ℓ) (referenceSemiclassicalCleanInput P inst ℓ) _
  · refine Eq.trans (semiclassical_peak_formula_balanced P R hP _ _ _ _ _ _ _ _ _ _ _
      (referenceGhostFreeSetup P inst ℓ).layout (shorRounds_pos inst)) ?_
    rw [referenceLayout_data_width', referenceLayout_work_width', referenceLayout_scratch_width']

/-- **Every site split, no exponent register: success and peak of one circuit, in the
model**, for every rule the reference layout fits (`Balanced.ReferenceFits P R`). -/
theorem model_semiclassical_lowered_balancedU_ghostfree_success_and_peak
    (P : ShorLoweringPolicy) (hP : P.Admissible) (R : Balanced.Rule)
    (hfits : Balanced.ReferenceFits P R) (inst : ShorOrderFindingInstance) (T : ℕ → ℕ)
    (hT : ContinuedFractionSearchComplete T) :
    ∃ ℓ : ℕ, referencePrecision ℓ ≤ shorPrecisionRounds inst.N (Nat.log2 (2 * inst.N ^ 2)) ∧
      probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
          (Nat.log2 (2 * inst.N ^ 2)) (ord inst.a inst.N inst.coprime)
          (2 ^ Nat.log2 (2 * inst.N ^ 2))
          ((orderFindingSemiclassicalLowBalancedU P R inst.a inst.N (referenceControl P inst ℓ)
              (Nat.log2 (2 * inst.N ^ 2)) (RL).data (RL).work (RL).scratch (RL).flag
              (referenceGhostFreeSetup P inst ℓ).circuit_workspace
              (referenceGhostFreeSetup P inst ℓ).step4_workspace
              (referenceSemiclassicalWorkspaceOK P inst ℓ _)
              (referenceSemiclassicalFits P R hfits inst ℓ _)).eval
            (MState.init (qs.ket RegEncoding.zero)))
        ≥ κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1)) ∧
      (orderFindingSemiclassicalLowBalancedU P R inst.a inst.N (referenceControl P inst ℓ)
          (Nat.log2 (2 * inst.N ^ 2)) (RL).data (RL).work (RL).scratch (RL).flag
          (referenceGhostFreeSetup P inst ℓ).circuit_workspace
          (referenceGhostFreeSetup P inst ℓ).step4_workspace
          (referenceSemiclassicalWorkspaceOK P inst ℓ _)
          (referenceSemiclassicalFits P R hfits inst ℓ _)).peakQubitsFor P.negation
          (orderFindingBaseSetSC (referenceControl P inst ℓ) (RL).data (RL).work (RL).scratch
            (RL).flag)
        = Policy.orderFindingQubitsUSC P R (referenceDataWidth inst) (referenceWorkWidth inst ℓ)
            (referenceScratchWidth inst ℓ) ∧
      0 < κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1)) := by
  obtain ⟨ℓ, hprec⟩ := exists_level_le_shorPrecisionRounds inst
  refine ⟨ℓ, hprec, ?_, ?_, bound_pos inst⟩
  · exact Shor_correct_semiclassical_lowered_balancedU_ghostfree_at_shorPrecision R T hT inst P hP
      _ _ _ _ _ _ (allocateReferenceLayout_data_width P inst ℓ) _ hprec
      (referenceGhostFreeSetup P inst ℓ) (referenceSemiclassicalCleanInput P inst ℓ) _ _
  · refine Eq.trans (semiclassical_peak_formula_balanced_u P R hP _ _ _ _ _ _ _ _ _ _ _ _
      (referenceGhostFreeSetup P inst ℓ).layout (shorRounds_pos inst)) ?_
    rw [referenceLayout_data_width', referenceLayout_work_width', referenceLayout_scratch_width']

/-- The `U` statement at the default rule (which every reference layout fits). -/
theorem model_semiclassical_lowered_balancedU_default_ghostfree_success_and_peak
    (P : ShorLoweringPolicy) (hP : P.Admissible) (inst : ShorOrderFindingInstance) (T : ℕ → ℕ)
    (hT : ContinuedFractionSearchComplete T) :
    ∃ ℓ : ℕ, referencePrecision ℓ ≤ shorPrecisionRounds inst.N (Nat.log2 (2 * inst.N ^ 2)) ∧
      probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
          (Nat.log2 (2 * inst.N ^ 2)) (ord inst.a inst.N inst.coprime)
          (2 ^ Nat.log2 (2 * inst.N ^ 2))
          ((orderFindingSemiclassicalLowBalancedU P Balanced.defaultRule inst.a inst.N
              (referenceControl P inst ℓ)
              (Nat.log2 (2 * inst.N ^ 2)) (RL).data (RL).work (RL).scratch (RL).flag
              (referenceGhostFreeSetup P inst ℓ).circuit_workspace
              (referenceGhostFreeSetup P inst ℓ).step4_workspace
              (referenceSemiclassicalWorkspaceOK P inst ℓ _)
              (referenceSemiclassicalFits P _ (Balanced.referenceFits_default P) inst ℓ _)).eval
            (MState.init (qs.ket RegEncoding.zero)))
        ≥ κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1)) ∧
      (orderFindingSemiclassicalLowBalancedU P Balanced.defaultRule inst.a inst.N
          (referenceControl P inst ℓ)
          (Nat.log2 (2 * inst.N ^ 2)) (RL).data (RL).work (RL).scratch (RL).flag
          (referenceGhostFreeSetup P inst ℓ).circuit_workspace
          (referenceGhostFreeSetup P inst ℓ).step4_workspace
          (referenceSemiclassicalWorkspaceOK P inst ℓ _)
          (referenceSemiclassicalFits P _ (Balanced.referenceFits_default P) inst ℓ _)).peakQubitsFor
          P.negation
          (orderFindingBaseSetSC (referenceControl P inst ℓ) (RL).data (RL).work (RL).scratch
            (RL).flag)
        = Policy.orderFindingQubitsUSC P Balanced.defaultRule (referenceDataWidth inst)
            (referenceWorkWidth inst ℓ) (referenceScratchWidth inst ℓ) ∧
      0 < κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1)) := by
  exact model_semiclassical_lowered_balancedU_ghostfree_success_and_peak P hP _
    (Balanced.referenceFits_default P) inst T hT


/-- **The model peak does not count the unused exponent-slot qubits.** The walk's base set
`orderFindingBaseSetSC` at the reference layout contains the control
`referenceControl P inst ℓ` (the slot's first qubit) and NO other qubit of the reference
layout's exponent slot `(allocateReferenceLayout P inst ℓ).x.active`. -/
theorem model_baseSetSC_excludes_unused_exponent (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (ℓ : ℕ) :
    referenceControl P inst ℓ
        ∈ orderFindingBaseSetSC (referenceControl P inst ℓ) (RL).data (RL).work (RL).scratch
          (RL).flag ∧
    ∀ q ∈ (RL).x.active.qubits, q ≠ referenceControl P inst ℓ →
      q ∉ orderFindingBaseSetSC (referenceControl P inst ℓ) (RL).data (RL).work (RL).scratch
        (RL).flag := by
  refine ⟨by simp [orderFindingBaseSetSC], fun q hq hqc hb => ?_⟩
  exact exponent_outside_semiclassicalQubits (referenceApproxSetup (qs := qs) P inst ℓ) q hq hqc
    (orderFindingBaseSetSC_subset _ _ _ _ _ (Finset.mem_coe.2 hb))

end Model
end Shor
