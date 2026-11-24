import ForShor.ShorVerification.Model.Standard.SemiclassicalLocalityModel
import ForShor.ShorVerification.Implementation.Readout.LocalityInfinite
import ForShor.ShorVerification.Implementation.Readout.LocalityInfiniteSuperpose
import ForShor.ShorVerification.Implementation.Readout.LocalityTests

/-!
# Semiclassical readout in the standard model: an INFINITE pattern outside the named qubits

The model basis is `ModelBasis = ℕ → Bool`, so basis states that differ at infinitely many
qubits exist, and `hfin` of `Locality.lean` is a real restriction there. Instances of the
infinite-difference theorems of `Implementation/Readout/LocalityInfinite.lean` at `Model.qs`,
the reference layout `allocateReferenceLayout P inst ℓ` and control `referenceControl P inst ℓ`,
for every policy, instance and level (`SQ` = `semiclassicalQubits` of that layout):

* `patternKet S b0 pat`: the basis state equal to `b0` on `S` and to the arbitrary pattern
  `pat : ℕ → Bool` everywhere else;
* `semiclassicalQubits_finite`, `model_allOnes_pattern_infinite`: `SQ` is finite, so the ket
  `patternKet SQ 0 (fun _ => true)` differs from `|0…0⟩` at INFINITELY many qubits (the old
  `hfin` hypothesis is false for it); `model_allOnes_pattern_exponent_tail`: it has every
  exponent qubit except the control at `1`;
* `model_real_pattern`, `model_lowered_pattern`: for EVERY pattern `pat`, the real circuit (any
  number of rounds) and the lowered circuit (every admissible policy) have the same record
  distribution from `patternKet SQ 0 pat` as from `|0…0⟩`;
* `model_lowered_success_pattern`: some level `ℓ` with `referencePrecision ℓ ≤ shorPrecision N x`
  at which the lowered circuit, started from `patternKet SQ 0 pat` for ANY pattern (infinite
  ones included), succeeds with probability `≥ κ / (2 log(log₂ N + 1)) > 0`;
* `model_allOnes_pattern_ne_zero`, `model_real_superpose_pattern`,
  `model_lowered_superpose_pattern`: the superposition `α|0…0⟩ + β|pattern⟩` of the all-zero
  ket and the all-ones INFINITE pattern outside the named qubits (two distinct kets differing at
  infinitely many qubits): every record probability of the real and of the lowered circuit is
  `(‖α‖² + ‖β‖²)` times its probability from `|0…0⟩`;
* `model_named_qubit_matters` (negative sanity at `Model.qs`): flipping a NAMED qubit can change
  a record probability from `1` to `0`.
-/

namespace Shor
namespace Model

open Reference Readout

/-- The basis state equal to `b0` on `S` and to the pattern `pat` outside `S`. -/
noncomputable def patternKet (S : Set ℕ) (b0 pat : ModelBasis) : ModelBasis := by
  classical
  exact fun p => if p ∈ S then b0 p else pat p

theorem bit_patternKet_mem {S : Set ℕ} {b0 pat : ModelBasis} {p : ℕ} (hp : p ∈ S) :
    RegEncoding.bit (Basis := qs.Basis) p (patternKet S b0 pat) = RegEncoding.bit p b0 := by
  change (patternKet S b0 pat) p = b0 p
  simp [patternKet, hp]

theorem bit_patternKet_not_mem {S : Set ℕ} {b0 pat : ModelBasis} {p : ℕ} (hp : p ∉ S) :
    RegEncoding.bit (Basis := qs.Basis) p (patternKet S b0 pat) = pat p := by
  change (patternKet S b0 pat) p = pat p
  simp [patternKet, hp]

/-- The named qubits of the semiclassical circuit are finitely many. -/
theorem semiclassicalQubits_finite (c : ℕ) (y work scratch : ExtReg) (flag : ℕ) :
    (semiclassicalQubits c y work scratch flag).Finite := by
  unfold semiclassicalQubits
  simp only [Set.ofPred_or, Set.ofPred_eq_eq_singleton]
  repeat' apply Set.Finite.union
  all_goals first | exact Set.finite_singleton _ | exact List.finite_toSet _

/-- Outside a finite set, the all-ones pattern differs from `|0…0⟩` at infinitely many
qubits. -/
theorem allOnes_pattern_infinite {S : Set ℕ} (hS : S.Finite) :
    {p | RegEncoding.bit (Basis := qs.Basis) p (patternKet S RegEncoding.zero (fun _ => true))
      ≠ RegEncoding.bit p (RegEncoding.zero (Basis := qs.Basis))}.Infinite := by
  refine hS.infinite_compl.mono fun p hp => ?_
  change RegEncoding.bit (Basis := qs.Basis) p _ ≠ _
  rw [bit_patternKet_not_mem hp, RegEncoding.bit_zero]
  decide

set_option hygiene false in
local notation "RL" => allocateReferenceLayout P inst ℓ

set_option hygiene false in
local notation "SQ" => semiclassicalQubits (referenceControl P inst ℓ) (RL).data (RL).work
  (RL).scratch (RL).flag

/-- A patterned ket agrees with `|0…0⟩` on the named qubits. -/
theorem model_pattern_agree (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (ℓ : ℕ)
    (pat : ModelBasis) :
    ∀ p ∈ SQ, RegEncoding.bit (Basis := qs.Basis) p (patternKet SQ RegEncoding.zero pat)
      = RegEncoding.bit p (RegEncoding.zero (Basis := qs.Basis)) :=
  fun _ hp => bit_patternKet_mem hp

/-- **Non-vacuity.** The all-ones pattern outside the named qubits differs from `|0…0⟩` at
infinitely many qubits: the finite-difference theorems of `Locality.lean` do not apply to it. -/
theorem model_allOnes_pattern_infinite (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (ℓ : ℕ) :
    {p | RegEncoding.bit (Basis := qs.Basis) p (patternKet SQ RegEncoding.zero (fun _ => true))
      ≠ RegEncoding.bit p (RegEncoding.zero (Basis := qs.Basis))}.Infinite :=
  allOnes_pattern_infinite (semiclassicalQubits_finite _ _ _ _ _)

/-- The all-ones patterned ket has every exponent qubit after the control at `1`. -/
theorem model_allOnes_pattern_exponent_tail (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (ℓ : ℕ) :
    ∀ q ∈ (RL).x.active.qubits.tail,
      RegEncoding.bit (Basis := qs.Basis) q (patternKet SQ RegEncoding.zero (fun _ => true))
        = true :=
  fun q hq => bit_patternKet_not_mem (model_exponent_tail_unnamed P inst ℓ q hq).1

/-- **Real circuit, model, any pattern.** -/
theorem model_real_pattern (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (ℓ m : ℕ) (pat : ModelBasis) (r : Record) :
    recordProb ((orderFindingSemiclassical inst.a inst.N (referenceControl P inst ℓ) m
        (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace).eval
        (MState.init (qs.ket (patternKet SQ RegEncoding.zero pat)))) r
      = recordProb ((orderFindingSemiclassical inst.a inst.N (referenceControl P inst ℓ) m
        (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace).eval
        (MState.init (qs.ket RegEncoding.zero))) r :=
  orderFindingSemiclassical_recordProb_of_agree_inf _ _ _ m _ _ _ _ _ _ _ _
    (model_pattern_agree P inst ℓ pat) r

/-- **Lowered circuit, model, any pattern**, every admissible policy. -/
theorem model_lowered_pattern (P : ShorLoweringPolicy) (hP : P.Admissible)
    (inst : ShorOrderFindingInstance) (ℓ m : ℕ) (pat : ModelBasis) (r : Record) :
    recordProb ((orderFindingSemiclassicalLow P inst.a inst.N (referenceControl P inst ℓ) m
        (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace
        (referenceSemiclassicalWorkspaceOK P inst ℓ m)).eval
        (MState.init (qs.ket (patternKet SQ RegEncoding.zero pat)))) r
      = recordProb ((orderFindingSemiclassicalLow P inst.a inst.N (referenceControl P inst ℓ) m
        (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace
        (referenceSemiclassicalWorkspaceOK P inst ℓ m)).eval
        (MState.init (qs.ket RegEncoding.zero))) r :=
  orderFindingSemiclassicalLow_recordProb_of_agree_inf hP _ _ _ m _ _ _ _ _ _ _
    (referenceSemiclassicalSetup P inst ℓ).layout _ _ (referenceSemiclassicalCleanInput P inst ℓ)
    (model_reference_scratch_zero P inst ℓ) (model_pattern_agree P inst ℓ pat) r

/-- **Success from an arbitrary (possibly infinite) pattern, lowered, model.** For every
admissible policy and instance there is a level `ℓ` with `referencePrecision ℓ ≤ shorPrecision
N x` at which the lowered circuit, started from `patternKet SQ 0 pat` for ANY pattern `pat`
(every qubit outside the named ones arbitrary, e.g. all `1`), succeeds with probability
`≥ κ / (2 log(log₂ N + 1)) > 0`. -/
theorem model_lowered_success_pattern (P : ShorLoweringPolicy) (hP : P.Admissible)
    (inst : ShorOrderFindingInstance) (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T) :
    ∃ ℓ : ℕ, referencePrecision ℓ ≤ shorPrecision inst.N (RL).x.active ∧
      (∀ pat : ModelBasis,
        probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
            (regSize (RL).x.active) (ord inst.a inst.N inst.coprime) (ASize (RL).x.active)
            ((orderFindingSemiclassicalLow P inst.a inst.N (referenceControl P inst ℓ)
                (regSize (RL).x.active) (RL).data (RL).work (RL).scratch (RL).flag
                (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
                (referenceSemiclassicalSetup P inst ℓ).step4_workspace
                (referenceSemiclassicalWorkspaceOK P inst ℓ _)).eval
              (MState.init (qs.ket (patternKet SQ RegEncoding.zero pat))))
          ≥ κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1))) ∧
      0 < κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1)) := by
  obtain ⟨ℓ, hprec, hsucc, hpos⟩ :=
    model_Shor_correct_semiclassical_lowered_at_shorPrecision P hP inst T hT
  refine ⟨ℓ, hprec, fun pat => ?_, hpos⟩
  rw [probability_of_success_M_congr _ _ _ _ _ fun rec =>
    model_lowered_pattern P hP inst ℓ _ pat rec]
  exact hsucc

/-- The all-ones patterned ket is not `|0…0⟩` (it is `1` at the exponent qubits after the
control, which exist). -/
theorem model_allOnes_pattern_ne_zero (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (ℓ : ℕ) : (patternKet SQ RegEncoding.zero (fun _ => true) : qs.Basis) ≠ RegEncoding.zero := by
  intro h
  obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ (model_tail_ne_nil P inst ℓ)
  have := model_allOnes_pattern_exponent_tail P inst ℓ q hq
  rw [h, RegEncoding.bit_zero] at this
  exact Bool.false_ne_true this

/-- The two-ket family `false ↦ |0…0⟩`, `true ↦ |all-ones pattern⟩`. -/
noncomputable def zeroOrPattern (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (ℓ : ℕ) (i : Bool) : qs.Basis :=
  if i then patternKet SQ RegEncoding.zero (fun _ => true) else RegEncoding.zero

theorem zeroOrPattern_injOn (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (ℓ : ℕ) :
    Set.InjOn (zeroOrPattern P inst ℓ) (Finset.univ : Finset Bool) := by
  have hne := model_allOnes_pattern_ne_zero P inst ℓ
  intro i _ j _ hij
  cases i <;> cases j <;> simp_all [zeroOrPattern, eq_comm]

theorem zeroOrPattern_agree (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (ℓ : ℕ) :
    ∀ i ∈ (Finset.univ : Finset Bool), ∀ p ∈ SQ,
      RegEncoding.bit p (zeroOrPattern P inst ℓ i) = RegEncoding.bit p (RegEncoding.zero (Basis := qs.Basis)) := by
  intro i _ p hp
  cases i
  · rfl
  · exact model_pattern_agree P inst ℓ _ p hp

theorem sum_zeroOrPattern (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (ℓ : ℕ)
    (α β : ℂ) :
    ∑ i ∈ (Finset.univ : Finset Bool), (fun i : Bool => if i then β else α) i
        • qs.ket (zeroOrPattern P inst ℓ i)
      = α • qs.ket RegEncoding.zero + β • qs.ket (patternKet SQ RegEncoding.zero (fun _ => true)) := by
  rw [Fintype.sum_bool]
  simp only [zeroOrPattern, ↓reduceIte, Bool.false_eq_true]
  exact add_comm _ _

/-- **Superposed infinite pattern, real circuit, model.** -/
theorem model_real_superpose_pattern (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (ℓ m : ℕ) (α β : ℂ) (r : Record) :
    recordProb ((orderFindingSemiclassical inst.a inst.N (referenceControl P inst ℓ) m
        (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace).eval
        (MState.init (α • qs.ket RegEncoding.zero
          + β • qs.ket (patternKet SQ RegEncoding.zero (fun _ => true))))) r
      = (‖α‖ ^ 2 + ‖β‖ ^ 2) * recordProb ((orderFindingSemiclassical inst.a inst.N
        (referenceControl P inst ℓ) m (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace).eval
        (MState.init (qs.ket RegEncoding.zero))) r := by
  have h := orderFindingSemiclassical_recordProb_superpose_inf inst.a inst.N (referenceControl P inst ℓ) m (RL).data (RL).work (RL).scratch (RL).flag
    (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
    (referenceSemiclassicalSetup P inst ℓ).step4_workspace Finset.univ
    (fun i : Bool => if i then β else α) (zeroOrPattern P inst ℓ) RegEncoding.zero
    (zeroOrPattern_injOn P inst ℓ) (zeroOrPattern_agree P inst ℓ) r
  rw [sum_zeroOrPattern, Fintype.sum_bool] at h
  simp only [↓reduceIte, Bool.false_eq_true] at h
  rw [h, add_comm (‖β‖ ^ 2)]

/-- **Superposed infinite pattern, lowered circuit, model**, every admissible policy. -/
theorem model_lowered_superpose_pattern (P : ShorLoweringPolicy) (hP : P.Admissible)
    (inst : ShorOrderFindingInstance) (ℓ m : ℕ) (α β : ℂ) (r : Record) :
    recordProb ((orderFindingSemiclassicalLow P inst.a inst.N (referenceControl P inst ℓ) m
        (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace
        (referenceSemiclassicalWorkspaceOK P inst ℓ m)).eval
        (MState.init (α • qs.ket RegEncoding.zero
          + β • qs.ket (patternKet SQ RegEncoding.zero (fun _ => true))))) r
      = (‖α‖ ^ 2 + ‖β‖ ^ 2) * recordProb ((orderFindingSemiclassicalLow P inst.a inst.N
        (referenceControl P inst ℓ) m (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace
        (referenceSemiclassicalWorkspaceOK P inst ℓ m)).eval
        (MState.init (qs.ket RegEncoding.zero))) r := by
  have h := orderFindingSemiclassicalLow_recordProb_superpose_inf hP inst.a inst.N (referenceControl P inst ℓ) m (RL).data (RL).work (RL).scratch (RL).flag
    (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
    (referenceSemiclassicalSetup P inst ℓ).step4_workspace
    (referenceSemiclassicalWorkspaceOK P inst ℓ m)
    (referenceSemiclassicalSetup P inst ℓ).layout _ (referenceSemiclassicalCleanInput P inst ℓ)
    (model_reference_scratch_zero P inst ℓ) Finset.univ (fun i : Bool => if i then β else α)
    (zeroOrPattern P inst ℓ) (zeroOrPattern_injOn P inst ℓ) (zeroOrPattern_agree P inst ℓ) r
  rw [sum_zeroOrPattern, Fintype.sum_bool] at h
  simp only [↓reduceIte, Bool.false_eq_true] at h
  rw [h, add_comm (‖β‖ ^ 2)]

/-- **Negative sanity at `Model.qs`: a named qubit matters.** `measureReset q` from `|0…0⟩`
gives record `[false]` with probability `1`; from `|0…0⟩` with `q` flipped, probability `0`. -/
theorem model_named_qubit_matters (q : ℕ) :
    recordProb ((MGate.measureReset q).eval
        (MState.init (qs.ket (RegEncoding.zero (Basis := qs.Basis))))) [false] = 1 ∧
    recordProb ((MGate.measureReset q).eval
        (MState.init (qs.ket (flipBit q (RegEncoding.zero (Basis := qs.Basis)))))) [false] = 0 :=
  LocalityTests.measureReset_flip_named q _ (RegEncoding.bit_zero q)

end Model
end Shor

#print axioms Shor.Model.bit_patternKet_mem
#print axioms Shor.Model.bit_patternKet_not_mem
#print axioms Shor.Model.semiclassicalQubits_finite
#print axioms Shor.Model.allOnes_pattern_infinite
#print axioms Shor.Model.model_pattern_agree
#print axioms Shor.Model.model_allOnes_pattern_infinite
#print axioms Shor.Model.model_allOnes_pattern_exponent_tail
#print axioms Shor.Model.model_real_pattern
#print axioms Shor.Model.model_lowered_pattern
#print axioms Shor.Model.model_lowered_success_pattern
#print axioms Shor.Model.model_named_qubit_matters
#print axioms Shor.Model.model_allOnes_pattern_ne_zero
#print axioms Shor.Model.zeroOrPattern_injOn
#print axioms Shor.Model.zeroOrPattern_agree
#print axioms Shor.Model.sum_zeroOrPattern
#print axioms Shor.Model.model_real_superpose_pattern
#print axioms Shor.Model.model_lowered_superpose_pattern
