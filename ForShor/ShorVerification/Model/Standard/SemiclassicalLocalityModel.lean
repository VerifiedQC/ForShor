import ForShor.ShorVerification.Model.Standard.SemiclassicalLoweredModel
import ForShor.ShorVerification.Implementation.Readout.LocalitySpectator

/-!
# Semiclassical readout in the standard model: exponent qubits other than the control do not matter

Instances of the locality theorems of `Implementation/Readout/Locality.lean` at `Model.qs`,
the reference layout `allocateReferenceLayout P inst ℓ` and the control
`referenceControl P inst ℓ` (= the first exponent qubit), for every policy, instance and level:

* `model_exponent_tail_mem_x_ne_control`: every exponent qubit after the first is a qubit of `x`
  and is not the control;
* `model_exponent_tail_unnamed`: every such qubit is outside `semiclassicalQubits` (control,
  owned qubits of data/work/scratch, flag) and outside the syntactic support of the circuit, for
  every number of rounds;
* `model_x_width_ge_three`, `model_tail_ne_nil`: there are such qubits (`|x| = log₂(2N²) ≥ 3`);
* `model_flipBits_tail_bits`, `model_flipBits_tail_ne_zero`: the start ket `flipBits x.tail
  |0…0⟩` has all those qubits at `1` and differs from `|0…0⟩` (the instances below are not about
  an unchanged ket);
* `model_reference_scratch_zero`: the scratch register is `0` in the all-zero ket (the named
  form of the setup field the lowered instances use);
* `model_real_superpose_exponent`, `model_lowered_superpose_exponent` (T5): any one of those
  exponent qubits in ANY superposition `α|0⟩ + β|1⟩`: every record probability of the real and
  of the lowered circuit is `(‖α‖² + ‖β‖²)` times its probability from `|0…0⟩`;
* `model_real_flip_exponent`: the real circuit `orderFindingSemiclassical` (any number of rounds)
  has the same record distribution from that ket as from `|0…0⟩`;
* `model_lowered_flip_exponent`: the same for the lowered circuit `orderFindingSemiclassicalLow`;
* `model_lowered_success_flip_exponent`: some level `ℓ` with `referencePrecision ℓ ≤
  shorPrecision N x` at which the lowered circuit, run from the ket with every exponent qubit
  but the control set to `1`, succeeds with probability `≥ κ / (2 log(log₂ N + 1)) > 0`;
* `model_ideal_flip_exponent`: the ideal circuit `semiclassicalIdeal`, from the start ket
  `semiclassicalStartKet` (data `= 1`), with any one exponent qubit other than the control
  flipped (T1, closed form).
-/

namespace Shor
namespace Model

open Reference Readout

set_option hygiene false in
local notation "RL" => allocateReferenceLayout P inst ℓ

/-- Every exponent qubit after the first is a qubit of the exponent register and is not the
control. -/
theorem model_exponent_tail_mem_x_ne_control (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (ℓ : ℕ) : ∀ q ∈ (RL).x.active.qubits.tail,
      q ∈ (RL).x.active.qubits ∧ q ≠ referenceControl P inst ℓ := by
  intro q hq
  have hnd := (RL).x.active.nodup
  rw [referenceX_qubits_eq] at hnd
  refine ⟨?_, ?_⟩
  · rw [referenceX_qubits_eq]; exact List.mem_cons_of_mem _ hq
  · rintro rfl; exact (List.nodup_cons.mp hnd).1 hq

/-- The flipped start ket has every exponent qubit after the first at `1`. -/
theorem model_flipBits_tail_bits (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (ℓ : ℕ) : ∀ q ∈ (RL).x.active.qubits.tail,
      RegEncoding.bit q (flipBits (RL).x.active.qubits.tail (RegEncoding.zero (Basis := qs.Basis)))
        = true := by
  intro q hq
  rw [bit_flipBits (List.Nodup.sublist (List.tail_sublist _) (RL).x.active.nodup)]
  simp only [hq, ↓reduceIte, RegEncoding.bit_zero, Bool.not_false]

/-- **The tail qubits are unnamed.** Every exponent qubit after the first is outside
`semiclassicalQubits` (control, owned qubits of data, work, scratch, flag) and outside the
syntactic support of the real circuit, for every number of rounds. -/
theorem model_exponent_tail_unnamed (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (ℓ : ℕ) : ∀ q ∈ (RL).x.active.qubits.tail,
      q ∉ semiclassicalQubits (referenceControl P inst ℓ) (RL).data (RL).work (RL).scratch
        (RL).flag ∧
      ∀ m, q ∉ (orderFindingSemiclassical inst.a inst.N (referenceControl P inst ℓ) m
        (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace).qubitSupport := by
  intro q hq
  have h := model_exponent_tail_mem_x_ne_control P inst ℓ q hq
  have hS := exponent_outside_semiclassicalQubits (referenceApproxSetup (qs := qs) P inst ℓ)
    q h.1 h.2
  exact ⟨hS, fun m => not_mem_orderFindingSemiclassical_support _ _ hS⟩

/-- The reference exponent register has at least three qubits: `|x| = log₂(2N²)` with
`N ≥ 2`. -/
theorem model_x_width_ge_three (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (ℓ : ℕ) : 3 ≤ regSize (RL).x.active := by
  rw [allocateReferenceLayout_x_width, Nat.log2_eq_log_two]
  have := inst.range
  have h8 : 2 ^ 3 ≤ 2 * inst.N ^ 2 := by nlinarith
  exact Nat.le_log_of_pow_le (by norm_num) h8

/-- So there are exponent qubits after the control. -/
theorem model_tail_ne_nil (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (ℓ : ℕ) :
    (RL).x.active.qubits.tail ≠ [] := by
  intro h
  have h3 := model_x_width_ge_three P inst ℓ
  have hl := congrArg List.length h
  rw [List.length_tail] at hl
  simp only [regSize, Reg.width] at h3
  simp only [List.length_nil] at hl
  omega

/-- The flipped start ket really differs from the all-zero ket. -/
theorem model_flipBits_tail_ne_zero (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (ℓ : ℕ) :
    flipBits (RL).x.active.qubits.tail (RegEncoding.zero (Basis := qs.Basis))
      ≠ RegEncoding.zero := by
  intro h
  obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ (model_tail_ne_nil P inst ℓ)
  have := model_flipBits_tail_bits P inst ℓ q hq
  rw [h, RegEncoding.bit_zero] at this
  exact Bool.false_ne_true this

/-- The scratch register of the reference layout is `0` in the all-zero ket (the setup's
`clean_input` field, named). -/
theorem model_reference_scratch_zero (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (ℓ : ℕ) :
    RegEncoding.toNat (RL).scratch.active (RegEncoding.zero (Basis := qs.Basis)) = 0 :=
  (referenceSemiclassicalSetup P inst ℓ).clean_input.2.2.2.2.2.1

/-- **Real circuit, model.** Flipping every exponent qubit except the control in the all-zero
start ket leaves every record probability of the real semiclassical circuit unchanged. -/
theorem model_real_flip_exponent (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (ℓ m : ℕ) (r : Record) :
    recordProb ((orderFindingSemiclassical inst.a inst.N (referenceControl P inst ℓ) m
        (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace).eval
        (MState.init (qs.ket (flipBits (RL).x.active.qubits.tail RegEncoding.zero)))) r
      = recordProb ((orderFindingSemiclassical inst.a inst.N (referenceControl P inst ℓ) m
        (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace).eval
        (MState.init (qs.ket RegEncoding.zero))) r :=
  orderFindingSemiclassical_recordProb_flip_exponent (referenceApproxSetup (qs := qs) P inst ℓ)
    inst.a m _ _ _ _ (model_exponent_tail_mem_x_ne_control P inst ℓ) r

/-- **Lowered circuit, model.** The same for the lowered circuit, for every admissible
policy. -/
theorem model_lowered_flip_exponent (P : ShorLoweringPolicy) (hP : P.Admissible)
    (inst : ShorOrderFindingInstance) (ℓ m : ℕ) (r : Record) :
    recordProb ((orderFindingSemiclassicalLow P inst.a inst.N (referenceControl P inst ℓ) m
        (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace
        (referenceSemiclassicalWorkspaceOK P inst ℓ m)).eval
        (MState.init (qs.ket (flipBits (RL).x.active.qubits.tail RegEncoding.zero)))) r
      = recordProb ((orderFindingSemiclassicalLow P inst.a inst.N (referenceControl P inst ℓ) m
        (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace
        (referenceSemiclassicalWorkspaceOK P inst ℓ m)).eval
        (MState.init (qs.ket RegEncoding.zero))) r :=
  orderFindingSemiclassicalLow_recordProb_flipBits hP _ _ _ m _ _ _ _ _ _ _
    (referenceSemiclassicalSetup P inst ℓ).layout _ (referenceSemiclassicalCleanInput P inst ℓ)
    (model_reference_scratch_zero P inst ℓ) _
    (fun q hq => (model_exponent_tail_unnamed P inst ℓ q hq).1) r

/-- **Success from a nonzero exponent register, lowered, model.** For every admissible policy
and instance there is a level `ℓ` with `referencePrecision ℓ ≤ shorPrecision N x` at which the
lowered semiclassical circuit, run from the ket with every exponent qubit except the control
set to `1`, succeeds with probability `≥ κ / (2 log(log₂ N + 1))`, a positive number. -/
theorem model_lowered_success_flip_exponent (P : ShorLoweringPolicy) (hP : P.Admissible)
    (inst : ShorOrderFindingInstance) (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T) :
    ∃ ℓ : ℕ, referencePrecision ℓ ≤ shorPrecision inst.N (RL).x.active ∧
      probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
          (regSize (RL).x.active) (ord inst.a inst.N inst.coprime) (ASize (RL).x.active)
          ((orderFindingSemiclassicalLow P inst.a inst.N (referenceControl P inst ℓ)
              (regSize (RL).x.active) (RL).data (RL).work (RL).scratch (RL).flag
              (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
              (referenceSemiclassicalSetup P inst ℓ).step4_workspace
              (referenceSemiclassicalWorkspaceOK P inst ℓ _)).eval
            (MState.init (qs.ket (flipBits (RL).x.active.qubits.tail RegEncoding.zero))))
        ≥ κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1)) ∧
      0 < κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1)) := by
  obtain ⟨ℓ, hprec, hsucc, hpos⟩ :=
    model_Shor_correct_semiclassical_lowered_at_shorPrecision P hP inst T hT
  refine ⟨ℓ, hprec, ?_, hpos⟩
  rw [probability_of_success_M_congr _ _ _ _ _ fun rec =>
    model_lowered_flip_exponent P hP inst ℓ _ rec]
  exact hsucc

/-- **Ideal circuit, model (T1).** From the start ket `semiclassicalStartKet` (data `= 1`,
control `0`) at the reference layout, flipping any exponent qubit other than the control leaves
every record probability of the ideal semiclassical readout unchanged. -/
theorem model_ideal_flip_exponent (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (ℓ m : ℕ) (q : ℕ) (hq : q ∈ (RL).x.active.qubits) (hqc : q ≠ referenceControl P inst ℓ)
    (r : Record) :
    let b1 := semiclassicalStartKet (qs := qs) (RL).data RegEncoding.zero
    recordProb ((semiclassicalIdeal inst.a inst.N m (RL).data.active
        (referenceControl P inst ℓ)).eval (MState.init (qs.ket (flipBit q b1)))) r
      = recordProb ((semiclassicalIdeal inst.a inst.N m (RL).data.active
        (referenceControl P inst ℓ)).eval (MState.init (qs.ket b1))) r := by
  intro b1
  have hN : 2 ≤ inst.N := by have := inst.range; omega
  have hn : regSize (RL).data.active = Nat.log2 (2 * inst.N) := by simp
  have hNy : inst.N ≤ ASize (RL).data.active := by
    simpa [ASize, hn] using shor_data_capacity_from_log2 inst.N
  obtain ⟨-, -, hdata1, hc0, -⟩ := model_semiclassical_start P inst ℓ
  have hS := exponent_outside_semiclassicalQubits (referenceApproxSetup (qs := qs) P inst ℓ) q hq hqc
  exact semiclassicalIdeal_recordProb_flipBit inst.a inst.N m _ _ b1 (by omega) hNy inst.coprime
    (fun h => (referenceSemiclassicalSetup P inst ℓ).layout.c_not_mem_data
      (List.mem_append_left _ h)) hdata1 hc0
    (fun h => hS (Or.inr (Or.inl (List.mem_append_left _ h)))) hqc r

/-- **T5, real circuit, model.** Any exponent qubit after the control, in ANY superposition
`α|0⟩ + β|1⟩` with every other qubit `0`: every record probability of the real circuit is
`(‖α‖² + ‖β‖²)` times its probability from `|0…0⟩`. -/
theorem model_real_superpose_exponent (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (ℓ m : ℕ) (q : ℕ) (hq : q ∈ (RL).x.active.qubits.tail) (α β : ℂ) (r : Record) :
    recordProb ((orderFindingSemiclassical inst.a inst.N (referenceControl P inst ℓ) m
        (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace).eval
        (MState.init (α • qs.ket RegEncoding.zero + β • qs.ket (flipBit q RegEncoding.zero)))) r
      = (‖α‖ ^ 2 + ‖β‖ ^ 2) * recordProb ((orderFindingSemiclassical inst.a inst.N
        (referenceControl P inst ℓ) m (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace).eval
        (MState.init (qs.ket RegEncoding.zero))) r :=
  orderFindingSemiclassical_recordProb_superpose _ _ _ m _ _ _ _ _ _ _
    (model_exponent_tail_unnamed P inst ℓ q hq).1 α β r

/-- **T5, lowered circuit, model.** The same for the lowered circuit, every admissible
policy. -/
theorem model_lowered_superpose_exponent (P : ShorLoweringPolicy) (hP : P.Admissible)
    (inst : ShorOrderFindingInstance) (ℓ m : ℕ) (q : ℕ) (hq : q ∈ (RL).x.active.qubits.tail)
    (α β : ℂ) (r : Record) :
    recordProb ((orderFindingSemiclassicalLow P inst.a inst.N (referenceControl P inst ℓ) m
        (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace
        (referenceSemiclassicalWorkspaceOK P inst ℓ m)).eval
        (MState.init (α • qs.ket RegEncoding.zero + β • qs.ket (flipBit q RegEncoding.zero)))) r
      = (‖α‖ ^ 2 + ‖β‖ ^ 2) * recordProb ((orderFindingSemiclassicalLow P inst.a inst.N
        (referenceControl P inst ℓ) m (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace
        (referenceSemiclassicalWorkspaceOK P inst ℓ m)).eval
        (MState.init (qs.ket RegEncoding.zero))) r :=
  orderFindingSemiclassicalLow_recordProb_superpose hP _ _ _ m _ _ _ _ _ _ _
    (referenceSemiclassicalSetup P inst ℓ).layout _ (referenceSemiclassicalCleanInput P inst ℓ)
    (model_reference_scratch_zero P inst ℓ) (model_exponent_tail_unnamed P inst ℓ q hq).1 α β r

end Model
end Shor

#print axioms Shor.Model.model_exponent_tail_mem_x_ne_control
#print axioms Shor.Model.model_exponent_tail_unnamed
#print axioms Shor.Model.model_x_width_ge_three
#print axioms Shor.Model.model_tail_ne_nil
#print axioms Shor.Model.model_flipBits_tail_ne_zero
#print axioms Shor.Model.model_reference_scratch_zero
#print axioms Shor.Model.model_real_superpose_exponent
#print axioms Shor.Model.model_lowered_superpose_exponent
#print axioms Shor.Model.model_flipBits_tail_bits
#print axioms Shor.Model.model_real_flip_exponent
#print axioms Shor.Model.model_lowered_flip_exponent
#print axioms Shor.Model.model_lowered_success_flip_exponent
#print axioms Shor.Model.model_ideal_flip_exponent
