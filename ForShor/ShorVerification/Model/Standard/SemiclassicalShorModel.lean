import ForShor.ShorVerification.Model.Standard.LowGates
import ForShor.ShorVerification.Implementation.Readout.Shor
import ForShor.ShorVerification.Implementation.Readout.Support
import ForShor.ShorVerification.Implementation.Reference.Standard.Proofs.Readiness
import ForShor.ShorVerification.Implementation.Readout.Proofs.ReferenceLayout

/-!
# Semiclassical order finding in the standard model

Non-vacuity of the success theorems of `Implementation/Readout/Shor.lean` at the
concrete model `Model.qs`: for EVERY lowering policy `P`, order-finding instance
`inst` and precision level `ℓ`, the reference layout of `Implementation/Reference/`
(all-zero start ket, exponent register of width `log₂(2N²)`, data of width
`log₂(2N)`) with the control `c` = its first exponent qubit satisfies every
hypothesis (`referenceSemiclassicalSetup`, through
`ShorApproxSetup.toSemiclassicalShorSetup`), so:

* `model_semiclassical_start`: the start ket `initY1 |0…0⟩` has `x = 0`,
  data `= 1`, control `0`, the side condition, and is a unit vector in
  `InRangeOn`;
* `model_semiclassical_avoids_exponent`: the circuit names no qubit of the
  reference exponent register except the control `c` (its first qubit): the
  other `log₂(2N²) - 1` exponent qubits are not used;
* `model_Shor_correct_semiclassical`: the bound
  `κ / log(log₂ N + 1) - 2 m √(2 · 1600 · η)` holds for the circuit;
* `model_Shor_correct_semiclassical_at_shorPrecision`: some level `ℓ` has
  `η = referencePrecision ℓ ≤ shorPrecision N x`, and there the success
  probability is `≥ κ / (2 log(log₂ N + 1))`, a positive number.
-/

namespace Shor
namespace Model

open Reference Readout

/-- **The semiclassical hypotheses hold at the reference layout** in the model,
from the all-zero ket, with `c = referenceControl`. -/
noncomputable def referenceSemiclassicalSetup (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (ℓ : ℕ) :
    SemiclassicalShorSetup qs (referencePrecision ℓ) inst.N (referenceControl P inst ℓ)
      (allocateReferenceLayout P inst ℓ).x (allocateReferenceLayout P inst ℓ).data
      (allocateReferenceLayout P inst ℓ).work (allocateReferenceLayout P inst ℓ).scratch
      (allocateReferenceLayout P inst ℓ).flag (RegEncoding.zero (Basis := qs.Basis)) :=
  (referenceApproxSetup (qs := qs) P inst ℓ).toSemiclassicalShorSetup (referenceX_pos P inst ℓ)

/-- **Start state in the model.** At the reference layout, `initY1` maps the
all-zero ket to `b1 = |0…0 with data := 1⟩`, and `b1` has `x = 0`, data `= 1`,
control `0`, the side condition, and `|b1⟩` is a unit vector in `InRangeOn`. -/
theorem model_semiclassical_start (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (ℓ : ℕ) :
    let L := allocateReferenceLayout P inst ℓ
    let b1 := semiclassicalStartKet (qs := qs) L.data RegEncoding.zero
    qs.eval (initY1 L.data.active) (qs.ket RegEncoding.zero) = qs.ket b1 ∧
    RegEncoding.toNat L.x.active b1 = 0 ∧ RegEncoding.toNat L.data.active b1 = 1 ∧
    RegEncoding.bit (referenceControl P inst ℓ) b1 = false ∧
    semiclassicalSide L.data L.work L.scratch L.flag b1 ∧
    InRangeOn (referenceControl P inst ℓ) L.data.active inst.N
      (semiclassicalSide L.data L.work L.scratch L.flag) (qs.ket b1) ∧
    ‖qs.ket b1‖ = 1 := by
  intro L b1
  have hN : 2 ≤ inst.N := by have := inst.range; omega
  have hn : regSize L.data.active = Nat.log2 (2 * inst.N) := by simp [L]
  have hNy : inst.N ≤ ASize L.data.active := by
    simpa [ASize, hn] using shor_data_capacity_from_log2 inst.N
  have h := referenceSemiclassicalSetup P inst ℓ
  exact ⟨eval_initY1_start L.data _ (regSize_pos_of_log2 inst.N hN _ hn) h.clean_input.2.1,
    semiclassical_start h (by omega) hNy⟩

/-- **The exponent register is gone, in the model.** On the reference layout the
semiclassical circuit (any number of rounds `m`) names no qubit of the exponent
register `x.active` other than the control `referenceControl` (= `x.active[0]`). -/
theorem model_semiclassical_avoids_exponent (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (ℓ m : ℕ) :
    let L := allocateReferenceLayout P inst ℓ
    ∀ q ∈ L.x.active.qubits, q ≠ referenceControl P inst ℓ →
      q ∉ (orderFindingSemiclassical inst.a inst.N (referenceControl P inst ℓ) m
            L.data L.work L.scratch L.flag
            (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
            (referenceSemiclassicalSetup P inst ℓ).step4_workspace).qubitSupport := by
  intro L q hq hqc hsup
  exact exponent_outside_semiclassicalQubits (referenceApproxSetup (qs := qs) P inst ℓ) q hq hqc
    (orderFindingSemiclassical_support _ _ m _ _ hsup)

/-- **The success bound in the model**, for every policy, instance and level:
the circuit `orderFindingSemiclassical` with the real multipliers on the
reference layout, control `referenceControl`, run from the all-zero ket. -/
theorem model_Shor_correct_semiclassical (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (ℓ : ℕ) (T : ℕ → ℕ)
    (hT : ContinuedFractionSearchComplete T) :
    let L := allocateReferenceLayout P inst ℓ
    probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
        (regSize L.x.active) (ord inst.a inst.N inst.coprime) (ASize L.x.active)
        ((orderFindingSemiclassical inst.a inst.N (referenceControl P inst ℓ) (regSize L.x.active)
            L.data L.work L.scratch L.flag
            (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
            (referenceSemiclassicalSetup P inst ℓ).step4_workspace).eval
          (MState.init (qs.ket RegEncoding.zero)))
      ≥ κ / Real.log ((Nat.log2 inst.N : ℝ) + 1)
        - 2 * (regSize L.x.active : ℝ) * Real.sqrt (2 * (1600 * referencePrecision ℓ)) := by
  intro L
  exact Shor_correct_semiclassical_of_modMul_bound 1600 (modMul_approx_valid_dist_1600 qs) T hT
    inst _ L.x L.data L.work L.scratch L.flag _ (allocateReferenceLayout_x_width P inst ℓ)
    (allocateReferenceLayout_data_width P inst ℓ) _
    (referenceSemiclassicalSetup P inst ℓ)

/-- `shorPrecision N x` is positive when `N ≥ 2` and `x` is nonempty. -/
theorem shorPrecision_pos (N : ℕ) (hN : 2 ≤ N) (x : Reg) (hx : 0 < regSize x) :
    0 < shorPrecision N x := by
  have hlog : 0 < Nat.log2 N := by
    rw [Nat.log2_eq_log_two]; exact Nat.log_pos Nat.one_lt_two hN
  have hL : (0 : ℝ) < Real.log ((Nat.log2 N : ℝ) + 1) := by
    apply Real.log_pos
    have : (0 : ℝ) < (Nat.log2 N : ℝ) := by exact_mod_cast hlog
    linarith
  set t : ℝ := (regSize x : ℝ) with ht
  have htpos : 0 < t := by rw [ht]; exact_mod_cast hx
  set L := Real.log ((Nat.log2 N : ℝ) + 1)
  have hκ := κ_pos
  unfold shorPrecision
  rw [← ht]
  positivity

/-- **At `shorPrecision` in the model.** For every policy and instance there is
a precision level `ℓ` with `referencePrecision ℓ ≤ shorPrecision N x`, and at it
the semiclassical circuit on the reference layout succeeds with probability at
least `κ / (2 log(log₂ N + 1))`, which is positive. -/
theorem model_Shor_correct_semiclassical_at_shorPrecision (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T) :
    ∃ ℓ : ℕ, referencePrecision ℓ ≤ shorPrecision inst.N (allocateReferenceLayout P inst ℓ).x.active ∧
      probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
          (regSize (allocateReferenceLayout P inst ℓ).x.active) (ord inst.a inst.N inst.coprime)
          (ASize (allocateReferenceLayout P inst ℓ).x.active)
          ((orderFindingSemiclassical inst.a inst.N (referenceControl P inst ℓ)
              (regSize (allocateReferenceLayout P inst ℓ).x.active)
              (allocateReferenceLayout P inst ℓ).data (allocateReferenceLayout P inst ℓ).work
              (allocateReferenceLayout P inst ℓ).scratch (allocateReferenceLayout P inst ℓ).flag
              (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
              (referenceSemiclassicalSetup P inst ℓ).step4_workspace).eval
            (MState.init (qs.ket RegEncoding.zero)))
        ≥ κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1)) ∧
      0 < κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1)) := by
  -- `shorPrecision` does not depend on the level: the exponent register is `referenceXActive inst`.
  have hN2 : 2 ≤ inst.N := by have := inst.range; omega
  set s := shorPrecision inst.N (referenceXActive inst) with hs
  have hspos : 0 < s := shorPrecision_pos inst.N hN2 _ (by
    simpa using referenceX_pos P inst 0)
  obtain ⟨ℓ, hℓ⟩ := exists_nat_gt (1 / s)
  have hsame : shorPrecision inst.N (allocateReferenceLayout P inst ℓ).x.active = s := by
    rw [allocateReferenceLayout_x_active]
  have hprec : referencePrecision ℓ ≤ s := by
    unfold referencePrecision
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hspos] at hℓ
    nlinarith
  have hN : 2 ≤ inst.N := by have := inst.range; omega
  have hlog : 0 < Nat.log2 inst.N := by
    rw [Nat.log2_eq_log_two]; exact Nat.log_pos Nat.one_lt_two hN
  have hL : (0 : ℝ) < Real.log ((Nat.log2 inst.N : ℝ) + 1) := by
    apply Real.log_pos
    have : (0 : ℝ) < (Nat.log2 inst.N : ℝ) := by exact_mod_cast hlog
    linarith
  refine ⟨ℓ, hsame ▸ hprec, ?_, by have := κ_pos; positivity⟩
  exact Shor_correct_semiclassical_at_shorPrecision T hT inst _ _ _ _ _ _ _
    (allocateReferenceLayout_x_width P inst ℓ) (allocateReferenceLayout_data_width P inst ℓ) _
    (hsame ▸ hprec) (referenceSemiclassicalSetup P inst ℓ)

end Model
end Shor
