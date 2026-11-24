import ForShor.ShorVerification.Model.Standard.LowGates
import ForShor.ShorVerification.Framework.Semantics.MSemanticsTests
import ForShor.ShorVerification.Implementation.Readout.Proofs.DeferredTests
import ForShor.ShorVerification.Implementation.Readout.Tests
import ForShor.ShorVerification.Implementation.Readout.Proofs.ApproxTests
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# `MGate` semantics in the standard model

The measurement language `MGate` (`Framework/AbstractMachine/MGate.lean`,
`Framework/Semantics/MSemantics.lean`) is evaluated under the classes
`GateSemanticsCore`, `LowerGateClass`, `MeasureClass` and, for its reset laws,
`PauliXSemantics`. This file checks that all four resolve at the concrete model
`Model.qs` (so the hypotheses of the `MGate` theorems are jointly satisfiable),
and specialises to it:

* conservation of probability (`mgate_eval_init_hasSum`) and the reset law
  (`mgate_measureReset_resets`);
* the measurement non-vacuity checks: the all-zero ket reads `0`
  (`mgate_measureReset_ket_zero`), the ket with qubit `q` flipped reads `1`
  (`mgate_measureReset_ket_one`), and the feed-forward phase acts (`ffPhase_acts`);
* the readout-round instances (after checking that `HadamardSemantics`,
  `ClassicalReversibleSemantics` and `IdealCtrlModMulExactSemantics` resolve too):
  deferred measurement with `CNOT` (`mgate_deferred_measurement_cnot`) and its
  negative instance (`mgate_deferred_measurement_wrong_U_differs`), and round 0
  with `U = CNOT c t` (`mgate_round_zero_CNOT_ket_zero`);
* `semiclassical_eq_iqft_model`: `semiclassical_eq_iqft` at `a = 2`, `N = 3`, two
  exponent qubits, so its class and register hypotheses hold together;
* the approximate-gate bound of `Readout/Proofs/ApproxTests.lean` at the same setting
  (`approx_init_hyps_model`, `semiclassical_shifted_phase_bound_model` with a real
  perturbation, `semiclassical_exact_gates_model` with zero error).

Nothing outside this folder uses it. The file imports the `Tests` modules (`MSemanticsTests`,
`Readout.Tests`, `Readout.Proofs.DeferredTests`, `Readout.Proofs.ApproxTests`) because its
examples instantiate the lemmas stated there at `Model.qs`; those lemmas are the tests'
own, so there is no non-test leaf to import instead.
-/

namespace Shor
namespace Model

/-- Every class `MGate.eval` and its laws need resolves at `Model.qs`. -/
noncomputable example : GateSemanticsCore qs := inferInstance
noncomputable example : LowerGateClass qs := inferInstance
noncomputable example : MeasureClass qs := inferInstance
noncomputable example : PauliXSemantics qs := inferInstance

/-- Conservation of probability for every `MGate` program, in the model. -/
theorem mgate_eval_init_hasSum (P : MGate) (ψ₀ : qs.State) :
    HasSum (recordProb (P.eval (MState.init ψ₀))) (‖ψ₀‖ ^ 2) :=
  MGate.eval_init_hasSum P ψ₀

/-- Measuring any qubit of the model's all-zero ket reads `0` with probability `1`. -/
theorem mgate_measureReset_ket_zero (q : ℕ) :
    recordProb ((MGate.measureReset q).eval (MState.init (qs.ket RegEncoding.zero))) [false]
      = 1 :=
  MSemanticsTests.measureReset_init_ket_zero q

/-- After `measureReset q`, qubit `q` is `|0⟩` in every branch, in the model. -/
theorem mgate_measureReset_resets (q : ℕ) (ψ : MState qs) (r : Record) :
    MeasureClass.measProj (qubitReg q) 0 ((MGate.measureReset q).eval ψ r)
      = (MGate.measureReset q).eval ψ r :=
  MSemanticsTests.measureReset_resets q ψ r

/-- Measuring qubit `q` of the model's ket with qubit `q` flipped to `1`
(`X q |0…0⟩`) reads `1` with probability `1`. -/
theorem mgate_measureReset_ket_one (q : ℕ) :
    recordProb ((MGate.measureReset q).eval
        (MState.init (qs.eval (Gate.X q) (qs.ket RegEncoding.zero)))) [true] = 1 := by
  rw [recordProb, show [true] = ([] : Record) ++ [true] from rfl, MGate.eval_measureReset_append]
  simp only [measureResetBranch, MState.init, ite_true]
  rw [norm_eval_gate, PauliXSemantics.eval_X_ket, RegEncoding.bit_zero,
    Readout.measProj_qubitReg_ket, Readout.bit_qubitReg_writeNat _ _ _ (by norm_num)]
  simp only [Bool.false_eq_true, ite_false, decide_true, ite_true]
  rw [ket_norm_one]
  norm_num

/-- The feed-forward phase acts: in round 1 after outcome `1` the angle is
`-1/2` (units of `π`), `ffPhase q 1` applies `Phase q (-1/2)` to that branch,
and that phase moves the model's ket with qubit `q` set to `1` (it multiplies
it by `exp(-iπ/2) = -i`), so the step is not the identity. -/
theorem ffPhase_acts (q : ℕ) (ψ : MState qs) :
    ffAngle 1 [true] = -1 / 2 ∧
    (MGate.ffPhase q 1).eval ψ [true]
      = LowerGateClass.evalL (LowGate.Phase q (-1 / 2)) (ψ [true]) ∧
    LowerGateClass.evalL (LowGate.Phase q (-1 / 2))
        (qs.ket (RegEncoding.writeNat (qubitReg q) 1 RegEncoding.zero))
      ≠ qs.ket (RegEncoding.writeNat (qubitReg q) 1 RegEncoding.zero) := by
  have h1 : ffAngle 1 [true] = -1 / 2 := by norm_num [ffAngle]
  refine ⟨h1, by rw [MGate.eval_ffPhase, h1], ?_⟩
  set y : qs.Basis := RegEncoding.writeNat (qubitReg q) 1 RegEncoding.zero
  have hy : RegEncoding.bit q y = true := by
    rw [Readout.bit_qubitReg_writeNat _ _ _ (by norm_num)]; rfl
  have he : Complex.exp (((Angle.toReal (-1 / 2) : ℝ) : ℂ) * Complex.I) = -Complex.I := by
    rw [Complex.exp_mul_I, Angle.toReal]
    push_cast
    rw [show (-1 / 2 : ℂ) * Real.pi = -((Real.pi : ℂ) / 2) by ring, Complex.cos_neg,
      Complex.sin_neg, Complex.cos_pi_div_two, Complex.sin_pi_div_two]
    ring
  rw [LowerGateClass.evalL_Phase_ket]
  simp only [hy, ite_true]
  rw [he]
  intro h
  have h0 : (-Complex.I - 1) • qs.ket y = 0 := by rw [sub_smul, h, one_smul, sub_self]
  rcases smul_eq_zero.1 h0 with h0 | h0
  · have := congrArg Complex.re h0
    simp at this
  · exact qs.ket_ne_zero y h0

/-- The extra classes the readout round and its tests need also resolve at
`Model.qs`. -/
noncomputable example : HadamardSemantics qs := inferInstance
noncomputable example : ClassicalReversibleSemantics qs := inferInstance
example : IdealCtrlModMulExactSemantics qs := inferInstance

/-- Deferred measurement with `U false = id`, `U true = X t`, `CU = CNOT q t`,
in the model: the two orders give equal branching states. -/
theorem mgate_deferred_measurement_cnot (q t : ℕ) (hqt : q ≠ t) (ψ : MState qs) :
    Readout.condOnLast (fun b => if b then Gate.X t else Gate.id)
        ((MGate.measureReset q).eval ψ)
      = (MGate.seq (.unitary (Gate.CNOT q t)) (.measureReset q)).eval ψ :=
  Readout.DeferredTests.deferred_measurement_cnot q t hqt ψ

/-- In the model, the wrong conditioned pair (`id` on both outcomes) does not
reproduce `CNOT q t` followed by measuring `q`. -/
theorem mgate_deferred_measurement_wrong_U_differs (q t : ℕ) (hqt : q ≠ t) :
    Readout.condOnLast (fun _ => Gate.id) ((MGate.measureReset q).eval
        (MState.init (qs.ket (RegEncoding.writeNat (qubitReg q) 1 RegEncoding.zero))))
      ≠ (MGate.seq (.unitary (Gate.CNOT q t)) (.measureReset q)).eval
        (MState.init (qs.ket (RegEncoding.writeNat (qubitReg q) 1 RegEncoding.zero))) :=
  Readout.DeferredTests.deferred_measurement_wrong_U_differs q t hqt

/-- One readout round in the model: round 0 with `U = CNOT c t` from the
all-zero ket has the children `(1/2)(|0…0⟩ ± |t = 1⟩)`. -/
theorem mgate_round_zero_CNOT_ket_zero (c t : ℕ) (hct : c ≠ t) (b : Bool) :
    (Readout.readoutRound c (Gate.CNOT c t) 0).eval (MState.init (qs.ket RegEncoding.zero)) [b]
      = (1 / 2 : ℂ) • (qs.ket RegEncoding.zero
          + Readout.outcomeSign b • qs.ket (RegEncoding.writeNat (qubitReg t) 1 RegEncoding.zero)) :=
  Readout.DeferredTests.round_zero_CNOT_ket_zero c t hct b

/-- `semiclassical_eq_iqft` instantiated in the model (non-vacuity of the class
and register hypotheses together): `a = 2`, `N = 3`, exponent register on
qubits `[0, 1]` (two rounds), data on `[2, 3]`, control qubit `4`, initial ket
`|data = 1⟩` built from the all-zero ket. -/
theorem semiclassical_eq_iqft_model (o : ℕ) :
    let x : ExtReg := ExtReg.ofReg ⟨[0, 1], by decide⟩
    let data : Reg := ⟨[2, 3], by decide⟩
    let b₀ : qs.Basis := RegEncoding.writeNat data 1 RegEncoding.zero
    (∑' r : Record, if r.length = regSize x.active ∧ readoutOfRecord r = o then
        recordProb ((semiclassicalIdeal 2 3 (regSize x.active) data 4).eval
          (MState.init (qs.ket b₀))) r else 0)
      = MeasureClass.probMeas x.active o
          (qs.eval (H_reg x.active ;; modExpIdeal' qs 2 3 x.active data ;; IQFT x)
            (qs.ket b₀)) := by
  intro x data b₀
  obtain ⟨h4, hdisj, hN, hsize, hx0, hd1, hc0⟩ := ReadoutTests.hyps_satisfiable (qs := qs)
  exact semiclassical_eq_iqft 2 3 x data 4 b₀ hN hsize (by norm_num) h4 hdisj hx0 hd1 hc0 o

/-- The initial ket of `semiclassical_eq_iqft_model` (`data = [2, 3]` holds `1`,
control qubit `4` is `0`) lies in `InRangeOn 4 data 3 (fun _ => True)` and has
norm `1`: the initial-state hypotheses of `semiclassical_dist_le_sum_errors`
hold in the model. -/
theorem approx_init_hyps_model :
    let data : Reg := ⟨[2, 3], by decide⟩
    let b₀ : qs.Basis := RegEncoding.writeNat data 1 RegEncoding.zero
    Readout.InRangeOn 4 data 3 (fun _ => True) (qs.ket b₀) ∧ ‖qs.ket b₀‖ = 1 := by
  intro data b₀
  obtain ⟨-, -, -, -, -, hd1, hc0⟩ := ReadoutTests.hyps_satisfiable (qs := qs)
  exact ⟨Submodule.subset_span ⟨b₀, ⟨hc0, by rw [hd1]; norm_num, trivial⟩, rfl⟩, ket_norm_one qs b₀⟩

/-- **Approximate-gate bound in the model, with a real perturbation.** `a = 2`,
`N = 3`, data on `[2, 3]`, control qubit `4`, two rounds, initial ket
`|data = 1⟩`; multipliers exact, every feed-forward phase replaced by
`Phase 4 (ffAngle j r + 1/8)` (a phase error of `π/8`). All hypotheses of
`semiclassical_dist_le_sum_errors` are discharged, and the `ℓ¹` distance
`∑|p - q|` between the implemented and ideal record distributions is at most
`π/2 < 2` (the trivial `ℓ¹` bound); in `TV = ½ · ℓ¹` terms `TV ≤ π/4`. -/
theorem semiclassical_shifted_phase_bound_model :
    let data : Reg := ⟨[2, 3], by decide⟩
    let b₀ : qs.Basis := RegEncoding.writeNat data 1 RegEncoding.zero
    (∑' r : Record,
        |recordProb (Readout.semiclassicalImpl 4 (Readout.schedule 2 3 2 data 4)
            (Readout.ApproxTests.shiftedPhase 4 (1 / 8)) 2 (MState.init (qs.ket b₀))) r
          - recordProb ((semiclassicalIdeal 2 3 2 data 4).eval (MState.init (qs.ket b₀))) r|)
      ≤ Real.pi / 2 ∧ Real.pi / 2 < 2 := by
  intro data b₀
  obtain ⟨h4, -, hN, hsize, -, -, -⟩ := ReadoutTests.hyps_satisfiable (qs := qs)
  obtain ⟨hψ, hnorm⟩ := approx_init_hyps_model
  obtain ⟨h1, h2⟩ := Readout.ApproxTests.semiclassical_shifted_phase_bound 2 3 2 data 4
    (fun _ => True) hN hsize (by norm_num) h4 (fun _ _ _ => trivial) (fun _ _ _ => trivial)
    (qs.ket b₀) hψ hnorm (1 / 8)
  have h8 : ((1 / 8 : Angle) : ℝ) = 1 / 8 := by norm_num
  rw [h8] at h2
  refine ⟨h1.trans (h2.trans_eq ?_), by linarith [Real.pi_lt_four]⟩
  norm_num
  ring

/-- **Zero error in the model.** With the exact gates, the implemented readout
of `semiclassical_shifted_phase_bound_model`'s setting has exactly the ideal
record distribution (`bound_at_zero_is_equality` at `Model.qs`). -/
theorem semiclassical_exact_gates_model (r : Record) :
    let data : Reg := ⟨[2, 3], by decide⟩
    let b₀ : qs.Basis := RegEncoding.writeNat data 1 RegEncoding.zero
    recordProb (Readout.semiclassicalImpl 4 (Readout.schedule 2 3 2 data 4)
        (fun j => Readout.exactPhase 4 j) 2 (MState.init (qs.ket b₀))) r
      = recordProb ((semiclassicalIdeal 2 3 2 data 4).eval (MState.init (qs.ket b₀))) r := by
  intro data b₀
  obtain ⟨h4, -, hN, hsize, -, -, -⟩ := ReadoutTests.hyps_satisfiable (qs := qs)
  obtain ⟨hψ, hnorm⟩ := approx_init_hyps_model
  exact (Readout.ApproxTests.bound_at_zero_is_equality 2 3 2 data 4 (fun _ => True) hN hsize
    (by norm_num) h4 (fun _ _ _ => trivial) (fun _ _ _ => trivial) (qs.ket b₀) hψ hnorm).2.1 r

end Model
end Shor
