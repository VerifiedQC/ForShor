import ForShor.ShorVerification.Implementation.Readout.Proofs.Deferred

/-!
# Readout: worked instances of `round_branch` and `deferred_measurement`

Non-vacuity checks for `Readout/Proofs/Deferred.lean`, for an arbitrary
quantum semantics with the classes named in each statement:

* `deferred_measurement_cnot`: the deferred-measurement lemma instantiated
  with `U false = id`, `U true = X t` and `CU = CNOT q t` (`q ≠ t`); its
  hypotheses are discharged, not assumed, and the two branching states are equal.
* `deferred_measurement_wrong_U_differs`: with the wrong pair (`id`, `id`) the
  two sides differ on a concrete run, so the conclusion is not automatic.
* `controlledOn_CNOT`: `CNOT c t` (`c ≠ t`) is `ControlledOn c`, so
  `round_branch_of_controlledOn` applies to a real gate.
* `round_zero_CNOT_ket_zero`: round 0 with `U = CNOT c t`, run from the
  all-zero ket, has the two children `(1/2)(|0…0⟩ ± |t = 1⟩)`.
-/

namespace Shor
namespace Readout
namespace DeferredTests

open MeasureClass

variable {qs : QSemantics} [RegEncoding qs.Basis]
  [GateSemanticsCore qs] [LowerGateClass qs] [MeasureClass qs]

omit [LowerGateClass qs] [MeasureClass qs] in
/-- `CNOT c t` (`c ≠ t`) on a basis ket: identity when bit `c` is `0`, `X t` when it is `1`. -/
theorem CNOT_ket [PauliXSemantics qs] [ClassicalReversibleSemantics qs]
    (c t : ℕ) (hct : c ≠ t) (x : qs.Basis) :
    qs.eval (Gate.CNOT c t) (qs.ket x)
      = if RegEncoding.bit c x then qs.eval (Gate.X t) (qs.ket x) else qs.ket x := by
  rw [ClassicalReversibleSemantics.eval_CNOT_ket, PauliXSemantics.eval_X_ket]
  unfold cnotBasis
  cases RegEncoding.bit c x <;> simp [hct]

/-- Deferred measurement with `U false = id`, `U true = X t`, `CU = CNOT q t`
(`q ≠ t`): measuring `q` and then flipping `t` on outcome `1` gives the same
branching state (every branch equal) as `CNOT q t` followed by measuring `q`.
All hypotheses of `deferred_measurement` are discharged here. -/
theorem deferred_measurement_cnot [PauliXSemantics qs] [ClassicalReversibleSemantics qs]
    (q t : ℕ) (hqt : q ≠ t) (ψ : MState qs) :
    condOnLast (fun b => if b then Gate.X t else Gate.id) ((MGate.measureReset q).eval ψ)
      = (MGate.seq (.unitary (Gate.CNOT q t)) (.measureReset q)).eval ψ := by
  refine deferred_measurement q _ (Gate.CNOT q t) (fun φ => ?_) (fun b o φ => ?_) (fun b φ => ?_) ψ
  · refine linearMap_ext_ket (gateL (Gate.CNOT q t))
      (gateL Gate.id ∘ₗ (measProj (qubitReg q) 0).toLinearMap
        + gateL (Gate.X t) ∘ₗ (measProj (qubitReg q) 1).toLinearMap) (fun x => ?_) φ
    simp only [gateL_apply, LinearMap.add_apply, LinearMap.comp_apply,
      ContinuousLinearMap.coe_coe, measProj_qubitReg_ket, CNOT_ket q t hqt]
    cases RegEncoding.bit q x <;>
      simp [GateSemanticsCore.eval_id, MGate.gate_eval_zero_state]
  · cases b
    · simp [GateSemanticsCore.eval_id]
    · simp only [ite_true]
      refine linearMap_ext_ket ((measProj (qubitReg q) o).toLinearMap ∘ₗ gateL (Gate.X t))
        (gateL (Gate.X t) ∘ₗ (measProj (qubitReg q) o).toLinearMap) (fun x => ?_) φ
      simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, gateL_apply,
        PauliXSemantics.eval_X_ket, measProj_qubitReg_ket]
      have hqt' : q ∉ (qubitReg t).qubits := by simpa [mem_qubitReg] using hqt
      rw [RegEncoding.bit_writeNat_out _ _ _ _ hqt']
      rw [apply_ite (qs.eval (Gate.X t)), PauliXSemantics.eval_X_ket, MGate.gate_eval_zero_state]
  · cases b
    · simp [GateSemanticsCore.eval_id]
    · simp only [ite_true]
      have hqt' : q ∉ (qubitReg t).qubits := by simpa [mem_qubitReg] using hqt
      have htq' : t ∉ (qubitReg q).qubits := by simpa [mem_qubitReg] using hqt.symm
      have hdisj : Disjoint (qubitReg q) (qubitReg t) := by
        simp [Disjoint, qubitReg, Reg.singleton, hqt.symm]
      refine linearMap_ext_ket (gateL (Gate.X q) ∘ₗ gateL (Gate.X t))
        (gateL (Gate.X t) ∘ₗ gateL (Gate.X q)) (fun x => ?_) φ
      simp only [LinearMap.comp_apply, gateL_apply, PauliXSemantics.eval_X_ket]
      rw [RegEncoding.bit_writeNat_out _ _ _ _ hqt', RegEncoding.bit_writeNat_out _ _ _ _ htq',
        writeNat_comm_of_disjoint (qubitReg q) (qubitReg t) hdisj]

/-- The conclusion of `deferred_measurement` is not automatic: with the WRONG
conditioned pair (`U b = id` for both outcomes) against `CU = CNOT q t`
(`q ≠ t`), the two sides differ, on the run from the ket `|q = 1, rest 0⟩`
(at record `[true]` the left side has `t = 0`, the right side `t = 1`). -/
theorem deferred_measurement_wrong_U_differs [PauliXSemantics qs]
    [ClassicalReversibleSemantics qs] (q t : ℕ) (hqt : q ≠ t) :
    condOnLast (fun _ => Gate.id) ((MGate.measureReset q).eval
        (MState.init (qs.ket (RegEncoding.writeNat (qubitReg q) 1 RegEncoding.zero))))
      ≠ (MGate.seq (.unitary (Gate.CNOT q t)) (.measureReset q)).eval
        (MState.init (qs.ket (RegEncoding.writeNat (qubitReg q) 1 RegEncoding.zero))) := by
  set x1 : qs.Basis := RegEncoding.writeNat (qubitReg q) 1 RegEncoding.zero with hx1
  have hqt' : q ∉ (qubitReg t).qubits := by simpa [mem_qubitReg] using hqt
  have hx1q : RegEncoding.bit q x1 = true := by
    rw [hx1, bit_qubitReg_writeNat _ _ _ (by norm_num)]; rfl
  have hx1t : RegEncoding.bit t x1 = false := by
    have htq' : t ∉ (qubitReg q).qubits := by simpa [mem_qubitReg] using hqt.symm
    rw [hx1, RegEncoding.bit_writeNat_out _ _ _ _ htq', RegEncoding.bit_zero]
  set x2 : qs.Basis := RegEncoding.writeNat (qubitReg t) 1 x1 with hx2
  have hx2q : RegEncoding.bit q x2 = true := by
    rw [hx2, RegEncoding.bit_writeNat_out _ _ _ _ hqt', hx1q]
  have hx2t : RegEncoding.bit t x2 = true := by
    rw [hx2, bit_qubitReg_writeNat _ _ _ (by norm_num)]; rfl
  have hC : qs.eval (Gate.CNOT q t) (qs.ket x1) = qs.ket x2 := by
    rw [CNOT_ket q t hqt, hx1q]
    simp only [ite_true]
    rw [PauliXSemantics.eval_X_ket, hx1t]; rfl
  intro h
  have h1 := congrFun h ([] ++ [true])
  simp only [condOnLast, MGate.eval_seq, MGate.eval_unitary, MGate.eval_measureReset_append,
    MState.init, ite_true, measureResetBranch] at h1
  have h2 := congrArg (qs.eval (Gate.X q)) h1
  have hid : ∀ φ : qs.State, qs.eval Gate.id φ = φ := GateSemanticsCore.eval_id
  rw [hid] at h2
  rw [gate_X_X, gate_X_X, hC, measProj_qubitReg_ket, measProj_qubitReg_ket, hx1q, hx2q] at h2
  simp only [ite_true] at h2
  have h3 := congrArg (RegEncoding.bit t) (qs.ket_inj h2)
  rw [hx1t, hx2t] at h3
  exact Bool.false_ne_true h3

omit [LowerGateClass qs] in
/-- `CNOT c t` with `c ≠ t` is a `c`-controlled gate in the sense of `ControlledOn`. -/
theorem controlledOn_CNOT [PauliXSemantics qs] [ClassicalReversibleSemantics qs]
    (c t : ℕ) (hct : c ≠ t) : ControlledOn (qs := qs) c (Gate.CNOT c t) := by
  refine ⟨fun ψ => ?_, fun ψ => ?_⟩
  · refine linearMap_ext_ket (gateL (Gate.CNOT c t) ∘ₗ (measProj (qubitReg c) 0).toLinearMap)
      (measProj (qubitReg c) 0).toLinearMap (fun x => ?_) ψ
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, gateL_apply,
      measProj_qubitReg_ket]
    cases hx : RegEncoding.bit c x
    · simp [CNOT_ket c t hct, hx]
    · simp [MGate.gate_eval_zero_state]
  · refine linearMap_ext_ket
      ((measProj (qubitReg c) 1).toLinearMap ∘ₗ gateL (Gate.CNOT c t) ∘ₗ
        (measProj (qubitReg c) 1).toLinearMap)
      (gateL (Gate.CNOT c t) ∘ₗ (measProj (qubitReg c) 1).toLinearMap) (fun x => ?_) ψ
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, gateL_apply,
      measProj_qubitReg_ket]
    cases hx : RegEncoding.bit c x
    · simp [MGate.gate_eval_zero_state]
    · have hct' : c ∉ (qubitReg t).qubits := by simpa [mem_qubitReg] using hct
      simp only [ite_true, CNOT_ket c t hct, hx, PauliXSemantics.eval_X_ket,
        measProj_qubitReg_ket, RegEncoding.bit_writeNat_out _ _ _ _ hct']

/-- Round 0 with `U = CNOT c t` (`c ≠ t`), run from the all-zero ket: the child
at record `[b]` is `(1/2) • (|0…0⟩ + (-1)^b • |0…0 with qubit t = 1⟩)`. -/
theorem round_zero_CNOT_ket_zero [HadamardSemantics qs] [PauliXSemantics qs]
    [ClassicalReversibleSemantics qs] (c t : ℕ) (hct : c ≠ t) (b : Bool) :
    (readoutRound c (Gate.CNOT c t) 0).eval (MState.init (qs.ket RegEncoding.zero)) [b]
      = (1 / 2 : ℂ) • (qs.ket RegEncoding.zero
          + outcomeSign b • qs.ket (RegEncoding.writeNat (qubitReg t) 1 RegEncoding.zero)) := by
  set z : qs.Basis := RegEncoding.zero
  have hz : ∀ q, RegEncoding.bit q z = false := RegEncoding.bit_zero
  have hφ : measProj (qubitReg c) 0 (MState.init (qs.ket z) []) = MState.init (qs.ket z) [] := by
    simp [MState.init, measProj_qubitReg_ket, hz]
  rw [show [b] = ([] : Record) ++ [b] from rfl,
    round_branch_of_controlledOn c _ (controlledOn_CNOT c t hct) 0 _ [] b hφ]
  have hT : uncontrolledAction c (Gate.CNOT c t) (qs.ket z)
      = qs.ket (RegEncoding.writeNat (qubitReg t) 1 z) := by
    have hct' : c ∉ (qubitReg t).qubits := by simpa [mem_qubitReg] using hct
    have htc' : t ∉ (qubitReg c).qubits := by simpa [mem_qubitReg] using hct.symm
    unfold uncontrolledAction
    rw [PauliXSemantics.eval_X_ket, hz, CNOT_ket c t hct]
    simp only [Bool.false_eq_true, ite_false]
    rw [bit_qubitReg_writeNat _ _ _ (by norm_num)]
    simp only [decide_true, ite_true]
    rw [PauliXSemantics.eval_X_ket, PauliXSemantics.eval_X_ket,
      RegEncoding.bit_writeNat_out _ _ _ _ htc', hz]
    simp only [Bool.false_eq_true, ite_false]
    rw [RegEncoding.bit_writeNat_out _ _ _ _ hct', bit_qubitReg_writeNat _ _ _ (by norm_num)]
    simp only [decide_true, ite_true]
    have hdisj : Disjoint (qubitReg c) (qubitReg t) := by
      simp [Disjoint, qubitReg, Reg.singleton, hct.symm]
    rw [writeNat_comm_of_disjoint (qubitReg c) (qubitReg t) hdisj,
      writeNat_qubitReg_writeNat _ _ _ _ (by norm_num) (by norm_num)]
    have h0 := writeNat_qubitReg_self c z
    rw [hz] at h0
    simp only [Bool.false_eq_true, ite_false] at h0
    rw [h0]
  simp only [MState.init, ite_true, hT]
  simp [ffAngle]

end DeferredTests
end Readout
end Shor
