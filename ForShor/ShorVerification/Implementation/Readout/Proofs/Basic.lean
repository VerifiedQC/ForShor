import ForShor.ShorVerification.Framework.Semantics.MSemantics
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Registers

/-!
# Readout: single-qubit basis and state lemmas

Generic facts about one qubit `c` used by the readout proofs
(`Readout/Proofs/Deferred.lean`) and by later readout files: reading and
writing the one-qubit register `qubitReg c` on basis states, the Born
projectors of `c` on kets, gates and low-level gates as `ℂ`-linear maps
(`gateL`, `lowL`) with the ket-extensionality principle `linearMap_ext_ket`,
and the action of `X c`, `H c` and `Phase c θ` on the `c = 0` / `c = 1`
subspaces. All derived from the existing classes; no new axioms.
-/

namespace Shor
namespace Readout

open MeasureClass

variable {qs : QSemantics} [RegEncoding qs.Basis]
  [GateSemanticsCore qs] [LowerGateClass qs] [MeasureClass qs]


/-- The one-qubit register has width `1`. -/
theorem regSize_qubitReg (q : ℕ) : regSize (qubitReg q) = 1 := rfl

/-- The only qubit of `qubitReg q` is `q`. -/
theorem mem_qubitReg (q q' : ℕ) : q' ∈ (qubitReg q).qubits ↔ q' = q := by
  simp [qubitReg, Reg.singleton]

omit [GateSemanticsCore qs] [LowerGateClass qs] [MeasureClass qs] in
/-- Reading the one-qubit register `qubitReg q` gives the bit `q`. -/
theorem toNat_qubitReg (q : ℕ) (x : qs.Basis) :
    RegEncoding.toNat (qubitReg q) x = if RegEncoding.bit q x then 1 else 0 := by
  have hlt := RegEncoding.toNat_lt_ASize (qubitReg q) x
  have hbit := RegEncoding.bit_eq_testBit_toNat (qubitReg q) x ⟨0, by simp⟩
  change RegEncoding.bit q x = _ at hbit
  change _ < 2 at hlt
  rw [hbit]
  interval_cases RegEncoding.toNat (qubitReg q) x <;> simp

omit [GateSemanticsCore qs] [LowerGateClass qs] [MeasureClass qs] in
/-- Writing `v < 2` into `qubitReg q` sets bit `q` to `v = 1`. -/
theorem bit_qubitReg_writeNat (q v : ℕ) (x : qs.Basis) (hv : v < 2) :
    RegEncoding.bit q (RegEncoding.writeNat (qubitReg q) v x) = decide (v = 1) := by
  have hbit := RegEncoding.bit_eq_testBit_toNat (qubitReg q)
    (RegEncoding.writeNat (qubitReg q) v x) ⟨0, by simp⟩
  change RegEncoding.bit q _ = _ at hbit
  rw [hbit, RegEncoding.toNat_writeNat_of_lt _ _ _ (by simpa [ASize, regSize_qubitReg] using hv)]
  interval_cases v <;> simp

omit [GateSemanticsCore qs] [LowerGateClass qs] [MeasureClass qs] in
/-- Writing a qubit's own bit back leaves the basis state unchanged. -/
theorem writeNat_qubitReg_self (q : ℕ) (x : qs.Basis) :
    RegEncoding.writeNat (qubitReg q) (if RegEncoding.bit q x then 1 else 0) x = x := by
  refine RegEncoding.basis_ext _ _ (fun q' => ?_)
  by_cases h : q' = q
  · subst h
    rw [bit_qubitReg_writeNat _ _ _ (by split <;> omega)]
    cases RegEncoding.bit q' x <;> simp
  · exact RegEncoding.bit_writeNat_out _ _ _ _ (by simpa [mem_qubitReg] using h)

omit [GateSemanticsCore qs] [LowerGateClass qs] [MeasureClass qs] in
/-- Two writes to the same one-qubit register: the second wins. -/
theorem writeNat_qubitReg_writeNat (q v w : ℕ) (x : qs.Basis) (hv : v < 2) (_hw : w < 2) :
    RegEncoding.writeNat (qubitReg q) v (RegEncoding.writeNat (qubitReg q) w x)
      = RegEncoding.writeNat (qubitReg q) v x := by
  refine RegEncoding.basis_ext _ _ (fun q' => ?_)
  by_cases h : q' = q
  · subst h
    rw [bit_qubitReg_writeNat _ _ _ hv, bit_qubitReg_writeNat _ _ _ hv]
  · have h' : q' ∉ (qubitReg q).qubits := by simpa [mem_qubitReg] using h
    rw [RegEncoding.bit_writeNat_out _ _ _ _ h', RegEncoding.bit_writeNat_out _ _ _ _ h',
      RegEncoding.bit_writeNat_out _ _ _ _ h']

omit [GateSemanticsCore qs] [LowerGateClass qs] [MeasureClass qs] in
/-- A register's value depends only on the bits of its own qubits. -/
theorem toNat_eq_of_bits (r : Reg) {x x' : qs.Basis}
    (h : ∀ q ∈ r.qubits, RegEncoding.bit q x = RegEncoding.bit q x') :
    RegEncoding.toNat r x = RegEncoding.toNat r x' := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < regSize r
  · rw [← RegEncoding.bit_eq_testBit_toNat r x ⟨i, hi⟩,
      ← RegEncoding.bit_eq_testBit_toNat r x' ⟨i, hi⟩]
    exact h _ (List.getElem_mem _)
  · push Not at hi
    have l1 := RegEncoding.toNat_lt_ASize r x
    have l2 := RegEncoding.toNat_lt_ASize r x'
    rw [ASize] at l1 l2
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le l1 (Nat.pow_le_pow_right (by norm_num) hi)),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le l2 (Nat.pow_le_pow_right (by norm_num) hi))]

omit [GateSemanticsCore qs] [LowerGateClass qs] in
/-- The one-qubit Born projectors on a basis ket. -/
theorem measProj_qubitReg_ket (q o : ℕ) (x : qs.Basis) :
    measProj (qubitReg q) o (qs.ket x)
      = if (if RegEncoding.bit q x then 1 else 0) = o then qs.ket x else 0 := by
  rw [MeasureClass.measProj_ket, toNat_qubitReg]

omit [LowerGateClass qs] [MeasureClass qs] in
/-- A `Gate` as a `ℂ`-linear map. -/
noncomputable def gateL (U : Gate) : qs.State →ₗ[ℂ] qs.State where
  toFun := qs.eval U
  map_add' := GateSemanticsCore.eval_add U
  map_smul' := GateSemanticsCore.eval_smul U

omit [LowerGateClass qs] [MeasureClass qs] in
@[simp] theorem gateL_apply (U : Gate) (φ : qs.State) : gateL U φ = qs.eval U φ := rfl

omit [GateSemanticsCore qs] [MeasureClass qs] in
/-- A `LowGate` as a `ℂ`-linear map. -/
noncomputable def lowL (L : LowGate) : qs.State →ₗ[ℂ] qs.State where
  toFun := LowerGateClass.evalL L
  map_add' := LowerGateClass.evalL_add L
  map_smul' := LowerGateClass.evalL_smul L

omit [GateSemanticsCore qs] [MeasureClass qs] in
@[simp] theorem lowL_apply (L : LowGate) (φ : qs.State) :
    lowL L φ = LowerGateClass.evalL L φ := rfl

omit [RegEncoding qs.Basis] [GateSemanticsCore qs] [LowerGateClass qs] [MeasureClass qs] in
/-- Two linear maps that agree on every basis ket agree everywhere. -/
theorem linearMap_ext_ket (f g : qs.State →ₗ[ℂ] qs.State)
    (h : ∀ x, f (qs.ket x) = g (qs.ket x)) (φ : qs.State) : f φ = g φ := by
  refine qs.state_induction (fun φ => f φ = g φ) (by simp) ?_ ?_ h φ
  · intro a b ha hb; rw [map_add, map_add, ha, hb]
  · intro a b hb; rw [map_smul, map_smul, hb]

omit [LowerGateClass qs] [MeasureClass qs] in
/-- A gate is additive. -/
theorem gate_eval_add (U : Gate) (φ χ : qs.State) :
    qs.eval U (φ + χ) = qs.eval U φ + qs.eval U χ := (gateL U).map_add φ χ

omit [LowerGateClass qs] [MeasureClass qs] in
/-- A gate is `ℂ`-homogeneous. -/
theorem gate_eval_smul (U : Gate) (a : ℂ) (φ : qs.State) :
    qs.eval U (a • φ) = a • qs.eval U φ := (gateL U).map_smul a φ

omit [LowerGateClass qs] [MeasureClass qs] in
/-- A gate commutes with subtraction. -/
theorem gate_eval_sub (U : Gate) (φ χ : qs.State) :
    qs.eval U (φ - χ) = qs.eval U φ - qs.eval U χ := (gateL U).map_sub φ χ

omit [LowerGateClass qs] [MeasureClass qs] in
/-- A gate commutes with negation. -/
theorem gate_eval_neg (U : Gate) (φ : qs.State) :
    qs.eval U (-φ) = -qs.eval U φ := (gateL U).map_neg φ

/-- `1/√2 · 1/√2 = 1/2`. -/
theorem invSqrtTwo_mul_self :
    (1 / (Real.sqrt 2 : ℂ)) * (1 / (Real.sqrt 2 : ℂ)) = 1 / 2 := by
  rw [div_mul_div_comm, one_mul, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  push_cast; ring

omit [LowerGateClass qs] in
/-- `X c` maps a state with `c = 0` to one with `c = 1`. -/
theorem measProj_one_X_measProj_zero [PauliXSemantics qs] (c : ℕ) (φ : qs.State) :
    measProj (qubitReg c) 1 (qs.eval (Gate.X c) (measProj (qubitReg c) 0 φ))
      = qs.eval (Gate.X c) (measProj (qubitReg c) 0 φ) := by
  refine linearMap_ext_ket
    ((measProj (qubitReg c) 1).toLinearMap ∘ₗ gateL (Gate.X c) ∘ₗ
      (measProj (qubitReg c) 0).toLinearMap)
    (gateL (Gate.X c) ∘ₗ (measProj (qubitReg c) 0).toLinearMap) (fun x => ?_) φ
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, gateL_apply,
    measProj_qubitReg_ket]
  cases hx : RegEncoding.bit c x
  · simp only [Bool.false_eq_true, ite_true, ite_false]
    rw [PauliXSemantics.eval_X_ket, hx, measProj_qubitReg_ket,
      bit_qubitReg_writeNat _ _ _ (by norm_num)]
    simp
  · simp [MGate.gate_eval_zero_state]

omit [LowerGateClass qs] [MeasureClass qs] in
/-- `X c` is an involution. -/
theorem gate_X_X [PauliXSemantics qs] (c : ℕ) (φ : qs.State) :
    qs.eval (Gate.X c) (qs.eval (Gate.X c) φ) = φ := by
  refine linearMap_ext_ket (gateL (Gate.X c) ∘ₗ gateL (Gate.X c)) LinearMap.id
    (fun x => ?_) φ
  simp only [LinearMap.comp_apply, gateL_apply, LinearMap.id_apply,
    PauliXSemantics.eval_X_ket]
  have h0 := writeNat_qubitReg_self c x
  cases hx : RegEncoding.bit c x <;>
  · simp only [hx, Bool.false_eq_true, ite_true, ite_false] at h0 ⊢
    rw [bit_qubitReg_writeNat _ _ _ (by norm_num)]
    simp only [decide_true, decide_false, zero_ne_one, Bool.false_eq_true, ite_true, ite_false]
    rw [writeNat_qubitReg_writeNat _ _ _ _ (by norm_num) (by norm_num), h0]

omit [LowerGateClass qs] in
/-- `H c` on a state with `c = 0`: `H φ = (1/√2) • (φ + X c φ)`. -/
theorem H_measProj_zero [HadamardSemantics qs] [PauliXSemantics qs] (c : ℕ) (φ : qs.State) :
    qs.eval (Gate.H c) (measProj (qubitReg c) 0 φ)
      = (1 / (Real.sqrt 2 : ℂ)) • (measProj (qubitReg c) 0 φ
          + qs.eval (Gate.X c) (measProj (qubitReg c) 0 φ)) := by
  refine linearMap_ext_ket
    (gateL (Gate.H c) ∘ₗ (measProj (qubitReg c) 0).toLinearMap)
    ((1 / (Real.sqrt 2 : ℂ)) • ((measProj (qubitReg c) 0).toLinearMap
      + gateL (Gate.X c) ∘ₗ (measProj (qubitReg c) 0).toLinearMap)) (fun x => ?_) φ
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.add_apply,
    ContinuousLinearMap.coe_coe, gateL_apply, measProj_qubitReg_ket]
  cases hx : RegEncoding.bit c x
  · simp only [Bool.false_eq_true, ite_true, ite_false]
    rw [HadamardSemantics.eval_H_ket, PauliXSemantics.eval_X_ket, hx]
    have h0 := writeNat_qubitReg_self c x
    rw [hx] at h0
    simp only [Bool.false_eq_true, ite_false] at h0 ⊢
    rw [h0, one_smul]
  · simp [MGate.gate_eval_zero_state]

omit [LowerGateClass qs] in
/-- `H c` on `X c φ` with `φ` in `c = 0`: `H (X c φ) = (1/√2) • (φ - X c φ)`. -/
theorem H_X_measProj_zero [HadamardSemantics qs] [PauliXSemantics qs] (c : ℕ) (φ : qs.State) :
    qs.eval (Gate.H c) (qs.eval (Gate.X c) (measProj (qubitReg c) 0 φ))
      = (1 / (Real.sqrt 2 : ℂ)) • (measProj (qubitReg c) 0 φ
          - qs.eval (Gate.X c) (measProj (qubitReg c) 0 φ)) := by
  refine linearMap_ext_ket
    (gateL (Gate.H c) ∘ₗ gateL (Gate.X c) ∘ₗ (measProj (qubitReg c) 0).toLinearMap)
    ((1 / (Real.sqrt 2 : ℂ)) • ((measProj (qubitReg c) 0).toLinearMap
      - gateL (Gate.X c) ∘ₗ (measProj (qubitReg c) 0).toLinearMap)) (fun x => ?_) φ
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    ContinuousLinearMap.coe_coe, gateL_apply, measProj_qubitReg_ket]
  cases hx : RegEncoding.bit c x
  · simp only [Bool.false_eq_true, ite_true, ite_false]
    rw [PauliXSemantics.eval_X_ket, hx, HadamardSemantics.eval_H_ket]
    simp only [Bool.false_eq_true, ite_false]
    rw [bit_qubitReg_writeNat _ _ _ (by norm_num),
      writeNat_qubitReg_writeNat _ _ _ _ (by norm_num) (by norm_num),
      writeNat_qubitReg_writeNat _ _ _ _ (by norm_num) (by norm_num)]
    have h0 := writeNat_qubitReg_self c x
    rw [hx] at h0
    simp only [Bool.false_eq_true, ite_false] at h0
    rw [h0]
    simp [sub_eq_add_neg]
  · simp [MGate.gate_eval_zero_state]

omit [GateSemanticsCore qs] in
/-- The phase on qubit `c` fixes the `c = 0` subspace. -/
theorem phase_measProj_zero (c : ℕ) (θ : Angle) (φ : qs.State) :
    LowerGateClass.evalL (LowGate.Phase c θ) (measProj (qubitReg c) 0 φ)
      = measProj (qubitReg c) 0 φ := by
  refine linearMap_ext_ket (lowL (LowGate.Phase c θ) ∘ₗ (measProj (qubitReg c) 0).toLinearMap)
    (measProj (qubitReg c) 0).toLinearMap (fun x => ?_) φ
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, lowL_apply,
    measProj_qubitReg_ket]
  cases hx : RegEncoding.bit c x
  · simp [LowerGateClass.evalL_Phase_ket, hx]
  · simp [MGate.lowGate_evalL_zero_state]

omit [GateSemanticsCore qs] in
/-- The phase on qubit `c` multiplies the `c = 1` subspace by `exp(iπθ)`. -/
theorem phase_measProj_one (c : ℕ) (θ : Angle) (φ : qs.State) :
    LowerGateClass.evalL (LowGate.Phase c θ) (measProj (qubitReg c) 1 φ)
      = Complex.exp (((Angle.toReal θ : ℝ) : ℂ) * Complex.I) • measProj (qubitReg c) 1 φ := by
  refine linearMap_ext_ket (lowL (LowGate.Phase c θ) ∘ₗ (measProj (qubitReg c) 1).toLinearMap)
    (Complex.exp (((Angle.toReal θ : ℝ) : ℂ) * Complex.I) •
      (measProj (qubitReg c) 1).toLinearMap) (fun x => ?_) φ
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
    lowL_apply, measProj_qubitReg_ket]
  cases hx : RegEncoding.bit c x
  · simp [MGate.lowGate_evalL_zero_state]
  · simp [LowerGateClass.evalL_Phase_ket, hx]

omit [GateSemanticsCore qs] [LowerGateClass qs] in
/-- A state in one outcome subspace has no component in the other. -/
theorem measProj_of_measProj_ne (q o o' : ℕ) (φ : qs.State) (h : measProj (qubitReg q) o' φ = φ)
    (hne : o ≠ o') : measProj (qubitReg q) o φ = 0 := by
  rw [← h]; exact MeasureClass.measProj_orthogonal _ _ _ _ hne

end Readout
end Shor
