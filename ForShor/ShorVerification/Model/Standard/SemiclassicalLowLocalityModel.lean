import ForShor.ShorVerification.Model.Standard.SemiclassicalLocalityModel
import ForShor.ShorVerification.Implementation.Readout.LowLocalityTests
import ForShor.ShorVerification.Implementation.Readout.LowLocalityNamed
import ForShor.ShorVerification.Implementation.Readout.LowLocalityBalanced
import ForShor.ShorVerification.Model.Standard.SemiclassicalMainModel

/-!
# Low-gate locality in the standard model

Instances of `Implementation/Readout/Proofs/LowLocality.lean` and
`Implementation/Readout/LowLocality.lean` at `Model.qs`.

* `model_signDealloc_not_commProj` (negative sanity): `LowGate.usedQubits` is NOT a semantic
  footprint. For the register `testReg` (active `[0]`, reserve `[1]`), qubit `1` is outside
  `usedQubits (signDealloc testReg 1)`, yet `evalL (signDealloc testReg 1)` does NOT commute with
  the Z projector `measProj (qubitReg 1) 0` at `Model.qs`: from the ket with only qubit `0` set
  (the register reads `-1`), the gate complements qubit `1`. This is why the theorems use
  `LowGate.lowFootprint` (which contains qubit `1` here).
* `model_adj_apply`: at `Model.qs`, `evalL L (evalL (adj L) ψ) = ψ`, an instance of
  `evalL_apply_adj` (B2 needs no new law, so there is no new class to instantiate).
* `model_lowered_decomp_exponent`, `model_lowered_superpose_exponent_direct`: for EVERY policy
  (no admissibility), the reference layout, any number of rounds, and an exponent qubit `q`
  after the control: if `q` is also outside `MGate.qftPhaseFoot` (the footprint of the lowered
  QFT / phase-product blocks; carried as a hypothesis in these two, discharged by B4 below),
  then the lowered circuit's record probabilities
  decompose along `q` for ANY start state, and a superposed `q` scales them by
  `‖α‖² + ‖β‖²`, from ANY start ket.
* B4: `model_exponent_tail_not_mem_qftPhaseFoot` discharges that hypothesis for every exponent
  qubit after the control; `model_exponent_tail_not_mem_lowSupport`: the lowered circuit names
  none of them; `model_lowered_decomp_exponent_named`, `model_lowered_superpose_exponent_named`:
  the two instances above with NO footprint hypothesis.
* B5 non-degeneracy: `model_x_head_eq_control` (the control IS the first qubit of the exponent
  register; the tail theorems are about the REST), `model_exponent_tail_nonvacuous` (the tail
  has at least two qubits, `|x| ≥ 3`, each outside `semiclassicalQubits` and outside the lowered
  circuit's low support, and flipping the tail changes the all-zero ket).
* Physics note: the exponent tail is idle BY DESIGN. The semiclassical circuit uses the
  control (the head of the exponent register) and never touches the rest of the (ghost)
  exponent register, so these Model results are a sanity property of the lowering (it allocates
  no hidden workspace there), not a deep locality fact.
* B5 fix round: `model_lowered_balancedU_default_decomp_exponent`,
  `…_flip_exponent`, `…_superpose_exponent`: the unconditionally balanced instances at the
  default rule with NO fit hypothesis (`hf` discharged by `Model.referenceSemiclassicalFits`
  with `Balanced.referenceFits_default`); `model_lowered_balanced_flip_exponent`,
  `model_lowered_balanced_superpose_exponent`: flip and superposition for the conditional
  balanced lowering, every rule.
* B5 balanced: `model_lowered_balanced_decomp_exponent`, `model_lowered_balancedU_decomp_exponent`:
  the decomposition for the balanced lowerings (every rule; `U` under its fit hypothesis), any
  start state.
-/

namespace Shor
namespace Model

open Reference Readout

set_option hygiene false in
local notation "RL" => allocateReferenceLayout P inst ℓ

/-- The basis state with only qubit `0` set. -/
def lowCeBasis : ModelBasis := fun q => decide (q = 0)

/-- `signDealloc testReg 1` complements qubit `1` on `lowCeBasis` (the register `[0]` reads
`-1`). -/
theorem model_signDealloc_flips :
    signDeallocBasis (Basis := ModelBasis) LowLocalityTests.testReg 1 lowCeBasis 1 = true := by
  decide

/-- **`usedQubits` is not a semantic footprint (negative sanity at `Model.qs`).** -/
theorem model_signDealloc_not_commProj :
    1 ∉ (LowGate.signDealloc LowLocalityTests.testReg 1).usedQubits ∧
      ¬ CommPL qs (LowGate.signDealloc LowLocalityTests.testReg 1) 1 0 := by
  refine ⟨LowLocalityTests.signDealloc_footprint_strict.2, fun h => ?_⟩
  have h1 := h (qs.ket lowCeBasis)
  have hb : RegEncoding.bit (Basis := qs.Basis) 1 lowCeBasis = false := by decide
  have hb' : RegEncoding.bit (Basis := qs.Basis) 1
      (signDeallocBasis LowLocalityTests.testReg 1 lowCeBasis) = true := model_signDealloc_flips
  rw [measProj_qubitReg_ket, hb] at h1
  simp only [Bool.false_eq_true, ↓reduceIte] at h1
  rw [LowerGateClass.evalL_signDealloc_ket_total, measProj_qubitReg_ket, hb'] at h1
  simp only [↓reduceIte, one_ne_zero] at h1
  exact qs.ket_ne_zero _ h1

/-- B2 at `Model.qs`: every low gate undoes its adjoint. -/
theorem model_adj_apply (L : LowGate) (ψ : qs.State) :
    LowerGateClass.evalL L (LowerGateClass.evalL (LowGate.adj L) ψ) = ψ :=
  evalL_apply_adj L ψ

/-- **Lowered circuit, model, decomposition along an exponent qubit, any start state.** Every
policy (no admissibility), any rounds `m`, any `ψ₀`; `q` an exponent qubit after the control and
outside the footprint of the lowered QFT / phase-product blocks (hypothesis `hq'`, carried). -/
theorem model_lowered_decomp_exponent (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (ℓ m : ℕ) (q : ℕ) (hq : q ∈ (RL).x.active.qubits.tail)
    (hq' : q ∉ MGate.qftPhaseFoot P (orderFindingSemiclassical inst.a inst.N
      (referenceControl P inst ℓ) m (RL).data (RL).work (RL).scratch (RL).flag
      (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
      (referenceSemiclassicalSetup P inst ℓ).step4_workspace)
      (referenceSemiclassicalWorkspaceOK P inst ℓ m))
    (ψ₀ : qs.State) (r : Record) :
    recordProb ((orderFindingSemiclassicalLow P inst.a inst.N (referenceControl P inst ℓ) m
        (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace
        (referenceSemiclassicalWorkspaceOK P inst ℓ m)).eval (MState.init ψ₀)) r
      = ∑ o ∈ Finset.range 2, recordProb ((orderFindingSemiclassicalLow P inst.a inst.N
        (referenceControl P inst ℓ) m (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace
        (referenceSemiclassicalWorkspaceOK P inst ℓ m)).eval
        (MState.init (MeasureClass.measProj (qubitReg q) o ψ₀))) r :=
  orderFindingSemiclassicalLow_recordProb_decomp (model_exponent_tail_unnamed P inst ℓ q hq).1
    hq' ψ₀ r

/-- **Lowered circuit, model, superposed exponent qubit, any start ket.** Same hypotheses;
ANY start ket `b0` (not only `|0…0⟩`), no admissibility. -/
theorem model_lowered_superpose_exponent_direct (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (ℓ m : ℕ) (q : ℕ) (hq : q ∈ (RL).x.active.qubits.tail)
    (hq' : q ∉ MGate.qftPhaseFoot P (orderFindingSemiclassical inst.a inst.N
      (referenceControl P inst ℓ) m (RL).data (RL).work (RL).scratch (RL).flag
      (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
      (referenceSemiclassicalSetup P inst ℓ).step4_workspace)
      (referenceSemiclassicalWorkspaceOK P inst ℓ m))
    (b0 : qs.Basis) (α β : ℂ) (r : Record) :
    recordProb ((orderFindingSemiclassicalLow P inst.a inst.N (referenceControl P inst ℓ) m
        (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace
        (referenceSemiclassicalWorkspaceOK P inst ℓ m)).eval
        (MState.init (α • qs.ket b0 + β • qs.ket (flipBit q b0)))) r
      = (‖α‖ ^ 2 + ‖β‖ ^ 2) * recordProb ((orderFindingSemiclassicalLow P inst.a inst.N
        (referenceControl P inst ℓ) m (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace
        (referenceSemiclassicalWorkspaceOK P inst ℓ m)).eval
        (MState.init (qs.ket b0))) r :=
  orderFindingSemiclassicalLow_recordProb_superpose_direct
    (model_exponent_tail_unnamed P inst ℓ q hq).1 hq' b0 α β r

/-! ## B4: no footprint hypothesis -/

/-- **(b) The residual hypothesis is discharged at the reference layout.** Every exponent qubit
after the control is outside the footprint of the lowered QFT / phase-product blocks of the
real circuit, for every policy and number of rounds. -/
theorem model_exponent_tail_not_mem_qftPhaseFoot (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (ℓ m : ℕ) (q : ℕ) (hq : q ∈ (RL).x.active.qubits.tail) :
    q ∉ MGate.qftPhaseFoot P (orderFindingSemiclassical inst.a inst.N
      (referenceControl P inst ℓ) m (RL).data (RL).work (RL).scratch (RL).flag
      (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
      (referenceSemiclassicalSetup P inst ℓ).step4_workspace)
      (referenceSemiclassicalWorkspaceOK P inst ℓ m) :=
  not_mem_qftPhaseFoot_of_not_mem_semiclassicalQubits (model_exponent_tail_unnamed P inst ℓ q hq).1

/-- **(a) at the model: the lowered circuit names no exponent qubit other than the control.** -/
theorem model_exponent_tail_not_mem_lowSupport (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (ℓ m : ℕ) (q : ℕ) (hq : q ∈ (RL).x.active.qubits.tail) :
    q ∉ (orderFindingSemiclassicalLow P inst.a inst.N (referenceControl P inst ℓ) m
        (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace
        (referenceSemiclassicalWorkspaceOK P inst ℓ m)).lowSupport := fun h =>
  (model_exponent_tail_unnamed P inst ℓ q hq).1
    (semiclassical_lowSupport_named P _ _ _ m _ _ _ _ _ _ _ h)

/-- **Lowered circuit, model, decomposition along an exponent qubit, any start state, no
footprint hypothesis.** Every policy (no admissibility), any rounds `m`, any `ψ₀`, any exponent
qubit after the control. -/
theorem model_lowered_decomp_exponent_named (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (ℓ m : ℕ) (q : ℕ) (hq : q ∈ (RL).x.active.qubits.tail)
    (ψ₀ : qs.State) (r : Record) :
    recordProb ((orderFindingSemiclassicalLow P inst.a inst.N (referenceControl P inst ℓ) m
        (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace
        (referenceSemiclassicalWorkspaceOK P inst ℓ m)).eval (MState.init ψ₀)) r
      = ∑ o ∈ Finset.range 2, recordProb ((orderFindingSemiclassicalLow P inst.a inst.N
        (referenceControl P inst ℓ) m (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace
        (referenceSemiclassicalWorkspaceOK P inst ℓ m)).eval
        (MState.init (MeasureClass.measProj (qubitReg q) o ψ₀))) r :=
  model_lowered_decomp_exponent P inst ℓ m q hq
    (model_exponent_tail_not_mem_qftPhaseFoot P inst ℓ m q hq) ψ₀ r

/-- **Lowered circuit, model, superposed exponent qubit, any start ket, no footprint
hypothesis.** -/
theorem model_lowered_superpose_exponent_named (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (ℓ m : ℕ) (q : ℕ) (hq : q ∈ (RL).x.active.qubits.tail)
    (b0 : qs.Basis) (α β : ℂ) (r : Record) :
    recordProb ((orderFindingSemiclassicalLow P inst.a inst.N (referenceControl P inst ℓ) m
        (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace
        (referenceSemiclassicalWorkspaceOK P inst ℓ m)).eval
        (MState.init (α • qs.ket b0 + β • qs.ket (flipBit q b0)))) r
      = (‖α‖ ^ 2 + ‖β‖ ^ 2) * recordProb ((orderFindingSemiclassicalLow P inst.a inst.N
        (referenceControl P inst ℓ) m (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace
        (referenceSemiclassicalWorkspaceOK P inst ℓ m)).eval
        (MState.init (qs.ket b0))) r :=
  model_lowered_superpose_exponent_direct P inst ℓ m q hq
    (model_exponent_tail_not_mem_qftPhaseFoot P inst ℓ m q hq) b0 α β r

/-! ## B5: non-degeneracy and the balanced lowerings -/

/-- **The control is the head of the exponent register.** The tail theorems above are about the
other exponent qubits. -/
theorem model_x_head_eq_control (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (ℓ : ℕ) : (RL).x.active.qubits.head? = some (referenceControl P inst ℓ) := by
  rw [referenceX_qubits_eq]; rfl

/-- **The tail instances are not vacuous.** The exponent register has at least three qubits,
so its tail (the exponent qubits other than the control) has at least two; every tail qubit is
outside `semiclassicalQubits` and outside the lowered circuit's low support, for every policy
and number of rounds; and flipping the tail changes the all-zero start ket. -/
theorem model_exponent_tail_nonvacuous (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (ℓ : ℕ) :
    3 ≤ regSize (RL).x.active ∧ (RL).x.active.qubits.tail ≠ [] ∧
    (∀ q ∈ (RL).x.active.qubits.tail,
      q ∉ semiclassicalQubits (referenceControl P inst ℓ) (RL).data (RL).work (RL).scratch
        (RL).flag ∧
      ∀ m, q ∉ (orderFindingSemiclassicalLow P inst.a inst.N (referenceControl P inst ℓ) m
        (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace
        (referenceSemiclassicalWorkspaceOK P inst ℓ m)).lowSupport) ∧
    flipBits (RL).x.active.qubits.tail (RegEncoding.zero (Basis := qs.Basis)) ≠ RegEncoding.zero :=
  ⟨model_x_width_ge_three P inst ℓ, model_tail_ne_nil P inst ℓ,
    fun q hq => ⟨(model_exponent_tail_unnamed P inst ℓ q hq).1,
      fun m => model_exponent_tail_not_mem_lowSupport P inst ℓ m q hq⟩,
    model_flipBits_tail_ne_zero P inst ℓ⟩

/-- **Balanced lowered circuit, model, decomposition along an exponent qubit after the control,
any start state.** Every policy and rule. -/
theorem model_lowered_balanced_decomp_exponent (P : ShorLoweringPolicy) (R : Balanced.Rule)
    (inst : ShorOrderFindingInstance) (ℓ m : ℕ) (q : ℕ) (hq : q ∈ (RL).x.active.qubits.tail)
    (ψ₀ : qs.State) (r : Record) :
    recordProb ((orderFindingSemiclassicalLowBalanced P R inst.a inst.N (referenceControl P inst ℓ)
        m (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace
        (referenceSemiclassicalWorkspaceOK P inst ℓ m)).eval (MState.init ψ₀)) r
      = ∑ o ∈ Finset.range 2, recordProb ((orderFindingSemiclassicalLowBalanced P R inst.a inst.N
        (referenceControl P inst ℓ) m (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace
        (referenceSemiclassicalWorkspaceOK P inst ℓ m)).eval
        (MState.init (MeasureClass.measProj (qubitReg q) o ψ₀))) r :=
  orderFindingSemiclassicalLowBalanced_recordProb_decomp_named
    (model_exponent_tail_unnamed P inst ℓ q hq).1 ψ₀ r

/-- **Unconditionally balanced lowered circuit, model, decomposition.** Every policy and rule,
under the circuit's own fit hypothesis `hf` (needed to define the circuit). -/
theorem model_lowered_balancedU_decomp_exponent (P : ShorLoweringPolicy) (R : Balanced.Rule)
    (inst : ShorOrderFindingInstance) (ℓ m : ℕ)
    (hf : MGate.Fits P R (orderFindingSemiclassical inst.a inst.N (referenceControl P inst ℓ) m
      (RL).data (RL).work (RL).scratch (RL).flag
      (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
      (referenceSemiclassicalSetup P inst ℓ).step4_workspace))
    (q : ℕ) (hq : q ∈ (RL).x.active.qubits.tail) (ψ₀ : qs.State) (r : Record) :
    recordProb ((orderFindingSemiclassicalLowBalancedU P R inst.a inst.N
        (referenceControl P inst ℓ) m (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace
        (referenceSemiclassicalWorkspaceOK P inst ℓ m) hf).eval (MState.init ψ₀)) r
      = ∑ o ∈ Finset.range 2, recordProb ((orderFindingSemiclassicalLowBalancedU P R inst.a inst.N
        (referenceControl P inst ℓ) m (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace
        (referenceSemiclassicalWorkspaceOK P inst ℓ m) hf).eval
        (MState.init (MeasureClass.measProj (qubitReg q) o ψ₀))) r :=
  orderFindingSemiclassicalLowBalancedU_recordProb_decomp_named
    (model_exponent_tail_unnamed P inst ℓ q hq).1 ψ₀ r


/-- **Balanced lowered circuit, model, exponent qubit after the control, every rule.** Flip form: any start state. -/
theorem model_lowered_balanced_flip_exponent (P : ShorLoweringPolicy) (R : Balanced.Rule)
    (inst : ShorOrderFindingInstance) (ℓ m : ℕ) (q : ℕ) (hq : q ∈ (RL).x.active.qubits.tail)
    (ψ₀ : qs.State) (r : Record) :
    recordProb ((orderFindingSemiclassicalLowBalanced P R inst.a inst.N (referenceControl P inst ℓ)
        m (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace
        (referenceSemiclassicalWorkspaceOK P inst ℓ m)).eval
        (MState.init (LowerGateClass.evalL (LowGate.X q) ψ₀))) r
      = recordProb ((orderFindingSemiclassicalLowBalanced P R inst.a inst.N (referenceControl P inst ℓ)
        m (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace
        (referenceSemiclassicalWorkspaceOK P inst ℓ m)).eval (MState.init ψ₀)) r :=
  MLowGate.recordProb_init_X _ (fun h => (model_exponent_tail_unnamed P inst ℓ q hq).1
    (semiclassical_lowSupport_balanced P R _ _ _ m _ _ _ _ _ _ _ h)) ψ₀ r

/-- **Balanced lowered circuit, model, exponent qubit after the control, every rule.** Superposition form: any start ket. -/
theorem model_lowered_balanced_superpose_exponent (P : ShorLoweringPolicy) (R : Balanced.Rule)
    (inst : ShorOrderFindingInstance) (ℓ m : ℕ) (q : ℕ) (hq : q ∈ (RL).x.active.qubits.tail)
    (b0 : qs.Basis) (α β : ℂ) (r : Record) :
    recordProb ((orderFindingSemiclassicalLowBalanced P R inst.a inst.N (referenceControl P inst ℓ)
        m (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace
        (referenceSemiclassicalWorkspaceOK P inst ℓ m)).eval
        (MState.init (α • qs.ket b0 + β • qs.ket (flipBit q b0)))) r
      = (‖α‖ ^ 2 + ‖β‖ ^ 2) * recordProb ((orderFindingSemiclassicalLowBalanced P R inst.a inst.N (referenceControl P inst ℓ)
        m (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace
        (referenceSemiclassicalWorkspaceOK P inst ℓ m)).eval (MState.init (qs.ket b0))) r :=
  MLowGate.recordProb_superpose _ (fun h => (model_exponent_tail_unnamed P inst ℓ q hq).1
    (semiclassical_lowSupport_balanced P R _ _ _ m _ _ _ _ _ _ _ h)) b0 α β r

/-- **Unconditionally balanced lowered circuit at the default rule, model, no fit hypothesis.** Flip form: any start state. -/
theorem model_lowered_balancedU_default_flip_exponent (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (ℓ m : ℕ) (q : ℕ) (hq : q ∈ (RL).x.active.qubits.tail)
    (ψ₀ : qs.State) (r : Record) :
    recordProb ((orderFindingSemiclassicalLowBalancedU P Balanced.defaultRule inst.a inst.N
        (referenceControl P inst ℓ) m (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace
        (referenceSemiclassicalWorkspaceOK P inst ℓ m)
        (Model.referenceSemiclassicalFits P _ (Balanced.referenceFits_default P) inst ℓ m)).eval
        (MState.init (LowerGateClass.evalL (LowGate.X q) ψ₀))) r
      = recordProb ((orderFindingSemiclassicalLowBalancedU P Balanced.defaultRule inst.a inst.N
        (referenceControl P inst ℓ) m (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace
        (referenceSemiclassicalWorkspaceOK P inst ℓ m)
        (Model.referenceSemiclassicalFits P _ (Balanced.referenceFits_default P) inst ℓ m)).eval (MState.init ψ₀)) r :=
  MLowGate.recordProb_init_X _ (fun h => (model_exponent_tail_unnamed P inst ℓ q hq).1
    (semiclassical_lowSupport_balancedU P Balanced.defaultRule _ _ _ m _ _ _ _ _ _ _ _ h)) ψ₀ r

/-- **Unconditionally balanced lowered circuit at the default rule, model, no fit hypothesis.** Superposition form: any start ket. -/
theorem model_lowered_balancedU_default_superpose_exponent (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (ℓ m : ℕ) (q : ℕ) (hq : q ∈ (RL).x.active.qubits.tail)
    (b0 : qs.Basis) (α β : ℂ) (r : Record) :
    recordProb ((orderFindingSemiclassicalLowBalancedU P Balanced.defaultRule inst.a inst.N
        (referenceControl P inst ℓ) m (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace
        (referenceSemiclassicalWorkspaceOK P inst ℓ m)
        (Model.referenceSemiclassicalFits P _ (Balanced.referenceFits_default P) inst ℓ m)).eval
        (MState.init (α • qs.ket b0 + β • qs.ket (flipBit q b0)))) r
      = (‖α‖ ^ 2 + ‖β‖ ^ 2) * recordProb ((orderFindingSemiclassicalLowBalancedU P Balanced.defaultRule inst.a inst.N
        (referenceControl P inst ℓ) m (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace
        (referenceSemiclassicalWorkspaceOK P inst ℓ m)
        (Model.referenceSemiclassicalFits P _ (Balanced.referenceFits_default P) inst ℓ m)).eval (MState.init (qs.ket b0))) r :=
  MLowGate.recordProb_superpose _ (fun h => (model_exponent_tail_unnamed P inst ℓ q hq).1
    (semiclassical_lowSupport_balancedU P Balanced.defaultRule _ _ _ m _ _ _ _ _ _ _ _ h)) b0 α β r

/-- **Unconditionally balanced lowered circuit at the default rule, model, decomposition, no fit
hypothesis.** The fit `hf` is discharged by `Model.referenceSemiclassicalFits` with
`Balanced.referenceFits_default`. -/
theorem model_lowered_balancedU_default_decomp_exponent (P : ShorLoweringPolicy)
    (inst : ShorOrderFindingInstance) (ℓ m : ℕ) (q : ℕ) (hq : q ∈ (RL).x.active.qubits.tail)
    (ψ₀ : qs.State) (r : Record) :
    recordProb ((orderFindingSemiclassicalLowBalancedU P Balanced.defaultRule inst.a inst.N
        (referenceControl P inst ℓ) m (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace
        (referenceSemiclassicalWorkspaceOK P inst ℓ m)
        (Model.referenceSemiclassicalFits P _ (Balanced.referenceFits_default P) inst ℓ m)).eval (MState.init ψ₀)) r
      = ∑ o ∈ Finset.range 2, recordProb ((orderFindingSemiclassicalLowBalancedU P Balanced.defaultRule inst.a inst.N
        (referenceControl P inst ℓ) m (RL).data (RL).work (RL).scratch (RL).flag
        (referenceSemiclassicalSetup P inst ℓ).circuit_workspace
        (referenceSemiclassicalSetup P inst ℓ).step4_workspace
        (referenceSemiclassicalWorkspaceOK P inst ℓ m)
        (Model.referenceSemiclassicalFits P _ (Balanced.referenceFits_default P) inst ℓ m)).eval
        (MState.init (MeasureClass.measProj (qubitReg q) o ψ₀))) r :=
  model_lowered_balancedU_decomp_exponent P Balanced.defaultRule inst ℓ m
    (Model.referenceSemiclassicalFits P _ (Balanced.referenceFits_default P) inst ℓ m) q hq ψ₀ r

end Model
end Shor

#print axioms Shor.Model.model_signDealloc_flips
#print axioms Shor.Model.model_signDealloc_not_commProj
#print axioms Shor.Model.model_adj_apply
#print axioms Shor.Model.model_lowered_decomp_exponent
#print axioms Shor.Model.model_lowered_superpose_exponent_direct
#print axioms Shor.Model.model_exponent_tail_not_mem_qftPhaseFoot
#print axioms Shor.Model.model_exponent_tail_not_mem_lowSupport
#print axioms Shor.Model.model_lowered_decomp_exponent_named
#print axioms Shor.Model.model_lowered_superpose_exponent_named
#print axioms Shor.Model.model_x_head_eq_control
#print axioms Shor.Model.model_exponent_tail_nonvacuous
#print axioms Shor.Model.model_lowered_balanced_decomp_exponent
#print axioms Shor.Model.model_lowered_balancedU_decomp_exponent
#print axioms Shor.Model.model_lowered_balanced_flip_exponent
#print axioms Shor.Model.model_lowered_balanced_superpose_exponent
#print axioms Shor.Model.model_lowered_balancedU_default_flip_exponent
#print axioms Shor.Model.model_lowered_balancedU_default_superpose_exponent
#print axioms Shor.Model.model_lowered_balancedU_default_decomp_exponent
