import ForShor.ShorVerification.Implementation.Readout.Proofs.LocalityProj
import ForShor.ShorVerification.Implementation.Readout.Locality

/-!
# Readout: unnamed qubits of the semiclassical circuits are spectators (T5)

The general spectator law (`Proofs/LocalityProj.lean`: commutation with the Z projectors of an
unnamed qubit, record decomposition, superposed spectator) instantiated for the semiclassical
circuits. "Unnamed" means outside `semiclassicalQubits c y work scratch flag` (the control,
every OWNED qubit of `y`, `work`, `scratch`, reserves included, and the flag), exactly as in
`Locality.lean`.

* Real circuit (no hypothesis on registers or start state):
  `orderFindingSemiclassical_eval_init_proj`, `orderFindingSemiclassical_recordProb_decomp`,
  `orderFindingSemiclassical_recordProb_superpose`.
* Lowered circuit, under the hypotheses of `semiclassical_lowerM_eval` for `b0`:
  `orderFindingSemiclassicalLow_recordProb_superpose`. It uses linearity of the lowered
  semantics (`MLowGate.eval_add`, `MLowGate.eval_smul`) and `semiclassical_lowerM_eval` at the
  two kets `b0` and `flipBit q b0` (the clean hypotheses carry over). The lowered decomposition
  for an ARBITRARY start state is not stated: `semiclassical_lowerM_eval` is proved for basis
  kets with clean registers, not for arbitrary states.
-/

namespace Shor
namespace Readout

open MeasureClass

variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]
  [MeasureClass qs]

/-! ## Linearity of the lowered semantics -/

omit [GateSemanticsFacts qs] in
theorem measureResetBranchL_add (p : ℕ) (c : Bool) (φ χ : qs.State) :
    measureResetBranchL p c (φ + χ) = measureResetBranchL p c φ + measureResetBranchL p c χ := by
  cases c <;> simp [measureResetBranchL, map_add, LowerGateClass.evalL_add]

omit [GateSemanticsFacts qs] in
theorem measureResetBranchL_smul (p : ℕ) (c : Bool) (a : ℂ) (φ : qs.State) :
    measureResetBranchL p c (a • φ) = a • measureResetBranchL p c φ := by
  cases c <;> simp [measureResetBranchL, map_smul, LowerGateClass.evalL_smul]

omit [GateSemanticsFacts qs] in
theorem MLowGate.eval_add (P : MLowGate) (ψ φ : MState qs) :
    P.eval (ψ + φ) = P.eval ψ + P.eval φ := by
  induction P generalizing ψ φ with
  | unitary g => funext r; exact LowerGateClass.evalL_add g (ψ r) (φ r)
  | seq a b iha ihb => simp only [MLowGate.eval]; rw [iha, ihb]
  | measureReset p =>
    funext r
    simp only [MLowGate.eval, Pi.add_apply]
    split
    · simp
    · exact measureResetBranchL_add p _ _ _
  | ffPhase p j => funext r; exact LowerGateClass.evalL_add _ (ψ r) (φ r)

omit [GateSemanticsFacts qs] in
theorem MLowGate.eval_smul (P : MLowGate) (a : ℂ) (ψ : MState qs) :
    P.eval (a • ψ) = a • P.eval ψ := by
  induction P generalizing ψ with
  | unitary g => funext r; exact LowerGateClass.evalL_smul g a (ψ r)
  | seq a' b iha ihb => simp only [MLowGate.eval]; rw [iha, ihb]
  | measureReset p =>
    funext r
    simp only [MLowGate.eval, Pi.smul_apply]
    split
    · simp
    · exact measureResetBranchL_smul p _ a _
  | ffPhase p j => funext r; exact LowerGateClass.evalL_smul _ a (ψ r)

/-! ## Real circuit -/

/-- **T5, real circuit, state level.** For ANY registers and ANY start state `ψ₀`, and any qubit
`q` outside `semiclassicalQubits c y work scratch flag`: the run from the Z-projection
`measProj (qubitReg q) o ψ₀` is, branch by branch, the projection of the run from `ψ₀`. -/
theorem orderFindingSemiclassical_eval_init_proj (a N c m : ℕ) (y work scratch : ExtReg)
    (flag : ℕ) (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) {q : ℕ}
    (hq : q ∉ semiclassicalQubits c y work scratch flag) (o : ℕ) (ψ₀ : qs.State) (r : Record) :
    (orderFindingSemiclassical a N c m y work scratch flag hw hs4).eval
        (MState.init (measProj (qubitReg q) o ψ₀)) r
      = measProj (qubitReg q) o ((orderFindingSemiclassical a N c m y work scratch flag hw
          hs4).eval (MState.init ψ₀) r) :=
  MGate.eval_init_proj _ (orderFindingSemiclassical_noIdeal a N c m hw hs4)
    (not_mem_orderFindingSemiclassical_support hw hs4 hq) o ψ₀ r

/-- **T5, real circuit, decomposition.** Same hypotheses: every record probability from `ψ₀`
is the sum over `o ∈ {0, 1}` of those from `measProj (qubitReg q) o ψ₀`. -/
theorem orderFindingSemiclassical_recordProb_decomp (a N c m : ℕ) (y work scratch : ExtReg)
    (flag : ℕ) (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) {q : ℕ}
    (hq : q ∉ semiclassicalQubits c y work scratch flag) (ψ₀ : qs.State) (r : Record) :
    recordProb ((orderFindingSemiclassical a N c m y work scratch flag hw hs4).eval
        (MState.init ψ₀)) r
      = ∑ o ∈ Finset.range 2, recordProb ((orderFindingSemiclassical a N c m y work scratch flag
          hw hs4).eval (MState.init (measProj (qubitReg q) o ψ₀))) r :=
  MGate.recordProb_decomp _ (orderFindingSemiclassical_noIdeal a N c m hw hs4)
    (not_mem_orderFindingSemiclassical_support hw hs4 hq) ψ₀ r

/-- **T5, real circuit, superposed spectator.** For ANY registers, ANY start ket `b0`, any qubit
`q` outside `semiclassicalQubits c y work scratch flag` and ANY `α β : ℂ`: from
`α|b0⟩ + β|flipBit q b0⟩` every record has `(‖α‖² + ‖β‖²)` times its probability from `|b0⟩`. -/
theorem orderFindingSemiclassical_recordProb_superpose (a N c m : ℕ) (y work scratch : ExtReg)
    (flag : ℕ) (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) (b0 : qs.Basis) {q : ℕ}
    (hq : q ∉ semiclassicalQubits c y work scratch flag) (α β : ℂ) (r : Record) :
    recordProb ((orderFindingSemiclassical a N c m y work scratch flag hw hs4).eval
        (MState.init (α • qs.ket b0 + β • qs.ket (flipBit q b0)))) r
      = (‖α‖ ^ 2 + ‖β‖ ^ 2) * recordProb ((orderFindingSemiclassical a N c m y work scratch flag
          hw hs4).eval (MState.init (qs.ket b0))) r :=
  MGate.recordProb_superpose _ (orderFindingSemiclassical_noIdeal a N c m hw hs4)
    (not_mem_orderFindingSemiclassical_support hw hs4 hq) b0 α β r

/-! ## Lowered circuit -/

/-- **T5, lowered circuit, superposed spectator.** Hypotheses of `semiclassical_lowerM_eval`
for `b0` (admissible policy, lowering workspace, layout, zero data/work/scratch reserves and
zero scratch register in `b0`), any qubit `q` outside `semiclassicalQubits c y work scratch flag`,
any `α β : ℂ`: from `α|b0⟩ + β|flipBit q b0⟩` every record of the LOWERED circuit has
`(‖α‖² + ‖β‖²)` times its probability from `|b0⟩`. -/
theorem orderFindingSemiclassicalLow_recordProb_superpose {P : ShorLoweringPolicy}
    (hP : P.Admissible) (a N c m : ℕ) (y work scratch : ExtReg) (flag : ℕ)
    (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hws : MGate.WorkspaceOK P (orderFindingSemiclassical a N c m y work scratch flag hw hs4))
    (hl : SemiclassicalLayout c y work scratch flag) (b0 : qs.Basis)
    (hzero : SemiclassicalWorkspaceCleanInput y work scratch b0)
    (hscratch : RegEncoding.toNat scratch.active b0 = 0) {q : ℕ}
    (hq : q ∉ semiclassicalQubits c y work scratch flag) (α β : ℂ) (r : Record) :
    recordProb ((orderFindingSemiclassicalLow P a N c m y work scratch flag hw hs4 hws).eval
        (MState.init (α • qs.ket b0 + β • qs.ket (flipBit q b0)))) r
      = (‖α‖ ^ 2 + ‖β‖ ^ 2) * recordProb ((orderFindingSemiclassicalLow P a N c m y work scratch
          flag hw hs4 hws).eval (MState.init (qs.ket b0))) r := by
  have hagree : ∀ p ∈ semiclassicalQubits c y work scratch flag,
      RegEncoding.bit p (flipBit q b0) = RegEncoding.bit p b0 := fun p hp =>
    bit_flipBit_ne (fun e : p = q => hq (e ▸ hp)) b0
  have hzero' := semiclassicalWorkspaceCleanInput_ofAgree hagree hzero
  have hscratch' : RegEncoding.toNat scratch.active (flipBit q b0) = 0 := by
    rw [toNat_ofAgree (fun p hp => mem_semiclassicalQubits_scratch (active_sub p hp)) hagree,
      hscratch]
  rw [orderFindingSemiclassicalLow, MState.init_add, MState.init_smul, MState.init_smul,
    MLowGate.eval_add, MLowGate.eval_smul, MLowGate.eval_smul,
    semiclassical_lowerM_eval hP a N c m y work scratch flag hw hs4 hws hl b0 hzero hscratch,
    semiclassical_lowerM_eval hP a N c m y work scratch flag hw hs4 hws hl _ hzero' hscratch',
    ← MGate.eval_smul, ← MGate.eval_smul, ← MGate.eval_add, ← MState.init_smul,
    ← MState.init_smul, ← MState.init_add]
  exact orderFindingSemiclassical_recordProb_superpose a N c m y work scratch flag hw hs4 b0 hq
    α β r

end Readout
end Shor
