import ForShor.ShorVerification.Framework.Semantics.LowGateSemantics
import ForShor.ShorVerification.Framework.ToomCookTable
import ForShor.ShorVerification.Implementation.ModularExponentiation.Lowering.ConstArithmetic
import ForShor.ShorVerification.Implementation.ModularExponentiation.Spec.Validity
import ForShor.ShorVerification.Implementation.PhaseProduct.Compiler.Workspace
import ForShor.ShorVerification.Implementation.PhaseProduct.Lowering.Lower
import ForShor.ShorVerification.Implementation.PhaseProduct.Spec.Cleanliness
import ForShor.ShorVerification.Implementation.QFT.Statement

/-!
# Compiler: lowering `Gate` to `LowGate` and its correctness statement

Everything needed to state the proposition proved in `Main.lean`: the
condition that a gate has the workspace its lowering needs, the lowering
itself, the clean-state precondition, and the correctness claim.
-/

namespace Shor

/-! =========================================================
    Static workspace condition
========================================================= -/

section
open Operations

/-- Every QFT, phase-product and modular-arithmetic block in a gate has the
workspace its lowerer needs under the policy `P`. -/
def Policy.GateWorkspaceOK (P : ShorLoweringPolicy) : Gate → Prop
  | Gate.seq U V => Policy.GateWorkspaceOK P U ∧ Policy.GateWorkspaceOK P V
  | Gate.adj U => Policy.GateWorkspaceOK P U
  | Gate.QFT r => Policy.QFTReserveOK P r
  | Gate.SignedPhaseProd _ x z => Policy.WorkspaceOK P x z
  | Gate.CSignedPhaseProd ctrl _ x z => Policy.CWorkspaceOK P ctrl x z
  | Gate.CmpGeConst N data scratch flag => ConstArithmeticWorkspace N data scratch flag
  | Gate.CSubConst N data scratch flag => ConstArithmeticWorkspace N data scratch flag
  | Gate.idealCtrlModMul _ _ _ _ => False
  | _ => True

end

/-! =========================================================
    The lowering
========================================================= -/

section
open Operations

/-- Lower a gate to `LowGate`, sending each QFT, phase-product and
modular-arithmetic block to its subroutine's lowerer. -/
def Policy.lowerGate (P : ShorLoweringPolicy) :
    (G : Gate) → Policy.GateWorkspaceOK P G → LowGate
  | Gate.id, _ => LowGate.id
  | Gate.seq U V, hworkspace =>
      LowGate.seq (Policy.lowerGate P U hworkspace.1) (Policy.lowerGate P V hworkspace.2)
  | Gate.adj U, hworkspace => LowGate.adj (Policy.lowerGate P U hworkspace)
  | Gate.H qbit, _ => LowGate.H qbit
  | Gate.X qbit, _ => LowGate.X qbit
  | Gate.CNOT ctrl target, _ => LowGate.CNOT ctrl target
  | Gate.Toffoli c₁ c₂ target, _ => LowGate.Toffoli c₁ c₂ target
  | Gate.QFT r, hworkspace => Policy.lowerQFT P r hworkspace
  | Gate.SignedPhaseProd phi x z, hworkspace => Policy.lowerSignedPhaseProd P phi x z hworkspace
  | Gate.CSignedPhaseProd ctrl phi x z, hworkspace =>
      Policy.lowerCSignedPhaseProd P ctrl phi x z hworkspace
  | Gate.CmpGeConst N data scratch flag, hworkspace =>
      lowerCmpGeConst N data scratch flag hworkspace
  | Gate.CSubConst N data scratch flag, hworkspace =>
      lowerCSubConst N data scratch flag hworkspace
  | Gate.ShiftL r n, _ => LowGate.ShiftL r n
  | Gate.ShiftR r n, _ => LowGate.ShiftR r n
  | Gate.Negate r, _ => LowGate.Negate r
  | Gate.AddScaled dst src negSrc shift, _ => LowGate.AddScaled dst src negSrc shift
  | Gate.zeroExtend r n, _ => LowGate.zeroExtend r n
  | Gate.signExtend r n, _ => LowGate.signExtend r n
  | Gate.zeroDealloc r n, _ => LowGate.zeroDealloc r n
  | Gate.signDealloc r n, _ => LowGate.signDealloc r n
  | Gate.RadixReverse r m, _ => LowGate.RadixReverse r m

end

/-! =========================================================
    Clean-state precondition
========================================================= -/

section
open Operations

/-- The spare qubits each lowered block will use are zero on the state it is
applied to. For a sequence, the second component's condition is checked on the
state after the first component's lowered circuit. -/
noncomputable def Policy.GateWorkspaceCleanState (qs : QSemantics) [RegEncoding qs.Basis]
    [GateSemanticsCore qs] [LowerGateClass qs] (P : ShorLoweringPolicy) :
    (G : Gate) → Policy.GateWorkspaceOK P G → qs.State → Prop
  | Gate.id, _, _ => True
  | Gate.seq U V, hworkspace, ψ =>
      Policy.GateWorkspaceCleanState qs P U hworkspace.1 ψ ∧
      Policy.GateWorkspaceCleanState qs P V hworkspace.2
        (LowerGateClass.evalL (qs := qs) (Policy.lowerGate P U hworkspace.1) ψ)
  | Gate.adj U, hworkspace, ψ =>
      Policy.GateWorkspaceCleanState qs P U hworkspace (qs.eval (Gate.adj U) ψ)
  | Gate.H _, _, _ => True
  | Gate.X _, _, _ => True
  | Gate.QFT r, _, ψ => QFTWorkspaceCleanState qs (Policy.qftXWork P r) (Policy.qftZWork P r) ψ
  | Gate.SignedPhaseProd _ x z, _, ψ => RecursiveWorkspaceCleanState qs x z ψ
  | Gate.CSignedPhaseProd _ _ x z, _, ψ => RecursiveWorkspaceCleanState qs x z ψ
  | Gate.CmpGeConst _ data scratch _, _, ψ => CmpGeConstCleanState qs data scratch ψ
  | Gate.CSubConst N data scratch flag, _, ψ => CSubConstCleanState qs N data scratch flag ψ
  | _, _, _ => True

end

/-! =========================================================
    Correctness
========================================================= -/

/-- For an admissible policy, the lowered program of a gate with enough
workspace acts on a clean state exactly as the gate does. -/
def Policy.LowerGateCorrect (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs]
    [LowerGateClass qs] (P : ShorLoweringPolicy) : Prop :=
  P.Admissible →
    ∀ (G : Gate) (hworkspace : Policy.GateWorkspaceOK P G) (ψ : qs.State),
      Policy.GateWorkspaceCleanState qs P G hworkspace ψ →
      ⟦Policy.lowerGate P G hworkspace⟧ₗ ψ = ⟦G⟧ ψ

end Shor
