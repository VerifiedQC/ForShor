import ForShor.ShorVerification.Implementation.QFT.Statement
import ForShor.ShorVerification.Framework.AbstractMachine.Gates
import ForShor.ShorVerification.Framework.AbstractMachine.LowGate
import ForShor.ShorVerification.Framework.Semantics.GateSemantics
import ForShor.ShorVerification.Framework.Semantics.LowGateSemantics

/-!
# Phase-product gate macros (implementation)

The unsigned/controlled phase-product macros (`PhaseProdWorkspace`,
`PhaseProdUsing`, `CPhaseProdUsing`) — specific circuit constructions used only
by the lowering and correctness proofs.  The general register-algebra lemmas
they build on stay in Framework/AbstractMachine/Gates.
-/

namespace Shor
namespace Gate

namespace PhaseProdWorkspace

/-! =========================================================
    Workspace Views And Cleanliness
========================================================= -/

/-- The reserve bits used by the unsigned-to-signed bridge are initially zero. -/
def Clean {Basis : Type u} [RegEncoding Basis] {x z : Reg} (ws : PhaseProdWorkspace x z)
    (b : Basis) : Prop :=
  ws.xExt.FreshFor 1 b ∧ ws.zExt.FreshFor 1 b

@[simp] theorem toNat_xExt
    {Basis : Type u} [RegEncoding Basis] {x z : Reg} (ws : PhaseProdWorkspace x z) (b : Basis) :
    ExtReg.toNat ws.xExt b = RegEncoding.toNat x b := rfl

@[simp] theorem toNat_zExt
    {Basis : Type u} [RegEncoding Basis] {x z : Reg} (ws : PhaseProdWorkspace x z) (b : Basis) :
    ExtReg.toNat ws.zExt b = RegEncoding.toNat z b := rfl

/-- The controlled bridge may read `ctrl`; this predicate keeps it outside all touched qubits. -/
def ControlDisjoint {x z : Reg} (ws : PhaseProdWorkspace x z) (ctrl : ℕ) : Prop :=
  ctrl ∉ x.qubits ∧ ctrl ∉ z.qubits ∧ ctrl ∉ ws.xReserve.qubits ∧ ctrl ∉ ws.zReserve.qubits

end PhaseProdWorkspace

end Gate
end Shor
