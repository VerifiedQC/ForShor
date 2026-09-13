import FastMultiplication.ShorVerification.Implementation.Semantics.CleanClosure
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Gates.Macros
import FastMultiplication.ShorVerification.Implementation.QFT.Lowering.Workspace

/-!
# QFT Cleanliness Predicates

The cleanliness predicates needed to state QFT workspace readiness: the
unsigned phase-product macro's own clean-workspace subspace, and the
state-level precondition on the QFT lowerer's inactive register.
-/

namespace Shor

namespace Gate.PhaseProdWorkspace

/--
The linear subspace in which both physical workspace qubits of an unsigned
phase-product macro are clean.
-/
abbrev CleanState
    (qs : QSemantics) [RegEncoding qs.Basis] {x z : Reg} (ws : Gate.PhaseProdWorkspace x z) : qs.State → Prop :=
  CleanClosure (fun b => ws.Clean b)

end Gate.PhaseProdWorkspace

/--
The linear subspace in which both portions of the inactive QFT register used
by the concrete lowering are zero.
-/
abbrev QFTWorkspaceCleanState
    (qs : QSemantics) [RegEncoding qs.Basis] (xWork zWork : Reg) :
    qs.State → Prop :=
  CleanClosure (fun b => FreshZero xWork b ∧ FreshZero zWork b)

namespace QFTWorkspaceCleanState
variable {qs : QSemantics} [RegEncoding qs.Basis] {xWork zWork : Reg}
/-- Smart constructors delegating to `CleanClosure`, preserving call sites. -/
theorem zero : QFTWorkspaceCleanState qs xWork zWork 0 := CleanClosure.zero
end QFTWorkspaceCleanState

/--
The public precondition for concrete QFT lowering.  It says only that the
inactive part of the supplied `ExtReg` is large enough and that the two slices
selected by the lowering are initially zero.
-/
structure QFTWorkspaceStateOK
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {k : ℕ}
    (ops : Prog k)
    (r : ExtReg)
    (ψ : qs.State) :
    Prop where

  static : QFTReserveOK ops r

  clean :
    QFTWorkspaceCleanState qs (qftXWork ops r) (qftZWork ops r) ψ

end Shor
