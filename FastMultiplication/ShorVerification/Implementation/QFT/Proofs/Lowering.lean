import FastMultiplication.ShorVerification.Implementation.QFT.Defs
import FastMultiplication.ShorVerification.Implementation.QFT.Proofs.LoweringCorrectness.PlanSemantics
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Defs

/-!
# QFT Lowering Workspace Construction

This file chooses the concrete reserve layout used by the public QFT lowerer
and constructs the canonical recursive QFT lowering plan.

It deliberately stops at construction:

* `qftWorkspaceNeed`, `qftXWork`, and `qftZWork` choose the reserve sizes and
  physical registers;
* `QFTWorkspaceOK` and `QFTReserveOK` record the static disjointness/capacity
  facts;
* `standardQFTLoweringPlan`, `reserveQFTLoweringPlan`, and `lowerQFT` build the
  actual lowered circuit.

The dynamic clean-state and semantic correctness proofs live in
`QFTLoweringCorrectness.Readiness`.

Main declarations:

* `qftWorkspaceNeed`, `qftXWork`, and `qftZWork` choose the reserve budget and
  physical workspace slices.
* `QFTReserveOK.explicitWorkspace` turns one reserve-capacity proof into the
  full recursive workspace object.
* `standardQFTLoweringPlan` is the main recursive construction over ordinary
  registers.
* `lowerQFT` is the final public constructor for the lowered QFT using
  workspace selected from an `ExtReg` reserve.
-/

namespace Shor

open Gate

universe u

/-! =========================================================
    Section 1: Canonical unsigned phase-product plans

    A split QFT uses an unsigned phase product between the left and right
    halves. This section packages that unsigned gate as a standard
    phase-product lowering plan by zero-extending both operands, lowering the
    resulting signed phase product, and deallocating the extensions.
========================================================= -/

/-! =========================================================
    Section 2: Public QFT workspace sizes and clean-state predicates

    The public QFT lowerer takes one `ExtReg`. Its inactive reserve is split
    deterministically into an x-side pool and a z-side pool. The predicates in
    this section are the static and dynamic contracts for those pools.
========================================================= -/

namespace QFTWorkspaceCleanState
variable {qs : QSemantics} [RegEncoding qs.Basis] {xWork zWork : Reg}
theorem ket (b : qs.Basis) (hx : FreshZero xWork b) (hz : FreshZero zWork b) :
    QFTWorkspaceCleanState qs xWork zWork (qs.ket b) := CleanClosure.ket b ⟨hx, hz⟩
theorem add {ψ φ : qs.State} (hψ : QFTWorkspaceCleanState qs xWork zWork ψ)
    (hφ : QFTWorkspaceCleanState qs xWork zWork φ) :
    QFTWorkspaceCleanState qs xWork zWork (ψ + φ) := CleanClosure.add hψ hφ
theorem smul (a : ℂ) {ψ : qs.State} (hψ : QFTWorkspaceCleanState qs xWork zWork ψ) :
    QFTWorkspaceCleanState qs xWork zWork (a • ψ) := CleanClosure.smul a hψ
/-- Custom eliminator so `induction`/`cases` keep the original 2-hypothesis
`ket` shape (`| ket b hx hz`) despite the generic single-predicate closure. -/
@[induction_eliminator, cases_eliminator]
def rec' {motive : (ψ : qs.State) → QFTWorkspaceCleanState qs xWork zWork ψ → Prop}
    (zero : motive 0 QFTWorkspaceCleanState.zero)
    (ket : ∀ (b : qs.Basis) (hx : FreshZero xWork b) (hz : FreshZero zWork b),
        motive (qs.ket b) (QFTWorkspaceCleanState.ket b hx hz))
    (add : ∀ {ψ φ : qs.State} (hψ : QFTWorkspaceCleanState qs xWork zWork ψ)
        (hφ : QFTWorkspaceCleanState qs xWork zWork φ),
        motive ψ hψ → motive φ hφ → motive (ψ + φ) (QFTWorkspaceCleanState.add hψ hφ))
    (smul : ∀ (a : ℂ) {ψ : qs.State} (hψ : QFTWorkspaceCleanState qs xWork zWork ψ),
        motive ψ hψ → motive (a • ψ) (QFTWorkspaceCleanState.smul a hψ))
    {ψ : qs.State} (h : QFTWorkspaceCleanState qs xWork zWork ψ) : motive ψ h := by
  induction h with
  | zero => exact zero
  | ket b hconj => exact ket b hconj.1 hconj.2
  | add hψ hφ ihψ ihφ => exact add hψ hφ ihψ ihφ
  | smul a hψ ih => exact smul a hψ ih
end QFTWorkspaceCleanState

/-! =========================================================
    Section 3: Helper lemmas for the selected workspace slices

    These lemmas prove that the selected workspace registers have the requested
    sizes, remain inside the inactive reserve, and are disjoint from the active
    data register and from each other.
========================================================= -/

namespace QFTReserveOK

end QFTReserveOK


/-! =========================================================
    Section 4: Unfolding and bounds for `qftWorkspaceNeed`

    A nontrivial QFT split must reserve enough space for the middle phase
    product and both recursive QFT calls. These monotonicity lemmas let the
    plan constructor reuse the same workspace pools for each child.
========================================================= -/

/-! =========================================================
    Section 5: Building child workspaces and recursive QFT plans

    The functions and lemmas below carve the two workspace pools into the
    pieces needed by the middle phase product and by the left/right recursive
    QFT calls. They culminate in the canonical plan and public lowered circuit.
========================================================= -/

namespace QFTWorkspaceOK

variable
    {k : ℕ}
    {ops : Prog k}
    {r xWork zWork : Reg}


end QFTWorkspaceOK

end Shor
