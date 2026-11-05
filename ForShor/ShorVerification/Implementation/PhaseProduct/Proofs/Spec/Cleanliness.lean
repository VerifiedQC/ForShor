import ForShor.ShorVerification.Implementation.PhaseProduct.Statement
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.Workspace
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.PolicyWorkspace
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.States

/-!
# Phase-Product Cleanliness Predicates

The cleanliness predicates needed to state phase-product readiness/assertions:
compiler-workspace cleanliness during a recursive compile step
(`CompilerWorkspaceOK`, `CleanWorkspaceState`), reserve cleanliness for a
layout (`LayoutReserveCleanBasis`, `LayoutReserveCleanState`), and cleanliness
of the complete reserves (`RecursiveWorkspaceCleanState`,
`SignedRecursiveWorkspaceStateOK`, `CSignedRecursiveWorkspaceStateOK`).
-/

/-!
# Phase-Product Cleanliness Predicates

The cleanliness predicates needed to state phase-product readiness/assertions:
compiler-workspace cleanliness during a recursive compile step
(`CompilerWorkspaceOK`, `CleanWorkspaceState`), reserve cleanliness for a
layout (`LayoutReserveCleanBasis`, `LayoutReserveCleanState`), and cleanliness
of the complete reserves (`RecursiveWorkspaceCleanState`,
`SignedRecursiveWorkspaceStateOK`, `CSignedRecursiveWorkspaceStateOK`).
-/

namespace Shor

/-- All reserve bits that would be activated when growing to `W` are zero in basis `b`. -/
def LayoutState.CleanForGrowth {Basis : Type u} [RegEncoding Basis] {k : ℕ} (src : LayoutState k) (W : ℕ) (b : Basis) : Prop :=
  (∀ i, ExtReg.FreshFor (src.xslot i) (W - (src.xslot i).width) b) ∧
  (∀ i, ExtReg.FreshFor (src.zslot i) (W - (src.zslot i).width) b)

/-- Concrete workspace hypothesis for running allocation gates from `src` to the scanned width. -/
def CompilerWorkspaceOK {Basis : Type u} [RegEncoding Basis] {k : ℕ} (src : LayoutState k) (need : NeededWidths k) (b : Basis) : Prop :=
  let Wwork := commonNeededWidth need
  src.CanGrowTo Wwork ∧ src.CleanForGrowth Wwork b

/-- Linear closure of basis states whose relevant compiler workspace is clean
(`CleanClosure` at the compiler-workspace-clean predicate). -/
abbrev CleanWorkspaceState (qs : QSemantics) [RegEncoding qs.Basis] {k : ℕ}
    (src : LayoutState k) (need : NeededWidths k) : qs.State → Prop :=
  CleanClosure (fun b => CompilerWorkspaceOK src need b)

/-- A basis state has zeroes in every reserve bit owned by a layout. -/
def LayoutReserveCleanBasis
    {Basis : Type u} [RegEncoding Basis] {k : ℕ} (st : LayoutState k) (b : Basis) : Prop :=
  (∀ i : Fin k, ExtReg.FreshFor (st.xslot i) (st.xslot i).capacity b) ∧
  (∀ i : Fin k, ExtReg.FreshFor (st.zslot i) (st.zslot i).capacity b)

/-- State-level reserve cleanliness, generated from clean basis states and linear closure. -/
abbrev LayoutReserveCleanState
    (qs : QSemantics) [RegEncoding qs.Basis] {k : ℕ} (st : LayoutState k) : qs.State → Prop :=
  CleanClosure (fun b => LayoutReserveCleanBasis st b)

/-! =========================================================
    The policy forms

    Same two records with the policy's static predicate in place of the fixed
    table's. The cleanliness half is unchanged: it is about the registers, not
    about which table will be used on them.
========================================================= -/

/-- The fixed-table precondition is the policy one at `constPolicy`. -/
theorem Policy.workspaceStateOK_const_iff
    {qs : QSemantics} [RegEncoding qs.Basis] {T : ToomCookTable} {x z : ExtReg} {ψ : qs.State} :
    Policy.WorkspaceStateOK qs (ShorLoweringPolicy.constPolicy T) x z ψ ↔
      SignedRecursiveWorkspaceStateOK qs T.ops x z ψ :=
  ⟨fun h => ⟨Policy.workspaceOK_const_iff.mp h.static, h.clean⟩,
   fun h => ⟨Policy.workspaceOK_const_iff.mpr h.static, h.clean⟩⟩

/-- The controlled bridge. -/
theorem Policy.cWorkspaceStateOK_const_iff
    {qs : QSemantics} [RegEncoding qs.Basis] {T : ToomCookTable} {ctrl : ℕ} {x z : ExtReg}
    {ψ : qs.State} :
    Policy.CWorkspaceStateOK qs (ShorLoweringPolicy.constPolicy T) ctrl x z ψ ↔
      CSignedRecursiveWorkspaceStateOK qs T.ops ctrl x z ψ :=
  ⟨fun h => ⟨Policy.cWorkspaceOK_const_iff.mp h.static, h.clean⟩,
   fun h => ⟨Policy.cWorkspaceOK_const_iff.mpr h.static, h.clean⟩⟩

end Shor
