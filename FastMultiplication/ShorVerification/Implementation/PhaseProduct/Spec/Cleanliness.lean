import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Workspace
import FastMultiplication.ShorVerification.Implementation.Semantics.CleanClosure

/-!
# Phase-Product Cleanliness Predicates

The cleanliness predicates needed to state phase-product readiness/assertions:
compiler-workspace cleanliness during a recursive compile step
(`CompilerWorkspaceOK`, `CleanWorkspaceState`), reserve cleanliness for a
layout (`LayoutReserveCleanBasis`, `LayoutReserveCleanState`), and cleanliness
of the complete reserves (`RecursiveWorkspaceCleanState`,
`SignedRecursiveWorkspaceStateOK`, `CSignedRecursiveWorkspaceStateOK`). Split
out of `DefsCore.lean`, `Proofs/GateLevelCorrectness/SupportLemmas.lean`, and
`Proofs/LoweringCorrectness/Linearity.lean` because these are definitions, not
proofs, and `PhaseLoweringReady`/`Assertions.lean` need them.
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
    {Basis : Type u}
    [RegEncoding Basis]
    {k : ℕ}
    (st : LayoutState k)
    (b : Basis) :
    Prop :=
  (∀ i : Fin k,
    ExtReg.FreshFor
      (st.xslot i)
      (st.xslot i).capacity
      b)
  ∧
  (∀ i : Fin k,
    ExtReg.FreshFor
      (st.zslot i)
      (st.zslot i).capacity
      b)

/-- State-level reserve cleanliness, generated from clean basis states and linear closure. -/
abbrev LayoutReserveCleanState
    (qs : QSemantics) [RegEncoding qs.Basis] {k : ℕ} (st : LayoutState k) : qs.State → Prop :=
  CleanClosure (fun b => LayoutReserveCleanBasis st b)

/-! =========================================================
    Section 7: Cleanliness of the complete reserves
========================================================= -/

/--
Both complete reserve registers are zero in a basis state.
Using `x.capacity` and `z.capacity` means that `FreshFor` covers all of each
reserve, rather than only the bits needed by the first compilation level.
-/
def RecursiveWorkspaceCleanBasis
    {Basis : Type u}
    [RegEncoding Basis]
    (x z : ExtReg)
    (b : Basis) :
    Prop :=
  ExtReg.FreshFor x x.capacity b ∧ ExtReg.FreshFor z z.capacity b

/--
An arbitrary quantum state supported on basis states whose entire `x` and `z`
reserves are zero.
The active data registers may be in an arbitrary superposition. Only the
reserve qubits are constrained.
-/
abbrev RecursiveWorkspaceCleanState
    (qs : QSemantics) [RegEncoding qs.Basis] (x z : ExtReg) : qs.State → Prop :=
  CleanClosure (fun b => RecursiveWorkspaceCleanBasis x z b)

/-! =========================================================
    Section 8: Combined public workspace preconditions
========================================================= -/

/--
The complete public workspace precondition for an uncontrolled signed phase
product.
-/
structure SignedRecursiveWorkspaceStateOK
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {k : ℕ}
    (ops : Prog k)
    (x z : ExtReg)
    (ψ : qs.State) :
    Prop where
  static : SignedRecursiveWorkspaceOK ops x z
  clean : RecursiveWorkspaceCleanState qs x z ψ

/--
The complete public workspace precondition for a controlled signed phase
product.
-/
structure CSignedRecursiveWorkspaceStateOK
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {k : ℕ}
    (ops : Prog k)
    (ctrl : ℕ)
    (x z : ExtReg)
    (ψ : qs.State) :
    Prop where
  static :
    CSignedRecursiveWorkspaceOK
      ops ctrl x z
  clean :
    RecursiveWorkspaceCleanState
      qs x z ψ

end Shor
