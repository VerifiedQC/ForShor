import FastMultiplication.ShorVerification.Implementation.QFT.DefsCore
import FastMultiplication.ShorVerification.Implementation.QFT.QFTLoweringPlan

/-!
# QFT Public Definitions

The single-symbol tip needed to state the QFT lowering-correctness assertion:
`lowerQFT`.  Imports `DefsCore` + `QFTLoweringPlan`.
-/

namespace Shor

open Gate

universe u




/-! =========================================================
    Section 1: Register arithmetic and split helpers
========================================================= -/

variable (qs : QSemantics)
  [RegEncoding qs.Basis]

  [GateSemanticsFacts qs]

namespace Gate.PhaseProdWorkspace

end Gate.PhaseProdWorkspace

/-! =========================================================
    Section 2: Encoding-only split-register lemmas
========================================================= -/

section EncodingOnly
variable (qs : QSemantics) [RegEncoding qs.Basis]

end EncodingOnly

/-! =========================================================
    Section 3: Exponential and qftPhase bridge lemmas
========================================================= -/

/-! =========================================================
    Section 4: Sum-pushing and scalar helper lemmas
========================================================= -/

/-! =========================================================
    Section 5: First split-QFT steps
========================================================= -/

/-! =========================================================
    Section 6: Phase-combination lemmas
========================================================= -/

/-! =========================================================
    Section 7: Reindexing sums and cast utilities
========================================================= -/

open scoped BigOperators


/-! =========================================================
    Section 8: QFT split on basis kets
========================================================= -/

/-! =========================================================
    Section 9: Radix reversal and exact QFT split
========================================================= -/





open Gate


/-! =========================================================
    Section 1: Explicit QFT lowering plans
========================================================= -/

/-! =========================================================
    Section 4: Linearity and workspace preservation
========================================================= -/



open Gate


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

/--
Final public constructor for this file.

The canonical lowered QFT. Its workspace is selected deterministically from
`r.reserve`; callers do not supply separate physical workspace registers.
-/
noncomputable def lowerQFT
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (r : ExtReg)
    (hworkspace : QFTReserveOK ops r) :
    LowGate :=
  lowerQFTPlan
    (reserveQFTLoweringPlan
      k hk ops r hworkspace)


end Shor
