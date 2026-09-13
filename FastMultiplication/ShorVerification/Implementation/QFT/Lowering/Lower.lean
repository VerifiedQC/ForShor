import FastMultiplication.ShorVerification.Implementation.QFT.Lowering.PlanBuilders

namespace Shor


/--
Final public constructor for this file.

The canonical lowered QFT. Its workspace is selected deterministically from
`r.reserve`; callers do not supply separate physical workspace registers.
-/
def lowerQFT
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (r : ExtReg)
    (hworkspace : QFTReserveOK ops r) :
    LowGate :=
  lowerQFTPlan (reserveQFTLoweringPlan k hk ops r hworkspace)


end Shor
