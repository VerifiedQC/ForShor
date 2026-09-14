import FastMultiplication.ShorVerification.Implementation.QFT.Lowering.Workspace
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Workspace

/-!
# Shor Workspace Budgets

The static reserve budgets and capacity/isolation conditions used by Shor's
lowering readiness proofs.
-/
namespace Shor

/-- Workspace required on each register family by lowered Shor order finding. -/
structure ShorWorkspaceNeed where
  /-- Reserve needed on the exponent register, mainly for QFT lowering. -/
  exponent : ℕ
  /-- Reserve needed on the modular data register across all ModExp stages. -/
  data : ℕ
  /-- Reserve needed on the auxiliary/work register across all ModExp stages. -/
  auxiliary : ℕ
  /-- Reserve needed by the concrete Step-3/4 scratch register. -/
  scratch : ℕ

/-- Total reserve required for lowering a QFT of width `n`. -/
def qftReserveNeed
    {k : ℕ}
    (ops : Prog k)
    (n : ℕ) : ℕ :=
  (qftWorkspaceNeed ops n).1 +
  (qftWorkspaceNeed ops n).2

/--
Compute the reserve required from the exponent, data, auxiliary, and comparator
scratch registers
when lowering the approximate Shor order-finding circuit.
-/
def shorWorkspaceNeed
    {k : ℕ}
    (ops : Prog k)
    (x data work scratch : ExtReg) :
    ShorWorkspaceNeed :=

  let step1Need :=
    RecursivePhaseWorkspace.reserveNeed ops (data.width + 1) (work.width + 1)

  let step2Need :=
    RecursivePhaseWorkspace.reserveNeed ops (work.width + 1) (data.width + 2)

  let step5Need :=
    RecursivePhaseWorkspace.reserveNeed ops (data.width + 2) (work.width + 1)

  let step4Need :=
    RecursivePhaseWorkspace.reserveNeed ops (work.width + 1) (scratch.width + 1)

  {
    exponent := qftReserveNeed ops x.width

    data :=
      (max (2 + step1Need.1)
        (max (1 + qftReserveNeed ops (data.width + 1))
          (max (2 + step2Need.2) (2 + step5Need.1))))

    auxiliary :=
      (max (qftReserveNeed ops work.width)
        (max (1 + step1Need.2)
          (max (1 + step2Need.1)
            (max (1 + step4Need.1) (1 + step5Need.2)))))

    scratch :=
      max (qftReserveNeed ops scratch.width) (1 + step4Need.2)
  }


/--
The exponent, data, auxiliary, and comparator scratch registers contain enough inactive reserve
for lowering the complete approximate Shor order-finding circuit.
-/
structure ShorWorkspaceLargeEnough
    {k : ℕ}
    (ops : Prog k)
    (x data work scratch : ExtReg) :
    Prop where

  /-- The exponent reserve meets the computed QFT-lowering budget. -/
  exponent_large_enough :
    (shorWorkspaceNeed ops x data work scratch).exponent
      ≤ x.capacity

  /-- The data reserve covers carry bits, QFT workspace, and phase-product use. -/
  data_large_enough :
    (shorWorkspaceNeed ops x data work scratch).data
      ≤ data.capacity

  /-- The auxiliary reserve covers QFT and all phase-product workspaces. -/
  auxiliary_large_enough :
    (shorWorkspaceNeed ops x data work scratch).auxiliary
      ≤ work.capacity

  /-- Scratch reserve covers its QFT, phase-product sign bit, and Step-3 unit bit. -/
  scratch_large_enough :
    (shorWorkspaceNeed ops x data work scratch).scratch
      ≤ scratch.capacity

/--
The reserve belonging to the exponent register is not reused by the
auxiliary register or comparator flag.
-/
structure ShorWorkspaceIsolation
    (x work scratch : ExtReg)
    (flag : ℕ) :
    Prop where

  /-- The exponent-owned qubits are separate from the auxiliary workspace. -/
  exponent_work_disjoint :
    ExtReg.OwnedDisjoint x work

  /-- The exponent-owned qubits are separate from comparator scratch. -/
  exponent_scratch_disjoint :
    ExtReg.OwnedDisjoint x scratch

  /-- The comparator flag is not part of the exponent register ownership. -/
  flag_outside_exponent :
    flag ∉ x.ownedQubits

end Shor
