import FastMultiplication.ShorVerification.Implementation.Compilation.LowerGate
import FastMultiplication.ShorVerification.Implementation.QFT.Lowering.Workspace
import FastMultiplication.ShorVerification.Implementation.QFT.Spec.Cleanliness
import FastMultiplication.ShorVerification.Implementation.QFT.Lowering.PlanBuilders
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Coefficients
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Workspace
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Gates.NaiveLeaf
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Lowering.Lower
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Lowering.PlanBuilders
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Spec.Cleanliness
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.Steps
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.ModExp
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.Workspace
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Spec.Precision
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Spec.Validity
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Lowering.ConstArithmetic
import FastMultiplication.ShorVerification.Framework.Submission
import FastMultiplication.ShorVerification.Framework.Math.ShorDefinition
import FastMultiplication.ShorVerification.Framework.Math.Factoring_Reduction.Reduction
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Shor Definitions

The definitional vocabulary the top-level Shor correctness statements need to
elaborate.  This file intentionally contains only public data, predicates, and
circuits; proofs and bridge lemmas live under `Implementation/Shor/Proofs`.
The generic `Gate → LowGate` compiler (`GateWorkspaceOK`, `lowerGate`,
`GateWorkspaceCleanState`) lives in `Implementation/Compilation/LowerGate.lean`,
since it mentions no Shor name. Clean-state predicates live in `Shor.Spec.Cleanliness`;
user-facing setup/readiness records and the classical factoring instance live
in `Shor.Spec.Setup`.

The declarations are grouped by the role they play in the final statement:

* Shor-specific workspace budgets;
* order-finding circuits.
-/
namespace Shor

universe u

/-!
## Shor Workspace Budgets And Clean Inputs

These declarations name the static reserve budgets and initial clean-workspace
conditions used by the readiness proofs.
-/

/-! =========================================================
    Static Reserve Budgets
========================================================= -/

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

/-! =========================================================
    Clean Workspace Inputs And Isolation
========================================================= -/

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

/-!
## Order-Finding Circuits And Setup Data

The approximate circuit uses the verified modular-exponentiation implementation;
the ideal circuit swaps in the abstract exact modular exponentiation gate.  The
setup records below collect the layout, precision, and clean-input assumptions
consumed by the correctness theorems in `Shor.Main`.
-/

/-! =========================================================
    Order-Finding Circuit Definitions
========================================================= -/

/-- Initialize the data register to the computational basis value `1`. -/
def initY1 (y : Reg) : Gate :=
  match y.qubits with
  | [] => Gate.id
  | q :: _ => Gate.X q

/-- Approximate order finding using the proved valid-input ModExp circuit. -/
def orderFindingApprox
    (a N : ℕ)
    (x y work scratch : ExtReg)
    (flag : ℕ)
    (hworkspace : ModMulCircuitWorkspaceOK y work)
    (hstep4 :
      CmpLtNWWorkspace N (y.grow 1) work scratch flag) :
    Gate :=
  (H_reg x.active) ;;
  (initY1 y.active) ;;
  (modExpApproxValid
    a N x.active y work scratch flag
    hworkspace hstep4) ;;
  (IQFT x)


/-- The lowered implementation of approximate order finding. -/
def orderFindingApproxLow
    (k : ℕ) (hk : 1 < k)
    (ops : Prog k)
    (a N : ℕ)
    (x y work scratch : ExtReg)
    (flag : ℕ)
    (hmodWorkspace : ModMulCircuitWorkspaceOK y work)
    (hstep4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hLowerWorkspace : GateWorkspaceOK ops (orderFindingApprox a N x y work scratch flag
          hmodWorkspace hstep4)) :=
  lowerGate k hk ops (orderFindingApprox a N x y work scratch flag hmodWorkspace hstep4)
    hLowerWorkspace

/-- Ideal order-finding circuit using exact modular exponentiation. -/
noncomputable def orderFindingIdeal
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (a N : ℕ)
    (x y : ExtReg) : Gate :=
  (H_reg x.active) ;;
  (initY1 y.active) ;;
  (modExpIdeal' qs a N x.active y.active) ;;
  (IQFT x)

end Shor
