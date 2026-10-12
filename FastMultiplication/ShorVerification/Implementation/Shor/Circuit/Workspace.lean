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
def qftReserveNeedOf (need : ℕ → ℕ × ℕ) (n : ℕ) : ℕ :=
  (need n).1 + (need n).2

/-- The fixed-table spelling. -/
abbrev qftReserveNeed {k : ℕ} (ops : Prog k) (n : ℕ) : ℕ :=
  qftReserveNeedOf (qftWorkspaceNeed ops) n

/-- The policy spelling. -/
abbrev Policy.qftReserveNeed (P : ShorLoweringPolicy) (n : ℕ) : ℕ :=
  qftReserveNeedOf (Policy.qftWorkspaceNeed P) n

/-- Bridge. -/
@[simp] theorem Policy.qftReserveNeed_const (T : ToomCookTable) (n : ℕ) :
    Policy.qftReserveNeed (ShorLoweringPolicy.constPolicy T) n
      = _root_.Shor.qftReserveNeed T.ops n := by
  unfold Policy.qftReserveNeed _root_.Shor.qftReserveNeed
  rw [Policy.qftWorkspaceNeed_const]

/--
Compute the reserve required from the exponent, data, auxiliary, and comparator
scratch registers
when lowering the approximate Shor order-finding circuit.
-/
def shorWorkspaceNeedOf
    (need : ℕ → ℕ × ℕ)
    (res : ℕ → ℕ → ℕ × ℕ)
    (x data work scratch : ExtReg) :
    ShorWorkspaceNeed :=

  let step1Need := res (data.width + 1) (work.width + 1)

  let step2Need := res (work.width + 1) (data.width + 2)

  let step5Need := res (data.width + 2) (work.width + 1)

  let step4Need := res (work.width + 1) (scratch.width + 1)

  {
    exponent := qftReserveNeedOf need x.width

    data :=
      (max (2 + step1Need.1)
        (max (1 + qftReserveNeedOf need (data.width + 1))
          (max (2 + step2Need.2) (2 + step5Need.1))))

    auxiliary :=
      (max (qftReserveNeedOf need work.width)
        (max (1 + step1Need.2)
          (max (1 + step2Need.1)
            (max (1 + step4Need.1) (1 + step5Need.2)))))

    scratch :=
      max (qftReserveNeedOf need scratch.width) (1 + step4Need.2)
  }

/-- The fixed-table spelling. -/
abbrev shorWorkspaceNeed {k : ℕ} (ops : Prog k) (x data work scratch : ExtReg) :
    ShorWorkspaceNeed :=
  shorWorkspaceNeedOf (qftWorkspaceNeed ops) (RecursivePhaseWorkspace.reserveNeed ops)
    x data work scratch

/-- The policy spelling. -/
abbrev Policy.shorWorkspaceNeed (P : ShorLoweringPolicy) (x data work scratch : ExtReg) :
    ShorWorkspaceNeed :=
  shorWorkspaceNeedOf (Policy.qftWorkspaceNeed P) (Policy.reserveNeed P) x data work scratch

/-- Bridge. -/
theorem Policy.shorWorkspaceNeed_const (T : ToomCookTable) (x data work scratch : ExtReg) :
    Policy.shorWorkspaceNeed (ShorLoweringPolicy.constPolicy T) x data work scratch
      = _root_.Shor.shorWorkspaceNeed T.ops x data work scratch := by
  unfold Policy.shorWorkspaceNeed _root_.Shor.shorWorkspaceNeed
  rw [Policy.qftWorkspaceNeed_const,
    show Policy.reserveNeed (ShorLoweringPolicy.constPolicy T)
        = RecursivePhaseWorkspace.reserveNeed T.ops from
      funext fun wx => funext fun wz => Policy.reserveNeed_const T wx wz]


/--
The exponent, data, auxiliary, and comparator scratch registers contain enough inactive reserve
for lowering the complete approximate Shor order-finding circuit.
-/
structure ShorWorkspaceLargeEnoughOf
    (needs : ShorWorkspaceNeed)
    (x data work scratch : ExtReg) :
    Prop where

  /-- The exponent reserve meets the computed QFT-lowering budget. -/
  exponent_large_enough :
    needs.exponent
      ≤ x.capacity

  /-- The data reserve covers carry bits, QFT workspace, and phase-product use. -/
  data_large_enough :
    needs.data
      ≤ data.capacity

  /-- The auxiliary reserve covers QFT and all phase-product workspaces. -/
  auxiliary_large_enough :
    needs.auxiliary
      ≤ work.capacity

  /-- Scratch reserve covers its QFT, phase-product sign bit, and Step-3 unit bit. -/
  scratch_large_enough :
    needs.scratch
      ≤ scratch.capacity

/-- The fixed-table spelling. -/
abbrev ShorWorkspaceLargeEnough {k : ℕ} (ops : Prog k) (x data work scratch : ExtReg) : Prop :=
  ShorWorkspaceLargeEnoughOf (shorWorkspaceNeed ops x data work scratch) x data work scratch

/-- The policy spelling. -/
abbrev Policy.ShorWorkspaceLargeEnough (P : ShorLoweringPolicy)
    (x data work scratch : ExtReg) : Prop :=
  ShorWorkspaceLargeEnoughOf (Policy.shorWorkspaceNeed P x data work scratch)
    x data work scratch

/-- Bridge: at the constant policy the two coincide. -/
theorem Policy.shorWorkspaceLargeEnough_const_iff {T : ToomCookTable}
    {x data work scratch : ExtReg} :
    Policy.ShorWorkspaceLargeEnough (ShorLoweringPolicy.constPolicy T) x data work scratch
      ↔ _root_.Shor.ShorWorkspaceLargeEnough T.ops x data work scratch := by
  unfold Policy.ShorWorkspaceLargeEnough _root_.Shor.ShorWorkspaceLargeEnough
  rw [Policy.shorWorkspaceNeed_const]

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
