import FastMultiplication.ShorVerification.Implementation.QFT.Proofs.LoweringCorrectness.Readiness
import FastMultiplication.ShorVerification.Implementation.QFT.Defs
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Main
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Defs
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.LoweringCorrectness.Workspace
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.GateLevelCorrectness.GateSemanticsLemmas
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Proofs.ModExp
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.ConstArithmeticLowering
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

The declarations are grouped by the role they play in the final statement:

* generic whole-gate lowering predicates;
* Shor-specific workspace budgets and clean-state assumptions;
* order-finding circuits;
* user-facing setup/readiness records;
* the final classical factoring instance.
-/
namespace Shor

universe u

/-!
## Generic Whole-Gate Lowering

The public whole-program lowerer does not ask its caller to construct QFT or
phase-product lowering plans.  Instead, the caller proves one recursive static
workspace condition on the source gate.  At each QFT or signed-phase-product
node, that proof supplies the reserve-capacity facts needed by the already
defined concrete lowerer.

Cleanliness is deliberately absent from `GateWorkspaceOK`: it is a condition
on the input state, not a condition on the syntax or physical register layout.
It belongs in the later semantic-correctness theorem.
-/

/-! =========================================================
    Static Workspace Precondition
========================================================= -/

/--
Every recursively lowered node in `G` has enough concrete physical workspace.

* A QFT register has enough inactive reserve for the two workspace pools
  selected by `lowerQFT`.
* A signed phase product has enough mutually disjoint reserve for its complete
  recursion.
* A controlled signed phase product additionally keeps its control qubit
  outside both operands' complete owned regions.
* Sequential composition and adjoint recurse structurally.

The remaining constructors lower directly and need no reserve.
-/
def GateWorkspaceOK
    {k : ℕ}
    (ops : Prog k) :
    Gate → Prop
  | Gate.seq U V =>
      GateWorkspaceOK ops U ∧ GateWorkspaceOK ops V
  | Gate.adj U =>
      GateWorkspaceOK ops U
  | Gate.QFT r =>
      QFTReserveOK ops r
  | Gate.SignedPhaseProd _ x z =>
      SignedRecursiveWorkspaceOK ops x z
  | Gate.CSignedPhaseProd ctrl _ x z =>
      CSignedRecursiveWorkspaceOK ops ctrl x z
  | Gate.CmpGeConst N data scratch flag =>
      ConstArithmeticWorkspace N data scratch flag
  | Gate.CSubConst N data scratch flag =>
      ConstArithmeticWorkspace N data scratch flag
  | Gate.idealCtrlModMul _ _ _ _ =>
      False
  | _ =>
      True

namespace GateWorkspaceOK

end GateWorkspaceOK

/-! =========================================================
    Whole-Program Lowering
========================================================= -/

/--
Lower an arbitrary high-level gate whose recursive workspace is large enough.

The proof parameter contains no lowering plan.  It supplies only the static
reserve and disjointness facts consumed by the concrete QFT and phase-product
lowerers.

The controlled signed-phase-product branch currently uses the naive controlled
leaf.  The phase-product layer has a controlled plan-directed lowerer, but it
does not yet have the analogue of `standardSignedPhaseLoweringPlan` which
constructs that plan solely from `CSignedRecursiveWorkspaceOK`.  Once that
constructor is added, only this branch needs to change.
-/
noncomputable def lowerGate
    {Basis : Type u}
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k) :
    (G : Gate) →
    GateWorkspaceOK ops G →
    LowGate

  | Gate.id, _ =>
      LowGate.id

  | Gate.seq U V, hworkspace =>
      LowGate.seq
        (lowerGate (Basis := Basis) k hk ops U hworkspace.1)
        (lowerGate (Basis := Basis) k hk ops V hworkspace.2)

  | Gate.adj U, hworkspace =>
      LowGate.adj
        (lowerGate (Basis := Basis) k hk ops U hworkspace)

  | Gate.H qbit, _ =>
      LowGate.H qbit

  | Gate.X qbit, _ =>
      LowGate.X qbit

  | Gate.CNOT ctrl target, _ =>
      LowGate.CNOT ctrl target

  | Gate.Toffoli c₁ c₂ target, _ =>
      LowGate.Toffoli c₁ c₂ target

  | Gate.QFT r, hworkspace =>
      lowerQFT
        k hk ops r hworkspace

  | Gate.SignedPhaseProd phi x z, hworkspace =>
      lowerSignedPhaseProdWithWorkspace k hk phi x z ops hworkspace

  | Gate.CSignedPhaseProd ctrl phi x z, hworkspace =>
      lowerCSignedPhaseProdWithWorkspace k hk ctrl phi x z ops hworkspace

  | Gate.CmpGeConst N data scratch flag, hworkspace =>
      lowerCmpGeConst N data scratch flag hworkspace

  | Gate.CSubConst N data scratch flag, hworkspace =>
      lowerCSubConst N data scratch flag hworkspace

  | Gate.ShiftL r n, _ =>
      LowGate.ShiftL r n

  | Gate.ShiftR r n, _ =>
      LowGate.ShiftR r n

  | Gate.Negate r, _ =>
      LowGate.Negate r

  | Gate.AddScaled dst src negSrc shift, _ =>
      LowGate.AddScaled
        dst src negSrc shift

  | Gate.zeroExtend r n, _ =>
      LowGate.zeroExtend r n

  | Gate.signExtend r n, _ =>
      LowGate.signExtend r n

  | Gate.zeroDealloc r n, _ =>
      LowGate.zeroDealloc r n

  | Gate.signDealloc r n, _ =>
      LowGate.signDealloc r n

  | Gate.RadixReverse r m, _ =>
      LowGate.RadixReverse r m


/-! =========================================================
    Dynamic Clean-State Precondition
========================================================= -/

/--
Runtime cleanliness required before evaluating each recursively lowered node.

For a sequence, cleanliness is threaded through the first lowered component
before checking the second.  For adjoints, the condition is phrased on the state
that would appear before the forward circuit.  Primitive and direct low-level
constructors carry no recursive workspace-cleanliness obligation here.
-/
noncomputable def GateWorkspaceCleanState
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [LowerGateClass qs]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k) :
    (G : Gate) →
    GateWorkspaceOK ops G →
    qs.State →
    Prop

  | Gate.id, _, _ =>
      True

  | Gate.seq U V, hworkspace, ψ =>
      GateWorkspaceCleanState qs k hk ops U hworkspace.1 ψ
        ∧
      GateWorkspaceCleanState qs k hk ops V hworkspace.2
          (LowerGateClass.evalL (qs := qs)
            (lowerGate (Basis := qs.Basis) k hk ops U hworkspace.1) ψ)

  | Gate.adj U, hworkspace, ψ =>
      GateWorkspaceCleanState qs k hk ops U hworkspace (qs.eval (Gate.adj U) ψ)

  | Gate.H _, _, _ =>
      True

  | Gate.X _, _, _ =>
      True

  | Gate.QFT r, _, ψ =>
      QFTWorkspaceCleanState qs (qftXWork ops r) (qftZWork ops r) ψ

  | Gate.SignedPhaseProd _ x z, _, ψ =>
      RecursiveWorkspaceCleanState qs x z ψ

  | Gate.CSignedPhaseProd _ _ x z, _, ψ =>
      RecursiveWorkspaceCleanState qs x z ψ

  | Gate.CmpGeConst _ data scratch _, _, ψ =>
      CmpGeConstCleanState qs data scratch ψ

  | Gate.CSubConst N data scratch flag, _, ψ =>
      CSubConstCleanState qs N data scratch flag ψ

  | _, _, _ =>
      True

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
Every reserve register that may be used during Shor lowering is initially zero.
-/
def ShorWorkspaceCleanInput
    {Basis : Type u}
    [RegEncoding Basis]
    (x y work scratch : ExtReg)
    (b0 : Basis) :
    Prop :=
  FreshZero x.reserve b0 ∧
  FreshZero y.reserve b0 ∧
  FreshZero work.reserve b0 ∧
  FreshZero scratch.reserve b0

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

/-! =========================================================
    Dynamic Clean-State Names

    Proof files extend these namespaces with induction and preservation lemmas.
    The names are kept here so users can read the public invariant vocabulary
    without opening the proof development.
========================================================= -/

/--
A state supported on basis states in which three specified registers are zero.
-/
abbrev ThreeRegsCleanState
    (qs : QSemantics) [RegEncoding qs.Basis] (r₁ r₂ r₃ : Reg) :
    qs.State → Prop :=
  CleanClosure (fun b => FreshZero r₁ b ∧ FreshZero r₂ b ∧ FreshZero r₃ b)

namespace ThreeRegsCleanState
variable {qs : QSemantics} [RegEncoding qs.Basis] {r₁ r₂ r₃ : Reg}
end ThreeRegsCleanState

namespace FullShorWorkspaceCleanState
variable {qs : QSemantics} [RegEncoding qs.Basis] {x data work : ExtReg}
end FullShorWorkspaceCleanState

namespace ShorLoweringCleanState
variable {qs : QSemantics} [RegEncoding qs.Basis] {x data work : ExtReg}
end ShorLoweringCleanState


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
noncomputable def orderFindingApprox
    (qs : QSemantics)
    [RegEncoding qs.Basis]
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
    (Basis := qs.Basis)
    a N x.active y work scratch flag
    hworkspace hstep4) ;;
  (IQFT x)


/-- The lowered implementation of approximate order finding. -/
noncomputable def orderFindingApproxLow
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (k : ℕ) (hk : 1 < k)
    (ops : Prog k)
    (a N : ℕ)
    (x y work scratch : ExtReg)
    (flag : ℕ)
    (hmodWorkspace : ModMulCircuitWorkspaceOK y work)
    (hstep4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hLowerWorkspace : GateWorkspaceOK ops (orderFindingApprox qs a N x y work scratch flag
          hmodWorkspace hstep4)) :=
  lowerGate (Basis := qs.Basis) k hk ops (orderFindingApprox qs a N x y work scratch flag hmodWorkspace hstep4)
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

/-! =========================================================
    Lowering Program Setup
========================================================= -/

/-- Low-level lowering assumptions shared by lowered Shor statements. -/
structure ShorLoweringSetup where
  /-- Number of synthesis registers used by the lowering program. -/
  k : ℕ
  /-- At least two synthesis registers are available. -/
  hk : 1 < k
  /-- Program that consumes the interpolation points used by lowering. -/
  ops : Prog k
  /-- The point-consuming program is safe. -/
  consumes :
    ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops (genInterpolationPoints k)
  /-- The point-consuming program uncomputes back to the start state. -/
  returns : run? ops State.start_state = some State.start_state

/-! =========================================================
    Approximate And Ideal Input Predicates
========================================================= -/

/-- The input basis state is clean on every register used by Shor. -/
def ShorCleanInput
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (x y work scratch : ExtReg)
    (flag : ℕ)
    (b0 : qs.Basis) : Prop :=
  RegEncoding.toNat x.active b0 = 0 ∧
  RegEncoding.toNat y.active b0 = 0 ∧
  y.FreshFor 2 b0 ∧
  RegEncoding.toNat work.active b0 = 0 ∧
  work.FreshFor 1 b0 ∧
  RegEncoding.toNat scratch.active b0 = 0 ∧
  scratch.FreshFor 1 b0 ∧
  RegEncoding.toNat (qubitReg flag) b0 = 0

/-- Public assumptions for the approximate implementation of Shor. -/
structure ShorApproxSetup
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (η : ℝ)
    (N : ℕ)
    (x y work scratch : ExtReg)
    (flag : ℕ)
    (b0 : qs.Basis) : Type where
  /-- The exponent, data, work, carry, and flag qubits do not overlap. -/
  register_layout :
    ModExpLayout x.active y work flag

  /-- The modular-exponentiation subcircuit has enough local workspace. -/
  circuit_workspace :
    ModMulCircuitWorkspaceOK y work

  /-- The concrete Step-4 comparator and its Step-3 scratch are well laid out. -/
  step4_workspace :
    CmpLtNWWorkspace N (y.grow 1) work scratch flag

  /-- The exponent register is owned separately from the modular data register. -/
  exponent_data_disjoint :
    ExtReg.OwnedDisjoint x y

  /-- The exponent register is owned separately from comparator scratch. -/
  exponent_scratch_disjoint :
    ExtReg.OwnedDisjoint x scratch

  /-- The work register has enough extra bits for precision `η`. -/
  work_precision :
    Algorithm1Precision η y.active work.active

  /-- Shor begins in `|0⋯0⟩` on all registers it uses. -/
  clean_input :
    ShorCleanInput qs x y work scratch flag b0

/--
Lower-level assumptions from which the public approximate setup is reconstructed
in `Shor.Proofs.OrderFinding`.
-/
structure ShorApproxSetupMinimal
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (η : ℝ)
    (N : ℕ)
    (x data work scratch : ExtReg)
    (flag : ℕ)
    (b0 : qs.Basis) :
    Type where

  /-- The data register has two available reserve qubits. -/
  data_can_grow_two :
    data.CanGrow 2

  /-- The work register has one available reserve qubit. -/
  work_can_grow_one :
    work.CanGrow 1

  /-- The comparator scratch layout is the same one used by Steps 3 and 4. -/
  step4_workspace :
    CmpLtNWWorkspace N (data.grow 1) work scratch flag

  /-- The exponent and data registers have no common owned qubits. -/
  exponent_data_disjoint :
    ExtReg.OwnedDisjoint x data

  /-- The exponent register is owned separately from comparator scratch. -/
  exponent_scratch_disjoint :
    ExtReg.OwnedDisjoint x scratch

  /-- The data and work registers have no common owned qubits. -/
  data_work_disjoint :
    ExtReg.OwnedDisjoint data work

  /-- The flag is not owned by the data register. -/
  flag_outside_data :
    flag ∉ data.ownedQubits

  /-- The flag is not owned by the work register. -/
  flag_outside_work :
    flag ∉ work.ownedQubits

  /-- No active exponent/control qubit is owned by the work register. -/
  controls_outside_work :
    ∀ q ∈ x.active.qubits,
      q ∉ work.ownedQubits

  /-- The flag is not an active exponent/control qubit. -/
  flag_outside_controls :
    flag ∉ x.active.qubits

  /--
  The error parameter and active work-register width satisfy
  Algorithm 1's precision requirement.
  -/
  algorithm1_precision :
    Algorithm1Precision
      η data.active work.active

  /-- The exponent register starts at zero. -/
  exponent_zero :
    RegEncoding.toNat x.active b0 = 0

  /-- The modular data register starts at zero. -/
  data_zero :
    RegEncoding.toNat data.active b0 = 0

  /-- The two temporary data-extension qubits start at zero. -/
  data_fresh :
    data.FreshFor 2 b0

  /-- The active work register starts at zero. -/
  work_zero :
    RegEncoding.toNat work.active b0 = 0

  /-- The temporary work-extension qubit starts at zero. -/
  work_fresh :
    work.FreshFor 1 b0

  /-- The active comparator scratch register starts at zero. -/
  scratch_zero :
    RegEncoding.toNat scratch.active b0 = 0

  /-- The borrowed comparator reserve bit starts at zero. -/
  scratch_fresh :
    scratch.FreshFor 1 b0

  /-- The comparison flag starts at zero. -/
  flag_zero :
    RegEncoding.toNat (qubitReg flag) b0 = 0

/-!
## Lowered Readiness Package

`LoweredShorReady` is the compact assumption bundle used by public lowered Shor
statements.  The actual construction of its `workspace` and `workspace_clean`
consequences lives in `Shor.Proofs.Readiness`.
-/

/-! =========================================================
    Public Lowered Readiness Record
========================================================= -/

/-- Public readiness package for static workspace and initial cleanliness. -/
structure LoweredShorReady
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (lowering : ShorLoweringSetup)
    (η : ℝ)
    (a N : ℕ)
    (x y work scratch : ExtReg)
    (flag : ℕ)
    (b0 : qs.Basis) :
    Type where

  /-- Layout, precision, and clean active-register assumptions. -/
  approx :
    ShorApproxSetupMinimal qs η N x y work scratch flag b0

  /-- Static reserve capacity is sufficient for all recursive lowerers. -/
  workspace_large_enough :
    ShorWorkspaceLargeEnough lowering.ops x y work scratch

  /-- Shared temporary resources do not overlap unsafe regions. -/
  workspace_isolated :
    ShorWorkspaceIsolation x work scratch flag

  /-- All reserve registers that may be allocated begin at zero. -/
  workspace_initially_zero :
    ShorWorkspaceCleanInput x y work scratch b0

/-!
## Final Factoring Input

The executable circuit definitions above are quantum-facing.  The final Shor
factoring statement also needs a small classical record describing the modulus
to which the order-finding theorem is applied.
-/

/-! =========================================================
    Classical Factoring Instance
========================================================= -/

/-- Classical assumptions on a modulus for the final factoring theorem. -/
structure ShorFactoringInstance where
  /-- The modulus to factor. -/
  N : ℕ
  /-- Shor's classical reduction is stated for odd composite moduli. -/
  odd : Odd N
  /-- The modulus is nontrivial. -/
  gt_two : N > 2
  /-- The modulus is not a prime power. -/
  not_prime_power : ∀ (p k : ℕ), Nat.Prime p → N ≠ p ^ k

end Shor
