import FastMultiplication.ShorVerification.Implementation.QFT.Proofs.LoweringCorrectness.Readiness
import FastMultiplication.ShorVerification.Implementation.QFT.Proofs.Lowering
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Main
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Defs
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.Lowering
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.GateSemanticsLemmas
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Proofs.ModExp
import FastMultiplication.ShorVerification.Framework.Submission
import FastMultiplication.ShorVerification.Framework.Math.ShorDefinition
import FastMultiplication.ShorVerification.Framework.Math.Factoring_Reduction.Reduction
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Shor Definitions

The definitional vocabulary the top-level Shor correctness statements need to
elaborate.  All supporting lemmas live under `Shor.Proofs`.
-/
namespace Shor


/-!
# Whole-Program Lowering

The public whole-program lowerer does not ask its caller to construct QFT or
phase-product lowering plans.  Instead, the caller proves one recursive static
workspace condition on the source gate.  At each QFT or signed-phase-product
node, that proof supplies the reserve-capacity facts needed by the already
defined concrete lowerer.

Cleanliness is deliberately absent from `GateWorkspaceOK`: it is a condition
on the input state, not a condition on the syntax or physical register layout.
It belongs in the later semantic-correctness theorem.
-/

universe u

/-! =========================================================
    Section 1: Static workspace precondition
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

  | _ =>
      True

namespace GateWorkspaceOK

end GateWorkspaceOK

/-! =========================================================
    Section 2: Whole-program lowering
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

  | Gate.QFT r, hworkspace =>
      lowerQFT
        k hk ops r hworkspace

  | Gate.SignedPhaseProd phi x z, hworkspace =>
      lowerSignedPhaseProdWithWorkspace k hk phi x z ops hworkspace

  | Gate.CSignedPhaseProd ctrl phi x z, hworkspace =>
    lowerCSignedPhaseProdWithWorkspace k hk ctrl phi x z ops hworkspace

  | Gate.Prim tag args, _ =>
      LowGate.Prim tag args

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
    Section 3: Definitional equations
========================================================= -/

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
            (lowerGate (Basis := qs.Basis)  k hk ops U hworkspace.1) ψ)

    | Gate.adj U, hworkspace, ψ =>
      GateWorkspaceCleanState  qs k hk ops U hworkspace (qs.eval (Gate.adj U) ψ)

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

  | _, _, _ =>
      True



/-!
# Shor workspace budgets and clean-state predicates

This file is the layer for the workspace directory. It names the static reserve
budgets and the dynamic clean-state invariants used by
`Workspace.ShorReadiness`.

Main declarations:

* `shorWorkspaceNeed` computes the reserve budget for exponent, data, and
  auxiliary registers.
* `ShorWorkspaceLargeEnough` is the public static capacity assumption.
* `ShorLoweringCleanState` is the clean-state invariant preserved by lowered
  Shor stages after the data carry bit is allowed to be live.
* `shorLoweringCleanState_ket` is the entry lemma that turns an initially clean
  basis state into the lowered clean invariant.
-/

/-! =========================================================
    Section 1: Static reserve budgets
========================================================= -/

/-- Workspace required on each register by lowered Shor order finding. -/
structure ShorWorkspaceNeed where
  exponent : ℕ
  data : ℕ
  auxiliary : ℕ

/-- Total reserve required for lowering a QFT of width `n`. -/
def qftReserveNeed
    {k : ℕ}
    (ops : Prog k)
    (n : ℕ) : ℕ :=
  (qftWorkspaceNeed ops n).1 +
  (qftWorkspaceNeed ops n).2

/--
Compute the reserve required from the exponent, data, and auxiliary registers
when lowering the approximate Shor order-finding circuit.
-/
def shorWorkspaceNeed
    {k : ℕ}
    (ops : Prog k)
    (x data work : ExtReg) :
    ShorWorkspaceNeed :=

  let step1Need :=
    RecursivePhaseWorkspace.reserveNeed ops (data.width + 1) (work.width + 1)

  let step2Need :=
    RecursivePhaseWorkspace.reserveNeed ops (work.width + 1) (data.width + 2)

  let step5Need :=
    RecursivePhaseWorkspace.reserveNeed ops (data.width + 2) (work.width + 1)

  {
    exponent := qftReserveNeed ops x.width

    data :=
      (max (2 + step1Need.1)
        (max (1 + qftReserveNeed ops (data.width + 1))
          (max (2 + step2Need.2) (2 + step5Need.1))))

    auxiliary :=
      (max (qftReserveNeed ops work.width)
        (max (1 + step1Need.2) (max (1 + step2Need.1) (1 + step5Need.2))))
  }


/--
The exponent, data, and auxiliary registers contain enough inactive reserve
for lowering the complete approximate Shor order-finding circuit.
-/
structure ShorWorkspaceLargeEnough
    {k : ℕ}
    (ops : Prog k)
    (x data work : ExtReg) :
    Prop where

  exponent_large_enough :
    (shorWorkspaceNeed ops x data work).exponent
      ≤ x.capacity

  data_large_enough :
    (shorWorkspaceNeed ops x data work).data
      ≤ data.capacity

  auxiliary_large_enough :
    (shorWorkspaceNeed ops x data work).auxiliary
      ≤ work.capacity

/-! =========================================================
    Section 2: Public workspace preconditions
========================================================= -/

/--
Every reserve register that may be used during Shor lowering is initially zero.
-/
def ShorWorkspaceCleanInput
    {Basis : Type u}
    [RegEncoding Basis]
    (x y work : ExtReg)
    (b0 : Basis) :
    Prop :=
  FreshZero x.reserve b0 ∧
  FreshZero y.reserve b0 ∧
  FreshZero work.reserve b0

/--
The reserve belonging to the exponent register is not reused by the
auxiliary register or comparator flag.
-/
structure ShorWorkspaceIsolation
    (x work : ExtReg)
    (flag : ℕ) :
    Prop where

  exponent_work_disjoint :
    ExtReg.OwnedDisjoint x work

  flag_outside_exponent :
    flag ∉ x.ownedQubits

/-! =========================================================
    Section 3: Dynamic clean-state invariants

    The main invariant for lowered readiness is `ShorLoweringCleanState`.
    The older full/carry predicates are kept as small bridge names because
    several imported correctness statements still expose them.
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


open Gate
open Classical

/-!
# Order-finding circuits and lowered Shor setup data

This module contains the circuit/setup declarations used by Shor workspace
readiness and by the final Shor correctness statements.

Main declarations:

* `orderFindingApprox` is the high-level circuit whose lowering workspace is
  proved ready in `Workspace.ShorReadiness`.
* `orderFindingApproxLow` applies the public lowerer once readiness is known.
* `ShorApproxSetup` collects the user-facing layout, workspace, precision, and
  clean-input assumptions for approximate Shor.
* `ShorApproxSetup.toIdealOrderFindingInput` is the final bridge from the
  approximate setup to the ideal order-finding input predicate.
-/

/-! =========================================================
    Section 1: Order-finding circuit definitions
========================================================= -/

def initY1 (y : Reg) : Gate :=
  match y.qubits with
  | [] => Gate.id
  | q :: _ => Gate.X q

/-- Approximate order finding using the proved valid-input ModExp circuit. -/
noncomputable def orderFindingApprox
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (a N : ℕ)
    (x y work : ExtReg)
    (flag : ℕ)
    (hworkspace : ModMulCircuitWorkspaceOK y work) : Gate :=
  (H_reg x.active) ;;
  (initY1 y.active) ;;
  (modExpApproxValid (Basis := qs.Basis) a N x.active y work flag hworkspace) ;;
  (IQFT x)


/-- The lowered implementation of approximate order finding. -/
noncomputable def orderFindingApproxLow
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (k : ℕ) (hk : 1 < k)
    (ops : Prog k)
    (a N : ℕ)
    (x y work : ExtReg)
    (flag : ℕ)
    (hmodWorkspace : ModMulCircuitWorkspaceOK y work)
    (hLowerWorkspace :
      GateWorkspaceOK ops (orderFindingApprox qs a N x y work flag hmodWorkspace)) :=
  lowerGate (Basis := qs.Basis) k hk ops
    (orderFindingApprox qs a N x y work flag hmodWorkspace) hLowerWorkspace

/-- Ideal order-finding circuit using exact modular exponentiation. -/
noncomputable def orderFindingIdeal
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [Spec]
    (a N : ℕ)
    (x y : ExtReg) : Gate :=
  (H_reg x.active) ;;
  (initY1 y.active) ;;
  (modExpIdeal' qs a N x.active y.active) ;;
  (IQFT x)

/-! =========================================================
    Section 2: Lowering setup
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
    Section 3: Approximate and ideal input predicates
========================================================= -/

/-- The input basis state is clean on every register used by Shor. -/
def ShorCleanInput
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (x y work : ExtReg)
    (flag : ℕ)
    (b0 : qs.Basis) : Prop :=
  RegEncoding.toNat x.active b0 = 0 ∧
  RegEncoding.toNat y.active b0 = 0 ∧
  y.FreshFor 2 b0 ∧
  RegEncoding.toNat work.active b0 = 0 ∧
  work.FreshFor 1 b0 ∧
  RegEncoding.toNat (qubitReg flag) b0 = 0

/--
Public assumptions for the approximate implementation of Shor.
-/
structure ShorApproxSetup
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (η : ℝ)
    (x y work : ExtReg)
    (flag : ℕ)
    (b0 : qs.Basis) : Prop where
  /-- The exponent, data, work, carry, and flag qubits do not overlap. -/
  register_layout :
    ModExpLayout x.active y work flag

  circuit_workspace :
    ModMulCircuitWorkspaceOK y work

  exponent_data_disjoint :
    ExtReg.OwnedDisjoint x y

  /-- The work register has enough extra bits for precision `η`. -/
  work_precision :
    Algorithm1Precision η y.active work.active

  /-- Shor begins in `|0⋯0⟩` on all registers it uses. -/
  clean_input :
    ShorCleanInput qs x y work flag b0

structure ShorApproxSetupMinimal
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (η : ℝ)
    (x data work : ExtReg)
    (flag : ℕ)
    (b0 : qs.Basis) :
    Prop where

  /- The data register has two available reserve qubits. -/
  data_can_grow_two :
    data.CanGrow 2

  /- The work register has one available reserve qubit. -/
  work_can_grow_one :
    work.CanGrow 1

  /- The exponent and data registers have no common owned qubits. -/
  exponent_data_disjoint :
    ExtReg.OwnedDisjoint x data

  /- The data and work registers have no common owned qubits. -/
  data_work_disjoint :
    ExtReg.OwnedDisjoint data work

  /- The flag is not owned by the data register. -/
  flag_outside_data :
    flag ∉ data.ownedQubits

  /- The flag is not owned by the work register. -/
  flag_outside_work :
    flag ∉ work.ownedQubits

  /- No active exponent/control qubit is owned by the work register. -/
  controls_outside_work :
    ∀ q ∈ x.active.qubits,
      q ∉ work.ownedQubits

  /- The flag is not an active exponent/control qubit. -/
  flag_outside_controls :
    flag ∉ x.active.qubits
  /-
  The error parameter and active work-register width satisfy
  Algorithm 1's precision requirement.
  -/
  algorithm1_precision :
    Algorithm1Precision
      η data.active work.active

  /- The exponent register starts at zero. -/
  exponent_zero :
    RegEncoding.toNat x.active b0 = 0

  /- The modular data register starts at zero. -/
  data_zero :
    RegEncoding.toNat data.active b0 = 0

  /- The two temporary data-extension qubits start at zero. -/
  data_fresh :
    data.FreshFor 2 b0

  /- The active work register starts at zero. -/
  work_zero :
    RegEncoding.toNat work.active b0 = 0

  /- The temporary work-extension qubit starts at zero. -/
  work_fresh :
    work.FreshFor 1 b0

  /-- The comparison flag starts at zero. -/
  flag_zero :
    RegEncoding.toNat (qubitReg flag) b0 = 0


open Gate
open Classical

/-!
# Shor workspace readiness and clean-state preservation

This module contains the lowered workspace readiness and dynamic clean-state
preservation results for the approximate Shor order-finding circuit.

Organization:

* Static readiness: `gateWorkspaceOK_orderFindingApprox` and
  `LoweredShorReady.workspace`.
* Dynamic infrastructure: `LoweredCleanResult`, workspace-free gates,
  disjointness/locality helpers, and clean-state preservation for primitive
  steps.
* Stage readiness: lowered readiness for initialization, Step 1, Step 2,
  Step 5, IQFT, one modular-multiplication core, modular exponentiation, and
  the full order-finding circuit.
* Public final result: `LoweredShorReady.workspace_clean`.
-/

/-! =========================================================
    Section 1: Public static readiness theorem
========================================================= -/

/-! ---------------------------------------------------------
    Static reserve arithmetic helpers
--------------------------------------------------------- -/

/--
Public readiness package for both static workspace availability and dynamic
initial cleanliness.
-/
structure LoweredShorReady
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGateGateBridge qs]
    (lowering : ShorLoweringSetup)
    (η : ℝ)
    (a N : ℕ)
    (x y work : ExtReg)
    (flag : ℕ)
    (b0 : qs.Basis) :
    Prop where

  approx :
    ShorApproxSetupMinimal qs η x y work flag b0

  workspace_large_enough :
    ShorWorkspaceLargeEnough lowering.ops x y work

  workspace_isolated :
    ShorWorkspaceIsolation x work flag

  workspace_initially_zero :
    ShorWorkspaceCleanInput x y work b0
  -- clean :
  --   let hworkspace :=
  --     gateWorkspaceOK_orderFindingApprox (ops := lowering.ops)  (η := η) (a := a) (N := N)
  --       (x := x) (data := y) (work := work) (flag := flag) (b0 := b0) approx workspace_large_enough

  --   GateWorkspaceCleanState qs lowering.k lowering.hk lowering.ops
  --     (orderFindingApprox qs a N x y work flag  approx.circuit_workspace)
  --     hworkspace (qs.ket b0)
/-! =========================================================
    Section 2: Clean-result sequencing infrastructure
========================================================= -/

/-!
`LoweredCleanResult P G hworkspace ψ` says:

1. every recursively lowered gate in `G` starts with clean local workspace;
2. after executing the lowered `G`, the state satisfies `P`.
-/
/-! =========================================================
    Section 3: Workspace-free gates

    These gates have no recursive lowerer workspace obligations. The final
    helper of this section, `WorkspaceFree.clean`, turns that syntactic fact
    into `GateWorkspaceCleanState`.
========================================================= -/

/-! =========================================================
    Section 4: Primitive locality and Step 3/4 readiness

    The disjointness helpers feed the primitive semantic locality assumptions
    for Steps 3 and 4. The final theorems in this section are
    `lowered_step3_ready_and_clean` and `lowered_step4_ready_and_clean`.
========================================================= -/

/-! =========================================================
    Section 5: Workspace-free initialization gates

    These helpers cover `H_reg x.active` and `initY1 data.active`, which do not
    allocate recursive lowering workspace but must still preserve the global
    lowered clean invariant.
========================================================= -/

/-! =========================================================
    Section 6: Step 1 readiness

    Step 1 uses the data reserve after dropping the carry bit and the full work
    reserve. The final theorem in this section is
    `lowered_step1_ready_and_full_clean`.
========================================================= -/

/-! =========================================================
    Section 7: Step 2 readiness

    Step 2 makes the carry bit active, swaps the phase-product operand order,
    and preserves `ShorLoweringCleanState`.
========================================================= -/

/-! =========================================================
    Section 8: Step 5 readiness via adjoint decomposition

    Step 5 is proved by proving the forward Step-5 body clean, then using the
    generic adjoint lemma `LoweredCleanResult.adj`.
========================================================= -/

/-! =========================================================
    Semantic decomposition of adjoint circuits
========================================================= -/

/-! =========================================================
    Step-5 QFT locality
========================================================= -/

/-! =========================================================
    Step-5 workspace subset facts
========================================================= -/
/-! =========================================================
    Adjoint controlled phase-product locality
========================================================= -/
/-! =========================================================
    Elementary Hadamard inverse facts
========================================================= -/
/-! =========================================================
    Locality of a single adjoint Hadamard
========================================================= -/

/-! =========================================================
    Adjoint register-Hadamard locality
========================================================= -/

/-! =========================================================
    Semantic decomposition of the Step-5 adjoint
========================================================= -/

/-! =========================================================
    Main Step-5 adjoint preservation theorem
========================================================= -/

/-! =========================================================
    Section 9: Final inverse QFT readiness
========================================================= -/

/-! =========================================================
    Section 10: One modular-multiplication core
========================================================= -/

/-! =========================================================
    Section 11: Modular exponentiation loop
========================================================= -/

/-! =========================================================
    Section 12: Full order-finding dynamic readiness
========================================================= -/

/-! =========================================================
    Section 13: Public final wrappers
========================================================= -/


open Gate
open Classical

/-!
# Shor/order-finding circuit statement

This file keeps the quantum-facing part of the Shor statement: the ideal and
approximate order-finding circuits, the measurement interface, and the final
success-probability theorem.  Classical order and continued-fraction material
lives in `MathBackbone/ShorAlgorithm.lean`.
-/

/-! =========================================================
    Section 1: Order-finding circuits

    These definitions assemble the high-level gates used by the ideal and
    approximate order-finding algorithms.
========================================================= -/

variable {qs : QSemantics}
variable [RegEncoding qs.Basis]

/-! =========================================================
    Section 2: Measurement and success probabilities

    `MeasureClass` packages the Born-rule projectors used to talk about
    measuring a register.  The lemmas in this section turn those projector
    axioms into the probability estimates needed later:

    * orthogonal projector sums have the expected norm square;
    * measurement mass outside a register range is zero;
    * measurement distributions are Lipschitz in state distance.
========================================================= -/

variable {qs : QSemantics}
variable [RegEncoding qs.Basis]
variable [MeasureClass qs]

/-! ## Projector Hilbert-space estimates -/

/-! ## Measurement distribution distance bounds -/

/-! ## Success probabilities and range facts -/

-- /-- Run the circuit G on input state ψ, then measure register r, and ask for probability of outcome o -/
-- noncomputable def measProbAfter (r : Reg) (o : ℕ) (G : Gate) (ψ : qs.State) : ℝ :=
--   MeasureClass.probMeas (qs := qs) r o (qs.eval G ψ)


variable [ContinuedFractionPost] [Spec]


/-! =========================================================
    Section 3: Probability-transfer lemmas

    These lemmas are the bridge from state-vector approximation to
    success-probability approximation.  The first group is pure real/probability
    bookkeeping; the second group uses gate isometry to move distance bounds
    through common circuit context.
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

/-! =========================================================
    Section 4: Final correctness statements

    The ideal theorem is the quantum order-finding lower bound used by the
    rest of the file.  The approximation theorem transfers that ideal bound
    across the modular-exponentiation implementation error, and the final
    factoring statement combines it with the classical reduction.
========================================================= -/


end Shor
