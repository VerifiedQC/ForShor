import FastMultiplication.ShorVerification.Implementation.Shor.Circuit.Workspace
import FastMultiplication.ShorVerification.Implementation.Shor.Circuit.OrderFinding
import FastMultiplication.ShorVerification.Implementation.Shor.Spec.Setup
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Budgets
import FastMultiplication.ShorVerification.Implementation.Compilation.Correctness
import FastMultiplication.ShorVerification.Implementation.QFT.Proofs.Lowering.Readiness
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Proofs.Core
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Proofs.ConstArithmetic
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Proofs.Algorithm1Expansion
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.Workspace
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.Steps
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.ModExp
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.CmpLtNW
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Lowering.ConstArithmetic
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Spec.Validity
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Workspace
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Gates.Macros
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Spec.Cleanliness
import FastMultiplication.ShorVerification.Implementation.Semantics.GateSemanticsLemmas
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.MacroSemantics
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness.Static
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness.Sequencing
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness.Primitives
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness.Init
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness.Step1
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness.Step2

/-!
# Step 5 Readiness via Adjoint Decomposition

Step 5 is proved by proving the forward Step-5 body clean, then using the
generic adjoint lemma `LoweredCleanResult.adj`.

Covers, in order: semantic decomposition of adjoint circuits; Step-5 QFT
locality; Step-5 workspace subset facts; adjoint controlled phase-product
locality; elementary Hadamard inverse facts; locality of a single adjoint
Hadamard and of the adjoint register-Hadamard fold; the semantic
decomposition of the Step-5 adjoint; and the main Step-5 adjoint
preservation theorem.
-/

namespace Shor
open Gate
open Classical

private theorem LoweredCleanResult.adj
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    {lowering : ShorLoweringSetup}
    {P : qs.State → Prop}
    {U : Gate}
    {hworkspace :
      GateWorkspaceOK lowering.ops U}
    {ψ : qs.State}
    (hpost :
      P (qs.eval (†U) ψ))
    (hforward :
      LoweredCleanResult
        qs
        lowering
        P
        U
        hworkspace
        (qs.eval (†U) ψ)) :
    LoweredCleanResult
      qs
      lowering
      P
      (†U)
      hworkspace
      ψ := by
  have hadjClean :
      GateWorkspaceCleanState
        qs
        lowering.k
        lowering.hk
        lowering.ops
        (†U)
        hworkspace
        ψ := by
    change
      GateWorkspaceCleanState
        qs
        lowering.k
        lowering.hk
        lowering.ops
        U
        hworkspace
        (qs.eval (†U) ψ)

    exact hforward.1

  constructor
  · exact hadjClean

  · rw [
      lowerGate_correctness
        qs
        lowering.k
        lowering.hk
        lowering.ops
        lowering.consumes
        lowering.returns
        (†U)
        hworkspace
        ψ
        hadjClean
    ]

    exact hpost

private def step5Forward
    (k5val N ctrl : ℕ)
    (data work : ExtReg)
    (hmod :
      ModMulCircuitWorkspaceOK data work) :
    Gate :=
  let φ : Angle :=
    (2 *
      ((k5val % N : ℕ) : ℚ)) /
    (N : ℚ)

  H_reg work.active ;;
  Gate.CPhaseProdUsing
    ctrl
    φ
    (data.grow 1).active
    work.active
    hmod.step5Workspace ;;
  IQFT hmod.step5Workspace.zExt

private theorem step5_eq_adj_step5Forward
    {Basis : Type u}
    [RegEncoding Basis]
    (k5val N ctrl : ℕ)
    (data work : ExtReg)
    (hmod :
      ModMulCircuitWorkspaceOK data work) :
    step5
        k5val N ctrl data work hmod
      =
    †(step5Forward
        k5val N ctrl data work hmod) := by
  rfl

private theorem ThreeRegsCleanState.weaken
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    {r₁ r₂ r₃ s₁ s₂ s₃ : Reg}
    {ψ : qs.State}
    (h₁ :
      ∀ q,
        q ∈ s₁.qubits →
        q ∈ r₁.qubits)
    (h₂ :
      ∀ q,
        q ∈ s₂.qubits →
        q ∈ r₂.qubits)
    (h₃ :
      ∀ q,
        q ∈ s₃.qubits →
        q ∈ r₃.qubits)
    (hclean :
      ThreeRegsCleanState
        qs r₁ r₂ r₃ ψ) :
    ThreeRegsCleanState
      qs s₁ s₂ s₃ ψ := by
  induction hclean with
  | zero =>
      exact ThreeRegsCleanState.zero

  | ket b hr₁ hr₂ hr₃ =>
      exact
        ThreeRegsCleanState.ket
          b
          (FreshZero.of_subset
            s₁ r₁ b h₁ hr₁)
          (FreshZero.of_subset
            s₂ r₂ b h₂ hr₂)
          (FreshZero.of_subset
            s₃ r₃ b h₃ hr₃)

  | add hψ hφ ihψ ihφ =>
      exact ThreeRegsCleanState.add ihψ ihφ

  | smul a hψ ihψ =>
      exact ThreeRegsCleanState.smul a ihψ


private theorem
    threeRegsCleanState_to_grownRecursiveWorkspaceCleanState_of_subset
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    {r₁ r₂ r₃ : Reg}
    {x z : Reg}
    (ws : Gate.PhaseProdWorkspace x z)
    (hxReserve :
      ∀ q,
        q ∈ ws.xExt.reserve.qubits →
        q ∈ r₂.qubits)
    (hzReserve :
      ∀ q,
        q ∈ ws.zExt.reserve.qubits →
        q ∈ r₃.qubits)
    {ψ : qs.State}
    (hclean :
      ThreeRegsCleanState
        qs r₁ r₂ r₃ ψ) :
    RecursiveWorkspaceCleanState
      qs
      (ws.xExt.grow 1)
      (ws.zExt.grow 1)
      ψ := by
  induction hclean with
  | zero =>
      exact CleanClosure.zero

  | ket b h₁ h₂ h₃ =>
      have hxZero :
          FreshZero ws.xExt.reserve b :=
        FreshZero.of_subset
          ws.xExt.reserve
          r₂
          b
          hxReserve
          h₂

      have hzZero :
          FreshZero ws.zExt.reserve b :=
        FreshZero.of_subset
          ws.zExt.reserve
          r₃
          b
          hzReserve
          h₃

      exact
        CleanClosure.ket
          b
          ⟨
            freshFor_grow_capacity_of_freshZero_reserve
              ws.xExt 1 b hxZero,
            freshFor_grow_capacity_of_freshZero_reserve
              ws.zExt 1 b hzZero
          ⟩

  | add hψ hφ ihψ ihφ =>
      exact CleanClosure.add ihψ ihφ

  | smul a hψ ihψ =>
      exact CleanClosure.smul a ihψ


private theorem
    gateWorkspaceCleanState_CPhaseProdUsing_of_threeRegsClean_of_subset
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    {lowering : ShorLoweringSetup}
    {r₁ r₂ r₃ : Reg}
    {x z : Reg}
    (ctrl : ℕ)
    (φ : Angle)
    (ws : Gate.PhaseProdWorkspace x z)
    (hxReserve :
      ∀ q,
        q ∈ ws.xExt.reserve.qubits →
        q ∈ r₂.qubits)
    (hzReserve :
      ∀ q,
        q ∈ ws.zExt.reserve.qubits →
        q ∈ r₃.qubits)
    (hworkspace :
      GateWorkspaceOK
        lowering.ops
        (Gate.CPhaseProdUsing
          ctrl φ x z ws))
    (ψ : qs.State)
    (hclean :
      ThreeRegsCleanState
        qs r₁ r₂ r₃ ψ) :
    GateWorkspaceCleanState
      qs
      lowering.k
      lowering.hk
      lowering.ops
      (Gate.CPhaseProdUsing
        ctrl φ x z ws)
      hworkspace
      ψ := by
  have hrecursive :
      RecursiveWorkspaceCleanState
        qs
        (ws.xExt.grow 1)
        (ws.zExt.grow 1)
        ψ :=
    threeRegsCleanState_to_grownRecursiveWorkspaceCleanState_of_subset
      ws
      hxReserve
      hzReserve
      hclean

  simpa [
    Gate.CPhaseProdUsing,
    GateWorkspaceCleanState,
    lowerGate,
    LowerGateClass.evalL_zeroExtend,
    ExtensionSemantics.eval_zeroExtend
  ] using hrecursive


private theorem
    eval_CPhaseProdUsing_preserves_threeRegsCleanState_of_subset
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {r₁ r₂ r₃ : Reg}
    (ctrl : ℕ)
    (φ : Angle)
    {x z : Reg}
    (ws : Gate.PhaseProdWorkspace x z)
    (hxReserve :
      ∀ q,
        q ∈ ws.xExt.reserve.qubits →
        q ∈ r₂.qubits)
    (hzReserve :
      ∀ q,
        q ∈ ws.zExt.reserve.qubits →
        q ∈ r₃.qubits)
    {ψ : qs.State}
    (hclean :
      ThreeRegsCleanState
        qs r₁ r₂ r₃ ψ) :
    ThreeRegsCleanState
      qs r₁ r₂ r₃
      (qs.eval
        (Gate.CPhaseProdUsing
          ctrl φ x z ws)
        ψ) := by
  induction hclean with
  | zero =>
      rw [qs.eval_zero]
      exact ThreeRegsCleanState.zero

  | ket b h₁ h₂ h₃ =>
      have hxZero :
          FreshZero ws.xExt.reserve b :=
        FreshZero.of_subset
          ws.xExt.reserve
          r₂
          b
          hxReserve
          h₂

      have hzZero :
          FreshZero ws.zExt.reserve b :=
        FreshZero.of_subset
          ws.zExt.reserve
          r₃
          b
          hzReserve
          h₃

      have hwsClean :
          ws.Clean b := by
        constructor
        · exact
            freshFor_of_freshZero_reserve
              ws.xExt 1 b hxZero

        · exact
            freshFor_of_freshZero_reserve
              ws.zExt 1 b hzZero

      rw [
        GateSemanticsFacts.eval_CPhaseProdUsing_ket
          qs ctrl φ x z ws b hwsClean
      ]

      exact
        ThreeRegsCleanState.smul
          _
          (ThreeRegsCleanState.ket
            b h₁ h₂ h₃)

  | add hψ hφ ihψ ihφ =>
      rw [qs.eval_add]
      exact ThreeRegsCleanState.add ihψ ihφ

  | smul a hψ ihψ =>
      rw [qs.eval_smul]
      exact ThreeRegsCleanState.smul a ihψ

private theorem lowered_step5Forward_ready_and_full_clean
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (lowering : ShorLoweringSetup)
    (x data work : ExtReg)
    (k5val N ctrl : ℕ)
    (_hxData :
      ExtReg.OwnedDisjoint x data)
    (hxWork :
      ExtReg.OwnedDisjoint x work)
    (hmod :
      ModMulCircuitWorkspaceOK data work)
    (hworkspace :
      GateWorkspaceOK
        lowering.ops
        (step5Forward
          k5val N ctrl data work hmod))
    (ψ : qs.State)
    (hclean :
      ShorLoweringCleanState
        qs x data work ψ) :
    LoweredCleanResult
      qs
      lowering
      (ShorLoweringCleanState
        qs x data work)
      (step5Forward
        k5val N ctrl data work hmod)
      hworkspace
      ψ := by
  let φ : Angle :=
    (2 *
      ((k5val % N : ℕ) : ℚ)) /
    (N : ℚ)

  let U1 : Gate :=
    H_reg work.active

  let U2 : Gate :=
    Gate.CPhaseProdUsing
      ctrl
      φ
      (data.grow 1).active
      work.active
      hmod.step5Workspace

  let U3 : Gate :=
    IQFT hmod.step5Workspace.zExt

  change
    GateWorkspaceOK lowering.ops U1
      ∧
    GateWorkspaceOK lowering.ops U2
      ∧
    GateWorkspaceOK lowering.ops U3
    at hworkspace

  change
    LoweredCleanResult
      qs
      lowering
      (ShorLoweringCleanState
        qs x data work)
      (U1 ;; U2 ;; U3)
      hworkspace
      ψ

  have hxWorkActive :
      Disjoint x.reserve work.active :=
    reserve_active_disjoint_of_ownedDisjoint
      hxWork

  have hdataWorkActive :
      Disjoint (data.reserve.drop 1) work.active :=
    reserve_drop_active_disjoint_of_ownedDisjoint
      hmod.2.2
      1

  have hworkWorkActive :
      Disjoint work.reserve work.active :=
    Disjoint.symm
      work.active_reserve_disjoint

  have hDataGrowReserve :
      ∀ q,
        q ∈ (data.grow 1).reserve.qubits →
        q ∈ data.reserve.qubits := by
    intro q hq
    have hqTail :
        q ∈ data.reserve.qubits.tail := by
      simpa [
        ExtReg.grow,
        ExtReg.remainingReserve,
        Reg.drop
      ] using hq
    exact List.tail_subset data.reserve.qubits hqTail

  have hStep5XReserve :
      ∀ q,
        q ∈ hmod.step5Workspace.xExt.reserve.qubits →
        q ∈ (data.reserve.drop 1).qubits := by
    intro q hq
    simpa [
      ModMulCircuitWorkspaceOK.step5Workspace,
      Gate.PhaseProdWorkspace.ofExtRegs,
      Gate.PhaseProdWorkspace.xExt,
      ExtReg.withReserve
    ] using hq

  have hStep5ZReserve :
      ∀ q,
        q ∈ hmod.step5Workspace.zExt.reserve.qubits →
        q ∈ work.reserve.qubits := by
    intro q hq
    simpa [
      ModMulCircuitWorkspaceOK.step5Workspace,
      Gate.PhaseProdWorkspace.ofExtRegs,
      Gate.PhaseProdWorkspace.zExt,
      ExtReg.withReserve
    ] using hq

  /- Hadamard stage. -/

  have hU1Clean :
      GateWorkspaceCleanState
        qs
        lowering.k
        lowering.hk
        lowering.ops
        U1
        hworkspace.1
        ψ := by
    exact
      (workspaceFree_H_reg work.active).clean
        hworkspace.1
        ψ

  let ψ1 : qs.State :=
    LowerGateClass.evalL
      (qs := qs)
      (lowerGate
        lowering.k
        lowering.hk
        lowering.ops
        U1
        hworkspace.1)
      ψ

  have hψ1 :
      ShorLoweringCleanState
        qs x data work ψ1 := by
    dsimp only [ψ1]

    rw [
      lowerGate_correctness
        qs
        lowering.k
        lowering.hk
        lowering.ops
        lowering.consumes
        lowering.returns
        U1
        hworkspace.1
        ψ
        hU1Clean
    ]

    simpa only [U1] using
      eval_H_reg_preserves_threeRegsCleanState
        work.active
        x.reserve
        (data.reserve.drop 1)
        work.reserve
        hxWorkActive
        hdataWorkActive
        hworkWorkActive
        hclean

  have hU1 :
      LoweredCleanResult
        qs
        lowering
        (ShorLoweringCleanState
          qs x data work)
        U1
        hworkspace.1
        ψ :=
    ⟨hU1Clean, hψ1⟩

  /- Controlled phase-product stage. -/

  have hU2Clean :
      GateWorkspaceCleanState
        qs
        lowering.k
        lowering.hk
        lowering.ops
        U2
        hworkspace.2.1
        ψ1 := by
    exact
      gateWorkspaceCleanState_CPhaseProdUsing_of_threeRegsClean_of_subset
        ctrl
        φ
        hmod.step5Workspace
        hStep5XReserve
        hStep5ZReserve
        hworkspace.2.1
        ψ1
        hψ1

  let ψ2 : qs.State :=
    LowerGateClass.evalL
      (qs := qs)
      (lowerGate
        lowering.k
        lowering.hk
        lowering.ops
        U2
        hworkspace.2.1)
      ψ1

  have hψ2 :
      ShorLoweringCleanState
        qs x data work ψ2 := by
    dsimp only [ψ2]

    rw [
      lowerGate_correctness
        qs
        lowering.k
        lowering.hk
        lowering.ops
        lowering.consumes
        lowering.returns
        U2
        hworkspace.2.1
        ψ1
        hU2Clean
    ]

    simpa only [U2] using
      eval_CPhaseProdUsing_preserves_threeRegsCleanState_of_subset
        ctrl
        φ
        hmod.step5Workspace
        hStep5XReserve
        hStep5ZReserve
        hψ1

  have hU2 :
      LoweredCleanResult
        qs
        lowering
        (ShorLoweringCleanState
          qs x data work)
        U2
        hworkspace.2.1
        ψ1 :=
    ⟨hU2Clean, hψ2⟩

  /- Inverse-QFT stage. -/

  have hzExtActive :
      hmod.step5Workspace.zExt.active =
        work.active := by
    rfl

  have hxZExt :
      Disjoint
        x.reserve
        hmod.step5Workspace.zExt.active := by
    simpa only [hzExtActive] using hxWorkActive

  have hdataZExt :
      Disjoint
        (data.reserve.drop 1)
        hmod.step5Workspace.zExt.active := by
    simpa only [hzExtActive] using hdataWorkActive

  have hworkZExt :
      Disjoint
        work.reserve
        hmod.step5Workspace.zExt.active := by
    simpa only [hzExtActive] using hworkWorkActive

  have hHighU3 :
      ShorLoweringCleanState
        qs x data work
        (qs.eval U3 ψ2) := by
    simpa only [U3] using
      eval_IQFT_preserves_threeRegsCleanState
        hmod.step5Workspace.zExt
        x.reserve
        (data.reserve.drop 1)
        work.reserve
        hxZExt
        hdataZExt
        hworkZExt
        hψ2

  have hzReserve :
      hmod.step5Workspace.zExt.reserve =
        work.reserve := by
    rfl

  have hQFTLocal :
      QFTWorkspaceCleanState
        qs
        (qftXWork
          lowering.ops
          hmod.step5Workspace.zExt)
        (qftZWork
          lowering.ops
          hmod.step5Workspace.zExt)
        (qs.eval U3 ψ2) := by
    exact
      threeRegsCleanState_to_QFTWorkspaceCleanState
        lowering.ops
        hmod.step5Workspace.zExt
        hzReserve
        hHighU3

  have hU3Clean :
      GateWorkspaceCleanState
        qs
        lowering.k
        lowering.hk
        lowering.ops
        U3
        hworkspace.2.2
        ψ2 := by
    simpa [
      U3,
      IQFT,
      GateWorkspaceCleanState
    ] using hQFTLocal

  have hU3 :
      LoweredCleanResult
        qs
        lowering
        (ShorLoweringCleanState
          qs x data work)
        U3
        hworkspace.2.2
        ψ2 := by
    constructor
    · exact hU3Clean

    · rw [
        lowerGate_correctness
          qs
          lowering.k
          lowering.hk
          lowering.ops
          lowering.consumes
          lowering.returns
          U3
          hworkspace.2.2
          ψ2
          hU3Clean
      ]

      exact hHighU3

  have hU23 :
      LoweredCleanResult
        qs
        lowering
        (ShorLoweringCleanState
          qs x data work)
        (U2 ;; U3)
        hworkspace.2
        ψ1 := by
    apply
      LoweredCleanResult.seq
        hworkspace.2
        ψ1
        hU2

    simpa only [ψ2] using hU3

  have hworkspace123 :
      GateWorkspaceOK lowering.ops (U1 ;; U2 ;; U3) := by
    exact hworkspace

  apply
    LoweredCleanResult.seq
      hworkspace123
      ψ
      hU1

  simpa only [ψ1] using hU23


/-! =========================================================
    Semantic decomposition of adjoint circuits
========================================================= -/

private theorem qeval_injective
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (U : Gate) :
    Function.Injective (qs.eval U) := by
  intro ψ φ h

  have h' :=
    congrArg (qs.eval (†U)) h

  simpa only [qs.eval_adj_apply] using h'

private theorem eval_adj_seq_eq
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (U V : Gate)
    (ψ : qs.State) :
    qs.eval (†(U ;; V)) ψ
      =
    qs.eval (†U)
      (qs.eval (†V) ψ) := by
  apply qeval_injective qs (U ;; V)

  calc
    qs.eval
        (U ;; V)
        (qs.eval (†(U ;; V)) ψ)
        =
      ψ := by
        exact qs.eval_apply_adj (U ;; V) ψ

    _ =
      qs.eval
        (U ;; V)
        (qs.eval (†U)
          (qs.eval (†V) ψ)) := by
        rw [
          qs.eval_seq,
          qs.eval_apply_adj,
          qs.eval_apply_adj
        ]

private theorem eval_adj_adj_eq
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (U : Gate)
    (ψ : qs.State) :
    qs.eval (†(†U)) ψ =
      qs.eval U ψ := by
  apply qeval_injective qs (†U)

  calc
    qs.eval
        (†U)
        (qs.eval (†(†U)) ψ)
        =
      ψ := by
        exact qs.eval_apply_adj (†U) ψ

    _ =
      qs.eval
        (†U)
        (qs.eval U ψ) := by
        symm
        exact qs.eval_adj_apply U ψ

/-! =========================================================
    Step-5 QFT locality
========================================================= -/

private theorem eval_step5_QFT_preserves_full_clean
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (x data work : ExtReg)
    (hxWork :
      ExtReg.OwnedDisjoint x work)
    (hmod :
      ModMulCircuitWorkspaceOK data work)
    (ψ : qs.State)
    (hclean :
      ShorLoweringCleanState
        qs x data work ψ) :
    ShorLoweringCleanState
      qs x data work
      (qs.eval
        (Gate.QFT hmod.step5Workspace.zExt)
        ψ) := by
  have hxWorkActive :
      Disjoint x.reserve work.active :=
    reserve_active_disjoint_of_ownedDisjoint
      hxWork

  have hdataWorkActive :
      Disjoint (data.reserve.drop 1) work.active :=
    reserve_drop_active_disjoint_of_ownedDisjoint
      hmod.2.2
      1

  have hworkWorkActive :
      Disjoint work.reserve work.active :=
    Disjoint.symm
      work.active_reserve_disjoint

  have hzActive :
      hmod.step5Workspace.zExt.active =
        work.active := by
    rfl

  have hxZActive :
      Disjoint
        x.reserve
        hmod.step5Workspace.zExt.active := by
    simpa only [hzActive] using hxWorkActive

  have hdataZActive :
      Disjoint
        (data.reserve.drop 1)
        hmod.step5Workspace.zExt.active := by
    simpa only [hzActive] using hdataWorkActive

  have hworkZActive :
      Disjoint
        work.reserve
        hmod.step5Workspace.zExt.active := by
    simpa only [hzActive] using hworkWorkActive

  induction hclean with
  | zero =>
      rw [qs.eval_zero]
      exact ThreeRegsCleanState.zero

  | ket b hx hdata hwork =>
      classical

      rw [QFTSemantics.eval_QFT_ket]
      apply ThreeRegsCleanState.smul

      let f :
          Fin
              (2 ^
                hmod.step5Workspace.zExt.width) →
            qs.State :=
        fun y =>
          qftPhase
              (2 ^
                hmod.step5Workspace.zExt.width)
              (ExtReg.toNat
                hmod.step5Workspace.zExt
                b)
              y.1
            •
          qs.ket
            (RegEncoding.writeNat
              hmod.step5Workspace.zExt.active
              y.1
              b)

      have hterm :
          ∀ y :
              Fin
                (2 ^
                  hmod.step5Workspace.zExt.width),
            ThreeRegsCleanState
              qs
              x.reserve
              (data.reserve.drop 1)
              work.reserve
              (f y) := by
        intro y

        apply ThreeRegsCleanState.smul
        apply ThreeRegsCleanState.ket

        · unfold FreshZero at hx ⊢
          rw [
            RegEncoding.toNat_left_write_right
              x.reserve
              hmod.step5Workspace.zExt.active
              hxZActive
              b
              y.1
          ]
          exact hx

        · unfold FreshZero at hdata ⊢
          rw [
            RegEncoding.toNat_left_write_right
              (data.reserve.drop 1)
              hmod.step5Workspace.zExt.active
              hdataZActive
              b
              y.1
          ]
          exact hdata

        · unfold FreshZero at hwork ⊢
          rw [
            RegEncoding.toNat_left_write_right
              work.reserve
              hmod.step5Workspace.zExt.active
              hworkZActive
              b
              y.1
          ]
          exact hwork

      have hsum :
          ∀ s :
              Finset
                (Fin
                  (2 ^
                    hmod.step5Workspace.zExt.width)),
            ThreeRegsCleanState
              qs
              x.reserve
              (data.reserve.drop 1)
              work.reserve
              (∑ y ∈ s, f y) := by
        intro s

        induction s using Finset.induction_on with
        | empty =>
            simpa using
              (ThreeRegsCleanState.zero :
                ThreeRegsCleanState
                  qs
                  x.reserve
                  (data.reserve.drop 1)
                  work.reserve
                  0)

        | @insert y s hy ih =>
            rw [Finset.sum_insert hy]
            exact
              ThreeRegsCleanState.add
                (hterm y)
                ih

      simpa [f] using hsum Finset.univ

  | add hψ hφ ihψ ihφ =>
      rw [qs.eval_add]
      exact
        ThreeRegsCleanState.add
          ihψ
          ihφ

  | smul a hψ ihψ =>
      rw [qs.eval_smul]
      exact
        ThreeRegsCleanState.smul
          a
          ihψ


/-! =========================================================
    Step-5 workspace subset facts
========================================================= -/
theorem step5Workspace_xReserve_subset
    {data work : ExtReg}
    (hmod :
      ModMulCircuitWorkspaceOK data work) :
    ∀ q,
      q ∈
          hmod.step5Workspace.xExt.reserve.qubits →
      q ∈ (data.reserve.drop 1).qubits := by
  intro q hq

  change
    q ∈ data.reserve.qubits.drop 1
    at hq

  exact hq

theorem step5Workspace_zReserve_subset
    {data work : ExtReg}
    (hmod :
      ModMulCircuitWorkspaceOK data work) :
    ∀ q,
      q ∈
          hmod.step5Workspace.zExt.reserve.qubits →
      q ∈ work.reserve.qubits := by
  intro q hq

  change q ∈ work.reserve.qubits at hq
  exact hq


/-! =========================================================
    Adjoint controlled phase-product locality
========================================================= -/
theorem
    eval_adj_step5_CPhaseProdUsing_preserves_full_clean
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (x data work : ExtReg)
    (ctrl : ℕ)
    (φ : Angle)
    (hmod :
      ModMulCircuitWorkspaceOK data work)
    (ψ : qs.State)
    (hclean :
      ShorLoweringCleanState
        qs x data work ψ) :
    ShorLoweringCleanState
      qs x data work
      (qs.eval
        (†(Gate.CPhaseProdUsing
          ctrl
          φ
          (data.grow 1).active
          work.active
          hmod.step5Workspace))
        ψ) := by
  let U : Gate :=
    Gate.CPhaseProdUsing
      ctrl
      φ
      (data.grow 1).active
      work.active
      hmod.step5Workspace

  induction hclean with
  | zero =>
      rw [qs.eval_zero]
      exact ThreeRegsCleanState.zero

  | ket b hx hdata hwork =>
      have hxReserveZero :
          FreshZero
            hmod.step5Workspace.xExt.reserve
            b := by
        exact
          FreshZero.of_subset
            hmod.step5Workspace.xExt.reserve
            (data.reserve.drop 1)
            b
            (step5Workspace_xReserve_subset hmod)
            hdata

      have hzReserveZero :
          FreshZero
            hmod.step5Workspace.zExt.reserve
            b := by
        exact
          FreshZero.of_subset
            hmod.step5Workspace.zExt.reserve
            work.reserve
            b
            (step5Workspace_zReserve_subset hmod)
            hwork

      have hworkspaceClean :
          hmod.step5Workspace.Clean b := by
        constructor
        · exact
            freshFor_of_freshZero_reserve
              hmod.step5Workspace.xExt
              1
              b
              hxReserveZero

        · exact
            freshFor_of_freshZero_reserve
              hmod.step5Workspace.zExt
              1
              b
              hzReserveZero

      let c : ℂ :=
        if RegEncoding.bit ctrl b then
          Complex.exp
            (((Angle.toReal φ : ℝ) : ℂ) * Complex.I *
              ((RegEncoding.toNat
                  (data.grow 1).active
                  b : ℂ) *
               (RegEncoding.toNat
                  work.active
                  b : ℂ)))
        else
          1

      have hforward :
          qs.eval U (qs.ket b) =
            c • qs.ket b := by
        simpa only [U, c] using
          GateSemanticsFacts.eval_CPhaseProdUsing_ket
            qs
            ctrl
            φ
            (data.grow 1).active
            work.active
            hmod.step5Workspace
            b
            hworkspaceClean

      have hc :
          c ≠ 0 := by
        dsimp only [c]

        split
        · exact Complex.exp_ne_zero _
        · simp

      have hinverse :
          qs.eval (†U)
              (qs.eval U (qs.ket b))
            =
          qs.ket b :=
        qs.eval_adj_apply U (qs.ket b)

      rw [hforward, qs.eval_smul] at hinverse

      have hscaled :=
        congrArg
          (fun ξ : qs.State =>
            c⁻¹ • ξ)
          hinverse

      have hadjoint :
          qs.eval (†U) (qs.ket b)
            =
          c⁻¹ • qs.ket b := by
        simpa [smul_smul, hc] using hscaled

      change
        ThreeRegsCleanState
          qs
          x.reserve
          (data.reserve.drop 1)
          work.reserve
          (qs.eval (†U) (qs.ket b))

      rw [hadjoint]

      exact
        ThreeRegsCleanState.smul
          c⁻¹
          (ThreeRegsCleanState.ket
            b hx hdata hwork)

  | add hψ hφ ihψ ihφ =>
      rw [qs.eval_add]
      exact
        ThreeRegsCleanState.add
          ihψ
          ihφ

  | smul a hψ ihψ =>
      rw [qs.eval_smul]
      exact
        ThreeRegsCleanState.smul
          a
          ihψ

/-! =========================================================
    Elementary Hadamard inverse facts
========================================================= -/
theorem writeNat_writeNat_same
    {Basis : Type u}
    [RegEncoding Basis]
    (r : Reg)
    (v w : ℕ)
    (b : Basis) :
    RegEncoding.writeNat r v
        (RegEncoding.writeNat r w b)
      =
    RegEncoding.writeNat r v b := by
  apply RegEncoding.basis_ext
  intro q

  by_cases hq : q ∈ r.qubits
  · exact
      RegEncoding.bit_writeNat_in
        r
        v
        (RegEncoding.writeNat r w b)
        b
        q
        hq

  · rw [
      RegEncoding.bit_writeNat_out
        r v
        (RegEncoding.writeNat r w b)
        q hq,
      RegEncoding.bit_writeNat_out
        r w b q hq,
      RegEncoding.bit_writeNat_out
        r v b q hq
    ]

private theorem bit_writeNat_qubitReg
    {Basis : Type u}
    [RegEncoding Basis]
    (q v : ℕ)
    (b : Basis)
    (hv : v < 2) :
    RegEncoding.bit q
        (RegEncoding.writeNat
          (qubitReg q)
          v
          b)
      =
    Nat.testBit v 0 := by
  let i : Fin (regSize (qubitReg q)) :=
    ⟨0, by simp⟩

  have hbit :=
    RegEncoding.bit_eq_testBit_toNat
      (qubitReg q)
      (RegEncoding.writeNat
        (qubitReg q)
        v
        b)
      i

  have hget :
      (qubitReg q).get i = q := by
    rfl

  rw [hget] at hbit

  have hv' :
      v < ASize (qubitReg q) := by
    simpa [ASize] using hv

  rw [
    RegEncoding.toNat_writeNat_of_lt
      (qubitReg q)
      v
      b
      hv'
  ] at hbit

  exact hbit

theorem bit_eq_testBit_toNat_qubitReg
    {Basis : Type u}
    [RegEncoding Basis]
    (q : ℕ)
    (b : Basis) :
    RegEncoding.bit q b
      =
    Nat.testBit
      (RegEncoding.toNat (qubitReg q) b)
      0 := by
  let i : Fin (regSize (qubitReg q)) :=
    ⟨0, by simp⟩

  have hbit :=
    RegEncoding.bit_eq_testBit_toNat
      (qubitReg q)
      b
      i

  have hget :
      (qubitReg q).get i = q := by
    rfl

  simpa only [hget] using hbit

lemma hadamard_scale_sq :
    let a : ℂ :=
      (1 / Real.sqrt (2 : ℝ) : ℂ)

    (a * a) * 2 = 1 := by
  dsimp

  have hsqrt_ne_real :
      Real.sqrt (2 : ℝ) ≠ 0 := by
    positivity

  have hsqrt_ne :
      (Real.sqrt (2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hsqrt_ne_real

  field_simp [hsqrt_ne]

  have hsqrt_sq :
      ((Real.sqrt (2 : ℝ) : ℂ) ^ 2) = 2 := by
    exact_mod_cast
      (Real.sq_sqrt
        (by norm_num : (0 : ℝ) ≤ 2))

  simpa [sq] using hsqrt_sq.symm


lemma hadamard_plus_identity
    {M : Type*}
    [AddCommGroup M]
    [Module ℂ M]
    (a : ℂ)
    (ha : (a * a) * 2 = 1)
    (u v : M) :
    a •
        (a • (u + v) +
         a • (u - v))
      =
    u := by
  calc
    a •
        (a • (u + v) +
         a • (u - v))
        =
      ((a * a) * 2) • u := by
        module

    _ = u := by
      rw [ha]
      simp

lemma hadamard_minus_identity
    {M : Type*}
    [AddCommGroup M]
    [Module ℂ M]
    (a : ℂ)
    (ha : (a * a) * 2 = 1)
    (u v : M) :
    a •
        (a • (u + v) -
         a • (u - v))
      =
    v := by
  calc
    a •
        (a • (u + v) -
         a • (u - v))
        =
      ((a * a) * 2) • v := by
        module

    _ = v := by
      rw [ha]
      simp


private theorem eval_H_involutive_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (q : ℕ)
    (b : qs.Basis) :
    qs.eval (Gate.H q)
        (qs.eval (Gate.H q) (qs.ket b))
      =
    qs.ket b := by
  let r : Reg :=
    qubitReg q

  let a : ℂ :=
    (1 / Real.sqrt (2 : ℝ) : ℂ)

  let b0 : qs.Basis :=
    RegEncoding.writeNat r 0 b

  let b1 : qs.Basis :=
    RegEncoding.writeNat r 1 b

  have hnlt :
      RegEncoding.toNat r b < 2 := by
    have h :=
      RegEncoding.toNat_lt_ASize r b

    simpa [r, ASize] using h

  have hn :
      RegEncoding.toNat r b = 0
        ∨
      RegEncoding.toNat r b = 1 := by
    omega

  have hb0 :
      RegEncoding.bit q b0 = false := by
    dsimp only [b0, r]

    simp

  have hb1 :
      RegEncoding.bit q b1 = true := by
    dsimp only [b1, r]

    simp

  have h00 :
      RegEncoding.writeNat r 0 b0 = b0 := by
    dsimp only [b0]

    exact
      writeNat_writeNat_same
        r 0 0 b

  have h01 :
      RegEncoding.writeNat r 1 b0 = b1 := by
    dsimp only [b0, b1]

    exact
      writeNat_writeNat_same
        r 1 0 b

  have h10 :
      RegEncoding.writeNat r 0 b1 = b0 := by
    dsimp only [b0, b1]

    exact
      writeNat_writeNat_same
        r 0 1 b

  have h11 :
      RegEncoding.writeNat r 1 b1 = b1 := by
    dsimp only [b1]

    exact
      writeNat_writeNat_same
        r 1 1 b

  rw [
    HadamardSemantics.eval_H_ket,
    qs.eval_smul,
    qs.eval_add,
    qs.eval_smul,
    HadamardSemantics.eval_H_ket,
    HadamardSemantics.eval_H_ket
  ]

  change
    a •
      (
        a •
          (
            qs.ket
              (RegEncoding.writeNat r 0 b0)
              +
            (if RegEncoding.bit q b0
             then (-1 : ℂ)
             else 1) •
              qs.ket
                (RegEncoding.writeNat r 1 b0)
          )
          +
        (if RegEncoding.bit q b
         then (-1 : ℂ)
         else 1) •
          (
            a •
              (
                qs.ket
                  (RegEncoding.writeNat r 0 b1)
                  +
                (if RegEncoding.bit q b1
                 then (-1 : ℂ)
                 else 1) •
                  qs.ket
                    (RegEncoding.writeNat r 1 b1)
              )
          )
      )
      =
    qs.ket b

  rw [h00, h01, h10, h11, hb0, hb1]
  simp only [ite_true, neg_one_smul]

  rcases hn with hn | hn
  · have hb :
        RegEncoding.bit q b = false := by
      rw [
        bit_eq_testBit_toNat_qubitReg
          q b,
        hn
      ]
      decide

    have hbEq :
        b0 = b := by
      dsimp only [b0]
      simpa [hn] using
        (RegEncoding.writeNat_toNat r b)

    simpa [
      a,
      hb,
      hbEq,
      sub_eq_add_neg,
      add_assoc,
      add_comm,
      add_left_comm
    ] using
      hadamard_plus_identity
        a
        hadamard_scale_sq
        (qs.ket b0)
        (qs.ket b1)

  · have hb :
        RegEncoding.bit q b = true := by
      rw [
        bit_eq_testBit_toNat_qubitReg
          q b,
        hn
      ]
      decide

    have hbEq :
        b1 = b := by
      dsimp only [b1]
      simpa [hn] using
        (RegEncoding.writeNat_toNat r b)

    simpa [
      a,
      hb,
      hbEq,
      sub_eq_add_neg,
      add_assoc,
      add_comm,
      add_left_comm
    ] using
      hadamard_minus_identity
        a
        hadamard_scale_sq
        (qs.ket b0)
        (qs.ket b1)


private theorem eval_H_involutive
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (q : ℕ)
    (ψ : qs.State) :
    qs.eval (Gate.H q)
        (qs.eval (Gate.H q) ψ)
      =
    ψ := by
  refine
    qs.state_induction
      (P := fun φ =>
        qs.eval (Gate.H q)
            (qs.eval (Gate.H q) φ)
          =
        φ)
      ?_
      ?_
      ?_
      ?_
      ψ

  · change
      qs.eval (Gate.H q)
          (qs.eval (Gate.H q) 0)
        =
      0
    rw [qs.eval_zero, qs.eval_zero]

  · intro ψ₁ ψ₂ hψ₁ hψ₂
    calc
      qs.eval (Gate.H q)
          (qs.eval (Gate.H q) (ψ₁ + ψ₂))
          =
        qs.eval (Gate.H q)
          (qs.eval (Gate.H q) ψ₁ +
           qs.eval (Gate.H q) ψ₂) := by
          rw [qs.eval_add]
      _ =
        qs.eval (Gate.H q)
            (qs.eval (Gate.H q) ψ₁)
          +
        qs.eval (Gate.H q)
            (qs.eval (Gate.H q) ψ₂) := by
          rw [qs.eval_add]
      _ = ψ₁ + ψ₂ := by
          rw [hψ₁, hψ₂]

  · intro a ψ hψ
    calc
      qs.eval (Gate.H q)
          (qs.eval (Gate.H q) (a • ψ))
          =
        qs.eval (Gate.H q)
          (a • qs.eval (Gate.H q) ψ) := by
          rw [qs.eval_smul]
      _ =
        a •
          qs.eval (Gate.H q)
            (qs.eval (Gate.H q) ψ) := by
          rw [qs.eval_smul]
      _ = a • ψ := by
          rw [hψ]

  · intro b
    exact
      eval_H_involutive_ket
        qs q b


private theorem eval_adj_H_eq_eval_H
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (q : ℕ)
    (ψ : qs.State) :
    qs.eval (†(Gate.H q)) ψ
      =
    qs.eval (Gate.H q) ψ := by
  apply qeval_injective qs (Gate.H q)

  rw [
    qs.eval_apply_adj,
    eval_H_involutive
  ]


/-! =========================================================
    Locality of a single adjoint Hadamard
========================================================= -/

private theorem eval_H_preserves_threeRegsCleanState
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (q : ℕ)
    (r₁ r₂ r₃ : Reg)
    {ψ : qs.State}
    (h₁q :
      Disjoint r₁ (qubitReg q))
    (h₂q :
      Disjoint r₂ (qubitReg q))
    (h₃q :
      Disjoint r₃ (qubitReg q))
    (hclean :
      ThreeRegsCleanState
        qs r₁ r₂ r₃ ψ) :
    ThreeRegsCleanState
      qs r₁ r₂ r₃
      (qs.eval (Gate.H q) ψ) := by
  induction hclean with
  | zero =>
      rw [qs.eval_zero]
      exact ThreeRegsCleanState.zero

  | ket b h₁ h₂ h₃ =>
      rw [HadamardSemantics.eval_H_ket]

      apply ThreeRegsCleanState.smul
      apply ThreeRegsCleanState.add

      · apply ThreeRegsCleanState.ket

        · unfold FreshZero at h₁ ⊢
          rw [
            RegEncoding.toNat_left_write_right
              r₁
              (qubitReg q)
              h₁q
              b
              0
          ]
          exact h₁

        · unfold FreshZero at h₂ ⊢
          rw [
            RegEncoding.toNat_left_write_right
              r₂
              (qubitReg q)
              h₂q
              b
              0
          ]
          exact h₂

        · unfold FreshZero at h₃ ⊢
          rw [
            RegEncoding.toNat_left_write_right
              r₃
              (qubitReg q)
              h₃q
              b
              0
          ]
          exact h₃

      · apply ThreeRegsCleanState.smul
        apply ThreeRegsCleanState.ket

        · unfold FreshZero at h₁ ⊢
          rw [
            RegEncoding.toNat_left_write_right
              r₁
              (qubitReg q)
              h₁q
              b
              1
          ]
          exact h₁

        · unfold FreshZero at h₂ ⊢
          rw [
            RegEncoding.toNat_left_write_right
              r₂
              (qubitReg q)
              h₂q
              b
              1
          ]
          exact h₂

        · unfold FreshZero at h₃ ⊢
          rw [
            RegEncoding.toNat_left_write_right
              r₃
              (qubitReg q)
              h₃q
              b
              1
          ]
          exact h₃

  | add hψ hφ ihψ ihφ =>
      rw [qs.eval_add]
      exact
        ThreeRegsCleanState.add
          ihψ
          ihφ

  | smul a hψ ihψ =>
      rw [qs.eval_smul]
      exact
        ThreeRegsCleanState.smul
          a
          ihψ


private theorem eval_adj_H_preserves_threeRegsCleanState
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (q : ℕ)
    (r₁ r₂ r₃ : Reg)
    {ψ : qs.State}
    (h₁q :
      Disjoint r₁ (qubitReg q))
    (h₂q :
      Disjoint r₂ (qubitReg q))
    (h₃q :
      Disjoint r₃ (qubitReg q))
    (hclean :
      ThreeRegsCleanState
        qs r₁ r₂ r₃ ψ) :
    ThreeRegsCleanState
      qs r₁ r₂ r₃
      (qs.eval (†(Gate.H q)) ψ) := by
  rw [eval_adj_H_eq_eval_H]

  exact
    eval_H_preserves_threeRegsCleanState
      q
      r₁
      r₂
      r₃
      h₁q
      h₂q
      h₃q
      hclean

/-! =========================================================
    Adjoint register-Hadamard locality
========================================================= -/

private theorem
    eval_adj_hadamardFold_preserves_threeRegsCleanState
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (qubits : List ℕ)
    (acc : Gate)
    (r₁ r₂ r₃ : Reg)
    (hqubits :
      ∀ q,
        q ∈ qubits →
        Disjoint r₁ (qubitReg q)
          ∧
        Disjoint r₂ (qubitReg q)
          ∧
        Disjoint r₃ (qubitReg q))
    (hacc :
      ∀ φ : qs.State,
        ThreeRegsCleanState
            qs r₁ r₂ r₃ φ →
        ThreeRegsCleanState
          qs r₁ r₂ r₃
          (qs.eval (†acc) φ))
    (ψ : qs.State)
    (hclean :
      ThreeRegsCleanState
        qs r₁ r₂ r₃ ψ) :
    ThreeRegsCleanState
      qs r₁ r₂ r₃
      (qs.eval
        (†(qubits.foldl
          (fun acc q =>
            (Gate.H q) ;; acc)
          acc))
        ψ) := by
  induction qubits generalizing acc ψ with
  | nil =>
      simpa using hacc ψ hclean

  | cons q qubits ih =>
      simp only [List.foldl]

      apply ih
      · intro p hp
        exact hqubits p (by simp [hp])

      · intro φ hφ

        rw [eval_adj_seq_eq]

        have hAfterAcc :
            ThreeRegsCleanState
              qs r₁ r₂ r₃
              (qs.eval (†acc) φ) :=
          hacc φ hφ

        have hq :=
          hqubits q (by simp)

        exact
          eval_adj_H_preserves_threeRegsCleanState
            q
            r₁
            r₂
            r₃
            hq.1
            hq.2.1
            hq.2.2
            hAfterAcc

      · exact hclean


private theorem eval_adj_H_reg_work_preserves_full_clean
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (x data work : ExtReg)
    (hxWork :
      ExtReg.OwnedDisjoint x work)
    (hmod :
      ModMulCircuitWorkspaceOK data work)
    (ψ : qs.State)
    (hclean :
      ShorLoweringCleanState
        qs x data work ψ) :
    ShorLoweringCleanState
      qs x data work
      (qs.eval
        (†(H_reg work.active))
        ψ) := by
  have hxWorkActive :
      Disjoint x.reserve work.active :=
    reserve_active_disjoint_of_ownedDisjoint
      hxWork

  have hdataWorkActive :
      Disjoint (data.reserve.drop 1) work.active :=
    reserve_drop_active_disjoint_of_ownedDisjoint
      hmod.2.2
      1

  have hworkWorkActive :
      Disjoint work.reserve work.active :=
    Disjoint.symm
      work.active_reserve_disjoint

  have hqubits :
      ∀ q,
        q ∈ regQubits work.active →
        Disjoint x.reserve (qubitReg q)
          ∧
        Disjoint (data.reserve.drop 1) (qubitReg q)
          ∧
        Disjoint work.reserve (qubitReg q) := by
    intro q hq

    have hqActive :
        q ∈ work.active.qubits := by
      simpa [regQubits] using hq

    exact
      ⟨
        disjoint_qubitReg_of_mem_right
          hxWorkActive
          hqActive,
        disjoint_qubitReg_of_mem_right
          hdataWorkActive
          hqActive,
        disjoint_qubitReg_of_mem_right
          hworkWorkActive
          hqActive
      ⟩

  have hid :
      ∀ φ : qs.State,
        ThreeRegsCleanState
            qs
            x.reserve
            (data.reserve.drop 1)
            work.reserve
            φ →
        ThreeRegsCleanState
          qs
          x.reserve
          (data.reserve.drop 1)
          work.reserve
          (qs.eval (†Gate.id) φ) := by
    intro φ hφ

    have heval :
        qs.eval (†Gate.id) φ = φ := by
      have h :=
        qs.eval_apply_adj Gate.id φ

      simpa only [qs.eval_id] using h

    rw [heval]
    exact hφ

  unfold H_reg

  exact
    eval_adj_hadamardFold_preserves_threeRegsCleanState
      (qs := qs)
      (regQubits work.active)
      Gate.id
      x.reserve
      (data.reserve.drop 1)
      work.reserve
      hqubits
      hid
      ψ
      hclean



/-! =========================================================
    Semantic decomposition of the Step-5 adjoint
========================================================= -/

private theorem eval_adj_step5Forward_eq
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (k5val N ctrl : ℕ)
    (data work : ExtReg)
    (hmod :
      ModMulCircuitWorkspaceOK data work)
    (ψ : qs.State) :
    qs.eval
        (†(step5Forward
          k5val N ctrl data work hmod))
        ψ
      =
    qs.eval
      (†(H_reg work.active))
      (qs.eval
        (†(Gate.CPhaseProdUsing
          ctrl
          ((2 *
              ((k5val % N : ℕ) : ℚ)) /
            (N : ℚ))
          (data.grow 1).active
          work.active
          hmod.step5Workspace))
        (qs.eval
          (Gate.QFT
            hmod.step5Workspace.zExt)
          ψ)) := by
  unfold step5Forward
  dsimp

  rw [
    eval_adj_seq_eq,
    eval_adj_seq_eq
  ]

  simp only [IQFT]

  rw [eval_adj_adj_eq]


/-! =========================================================
    Main Step-5 adjoint preservation theorem
========================================================= -/

/--
Main semantic preservation theorem for the Step-5 adjoint block.

The high-level adjoint Step-5 circuit is decomposed into QFT, adjoint
controlled phase product, and adjoint Hadamards. Each component preserves
`ShorLoweringCleanState`, so the whole adjoint does as well.
-/
theorem eval_adj_step5Forward_preserves_full_clean
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (x data work : ExtReg)
    (k5val N ctrl : ℕ)
    (hxWork :
      ExtReg.OwnedDisjoint x work)
    (hmod :
      ModMulCircuitWorkspaceOK data work)
    (ψ : qs.State)
    (hclean :
      ShorLoweringCleanState
        qs x data work ψ) :
    ShorLoweringCleanState
      qs x data work
      (qs.eval
        (†(step5Forward
          k5val N ctrl data work hmod))
        ψ) := by
  let φ : Angle :=
    (2 *
      ((k5val % N : ℕ) : ℚ)) /
    (N : ℚ)

  let ψQFT : qs.State :=
    qs.eval
      (Gate.QFT
        hmod.step5Workspace.zExt)
      ψ

  have hQFT :
      ShorLoweringCleanState
        qs x data work ψQFT := by
    dsimp only [ψQFT]

    exact
      eval_step5_QFT_preserves_full_clean
        qs
        x
        data
        work
        hxWork
        hmod
        ψ
        hclean

  let ψPhase : qs.State :=
    qs.eval
      (†(Gate.CPhaseProdUsing
        ctrl
        φ
        (data.grow 1).active
        work.active
        hmod.step5Workspace))
      ψQFT

  have hPhase :
      ShorLoweringCleanState
        qs x data work ψPhase := by
    dsimp only [ψPhase]

    exact
      eval_adj_step5_CPhaseProdUsing_preserves_full_clean
        qs
        x
        data
        work
        ctrl
        φ
        hmod
        ψQFT
        hQFT

  have hHadamard :
      ShorLoweringCleanState
        qs x data work
        (qs.eval
          (†(H_reg work.active))
          ψPhase) := by
    exact
      eval_adj_H_reg_work_preserves_full_clean
        qs
        x
        data
        work
        hxWork
        hmod
        ψPhase
        hPhase

  rw [
    eval_adj_step5Forward_eq
      qs
      k5val
      N
      ctrl
      data
      work
      hmod
      ψ
  ]

  simpa only [φ, ψQFT, ψPhase] using hHadamard

/--
Main lowered-readiness theorem for Step 5.

It packages Step 5's adjoint semantic preservation with the local lowering
workspace obligations, producing a `LoweredCleanResult` for the public
`step5` gate.
-/
theorem lowered_step5_ready_and_full_clean
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (lowering : ShorLoweringSetup)
    (x data work : ExtReg)
    (k5val N ctrl : ℕ)
    (hxData :
      ExtReg.OwnedDisjoint x data)
    (hxWork :
      ExtReg.OwnedDisjoint x work)
    (hmod :
      ModMulCircuitWorkspaceOK data work)
    (hworkspace :
      GateWorkspaceOK
        lowering.ops
        (step5
          k5val N ctrl data work hmod))
    (ψ : qs.State)
    (hclean :
      ShorLoweringCleanState
        qs x data work ψ) :
    LoweredCleanResult
      qs
      lowering
      (ShorLoweringCleanState
        qs x data work)
      (step5
        k5val N ctrl data work hmod)
      hworkspace
      ψ := by
  let U : Gate :=
    step5Forward
      k5val N ctrl data work hmod

  have hstep5 :
      step5
          k5val N ctrl data work hmod
        =
      †U := by
    rfl

  change
    LoweredCleanResult
      qs
      lowering
      (ShorLoweringCleanState
        qs x data work)
      (†U)
      hworkspace
      ψ

  have hpost :
      ShorLoweringCleanState
        qs x data work
        (qs.eval (†U) ψ) := by
    simpa only [U] using
      eval_adj_step5Forward_preserves_full_clean
        qs
        x
        data
        work
        k5val
        N
        ctrl
        hxWork
        hmod
        ψ
        hclean

  have hforward :
      LoweredCleanResult
        qs
        lowering
        (ShorLoweringCleanState
          qs x data work)
        U
        hworkspace
        (qs.eval (†U) ψ) := by
    simpa only [U] using
      lowered_step5Forward_ready_and_full_clean
        qs
        lowering
        x
        data
        work
        k5val
        N
        ctrl
        hxData
        hxWork
        hmod
        hworkspace
        (qs.eval (†U) ψ)
        hpost

  exact
    LoweredCleanResult.adj
      hpost
      hforward

theorem
    threeRegsCleanState_to_QFTWorkspaceCleanState_first
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    {k : ℕ}
    (ops : Prog k)
    (r : ExtReg)
    {r₁ r₂ r₃ : Reg}
    (hreserve :
      r.reserve = r₁)
    {ψ : qs.State}
    (hclean :
      ThreeRegsCleanState
        qs r₁ r₂ r₃ ψ) :
    QFTWorkspaceCleanState
      qs
      (qftXWork ops r)
      (qftZWork ops r)
      ψ := by
  induction hclean with
  | zero =>
      exact QFTWorkspaceCleanState.zero

  | ket b h₁ h₂ h₃ =>
      apply QFTWorkspaceCleanState.ket b

      · exact
          FreshZero.of_subset
            (qftXWork ops r)
            r₁
            b
            (fun q hq => by
              simpa only [hreserve] using
                qftXWork_mem_reserve
                  ops r hq)
            h₁

      · exact
          FreshZero.of_subset
            (qftZWork ops r)
            r₁
            b
            (fun q hq => by
              simpa only [hreserve] using
                qftZWork_mem_reserve
                  ops r hq)
            h₁

  | add hψ hφ ihψ ihφ =>
      exact
        QFTWorkspaceCleanState.add
          ihψ
          ihφ

  | smul a hψ ihψ =>
      exact
        QFTWorkspaceCleanState.smul
          a
          ihψ


end Shor
