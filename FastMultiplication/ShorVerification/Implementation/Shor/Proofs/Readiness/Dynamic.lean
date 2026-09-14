import FastMultiplication.ShorVerification.Implementation.Shor.Circuit.Workspace
import FastMultiplication.ShorVerification.Implementation.Shor.Circuit.OrderFinding
import FastMultiplication.ShorVerification.Implementation.Shor.Spec.Setup
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Budgets
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness.Static
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness.Sequencing
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness.Primitives
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness.Init
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness.IQFT
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness.ModMul
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness.ModExp
import FastMultiplication.ShorVerification.Implementation.Compilation.Correctness
import FastMultiplication.ShorVerification.Implementation.QFT.Proofs.Lowering.Readiness
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.Workspace
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.Steps
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.ModExp
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Workspace
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Full Order-Finding Dynamic Readiness

Assembles readiness and dynamic clean-state preservation for the complete
approximate order-finding circuit (`H_reg`, `initY1`, modular exponentiation,
and the final inverse QFT) from the per-stage results proved in
`Readiness.Init`/`Step1`/`Step2`/`Step5`/`IQFT`/`ModMul`/`ModExp`, culminating
in `gateWorkspaceCleanState_orderFindingApprox` and its packaged form
`LoweredShorReady.workspace_clean` -- the final theorem of this directory.
-/

namespace Shor
open Gate
open Classical

/--
Main dynamic theorem for approximate order finding.

It composes exponent Hadamards, data initialization, modular exponentiation,
and the final inverse QFT, proving the complete lowered circuit starts each
recursive sub-lowering with clean workspace and preserves
`ShorLoweringCleanState`.
-/
theorem lowered_orderFindingApprox_ready_and_full_clean
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (lowering : ShorLoweringSetup)
    (η : ℝ)
    (a N : ℕ)
    (x data work scratch : ExtReg)
    (flag : ℕ)
    (b0 : qs.Basis)
    (hsetup :
      ShorApproxSetup
        qs η N x data work scratch flag b0)
    (_hlarge :
      ShorWorkspaceLargeEnough
        lowering.ops x data work scratch)
    (hisolated :
      ShorWorkspaceIsolation x work scratch flag)
    (hworkspace :
      GateWorkspaceOK
        lowering.ops
        (orderFindingApprox a N x data work scratch flag
          hsetup.circuit_workspace hsetup.step4_workspace))
    {ψ : qs.State}
    (hclean :
      ShorConcreteCleanState
        qs x data work scratch
        hisolated.exponent_scratch_disjoint ψ)
    (hLayout :
      ∀ ctrl ∈ x.active.qubits,
        ModMulCoreLayout data work flag ctrl) :
    LoweredCleanResult
      qs
      lowering
      (ShorConcreteCleanState
        qs x data work scratch
        hisolated.exponent_scratch_disjoint)
      (orderFindingApprox a N x data work scratch flag
        hsetup.circuit_workspace hsetup.step4_workspace)
      hworkspace
      ψ := by
  let U1 := H_reg x.active

  let U2 := initY1 data.active

  let U3 :=
    modExpApproxValid
      a N x.active data work scratch flag
      hsetup.circuit_workspace hsetup.step4_workspace

  let U4 := IQFT x

  change
    GateWorkspaceOK lowering.ops U1
      ∧
    GateWorkspaceOK lowering.ops U2
      ∧
    GateWorkspaceOK lowering.ops U3
      ∧
    GateWorkspaceOK lowering.ops U4
    at hworkspace

  have hworkspace34 :
      GateWorkspaceOK lowering.ops (U3 ;; U4) := by
    exact hworkspace.2.2

  have hworkspace234 :
      GateWorkspaceOK lowering.ops (U2 ;; U3 ;; U4) := by
    exact hworkspace.2

  have hworkspace1234 :
      GateWorkspaceOK lowering.ops (U1 ;; U2 ;; U3 ;; U4) := by
    exact hworkspace

  let ψ1 :=
    LowerGateClass.evalL
      (qs := qs)
      (lowerGate
        lowering.k lowering.hk lowering.ops
        U1 hworkspace.1)
      ψ

  have h1 :
      LoweredCleanResult
        qs lowering
        (ShorConcreteCleanState
          qs x data work scratch
          hisolated.exponent_scratch_disjoint)
        U1 hworkspace.1 ψ :=
    by
      let carrier :=
        shorConcreteCarrier
          x scratch hisolated.exponent_scratch_disjoint
      have hdataScratch : data.OwnedDisjoint scratch := by
        simpa [ExtReg.OwnedDisjoint, Gate.ExtReg.ownedQubits_grow] using
          hsetup.step4_workspace.data_scratch_disjoint
      have hcarrierData : carrier.OwnedDisjoint data :=
        shorConcreteCarrier_ownedDisjoint_right
          x scratch data hisolated.exponent_scratch_disjoint
          hsetup.exponent_data_disjoint
          (ownedDisjoint_symm hdataScratch)
      have hcarrierWork : carrier.OwnedDisjoint work :=
        shorConcreteCarrier_ownedDisjoint_right
          x scratch work hisolated.exponent_scratch_disjoint
          hisolated.exponent_work_disjoint
          (ownedDisjoint_symm
            hsetup.step4_workspace.work_scratch_disjoint)
      simpa [carrier, shorConcreteCarrier] using
        (lowered_H_reg_ready_and_full_clean
          qs lowering carrier data work
          hcarrierData hcarrierWork
          hworkspace.1 ψ
          (by
            simpa [carrier, shorConcreteCarrier] using hclean))

  let ψ2 :=
    LowerGateClass.evalL
      (qs := qs)
      (lowerGate
        lowering.k lowering.hk lowering.ops
        U2 hworkspace.2.1)
      ψ1

  have h2 :
      LoweredCleanResult
        qs lowering
        (ShorConcreteCleanState
          qs x data work scratch
          hisolated.exponent_scratch_disjoint)
        U2 hworkspace.2.1 ψ1 :=
    by
      let carrier :=
        shorConcreteCarrier
          x scratch hisolated.exponent_scratch_disjoint
      have hdataScratch : data.OwnedDisjoint scratch := by
        simpa [ExtReg.OwnedDisjoint, Gate.ExtReg.ownedQubits_grow] using
          hsetup.step4_workspace.data_scratch_disjoint
      have hcarrierData : carrier.OwnedDisjoint data :=
        shorConcreteCarrier_ownedDisjoint_right
          x scratch data hisolated.exponent_scratch_disjoint
          hsetup.exponent_data_disjoint
          (ownedDisjoint_symm hdataScratch)
      simpa [carrier, shorConcreteCarrier] using
        (lowered_initY1_ready_and_full_clean
          qs lowering carrier data work
          hcarrierData hsetup.circuit_workspace
          hworkspace.2.1 ψ1
          (by
            simpa [carrier, shorConcreteCarrier] using h1.2))

  let ψ3 :=
    LowerGateClass.evalL
      (qs := qs)
      (lowerGate
        lowering.k lowering.hk lowering.ops
        U3 hworkspace.2.2.1)
      ψ2

  have h3 :
      LoweredCleanResult
        qs lowering
        (ShorConcreteCleanState
          qs x data work scratch
          hisolated.exponent_scratch_disjoint)
        U3 hworkspace.2.2.1 ψ2 :=
    lowered_modExpApproxStepsValid_ready_and_clean
      lowering
      x data work scratch
      a N flag 0
      x.active.qubits
      hsetup.circuit_workspace
      hsetup.exponent_data_disjoint
      hisolated.exponent_work_disjoint
      hisolated.exponent_scratch_disjoint
      hisolated.flag_outside_exponent
      hsetup.step4_workspace
      hLayout
      hworkspace.2.2.1
      ψ2
      h2.2

  have h4 :
      LoweredCleanResult
        qs lowering
        (ShorConcreteCleanState
          qs x data work scratch
          hisolated.exponent_scratch_disjoint)
        U4 hworkspace.2.2.2 ψ3 :=
    lowered_IQFT_ready_and_concrete_clean
      lowering x data work scratch
      hsetup.exponent_data_disjoint
      hisolated.exponent_work_disjoint
      hisolated.exponent_scratch_disjoint
      hworkspace.2.2.2
      ψ3
      h3.2

  have h34 :
      LoweredCleanResult
        qs lowering
        (ShorConcreteCleanState
          qs x data work scratch
          hisolated.exponent_scratch_disjoint)
        (U3 ;; U4)
        hworkspace34
        ψ2 :=
    LoweredCleanResult.seq
      hworkspace34
      ψ2
      h3
      h4

  have h234 :
      LoweredCleanResult
        qs lowering
        (ShorConcreteCleanState
          qs x data work scratch
          hisolated.exponent_scratch_disjoint)
        (U2 ;; U3 ;; U4)
        hworkspace234
        ψ1 :=
    LoweredCleanResult.seq
      hworkspace234
      ψ1
      h2
      h34

  have h1234 :
      LoweredCleanResult
        qs lowering
        (ShorConcreteCleanState
          qs x data work scratch
          hisolated.exponent_scratch_disjoint)
        (U1 ;; U2 ;; U3 ;; U4)
        hworkspace1234
        ψ :=
    LoweredCleanResult.seq
      hworkspace1234
      ψ
      h1
      h234

  simpa [
    U1,
    U2,
    U3,
    U4,
    orderFindingApprox,
    modExpApproxValid
  ] using h1234

/--
Main public clean-workspace theorem for the raw setup arguments.

Starting from an initially clean basis state, the full approximate order-finding
gate has clean local workspace everywhere the lowering procedure needs it.
-/
theorem gateWorkspaceCleanState_orderFindingApprox
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (lowering : ShorLoweringSetup)
    (η : ℝ)
    (a N : ℕ)
    (x data work scratch : ExtReg)
    (flag : ℕ)
    (b0 : qs.Basis)
    (hsetup :
      ShorApproxSetup
        qs η N x data work scratch flag b0)
    (hlarge :
      ShorWorkspaceLargeEnough
        lowering.ops x data work scratch)
    (hisolated :
      ShorWorkspaceIsolation x work scratch flag)
    (hzero :
      ShorWorkspaceCleanInput
        x data work scratch b0) :
    let hworkspace :=
      gateWorkspaceOK_orderFindingApprox
        (ops := lowering.ops)
        (η := η)
        (a := a)
        (N := N)
        (x := x)
        (data := data)
        (work := work)
        (scratch := scratch)
        (flag := flag)
        (b0 := b0)
        hsetup
        hlarge

    GateWorkspaceCleanState
      qs
      lowering.k
      lowering.hk
      lowering.ops
      (orderFindingApprox a N x data work scratch flag
        hsetup.circuit_workspace hsetup.step4_workspace)
      hworkspace
      (qs.ket b0) := by
  let hworkspace :=
    gateWorkspaceOK_orderFindingApprox
      (ops := lowering.ops)
      (η := η)
      (a := a)
      (N := N)
      (x := x)
      (data := data)
      (work := work)
      (scratch := scratch)
      (flag := flag)
      (b0 := b0)
      hsetup
      hlarge

  have hLayoutOfMem :
      ∀ ctrl ∈ x.active.qubits,
        ModMulCoreLayout
          data work flag ctrl := by
    intro ctrl hctrl

    rcases List.get_of_mem hctrl with
      ⟨j, hj⟩

    let i : Fin (regSize x.active) :=
      ⟨j.1, by
        simp [regSize, Reg.width]⟩

    have hget :
        x.active.get i = ctrl := by
      dsimp [i, Reg.get]
      simpa [regSize, Reg.width] using hj

    have hi :=
      hsetup.register_layout i

    simpa only [hget] using hi

  have hInitial :
      ShorConcreteCleanState
        qs x data work scratch
        hisolated.exponent_scratch_disjoint
        (qs.ket b0) :=
    shorConcreteCleanState_ket
      hzero hsetup.clean_input.2.2.2.2.2.1

  have hResult :
      LoweredCleanResult
        qs
        lowering
        (ShorConcreteCleanState
          qs x data work scratch
          hisolated.exponent_scratch_disjoint)
        (orderFindingApprox a N x data work scratch flag
          hsetup.circuit_workspace hsetup.step4_workspace)
        hworkspace
        (qs.ket b0) := by
    -- Compose:
    --
    --   H_reg x.active
    --   initY1 data.active
    --   modExpApproxValid
    --   IQFT x
    --
    -- using the six non-primitive helper lemmas and
    -- `lowered_modExpApproxStepsValid_ready_and_clean`.
    exact
      lowered_orderFindingApprox_ready_and_full_clean
        lowering
        η
        a N
        x data work scratch
        flag b0
        hsetup
        hlarge
        hisolated
        hworkspace
        hInitial
        hLayoutOfMem

  exact hResult.1


/--
Final theorem of the workspace directory.

For a packaged `LoweredShorReady` assumption, the lowered approximate
order-finding circuit satisfies the dynamic `GateWorkspaceCleanState`
precondition needed by `lowerGate_correctness`.
-/
theorem LoweredShorReady.workspace_clean
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    {lowering : ShorLoweringSetup}
    {η : ℝ}
    {a N : ℕ}
    {x y work scratch : ExtReg}
    {flag : ℕ}
    {b0 : qs.Basis}
    (h :
      LoweredShorReady
        qs lowering η a N x y work scratch flag b0) :
    GateWorkspaceCleanState
      qs
      lowering.k
      lowering.hk
      lowering.ops
      (orderFindingApprox a N x y work scratch flag
        (ShorApproxSetupMinimal.toShorApproxSetup h.approx).circuit_workspace
        (ShorApproxSetupMinimal.toShorApproxSetup h.approx).step4_workspace)
      h.workspace
      (qs.ket b0) := by
  exact
    gateWorkspaceCleanState_orderFindingApprox
      lowering
      η
      a
      N
      x
      y
      work
      scratch
      flag
      b0
      (ShorApproxSetupMinimal.toShorApproxSetup h.approx)
      h.workspace_large_enough
      h.workspace_isolated
      h.workspace_initially_zero

end Shor
