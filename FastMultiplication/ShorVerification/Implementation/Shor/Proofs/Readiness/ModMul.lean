import FastMultiplication.ShorVerification.Implementation.Shor.Spec.Setup
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.Workspace
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.Steps
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Workspace
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness.Static
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness.Sequencing
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness.Primitives
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness.Step2
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness.Step5

/-!
# One Modular-Multiplication Core: Lowered Readiness

Lowered readiness and clean-state preservation for one controlled
modular-multiplication core (`CmodMulInPlaceCore`), one exponent/control qubit
at a time. `shorConcreteCarrier` is the proof-only exponent view (real
exponent reserve strengthened with the Step-3/4 scratch register) reused from
the earlier Hadamard/Step-1/2/5 proofs; `lowered_CmodMulInPlaceCore_ready_and_clean`
is the main theorem assembling them into readiness for one core invocation.
-/

namespace Shor
open Gate
open Classical


/-- A proof-only exponent view whose reserve is exactly the strengthened first
register of `ShorConcreteCleanState`.  Its active part is the real exponent,
so the existing Hadamard proof and the Step-1/2/5 proofs can be reused without
forgetting scratch cleanliness. -/
def shorConcreteCarrier
    (x scratch : ExtReg)
    (hxScratch : x.OwnedDisjoint scratch) : ExtReg :=
  ExtReg.withReserve
    x.active
    (exponentScratchCleanReg x scratch hxScratch)
    (by
      rw [Disjoint, List.disjoint_left]
      intro q hqActive hqCombined
      simp only [
        exponentScratchCleanReg,
        Reg.append,
        ExtReg.ownedReg,
        List.mem_append
      ] at hqCombined
      rcases hqCombined with hqReserve | hqScratch
      · exact
          (not_mem_right_of_mem_left_of_disjoint
            x.active_reserve_disjoint hqActive) hqReserve
      · rw [ExtReg.OwnedDisjoint, List.disjoint_left] at hxScratch
        exact hxScratch
          (by
            rw [ExtReg.ownedQubits, List.mem_append]
            exact Or.inl hqActive)
          (by
            rw [ExtReg.ownedQubits, List.mem_append]
            exact hqScratch))

@[simp] private theorem shorConcreteCarrier_ownedQubits
    (x scratch : ExtReg)
    (hxScratch : x.OwnedDisjoint scratch) :
    (shorConcreteCarrier x scratch hxScratch).ownedQubits =
      x.ownedQubits ++ scratch.ownedQubits := by
  simp [
    shorConcreteCarrier,
    ExtReg.withReserve,
    ExtReg.ownedQubits,
    exponentScratchCleanReg,
    ExtReg.ownedReg,
    Reg.append,
    List.append_assoc
  ]

theorem shorConcreteCarrier_ownedDisjoint_right
    (x scratch y : ExtReg)
    (hxScratch : x.OwnedDisjoint scratch)
    (hxY : x.OwnedDisjoint y)
    (hscratchY : scratch.OwnedDisjoint y) :
    (shorConcreteCarrier x scratch hxScratch).OwnedDisjoint y := by
  rw [ExtReg.OwnedDisjoint, List.disjoint_left] at hxY hscratchY ⊢
  intro q hqCarrier hqY
  rw [shorConcreteCarrier_ownedQubits, List.mem_append] at hqCarrier
  rcases hqCarrier with hqExponent | hqScratch
  · exact hxY hqExponent hqY
  · exact hscratchY hqScratch hqY

private theorem flag_not_shorConcreteCarrier
    (x scratch : ExtReg)
    (hxScratch : x.OwnedDisjoint scratch)
    (flag : ℕ)
    (hflagX : flag ∉ x.ownedQubits)
    (hflagScratch : flag ∉ scratch.ownedQubits) :
    flag ∉ (shorConcreteCarrier x scratch hxScratch).ownedQubits := by
  rw [shorConcreteCarrier_ownedQubits, List.mem_append]
  rintro (hflagExponent | hflagScratch')
  · exact hflagX hflagExponent
  · exact hflagScratch hflagScratch'

/--
Main theorem for one controlled modular-multiplication core.

It sequences Steps 1 through 5, threading `ShorLoweringCleanState` through the
lowered implementation and discharging each stage's local workspace-clean
obligation.
-/
theorem lowered_CmodMulInPlaceCore_ready_and_clean
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (lowering : ShorLoweringSetup)
    (x data work scratch : ExtReg)
    (c N ctrl flag : ℕ)
    (hxData :
      ExtReg.OwnedDisjoint x data)
    (hxWork :
      ExtReg.OwnedDisjoint x work)
    (hxScratch :
      ExtReg.OwnedDisjoint x scratch)
    (hmod :
      ModMulCircuitWorkspaceOK data work)
    (hflagX :
      flag ∉ x.ownedQubits)
    (_hlayout :
      ModMulCoreLayout data work flag ctrl)
    (hstep4 :
      CmpLtNWWorkspace N (data.grow 1) work scratch flag)
    (hworkspace :
      GateWorkspaceOK
        lowering.ops
        (CmodMulInPlaceCore
          c N ctrl data work scratch flag hmod hstep4))
    (ψ : qs.State)
    (hclean :
      ShorConcreteCleanState
        qs x data work scratch hxScratch ψ) :
    LoweredCleanResult
      qs
      lowering
      (ShorConcreteCleanState
        qs x data work scratch hxScratch)
      (CmodMulInPlaceCore
        c N ctrl data work scratch flag hmod hstep4)
      hworkspace
      ψ := by
  let carrier := shorConcreteCarrier x scratch hxScratch

  have hdataScratch : data.OwnedDisjoint scratch := by
    simpa [ExtReg.OwnedDisjoint, Gate.ExtReg.ownedQubits_grow] using
      hstep4.data_scratch_disjoint
  have hcarrierData : carrier.OwnedDisjoint data := by
    exact
      shorConcreteCarrier_ownedDisjoint_right
        x scratch data hxScratch hxData
        (ownedDisjoint_symm hdataScratch)
  have hcarrierWork : carrier.OwnedDisjoint work := by
    exact
      shorConcreteCarrier_ownedDisjoint_right
        x scratch work hxScratch hxWork
        (ownedDisjoint_symm hstep4.work_scratch_disjoint)
  have hcleanCarrier :
      ShorLoweringCleanState qs carrier data work ψ := by
    simpa [carrier, shorConcreteCarrier] using hclean

  let U1 :=
    step1
      c N ctrl data work hmod

  let U2 :=
    step2
      N data work hmod

  let U3 :=
    step3 N (data.grow 1) scratch flag

  let U4 :=
    step4
      N
      (data.grow 1)
      work
      scratch
      flag
      hstep4

  let U5 :=
    step5
      (step5Constant c N)
      N ctrl data work hmod

  change
    GateWorkspaceOK lowering.ops U1
      ∧
    GateWorkspaceOK lowering.ops U2
      ∧
    GateWorkspaceOK lowering.ops U3
      ∧
    GateWorkspaceOK lowering.ops U4
      ∧
    GateWorkspaceOK lowering.ops U5
    at hworkspace

  have hworkspace45 :
      GateWorkspaceOK lowering.ops (U4 ;; U5) := by
    exact hworkspace.2.2.2

  have hworkspace345 :
      GateWorkspaceOK lowering.ops (U3 ;; U4 ;; U5) := by
    exact hworkspace.2.2

  have hworkspace2345 :
      GateWorkspaceOK lowering.ops (U2 ;; U3 ;; U4 ;; U5) := by
    exact hworkspace.2

  have hworkspace12345 :
      GateWorkspaceOK lowering.ops (U1 ;; U2 ;; U3 ;; U4 ;; U5) := by
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
          qs x data work scratch hxScratch)
        U1 hworkspace.1 ψ :=
    by
      simpa [carrier, shorConcreteCarrier] using
        (lowered_step1_ready_and_full_clean
          qs lowering carrier data work
          c N ctrl
          hcarrierWork
          hmod
          hworkspace.1 ψ hcleanCarrier)

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
          qs x data work scratch hxScratch)
        U2 hworkspace.2.1 ψ1 :=
    by
      simpa [carrier, shorConcreteCarrier] using
        (lowered_step2_ready_and_carry_clean
          qs lowering carrier data work
          N
          hcarrierData
          hmod
          hworkspace.2.1
          ψ1
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
          qs x data work scratch hxScratch)
        U3 hworkspace.2.2.1 ψ2 :=
    lowered_step3_ready_and_clean
      lowering x data work scratch N flag
      hxData hxScratch hmod hflagX hstep4
      hworkspace.2.2.1
      ψ2
      h2.2

  let ψ4 :=
    LowerGateClass.evalL
      (qs := qs)
      (lowerGate
        lowering.k lowering.hk lowering.ops
        U4 hworkspace.2.2.2.1)
      ψ3

  have h4 :
      LoweredCleanResult
        qs lowering
        (ShorConcreteCleanState
          qs x data work scratch hxScratch)
        U4 hworkspace.2.2.2.1 ψ3 :=
    lowered_step4_ready_and_clean
      lowering
      x data work scratch
      N flag
      hxData hxWork hxScratch hmod hflagX hstep4
      hworkspace.2.2.2.1
      ψ3
      h3.2

  have h5 :
      LoweredCleanResult
        qs lowering
        (ShorConcreteCleanState
          qs x data work scratch hxScratch)
        U5 hworkspace.2.2.2.2 ψ4 :=
    by
      simpa [carrier, shorConcreteCarrier] using
        (lowered_step5_ready_and_full_clean
          qs lowering carrier data work
          (step5Constant c N)
          N ctrl
          hcarrierData
          hcarrierWork
          hmod
          hworkspace.2.2.2.2
          ψ4
          (by
            simpa [carrier, shorConcreteCarrier] using h4.2))

  have h45 :
      LoweredCleanResult
        qs lowering
        (ShorConcreteCleanState
          qs x data work scratch hxScratch)
        (U4 ;; U5)
        hworkspace45
        ψ3 :=
    LoweredCleanResult.seq
      hworkspace45
      ψ3
      h4
      h5

  have h345 :
      LoweredCleanResult
        qs lowering
        (ShorConcreteCleanState
          qs x data work scratch hxScratch)
        (U3 ;; U4 ;; U5)
        hworkspace345
        ψ2 :=
    LoweredCleanResult.seq
      hworkspace345
      ψ2
      h3
      h45

  have h2345 :
      LoweredCleanResult
        qs lowering
        (ShorConcreteCleanState
          qs x data work scratch hxScratch)
        (U2 ;; U3 ;; U4 ;; U5)
        hworkspace2345
        ψ1 :=
    LoweredCleanResult.seq
      hworkspace2345
      ψ1
      h2
      h345

  have h12345 :
      LoweredCleanResult
        qs lowering
        (ShorConcreteCleanState
          qs x data work scratch hxScratch)
        (U1 ;; U2 ;; U3 ;; U4 ;; U5)
        hworkspace12345
        ψ :=
    LoweredCleanResult.seq
      hworkspace12345
      ψ
      h1
      h2345

  simpa [
    U1,
    U2,
    U3,
    U4,
    U5,
    CmodMulInPlaceCore
  ] using h12345


end Shor
