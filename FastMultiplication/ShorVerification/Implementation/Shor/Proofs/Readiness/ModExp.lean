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
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness.Step5
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness.IQFT
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness.ModMul

/-!
# Modular-Exponentiation Loop: Lowered Readiness

`lowered_modExpApproxStepsValid_ready_and_clean` folds
`lowered_CmodMulInPlaceCore_ready_and_clean` over the list of exponent/control
qubits, preserving the lowered Shor workspace invariant after every controlled
modular multiplication in the loop.
-/

namespace Shor
open Gate
open Classical


/--
Main theorem for the modular-exponentiation loop.

The theorem folds `lowered_CmodMulInPlaceCore_ready_and_clean` over the list of
control qubits, preserving the lowered Shor workspace invariant after every
controlled modular multiplication.
-/
theorem lowered_modExpApproxStepsValid_ready_and_clean
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (lowering : ShorLoweringSetup)
    (x data work scratch : ExtReg)
    (a N flag e : ℕ)
    (ctrls : List ℕ)
    (hmod :
      ModMulCircuitWorkspaceOK data work)
    (hxData :
      ExtReg.OwnedDisjoint x data)
    (hxWork :
      ExtReg.OwnedDisjoint x work)
    (hxScratch :
      ExtReg.OwnedDisjoint x scratch)
    (hflagX :
      flag ∉ x.ownedQubits)
    (hstep4 :
      CmpLtNWWorkspace N (data.grow 1) work scratch flag)
    (hLayout :
      ∀ ctrl ∈ ctrls,
        ModMulCoreLayout data work flag ctrl)
    (hworkspace :
      GateWorkspaceOK
        lowering.ops
        (modExpApproxStepsValid
          a N data work scratch flag hmod hstep4 e ctrls))
    (ψ : qs.State)
    (hclean :
      ShorConcreteCleanState
        qs x data work scratch hxScratch ψ) :
    LoweredCleanResult
      qs
      lowering
      (ShorConcreteCleanState
        qs x data work scratch hxScratch)
      (modExpApproxStepsValid
        a N data work scratch flag hmod hstep4 e ctrls)
      hworkspace
      ψ := by
  induction ctrls generalizing e ψ with
  | nil =>
      constructor
      · simp [
          modExpApproxStepsValid,
          GateWorkspaceCleanState
        ]
      · simpa [
          LoweredCleanResult,
          modExpApproxStepsValid,
          LowerGateClass.evalL_id
        ] using hclean

  | cons ctrl ctrls ih =>
      let c := (a ^ (2 ^ e)) % N

      let U :=
        CmodMulInPlaceCore
          c N ctrl data work scratch flag hmod hstep4

      let V :=
        modExpApproxStepsValid
          a N data work scratch flag hmod hstep4
          (e + 1) ctrls

      change
        GateWorkspaceOK lowering.ops U
          ∧
        GateWorkspaceOK lowering.ops V
        at hworkspace

      have hHeadLayout :
          ModMulCoreLayout
            data work flag ctrl :=
        hLayout ctrl (by simp)

      have hTailLayout :
          ∀ q ∈ ctrls,
            ModMulCoreLayout
              data work flag q := by
        intro q hq
        exact hLayout q (by simp [hq])

      have hU :
          LoweredCleanResult
            qs lowering
            (ShorConcreteCleanState
              qs x data work scratch hxScratch)
            U hworkspace.1 ψ :=
        lowered_CmodMulInPlaceCore_ready_and_clean
          lowering
          x data work scratch
          c N ctrl flag
          hxData
          hxWork
          hxScratch
          hmod
          hflagX
          hHeadLayout
          hstep4
          hworkspace.1
          ψ
          hclean

      let ψ' :=
        LowerGateClass.evalL
          (qs := qs)
          (lowerGate
            lowering.k
            lowering.hk
            lowering.ops
            U
            hworkspace.1)
          ψ

      have hV :
          LoweredCleanResult
            qs lowering
            (ShorConcreteCleanState
              qs x data work scratch hxScratch)
            V hworkspace.2 ψ' :=
        ih
          (e := e + 1)
          (ψ := ψ')
          hTailLayout
          hworkspace.2
          hU.2

      have hseq :=
        LoweredCleanResult.seq
          hworkspace
          ψ
          hU
          hV

      simpa [
        U,
        V,
        c,
        modExpApproxStepsValid
      ] using hseq

end Shor
