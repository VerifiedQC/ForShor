import FastMultiplication.ShorVerification.Implementation.Shor.Spec.Setup
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Budgets
import FastMultiplication.ShorVerification.Implementation.Compilation.Correctness
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.Steps
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness.Static
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness.Sequencing
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness.Primitives
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness.Step1
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness.Step5

/-!
# Final Inverse QFT Readiness

Lowered readiness and clean-state preservation for the final inverse QFT
applied to the exponent register at the end of order finding:
`lowered_IQFT_ready_and_full_clean` derives it under the full
`ShorLoweringCleanState` invariant, and `lowered_IQFT_ready_and_concrete_clean`
derives the analogous fact under the strengthened concrete clean-state
invariant that also tracks the Step-3/4 scratch register.
-/

namespace Shor
open Gate
open Classical


private theorem lowered_IQFT_ready_and_full_clean
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (lowering : ShorLoweringSetup)
    (x data work : ExtReg)
    (hxData :
      ExtReg.OwnedDisjoint x data)
    (hxWork :
      ExtReg.OwnedDisjoint x work)
    (hworkspace :
      GateWorkspaceOK
        lowering.ops
        (IQFT x))
    (ψ : qs.State)
    (hclean :
      ShorLoweringCleanState
        qs x data work ψ) :
    LoweredCleanResult
      qs
      lowering
      (ShorLoweringCleanState
        qs x data work)
      (IQFT x)
      hworkspace
      ψ := by
  have hxReserveActive :
      Disjoint x.reserve x.active :=
    Disjoint.symm
      x.active_reserve_disjoint

  have hdataReserveActive :
      Disjoint (data.reserve.drop 1) x.active :=
    reserve_drop_active_disjoint_of_ownedDisjoint
      (ownedDisjoint_symm hxData)
      1

  have hworkReserveActive :
      Disjoint work.reserve x.active :=
    reserve_active_disjoint_of_ownedDisjoint
      (ownedDisjoint_symm hxWork)

  /-
  The high-level inverse QFT changes only `x.active`, so all three
  reserve registers remain zero.
  -/
  have hHighClean :
      ShorLoweringCleanState
        qs x data work
        (qs.eval (IQFT x) ψ) := by
    exact
      eval_IQFT_preserves_threeRegsCleanState
        x
        x.reserve
        (data.reserve.drop 1)
        work.reserve
        hxReserveActive
        hdataReserveActive
        hworkReserveActive
        hclean

  /-
  `GateWorkspaceCleanState` for an adjoint QFT asks for the QFT
  workspace to be clean after applying the inverse QFT.
  -/
  have hQFTWorkspaceClean :
      QFTWorkspaceCleanState
        qs
        (qftXWork lowering.ops x)
        (qftZWork lowering.ops x)
        (qs.eval (IQFT x) ψ) := by
    exact
      threeRegsCleanState_to_QFTWorkspaceCleanState_first
        lowering.ops
        x
        rfl
        hHighClean

  have hgateClean :
      GateWorkspaceCleanState
        qs
        lowering.k
        lowering.hk
        lowering.ops
        (IQFT x)
        hworkspace
        ψ := by
    simpa [
      IQFT,
      GateWorkspaceCleanState
    ] using hQFTWorkspaceClean

  constructor

  · exact hgateClean

  · rw [
      lowerGate_correctness
        qs
        lowering.k
        lowering.hk
        lowering.ops
        lowering.consumes
        lowering.returns
        (IQFT x)
        hworkspace
        ψ
        hgateClean
    ]

    exact hHighClean

/-- The final inverse QFT uses only the real exponent reserve for lowering,
while preserving the strengthened exponent-plus-scratch clean register. -/
theorem lowered_IQFT_ready_and_concrete_clean
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (lowering : ShorLoweringSetup)
    (x data work scratch : ExtReg)
    (hxData : x.OwnedDisjoint data)
    (hxWork : x.OwnedDisjoint work)
    (hxScratch : x.OwnedDisjoint scratch)
    (hworkspace :
      GateWorkspaceOK lowering.ops (IQFT x))
    (ψ : qs.State)
    (hclean :
      ShorConcreteCleanState
        qs x data work scratch hxScratch ψ) :
    LoweredCleanResult
      qs lowering
      (ShorConcreteCleanState
        qs x data work scratch hxScratch)
      (IQFT x) hworkspace ψ := by
  have hcombinedActive :
      Disjoint
        (exponentScratchCleanReg x scratch hxScratch)
        x.active := by
    rw [Disjoint, List.disjoint_left]
    intro q hqCombined hqActive
    simp only [
      exponentScratchCleanReg,
      Reg.append,
      ExtReg.ownedReg,
      List.mem_append
    ] at hqCombined
    rcases hqCombined with hqReserve | hqScratch
    · exact
        (not_mem_right_of_mem_left_of_disjoint
          (Disjoint.symm x.active_reserve_disjoint) hqReserve)
          hqActive
    · rw [ExtReg.OwnedDisjoint, List.disjoint_left] at hxScratch
      exact hxScratch
        (by
          rw [ExtReg.ownedQubits, List.mem_append]
          exact Or.inl hqActive)
        (by
          rw [ExtReg.ownedQubits, List.mem_append]
          simpa only [
            ExtReg.ownedReg,
            Reg.append,
            List.mem_append
          ] using hqScratch)

  have hdataActive :
      Disjoint (data.reserve.drop 1) x.active :=
    reserve_drop_active_disjoint_of_ownedDisjoint
      (ownedDisjoint_symm hxData) 1
  have hworkActive :
      Disjoint work.reserve x.active :=
    reserve_active_disjoint_of_ownedDisjoint
      (ownedDisjoint_symm hxWork)

  have hHighClean :
      ShorConcreteCleanState
        qs x data work scratch hxScratch
        (qs.eval (IQFT x) ψ) :=
    eval_IQFT_preserves_threeRegsCleanState
      x
      (exponentScratchCleanReg x scratch hxScratch)
      (data.reserve.drop 1)
      work.reserve
      hcombinedActive hdataActive hworkActive hclean

  have hLoweringClean :
      ShorLoweringCleanState
        qs x data work (qs.eval (IQFT x) ψ) :=
    ShorConcreteCleanState.to_lowering hHighClean

  have hQFTWorkspaceClean :
      QFTWorkspaceCleanState
        qs
        (qftXWork lowering.ops x)
        (qftZWork lowering.ops x)
        (qs.eval (IQFT x) ψ) :=
    threeRegsCleanState_to_QFTWorkspaceCleanState_first
      lowering.ops x rfl hLoweringClean

  have hgateClean :
      GateWorkspaceCleanState
        qs lowering.k lowering.hk lowering.ops
        (IQFT x) hworkspace ψ := by
    simpa [IQFT, GateWorkspaceCleanState] using hQFTWorkspaceClean

  constructor
  · exact hgateClean
  · rw [
      lowerGate_correctness
        qs lowering.k lowering.hk lowering.ops
        lowering.consumes lowering.returns
        (IQFT x) hworkspace ψ hgateClean
    ]
    exact hHighClean


end Shor
