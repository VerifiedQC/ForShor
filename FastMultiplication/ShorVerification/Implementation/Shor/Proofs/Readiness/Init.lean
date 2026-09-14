import FastMultiplication.ShorVerification.Implementation.Shor.Circuit.OrderFinding
import FastMultiplication.ShorVerification.Implementation.Shor.Spec.Setup
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Lowering
import FastMultiplication.ShorVerification.Implementation.QFT.Proofs.Lowering.Readiness
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Proofs.Core
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.Workspace
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.Steps
import FastMultiplication.ShorVerification.Implementation.Semantics.GateSemanticsLemmas
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness.Static
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness.Sequencing
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness.Primitives

/-!
# Workspace-Free Initialization Gates

Readiness and clean-state preservation for `H_reg x.active` and
`initY1 data.active`, which do not allocate recursive lowering workspace but
must still preserve the global clean-state invariant across the rest of the
circuit.
-/

namespace Shor
open Gate
open Classical

/-! =========================================================
    Workspace-free initialization gates

    These helpers cover `H_reg x.active` and `initY1 data.active`, which do not
    allocate recursive lowering workspace but must still preserve the global
    lowered clean invariant.
========================================================= -/

theorem eval_H_reg_preserves_threeRegsCleanState
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (r r₁ r₂ r₃ : Reg)
    {ψ : qs.State}
    (h₁r : Disjoint r₁ r)
    (h₂r : Disjoint r₂ r)
    (h₃r : Disjoint r₃ r)
    (hclean :
      ThreeRegsCleanState
        qs r₁ r₂ r₃ ψ) :
    ThreeRegsCleanState
      qs r₁ r₂ r₃
      (qs.eval (H_reg r) ψ) := by
  induction hclean with
  | zero =>
      rw [qs.eval_zero]
      exact ThreeRegsCleanState.zero

  | ket b h₁ h₂ h₃ =>
      classical

      rcases
          RegisterHadamardSemantics.eval_Hreg_ket
            r b with
        ⟨α, heval⟩

      have heval' :
          qs.eval (H_reg r) (qs.ket b)
            =
          ∑ t : Fin (ASize r),
            α t •
              qs.ket
                (RegEncoding.writeNat r t.1 b) := by
        simpa [H_reg] using heval

      rw [heval']

      let f : Fin (ASize r) → qs.State :=
        fun t =>
          α t •
            qs.ket
              (RegEncoding.writeNat r t.1 b)

      have hterm :
          ∀ t : Fin (ASize r),
            ThreeRegsCleanState
              qs r₁ r₂ r₃
              (f t) := by
        intro t

        apply ThreeRegsCleanState.smul
        apply ThreeRegsCleanState.ket

        · unfold FreshZero at h₁ ⊢
          rw [
            RegEncoding.toNat_left_write_right
              r₁ r h₁r b t.1
          ]
          exact h₁

        · unfold FreshZero at h₂ ⊢
          rw [
            RegEncoding.toNat_left_write_right
              r₂ r h₂r b t.1
          ]
          exact h₂

        · unfold FreshZero at h₃ ⊢
          rw [
            RegEncoding.toNat_left_write_right
              r₃ r h₃r b t.1
          ]
          exact h₃

      have hsum :
          ∀ s : Finset (Fin (ASize r)),
            ThreeRegsCleanState
              qs r₁ r₂ r₃
              (∑ t ∈ s, f t) := by
        intro s

        induction s using Finset.induction_on with
        | empty =>
            simpa using
              (ThreeRegsCleanState.zero :
                ThreeRegsCleanState
                  qs r₁ r₂ r₃ 0)

        | @insert t s ht ih =>
            rw [Finset.sum_insert ht]

            exact
              ThreeRegsCleanState.add
                (hterm t)
                ih

      simpa [f] using hsum Finset.univ

  | add hψ hφ ihψ ihφ =>
      rw [qs.eval_add]
      exact ThreeRegsCleanState.add ihψ ihφ

  | smul a hψ ihψ =>
      rw [qs.eval_smul]
      exact ThreeRegsCleanState.smul a ihψ


private theorem eval_X_preserves_threeRegsCleanState
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
      (qs.eval (Gate.X q) ψ) := by
  induction hclean with
  | zero =>
      rw [qs.eval_zero]
      exact ThreeRegsCleanState.zero

  | ket b h₁ h₂ h₃ =>
      rw [PauliXSemantics.eval_X_ket]

      apply ThreeRegsCleanState.ket

      · unfold FreshZero at h₁ ⊢
        rw [
          RegEncoding.toNat_left_write_right
            r₁
            (qubitReg q)
            h₁q
            b
            (if RegEncoding.bit q b then 0 else 1)
        ]
        exact h₁

      · unfold FreshZero at h₂ ⊢
        rw [
          RegEncoding.toNat_left_write_right
            r₂
            (qubitReg q)
            h₂q
            b
            (if RegEncoding.bit q b then 0 else 1)
        ]
        exact h₂

      · unfold FreshZero at h₃ ⊢
        rw [
          RegEncoding.toNat_left_write_right
            r₃
            (qubitReg q)
            h₃q
            b
            (if RegEncoding.bit q b then 0 else 1)
        ]
        exact h₃

  | add hψ hφ ihψ ihφ =>
      rw [qs.eval_add]
      exact ThreeRegsCleanState.add ihψ ihφ

  | smul a hψ ihψ =>
      rw [qs.eval_smul]
      exact ThreeRegsCleanState.smul a ihψ

theorem lowered_H_reg_ready_and_full_clean
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
        (H_reg x.active))
    (ψ : qs.State)
    (hclean :
      ShorLoweringCleanState
        qs x data work ψ) :
    LoweredCleanResult
      qs
      lowering
      (ShorLoweringCleanState
        qs x data work)
      (H_reg x.active)
      hworkspace
      ψ := by
  have hgateClean :
      GateWorkspaceCleanState
        qs
        lowering.k
        lowering.hk
        lowering.ops
        (H_reg x.active)
        hworkspace
        ψ :=
    (workspaceFree_H_reg x.active).clean
      hworkspace ψ

  have hxReserve :
      Disjoint x.reserve x.active :=
    Disjoint.symm
      x.active_reserve_disjoint

  have hdataReserve :
      Disjoint (data.reserve.drop 1) x.active :=
    reserve_drop_active_disjoint_of_ownedDisjoint
      (ownedDisjoint_symm hxData)
      1

  have hworkReserve :
      Disjoint work.reserve x.active :=
    reserve_active_disjoint_of_ownedDisjoint
      (ownedDisjoint_symm hxWork)

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
        (H_reg x.active)
        hworkspace
        ψ
        hgateClean
    ]

    exact
      eval_H_reg_preserves_threeRegsCleanState
        x.active
        x.reserve
        (data.reserve.drop 1)
        work.reserve
        hxReserve
        hdataReserve
        hworkReserve
        hclean

private theorem eval_initY1_preserves_fullShorWorkspaceCleanState
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (x data work : ExtReg)
    (hxData :
      ExtReg.OwnedDisjoint x data)
    (hmod :
      ModMulCircuitWorkspaceOK data work)
    {ψ : qs.State}
    (hclean :
      ShorLoweringCleanState
        qs x data work ψ) :
    ShorLoweringCleanState
      qs x data work
      (qs.eval (initY1 data.active) ψ) := by
  cases hqubits : data.active.qubits with
  | nil =>
      have hgate :
          initY1 data.active = Gate.id := by
        simp [initY1, hqubits]

      rw [hgate, qs.eval_id]
      exact hclean

  | cons q qubits =>
      have hgate :
          initY1 data.active = Gate.X q := by
        simp [initY1, hqubits]

      have hqActive :
          q ∈ data.active.qubits := by
        simp [hqubits]

      have hxReserveData :
          Disjoint x.reserve data.active :=
        reserve_active_disjoint_of_ownedDisjoint
          hxData

      have hdataReserveData :
          Disjoint (data.reserve.drop 1) data.active :=
        reserve_drop_active_disjoint_self data 1

      have hworkDataOwned :
          ExtReg.OwnedDisjoint work data :=
        ownedDisjoint_symm hmod.2.2

      have hworkReserveData :
          Disjoint work.reserve data.active :=
        reserve_active_disjoint_of_ownedDisjoint
          hworkDataOwned

      have hxQubit :
          Disjoint x.reserve (qubitReg q) :=
        disjoint_qubitReg_of_mem_right
          hxReserveData
          hqActive

      have hdataQubit :
          Disjoint (data.reserve.drop 1) (qubitReg q) :=
        disjoint_qubitReg_of_mem_right
          hdataReserveData
          hqActive

      have hworkQubit :
          Disjoint work.reserve (qubitReg q) :=
        disjoint_qubitReg_of_mem_right
          hworkReserveData
          hqActive

      rw [hgate]

      exact
        eval_X_preserves_threeRegsCleanState
          q
          x.reserve
          (data.reserve.drop 1)
          work.reserve
          hxQubit
          hdataQubit
          hworkQubit
          hclean

theorem lowered_initY1_ready_and_full_clean
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (lowering : ShorLoweringSetup)
    (x data work : ExtReg)
    (hxData :
      ExtReg.OwnedDisjoint x data)
    (hmod :
      ModMulCircuitWorkspaceOK data work)
    (hworkspace :
      GateWorkspaceOK
        lowering.ops
        (initY1 data.active))
    (ψ : qs.State)
    (hclean :
      ShorLoweringCleanState
        qs x data work ψ) :
    LoweredCleanResult
      qs
      lowering
      (ShorLoweringCleanState
        qs x data work)
      (initY1 data.active)
      hworkspace
      ψ := by
  have hgateClean :
      GateWorkspaceCleanState
        qs
        lowering.k
        lowering.hk
        lowering.ops
        (initY1 data.active)
        hworkspace
        ψ :=
    (workspaceFree_initY1 data.active).clean
      hworkspace ψ

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
        (initY1 data.active)
        hworkspace
        ψ
        hgateClean
    ]

    exact
      eval_initY1_preserves_fullShorWorkspaceCleanState
        x
        data
        work
        hxData
        hmod
        hclean


end Shor
