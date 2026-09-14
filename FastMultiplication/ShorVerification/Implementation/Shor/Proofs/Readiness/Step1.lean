import FastMultiplication.ShorVerification.Implementation.Shor.Spec.Setup
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness.Primitives
import FastMultiplication.ShorVerification.Implementation.Shor.Lowering.LowerGate
import FastMultiplication.ShorVerification.Implementation.QFT.Proofs.Lowering.Readiness
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Proofs.Algorithm1Expansion
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.Steps
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Gates.Macros
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Spec.Cleanliness
import FastMultiplication.ShorVerification.Implementation.Shared.States
import FastMultiplication.ShorVerification.Implementation.Shared.Registers
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.MacroSemantics
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Step 1 Readiness

Step 1 uses the data reserve after dropping the carry bit and the full work
reserve. The final theorem in this section is
`lowered_step1_ready_and_full_clean`.
-/

namespace Shor
open Gate
open Classical


theorem threeRegsCleanState_to_grownRecursiveWorkspaceCleanState
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    {r₁ r₂ r₃ : Reg}
    {x z : Reg}
    (ws : Gate.PhaseProdWorkspace x z)
    (hxReserve :
      ws.xExt.reserve = r₂)
    (hzReserve :
      ws.zExt.reserve = r₃)
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
          FreshZero ws.xExt.reserve b := by
        simpa only [hxReserve] using h₂

      have hzZero :
          FreshZero ws.zExt.reserve b := by
        simpa only [hzReserve] using h₃

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
      exact
        CleanClosure.add
          ihψ
          ihφ

  | smul a hψ ihψ =>
      exact
        CleanClosure.smul
          a
          ihψ

theorem gateWorkspaceCleanState_CPhaseProdUsing_of_threeRegsClean
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
      ws.xExt.reserve = r₂)
    (hzReserve :
      ws.zExt.reserve = r₃)
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
    threeRegsCleanState_to_grownRecursiveWorkspaceCleanState
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


theorem eval_CPhaseProdUsing_preserves_threeRegsCleanState
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {r₁ r₂ r₃ : Reg}
    (ctrl : ℕ)
    (φ : Angle)
    {x z : Reg}
    (ws : Gate.PhaseProdWorkspace x z)
    (hxReserve :
      ws.xExt.reserve = r₂)
    (hzReserve :
      ws.zExt.reserve = r₃)
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
          FreshZero ws.xExt.reserve b := by
        simpa only [hxReserve] using h₂

      have hzZero :
          FreshZero ws.zExt.reserve b := by
        simpa only [hzReserve] using h₃

      have hwsClean :
          ws.Clean b := by
        constructor
        · exact
            freshFor_of_freshZero_reserve
              ws.xExt
              1
              b
              hxZero

        · exact
            freshFor_of_freshZero_reserve
              ws.zExt
              1
              b
              hzZero

      rw [
        GateSemanticsFacts.eval_CPhaseProdUsing_ket
          qs
          ctrl
          φ
          x
          z
          ws
          b
          hwsClean
      ]

      exact
        ThreeRegsCleanState.smul
          _
          (ThreeRegsCleanState.ket
            b h₁ h₂ h₃)

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

theorem eval_IQFT_preserves_threeRegsCleanState
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (r : ExtReg)
    (r₁ r₂ r₃ : Reg)
    {ψ : qs.State}
    (h₁r :
      Disjoint r₁ r.active)
    (h₂r :
      Disjoint r₂ r.active)
    (h₃r :
      Disjoint r₃ r.active)
    (hclean :
      ThreeRegsCleanState
        qs r₁ r₂ r₃ ψ) :
    ThreeRegsCleanState
      qs r₁ r₂ r₃
      (qs.eval (IQFT r) ψ) := by
  classical

  induction hclean with
  | zero =>
      rw [qs.eval_zero]
      exact ThreeRegsCleanState.zero

  | ket b h₁ h₂ h₃ =>
      rcases
          eval_iqft_work_expansion
            qs r b with
        ⟨α, heval⟩

      rw [heval]

      let f :
          Fin (ASize r.active) →
            qs.State :=
        fun t =>
          α t •
            qs.ket
              (RegEncoding.writeNat
                r.active
                t.1
                b)

      have hterm :
          ∀ t : Fin (ASize r.active),
            ThreeRegsCleanState
              qs r₁ r₂ r₃
              (f t) := by
        intro t

        apply ThreeRegsCleanState.smul
        apply ThreeRegsCleanState.ket

        · unfold FreshZero at h₁ ⊢
          rw [
            RegEncoding.toNat_left_write_right
              r₁
              r.active
              h₁r
              b
              t.1
          ]
          exact h₁

        · unfold FreshZero at h₂ ⊢
          rw [
            RegEncoding.toNat_left_write_right
              r₂
              r.active
              h₂r
              b
              t.1
          ]
          exact h₂

        · unfold FreshZero at h₃ ⊢
          rw [
            RegEncoding.toNat_left_write_right
              r₃
              r.active
              h₃r
              b
              t.1
          ]
          exact h₃

      have hsum :
          ∀ s : Finset (Fin (ASize r.active)),
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


theorem threeRegsCleanState_to_QFTWorkspaceCleanState
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    {k : ℕ}
    (ops : Prog k)
    (r : ExtReg)
    {r₁ r₂ r₃ : Reg}
    (hreserve :
      r.reserve = r₃)
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

      · apply FreshZero.of_subset
          (qftXWork ops r)
          r₃
          b
        · intro q hq

          simpa only [hreserve] using
            qftXWork_mem_reserve
              ops r hq

        · exact h₃

      · apply FreshZero.of_subset
          (qftZWork ops r)
          r₃
          b
        · intro q hq

          simpa only [hreserve] using
            qftZWork_mem_reserve
              ops r hq

        · exact h₃

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
