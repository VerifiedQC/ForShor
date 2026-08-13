import FastMultiplication.ShorVerification.Implementation.AlgorithmCorrectness.QFT.Decomposition
import FastMultiplication.ShorVerification.Implementation.GateConstructions
import FastMultiplication.ShorVerification.Implementation.AbstractMachine.PhaseProductLoweringCorrectness.Correctness

/-!
# QFT Lowering Plan Semantics

This file defines the explicit recursive plan used to lower a QFT and proves
that interpreting such a plan agrees with the abstract QFT gate whenever the
plan is ready at the input state.

The file is deliberately workspace-agnostic: it knows that a split node carries
an unsigned phase-product lowering plan, but it does not choose concrete reserve
registers.  `QFTLoweringCorrectness.Workspace` supplies that canonical choice.
-/

namespace Shor

open Gate

universe u

/-! =========================================================
    Section 1: Explicit QFT lowering plans
========================================================= -/

/--
A complete physical lowering plan for one QFT.

The phase plan is intentionally explicit.  This is the point at which a caller
chooses either a base-case signed phase product or a recursive implementation
with concrete reserve layouts.
-/
inductive QFTLoweringPlan
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k) :
    Reg → Type

  | empty
      (r : Reg)
      (hsize : regSize r = 0) :
      QFTLoweringPlan k hk ops r

  | singleton
      (r : Reg)
      (hsize : regSize r = 1) :
      QFTLoweringPlan k hk ops r

  | split
      (r : Reg)
      (hsize : 2 ≤ regSize r)
      (ws : Gate.PhaseProdWorkspace (leftReg r) (rightReg r))
      (phaseInitSize : ℕ)
      (phasePlan :
        StandardPhaseLoweringPlan k hk ops
          phaseInitSize (Gate.PhaseProdUsing (qftPhi (regSize r)) (leftReg r) (rightReg r) ws))
      (rightPlan : QFTLoweringPlan k hk ops (rightReg r))
      (leftPlan : QFTLoweringPlan k hk ops (leftReg r)) :
      QFTLoweringPlan k hk ops r

noncomputable def lowerQFTPlan
    {k : ℕ}
    {hk : 1 < k}
    {ops : Prog k}
    {r : Reg}
    (plan : QFTLoweringPlan k hk ops r) :
    LowGate := by
  induction plan with
  | empty r hsize =>
      exact LowGate.id

  | singleton r hsize =>
      exact
        LowGate.H
          (r.lowQubit (by omega))

  | split r hsize ws phaseInitSize phasePlan
      rightPlan leftPlan lowerRight lowerLeft =>
      exact
        lowerRight ;;
        lowerGateRec phasePlan ;;
        lowerLeft ;;
        LowGate.RadixReverse r (splitM r)

noncomputable def QFTLoweringReady
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [LowerGateClass qs]
    {k : ℕ}
    {hk : 1 < k}
    {ops : Prog k}
    {r : Reg}
    (plan : QFTLoweringPlan k hk ops r) :
    qs.State → Prop := by
  induction plan with
  | empty r hsize =>
      exact fun _ => True

  | singleton r hsize =>
      exact fun _ => True

  | split r hsize ws phaseInitSize phasePlan
      rightPlan leftPlan readyRight readyLeft =>
      exact fun ψ =>
        Gate.PhaseProdWorkspace.CleanState qs ws ψ
        ∧
        readyRight ψ
        ∧
        let ψRight := LowerGateClass.evalL (qs := qs) (lowerQFTPlan rightPlan) ψ
        PhaseLoweringReady qs phasePlan ψRight
        ∧
        let ψPhase :=
          LowerGateClass.evalL (qs := qs) (lowerGateRec phasePlan) ψRight
        readyLeft ψPhase

theorem evalL_lowerQFTPlan
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGateGateBridge qs]
    {k : ℕ}
    (hk : 1 < k)
    (ops : Prog k)
    (hC :
      ProgConsumesPtsSafe
        (k := k)
        (by omega)
        State.start_state
        ops
        (genInterpolationPoints k))
    (hRun :
      run? ops State.start_state =
        some State.start_state)
    {r : Reg}
    (plan : QFTLoweringPlan k hk ops r)
    (ψ : qs.State)
    (hready : QFTLoweringReady qs plan ψ) :
    LowerGateClass.evalL
        (qs := qs)
        (lowerQFTPlan plan)
        ψ
      =
    qs.eval (Gate.QFT (ExtReg.ofReg r)) ψ := by
  induction plan generalizing ψ with

  | empty r hsize =>
      have hQFT :=
        QFTSemantics.eval_QFT_size0
          (qs := qs)
          (r := ExtReg.ofReg r)
          (ψ := ψ)
          hsize

      calc
        LowerGateClass.evalL
            (qs := qs)
            (lowerQFTPlan
              (QFTLoweringPlan.empty r hsize))
            ψ
            =
          ψ := by
            simp only [
              lowerQFTPlan,
              LowerGateClass.evalL_id
            ]

        _ =
          qs.eval Gate.id ψ := by
            exact (qs.eval_id ψ).symm

        _ =
          qs.eval (Gate.QFT (ExtReg.ofReg r)) ψ := by
            exact hQFT.symm

  | singleton r hsize =>
      have hQFT :=
        QFTSemantics.eval_QFT_size1
          (qs := qs)
          (r := ExtReg.ofReg r)
          (ψ := ψ)
          hsize

      calc
        LowerGateClass.evalL
            (qs := qs)
            (lowerQFTPlan
              (QFTLoweringPlan.singleton r hsize))
            ψ
            =
          qs.eval
            (Gate.H
              (r.lowQubit (by omega)))
            ψ := by
              simp only [
                lowerQFTPlan,
                LowerGateClass.evalL_H
              ]

        _ =
          qs.eval (Gate.QFT (ExtReg.ofReg r)) ψ := by
            exact hQFT.symm

  | split
      r hsize ws phaseInitSize phasePlan
      rightPlan leftPlan ihRight ihLeft =>

      change
        Gate.PhaseProdWorkspace.CleanState
            qs ws ψ
          ∧
        QFTLoweringReady
            qs rightPlan ψ
          ∧
        PhaseLoweringReady
            qs
            phasePlan
            (LowerGateClass.evalL
              (qs := qs)
              (lowerQFTPlan rightPlan)
              ψ)
          ∧
        QFTLoweringReady
            qs
            leftPlan
            (LowerGateClass.evalL
              (qs := qs)
              (lowerGateRec phasePlan)
              (LowerGateClass.evalL
                (qs := qs)
                (lowerQFTPlan rightPlan)
                ψ))
        at hready

      rcases hready with
        ⟨hclean, hreadyRight, hreadyPhase, hreadyLeft⟩

      have hRight :
          LowerGateClass.evalL
              (qs := qs)
              (lowerQFTPlan rightPlan)
              ψ
            =
          qs.eval
              (Gate.QFT
                (ExtReg.ofReg (rightReg r)))
              ψ := by
        exact ihRight ψ hreadyRight

      have hInterp :
          GoodToomCookPoints
            k
            (genInterpolationPoints k)
            (generatedInterpolationPoints_length k) := by
        simpa using
          genInterpolationPoints_good k

      have hPhase :
          LowerGateClass.evalL
              (qs := qs)
              (lowerGateRec phasePlan)
              (LowerGateClass.evalL
                (qs := qs)
                (lowerQFTPlan rightPlan)
                ψ)
            =
          qs.eval
              (Gate.PhaseProdUsing
                (qftPhi (regSize r))
                (leftReg r)
                (rightReg r)
                ws)
              (LowerGateClass.evalL
                (qs := qs)
                (lowerQFTPlan rightPlan)
                ψ) := by
        exact
          evalL_lowerGateRec_correct
            (qs := qs)
            (hInterp := hInterp)
            (hC := hC)
            (hRun := hRun)
            phasePlan
            _
            hreadyPhase

      have hLeft :
          LowerGateClass.evalL
              (qs := qs)
              (lowerQFTPlan leftPlan)
              (LowerGateClass.evalL
                (qs := qs)
                (lowerGateRec phasePlan)
                (LowerGateClass.evalL
                  (qs := qs)
                  (lowerQFTPlan rightPlan)
                  ψ))
            =
          qs.eval
              (Gate.QFT
                (ExtReg.ofReg (leftReg r)))
              (LowerGateClass.evalL
                (qs := qs)
                (lowerGateRec phasePlan)
                (LowerGateClass.evalL
                  (qs := qs)
                  (lowerQFTPlan rightPlan)
                  ψ)) := by
        exact
          ihLeft
            _
            hreadyLeft

      have hSplit :
          qs.eval
            (Gate.QFT (ExtReg.ofReg r))
            ψ
            =
          qs.eval
            (
              Gate.QFT
                (ExtReg.ofReg (rightReg r)) ;;
              Gate.PhaseProdUsing
                (qftPhi (regSize r))
                (leftReg r)
                (rightReg r)
                ws ;;
              Gate.QFT
                (ExtReg.ofReg (leftReg r)) ;;
              Gate.RadixReverse r (splitM r)
            )
            ψ := by
        simpa [
          splitM,
          leftQFTReg,
          rightQFTReg,
          ExtReg.width
        ] using
          eval_QFT_split
            (qs := qs)
            (ExtReg.ofReg r)
            ws
            ψ
            hclean
            hsize

      simp only [
        lowerQFTPlan,
        LowerGateClass.evalL_seq
      ]

      rw [LowerGateClass.evalL_radixReverse]
      change
        qs.eval (Gate.RadixReverse r (splitM r))
          (LowerGateClass.evalL
            (qs := qs)
            (lowerQFTPlan leftPlan)
            (LowerGateClass.evalL
              (qs := qs)
              (lowerGateRec phasePlan)
              (LowerGateClass.evalL
                (qs := qs)
                (lowerQFTPlan rightPlan)
                ψ)))
          =
        qs.eval
          (Gate.QFT (ExtReg.ofReg r))
          ψ
      rw [hLeft]
      rw [hPhase]
      rw [hRight]

      simpa [qs.eval_seq] using hSplit.symm

/-! =========================================================
    Section 4: Linearity and workspace preservation
========================================================= -/

lemma evalL_lowerQFTPlan_zero
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    {k : ℕ}
    {hk : 1 < k}
    {ops : Prog k}
    {r : Reg}
    (plan : QFTLoweringPlan k hk ops r) :
    LowerGateClass.evalL
        (qs := qs)
        (lowerQFTPlan plan)
        0
      =
    0 := by
  exact LowerGateClass.evalL_zero (qs := qs) (lowerQFTPlan plan)


lemma evalL_lowerQFTPlan_add
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    {k : ℕ}
    {hk : 1 < k}
    {ops : Prog k}
    {r : Reg}
    (plan : QFTLoweringPlan k hk ops r)
    (ψ φ : qs.State) :
    LowerGateClass.evalL
        (qs := qs)
        (lowerQFTPlan plan)
        (ψ + φ)
      =
    LowerGateClass.evalL
        (qs := qs)
        (lowerQFTPlan plan)
        ψ
      +
    LowerGateClass.evalL
        (qs := qs)
        (lowerQFTPlan plan)
        φ := by
  exact LowerGateClass.evalL_add (qs := qs) (lowerQFTPlan plan) ψ φ


lemma evalL_lowerQFTPlan_smul
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    {k : ℕ}
    {hk : 1 < k}
    {ops : Prog k}
    {r : Reg}
    (plan : QFTLoweringPlan k hk ops r)
    (a : ℂ)
    (ψ : qs.State) :
    LowerGateClass.evalL
        (qs := qs)
        (lowerQFTPlan plan)
        (a • ψ)
      =
    a •
      LowerGateClass.evalL
        (qs := qs)
        (lowerQFTPlan plan)
        ψ := by
  exact LowerGateClass.evalL_smul (qs := qs) (lowerQFTPlan plan) a ψ


lemma QFTLoweringReady.zero
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [LowerGateClass qs]
    {k : ℕ}
    {hk : 1 < k}
    {ops : Prog k}
    {r : Reg}
    (plan : QFTLoweringPlan k hk ops r) :
    QFTLoweringReady qs plan 0 := by
  induction plan with
  | empty =>
      trivial
  | singleton =>
      trivial
  | split r hsize ws phaseInitSize phasePlan
      rightPlan leftPlan ihRight ihLeft =>
      change
        Gate.PhaseProdWorkspace.CleanState qs ws 0
          ∧
        QFTLoweringReady qs rightPlan 0
          ∧
        PhaseLoweringReady
          qs phasePlan
          (LowerGateClass.evalL
            (qs := qs)
            (lowerQFTPlan rightPlan)
            0)
          ∧
        QFTLoweringReady
          qs leftPlan
          (LowerGateClass.evalL
            (qs := qs)
            (lowerGateRec phasePlan)
            (LowerGateClass.evalL
              (qs := qs)
              (lowerQFTPlan rightPlan)
              0))
      rw [
        evalL_lowerQFTPlan_zero,
        evalL_lowerGateRec_zero
      ]
      exact
        ⟨
          CleanClosure.zero,
          ihRight,
          PhaseLoweringReady.zero qs phasePlan,
          ihLeft
        ⟩


lemma QFTLoweringReady.add
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [LowerGateClass qs]
    {k : ℕ}
    {hk : 1 < k}
    {ops : Prog k}
    {r : Reg}
    (plan : QFTLoweringPlan k hk ops r)
    {ψ φ : qs.State}
    (hψ : QFTLoweringReady qs plan ψ)
    (hφ : QFTLoweringReady qs plan φ) :
    QFTLoweringReady qs plan (ψ + φ) := by
  induction plan generalizing ψ φ with
  | empty =>
      trivial
  | singleton =>
      trivial
  | split r hsize ws phaseInitSize phasePlan
      rightPlan leftPlan ihRight ihLeft =>
      change
        Gate.PhaseProdWorkspace.CleanState qs ws ψ
          ∧
        QFTLoweringReady qs rightPlan ψ
          ∧
        PhaseLoweringReady
          qs phasePlan
          (LowerGateClass.evalL
            (qs := qs)
            (lowerQFTPlan rightPlan)
            ψ)
          ∧
        QFTLoweringReady
          qs leftPlan
          (LowerGateClass.evalL
            (qs := qs)
            (lowerGateRec phasePlan)
            (LowerGateClass.evalL
              (qs := qs)
              (lowerQFTPlan rightPlan)
              ψ))
        at hψ
      change
        Gate.PhaseProdWorkspace.CleanState qs ws φ
          ∧
        QFTLoweringReady qs rightPlan φ
          ∧
        PhaseLoweringReady
          qs phasePlan
          (LowerGateClass.evalL
            (qs := qs)
            (lowerQFTPlan rightPlan)
            φ)
          ∧
        QFTLoweringReady
          qs leftPlan
          (LowerGateClass.evalL
            (qs := qs)
            (lowerGateRec phasePlan)
            (LowerGateClass.evalL
              (qs := qs)
              (lowerQFTPlan rightPlan)
              φ))
        at hφ
      rcases hψ with
        ⟨hcleanψ, hrightψ, hphaseψ, hleftψ⟩
      rcases hφ with
        ⟨hcleanφ, hrightφ, hphaseφ, hleftφ⟩
      change
        Gate.PhaseProdWorkspace.CleanState qs ws (ψ + φ)
          ∧
        QFTLoweringReady qs rightPlan (ψ + φ)
          ∧
        PhaseLoweringReady
          qs phasePlan
          (LowerGateClass.evalL
            (qs := qs)
            (lowerQFTPlan rightPlan)
            (ψ + φ))
          ∧
        QFTLoweringReady
          qs leftPlan
          (LowerGateClass.evalL
            (qs := qs)
            (lowerGateRec phasePlan)
            (LowerGateClass.evalL
              (qs := qs)
              (lowerQFTPlan rightPlan)
              (ψ + φ)))
      rw [
        evalL_lowerQFTPlan_add,
        evalL_lowerGateRec_add
      ]
      exact
        ⟨
          CleanClosure.add
            hcleanψ hcleanφ,
          ihRight hrightψ hrightφ,
          PhaseLoweringReady.add
            qs phasePlan hphaseψ hphaseφ,
          ihLeft hleftψ hleftφ
        ⟩


lemma QFTLoweringReady.smul
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [LowerGateClass qs]
    {k : ℕ}
    {hk : 1 < k}
    {ops : Prog k}
    {r : Reg}
    (plan : QFTLoweringPlan k hk ops r)
    (a : ℂ)
    {ψ : qs.State}
    (hψ : QFTLoweringReady qs plan ψ) :
    QFTLoweringReady qs plan (a • ψ) := by
  induction plan generalizing ψ with
  | empty =>
      trivial
  | singleton =>
      trivial
  | split r hsize ws phaseInitSize phasePlan
      rightPlan leftPlan ihRight ihLeft =>
      change
        Gate.PhaseProdWorkspace.CleanState qs ws ψ
          ∧
        QFTLoweringReady qs rightPlan ψ
          ∧
        PhaseLoweringReady
          qs phasePlan
          (LowerGateClass.evalL
            (qs := qs)
            (lowerQFTPlan rightPlan)
            ψ)
          ∧
        QFTLoweringReady
          qs leftPlan
          (LowerGateClass.evalL
            (qs := qs)
            (lowerGateRec phasePlan)
            (LowerGateClass.evalL
              (qs := qs)
              (lowerQFTPlan rightPlan)
              ψ))
        at hψ
      rcases hψ with
        ⟨hclean, hright, hphase, hleft⟩
      change
        Gate.PhaseProdWorkspace.CleanState qs ws (a • ψ)
          ∧
        QFTLoweringReady qs rightPlan (a • ψ)
          ∧
        PhaseLoweringReady
          qs phasePlan
          (LowerGateClass.evalL
            (qs := qs)
            (lowerQFTPlan rightPlan)
            (a • ψ))
          ∧
        QFTLoweringReady
          qs leftPlan
          (LowerGateClass.evalL
            (qs := qs)
            (lowerGateRec phasePlan)
            (LowerGateClass.evalL
              (qs := qs)
              (lowerQFTPlan rightPlan)
              (a • ψ)))
      rw [
        evalL_lowerQFTPlan_smul,
        evalL_lowerGateRec_smul
      ]
      exact
        ⟨
          CleanClosure.smul
            a hclean,
          ihRight hright,
          PhaseLoweringReady.smul
            qs phasePlan a hphase,
          ihLeft hleft
        ⟩
