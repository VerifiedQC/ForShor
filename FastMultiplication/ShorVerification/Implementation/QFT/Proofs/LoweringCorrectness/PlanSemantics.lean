import FastMultiplication.ShorVerification.Implementation.QFT.Defs
import FastMultiplication.ShorVerification.Implementation.QFT.Proofs.Decomposition
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Defs
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.LoweringCorrectness.Linearity
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.GateLevelCorrectness.GateSemanticsLemmas

namespace Shor

section GateSemanticsDissolvedQFT
universe u
variable {Basis : Type u} [RegEncoding Basis]
open QSemantics

namespace QFTSemantics

/-! =========================================================
    Section 1: Base cases — QFT on size-0 and size-1 registers
========================================================= -/

theorem eval_QFT_size0_ket
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [QFTSemantics qs]
    (r : ExtReg)
    (b : qs.Basis)
    (hsize : r.width = 0) :
    qs.eval (Gate.QFT r) (qs.ket b) = qs.ket b := by

  have hactive : regSize r.active = 0 := by
    simpa [ExtReg.width] using hsize

  have hread : RegEncoding.toNat r.active b = 0 := by
    have hlt := RegEncoding.toNat_lt_ASize r.active b
    simp [ASize, hactive] at hlt
    omega

  have hwrite :
      RegEncoding.writeNat r.active 0 b = b := by
    rw [← hread]
    exact RegEncoding.writeNat_toNat r.active b

  rw [QFTSemantics.eval_QFT_ket]
  rw [hsize]

  simp [qftPhase, ωPow, hwrite]

theorem eval_QFT_size0
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [QFTSemantics qs]
    (r : ExtReg)
    (ψ : qs.State)
    (hsize : r.width = 0) :
    qs.eval (Gate.QFT r) ψ = qs.eval Gate.id ψ := by

  have h :
      ∀ φ : qs.State,
        qs.eval (Gate.QFT r) φ = φ := by
    intro φ

    apply qs.state_induction
      (P := fun φ => qs.eval (Gate.QFT r) φ = φ)

    · simp [GateSemanticsCore.eval_zero]

    · intro φ χ hφ hχ
      unfold eval at *
      rw [GateSemanticsCore.eval_add]
      rw [hφ, hχ]

    · intro a φ hφ
      unfold eval at *
      rw [GateSemanticsCore.eval_smul]
      rw [hφ]

    · intro b
      exact eval_QFT_size0_ket (qs := qs) r b hsize

  rw [h ψ]
  symm
  exact GateSemanticsCore.eval_id ψ

theorem eval_QFT_size1_ket
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [QFTSemantics qs]
    [HadamardSemantics qs]
    (r : ExtReg)
    (b : qs.Basis)
    (hsize : r.width = 1) :
    qs.eval (Gate.QFT r) (qs.ket b) =
      qs.eval
        (Gate.H
          (r.active.lowQubit (by
            simp [ExtReg.width] at hsize
            omega)))
        (qs.ket b) := by

  have hactive_size : regSize r.active = 1 := by
    simpa [ExtReg.width] using hsize

  let hpos : 0 < regSize r.active := by
    omega

  let q : ℕ := r.active.lowQubit hpos

  change qs.eval (Gate.QFT r) (qs.ket b) = qs.eval (Gate.H q) (qs.ket b)

  have hactive :
      r.active = qubitReg q := by
    simpa [q] using
      Reg.eq_qubitReg_lowQubit r.active hactive_size

  -- The value stored in the one-bit register is either 0 or 1.
  have hxlt :
      ExtReg.toNat r b < 2 := by
    have h := ExtReg.toNat_lt r b
    simpa [hsize] using h

  -- Logical bit 0 of the active register is precisely physical qubit q.
  have hbit :
      RegEncoding.bit q b =
        Nat.testBit (ExtReg.toNat r b) 0 := by
    have h :=
      RegEncoding.bit_eq_testBit_toNat
        (qubitReg q)
        b
        (⟨0, by simp⟩ : Fin (regSize (qubitReg q)))

    simpa [
      ExtReg.toNat,
      hactive,
      qubitReg,
      Reg.singleton,
      Reg.get,
      regSize,
      Reg.width
    ] using h

  -- Hence the numeric value of this one-bit register is exactly its bit.
  have hx :
      ExtReg.toNat r b =
        if RegEncoding.bit q b then 1 else 0 := by
    have hx_cases :
        ExtReg.toNat r b = 0 ∨
          ExtReg.toNat r b = 1 := by
      omega

    rcases hx_cases with hx0 | hx1
    · have hb :
          RegEncoding.bit q b = false := by
        simpa [hx0] using hbit
      simp [hx0, hb]

    · have hb :
          RegEncoding.bit q b = true := by
        simpa [hx1] using hbit
      simp [hx1, hb]

  -- y = 0 contributes phase 1.
  have hphase0 :
      qftPhase 2 (ExtReg.toNat r b) 0 = 1 := by
    simp [qftPhase, ωPow]

  -- y = 1 contributes +1 or -1 according to the input bit.
  have hphase1 :
      qftPhase 2 (ExtReg.toNat r b) 1 =
        if RegEncoding.bit q b then (-1 : ℂ) else 1 := by
    rw [hx]
    cases hb : RegEncoding.bit q b <;> simp [qftPhase, ωPow, omega_two]
  rw [QFTSemantics.eval_QFT_ket, HadamardSemantics.eval_H_ket]
  rw [hsize]
  simp [pow_one]
  simp at *
  rw [hactive, hphase0, hphase1]
  simp

theorem eval_QFT_size1
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [QFTSemantics qs]
    [HadamardSemantics qs]
    (r : ExtReg)
    (ψ : qs.State)
    (hsize : r.width = 1) :
    qs.eval (Gate.QFT r) ψ =
      qs.eval
        (Gate.H
          (r.active.lowQubit (by
            simp [ExtReg.width] at hsize
            omega)))
        ψ := by

  have h :
      ∀ φ : qs.State,
        qs.eval (Gate.QFT r) φ =
          qs.eval
            (Gate.H
              (r.active.lowQubit (by
                simp [ExtReg.width] at hsize
                omega)))
            φ := by
    intro φ

    apply qs.state_induction
      (P := fun φ =>
        qs.eval (Gate.QFT r) φ =
          qs.eval
            (Gate.H
              (r.active.lowQubit (by
                simp [ExtReg.width] at hsize
                omega)))
            φ)

    · simp [GateSemanticsCore.eval_zero]

    · intro φ χ hφ hχ
      unfold QSemantics.eval at *
      rw [
        GateSemanticsCore.eval_add,
        GateSemanticsCore.eval_add,
        hφ,
        hχ
      ]

    · intro a φ hφ
      unfold QSemantics.eval at *
      rw [
        GateSemanticsCore.eval_smul,
        GateSemanticsCore.eval_smul,
        hφ
      ]

    · intro b
      exact eval_QFT_size1_ket (qs := qs) r b hsize

  exact h ψ

end QFTSemantics

end GateSemanticsDissolvedQFT
end Shor

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
    Section 2: Plan evaluation and its linearity
========================================================= -/

theorem evalL_lowerQFTPlan
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
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

/-! =========================================================
    Section 3: Readiness linearity
========================================================= -/

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
