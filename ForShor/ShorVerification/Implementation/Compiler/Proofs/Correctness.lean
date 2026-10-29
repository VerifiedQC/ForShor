import ForShor.ShorVerification.Implementation.Compiler.Proofs.SingleTable
import ForShor.ShorVerification.Implementation.QFT.Proofs.Lowering.Readiness
import ForShor.ShorVerification.Implementation.PhaseProduct.Compiler.Coefficients
import ForShor.ShorVerification.Implementation.PhaseProduct.Compiler.Workspace
import ForShor.ShorVerification.Implementation.PhaseProduct.Lowering.Lower
import ForShor.ShorVerification.Implementation.PhaseProduct.Spec.Cleanliness
import ForShor.ShorVerification.Implementation.PhaseProduct.Main
import ForShor.ShorVerification.Implementation.ModularExponentiation.Proofs.ConstArithmetic

/-!
# Whole-program lowering correctness

This file proves `Policy.lowerGate` (`Compiler/Statement.lean`)
correct: `Policy.lowerGate_correctness` states that the lowered program has
the same action as the source gate whenever the static precondition
(`Policy.GateWorkspaceOK`) and the dynamic one
(`Policy.GateWorkspaceCleanState`) hold, for any admissible policy. The
fixed-table `lowerGate` is the constant-policy instance
(`Policy.gateWorkspaceOK_const_iff`), so no separate proof is needed for it.
-/
namespace Shor
open Operations

universe u

theorem Policy.lowerGate_correctness
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (P : ShorLoweringPolicy)
    (hP : P.Admissible)
    (G : Gate)
    (hworkspace : Policy.GateWorkspaceOK P G)
    (ψ : qs.State)
    (hclean : Policy.GateWorkspaceCleanState qs P G hworkspace ψ) :
    LowerGateClass.evalL (qs := qs) (Policy.lowerGate P G hworkspace) ψ
      =
    qs.eval G ψ := by
  induction G generalizing ψ with

  | id =>
      simp [Policy.lowerGate, LowerGateClass.evalL_id, QSemantics.eval_id]

  | seq U V ihU ihV =>
      change
        Policy.GateWorkspaceCleanState
            qs P
            U
            hworkspace.1
            ψ
          ∧
        Policy.GateWorkspaceCleanState
            qs P
            V
            hworkspace.2
            (LowerGateClass.evalL
              (qs := qs)
              (Policy.lowerGate
                P
                U
                hworkspace.1)
              ψ)
        at hclean

      rcases hclean with
        ⟨hcleanU, hcleanV⟩

      have hUcorrect :
          LowerGateClass.evalL
              (qs := qs)
              (Policy.lowerGate
                P
                U
                hworkspace.1)
              ψ
            =
          qs.eval U ψ := by
        exact
          ihU
            hworkspace.1
            ψ
            hcleanU

      have hcleanV' :
          Policy.GateWorkspaceCleanState
            qs P
            V
            hworkspace.2
            (qs.eval U ψ) := by
        simpa only [hUcorrect] using hcleanV

      calc
        LowerGateClass.evalL
            (qs := qs)
            (Policy.lowerGate
              P
              (Gate.seq U V)
              hworkspace)
            ψ
            =
          LowerGateClass.evalL
            (qs := qs)
            (Policy.lowerGate
              P
              V
              hworkspace.2)
            (LowerGateClass.evalL
              (qs := qs)
              (Policy.lowerGate
                P
                U
                hworkspace.1)
              ψ) := by
                exact
                  LowerGateClass.evalL_seq
                    (Policy.lowerGate
                      P
                      U
                      hworkspace.1)
                    (Policy.lowerGate
                      P
                      V
                      hworkspace.2)
                    ψ

        _ =
          LowerGateClass.evalL
            (qs := qs)
            (Policy.lowerGate
              P
              V
              hworkspace.2)
            (qs.eval U ψ) := by
              rw [hUcorrect]

        _ =
          qs.eval V (qs.eval U ψ) := by
            exact
              ihV
                hworkspace.2
                (qs.eval U ψ)
                hcleanV'

        _ =
          qs.eval (Gate.seq U V) ψ := by
            exact
              (qs.eval_seq U V ψ).symm

    | adj U ihU =>
      change
        Policy.GateWorkspaceCleanState
          qs P U hworkspace
          (qs.eval (Gate.adj U) ψ)
        at hclean

      let φ : qs.State :=
        qs.eval (Gate.adj U) ψ

      have hforward :
          LowerGateClass.evalL
              (qs := qs)
              (Policy.lowerGate
                P U hworkspace)
              φ
            =
          ψ := by
        calc
          LowerGateClass.evalL
              (qs := qs)
              (Policy.lowerGate
                P U hworkspace)
              φ
              =
            qs.eval U φ := by
              exact ihU hworkspace φ hclean
          _ = ψ := by
            exact qs.eval_apply_adj U ψ

      calc
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.adj
              (Policy.lowerGate
                P U hworkspace))
            ψ
            =
          LowerGateClass.evalL
            (qs := qs)
            (LowGate.adj
              (Policy.lowerGate
                P U hworkspace))
            (LowerGateClass.evalL
              (qs := qs)
              (Policy.lowerGate
                P U hworkspace)
              φ) := by
                rw [hforward]

        _ = φ := by
          exact
            LowerGateClass.evalL_adj_apply
              (qs := qs)
              (Policy.lowerGate
                P U hworkspace)
              φ

        _ = qs.eval (Gate.adj U) ψ := rfl

  | H qbit =>
      simpa only [Policy.lowerGate] using
        (LowerGateClass.evalL_H
          (qs := qs)
          qbit
          ψ)

  | X qbit =>
      simpa only [Policy.lowerGate] using
        (LowerGateClass.evalL_X
          (qs := qs)
          qbit
          ψ)

  | CNOT ctrl target =>
      simpa only [Policy.lowerGate] using
        (LowerGateClass.evalL_CNOT
          (qs := qs)
          ctrl
          target
          ψ)

  | Toffoli c₁ c₂ target =>
      simpa only [Policy.lowerGate] using
        (LowerGateClass.evalL_Toffoli
          (qs := qs)
          c₁
          c₂
          target
          ψ)

  | QFT r =>
      change
        QFTWorkspaceCleanState
          qs
          (Policy.qftXWork P r)
          (Policy.qftZWork P r)
          ψ
        at hclean

      simpa only [Policy.lowerGate] using
        (Policy.evalL_lowerQFT qs P hP r ψ
          {
            static := hworkspace
            clean := hclean
          })

  | SignedPhaseProd phi x z =>
      change
        RecursiveWorkspaceCleanState
          qs x z ψ
        at hclean

      simpa only [Policy.lowerGate] using
        (Policy.lowerSignedPhaseProduct_correct qs P phi x z ψ
          {
            static := hworkspace
            clean := hclean
          }
          hP)

    | CSignedPhaseProd ctrl phi x z =>
      change
        RecursiveWorkspaceCleanState
          qs x z ψ
        at hclean

      simpa only [Policy.lowerGate] using
        (Policy.lowerCSignedPhaseProduct_correct qs P ctrl phi x z ψ
          {
            static := hworkspace
            clean := hclean
          }
          hP)

  | CmpGeConst N data scratch flag =>
      change CmpGeConstCleanState qs data scratch ψ at hclean
      simpa only [Policy.lowerGate] using
        (evalL_lowerCmpGeConst qs N data scratch flag
          hworkspace ψ hclean)

  | CSubConst N data scratch flag =>
      change CSubConstCleanState qs N data scratch flag ψ at hclean
      simpa only [Policy.lowerGate] using
        (evalL_lowerCSubConst qs N data scratch flag
          hworkspace ψ hclean)

  | ShiftL r n =>
      simpa only [Policy.lowerGate] using
        (LowerGateClass.evalL_shiftL
          (qs := qs)
          r
          n
          ψ)

  | ShiftR r n =>
      simpa only [Policy.lowerGate] using
        (LowerGateClass.evalL_shiftR
          (qs := qs)
          r
          n
          ψ)

  | Negate r =>
      simpa only [Policy.lowerGate] using
        (LowerGateClass.evalL_negate
          (qs := qs)
          r
          ψ)

  | AddScaled dst src negSrc shift =>
      simpa only [Policy.lowerGate] using
        (LowerGateClass.evalL_addScaled
          (qs := qs)
          dst
          src
          negSrc
          shift
          ψ)

  | zeroExtend r n =>
      simpa only [Policy.lowerGate] using
        (LowerGateClass.evalL_zeroExtend
          (qs := qs)
          r
          n
          ψ)

  | signExtend r n =>
      simpa only [Policy.lowerGate] using
        (LowerGateClass.evalL_signExtend
          (qs := qs)
          r
          n
          ψ)

  | zeroDealloc r n =>
      simpa only [Policy.lowerGate] using
        (LowerGateClass.evalL_zeroDealloc
          (qs := qs)
          r
          n
          ψ)

  | signDealloc r n =>
      simpa only [Policy.lowerGate] using
        (LowerGateClass.evalL_signDealloc
          (qs := qs)
          r
          n
          ψ)

  | RadixReverse r m =>
      simpa only [Policy.lowerGate] using
        (LowerGateClass.evalL_radixReverse
          (qs := qs)
          r
          m
          ψ)

  | idealCtrlModMul c N data ctrl =>
      have hfalse : False := by
        simpa[GateWorkspaceOK]
      exact hfalse.elim

end Shor
