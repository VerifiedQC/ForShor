import FastMultiplication.ShorVerification.Implementation.Reference.Balanced.Correctness
import FastMultiplication.ShorVerification.Implementation.Shor.Main

/-!
# Balanced phase products in the end-to-end Shor theorem

`orderFindingApproxLowBalanced` lowers the approximate order-finding circuit
with every phase-product site balanced (`Balanced.balance`) and ForShor's own
`Policy.lowerGate`. It takes exactly the hypotheses `orderFindingApproxLow`
takes, and the success-probability theorem holds for it with exactly the
hypotheses and conclusion of `Shor_correct_approx_lowered_of_modExp_bound`.
-/

namespace Shor
namespace Balanced

variable {qs : QSemantics}
variable [RegEncoding qs.Basis]
variable [MeasureClass qs]

/-- Lowered approximate order finding with balanced phase-product sites. -/
def orderFindingApproxLowBalanced
    (P : ShorLoweringPolicy) (R : Rule)
    (a N : ℕ) (x y work scratch : ExtReg) (flag : ℕ)
    (hmodWorkspace : ModMulCircuitWorkspaceOK y work)
    (hstep4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hLowerWorkspace : Policy.GateWorkspaceOK P
      (orderFindingApprox a N x y work scratch flag hmodWorkspace hstep4)) : LowGate :=
  Policy.lowerGate P
    (balance P R (orderFindingApprox a N x y work scratch flag hmodWorkspace hstep4))
    (balance_ok P R _ hLowerWorkspace)

/-- Balancing changes no success probability: the balanced lowering has the
source circuit's success probability. -/
theorem probability_of_success_balance_eq
    [GateSemanticsFacts qs] [LowerGateClass qs]
    (P : ShorLoweringPolicy) (hP : P.Admissible) (R : Rule)
    (T : ℕ → ℕ) (verify : OrderVerifier) (x : Reg) (r Q : ℕ)
    (G : Gate) (hworkspace : Policy.GateWorkspaceOK P G) (ψ : qs.State)
    (hclean : Policy.GateWorkspaceCleanState qs P G hworkspace ψ) :
    probability_of_success (qs := qs) (evalC := LowerGateClass.evalL (qs := qs))
        (T := T) (verify := verify) (x := x) (r := r) (Q := Q)
        (C := Policy.lowerGate P (balance P R G) (balance_ok P R G hworkspace)) (ψ := ψ)
      =
    probability_of_success (qs := qs) (evalC := qs.eval)
        (T := T) (verify := verify) (x := x) (r := r) (Q := Q) (C := G) (ψ := ψ) := by
  have hEval := Policy.lowerGate_balance_correctness qs P hP R G hworkspace ψ hclean
  unfold probability_of_success MeasureClass.probMeas
  apply Finset.sum_congr rfl
  intro o _
  rw [hEval]

/-- **End-to-end Shor correctness with the balanced split**: the statement of
`Shor_correct_approx_lowered_of_modExp_bound`, for the balanced lowering. -/
theorem Shor_correct_approx_lowered_balanced_of_modExp_bound
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (R : Rule)
    (K : ℝ)
    (hmodExp :
      ∀ (η : ℝ) (cfg : ModExpConfig η) (ψ : qs.State),
        ModExpConfig.ValidUnitState qs cfg ψ →
        ‖qs.eval (ModExpConfig.approxGate cfg) ψ -
            qs.eval (ModExpConfig.idealGate qs cfg) ψ‖
          ≤ (tbits cfg.x : ℝ) * stepErr K η)
    (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T)
    (inst : ShorOrderFindingInstance)
    (P : ShorLoweringPolicy)
    (hP : P.Admissible)
    (x y work scratch : ExtReg) (flag : ℕ)
    (b0 : qs.Basis)
    (hm : regSize x.active = Nat.log2 (2 * inst.N^2))
    (hn : regSize y.active = Nat.log2 (2 * inst.N))
    (η : ℝ)
    (hready : LoweredShorReady
      qs P η inst.a inst.N x y work scratch flag b0) :
    probability_of_success
        (qs := qs) (T := T)
        (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
        (x := x.active)
        (r := ord inst.a inst.N inst.coprime)
        (Q := ASize x.active)
        (evalC := LowerGateClass.evalL (qs := qs))
        (C := orderFindingApproxLowBalanced P R
          inst.a inst.N x y work scratch flag
          (ShorApproxSetupMinimal.toShorApproxSetup hready.approx).circuit_workspace
          (ShorApproxSetupMinimal.toShorApproxSetup hready.approx).step4_workspace
          hready.workspace)
        (ψ := qs.ket b0)
      ≥
    κ / Real.log ((Nat.log2 inst.N : ℝ) + 1) -
      2 * (tbits x.active : ℝ) * Real.sqrt (2 * (K * η)) := by
  have h := Shor_correct_approx_lowered_of_modExp_bound (qs := qs) K hmodExp T hT
    inst P hP x y work scratch flag b0 hm hn η hready
  rw [orderFindingApproxLow_probability_eq (qs := qs) P hP T _ inst.a inst.N x y work scratch flag
    _ _ hready.workspace (qs.ket b0) (hready.workspace_clean hP)] at h
  unfold orderFindingApproxLowBalanced
  rw [probability_of_success_balance_eq (qs := qs) P hP R T _ _ _ _ _ hready.workspace (qs.ket b0)
    (hready.workspace_clean hP)]
  exact h

end Balanced
end Shor
