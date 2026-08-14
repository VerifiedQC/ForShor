import FastMultiplication.ShorVerification.Implementation.Shor.Defs
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Proofs.ModExp
import FastMultiplication.ShorVerification.Framework.Submission
import FastMultiplication.ShorVerification.Framework.Math.ShorDefinition
import FastMultiplication.ShorVerification.Framework.Math.Factoring_Reduction.Reduction

/-!
# Shor Public Assertions

The final Shor correctness guarantees, each stated once as a named proposition.
The theorems in `Proofs/Correctness.lean` are typed directly by these Props, so
there is exactly one copy of each statement and it is the one consumers resolve
through.

This file imports `Proofs.Readiness`: the statements plug proof-derived terms
into `Prop`-valued hypothesis slots (e.g. `hready.workspace`), so by proof
irrelevance the meaning of each Prop does not depend on those proof bodies —
the trusted reading surface remains `Defs` + `Assertions`.
-/

namespace Shor

variable {qs : QSemantics}
variable [RegEncoding qs.Basis]
variable [MeasureClass qs]
variable [ContinuedFractionPost]
variable [Spec]

/-- Public assertion for `Shor_correct`. -/
def ShorCorrect
    [GateSemanticsFacts qs]
    [IdealCtrlModMulExactSemantics qs]
    (T : ℕ → ℕ)
    (hT : ContinuedFractionSearchComplete T)
    (inst : ShorOrderFindingInstance)
    (b0 : qs.Basis)
    (hinput :
      IdealOrderFindingInput qs inst.x inst.y b0) : Prop :=
  probability_of_success
        (qs := qs)
        (T := T)
        (verify :=
          fun d => decide ((inst.a ^ d) % inst.N = 1))
        (x := inst.x.active)
        (r := ord inst.a inst.N inst.coprime)
        (Q := ASize inst.x.active)
        (evalC := qs.eval)
        (C :=
          orderFindingIdeal
            (qs := qs)
            inst.a inst.N inst.x inst.y)
        (ψ := qs.ket b0)
      ≥
    κ / (Nat.log2 inst.N : ℝ) ^ 4

/-- Public assertion for `Shor_end_to_end_factoring`. -/
def ShorEndToEndFactoring
    [GateSemanticsFacts qs]
    [IdealCtrlModMulExactSemantics qs]
    (T : ℕ → ℕ)
    (hT : ContinuedFractionSearchComplete T)
    (fact : ShorFactoringInstance)
    (x y : ExtReg)
    (b0 : qs.Basis)
    (hinput : IdealOrderFindingInput qs x y b0)
    (hm : regSize x.active = Nat.log2 (2 * fact.N^2))
    (hn : regSize y.active = Nat.log2 (2 * fact.N)) : Prop :=
  (2 * (successful_choices fact.N).card ≥ (valid_choices fact.N).card)
  ∧
  (∀ a ∈ successful_choices fact.N, ∃ (hgcd : Nat.gcd a fact.N = 1),
    (probability_of_success (qs := qs) (T := T)
      (verify := fun d => decide ((a ^ d) % fact.N = 1))
      (x := x.active)
      (r := ord a fact.N hgcd)
      (Q := ASize x.active)
      (evalC := qs.eval)
      (C := orderFindingIdeal (qs := qs) a fact.N x y)
      (ψ := qs.ket b0)
    ≥ κ / (Nat.log2 fact.N : ℝ)^4)
    ∧
    (is_nontrivial_factor
        (Nat.gcd ((a ^ (ord a fact.N hgcd / 2)) - 1) fact.N)
        fact.N ∨
     is_nontrivial_factor
        (Nat.gcd ((a ^ (ord a fact.N hgcd / 2)) + 1) fact.N)
        fact.N))

/-- Public assertion for `Shor_correct_approx_lowered_uniform`. -/
def ShorCorrectApproxLoweredUniform
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGateGateBridge qs]
    [IdealCtrlModMulExactSemantics qs]
    [ModMulPrimitiveGateSemantics qs]
    (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧
      ∀ (inst : ShorOrderFindingInstance)
        (lowering : ShorLoweringSetup)
        (work : ExtReg) (flag : ℕ)
        (b0 : qs.Basis)
        (η : ℝ)
        (hready : LoweredShorReady qs lowering η inst.a inst.N inst.x inst.y work flag b0),
        probability_of_success (qs := qs) (T := T)
          (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
          (x := inst.x.active) (r := ord inst.a inst.N inst.coprime)
          (Q := ASize inst.x.active) (evalC := LowerGateClass.evalL (qs := qs))
          (C := orderFindingApproxLow qs lowering.k lowering.hk lowering.ops
              inst.a inst.N inst.x inst.y work flag
              (ShorApproxSetupMinimal.toShorApproxSetup hready.approx).circuit_workspace hready.workspace)
            (ψ := qs.ket b0)
          ≥
        κ / (Nat.log2 inst.N : ℝ) ^ 4
          -
        2 * (tbits inst.x.active : ℝ) * Real.sqrt (2 * (K * η))

end Shor
