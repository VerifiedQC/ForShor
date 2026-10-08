import FastMultiplication.ShorVerification.Implementation.Shor.Circuit.OrderFinding
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness.Static
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.ModExp
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Spec.Config
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Spec.Precision
import FastMultiplication.ShorVerification.Framework.Contract
import FastMultiplication.ShorVerification.Framework.Math.ShorDefinition
import FastMultiplication.ShorVerification.Framework.Math.Factoring_Reduction.Defs

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

/-! A note on the underscored binders below. `_hT`, `_hm`, `_hn`, `_hinput`
and friends do not appear in the *conclusion* of the Prop they belong to, so
Lean's unused-variable linter wants the underscore; they are not unused
hypotheses. Each is consumed by the theorem that proves the Prop — `_hm`/`_hn`
fix the register widths for `basicSetting_of_shor_instance`, `_hT` bounds the
continued-fraction scan, `_hinput` is the ideal input state — and deleting any
of them does not typecheck. -/

variable {qs : QSemantics}
variable [RegEncoding qs.Basis]
variable [MeasureClass qs]

/-- Public assertion for `Shor_correct`. -/
def ShorCorrect
    [GateSemanticsFacts qs]
    [IdealCtrlModMulExactSemantics qs]
    (T : ℕ → ℕ)
    (_hT : ContinuedFractionSearchComplete T)
    (inst : ShorOrderFindingInstance)
    (x y : ExtReg)
    (b0 : qs.Basis)
    (_hm : regSize x.active = Nat.log2 (2 * inst.N^2))
    (_hn : regSize y.active = Nat.log2 (2 * inst.N))
    (_hinput : IdealOrderFindingInput qs x y b0) : Prop :=
  probability_of_success
        (qs := qs) (T := T)
        (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
        (x := x.active)
        (r := ord inst.a inst.N inst.coprime)
        (Q := ASize x.active)
        (evalC := qs.eval)
        (C := orderFindingIdeal (qs := qs) inst.a inst.N x y)
        (ψ := qs.ket b0)
      ≥
    κ / (Nat.log2 inst.N : ℝ) ^ 4

/-- Public assertion for `Shor_end_to_end_factoring`. -/
def ShorEndToEndFactoring
    [GateSemanticsFacts qs]
    [IdealCtrlModMulExactSemantics qs]
    (T : ℕ → ℕ)
    (_hT : ContinuedFractionSearchComplete T)
    (fact : ShorFactoringInstance)
    (x y : ExtReg)
    (b0 : qs.Basis)
    (_hinput : IdealOrderFindingInput qs x y b0)
    (_hm : regSize x.active = Nat.log2 (2 * fact.N^2))
    (_hn : regSize y.active = Nat.log2 (2 * fact.N)) : Prop :=
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
    [IdealCtrlModMulExactSemantics qs]
    (T : ℕ → ℕ) (_hT : ContinuedFractionSearchComplete T) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧
      ∀ (inst : ShorOrderFindingInstance)
        (lowering : ShorLoweringSetup)
        (x y work scratch : ExtReg) (flag : ℕ)
        (b0 : qs.Basis)
        (_hm : regSize x.active = Nat.log2 (2 * inst.N^2))
        (_hn : regSize y.active = Nat.log2 (2 * inst.N))
        (η : ℝ)
        (hready : LoweredShorReady
          qs lowering η inst.a inst.N x y work scratch flag b0),
        probability_of_success (qs := qs) (T := T)
          (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
          (x := x.active) (r := ord inst.a inst.N inst.coprime)
          (Q := ASize x.active) (evalC := LowerGateClass.evalL (qs := qs))
          (C := orderFindingApproxLow lowering.k lowering.hk lowering.ops
              lowering.pts lowering.hpts
              inst.a inst.N x y work scratch flag
              (ShorApproxSetupMinimal.toShorApproxSetup hready.approx).circuit_workspace
              (ShorApproxSetupMinimal.toShorApproxSetup hready.approx).step4_workspace
              hready.workspace)
            (ψ := qs.ket b0)
          ≥
        κ / (Nat.log2 inst.N : ℝ) ^ 4
          -
        2 * (tbits x.active : ℝ) * Real.sqrt (2 * (K * η))

/-- Public assertion for `Shor_correct_approx_lowered_of_modExp_bound`: the
lowered circuit's success bound, stated against an *assumed* uniform
modular-exponentiation distance bound at a caller-supplied `K`.

This is the form a concrete implementation wants. `ShorCorrectApproxLoweredUniform`
hoists `K` into an existential, which is the right shape for a headline
statement but the wrong one for a caller that has already fixed its own `K`
(as `Reference` does, at `2048`) and needs the conclusion at *that* constant. -/
def ShorCorrectApproxLoweredOfModExpBound
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [IdealCtrlModMulExactSemantics qs]
    (K : ℝ)
    (T : ℕ → ℕ) (_hT : ContinuedFractionSearchComplete T) : Prop :=
  (∀ (η : ℝ) (cfg : ModExpConfig η) (ψ : qs.State),
      ModExpConfig.ValidUnitState qs cfg ψ →
      ‖qs.eval (ModExpConfig.approxGate cfg) ψ -
          qs.eval (ModExpConfig.idealGate qs cfg) ψ‖
        ≤ (tbits cfg.x : ℝ) * stepErr K η) →
    ∀ (inst : ShorOrderFindingInstance)
      (lowering : ShorLoweringSetup)
      (x y work scratch : ExtReg) (flag : ℕ)
      (b0 : qs.Basis)
      (_hm : regSize x.active = Nat.log2 (2 * inst.N^2))
      (_hn : regSize y.active = Nat.log2 (2 * inst.N))
      (η : ℝ)
      (hready : LoweredShorReady
        qs lowering η inst.a inst.N x y work scratch flag b0),
      probability_of_success (qs := qs) (T := T)
        (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
        (x := x.active) (r := ord inst.a inst.N inst.coprime)
        (Q := ASize x.active) (evalC := LowerGateClass.evalL (qs := qs))
        (C := orderFindingApproxLow lowering.k lowering.hk lowering.ops
            lowering.pts lowering.hpts
            inst.a inst.N x y work scratch flag
            (ShorApproxSetupMinimal.toShorApproxSetup hready.approx).circuit_workspace
            (ShorApproxSetupMinimal.toShorApproxSetup hready.approx).step4_workspace
            hready.workspace)
          (ψ := qs.ket b0)
        ≥
      κ / (Nat.log2 inst.N : ℝ) ^ 4
        -
      2 * (tbits x.active : ℝ) * Real.sqrt (2 * (K * η))

/-- The per-step precision at which the lowering loss is at most half of the
ideal success bound `κ / log₂(N)⁴`.

Solving `2 · tbits · √(2 · 2048 · η) ≤ κ / (2 · log₂(N)⁴)` for `η` gives this
threshold; `65536 = 32 · 2048` folds in the uniform constant `K ≤ 2048` of
`modExpApprox_valid_dist_uniform`. With `tbits ≈ 2n` it is `Θ(n⁻¹⁰)` and costs
`algorithm1ExtraBits η ≈ 20 · log₂ n` extra work bits; at 2048 bits it is about
`2⁻¹³⁶`.

The exponents are large because the ideal bound `κ / log₂(N)⁴` is the loose
textbook one and the loss carries a square root, so solving for `η` squares
`κ`, `tbits` and `log⁴N`. `2048` is an unoptimised proof constant, not a
physical one. -/
noncomputable def shorPrecision (N : ℕ) (x : Reg) : ℝ :=
  κ ^ 2 / (65536 * (tbits x : ℝ) ^ 2 * (Nat.log2 N : ℝ) ^ 8)

/-- Public assertion for `Shor_correct_approx_lowered`: at any precision at or
below `shorPrecision N x`, the fully lowered approximate order-finding circuit
keeps at least half of the ideal success bound.

No hidden constant: everything needed to choose `η` before building the circuit
is in the statement. -/
def ShorCorrectApproxLowered
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [IdealCtrlModMulExactSemantics qs]
    (T : ℕ → ℕ) (_hT : ContinuedFractionSearchComplete T) : Prop :=
  ∀ (inst : ShorOrderFindingInstance)
    (lowering : ShorLoweringSetup)
    (x y work scratch : ExtReg) (flag : ℕ)
    (b0 : qs.Basis)
    (_hm : regSize x.active = Nat.log2 (2 * inst.N^2))
    (_hn : regSize y.active = Nat.log2 (2 * inst.N))
    (η : ℝ)
    (_hη : η ≤ shorPrecision inst.N x.active)
    (hready : LoweredShorReady
      qs lowering η inst.a inst.N x y work scratch flag b0),
    probability_of_success (qs := qs) (T := T)
      (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
      (x := x.active) (r := ord inst.a inst.N inst.coprime)
      (Q := ASize x.active) (evalC := LowerGateClass.evalL (qs := qs))
      (C := orderFindingApproxLow lowering.k lowering.hk lowering.ops
          lowering.pts lowering.hpts
          inst.a inst.N x y work scratch flag
          (ShorApproxSetupMinimal.toShorApproxSetup hready.approx).circuit_workspace
          (ShorApproxSetupMinimal.toShorApproxSetup hready.approx).step4_workspace
          hready.workspace)
        (ψ := qs.ket b0)
      ≥
    κ / (2 * (Nat.log2 inst.N : ℝ) ^ 4)

end Shor
