import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.Workspace
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.Steps
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.ModExp
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Spec.Precision
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Spec.Validity

/-!
# Modular-Exponentiation Configurations

The bound files pass around compact records rather than repeatedly threading the
modulus, registers, precision proof, workspace proof, layout proof, and
coprimality hypotheses: `Algorithm1Env`, `ModExpConfig` (+ `approxGate`,
`idealGate`, `ValidUnitState`), and `ModMulConfig` (+ `approxGate`, `idealGate`,
`ValidState`, `ValidUnitState`).
-/

namespace Shor

/-- Common environment for one Algorithm 1 modular-multiplication analysis. -/
structure Algorithm1Env (η : ℝ) where
  N : ℕ
  data : ExtReg
  work : ExtReg
  scratch : ExtReg
  modulus_gt_one : 1 < N
  data_capacity  : N ≤ ASize data.active
  precision      : Algorithm1Precision η data.active work.active
  circuit_workspace : ModMulCircuitWorkspaceOK data work

/-- Configuration for approximate modular exponentiation. -/
structure ModExpConfig (η : ℝ) where
  env : Algorithm1Env η
  a : ℕ
  x : Reg
  flag : ℕ
  layout : ModExpLayout x env.data env.work flag
  arithmetic : ModExpArithmeticOK a env.N x
  step4_workspace : CmpLtNWWorkspace env.N (env.data.grow 1) env.work env.scratch flag

namespace ModExpConfig

/-- Concrete approximate modular-exponentiation gate for this configuration. -/
def approxGate {η : ℝ} (cfg : ModExpConfig η) : Gate :=
  modExpApproxValid
    cfg.a cfg.env.N cfg.x cfg.env.data cfg.env.work cfg.env.scratch cfg.flag cfg.env.circuit_workspace cfg.step4_workspace

/-- Ideal modular-exponentiation gate for this configuration. -/
def idealGate
    (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsCore qs] {η : ℝ} (cfg : ModExpConfig η) :
    Gate :=
  modExpIdeal' qs cfg.a cfg.env.N cfg.x cfg.env.data.active

/-- Valid modular-multiplication state with unit norm for modular exponentiation. -/
def ValidUnitState
    (qs : QSemantics) [RegEncoding qs.Basis] {η : ℝ} (cfg : ModExpConfig η) (ψ : qs.State) : Prop :=
  ψ ∈ ValidAlgorithm1State qs cfg.env.N cfg.env.data cfg.env.work cfg.env.scratch cfg.flag ∧ ‖ψ‖ = 1

end ModExpConfig

/-- Configuration for one controlled modular-multiplication core. -/
structure ModMulConfig (η : ℝ) where
  env : Algorithm1Env η
  c : ℕ
  flag : ℕ
  ctrl : ℕ
  coprime  : Nat.Coprime c env.N
  layout   : ModMulCoreLayout env.data env.work flag ctrl
  step4_workspace : CmpLtNWWorkspace env.N (env.data.grow 1) env.work env.scratch flag

namespace ModMulConfig

/-- Concrete five-step approximate modular-multiplication gate for this configuration. -/
def approxGate {η : ℝ} (cfg : ModMulConfig η) : Gate :=
  CmodMulInPlaceCore cfg.c cfg.env.N
    cfg.ctrl cfg.env.data cfg.env.work cfg.env.scratch cfg.flag
    cfg.env.circuit_workspace cfg.step4_workspace

/-- Ideal controlled modular-multiplication gate for this configuration. -/
def idealGate {η : ℝ} (cfg : ModMulConfig η) : Gate :=
  Gate.idealCtrlModMul cfg.c cfg.env.N cfg.env.data.active cfg.ctrl

/-- Valid-state predicate for one modular-multiplication configuration. -/
def ValidState
    (qs : QSemantics) [RegEncoding qs.Basis] {η : ℝ} (cfg : ModMulConfig η) (ψ : qs.State) : Prop :=
  ψ ∈ ValidAlgorithm1State qs cfg.env.N cfg.env.data cfg.env.work cfg.env.scratch cfg.flag

/-- Valid modular-multiplication state with unit norm. -/
def ValidUnitState
    (qs : QSemantics) [RegEncoding qs.Basis] {η : ℝ} (cfg : ModMulConfig η) (ψ : qs.State) : Prop :=
  cfg.ValidState qs ψ ∧ ‖ψ‖ = 1

end ModMulConfig

end Shor
