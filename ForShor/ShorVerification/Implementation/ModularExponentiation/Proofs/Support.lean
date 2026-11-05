import ForShor.ShorVerification.Implementation.ModularExponentiation.Statement

/-!
# Modular exponentiation: definitions the proofs use

The spare-qubit facts behind the step workspaces, `ValidModMulState` and the
exponentiation-tail conditions, and `ModMulConfig`, the record the per-core
bounds are stated over.
-/

namespace Shor

/-! The spare-qubit facts the step workspaces are built from. -/

lemma ModMulCircuitWorkspaceOK.data_canGrow_one {data work : ExtReg}
    (h : ModMulCircuitWorkspaceOK data work) : data.CanGrow 1 :=
  ExtReg.CanGrow.mono h.1 (by norm_num)

lemma ModMulCircuitWorkspaceOK.dataCarry_canGrow_one {data work : ExtReg}
    (h : ModMulCircuitWorkspaceOK data work) : (data.grow 1).CanGrow 1 :=
  ExtReg.canGrow_grow (n := 1) (k := 1) h.1

lemma ModMulCircuitWorkspaceOK.work_canGrow_one {data work : ExtReg}
    (h : ModMulCircuitWorkspaceOK data work) : work.CanGrow 1 :=
  h.2.1

lemma ModMulCircuitWorkspaceOK.dataCarry_work_disjoint {data work : ExtReg}
    (h : ModMulCircuitWorkspaceOK data work) : ExtReg.OwnedDisjoint (data.grow 1) work :=
  h.2.2.grow_left 1

lemma ModMulCircuitWorkspaceOK.work_dataCarry_disjoint {data work : ExtReg}
    (h : ModMulCircuitWorkspaceOK data work) : ExtReg.OwnedDisjoint work (data.grow 1) :=
  (h.2.2.grow_left 1).symm

/--
The full valid-input subspace.

This is the span of *all* computational-basis states satisfying
`GoodModMulBasisInput`; hence it includes arbitrary superpositions over
the control register, exponent register, and valid modular data values.
-/
def ValidModMulState
    (qs : QSemantics) [RegEncoding qs.Basis]
    (N : ℕ) (data work : ExtReg) (flag : ℕ) :
    Submodule ℂ qs.State :=
  Submodule.span ℂ
    ({ ψ : qs.State |
        ∃ b : qs.Basis, GoodModMulBasisInput qs N data work flag b ∧ ψ = qs.ket b } : Set qs.State)

/--
Layout condition required by every controlled modular-multiplication step in a
tail of exponent-control qubits.
-/
def ModExpTailLayout (data work : ExtReg) (flag : ℕ) (ctrls : List ℕ) : Prop :=
  ∀ i : Fin ctrls.length, ModMulCoreLayout data work flag (ctrls.get i)

/--
Arithmetic side condition for a modular-exponentiation tail: the multiplier
used at every remaining exponent position is coprime to `N`.
-/
def ModExpTailArithmeticOK (a N e : ℕ) (ctrls : List ℕ) : Prop :=
  ∀ i : Fin ctrls.length, Nat.Coprime ((a ^ (2 ^ (e + i.1))) % N) N

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
