import ForShor.ShorVerification.Implementation.Readout.LoweredShor
import ForShor.ShorVerification.Implementation.Readout.Proofs.LowerPeak
import ForShor.ShorVerification.Implementation.Reference.Balanced.Proofs.Fits

/-!
# Readout: success of the BALANCED lowerings of the semiclassical program

The board's qubit counts for the semiclassical readout are those of the balanced
lowerings (`Policy.SemiclassicalPeakFormulaBalanced` / `…BalancedU`). This file
proves that those same lowered programs succeed with the bound of the plain lowering:

* `ShorCorrectSemiclassicalLoweredBalanced R` / `Shor_correct_semiclassical_lowered_balanced_at_shorPrecision`:
  for every rule `R`, the program `orderFindingSemiclassicalLowBalanced P R …`
  (`Policy.lowerGate P (Balanced.balance P R u)` on every unitary part `u`,
  `measureReset` / `ffPhase` copied), run by `MLowGate.eval` from `MState.init |b0⟩`,
  succeeds with probability `≥ κ / (2 log(log₂ N + 1))` at every `η ≤ shorPrecision N x`.
* `ShorCorrectSemiclassicalLoweredBalancedU R` / `Shor_correct_semiclassical_lowered_balancedU_at_shorPrecision`:
  the same for `orderFindingSemiclassicalLowBalancedU P R …` (every site split by
  `Balanced.balanceU R`), under `MGate.Fits P R` of the circuit.

These mirror the coherent `Balanced.Shor_correct_approx_lowered_balanced_of_modExp_bound`
(any rule, no fit hypothesis, because `Balanced.balance` is the guarded pass) and
`Balanced.balancedUShorCorrect` (fit hypothesis `Balanced.Fits` for `balanceU`).

## Route

`lowerMBalanced_eval`: on a branching state where `MGate.WorkspaceCleanState` holds
(the cleanness of the PLAIN lowered run, the hypothesis of `lowerM_eval`), the balanced
lowering evaluates as the program. Per unitary part this is the existing
`Policy.lowerGate_balance_correctness` (its hypothesis is the plain
`Policy.GateWorkspaceCleanState` of the unbalanced gate, on any state, for any control
qubit: no exponent-register or valid-state hypothesis); over `seq`, the plain lowered
state after the first part equals the high-level one (`lowerM_eval`), so the second
part's cleanness transfers. `semiclassical_clean` (`Proofs/LowerClean.lean`) gives the hypothesis for the
real circuit; then the `Shor.lean` bound applies verbatim, exactly as in
`Shor_correct_semiclassical_lowered_at_shorPrecision`.

## Hypotheses

Those of `ShorCorrectSemiclassicalLowered` (`P.Admissible`, the widths, `η ≤ shorPrecision`,
`SemiclassicalShorSetup`, `SemiclassicalWorkspaceCleanInput`, the lowering workspace
`hws : MGate.WorkspaceOK P …` of the UNBALANCED circuit), plus, for the `U` variant
only, `hf : MGate.Fits P R …` (every phase-product site's plan fits its operands' spare
qubits; the hypothesis of `Policy.lowerMBalancedU`). The guarded variant takes no
hypothesis on `R`.

## Scope

As for the plain lowering: the feed-forward phases are the exact
`LowGate.Phase c (ffAngle j r)` (ρ = 0); the reference register `x` is a ghost (it only
fixes `m = log₂(2N²)`); the lowered QFT and phase-product blocks of the multipliers are counted by the existing
proved walk exactly as in the coherent circuit (`QubitCount.lower_walk` via `qft_block` /
`signed_block` / `csigned_block`): every named qubit they touch is counted in
`semiclassical_peak_formula`, and their scratch is counted as a number. What is not proved
is a syntactic list of the names those blocks reach (`MGate.qftPhaseReach`), which the qubit
count does not need. Negation scratch and rotation-synthesis ancillas are counted as numbers
or not modelled.
-/

namespace Shor

open Readout

section
variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]
  [MeasureClass qs]

/-- **The balanced lowering of the measurement language is correct** on every branching
state where the plain lowering's run is clean (`MGate.WorkspaceCleanState`, the hypothesis
of `lowerM_eval`): it evaluates exactly as the program. -/
theorem lowerMBalanced_eval {P : ShorLoweringPolicy} (hP : P.Admissible) (R : Balanced.Rule)
    (G : MGate) (hws : MGate.WorkspaceOK P G) (ψ : MState qs)
    (hclean : MGate.WorkspaceCleanState qs P G hws ψ) :
    (Policy.lowerMBalanced P R G hws).eval ψ = G.eval ψ := by
  revert hws ψ
  induction G with
  | unitary u =>
      intro h ψ hc
      funext r
      exact Balanced.Policy.lowerGate_balance_correctness qs P hP R u h (ψ r) (hc r)
  | seq a b iha ihb =>
      intro h ψ hc
      have hb : MGate.WorkspaceCleanState qs P b h.2 (a.eval ψ) := by
        have := hc.2
        rwa [lowerM_eval hP a h.1 ψ hc.1] at this
      show (Policy.lowerMBalanced P R b h.2).eval ((Policy.lowerMBalanced P R a h.1).eval ψ)
        = b.eval (a.eval ψ)
      rw [iha h.1 ψ hc.1, ihb h.2 _ hb]
  | measureReset q =>
      intro _ ψ _
      funext r
      show (if h : r = [] then 0 else measureResetBranchL q (r.getLast h) (ψ r.dropLast))
        = (if h : r = [] then 0 else measureResetBranch q (r.getLast h) (ψ r.dropLast))
      split
      · rfl
      · exact measureResetBranchL_eq hP _ _ _
  | ffPhase q j => intro _ _ _; rfl

/-- The unconditional balanced lowering is correct under the same hypothesis, where every
site fits (`MGate.Fits`). -/
theorem lowerMBalancedU_eval {P : ShorLoweringPolicy} (hP : P.Admissible) (R : Balanced.Rule)
    (G : MGate) (hws : MGate.WorkspaceOK P G) (hf : MGate.Fits P R G) (ψ : MState qs)
    (hclean : MGate.WorkspaceCleanState qs P G hws ψ) :
    (Policy.lowerMBalancedU P R G hws hf).eval ψ = G.eval ψ := by
  rw [Readout.lowerMBalancedU_eq]
  exact lowerMBalanced_eval hP R G hws ψ hclean

/-- **The balanced lowered semiclassical circuit evaluates as the circuit**, under the
hypotheses of `semiclassical_lowerM_eval`. -/
theorem semiclassical_lowerMBalanced_eval {P : ShorLoweringPolicy} (hP : P.Admissible)
    (R : Balanced.Rule) (a N c m : ℕ)
    (y work scratch : ExtReg) (flag : ℕ) (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hws : MGate.WorkspaceOK P (orderFindingSemiclassical a N c m y work scratch flag hw hs4))
    (hl : SemiclassicalLayout c y work scratch flag) (b0 : qs.Basis)
    (hzero : SemiclassicalWorkspaceCleanInput y work scratch b0)
    (hscratch : RegEncoding.toNat scratch.active b0 = 0) :
    (orderFindingSemiclassicalLowBalanced P R a N c m y work scratch flag hw hs4 hws).eval
        (MState.init (qs.ket b0))
      = (orderFindingSemiclassical a N c m y work scratch flag hw hs4).eval
        (MState.init (qs.ket b0)) := by
  exact lowerMBalanced_eval hP R _ hws _ (semiclassical_clean hP a N c m y work scratch flag hw hs4
    hws hl b0 hzero hscratch)

/-- **The unconditionally balanced lowered semiclassical circuit evaluates as the circuit**,
under the hypotheses of `semiclassical_lowerM_eval` and `MGate.Fits`. -/
theorem semiclassical_lowerMBalancedU_eval {P : ShorLoweringPolicy} (hP : P.Admissible)
    (R : Balanced.Rule) (a N c m : ℕ)
    (y work scratch : ExtReg) (flag : ℕ) (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hws : MGate.WorkspaceOK P (orderFindingSemiclassical a N c m y work scratch flag hw hs4))
    (hf : MGate.Fits P R (orderFindingSemiclassical a N c m y work scratch flag hw hs4))
    (hl : SemiclassicalLayout c y work scratch flag) (b0 : qs.Basis)
    (hzero : SemiclassicalWorkspaceCleanInput y work scratch b0)
    (hscratch : RegEncoding.toNat scratch.active b0 = 0) :
    (orderFindingSemiclassicalLowBalancedU P R a N c m y work scratch flag hw hs4 hws hf).eval
        (MState.init (qs.ket b0))
      = (orderFindingSemiclassical a N c m y work scratch flag hw hs4).eval
        (MState.init (qs.ket b0)) := by
  exact lowerMBalancedU_eval hP R _ hws hf _ (semiclassical_clean hP a N c m y work scratch flag
    hw hs4 hws hl b0 hzero hscratch)

end

section
variable {qs : QSemantics.{0}} [RegEncoding qs.Basis] [MeasureClass qs]

/-- **The balanced lowered semiclassical program keeps half of the ideal success bound**
(the statement; proved by `Shor_correct_semiclassical_lowered_balanced_at_shorPrecision`).
For every rule `R`: the hypotheses of `ShorCorrectSemiclassicalLowered` (admissible `P`,
control `c`, `m = regSize x.active = log₂(2N²)`, `regSize y.active = log₂(2N)`,
`η ≤ shorPrecision N x`, `SemiclassicalShorSetup`, zero data/work/scratch reserves, and
the lowering workspace `hws` of the unbalanced circuit) give: the balanced lowered program
`orderFindingSemiclassicalLowBalanced P R …`, run by `MLowGate.eval` from
`MState.init |b0⟩`, finds the order with probability at least `κ / (2 log(log₂ N + 1))`.
No hypothesis on `R` (the guarded pass `Balanced.balance` splits a site only where its
plan fits). -/
def ShorCorrectSemiclassicalLoweredBalanced [GateSemanticsFacts qs] [LowerGateClass qs]
    (R : Balanced.Rule) (T : ℕ → ℕ) (_hT : ContinuedFractionSearchComplete T) : Prop :=
  ∀ (inst : ShorOrderFindingInstance) (P : ShorLoweringPolicy) (_hP : P.Admissible)
    (c : ℕ) (x y work scratch : ExtReg) (flag : ℕ) (b0 : qs.Basis)
    (_hm : regSize x.active = Nat.log2 (2 * inst.N ^ 2))
    (_hn : regSize y.active = Nat.log2 (2 * inst.N)) (η : ℝ)
    (_hη : η ≤ shorPrecision inst.N x.active)
    (hsetup : SemiclassicalShorSetup qs η inst.N c x y work scratch flag b0)
    (_hzero : SemiclassicalWorkspaceCleanInput y work scratch b0)
    (hws : MGate.WorkspaceOK P (orderFindingSemiclassical inst.a inst.N c (regSize x.active)
      y work scratch flag hsetup.circuit_workspace hsetup.step4_workspace)),
    probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
        (regSize x.active) (ord inst.a inst.N inst.coprime) (ASize x.active)
        ((orderFindingSemiclassicalLowBalanced P R inst.a inst.N c (regSize x.active) y work
            scratch flag hsetup.circuit_workspace hsetup.step4_workspace hws).eval
          (MState.init (qs.ket b0)))
      ≥ κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1))

/-- **The unconditionally balanced lowered semiclassical program keeps half of the ideal
success bound** (the statement). The hypotheses of
`ShorCorrectSemiclassicalLoweredBalanced`, plus `MGate.Fits P R` of the circuit (every
phase-product site's plan fits), for the program `orderFindingSemiclassicalLowBalancedU`. -/
def ShorCorrectSemiclassicalLoweredBalancedU [GateSemanticsFacts qs] [LowerGateClass qs]
    (R : Balanced.Rule) (T : ℕ → ℕ) (_hT : ContinuedFractionSearchComplete T) : Prop :=
  ∀ (inst : ShorOrderFindingInstance) (P : ShorLoweringPolicy) (_hP : P.Admissible)
    (c : ℕ) (x y work scratch : ExtReg) (flag : ℕ) (b0 : qs.Basis)
    (_hm : regSize x.active = Nat.log2 (2 * inst.N ^ 2))
    (_hn : regSize y.active = Nat.log2 (2 * inst.N)) (η : ℝ)
    (_hη : η ≤ shorPrecision inst.N x.active)
    (hsetup : SemiclassicalShorSetup qs η inst.N c x y work scratch flag b0)
    (_hzero : SemiclassicalWorkspaceCleanInput y work scratch b0)
    (hws : MGate.WorkspaceOK P (orderFindingSemiclassical inst.a inst.N c (regSize x.active)
      y work scratch flag hsetup.circuit_workspace hsetup.step4_workspace))
    (hf : MGate.Fits P R (orderFindingSemiclassical inst.a inst.N c (regSize x.active)
      y work scratch flag hsetup.circuit_workspace hsetup.step4_workspace)),
    probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
        (regSize x.active) (ord inst.a inst.N inst.coprime) (ASize x.active)
        ((orderFindingSemiclassicalLowBalancedU P R inst.a inst.N c (regSize x.active) y work
            scratch flag hsetup.circuit_workspace hsetup.step4_workspace hws hf).eval
          (MState.init (qs.ket b0)))
      ≥ κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1))

/-- **Semiclassical order finding, BALANCED lowering, at `shorPrecision`.** The statement
`ShorCorrectSemiclassicalLoweredBalanced R` holds for every rule `R`. -/
theorem Shor_correct_semiclassical_lowered_balanced_at_shorPrecision [GateSemanticsFacts qs]
    [LowerGateClass qs] (R : Balanced.Rule) (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T) :
    ShorCorrectSemiclassicalLoweredBalanced (qs := qs) R T hT := by
  intro inst P hP c x y work scratch flag b0 hm hn η hη hsetup hzero hws
  rw [semiclassical_lowerMBalanced_eval hP R _ _ _ _ _ _ _ _ _ _ hws hsetup.layout b0 hzero
    hsetup.clean_input.2.2.2.2.2.1]
  exact Shor_correct_semiclassical_at_shorPrecision T hT inst c x y work scratch flag b0 hm hn η
    hη hsetup

/-- **Semiclassical order finding, every site split, at `shorPrecision`.** The statement
`ShorCorrectSemiclassicalLoweredBalancedU R` holds for every rule `R`. -/
theorem Shor_correct_semiclassical_lowered_balancedU_at_shorPrecision [GateSemanticsFacts qs]
    [LowerGateClass qs] (R : Balanced.Rule) (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T) :
    ShorCorrectSemiclassicalLoweredBalancedU (qs := qs) R T hT := by
  intro inst P hP c x y work scratch flag b0 hm hn η hη hsetup hzero hws hf
  rw [semiclassical_lowerMBalancedU_eval hP R _ _ _ _ _ _ _ _ _ _ hws hf hsetup.layout b0 hzero
    hsetup.clean_input.2.2.2.2.2.1]
  exact Shor_correct_semiclassical_at_shorPrecision T hT inst c x y work scratch flag b0 hm hn η
    hη hsetup

end

end Shor
