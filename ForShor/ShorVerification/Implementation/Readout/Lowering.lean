import ForShor.ShorVerification.Framework.AbstractMachine.MLowGate
import ForShor.ShorVerification.Implementation.Readout.Cost
import ForShor.ShorVerification.Implementation.Readout.Support
import ForShor.ShorVerification.Implementation.QubitCount.Proofs.Walk

/-!
# Readout: lowering the measurement language, and the claims about it

Everything needed to state what `Readout/Proofs/LowerEval.lean`,
`Readout/Proofs/LowerPeak.lean` and `Readout/Proofs/LowerSupport.lean` prove.

## The lowering

`Policy.lowerM P g hws : MLowGate` lowers an `MGate` under the policy `P`: every
`unitary u` becomes `unitary (Policy.lowerGate P u _)` (the existing lowering,
unchanged), `seq` is kept, and `measureReset` / `ffPhase` are copied as they are.
The workspace argument `hws : MGate.WorkspaceOK P g` is `Policy.GateWorkspaceOK P u`
for every unitary part `u`, taken as a hypothesis exactly as
`orderFindingApproxLow` takes `Policy.GateWorkspaceOK P (orderFindingApprox …)`.
`orderFindingSemiclassicalLow` is the lowered real semiclassical circuit.

## Semantics (ruling R8)

`MLowGate.eval` is the branching-record semantics of `MGate.eval` with the
low-level evaluator `LowerGateClass.evalL` in place of `qs.eval`: on each branch,
`unitary g` applies `evalL g`; `measureReset q` splits a branch by the Born
projectors of `MeasureClass` and resets with `evalL (LowGate.X q)`; `ffPhase q j`
applies `evalL (LowGate.Phase q (ffAngle j rec))` (as in `MGate.eval`).
`Policy.MLowerGateCorrect` is stated in the form of the existing
`Policy.LowerGateCorrect`: for an admissible policy, on a state whose
workspace is clean before every lowered block (`MGate.WorkspaceCleanState`, the
branchwise `Policy.GateWorkspaceCleanState`, with the second component of a
`seq` checked after the first component's LOWERED run, as in the existing
definition), the lowered program evaluates exactly as the program.

## The qubit walk

`MLowGate.peakQubitsFor m g L` walks `g` forwards from the live set `L`: a
`unitary` part walks as `LowGate.peakQubitsFor` (live-set walk of
`QubitCount.peak`, scratch charged by the negation method `m`); `measureReset q`
and `ffPhase q j` make `q` live and allocate nothing (live set `insert q L`, size
counted, no scratch: `ffPhase` is charged like `LowGate.Phase`, whose scratch is
`0`). A qubit that is measured, reset and reused is one element of the live set,
so it is counted once. The peak is the largest live-set size reached.

`Policy.SemiclassicalPeakFormula P`: under the hypotheses of the semiclassical
circuit (its workspaces `hw`, `hs4`, the lowering workspace `hws`, the layout
`SemiclassicalLayout c y work scratch flag`) and at least one round, the
lowered real circuit started from `orderFindingBaseSetSC` (control `c`, data with
carry bit, work, scratch, flag) peaks at exactly `Policy.orderFindingQubitsSC`
(the formula of `Cost.lean`), with the negations counted by `P.negation`.
`Policy.SemiclassicalPeakFormulaBalanced` / `…BalancedU` are the same claim for the
lowerings after `Balanced.balance` / `Balanced.balanceU` of every unitary part
(`Policy.lowerMBalanced`, `Policy.lowerMBalancedU`), with the budgets
`orderFindingQubitsBalancedSC` / `orderFindingQubitsUSC`, mirroring
`Policy.OrderFindingPeakFormulaBalanced` / `…BalancedU`.

The lowered QFT and phase-product blocks are counted by the existing proved walk exactly
as in the coherent circuit (`QubitCount.lower_walk` via `qft_block` / `signed_block` /
`csigned_block`): every named qubit they touch is counted in `semiclassical_peak_formula`,
and their scratch is counted as a number. What is not proved is a syntactic list of the
names those blocks reach (`Gate.qftPhaseReach` / `MGate.qftPhaseReach`, the residual of
`Readout/Proofs/LowerSupport.lean`'s link to the syntactic support `MGate.qubitSupport`),
which the qubit count does not need.

**Scope of the peak claims.** The count is for a model in which `LowGate.Phase` is a
primitive gate with zero scratch: the ancillas of a rotation synthesis (catalyst
states, phase-gradient registers) are NOT counted. Negation scratch (and the one
carry qubit of `AddScaled`) is counted as a number added at the moment it is used
(`QubitCount.scratchFor`), never assigned to named physical qubits. So negation scratch
and rotation-synthesis ancillas are counted as numbers or not modelled, as in the coherent
theorems. For fixed register widths the peak does not depend on the constant `a` or the
modulus `N`: they appear in the circuit only as classical constants and angles (the
widths themselves are chosen from `N` by the caller).
-/

namespace Shor

open QubitCount

/-! ## Lowering -/

/-- Every unitary part of a measurement-language program has the workspace its
lowering needs under `P` (`Policy.GateWorkspaceOK`); `measureReset` and `ffPhase`
need none. -/
def MGate.WorkspaceOK (P : ShorLoweringPolicy) : MGate → Prop
  | .unitary g => Policy.GateWorkspaceOK P g
  | .seq a b => MGate.WorkspaceOK P a ∧ MGate.WorkspaceOK P b
  | .measureReset _ => True
  | .ffPhase _ _ => True

/-- Lower a measurement-language program with the gate lowering `f` on its unitary
parts: `seq` kept, `measureReset` and `ffPhase` copied. -/
def Policy.lowerMWith (P : ShorLoweringPolicy) (f : (u : Gate) → Policy.GateWorkspaceOK P u → LowGate) :
    (g : MGate) → MGate.WorkspaceOK P g → MLowGate
  | .unitary g, h => .unitary (f g h)
  | .seq a b, h => .seq (Policy.lowerMWith P f a h.1) (Policy.lowerMWith P f b h.2)
  | .measureReset q, _ => .measureReset q
  | .ffPhase q j, _ => .ffPhase q j

/-- **The lowering of the measurement language** (`lowerM`). `Policy.lowerGate P` on
every unitary part, `seq` kept, `measureReset` and `ffPhase` copied. -/
def Policy.lowerM (P : ShorLoweringPolicy) : (g : MGate) → MGate.WorkspaceOK P g → MLowGate :=
  Policy.lowerMWith P (Policy.lowerGate P)

/-- The lowering after the balanced split `Balanced.balance P R` of every unitary part
(the measurement-language form of `Balanced.orderFindingApproxLowBalanced`). -/
def Policy.lowerMBalanced (P : ShorLoweringPolicy) (R : Balanced.Rule) :
    (g : MGate) → MGate.WorkspaceOK P g → MLowGate :=
  Policy.lowerMWith P (fun u h => Policy.lowerGate P (Balanced.balance P R u) (Balanced.balance_ok P R u h))

/-- Every phase-product site of every unitary part fits its plan (`Balanced.Fits`). -/
def MGate.Fits (P : ShorLoweringPolicy) (R : Balanced.Rule) : MGate → Prop
  | .unitary g => Balanced.Fits P R g
  | .seq a b => MGate.Fits P R a ∧ MGate.Fits P R b
  | .measureReset _ => True
  | .ffPhase _ _ => True

/-- The lowering after the unconditional balanced split `Balanced.balanceU R` of every
unitary part (the form of `Balanced.orderFindingApproxLowBalancedU`). -/
def Policy.lowerMBalancedU (P : ShorLoweringPolicy) (R : Balanced.Rule) :
    (g : MGate) → MGate.WorkspaceOK P g → MGate.Fits P R g → MLowGate
  | .unitary g, h, hf => .unitary (Policy.lowerGate P (Balanced.balanceU R g) (Balanced.balanceU_ok P R g h hf))
  | .seq a b, h, hf => .seq (Policy.lowerMBalancedU P R a h.1 hf.1) (Policy.lowerMBalancedU P R b h.2 hf.2)
  | .measureReset q, _, _ => .measureReset q
  | .ffPhase q j, _, _ => .ffPhase q j

/-- **The lowered semiclassical order-finding circuit**: `Policy.lowerM` of the real
circuit `orderFindingSemiclassical` (`initY1`, then `m` rounds with the real
multiplier `CmodMulInPlaceCore … (ctrl := c)`), the analogue of
`orderFindingApproxLow`. -/
def orderFindingSemiclassicalLow (P : ShorLoweringPolicy) (a N c m : ℕ)
    (y work scratch : ExtReg) (flag : ℕ) (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hws : MGate.WorkspaceOK P (orderFindingSemiclassical a N c m y work scratch flag hw hs4)) :
    MLowGate :=
  Policy.lowerM P (orderFindingSemiclassical a N c m y work scratch flag hw hs4) hws

/-- The lowered semiclassical circuit after the balanced split. -/
def orderFindingSemiclassicalLowBalanced (P : ShorLoweringPolicy) (R : Balanced.Rule)
    (a N c m : ℕ) (y work scratch : ExtReg) (flag : ℕ) (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hws : MGate.WorkspaceOK P (orderFindingSemiclassical a N c m y work scratch flag hw hs4)) :
    MLowGate :=
  Policy.lowerMBalanced P R (orderFindingSemiclassical a N c m y work scratch flag hw hs4) hws

/-- The lowered semiclassical circuit after the unconditional balanced split. -/
def orderFindingSemiclassicalLowBalancedU (P : ShorLoweringPolicy) (R : Balanced.Rule)
    (a N c m : ℕ) (y work scratch : ExtReg) (flag : ℕ) (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hws : MGate.WorkspaceOK P (orderFindingSemiclassical a N c m y work scratch flag hw hs4))
    (hf : MGate.Fits P R (orderFindingSemiclassical a N c m y work scratch flag hw hs4)) :
    MLowGate :=
  Policy.lowerMBalancedU P R (orderFindingSemiclassical a N c m y work scratch flag hw hs4) hws hf

/-! ## Semantics -/

section Semantics
variable {qs : QSemantics} [RegEncoding qs.Basis]

/-- One child of a branch under the lowered `measureReset q`: the outcome-`b`
projection on qubit `q`, then the low-level `LowGate.X q` when `b = true` (the
low-level form of `measureResetBranch`). -/
noncomputable def measureResetBranchL [LowerGateClass qs] [MeasureClass qs]
    (q : ℕ) (b : Bool) (φ : qs.State) : qs.State :=
  if b then LowerGateClass.evalL (LowGate.X q) (MeasureClass.measProj (qubitReg q) 1 φ)
  else MeasureClass.measProj (qubitReg q) 0 φ

/-- **Branching-record semantics of `MLowGate`**, over `LowerGateClass.evalL`: the
semantics of `MGate.eval` with the low-level evaluator. -/
noncomputable def MLowGate.eval [LowerGateClass qs] [MeasureClass qs] :
    MLowGate → MState qs → MState qs
  | .unitary g, ψ => fun r => LowerGateClass.evalL g (ψ r)
  | .seq a b, ψ => MLowGate.eval b (MLowGate.eval a ψ)
  | .measureReset q, ψ => fun r =>
      if h : r = [] then 0 else measureResetBranchL q (r.getLast h) (ψ r.dropLast)
  | .ffPhase q j, ψ => fun r => LowerGateClass.evalL (LowGate.Phase q (ffAngle j r)) (ψ r)

/-- The workspace of every lowered block is clean where it runs: for `unitary u`,
`Policy.GateWorkspaceCleanState` on every branch; for `seq a b`, `a`'s condition
on the input and `b`'s on the branching state after `a`'s LOWERED run (the form
of the existing `Policy.GateWorkspaceCleanState`); none for `measureReset`,
`ffPhase`. -/
noncomputable def MGate.WorkspaceCleanState (qs : QSemantics) [RegEncoding qs.Basis]
    [GateSemanticsCore qs] [LowerGateClass qs] [MeasureClass qs] (P : ShorLoweringPolicy) :
    (g : MGate) → MGate.WorkspaceOK P g → MState qs → Prop
  | .unitary u, h, ψ => ∀ r, Policy.GateWorkspaceCleanState qs P u h (ψ r)
  | .seq a b, h, ψ =>
      MGate.WorkspaceCleanState qs P a h.1 ψ ∧
      MGate.WorkspaceCleanState qs P b h.2 ((Policy.lowerM P a h.1).eval ψ)
  | .measureReset _, _, _ => True
  | .ffPhase _ _, _, _ => True

/-- **Lowering correctness for the measurement language**, in the form of
`Policy.LowerGateCorrect`: for an admissible policy, the lowered program of a
program with enough workspace acts on a branching state that is clean for it
exactly as the program does. -/
def Policy.MLowerGateCorrect (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs]
    [LowerGateClass qs] [MeasureClass qs] (P : ShorLoweringPolicy) : Prop :=
  P.Admissible →
    ∀ (G : MGate) (hworkspace : MGate.WorkspaceOK P G) (ψ : MState qs),
      MGate.WorkspaceCleanState qs P G hworkspace ψ →
      (Policy.lowerM P G hworkspace).eval ψ = G.eval ψ

end Semantics

/-! ## The qubit walk -/

namespace MLowGate

/-- The live set after `g`, walked forwards from `L`: a unitary part as
`QubitCount.after`; `measureReset q` and `ffPhase q j` make `q` live. -/
def after : MLowGate → Finset ℕ → Finset ℕ
  | .unitary g, L => QubitCount.after g true L
  | .seq a b, L => after b (after a L)
  | .measureReset q, L => insert q L
  | .ffPhase q _, L => insert q L

/-- The largest live-set size reached while walking `g` forwards from `L`, with
`anc u` scratch charged while the low-level primitive `u` runs. `measureReset q`
allocates nothing: it counts the live set with `q` in it. `ffPhase q j` is walked as
the primitive `LowGate.Phase q 0` (the walk of `Phase` does not read the angle), so it
is charged exactly what a `Phase` is charged, `anc (Phase q 0)` included. -/
def peak (anc : LowGate → ℕ) : MLowGate → Finset ℕ → ℕ
  | .unitary g, L => QubitCount.peak anc g true L
  | .seq a b, L => max (peak anc a L) (peak anc b (after a L))
  | .measureReset q, L => (insert q L).card
  | .ffPhase q _, L => QubitCount.peak anc (LowGate.Phase q 0) true L

/-- **Peak number of live qubits** while `g` runs from the live set `L`, scratch
included, with the negations built by `m`: the analogue of
`LowGate.peakQubitsFor`. A recycled qubit (measured, reset, reused) is one live
qubit, counted once. -/
def peakQubitsFor (m : NegationMethod) (g : MLowGate) (L : Finset ℕ) : ℕ :=
  peak (QubitCount.scratchFor m) g L

/-- Every qubit the walk of `g` can make live: `QubitCount.reach` of its unitary
parts, and the qubit of every `measureReset` and `ffPhase`. -/
def reach : MLowGate → Finset ℕ
  | .unitary g => QubitCount.reach g
  | .seq a b => reach a ∪ reach b
  | .measureReset q => {q}
  | .ffPhase q _ => {q}

end MLowGate

/-! ## The QFT and phase-product blocks of a lowering -/

/-- The qubits reached by the lowered QFT and phase-product blocks of `G`: the
circuits `Policy.lowerQFT`, `Policy.lowerSignedPhaseProd` and
`Policy.lowerCSignedPhaseProd` build with their own recursive workspace layouts.
This set is the residual term of the support link (`lowerGate_reach_subset`); it is the
blocks' own `QubitCount.reach`, so the link states no named list of the qubits they reach.
The qubit count does not need one: the peak walk (`QubitCount.lower_walk` via `qft_block` /
`signed_block` / `csigned_block`) counts every named qubit these blocks touch, and their
scratch as a number, exactly as in the coherent circuit. Every other constructor
contributes nothing; in particular the constant comparison and subtraction blocks
are proved to stay inside their operands (`cmpGe_reach_subset`, `cSub_reach_subset`). -/
def Gate.qftPhaseReach (P : ShorLoweringPolicy) : (G : Gate) → Policy.GateWorkspaceOK P G → Finset ℕ
  | .seq U V, h => Gate.qftPhaseReach P U h.1 ∪ Gate.qftPhaseReach P V h.2
  | .adj U, h => Gate.qftPhaseReach P U h
  | .QFT r, h => QubitCount.reach (Policy.lowerQFT P r h)
  | .SignedPhaseProd phi x z, _ => QubitCount.reach (Policy.lowerSignedPhaseProd P phi x z)
  | .CSignedPhaseProd ctrl phi x z, _ =>
      QubitCount.reach (Policy.lowerCSignedPhaseProd P ctrl phi x z)
  | _, _ => ∅

/-- `Gate.qftPhaseReach` over the unitary parts of a measurement-language program. -/
def MGate.qftPhaseReach (P : ShorLoweringPolicy) : (g : MGate) → MGate.WorkspaceOK P g → Finset ℕ
  | .unitary u, h => Gate.qftPhaseReach P u h
  | .seq a b, h => MGate.qftPhaseReach P a h.1 ∪ MGate.qftPhaseReach P b h.2
  | .measureReset _, _ => ∅
  | .ffPhase _ _, _ => ∅

/-! ## The peak claim -/

/--
**The qubit-count formula for the lowered semiclassical order-finding circuit.**
For an admissible policy `P`, every constant `a`, modulus `N`, control `c`, number of
rounds `m ≥ 1`, registers `y` (data), `work`, `scratch` and flag with the
multiplier's workspaces `hw`, `hs4`, the lowering workspace `hws`, and the layout
`SemiclassicalLayout c y work scratch flag` (`c` outside `y`, `work`, `scratch`,
reserves included, and `c ≠ flag`): the lowered circuit
`orderFindingSemiclassicalLow`, walked from `orderFindingBaseSetSC` (`c`, the data
register with its carry bit, work, scratch, flag), peaks, scratch included and the
negations built by `P.negation`, at exactly `Policy.orderFindingQubitsSC P y.width
work.width scratch.width` `= 1 + (dW + 1) + wW + sW + 1 + orderFindingPeakSC`.
The analogue of `Policy.OrderFindingPeakFormula`.
-/
def Policy.SemiclassicalPeakFormula (P : ShorLoweringPolicy) : Prop :=
  P.Admissible →
  ∀ (a N c m : ℕ) (y work scratch : ExtReg) (flag : ℕ)
    (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hws : MGate.WorkspaceOK P (orderFindingSemiclassical a N c m y work scratch flag hw hs4)),
    SemiclassicalLayout c y work scratch flag → 1 ≤ m →
    (orderFindingSemiclassicalLow P a N c m y work scratch flag hw hs4 hws).peakQubitsFor
        P.negation (orderFindingBaseSetSC c y work scratch flag)
      = Policy.orderFindingQubitsSC P y.width work.width scratch.width

/-- **The qubit-count formula for the balanced lowered semiclassical circuit**: the
same hypotheses, lowered after `Balanced.balance` with the rule `R`, the peak is
`Policy.orderFindingQubitsBalancedSC` at the registers' widths and spare
capacities. The analogue of `Policy.OrderFindingPeakFormulaBalanced`. -/
def Policy.SemiclassicalPeakFormulaBalanced (P : ShorLoweringPolicy) (R : Balanced.Rule) : Prop :=
  P.Admissible →
  ∀ (a N c m : ℕ) (y work scratch : ExtReg) (flag : ℕ)
    (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hws : MGate.WorkspaceOK P (orderFindingSemiclassical a N c m y work scratch flag hw hs4)),
    SemiclassicalLayout c y work scratch flag → 1 ≤ m →
    (orderFindingSemiclassicalLowBalanced P R a N c m y work scratch flag hw hs4 hws).peakQubitsFor
        P.negation (orderFindingBaseSetSC c y work scratch flag)
      = Policy.orderFindingQubitsBalancedSC P R y.width y.capacity work.width work.capacity
          scratch.width scratch.capacity

/-- **The qubit-count formula for the unconditionally balanced lowered semiclassical
circuit**: lowered after `Balanced.balanceU` with the rule `R`, on registers whose
spare qubits hold every site's plan (`MGate.Fits`), the peak is
`Policy.orderFindingQubitsUSC` at the register widths alone. The analogue of
`Policy.OrderFindingPeakFormulaBalancedU`. -/
def Policy.SemiclassicalPeakFormulaBalancedU (P : ShorLoweringPolicy) (R : Balanced.Rule) : Prop :=
  P.Admissible →
  ∀ (a N c m : ℕ) (y work scratch : ExtReg) (flag : ℕ)
    (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hws : MGate.WorkspaceOK P (orderFindingSemiclassical a N c m y work scratch flag hw hs4))
    (hf : MGate.Fits P R (orderFindingSemiclassical a N c m y work scratch flag hw hs4)),
    SemiclassicalLayout c y work scratch flag → 1 ≤ m →
    (orderFindingSemiclassicalLowBalancedU P R a N c m y work scratch flag hw hs4 hws hf).peakQubitsFor
        P.negation (orderFindingBaseSetSC c y work scratch flag)
      = Policy.orderFindingQubitsUSC P R y.width work.width scratch.width

end Shor
