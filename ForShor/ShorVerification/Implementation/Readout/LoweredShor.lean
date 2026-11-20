import ForShor.ShorVerification.Implementation.Readout.Proofs.LowerClean
import ForShor.ShorVerification.Implementation.Readout.Shor

/-!
# Readout: success of the LOWERED semiclassical order-finding program

`Shor_correct_semiclassical_lowered_at_shorPrecision`: the lowered measurement
program `orderFindingSemiclassicalLow P … = Policy.lowerM P (orderFindingSemiclassical …)`
(every unitary part lowered by `Policy.lowerGate P`; `measureReset` and `ffPhase` copied),
evaluated by the low-level branching semantics `MLowGate.eval` from `MState.init |b0⟩`,
with the record of `m = regSize x.active` outcomes read little-endian and
post-processed by `r_found` (`probability_of_success_M`), succeeds with probability at
least `κ / (2 log(log₂ N + 1))` for every `η ≤ shorPrecision N x`. It is the conclusion
of the coherent `ShorCorrectApproxLowered` (`Shor_correct_approx_lowered_at_shorPrecision`)
for the semiclassical program.

Proof: the run is clean (`semiclassical_clean`), so by `lowerM_eval` the lowered
branching state IS the high-level one (`semiclassical_lowerM_eval`, branch by branch);
record probabilities are read from it, and the high-level bound is
`Shor_correct_semiclassical_at_shorPrecision` (`Shor.lean`).

## Hypotheses, compared with the coherent lowered theorem

The coherent theorem takes `P.Admissible`, the widths `hm`, `hn`, `η ≤ shorPrecision`,
a readiness package `LoweredShorReady` (approximate setup, workspace budget, isolation of
the exponent register, reserves initially zero) and the lowering workspace `hws`. Here:

* `P.Admissible`, `hm`, `hn`, `hη`: the same.
* `SemiclassicalShorSetup` (`Proofs/ShorSetup.lean`): the layout (control `c` outside data, work, scratch,
  reserves included, and `c ≠ flag`), the multiplier workspaces, the precision of the work
  register, the start ket zero on the registers, the flag and `c`, and the reference
  register `x`.
* `SemiclassicalWorkspaceCleanInput y work scratch b0`: the data, work and scratch
  reserves are zero in `b0` (the coherent `workspace_initially_zero` without the
  exponent register's reserve; implied by it, `SemiclassicalWorkspaceCleanInput.of_shor`).
* `hws : MGate.WorkspaceOK P (orderFindingSemiclassical …)`: the lowering workspace of
  every unitary part, taken as a hypothesis exactly as the coherent theorem takes
  `Policy.GateWorkspaceOK P hready.circuit`. (The coherent package's workspace budget is
  only used there to produce such a proof; it is not needed here. On the coherent
  registers, `Readout.semiclassical_hyps_of_coherent` gives `hws` from the coherent one.)

**The reference register `x` is a ghost.** The circuit never touches it: it only fixes
`m = regSize x.active = log₂(2N²)`, `Q = 2^m`, and lets the proof compare with the
textbook circuit `orderFindingIdeal` (see `SemiclassicalShorSetup`).

## Scope

* The feed-forward phases are the ideal exact `LowGate.Phase c (ffAngle j r)` (ρ = 0).
  A synthesized rotation's error is budgeted outside Lean per the project's cost model
  (the `_impl_` theorems of `Readout/Shor.lean` carry a `ρ`, at the `Gate` level).
* This file is about the success probability only. For the qubit count (`Proofs/LowerPeak.lean`),
  the lowered QFT and phase-product blocks of the multipliers are counted by the existing
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
variable {qs : QSemantics.{0}} [RegEncoding qs.Basis] [MeasureClass qs]

/-- **The lowered semiclassical program keeps half of the ideal success bound** (the
statement; proved by `Shor_correct_semiclassical_lowered_at_shorPrecision`). For every
order-finding instance, admissible policy `P`, control `c`, registers with
`m = regSize x.active = log₂(2N²)` and `regSize y.active = log₂(2N)`, precision
`η ≤ shorPrecision N x`, `SemiclassicalShorSetup`, zero data/work/scratch reserves and
lowering workspace `hws`: the lowered program `orderFindingSemiclassicalLow`, run by
`MLowGate.eval` from `MState.init |b0⟩`, finds the order with probability at least
`κ / (2 log(log₂ N + 1))`. The semiclassical counterpart of `ShorCorrectApproxLowered`. -/
def ShorCorrectSemiclassicalLowered [GateSemanticsFacts qs] [LowerGateClass qs] (T : ℕ → ℕ)
    (_hT : ContinuedFractionSearchComplete T) : Prop :=
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
        ((orderFindingSemiclassicalLow P inst.a inst.N c (regSize x.active) y work scratch flag
            hsetup.circuit_workspace hsetup.step4_workspace hws).eval (MState.init (qs.ket b0)))
      ≥ κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1))

/-- **Semiclassical order finding, LOWERED, at `shorPrecision`.** The statement
`ShorCorrectSemiclassicalLowered` holds: for an admissible policy the lowered program
`Policy.lowerM P (orderFindingSemiclassical …)` succeeds with probability
`≥ κ / (2 log(log₂ N + 1))` at every `η ≤ shorPrecision N x`. -/
theorem Shor_correct_semiclassical_lowered_at_shorPrecision [GateSemanticsFacts qs]
    [LowerGateClass qs] (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T) :
    ShorCorrectSemiclassicalLowered (qs := qs) T hT := by
  intro inst P hP c x y work scratch flag b0 hm hn η hη hsetup hzero hws
  rw [orderFindingSemiclassicalLow, semiclassical_lowerM_eval hP _ _ _ _ _ _ _ _ _ _ hws
    hsetup.layout b0 hzero hsetup.clean_input.2.2.2.2.2.1]
  exact Shor_correct_semiclassical_at_shorPrecision T hT inst c x y work scratch flag b0 hm hn η
    hη hsetup

end

end Shor
