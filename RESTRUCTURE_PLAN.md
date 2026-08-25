# ForShor restructuring plan (v2)

## Organizing principle: Framework vs. Implementation, boundary at LowGate

The repo splits into two independent parts:

- **`Framework/`** — a general framework for *implementing and proving*
  Shor. It fixes what a Shor implementation must provide and proves, once
  and for all, that anything providing it solves order finding within the
  stated resources. **The framework speaks only `LowGate`**: an
  implementation is a `LowGate` program plus a proof of its correctness and
  a proved gate-count bound. The framework never mentions the high-level
  `Gate` language or any particular construction.

- **`Implementations/Reference/`** — one concrete Shor implementation and
  its correctness proof: exactly the development that already exists. It
  builds its `LowGate` program by compiling from the high-level `Gate`
  language (`ModExp`/`QFT`/`PhaseProduct`/`TableGen` constructions +
  `lowerGate`), and discharges the framework's obligations. The existing
  `Shor_correct` / `exists_shorGateCountBound` are this instance — i.e.
  the proof that the framework is non-vacuous.

**The boundary is LowGate.** Everything about `Gate`, the Gate→LowGate
compilation, and the specific circuit constructions lives on the
*implementation* side. The framework side is: the quantum model, the
`LowGate` language + its evaluator, the cost model, the
program-independent mathematics, and the spec + theorems stated over an
abstract `LowGate` implementation.

## Target layout

```
Framework/
  Semantics/
    QSemantics.lean       -- pure quantum model (states, kets, inner product)
    LowGate.lean          -- LowGate syntax + LowerGateClass (evalL) + laws
                             [relocated here as a peer of the model; today it
                              is buried in PhaseProductLoweringCorrectness]
    CostModel.lean        -- LowGate -> gate count (shorGateCostModel, LowGate.gateCount)
  Math/                   -- the mathematical BACKBONE OF SHOR'S ALGORITHM,
                             true of ANY implementation (order->factor,
                             continued-fraction recovery, probability).
                             LITMUS: "would a DIFFERENT correct Shor
                             implementation still need this theorem?" If yes,
                             framework; if it is about THIS construction
                             (Toom-Cook interpolation, Master theorem, table
                             synthesis) it is implementation math under
                             Implementations/Reference. (All the math is
                             already circuit-free, so implementation-
                             INDEPENDENCE is the test, not "mentions a circuit".)
  Spec/
    Implementation.lean   -- structure ShorImplementation: a LowGate program
                             family + correctness obligation + gate-count
                             obligation (stated purely over LowGate + QSemantics)
    Theorems.lean         -- framework theorems: for every ShorImplementation,
                             order finding succeeds with the stated probability
                             and the gate count is bounded. Quantified over the
                             interface, not any construction.
  Checks/                 -- axiom whitelist + #print axioms machinery
Implementations/
  Reference/
    Gate/                 -- the high-level Gate language + GateSemanticsCore
    Subroutines/          -- ModExp, QFT, PhaseProduct, TableGen; each split
                             per Runzhou's directive into
                               Math.lean         (program-independent, no Prog)
                               Spec.lean/Def.lean
                               Correctness.lean  (program-dependent)
    Compilation/          -- Gate -> LowGate lowering (lowerGate) + the
                             LowerGate*Bridge classes
    Discharge.lean        -- the compiled LowGate program satisfies the
                             Framework spec => Shor_correct /
                             exists_shorGateCountBound as instances of the
                             Framework theorems
```

Two nested organizing axes coexist:
- top level: **Framework (LowGate + spec + math + model) vs Implementation
  (Gate + compilation + constructions)** — Anirudh's directive;
- within the Reference implementation: **by subroutine**, each split into
  program-independent `Math` vs program-dependent `Correctness` — Runzhou's
  directive.

## Invariant for every PR

`lake build` green, and `#print axioms` unchanged on `Shor.Shor_correct`
and `Shor.exists_shorGateCountBound` (no new axioms; the one pre-existing
`sorry` untouched). No statement or proof changes except where a phase
explicitly merges duplicate definitions (verified by the same two gates).

## Phases

- **Phase 0 — dedup (DONE).** 0a byte-identical alias; 0b the six-way
  `CleanState` clone unified into one generic `CleanClosure`. Deliberately
  kept distinct: `Full` vs `ShorLowering`, and the two `Point` types
  (correct math-vs-program boundary).
- **Phase 1 — Framework/Semantics.** Carve out `QSemantics`, relocate
  `LowerGateClass` next to the `LowGate` syntax as a peer of
  `GateSemanticsCore` (fixes the placement asymmetry), split `Basic.lean`
  along its section banners, isolate the cost model.
- **Phase 2 — Framework/Math (DONE).** Moved the algorithm backbone
  (`ShorDefinition`; `Factoring_Reduction/`) into `Framework/Math/`, the old
  `MathBackbone/` paths deleted and the sole importer (`ShorCorrectness`)
  updated — no umbrellas. Construction math (`Toom_Cook_formula`,
  `MasterTheoremProof`, `Table_Generation`) stays and relocates to
  Implementations/Reference in Phase 4.
- **Phase 3 — Framework/Spec (DONE — the load-bearing generalization).**
  `Framework/Spec/ShorImplementation.lean` defines `ShorImplementation` as a
  **construction-free** interface: a bare LowGate circuit family
  `prog : ShorOrderFindingInstance → ℕ → LowGate` plus two behavioural
  obligations. Nothing about how the circuit is built appears — no
  `ShorLoweringSetup`, no `PhaseProductProgramOK`, no Toom–Cook / table
  synthesis, no specific Gate-level circuit — so an implementation that
  multiplies a completely different way can still satisfy it. Fields: `prog`;
  `correct` (`ShorImplementsOrderFinding`: for any instance, clean input, and
  search budget, the implementation-neutral `∀ ε > 0, ∃ m,
  prob(prog inst m) ≥ κ/log⁴N − ε` — arbitrary closeness, no `η`/precision knob
  exposed); `gateBound : instance → ℕ → ℕ` (a declared *concrete* count
  function); and `counted` (`gateCount shorGateCostModel (prog inst m) ≤
  gateBound inst m`; tightening `≤` to `=` is a future step). Preconditions are
  as weak as order-finding itself: an instance + `IdealOrderFindingInput`
  (clean, disjoint exponent/data registers) — no ancilla/workspace assumptions.
  `framework_order_finding_correct` / `framework_gate_count` quantify over any
  such implementation. Continued-fraction recovery is implemented in the
  framework, while `MeasureClass` remains a framework-side assumption rather
  than a user field. All synthesis machinery
  (`ShorLoweringSetup`, `PhaseProduct`, `orderFindingApprox`, `lowerGate`) is
  pushed to the reference implementation (Phase 4), which builds a concrete
  `prog` and discharges the obligations from the existing proofs
  (`Shor_correct_approx_lowered_uniform`, `shorGateCountBound_of_programOK`) via
  an ε-from-precision packaging. Build green; `#print axioms` unchanged on both
  headline theorems; framework theorems are sorry-free.
- **Phase 4 — Implementations/Reference.** Move `Gate`, the subroutine
  constructions, and the Gate→LowGate compilation into `Reference/`;
  organize the subroutines by-subroutine with the Math/Correctness split;
  the existing theorems become instances via `Discharge.lean`.
- **Phase 5 — Framework/Checks + align with shor-challenges.** The
  `ShorImplementation` interface IS the challenge site's submission
  interface (a LowGate program + correctness + proved bound), so the two
  repos share one spec: a leaderboard submission and a ForShor
  implementation become the same object.

## Status
- Phase 0: done (PRs #5, #6 merged).
- Phases 1-2: done (PRs #8, #9, #10 merged).
- Phase 3: done (this PR). Field set signed off by the lead.
- Phases 4-5: pending, one PR at a time, lead-reviewed. Phase 3 was the one
  that needed sign-off on the `ShorImplementation` field set before it
  freezes.
