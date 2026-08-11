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
  Math/                   -- PROGRAM-INDEPENDENT facts only (litmus: no Gate,
                             no LowGate program, no lowerGate):
                             order->factor, continued fractions, QFT phase
                             algebra, Toom-Cook interpolation, Master theorem,
                             success-probability math
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
- **Phase 2 — Framework/Math.** Lift the program-independent mathematics
  out (litmus test: no `Gate`/`LowGate`/`lowerGate`).
- **Phase 3 — Framework/Spec (the load-bearing generalization).** Define
  `ShorImplementation` over `LowGate`, and restate the two headline
  theorems as framework theorems quantified over it. This is where the
  design decisions concentrate (the obligation field set) — needs review.
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
- Phases 1-5: pending, one PR at a time, lead-reviewed. Phase 3 is the one
  that needs your sign-off on the `ShorImplementation` field set before it
  freezes.
