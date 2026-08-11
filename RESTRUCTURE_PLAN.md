# ForShor restructuring plan

Goal (from the project lead, first-principles): opening any file should
give you the natural mental model — **spec + def + proof** — and the
reading path should mirror the *conceptual* architecture, not the order
proofs happened to be written. Each Shor subroutine should be a
self-contained spec/def/proof unit; the abstract machine its own clean
layer; and semantic machinery (e.g. the measurement interface) should be
introduced, with motivation, in a foundations layer — never dumped on the
reader mid-proof.

This is a staged, low-risk campaign. **Invariant for every PR**: `lake
build` green, and `#print axioms` unchanged on `Shor.Shor_correct` and
`Shor.exists_shorGateCountBound` (no new axioms; the one pre-existing
`sorry` untouched). No statement or proof is altered except where a phase
explicitly merges duplicate definitions (verified by the same two gates).

## Target skeleton (by-subroutine, approved direction)

```
Foundations/
  QuantumSemantics.lean   -- QSemantics + MeasureClass + RegEncoding,
                             with a first-principles docstring: what a
                             quantum computation IS, and why measurement
                             (Born rule / probabilities) needs its own
                             interface. MeasureClass moves here from
                             ShorCorrectness.lean.
  Gates.lean              -- gate syntax, workspace records, gate macros
  SemanticLemmas.lean     -- reusable sum/encoding/isometry/freshness facts
Subroutines/
  ModExp/       { Math, Spec, Def, Correctness }
  QFT/          { Math, Spec, Def, Correctness }
  PhaseProduct/ { Math, Spec, Def, Correctness }
  TableGen/     (already Core/Builders/Programs from the earlier reorg)

Each subroutine's mathematics is split into two layers that are handled
separately (lead directive):
  Math.lean         -- PROGRAM-INDEPENDENT facts: ℕ/ℤ/ℂ/matrices and
                       abstract theorems only (Toom-Cook interpolation,
                       Master theorem, QFT phase algebra, continued-fraction
                       recovery, order->factor reduction, success-probability
                       math). LITMUS TEST: this file may NOT mention `Prog`,
                       `Gate`, `lowerGate`, or `QSemantics.eval` on a concrete
                       circuit. If it does, that content is program-dependent
                       and belongs in Correctness.lean.
  Correctness.lean  -- PROGRAM-DEPENDENT: imports Math, attaches the abstract
                       facts to the concrete def/circuit (def |= spec). This
                       is the only place Prog/lowering appear.
The top-level Shor correctness splits the same way: the classical/
number-theoretic core (order-found => factor, CF recovery, probability
bound) is program-independent; the circuit-meets-spec part is
program-dependent.
AbstractMachine/
  LowGate.lean            -- the machine + cost model
  Lowering.lean           -- lowering semantics (was *LoweringCorrectness)
Shor/
  Spec.lean / Def.lean / Correctness.lean  -- top level, composes subroutines
```

Current layout splits by LAYER (AlgorithmCorrectness/* vs
AbstractMachine/*), so "everything about QFT" is in two places. The
approved change is to regroup by SUBROUTINE.

## Phases (each = one or more verified PRs)

### Phase 0 — necessity / dedup (shrink the definition surface first)
So we never carry redundancy into the new structure. From the audit:
0a. `CarryShorWorkspaceCleanState` (Workspace/Shor.lean:187) is
    byte-identical to `ShorLoweringCleanState` (:205) and used once —
    merge. **[first PR, cheapest]**
0b. The 6-way `*CleanState` clone (QFT/PhaseProduct/Layout/ThreeRegs/
    Recursive/QFTWorkspace) — introduce one generic
    `CleanState (P : Basis → Prop)` and instantiate. Highest structural
    value; its own PR.
0c. Two `Point` types (Operations.Point / ToomCookMath.Point) + the
    `toMathPoint` bridge — pick one, delete the bridge.
0d. Consolidate the three `ThreeRegsCleanState` aliases.
NOTE: `MeasureClass` is NOT a duplicate (one def, ~125 uses) — it is
canonical; it moves in Phase 1, it is not deleted. The `Plan` types are
distinct per pipeline — a naming/discoverability fix, not a merge.

### Phase 1 — Foundations layer
Create Foundations/, move QSemantics/RegEncoding/gates/semantic lemmas out
of the 1694-line Basic.lean, and relocate MeasureClass next to QSemantics
with the motivating docstring. Split Basic.lean along its existing
"Section N" banners.

### Phase 2..N — one subroutine at a time
Per subroutine: gather its math-level and lowering material under
Subroutines/<name>/, split into Spec/Def/Correctness, add a chapter
docstring. Order: ModExp, QFT, PhaseProduct (leave TableGen — already
restructured). Then the AbstractMachine layer, then the Shor/ top level.

### Phase final — STYLE.md + reading guides
Codify the Foundations/Subroutines/AbstractMachine/Shor convention and the
per-file Defs-first rule; add a top-level reading guide.

## Status
- Phase 0a: in this PR.
- Everything else: pending, one PR at a time, lead-reviewed.
