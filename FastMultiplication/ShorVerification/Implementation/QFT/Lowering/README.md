# `Lowering/`

Turns a recursive QFT split into a finite, structurally-checked *plan* for
lowering it to primitive `LowGate`s, and provides the public entry points
that build such a plan automatically from a workspace assumption.

## `Plan.lean`

- **`QFTLoweringPlan k hk ops r`** — an inductive, finite certificate that a
  QFT on register `r` can be lowered: `empty`/`singleton` base cases for
  registers of size 0/1, and a `split` case carrying the phase-product
  workspace `ws`, an explicit subplan for the unsigned phase-product macro
  between the two halves (`StandardPhaseLoweringPlan`), and a child
  `QFTLoweringPlan` for each half.
- **`lowerQFTPlan`** — the interpreter: erases a plan's proof data and
  returns the `LowGate` it certifies (structural recursion on the plan) —
  right half, then the phase macro, then the left half, then a radix
  reversal.

## `PlanBuilders.lean`

- **`phaseProdUsingInputSize`** / **`standardPhaseProdUsingPlan`** — the
  canonical lowering plan for one split's unsigned phase-product macro,
  built by zero-extending both operands by one qubit, lowering the resulting
  *signed* phase product via `standardSignedPhaseLoweringPlan`, then
  deallocating both extensions.
- **`standardQFTLoweringPlan`** — the canonical planner: given explicit
  x-side/z-side workspace registers satisfying `QFTWorkspaceOK`, recursively
  chooses the empty/singleton base case or a split node (reusing the same two
  pools for both recursive children, via `QFTWorkspaceOK.left`/`.right`).
- **`reserveQFTLoweringPlan`** — the bridge from the public reserve
  precondition `QFTReserveOK` to a concrete plan: derives the two workspace
  registers from `qftXWork`/`qftZWork` and calls `standardQFTLoweringPlan`.
- **`lowerQFT`** — the public top-level constructor: builds the canonical
  reserve-backed plan via `reserveQFTLoweringPlan` and lowers it with
  `lowerQFTPlan`. Its workspace is selected deterministically from the
  reserve precondition; callers do not supply separate physical workspace
  registers. This is the function `Spec/Assertions.lean`'s claim is about,
  and what `Shor/Defs.lean` imports to get a lowered QFT circuit.
