# `Lowering/`

The recursive workspace budget model, and turning a recursive QFT split into
a finite, structurally-checked *plan* for lowering it to primitive
`LowGate`s, with public entry points that build such a plan automatically
from a reserve-workspace assumption. `Workspace.lean` and `Plan.lean` are
independent siblings (both depend only on `Split.lean`); `PlanBuilders.lean`
builds on both.

## `Workspace.lean`

- **`qftWorkspaceNeed`** — recursively computes how large the two global
  reserve pools (x-side and z-side) must be for a register of a given width,
  accounting for the middle phase product and both recursive QFT calls at
  every level.
- **`qftXWork`** / **`qftZWork`** — the two concrete slices of an `ExtReg`'s
  inactive register assigned to those pools (a `take`/`drop` split).
- **`QFTReserveOK`** — the public precondition: the inactive part of the
  supplied register is large enough to hold both pools.
- **`QFTWorkspaceOK`** — the internal static condition on an already-selected
  pair of workspace registers (disjoint from the data register, disjoint from
  each other, and each large enough), derived from `QFTReserveOK` by
  **`QFTReserveOK.explicitWorkspace`**.
- **`QFTWorkspaceOK.phaseWorkspace`** — constructs the concrete unsigned
  phase-product workspace (`Gate.PhaseProdWorkspace`) needed at the current
  split node from the two root pools; **`.signedWorkspaceOK`** shows that
  workspace is also large enough for the *signed* phase-product lowering.
- **`QFTWorkspaceOK.left`** / **`.right`** — the same root workspace condition
  remains valid, unchanged, for the left/right recursive QFT calls (both
  reuse the same two pools).

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
