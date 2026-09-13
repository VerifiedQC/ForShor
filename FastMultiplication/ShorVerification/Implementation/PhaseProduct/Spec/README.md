# `Spec/`

The public specification surface: the predicates that state what "the
workspace is clean enough to run" and "the lowered circuit behaves correctly"
mean, and the final named claims proved in `Main.lean`.

## `Cleanliness.lean`

- **`CompilerWorkspaceOK`**, **`CleanWorkspaceState`** — the concrete
  precondition for running one level's allocation gates: the layout can grow
  to the scanned target width, and the bits that growth would touch are
  currently zero. `CleanWorkspaceState` is the linear closure (`CleanClosure`)
  of that basis-level predicate, so it applies to arbitrary quantum states.
- **`LayoutReserveCleanBasis`/`.CleanState`** — a basis state has zeroes in
  every reserve bit a layout owns (its full future growth capacity, not just
  the current level's need).
- **`RecursiveWorkspaceCleanBasis`/`.CleanState`** — the same idea at the
  top level: both operands' *complete* reserve registers are zero.
- **`SignedRecursiveWorkspaceStateOK`** / **`CSignedRecursiveWorkspaceStateOK`**
  — the full public workspace precondition combining the static capacity
  facts (`Compiler.Workspace`'s `SignedRecursiveWorkspaceOK`/
  `CSignedRecursiveWorkspaceOK`) with this state-level cleanliness.

## `Readiness.lean`

- **`PhaseLoweringReady`** — the semantic precondition for executing a
  `PhaseLoweringPlan` on a given state: primitive gates need nothing;
  recursive nodes require the workspace to be clean *and* the child plan to
  be ready on the state reached after the current level runs. `QFT/Spec/Readiness.lean`
  needs this definition directly, to define its own `QFTLoweringReady`.

## `Assertions.lean`

- **`LowerSignedPhaseProductCorrect`** — the headline claim: for any state
  with a valid, clean recursive workspace (and the source program's
  interpolation-safety side conditions), the canonical lowered circuit
  evaluates exactly like the high-level `Gate.SignedPhaseProd`.
- **`LowerCSignedPhaseProductCorrect`** — the same claim for the controlled
  gate. Both are proved in `Main.lean`.
