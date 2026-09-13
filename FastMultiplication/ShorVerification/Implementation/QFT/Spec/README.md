# `Spec/`

The public specification surface: the predicates that state what "the QFT
workspace is clean enough to run" and "the lowered circuit behaves correctly"
mean, and the final named claim proved in `Main.lean`.

## `Cleanliness.lean`

- **`Gate.PhaseProdWorkspace.CleanState`** — the linear subspace (`CleanClosure`)
  in which both physical workspace qubits of the unsigned phase-product macro
  used at a split node are clean. Lives here (rather than in `PhaseProduct/`)
  because every user of it is a QFT file.
- **`QFTWorkspaceCleanState`** — the linear subspace in which both portions
  (`xWork`, `zWork`) of the inactive QFT register selected by the concrete
  lowering are zero.
- **`QFTWorkspaceStateOK`** — the public state-level precondition for
  concrete QFT lowering: the inactive part of the supplied `ExtReg` is large
  enough (`QFTReserveOK`, `Workspace.lean`) and the two slices the lowering
  selects are initially zero (`QFTWorkspaceCleanState`).

## `Readiness.lean`

- **`QFTLoweringReady`** — the semantic precondition for executing a
  `QFTLoweringPlan` on a given state: base cases need nothing; a split node
  requires the phase-product macro workspace to be clean, the right child's
  plan to be ready, the phase-product subplan to be ready on the state
  reached after the right child runs, and the left child's plan to be ready
  on the state reached after the phase macro runs.

## `Assertions.lean`

- **`LowerQFTCorrect`** — the headline claim: for any state with a valid,
  clean recursive workspace (and the source program's interpolation-safety
  side conditions), the canonical lowered QFT circuit (`lowerQFT`) evaluates
  exactly like the high-level `Gate.QFT`. Proved in `Main.lean`.
