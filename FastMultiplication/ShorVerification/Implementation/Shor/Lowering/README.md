# `Lowering/`

The whole-`Gate` lowerer: the one place that knows about all three subroutine
lowerers at once and dispatches a source `Gate` to its `LowGate` translation.
It imports from `QFT/`, `PhaseProduct/`, and `ModularExponentiation/` and
nothing from `Shor/`.

## `LowerGate.lean`

- **`GateWorkspaceOK`** — the static reserve precondition, recursive on
  `Gate`: a QFT register has enough inactive reserve for its two workspace
  pools, a signed phase product has enough mutually disjoint reserve for its
  complete recursion, a controlled signed phase product additionally keeps
  its control qubit outside both operands' owned regions, and sequential
  composition/adjoint recurse structurally. The remaining constructors need
  no reserve.
- **`lowerGate`** — the whole-`Gate` → `LowGate` compiler, dispatching by
  constructor:
  - `QFT ↦ lowerQFT`
  - `SignedPhaseProd ↦ lowerSignedPhaseProdWithWorkspace`
  - `CSignedPhaseProd ↦ lowerCSignedPhaseProdWithWorkspace`
  - `CmpGeConst ↦ lowerCmpGeConst`
  - `CSubConst ↦ lowerCSubConst`
  - every other constructor ↦ its `LowGate` twin

  The controlled signed-phase-product branch currently uses the naive
  controlled leaf. The phase-product layer has a controlled plan-directed
  lowerer, but it does not yet have the analogue of
  `standardSignedPhaseLoweringPlan` which constructs that plan solely from
  `CSignedRecursiveWorkspaceOK`. Once that constructor is added, only this
  branch needs to change.
- **`GateWorkspaceCleanState`** — the dynamic clean-state precondition,
  noncomputable, defined by recursion through `lowerGate`: runtime
  cleanliness required before evaluating each recursively lowered node.
