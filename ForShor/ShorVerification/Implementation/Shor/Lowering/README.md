# `Lowering/`

The whole-`Gate` lowerer: the one place that knows about all three subroutine
lowerers at once and dispatches a source `Gate` to its `LowGate` translation.
It imports from `QFT/`, `PhaseProduct/`, and `ModularExponentiation/` and
nothing from `Shor/`.

## `LowerGate.lean`

Each of the three objects below is defined twice: over a `ShorLoweringPolicy`
(the `Policy.*` names, which `Circuit/OrderFinding.lean` and the theorems in
`Main.lean` use) and over a single fixed table (the unprefixed names, the
constant-policy instance that `GateCount/` and `Emit/` are stated with).
`Policy.gateWorkspaceOK_const_iff` relates the two.

- **`Policy.GateWorkspaceOK P`** / **`GateWorkspaceOK ops`** — the static
  reserve precondition, recursive on
  `Gate`: a QFT register has enough inactive reserve for its two workspace
  pools, a signed phase product has enough mutually disjoint reserve for its
  complete recursion, a controlled signed phase product additionally keeps
  its control qubit outside both operands' owned regions, and sequential
  composition/adjoint recurse structurally. The remaining constructors need
  no reserve.
- **`Policy.lowerGate P`** / **`lowerGate`** — the whole-`Gate` → `LowGate`
  compiler, dispatching by constructor (fixed-table target in parentheses):
  - `QFT ↦ Policy.lowerQFT` (`lowerQFT`)
  - `SignedPhaseProd ↦ Policy.lowerSignedPhaseProd` (`lowerSignedPhaseProdWithWorkspace`)
  - `CSignedPhaseProd ↦ Policy.lowerCSignedPhaseProd` (`lowerCSignedPhaseProdWithWorkspace`)
  - `CmpGeConst ↦ lowerCmpGeConst`
  - `CSubConst ↦ lowerCSubConst`
  - every other constructor ↦ its `LowGate` twin
- **`Policy.GateWorkspaceCleanState`** / **`GateWorkspaceCleanState`** — the
  dynamic clean-state precondition, noncomputable, defined by recursion
  through the lowerer: runtime cleanliness required before evaluating each
  recursively lowered node.
