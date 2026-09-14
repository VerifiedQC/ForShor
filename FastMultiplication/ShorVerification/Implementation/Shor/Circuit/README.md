# `Circuit/`

The concrete Shor order-finding circuit and the static workspace budget it
needs. `Workspace.lean` and `OrderFinding.lean` are independent siblings
(neither imports the other).

## `Workspace.lean` — static reserve budgets

- **`ShorWorkspaceNeed`** — the reserve required on each of the four register
  families (`exponent`, `data`, `auxiliary`, `scratch`) to lower the whole
  circuit.
- **`qftReserveNeed`** — total reserve for lowering a QFT of a given width,
  summing the two `qftWorkspaceNeed` pools from `QFT/Lowering/Workspace.lean`.
- **`shorWorkspaceNeed`** — computes a `ShorWorkspaceNeed` from the circuit's
  four registers, taking the max of each register's per-step phase-product
  workspace needs (Steps 1, 2, 4, 5) and its own QFT-lowering need.
- **`ShorWorkspaceLargeEnough`** — the public precondition: each register's
  capacity meets the corresponding `shorWorkspaceNeed` field. This is what
  `Proofs/Readiness/Static.lean`'s `gateWorkspaceOK_orderFindingApprox`
  expands into per-stage `GateWorkspaceOK` facts.
- **`ShorWorkspaceIsolation`** — the exponent register's owned qubits are
  disjoint from the auxiliary register, from comparator scratch, and from
  the comparator flag qubit itself.

## `OrderFinding.lean` — the order-finding circuits

- **`initY1`** — initializes the data register's first qubit to `1` (an `X`
  gate, or `Gate.id` if the register is empty).
- **`orderFindingApprox`** — the approximate order-finding circuit: register
  Hadamard on the exponent register, `initY1`, the proved-valid modular
  exponentiation circuit (`modExpApproxValid`), then inverse QFT on the
  exponent register.
- **`orderFindingApproxLow`** — `orderFindingApprox` lowered to a `LowGate`
  via `lowerGate` (`Shor/Lowering/LowerGate.lean`), given a `GateWorkspaceOK`
  proof for it.
- **`orderFindingIdeal`** — the ideal order-finding circuit, swapping in the
  abstract exact modular-exponentiation gate (`modExpIdeal'`) in place of the
  approximate one; used by `Proofs/NaiveShor/` for the ideal-circuit analysis.
