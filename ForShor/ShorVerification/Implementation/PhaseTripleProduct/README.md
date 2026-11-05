# PhaseTripleProduct

This folder builds the phase-triple-product circuit, which applies the phase `exp(i·π·φ·x·y·z)` to three registers `x`, `y` and `z`, and states what is to be proved about it. It is the three-operand analogue of `PhaseProduct`, and it is **not** used by the order-finding circuit: nothing in `Shor/`, `QFT/` or `ModularExponentiation/` imports it.

The circuit is a Toom-Cook recursion. Each operand is cut into `k` limbs, the product phase is rebuilt from `3k - 2` smaller phase triple products (the product of three degree-`k - 1` limb polynomials has degree `3 (k - 1)`) plus classical arithmetic, and the recursion bottoms out in a leaf that multiplies out bit by bit. Which table is used at each width comes from a banded policy, `PTPPolicy`; a single fixed table is the policy with one band.

## Status

**Phase 1 of the port: `Statement.lean` is in place; `Proofs/` and `Main.lean` are in progress.** Until `Main.lean` exists the claims below are stated but not yet proved in this repository. The proofs they correspond to are the PTP suite of the ShorTableOptimization interim fork (`TableGeneration/RecursiveCost/PTP/`), which is being moved here file by file.

## Files

- `Statement.lean` has the definitions (tables and policies, widths, the leaf and node circuits, the recursion, the census, the specification operators) and the statements of the claims as propositions. It imports only Mathlib, `Framework/` and `PhaseProduct/Statement.lean`, so you can check the claims against it alone. `scripts/StatementClosure.lean` checks that rule semantically: it computes every constant the claims reach and fails if one lives outside Mathlib/core, `Framework/` or a `Statement.lean`.
- `Proofs/` will hold all the lemmas. *(Phase 2.)*
- `Main.lean` will prove the final claims. *(Phase 2.)*

If you are new here, read `Main.lean` first once it exists to see what is proved, then `Statement.lean` for what the claims mean.

## The claims

Each is a `def … : Prop` in `Statement.lean`; `Main.lean` will prove it under the name in the last column. The "was" column is the theorem of the same content in the interim fork.

| Claim | In words | Proved as |
| --- | --- | --- |
| `PTPLowerExactCorrect` (with `PTPExactCensus`) | For a checked policy and three disjoint `n`-qubit registers there is a circuit following the policy at exact widths that acts as the PTP phase operator on every clean state, with an exact gate census and a qubit upper bound | `ptp_lowerExact_correct` |
| `PTPCtlLowerExactCorrect` | The same, controlled, by masking one operand | `ptp_ctl_lowerExact_correct` |
| `PTPPadLowerExactCorrect` | The same on operands of unequal widths, by sign-extension padding | `ptp_pad_lowerExact_correct` |
| `PTPGateTotalBound` | For a constant policy the census total is `O(n ^ log_k (3k − 2))` | `ptp_gateTotal_bound` |
| `PTPCircuitGateCountBound` | The constructed circuit has that many gates | `ptp_circuit_gateCount_bound` |
| `PTPQubitsTight`, `PTPQubitsTightExact`, `PTPQubitsLePtpQubits` | The circuit touches at most `3n + ptpWsTD` distinct qubits; `ptpQubits` is a proved upper bound at the scan rule | `ptp_qubits_tight`, `ptp_qubits_tight_exact`, `ptp_qubits_le_ptpQubits` |
| `PTPChainContractsTightIffReach` | The exact-width acceptance rule, stated without the ladder | `PTPPolicy.chainContractsTight_iff_reach` |

## Scope, read before citing

- The state-level claims cover the span of **clean** kets: the operands fit signed `n ≥ 1` bits and the workspace is `|0⟩`. For `n = 0` they are vacuous.
- Controlled PTP is built by **masking** one operand. ForShor's construction, which controls every leaf phase, is a different one and is not covered here.
- The gate-count claims are for a **constant policy** (one table at every width) and count `rz + toffoli + x + h + cnot` under `shorGateResourceModel`. They are not T counts.
- The qubit claims bound `LowGate.usedQubits`, the qubits the gates name. They are not the framework's `qubitCount`, which also adds the scratch `cleanAnc`.
- A table is admissible when it passes `PTPTable.contract`, a Boolean check: `3k − 2` distinct benchmark-valid points (`validPoint?`, signed powers of two and `∞`), the program consumes them in order, no `addScaled` adds a register to itself, and the program returns the registers to where they started.

## Relation to the Framework's table language

`Statement.lean` reuses `Framework/ToomCookTable.lean` for registers, states, points, `valid_ops`, `Prog`, `applyOp?`, `run?` and `expectedRow`. The Framework states admissibility as propositions (`ProgConsumesPts`, `SafeProg`); the PTP contract needs a decision procedure, so `Statement.lean` also defines the Boolean checkers `progConsumesPts?`, `safeProg?` and `returnsToStartCheck`. `Proofs/` will relate each to its propositional form.
