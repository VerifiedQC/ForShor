# PhaseTripleProduct

This folder builds the phase-triple-product circuit, which applies the phase `exp(i·π·φ·x·y·z)` to three registers `x`, `y` and `z`, and proves it correct. It is the three-operand analogue of `PhaseProduct`, and it is **not** used by the order-finding circuit: nothing in `Shor/`, `QFT/` or `ModularExponentiation/` imports it.

The circuit is a Toom-Cook recursion. Each operand is cut into `k` limbs, the product phase is rebuilt from `3k - 2` smaller phase triple products (the product of three degree-`k - 1` limb polynomials has degree `3 (k - 1)`) plus classical arithmetic, and the recursion bottoms out in a leaf that multiplies out bit by bit. Which table is used at each width comes from a banded policy, `PTPPolicy`; a single fixed table is the policy with one band.

## Files

- `Statement.lean` has the definitions (tables and policies, widths, the leaf and node circuits, the recursion, the census, the specification operators) and the statements of the claims as propositions. It imports only Mathlib, `Framework/` and `PhaseProduct/Statement.lean`, so you can check the claims against it alone. `scripts/StatementClosure.lean` checks that rule semantically: it computes every constant the claims reach and fails if one lives outside Mathlib/core, `Framework/` or a `Statement.lean`. CI runs it.
- `Proofs/` has all the lemmas:
  - `Support/`: the table-language lemmas, and the bridges between the Boolean checkers in the Statement and the Framework's propositions.
  - `Table/`, `Values/`: the table contract and width scan; the node identity and exact widths.
  - `Gates/`, `Recursion/`, `ExactBoard/`: the leaf and node circuits, and the gate-level recursion at the conservative scan widths and at exact widths.
  - `Surface.lean`, `Threshold.lean`, `Controlled.lean`, `Unbalanced.lean`, `Asymptotic.lean`, `QubitsTight.lean`: the state-level lemmas, the acceptance rule and the extensions. The final theorem of each extension carries a `_core` suffix here; `Main.lean` re-states it under the claim's name.
  - `Witness/`: negative controls and non-vacuity (see below).
- `Main.lean` proves the claims.

If you are new here, read `Main.lean` first to see what is proved, then `Statement.lean` for what the claims mean. `Model/Standard/PhaseTripleProductHeadline.lean` specialises the two state-level claims to ForShor's concrete model `Model.qs`.

## The claims

Each is a `def … : Prop` in `Statement.lean`; `Main.lean` proves it under the name in the last column.

| Claim | In words | Proved as |
| --- | --- | --- |
| `PTPLowerExactCorrect` (with `PTPExactCensus`) | For a checked policy and three disjoint `n`-qubit registers there is a circuit following the policy at exact widths that acts as the PTP phase operator on every clean state, with an exact gate census and a qubit upper bound | `ptp_lowerExact_correct` |
| `PTPCtlLowerExactCorrect` | The same, controlled, by masking one operand | `ptp_ctl_lowerExact_correct` |
| `PTPPadLowerExactCorrect` | The same on operands of unequal widths, by sign-extension padding | `ptp_pad_lowerExact_correct` |
| `PTPGateTotalBound` | For a constant policy, under either negation method, the census total is `O(n ^ log_k (3k − 2))` | `ptp_gateTotal_bound` |
| `PTPCircuitGateCountBound` | For a constant policy, under either negation method, there is a circuit following it with at most that many gates | `ptp_circuit_gateCount_bound` |
| `PTPQubitsTight`, `PTPQubitsTightExact`, `PTPQubitsLePtpQubits` | There is a circuit following the policy touching at most `3n + ptpWsTD` distinct qubits; `ptpQubits` is a proved upper bound at the scan rule | `ptp_qubits_tight`, `ptp_qubits_tight_exact`, `ptp_qubits_le_ptpQubits` |
| `PTPChainContractsTightIffReach` | The exact-width acceptance rule, stated without the ladder | `ptp_chainContractsTight_iff_reach` |

## Scope, read before citing

- The state-level claims cover the span of **clean** kets: the operands fit signed `n ≥ 1` bits and the workspace is `|0⟩`. For `n = 0` no basis ket is clean, so the state-level conjunct is vacuous (the circuit, the workspace bound and the census are still required).
- **The gate-count and qubit claims are existential.** Each says that *some* circuit following the policy has that count. None of them says it is the circuit of `PTPLowerExactCorrect`, or that it is correct; correctness and the census are separately proved for every circuit of the form `PolicyImplX`, but no single claim bundles the two.
- Controlled PTP is built by **masking** one operand. ForShor's construction, which controls every leaf phase, is a different one and is not covered here.
- The gate-count claims are for a **constant policy** (one table at every width), for **either negation method** (next section), and count `rz + toffoli + x + h + cnot` under the policy's own resource model `PTPPolicy.resourceModel` (`shorGateResourceModel` for the default method). They are not T counts.
- The qubit claims bound `LowGate.usedQubits`, the qubits the gates name. They are not the framework's `qubitCount`, which also adds the scratch `cleanAnc` (bounded separately, see the next section).
- A table is admissible when it passes `PTPTable.contract`, a Boolean check: `3k − 2` distinct benchmark-valid points (`validPoint?`, signed powers of two and `∞`), the program consumes them in order, no `addScaled` adds a register to itself, and the program returns the registers to where they started. The "benchmark-valid" restriction is the benchmark's rule, not something the mathematics needs.

## The negation method

A table's `negate` operation is realised by one of two circuits, and a policy chooses which: `PTPPolicy.negation : NegationMethod` (default `oneQubit`; `PTPPolicy.withNegation` changes it). The gate `LowGate.Negate` and its meaning are the same for both, so correctness is unaffected; only the resource charge differs, and `PTPPolicy.resourceModel P = shorGateResourceModelFor P.negation` is the model the policy is costed with. Every census the policy-level definitions compute (`ptpResources`, `ptpCnotFull`, `ptpResourcesD`, `ptpCnotFullD`, `ptpGateTotalD`, `ptpCleanAnc`, `ptpCleanAncD`, `ptpQubits`) reads `P.negation`, and every gate-level theorem is stated for `P.resourceModel`.

| | `oneQubit` (default) | `scratch` |
| --- | --- | --- |
| Construction | complement, then Gidney's single-ancilla increment | complement, then a Cuccaro adder against a clean constant-one register as wide as the register |
| Toffoli | `12 w - 28` (`w` even), `10 w - 18` (`w` odd) | `2 w - 3` |
| CNOT | `17 w - 22` / `17 w - 5` | `5 w - 7` |
| X | `5 w - 3` / `5 w + 1` | `w + (2 w - 6) + 2 = 3 w - 4` (for `w ≥ 3`) |
| Clean scratch held while it runs | `1` | `w + 1` |

(`w` is the width of the register negated; the closed forms are `negateXGatesFor`, `negateCnotGatesFor`, `negateToffoliGatesFor` and `negateCleanAncFor` in `Statement.lean`, and `negateResourcesFor_eq` ties them to the Framework's `negateResourcesFor`.) An addition is charged the same under both methods: the Cuccaro adder, with one clean qubit for its carry.

`ptpCleanAnc P n` is the peak number of clean scratch qubits the model holds at once along the ladder, per node: none if the table neither adds nor negates, one if it only adds, and `negateCleanAncFor P.negation C` (one for `oneQubit`, `C + 1` for `scratch`, `C` the node's working width) if it negates; the sandwich leaves hold none, their two ancillas being explicit qubits. `PolicyImplD.cleanAnc_le` proves it is an upper bound on the `cleanAnc` of every gate-level recursion following `P`. For `scratch` every census equals the one before the one-qubit negation was introduced (`nodeCensusFor_scratch`: for instance `CNOT = 3 (A + N)(5 C - 7)`); `oneQubit` keeps the census of the one-qubit negation; its `ptpCleanAnc` is now the tight `1` (the previous definition was the looser bound `C + 1`, a valid but no longer tight bound), so `max (ptpCleanAnc) 2` in `ptpQubits` is `2` for it.

## Witnesses

`Proofs/Witness/` holds executable evidence that the hypotheses are satisfiable and that the side conditions matter. `FaultChallenge` shows the contract rejects a table whose points are declared in the wrong order, and that evaluating it anyway gives the wrong value; and that wrapping the registers one bit below the width scan breaks the node. `RecursionWitness` builds a concrete depth-one recursion on three 20-qubit registers. `ExactFault` shows that one bit below the exact width the gate-level circuit is wrong on a concrete state.

## Relation to the Framework's table language

`Statement.lean` reuses `Framework/ToomCookTable.lean` for registers, states, points, `valid_ops`, `Prog`, `applyOp?`, `run?` and `expectedRow`. The Framework states admissibility as propositions (`ProgConsumesPts`, `SafeProg`); the PTP contract needs a decision procedure, so `Statement.lean` also defines the Boolean checkers `progConsumesPts?`, `safeProg?` and `returnsToStartCheck`. `Proofs/Support/Language.lean` relates each to its propositional form (`checkedProg_iff_framework`, `contract_iff_framework`).

## Provenance

This development was ported from the PTP verification suite of an interim fork of ShorTableOptimization (`TableGeneration/RecursiveCost/PTP/`, commit `11fd68b`), onto this repository's table language. Theorem names are as in that suite, except that the seven final theorems of the extensions are named in `Main.lean` and carry a `_core` suffix in `Proofs/`. Statements of the first three claims are verbatim copies; the others were rewritten from theorem statements into propositions with their hypotheses as implications, and an independent line-by-line review found no difference in meaning.
