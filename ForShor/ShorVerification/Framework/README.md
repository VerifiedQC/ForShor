# `Framework/`

The trusted base. Everything in [`Implementation/`](../Implementation),
[`Submission/`](../Submission) and [`Emit/`](../../Emit) is proved against,
or built from, the definitions here, and nothing here imports any of them.
A reader who wants to know *what* the development proves, as opposed to
*how*, reads this folder together with the two Shor-specific files that state
the correctness criterion over it:
[`Implementation/Shor/Math/ShorDefinition.lean`](../Implementation/Shor/Math/ShorDefinition.lean)
(the classical side of order finding) and
[`Implementation/Shor/Statement.lean`](../Implementation/Shor/Statement.lean)
(`probability_of_success`) and
[`Implementation/Shor/Interface.lean`](../Implementation/Shor/Interface.lean)
(`ShorImplementation`).

Files import only Mathlib and other `Framework/` files.
`ToomCookTable.lean` imports Mathlib and nothing else, and `Policy.lean`
imports only `ToomCookTable.lean`, so the rules a submission must meet can be
read without the rest of the framework.

## The trust boundary

The theorems are stated over abstract typeclasses rather than a fixed
encoding of states and gates: a `QSemantics` (a state space with kets), a
`RegEncoding` on its basis, a `MeasureClass`, the gate laws bundled as
`GateSemanticsFacts`, and `LowerGateClass` for the lowered language. The
proofs use only the laws these classes state. [`Model/Standard/`](../Model/Standard)
instantiates every class with the standard matrix model and checks that the
headline theorems specialise to it, so the laws are satisfiable by ordinary
unitaries. Reading this folder therefore answers two questions: which
statements are assumed (the class laws and the cost model), and which are
proved elsewhere (everything stated in terms of them).

## Files

| file | what it defines |
|---|---|
| `Quantum/Registers.lean` | `Reg` (an ordered list of distinct physical qubits) and its splits (`splitLeft`/`splitRight`, and the halves `leftReg`/`rightReg` at `halfSplitPoint`, with their sizes), `RegEncoding` (the basis-level read/write interface: `toNat`, `writeNat`, `bit`, and their laws), `ExtReg` (an active register plus an owned inactive reserve), the two's-complement decodings (`tcDecodeWidth`, `extToInt`, `FitsSignedWidth`) and the freshness predicates (`FreshZero`, `ExtReg.FreshFor`) |
| `Quantum/QSemantics.lean` | `QSemantics`: a normed inner-product state space with `ket`, finite-combination induction, and ket orthonormality |
| `Quantum/Measurement.lean` | `MeasureClass`: the Born-rule projectors for measuring a register, and `probMeas` |
| `AbstractMachine/Angle.lean` | `Angle`, a rational multiple of π, and `Angle.toReal` |
| `AbstractMachine/Gates.lean` | `Gate`, the high-level circuit language (QFT, signed and controlled phase products, shifts, negation, scaled addition, comparison and subtraction by a constant, the ideal modular multiplier), and the QFT phase `ω`/`qftPhase` |
| `AbstractMachine/LowGate.lean` | `LowGate`, the lowered language: H, X, Phase, CNOT, Toffoli, the reversible arithmetic primitives, register extension and deallocation, radix reversal |
| `Semantics/GateSemantics.lean` | The gate laws, one class per gate family, bundled as `GateSemanticsFacts`: the action of every `Gate` on a basis ket, stated through total basis maps (`negateBasis`, `addScaledBasis`, `shiftLBasis`, …) |
| `Semantics/LowGateSemantics.lean` | `LowerGateClass`: the same for `LowGate`, over `evalL` |

Notation: `⟦U⟧ ψ` is `qs.eval U ψ` (a `Gate` applied to a state) and `⟦L⟧ₗ ψ` is `LowerGateClass.evalL L ψ` (a `LowGate` applied to a state); `qs` is inferred from `ψ`, and goals print in this form.
| `Gatecount/CostModel.lean` | `LowGateCostModel` and `gateCount`: how a lowered circuit is priced |
| `Gatecount/ResourceModel.lean` | `shorGateResourceModel`, the concrete charges (Cuccaro adders for scaled addition and negation, wiring conventions for shifts and radix reversal) and the proof-side bounds the asymptotic theorems use |
| `ToomCookTable.lean` | What a submitted table is and when it is admissible: `Point`, `valid_ops`, `Prog`, the symbolic `State`, `run?`, and the conditions C1–C4 (`q`, `GoodToomCookPoints`, `ProgConsumesPtsSafe`), bundled as `ShorLoweringSetup` / `ShorSubmission` |
| `Policy.lean` | What a submitted policy is: `ToomCookTable` (a table's data), `ShorLoweringPolicy` (width-indexed bands, `choose`, `Stops`), `Admissible`, `constPolicy`, and `ShorPolicySubmission` with its `sorted` field |

## Where the headline statements are

The theorems themselves live in `Implementation/` and `Submission/`; this
folder only states the vocabulary they are about. The correctness criterion is
`probability_of_success` in `Implementation/Shor/Statement.lean`; the gate-count function the
asymptotic bounds are stated with is `ShorOrderFindingProgram.frameworkGateCount`;
the admissibility conditions a submission must satisfy are the four fields
of `ShorLoweringSetup` and the `sorted` field of `ShorPolicySubmission`.
