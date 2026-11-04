# Framework

This folder is the vocabulary everything else is written in: what a register is, what a circuit is, what it means to run one, how gates are counted, and what a submitted Toom-Cook table is. It defines things and states laws; it proves no theorem about Shor's algorithm. Everything in `Implementation/`, `Submission/` and `Emit/` is built on it, and nothing here imports any of them.

If you want to know *what* the development proves rather than *how*, read this folder, then `Implementation/Shor/Statement.lean` for the success probability and `Implementation/Reference/Contract.lean` for what a finished implementation has to provide.

## What is assumed

The theorems are not stated about one fixed matrix model. They are stated over a few typeclasses: a state space with kets (`QSemantics`), a way to read and write registers in the basis (`RegEncoding`), measurement (`MeasureClass`), and the laws each gate obeys (`GateSemanticsFacts` for the circuit language, `LowerGateClass` for the lowered one). The proofs use only these laws. `Model/` then instantiates every class with the ordinary matrix model and checks that the main theorems specialise to it, which shows the laws are satisfiable.

So the trust boundary is: the class laws, and the cost model. Everything stated in terms of them is proved.

## The files

**`Quantum/`** — registers and states.
- `Registers.lean`: `Reg`, an ordered list of distinct qubits; `ExtReg`, a register plus the spare qubits it owns; `RegEncoding`, reading and writing a register's value in a basis state; two's-complement decoding; what it means for spare qubits to be clean.
- `QSemantics.lean`: `QSemantics`, the state space, with kets and finite linear combinations.
- `Measurement.lean`: `MeasureClass`, the Born-rule projectors and the probability of a measurement outcome.

**`AbstractMachine/`** — the two circuit languages.
- `Angle.lean`: `Angle`, a rational multiple of π.
- `Gates.lean`: `Gate`, the high-level language the construction is written in: QFT, phase products, shifts, negation, scaled addition, comparison and subtraction by a constant.
- `LowGate.lean`: `LowGate`, the lowered language the circuit is counted in: H, X, phase, CNOT, Toffoli, the reversible arithmetic primitives, register extension and deallocation.

**`Semantics/`** — what the gates do.
- `GateSemantics.lean`: the laws of each `Gate` on a basis ket, bundled as `GateSemanticsFacts`.
- `LowGateSemantics.lean`: the same for `LowGate`, as `LowerGateClass`.

`⟦U⟧ ψ` is a `Gate` applied to a state and `⟦L⟧ₗ ψ` a `LowGate` applied to a state; goals print in this form.

**`Gatecount/`** — how a lowered circuit is priced.
- `CostModel.lean`: `LowGateCostModel` and `gateCount`.
- `ResourceModel.lean`: `shorGateResourceModel`, the concrete charges (Cuccaro adders for addition and negation, wiring for shifts and radix reversal), and the per-gate bounds the asymptotic theorems use.

**`ToomCookTable.lean`** — what a submission is: a Toom-Cook table (an arithmetic program over limb registers and the interpolation points it evaluates at) and the four decidable conditions C1–C4 under which it is admissible, bundled as `ShorSubmission`. It imports only Mathlib, so the rules a submission must meet can be read on their own.

**`Policy.lean`** — a policy, which is a list of tables indexed by operand width (`ShorLoweringPolicy`), when it is admissible, and `ShorPolicySubmission`. A single table is the one-band policy. It imports only `ToomCookTable.lean`.
