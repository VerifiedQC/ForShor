# Framework

This directory defines the shared mathematical model and public contract for
verified Shor order-finding implementations. It describes registers, quantum
states, measurement, low-level circuits, gate costs, classical postprocessing,
and the conditions an implementation must prove. It is primarily a
specification and interface, not a concrete quantum simulator.

When reading the framework, keep four questions in mind:

1. How are qubits arranged, and how are classical values stored in them?
2. How are basis configurations represented as quantum states and measured?
3. What do low-level circuit operations mean, and how is their cost counted?
4. What must an implementation prove to satisfy the framework?

## Directory Overview

- `Quantum/` defines registers, basis-state encodings, abstract quantum states,
  and measurement.
- `AbstractMachine/` defines circuit syntax. `LowGate` is the language exposed
  by the framework; `Gate` is a richer language used by the reference
  implementation.
- `Semantics/` states how circuit syntax acts on quantum states and basis
  configurations.
- `Gatecount/` defines the cost model and gate-counting function.
- `Math/` contains the mathematical definition of order finding, classical
  postprocessing, and the reduction from factoring to order finding.
- `Submission.lean` combines these pieces into the contract that a verified
  implementation must satisfy.

## Recommended Reading Order

The following is a suggested learning order rather than an import or dependency
order.

1. `Quantum/Registers.lean`
   Learn `Reg`, `RegEncoding`, and `ExtReg`. A register describes where data is
   stored; it is not itself a quantum state.

2. `Quantum/QSemantics.lean`
   Introduces the abstract basis and state spaces, the `ket` embedding, and the
   main state-level proof principle.

3. `Quantum/Measurement.lean`
   Defines measurement projectors and the probability of an outcome.

4. `AbstractMachine/LowGate.lean`
   Defines the low-level circuit operations accepted by the framework.

5. `Semantics/LowerGate.lean`
   States the laws that give `LowGate` programs their meaning. Treat the class
   fields as obligations for an evaluator rather than implementations of the
   gates.

6. `Gatecount/CostModel.lean`
   Explains how a `LowGate` program is assigned a concrete gate cost.

7. `Math/ShorDefinition.lean`
   Defines order, valid measurement outcomes, continued-fraction
   postprocessing, and the final order-finding result.

8. `Submission.lean`
   Read this last. `ShorImplementation` ties together a program, its correctness
   proof, its reported gate bound, and proof that the bound is respected.

On a first pass, focus on definitions, class fields, and theorem statements.
Most proof bodies and collections of derived lemmas can be skipped until a
specific fact is needed.

## Optional Paths

To understand the reference circuit construction, read
`AbstractMachine/Gates.lean` and `Semantics/GateSemantics.lean`, then continue
into `FastMultiplication/ShorVerification/Implementation/`. The repository is
moving toward the boundary described in `RESTRUCTURE_PLAN.md`, where this richer
construction language belongs on the implementation side.

To study the factoring reduction, read `Math/Factoring_Reduction/Defs.lean`, the
public theorem statements in `ProbabilityBound.lean`, and then
`Reduction.lean`. The internal counting proofs are not required to understand
or use the order-finding interface.

## Reading Approach

For each file, first read its module comment and declaration signatures without
opening the proof bodies. Identify which declarations are data, operations,
predicates, or laws. For a dense class field, separate its inputs and
preconditions from each part of its result, then restate the field in one plain
sentence. Tracing one basis configuration through a register operation, gate,
or measurement is often the quickest way to connect the abstractions.
