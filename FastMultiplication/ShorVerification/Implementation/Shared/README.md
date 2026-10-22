# `Implementation/Shared/`

What the files in this folder have in common is not "semantics" — it is their
**position**: each is a lemma library over Framework vocabulary, imports
nothing from any subroutine folder, and is imported by two or more of
`PhaseProduct/`, `QFT/`, `ModularExponentiation/`, `Shor/`.

**Admission rule:** a file lives in `Shared/` iff (a) it imports only
`Framework/`, Mathlib, and other `Shared/` files, and (b) it is imported from
at least two different folders among `PhaseProduct`, `QFT`,
`ModularExponentiation`, `Shor`, `GateCount`, `Reference`. (a) is enforced by
`scripts/check_layers.py Shared` (repo root), which also checks the internal
layer order below; (b) is reported by the same script as a warning, not a
build failure, and `Measurement.lean` is the one file it currently flags as
imported from a single folder.

## Internal layer order

```
QftPhase, Registers  <  States  <  Hadamard, GateLaws  <  LowGateEval        Measurement (independent)
```

A file may import its own layer or any layer to its left; `Measurement.lean`
has no `Shared/` dependencies and sits outside the chain.

## Files

| File | Derived laws of | Contents | Imported by |
|---|---|---|---|
| `Registers.lean` | `Framework/Quantum/Registers.lean` (`Reg`, `RegEncoding`, `ExtReg`, two's complement) | Every derived register/encoding law used by concrete implementations: split/append arithmetic, bit/basis-write transport helpers, encoding transport across disjoint registers. | `PhaseProduct/`, `QFT/`, `ModularExponentiation/`, `Shor/`, and `Shared/GateLaws.lean`/`Hadamard.lean`/`LowGateEval.lean` themselves. |
| `States.lean` | `Framework/Quantum/QSemantics.lean` (`eval` algebra, norms, isometry, freshness) | The zero/subtraction/injectivity/adjoint-inverse consequences of `GateSemanticsCore`, convenient `QSemantics.*` wrapper names for the class laws, a `Finset.sum` push-through lemma, isometry/norm/freshness transport facts, and the `CleanClosure` predicate on `qs.State`. | `PhaseProduct/`, `QFT/`, `ModularExponentiation/`, `Shor/`, and `Shared/Hadamard.lean`/`GateLaws.lean`/`LowGateEval.lean` themselves. |
| `Hadamard.lean` | `H_reg` on a register: uniform superposition, span closure | One-qubit register/zero-split/Hadamard-superposition facts and normalization constants, plus the finite-span closure of basis states reachable by applying Hadamards over a register's qubits. | `QFT/`, `ModularExponentiation/`. |
| `GateLaws.lean` | `Framework/Semantics/GateSemantics.lean` classes (Pauli-X, extension, radix reverse, arithmetic basis functions) | Pauli-X/zero-extension locality, the unsigned phase-product macro semantics, the proof declarations moved out of the framework file for radix reverse/extension/arithmetic basis functions, and the generic basis-write arithmetic lemmas for `ArithmeticSemantics`. | `PhaseProduct/`, `QFT/`, and `Shared/LowGateEval.lean`. |
| `LowGateEval.lean` | `Framework/Semantics/LowGateSemantics.lean` (`LowerGateClass.evalL` on each primitive, the `Gate` bridge) | `LowerGateClass.evalL`'s zero/algebra consequences, and the `evalL` correctness lemmas for the unsigned macro gates implemented in terms of the signed primitives (`LowerGateGateBridge`). | `PhaseProduct/`, `QFT/`. |
| `Measurement.lean` | `Framework/Quantum/Measurement.lean` (`MeasureClass`) | Probability estimates built on `MeasureClass`. | `Shor/`. |
| `QftPhase.lean` | `qftPhase`/`ωPow` from `Framework/AbstractMachine/Gates.lean` | Grid-exponential form of `qftPhase`, its conjugate, periodicity, and unit norm. | `ModularExponentiation/`, `Shor/`. |
