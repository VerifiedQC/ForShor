# Model/QuantumLib

The main theorems restated so that every term is a QuantumLib matrix or vector: the circuit is a `CSquare (2^dim)`, the input is the all-zeros `CVector (2^dim)`, and the success probability is a weighted sum of squared ℓ² norms of projected vectors. They are proved by transfer from `../Standard/`, with nothing reproved.

`../Standard/` is infinite-dimensional, because the register encoding allows arbitrarily large qubit names. That makes it a good consistency witness but not the finite matrix picture a reader coming from a library like SQIR expects. This folder gives that picture for the language the main theorems run on, `LowGate`.

## How it works

The finite vector space `CVector (2^dim)` is embedded into the `Standard/` state space (`ι`), each `LowGate` is given a matrix (`denote`), and `Transfer.lean` proves that running a circuit on an embedded vector is the same as multiplying by its matrix. Measurement becomes a projector matrix, so the success probability transfers too. Gates that have no matrix in QuantumLib, such as the reversible arithmetic, are permutation matrices; that matches how the development counts them.

Index `k` of a vector is the basis state whose qubit `i` is bit `i` of `k`, so qubit `0` is the least significant bit. QuantumLib's `kron` puts the left factor on the high bits, so a gate on qubit `q` is padded as `1 ⊗ gate ⊗ 1` with the identity on the higher qubits on the left.

## Why QuantumLib is vendored

No release of QuantumLib builds on this repository's Lean toolchain, so depending on it as a package would mean changing the toolchain for the whole development. `Vendored.lean` instead copies the dozen definitions this folder uses, character for character, with a header naming the source commit and reproducing QuantumLib's MIT license, as that license requires. Swapping it for a real dependency later changes no statement.

## The files

- `Vendored.lean`: the QuantumLib types and gates (`CMatrix`, `kron`, `hadamard`, `cnot`, `phaseShift`, ...).
- `Embed.lean`: the embedding `ι` and the ℓ² norm.
- `Denote.lean`: `denote`, the matrix of a `LowGate`, and its unitarity.
- `Native.lean`: sanity checks that `denote` of H, CNOT and Phase are the padded QuantumLib matrices.
- `Transfer.lean`: running a circuit equals multiplying by its matrix.
- `Measure.lean`: the projectors and the Born rule.
- `Headline.lean`: the main theorems over matrices. It is the only file here that imports `Implementation/` and `Submission/`.

## Building

```bash
lake build ForShor.ShorVerification.Model.QuantumLib.Headline
```
