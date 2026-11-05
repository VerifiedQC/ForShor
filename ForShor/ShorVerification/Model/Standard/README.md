# Model/Standard

One concrete model of every semantic class in `Framework/`, and a check that the main theorems hold in it (`Headline.lean`). Nothing here is used by any proof outside this folder.

## What the model is

- **The basis is `ℕ → Bool`**, one bit per qubit, over infinitely many qubits. It has to be infinite: a register can name any qubit, and reading back what you wrote must work for every register, so no fixed dimension can carry the class.
- **States are finite complex combinations of basis kets** (`ModelBasis →₀ ℂ`), with the ℓ² inner product. A ket is literally a standard basis vector.
- **Gates are linear isometric equivalences of the state space.** Every gate law in `Framework/` gives the image of a ket explicitly, and those images come in three shapes: a relabelling of the basis (arithmetic gates), a diagonal phase (phase products), or a small matrix on one register (Hadamard, the QFT). One lemma, `liftIso`, turns each shape into a gate.
- **`adj` is the inverse**, so the adjoint laws are just linear-isometry facts.

## The files

- `Basis.lean`: the basis and its `RegEncoding` instance.
- `Arith.lean`: two's-complement arithmetic on words; the shifts are mutually inverse.
- `State.lean`: the state space, kets, `QSemantics` and `MeasureClass`.
- `Lift.lean`: the three ways of turning a basis map into a gate.
- `BasisMaps.lean`: a basis permutation for each arithmetic gate, and the model's ideal modular multiplier.
- `Blocks.lean`: the Hadamard and QFT matrices and the diagonal phases.
- `Gates.lean`, `LowGates.lean`: the `GateSemanticsFacts` and `LowerGateClass` instances.
- `Headline.lean`: the main theorems specialised to this model. It is the only file here that imports `Implementation/` and `Submission/`.

## Building

```bash
lake build ForShor.ShorVerification.Model.Standard.Headline
```
