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
- `Headline.lean`: the main theorems specialised to this model. It, `PhaseTripleProductHeadline.lean`, `MSemanticsModel.lean` and the `Semiclassical*Model.lean` files (which import `Implementation/Readout/` and `Implementation/Reference/`) are the only files here that import `Implementation/`; only `Headline.lean` imports `Submission/`.
- `MSemanticsModel.lean`: the classes the measurement language `MGate` needs all resolve here; its conservation of probability and reset law specialised to this model; non-vacuity checks (measuring `X q |0…0⟩` reads `1`, the feed-forward phase acts) and the readout round and deferred-measurement instances of `Implementation/Readout/Proofs/DeferredTests.lean` at this model. `semiclassical_eq_iqft_model` instantiates `semiclassical_eq_iqft` here (`a = 2`, `N = 3`, two exponent qubits), so its class and register hypotheses hold together.
- `SemiclassicalShorModel.lean`: the success theorems of the semiclassical order-finding circuit (`Implementation/Readout/Shor.lean`, one recycled control qubit, real modular multiplier) hold non-vacuously here: for every policy, instance and precision level the reference layout of `Implementation/Reference/` with the control = its first exponent qubit meets every hypothesis (`referenceSemiclassicalSetup`), the circuit names no exponent qubit other than the control (`model_semiclassical_avoids_exponent`), and some level reaches `shorPrecision`, where the success probability is `≥ κ / (2 log(log₂ N + 1)) > 0`.
- `SemiclassicalLoweredModel.lean`: the same for the LOWERED program (`Implementation/Readout/LoweredShor.lean`): at the reference layout the lowered program evaluates exactly as the high-level one (`model_semiclassical_lowerM_eval`) and succeeds with probability `≥ κ / (2 log(log₂ N + 1))` (`model_Shor_correct_semiclassical_lowered_at_shorPrecision`).
- `SemiclassicalMainModel.lean`: for the plain, balanced and every-site-split lowerings, one theorem each conjoins, on the same lowered circuit term at the reference layout, the success bound and the proved peak (`model_semiclassical_lowered*_success_and_peak`).
- `SemiclassicalGhostFreeModel.lean`: the ghost-free success theorems (`Implementation/Readout/GhostFree.lean`, no exponent register in the statement) and their success-and-peak conjunctions hold here, with the control the first qubit of the reference layout's exponent slot.

## Building

```bash
lake build ForShor.ShorVerification.Model.Standard.Headline
lake build ForShor.ShorVerification.Model.Standard.MSemanticsModel ForShor.ShorVerification.Model.Standard.SemiclassicalShorModel
lake build ForShor.ShorVerification.Model.Standard.SemiclassicalLoweredModel ForShor.ShorVerification.Model.Standard.SemiclassicalMainModel ForShor.ShorVerification.Model.Standard.SemiclassicalGhostFreeModel
```
