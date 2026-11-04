# Model

Every theorem in `Framework/`, `Implementation/` and `Submission/` is stated over abstract typeclasses: a state space with kets, gates that act on kets in a certain way, measurement as projectors. The proofs use only the laws those classes state. That keeps them independent of any particular linear-algebra library, but it leaves one question open: can all the laws hold at once? If they couldn't, every theorem would be vacuously true and `#print axioms` would never notice.

This folder answers that question. It builds a concrete model of every class and checks that the main theorems specialise to it. It proves nothing new about Shor's algorithm.

**`Standard/`** builds the model: states are finite complex combinations of basis kets over infinitely many qubits, Hadamard and the QFT are their usual matrices on a register, arithmetic gates are permutations of the basis, phase products are diagonal phases, measurement is projection. `Standard/Headline.lean` applies the main theorems at this model.

**`QuantumLib/`** restates the same theorems in the form a reader used to matrix-based developments expects: the circuit is a `2^dim × 2^dim` complex matrix, the input is the all-zeros vector, and the success probability is a sum of squared norms of projected vectors, using QuantumLib's types. Nothing is reproved; each statement is transported from `Standard/`.

Nothing outside this folder imports anything in it, and that is part of the point: the development doesn't depend on the model. Removing the folder changes no theorem outside it.

## Building

The folder isn't in the library root, so `lake build ForShor` doesn't see it. Each subfolder's `Headline.lean` imports everything else in it:

```bash
lake build ForShor.ShorVerification.Model.Standard.Headline
```

```bash
lake build ForShor.ShorVerification.Model.QuantumLib.Headline
```
