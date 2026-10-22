# `Model/`

Concrete models of the semantics the rest of the development is stated over.
This folder proves nothing new about Shor's algorithm. It answers a question
the other folders cannot: *are the theorems about anything?*

## The gap

Every theorem in [`Framework/`](../Framework), [`Implementation/`](../Implementation)
and [`Submission/`](../Submission) is stated over abstract typeclasses rather
than a fixed notion of state and gate. A `QSemantics` says there is a state
space with kets in it, a `GateSemanticsFacts` says each gate acts on kets in a
certain way, a `MeasureClass` says measurement is a family of projectors, and
so on. The proofs use only the laws these classes state, never a particular
encoding. That is what keeps them independent of any linear-algebra library
and reusable as the circuit designs change.

The cost of that generality is that nothing in those folders ever exhibits
*one* state space and *one* set of gates satisfying all the laws at once. If
the laws were jointly contradictory, every theorem would hold vacuously, and
`#print axioms` would still report only the standard three axioms. A reader
who checks the axioms is entitled to ask whether the hypotheses can be met.

This folder closes that gap by building such a model and checking that the
headline theorems specialise to it. Nothing outside this folder imports
anything inside it; the development's independence from the model is itself
part of what is being certified.

## The two subfolders

**[`Standard/`](Standard)** builds the model. States are finite complex
combinations of computational-basis kets over infinitely many qubits, which is
forced by the register encoding allowing arbitrarily large qubit names. Gates
are the textbook ones: Hadamard and the QFT as their matrices on one register,
reversible arithmetic as permutations of the basis, phase products as diagonal
phases, measurement as projection onto an outcome. Every semantic class gets an
instance here, and `Standard/Headline.lean` applies the correctness and
gate-count theorems and the submission certificates at that instance. If any
law could not be satisfied, that file would fail to elaborate.

**[`QuantumLib/`](QuantumLib)** restates the same headline theorems in the
form a reader coming from a matrix-based development expects: the circuit is a
`2^dim × 2^dim` complex matrix, the input is the all-zeros column vector, and
the success probability is a weighted sum of squared norms of projected
vectors, using the types and gate definitions of the QuantumLib library. It
does this by embedding the finite column-vector space into the `Standard/`
model and proving that running a `LowGate` circuit there agrees with
multiplying by its matrix. Nothing is reproved; each statement is transported
from its abstract original. QuantumLib's definitions are vendored rather than
required, because no release of that library builds on this repository's
toolchain; its README explains the consequences.

## What this does and does not establish

It establishes that the semantic classes are satisfiable, and satisfiable by
the standard unitaries, so the theorems are statements about ordinary quantum
circuits. It does not make the development depend on this model, and it is not
a claim about physical hardware. Removing the folder changes no theorem
outside it.

## Building

The folder is not in the library root, so `lake build FastMultiplication`
does not see it. Each subfolder's `Headline.lean` imports everything else in
it:

```
lake build FastMultiplication.ShorVerification.Model.Standard.Headline
lake build FastMultiplication.ShorVerification.Model.QuantumLib.Headline
```

Each subfolder's own `README.md` has the file-by-file breakdown.
