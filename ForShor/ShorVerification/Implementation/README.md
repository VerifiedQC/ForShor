# Implementation

This folder builds Shor's order-finding circuit and proves it correct. `Framework/` only sets up the vocabulary (registers, gates, semantics, cost model); everything here is the construction.

Each folder has the same shape: `Statement.lean` holds the definitions and the claims, `Proofs/` holds the lemmas, and `Main.lean` proves the claims. If you want to know what a folder proves, read its `Main.lean`.

## The folders

**`PhaseProduct/`** builds the circuit that applies the phase `exp(i·φ·x·z)` to two registers, using a Toom-Cook recursion so it beats the naive quadratic circuit. Main result: `lowerSignedPhaseProduct_correct` (and the controlled version), plus a gate-count bound of `n^(log_k(2k−1))`.

**`QFT/`** builds the quantum Fourier transform recursively, splitting a register in two and joining the halves with a phase product from `PhaseProduct/`. Main result: `lowerQFT_correct`, plus its gate-count bound.

**`ModularExponentiation/`** builds the in-place modular multiplication (Algorithm 1) and, by repeating it over the exponent register, modular exponentiation, with a bound on the approximation error. Main result: `modExpApprox_correct`.

**`Compiler/`** lowers a high-level `Gate` circuit to a `LowGate` program by sending each piece to its folder's lowerer. Which Toom-Cook table is used at each width is given by a `ShorLoweringPolicy`. Main result: `Policy.lowerGate_correct`.

**`Shor/`** puts the pieces together into the order-finding circuit and proves it is Shor's algorithm: a lower bound on the success probability, carried across the approximation error of the modular exponentiation. Main results: `Shor_correct_approx_lowered` and the gate-count bound `exists_shorGateCountBound`, which is `O(n^(2+ε))`; `Policy.shorGateCountBound` gives the same bound for any admissible policy whose first band's exponent `log_k(2k-1)` is at most `1 + ε`.

**`QubitCount/`** counts how many qubits the lowered circuit needs at once, and proves an exact formula for it. Main results: the three formulas `Policy.orderFinding_peak_formula`, `_balanced` and `_balanced_u`. At 2048 bits the plain circuit peaks at 19,319 qubits and the balanced one at 13,449. These are for the default negation method (below); a policy that asks for the scratch one has a balanced peak of 17,291, the plain peak being the same. A policy chooses how `Negate` is built: `negation := .oneQubit` (default, one clean qubit) or `.scratch` (a clean register as wide as the operand, fewer gates), and its qubit count and gate resources are stated for the method it names. The headline `ShorImplementation` gate count (`exists_shorGateCountBound` and the contract's cost figures) is priced with the default one-qubit model; the per-method versions are the `...For` theorems in `Shor/Proofs/GateCount.lean`, `PhaseProduct/Proofs/GateCount` and `QFT/Proofs/GateCount.lean`.

**`Reference/`** exists because everything above is stated for *any* registers, layout and policy that satisfy some conditions. Somebody has to actually pick them. `Reference/` makes every choice concrete: the precision, the register widths, where each register sits, and proves that this concrete layout satisfies all the conditions the other folders ask for. The result is a value of `ShorImplementation` (`Contract.lean`), the contract a submission has to meet: a circuit for every instance, a declared success probability, and a trial count.

- `Standard/` is the reference as is. Main result: `referenceShorImplementation`.
- `Balanced/` is the same with each unequal phase product split into equal-width blocks first, which lowers the qubit count. Main results: `balancedShorImplementation` and `balancedUShorImplementation`.

## A submission

A submission is just a Toom-Cook table (or a list of them by width, a policy) with four decidable side conditions. `Reference/` turns any admissible table into a full `ShorImplementation`, and its correctness proof is generic in the table, so a submitter never writes a proof. See `Submission/README.md`.
