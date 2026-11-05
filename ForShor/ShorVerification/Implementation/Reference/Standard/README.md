# Standard

This is the reference implementation: Shor's order-finding circuit, lowered as the other folders define it, on a concrete layout.

The other folders leave some things open: how precise the modular exponentiation is, how wide each register is, where the registers sit, and how many spare qubits each one has. `Statement.lean` picks all of them. The precision at level `m` is `1/(m+3)`; the register widths follow from the modulus and the precision; the registers are laid out one after another from qubit 0, each followed by its spare qubits, sized to what the lowering needs. It also fixes the success bound the reference declares and the trial count that amplifies it to 99%.

`Proofs/` shows that this layout meets every condition the other folders ask for: the registers don't overlap, every reserve is large enough, and everything starts clean from the all-zero state (`Layout.lean`, `Readiness.lean`). It then carries `Shor/`'s success bound over to this circuit (`Success.lean`) and works out the bound at the 2048-bit level (`Headline.lean`).

`Main.lean` builds the circuit and packages it as `referenceShorImplementation`, a value of the contract in `../Contract.lean`. The standard Toom-Cook table, `standardPolicy`, is defined there too.

The claims in `Statement.lean` are the correctness of the circuit at any precision level and at the chosen one, the trial count, and the 2048-bit bound.
