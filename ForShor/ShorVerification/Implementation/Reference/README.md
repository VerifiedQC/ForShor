# Reference

The other folders prove things about the order-finding circuit for any registers, layout and policy that satisfy their conditions. This folder picks all of those concretely (the precision, the register widths, where each register sits) and proves the conditions hold for that choice. Out comes a finished implementation.

## The contract

`Contract.lean` says what "finished" means. A `ShorImplementation` has to provide:

- a circuit for every valid order-finding instance, and the register to measure
- a declared lower bound on the single-run success probability, with a proof that every circuit meets it
- a number of trials that pushes that bound to 99% for every 2048-bit modulus, with a proof.

Both folders below build a value of this structure, so both are complete, verified implementations.

## Standard and Balanced

**`Standard/`** is the reference implementation as such: it lowers the order-finding circuit directly, on the layout it chooses. Main result: `referenceShorImplementation`.

**`Balanced/`** keeps the same layout, precision and success bound, but changes the circuit. The modular multiplication multiplies registers of unequal width, and the recursive phase product is expensive on unequal operands. `Balanced/` first cuts the wider operand into blocks and runs equal-width products instead, which brings the peak qubit count at 2048 bits down from 19,319 to 17,291. Its correctness comes from `Standard/`'s: the balanced circuit computes the same thing, so it has the same success probability. Main results: `balancedShorImplementation` (a split is used only where the layout has room for it) and `balancedUShorImplementation` (every site is split; the layout always has room).
