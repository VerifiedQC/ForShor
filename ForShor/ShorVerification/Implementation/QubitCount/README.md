# QubitCount

This folder works out how many qubits the lowered order-finding circuit needs at once, and proves an exact formula for it. There is a version for the plain circuit and one for the circuit after the balanced split in `Reference/Balanced/`.

## What gets counted

We walk the lowered circuit in order and keep track of which qubits are live. A gate makes the qubits it touches live. Extending a register brings reserve qubits in, and deallocating releases them. The peak is the largest the live set ever gets.

`AddScaled` and `Negate` also borrow a few clean scratch qubits while they run (a carry for the adder, a constant-one register and a carry for negation). Those are added in while the primitive runs and returned afterwards.

This is not the same as the number of qubits the circuit ever touches (`LowGate.qubitCount`). The allocator gives every child of a phase-product recursion its own reserve, but the children run one after another, so only one of them is live at a time.

## Files

- `Statement.lean` has the counting walk, the closed-form budgets and the claims. It doesn't import anything else from this folder.
- `Proofs/` has the lemmas: one file per piece of the circuit (a recursion level, a phase product, the QFT, a modular multiplication, the whole order-finding circuit), plus the 2048-bit numerals.
- `Main.lean` proves the three formulas:
  - `Policy.orderFinding_peak_formula`: the peak is the base registers plus the most expensive step, for any admissible policy.
  - `Policy.orderFinding_peak_formula_balanced`: the same for the balanced circuit, where each site costs its split if the spare qubits hold it and the plain product otherwise.
  - `Policy.orderFinding_peak_formula_balanced_u`: the same for the unconditionally balanced circuit, where every site is split and the count depends on the register widths alone.

## The 2048-bit numbers

These are for the reference circuit with the standard `k = 2` table. The registers are data 2048, work 2347 and scratch 4398 qubits, and the exponent register is 4095 or 4096 qubits depending on `N`. With a 4096-qubit exponent register:

| circuit | base registers | most expensive step | peak |
|---|---|---|---|
| plain | 12,891 | Step 4's phase product, 6,428 | **19,319** |
| balanced | 12,891 | negating the scratch register, 4,400 | **17,291** |

With 4095 exponent qubits, take one off each. The plain circuit peaks in Step 4 because that phase product multiplies a 2348-bit register by a 4399-bit one. Balancing splits it into two 2348 × 2348 products, which cost 553 qubits instead, so the negation becomes the largest step.

The numbers are proved in `Proofs/Numerals.lean` and `Proofs/BalancedNumerals.lean`, checked by the kernel (`decide +kernel`). The formula without scratch was also compared against the real compiled circuit from `forshor_emit` for small instances, and it matched every time.
