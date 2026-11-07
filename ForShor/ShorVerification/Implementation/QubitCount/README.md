# QubitCount

This folder works out how many qubits the lowered order-finding circuit needs at once, and proves an exact formula for it. There is a version for the plain circuit and one for the circuit after the balanced split in `Reference/Balanced/`.

## What gets counted

We walk the lowered circuit in order and keep track of which qubits are live. A gate makes the qubits it touches live. Extending a register brings reserve qubits in, and deallocating releases them. The peak is the largest the live set ever gets.

`AddScaled` and `Negate` also borrow clean scratch qubits while they run. `AddScaled` borrows one carry. What `Negate` borrows depends on the negation method the policy asks for (`P.negation`, a `NegationMethod`):

- `oneQubit` (the default): negation is the complement followed by a one-clean-ancilla increment gate, so it borrows one qubit.
- `scratch`: negation is the complement followed by an addition against a constant-one register as wide as the register it negates, plus the adder's carry, so it borrows the register's width plus one. This is the model that held before modular swap 001, and it reproduces the numbers of that time.

Those qubits are added in while the primitive runs and returned afterwards. Every budget and every theorem below is stated for both methods: `scratchFor m` is the scratch charge of the method `m`, the budgets take `m` (written `P.negation` at the level of a policy), and a policy submitted with `negation := .scratch` is counted with the register-wide charge while one that names no method is counted with the one-qubit charge.

This is not the same as the number of qubits the circuit ever touches (`LowGate.qubitCount`). The allocator gives every child of a phase-product recursion its own reserve, but the children run one after another, so only one of them is live at a time.

## Files

- `Statement.lean` has the counting walk, the closed-form budgets and the claims. It doesn't import anything else from this folder.
- `Proofs/` has the lemmas: one file per piece of the circuit (a recursion level, a phase product, the QFT, a modular multiplication, the whole order-finding circuit), plus the 2048-bit numerals. `Proofs/PolicyPeak.lean` is the interface for costing an arbitrary policy at the 2048-bit reference widths: it reduces the peak of the reference circuit to `Policy.orderFindingPeak P` (or `Policy.orderFindingPeakBalanced P`), which the kernel can evaluate on a concrete policy.
- `Main.lean` proves the three formulas:
  - `Policy.orderFinding_peak_formula`: the peak is the base registers plus the most expensive step, for any admissible policy, counted with that policy's negation method.
  - `Policy.orderFinding_peak_formula_balanced`: the same for the balanced circuit, where each site costs its split if the spare qubits hold it and the plain product otherwise.
  - `Policy.orderFinding_peak_formula_balanced_u`: the same for the unconditionally balanced circuit, where every site is split and the count depends on the register widths alone.

## The 2048-bit numbers

These are for the reference circuit with the standard `k = 2` table. The registers are data 2048, work 2347 and scratch 4398 qubits, and the exponent register is 4095 or 4096 qubits depending on `N`. With a 4096-qubit exponent register:

| circuit | method | base registers | most expensive step | peak |
|---|---|---|---|---|
| plain | `oneQubit` (default) | 12,891 | Step 4's phase product, 6,428 | **19,319** |
| plain | `scratch` | 12,891 | Step 4's phase product, 6,428 | **19,319** |
| balanced | `oneQubit` (default) | 12,891 | Step 1's phase product, 558 | **13,449** |
| balanced | `scratch` | 12,891 | negating the scratch register, 4,400 | **17,291** |

With 4095 exponent qubits, take one off each. The plain circuit peaks in Step 4 because that phase product multiplies a 2348-bit register by a 4399-bit one, and this is the same for both methods. Balancing splits it into two 2348 × 2348 products, which cost 553 qubits instead. What is then the largest step depends on the method. With `scratch`, Step 3's constant arithmetic on the 4398-qubit scratch register needs its unit qubit plus the register-wide constant and carry, 4,400 qubits, so that is the largest step. With `oneQubit` it needs 3, and Step 1's phase product, with its two qubits of scratch, is the largest (558).

The numbers are proved in `Proofs/Numerals.lean` and `Proofs/BalancedNumerals.lean`, checked by the kernel (`decide +kernel`). Each theorem has a form for a general method `m` (`..._for`) and the two instances: the unsuffixed name is the default `oneQubit` method, and `_scratch` is the `scratch` method (`standardPolicy2S`). The formula without scratch was also compared against the real compiled circuit from `forshor_emit` for small instances, and it matched every time.
