# Balanced

This folder changes one thing about the reference circuit in `../Standard/`: the phase products whose two operands have different widths.

The phase product cuts both operands into the same number of chunks, so when one operand is much wider than the other, its chunks are much wider too, and the recursion pays for it. In the modular multiplication, Step 4 multiplies the 2348-bit work register by the 4399-bit scratch register, and that one product dominates the qubit count. Balancing fixes this before lowering: the wider operand is cut into blocks of about the narrower operand's width, and each block is multiplied by the whole narrower operand at a common width, using ordinary equal-width phase products. The phases add up, so the result is the same.

There are two versions of the pass.

- `balance` checks each site first. A site is split only if the spare qubits already there hold every block (`fitsB`); otherwise it is left alone. This pass needs nothing from the layout, so it is correct on any registers the plain circuit is correct on, but the shape of the circuit depends on the reserves.
- `balanceU` splits every site the rule has a plan for, with no check. It is correct wherever every site's plan fits (`Fits`). The reference layout in `../Standard/` is sized so that this always holds for the default rule, which is why the unconditional implementation needs no extra hypothesis and why its qubit count depends on the register widths alone.

`Statement.lean` has the split, the two passes, the default rule, and the claims: each pass keeps the workspace and the semantics, and Shor's circuit lowered after each pass keeps its success bound. `Proofs/` proves them (`Semantics.lean` for what a split computes, `Correctness.lean` for the workspace and the lowering, `Fits.lean` for when a plan fits and that the reference layout always does). `Main.lean` builds `balancedShorImplementation` and `balancedUShorImplementation`; both reuse `../Standard/`'s layout, precision, success bound and trial count, so their correctness comes straight from the standard one.

At 2048 bits the peak qubit count goes from 19,319 to 17,291 (`QubitCount/`).
