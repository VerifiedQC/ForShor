# `Implementation/QFT/`

The QFT lowered to elementary gates, with a proof that the lowered circuit
implements `Gate.QFT`.

`Statement.lean` is the only file needed to see what is claimed: it holds
every definition the claim depends on and imports nothing else from this
folder. `Main.lean` proves the claims stated in `Statement.lean`; `Proofs/`
holds the lemmas those proofs use.

## Background

The lowering follows the Cooley–Tukey split of the QFT. For an `n`-qubit
register with `n ≥ 2`, let `m = ⌊n/2⌋`, and write a basis value as
`x = x_L + 2^m·x_H`, with `x_L` on the low `m` qubits (`leftReg`) and `x_H` on
the high `n − m` qubits (`rightReg`). Then

```
QFT_n = R_m · (QFT_m ⊗ I) · P_{2π/2ⁿ} · (I ⊗ QFT_{n−m})
```

where `P_{2π/2ⁿ} |a⟩|b⟩ = e^{2πi·a·b/2ⁿ} |a⟩|b⟩` is a phase product between the
two halves (`Gate.PhaseProdUsing (qftPhi n)`), and the radix reversal
`R_m |k_L⟩|k_H⟩ = |2^{n−m}·k_L + k_H⟩` (`Gate.RadixReverse r m`) puts the output
in standard order. 

## `Statement.lean`

The following explains each section of the code in the Statement.lean file

**Workspace budget.** The number of ancillas the full recursion needs for an
`n`-qubit register, split between the two ancilla registers the phase product uses. Since
the steps run in sequence and reuse ancillas, it is the maximum over the
middle phase product and the two recursive calls, not their sum.

**Workspace registers and static preconditions.** The two ancilla registers
(`qftXWork`, `qftZWork`) are carved from the spare qubits of the input
register. The preconditions say there are enough spares, and the data register
and the two ancilla registers are pairwise disjoint.

**Child workspaces.** At each split, the phase product's ancilla space is
built from the two ancilla registers, and the same registers are shown to
remain valid for both halves, so the recursion reuses them unchanged.

**Lowering plans.** A plan records how one QFT is lowered: empty, a single
`H`, or a split carrying the phase-product plan and the plans for both
halves. `lowerQFTPlan` turns a plan into the `LowGate` circuit, following the
identity above.

**The unsigned phase-product subplan.** The QFT's phase product is on
unsigned values; the multiplier is signed. Each half is zero-extended by one
qubit, the signed phase product is applied, and the extensions are removed.

**The canonical plan and the lowered QFT.** The standard plan for any
register, and `lowerQFT` / `Policy.lowerQFT`: the lowered QFT, determined by
the register and its spare qubits alone.

**Workspace precondition on states.** The input must satisfy the static
preconditions and have both ancilla registers in `|0⟩`.

**Correctness.** For every input meeting that precondition,
`⟦lowered circuit⟧ₗ ψ = ⟦Gate.QFT r⟧ ψ`. `Policy.LowerQFTCorrect` states this
for any admissible policy, `LowerQFTCorrect` for a single admissible table.

## `Main.lean`

Proves `LowerQFTCorrect` and `Policy.LowerQFTCorrect`.
