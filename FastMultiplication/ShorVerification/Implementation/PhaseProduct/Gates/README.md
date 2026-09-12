# `Gates/`

Circuit-macro definitions: the actual `Gate` constructions the compiler and
the naive reference implementation are built from. These depend only on
`Framework/`, not on `Compiler/`.

## `Macros.lean`

- **`PhaseProdWorkspace x z`** — the one-clean-bit-per-operand workspace an
  *unsigned* phase product needs to reuse the signed phase-product gate: two
  reserve bits (`xReserve`, `zReserve`), each disjoint from `x`, `z`, and each
  other.
- **`PhaseProdWorkspace.xExt`/`.zExt`** — the corresponding extendable
  registers (operand plus its one-bit reserve); **`.Clean`** — the reserve
  bits are zero in a given basis state; **`.ControlDisjoint`** — a control
  qubit stays outside every register the workspace touches.
- **`PhaseProdUsing`** — the unsigned phase-product macro: zero-extend both
  operands by one bit, run the signed phase product on the grown registers,
  then deallocate the extension bits.
- **`CPhaseProdUsing`** — the controlled counterpart, using `CSignedPhaseProd`
  in the middle.

## `NaiveLeaf.lean`

The reference (unoptimized) circuit constructions — one `LowGate` per pair of
signed bit-weighted terms, with no chunking or interpolation. Used as the
recursion base case and as the ground truth the compiled circuit is checked
against.

- **`Naive_SignedPhaseProd`** — sequences a `CPhase` gate for every pair
  `(x-bit, z-bit)`, each angle scaled by the pair's signed bit weights
  (`signedPairAngle`); **`Naive_CSignedPhaseProd`** is the controlled version,
  built from `CCPhase` (a doubly-controlled phase, itself expanded into
  `CPhase`/`Toffoli`).
- **`signedBitWeight`**, **`signedTerms`** — the signed place-value weight of
  each bit of an extended register (the top bit is negative, per two's
  complement), and the resulting list of `(qubit, weight)` terms.
- **`signedPairExponent`**, **`naiveSignedPhaseExponents`** (and their
  controlled counterparts `cSignedPairExponent`,
  `naiveCSignedPhaseExponents`) — the complex phase each term pair
  contributes, and the full list of them; these are the quantities the
  correctness proofs in `Proofs/NaiveLeaf.lean` sum up.
