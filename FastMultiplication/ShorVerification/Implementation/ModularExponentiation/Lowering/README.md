# `Lowering/`

Concrete lowering of the Step-3 constant arithmetic to `LowGate` primitives.
`Gate.CmpGeConst`/`Gate.CSubConst` remain useful typed gates in the source
language, but they are not `LowGate` primitives — this file realizes both
with the target gates that are.

## `ConstArithmetic.lean`

One real reserve qubit of `scratch` is used as the signed one-bit constant
`-1`; the active scratch register is computed and uncomputed around the data
operation.

- **`constArithmeticUnitQubit`** — the first genuinely allocated reserve
  qubit of `scratch`.
- **`constArithmeticUnit`** — that qubit, regarded as a one-bit signed
  extendable register.
- **`lowerCopyBitPowers`** / **`lowerCopyConstFromUnit`** — controlled-write
  the binary expansion of a classical constant into a clean register, one
  `CNOT` per set bit (`Nat.bitIndices`).
- **`lowerPrepareNegConst`** — prepare `scratch = -N` from a clean active
  scratch and one clean reserve bit: write `N`'s bits, then negate. At most
  one `CNOT` per active bit plus one linear-cost negation.
- **`lowerCmpGeConst`** — lowering of `Gate.CmpGeConst`: prepare `-N`, take
  the signed difference against the (bit-extended) data register, copy the
  sign bit to `flag`, then uncompute both the difference and the
  preparation. Consumes a `ConstArithmeticWorkspace` (`Circuit/Workspace.lean`).
- **`lowerCSubConst`** — lowering of `Gate.CSubConst`: prepare `0` or `-N`
  depending on `flag`, add it into `data` with one fixed-width `AddScaled`,
  then uncompute the preparation. Also consumes a `ConstArithmeticWorkspace`.

These are the two lowerers `Shor/Proofs/Readiness.lean` and
`Shor/Proofs/WholeProgramCorrectness.lean` need directly to connect the
source-level `Circuit/Steps.lean:step3` to an actual `LowGate` circuit.
