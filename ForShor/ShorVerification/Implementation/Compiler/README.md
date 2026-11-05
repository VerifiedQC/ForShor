# `Implementation/Compiler/`

This folder compiles a `Gate` circuit to a `LowGate` program by sending each
QFT, phase-product and modular-arithmetic block to its subroutine's lowerer,
and proves that the compiled program acts exactly as the circuit does.

`Statement.lean` is the only file needed to see what is claimed: it holds
every definition the claim depends on and imports nothing else from this
folder. `Main.lean` proves the claim stated in `Statement.lean`; `Proofs/`
holds the lemmas that proof uses, and the single-table forms used by `Emit/`,
`GateCount/` and `Reference/`.

## Background

`Gate` has high-level blocks: the QFT, signed phase products (plain and
controlled), and comparison and subtraction against a constant. `LowGate` has
only elementary gates. The compiler walks the circuit, keeps sequencing and
adjoints, copies elementary gates across, and replaces each high-level block
by a lowered circuit: the QFT and phase products by those of `QFT/` and
`PhaseProduct/`, and the constant comparison and subtraction by ones defined
here.

**Constant arithmetic.** Both use one spare qubit of a scratch register as the
constant 1, copy the bits of N into the scratch register with one CNOT per set
bit, and negate it to get −N. The comparison then adds the data register to
the scratch register, copies the sign of data − N to the flag, and uncomputes.
The subtraction controls the preparation of −N on the flag, adds the scratch
register to the data register, and uncomputes.

Those lowered circuits borrow spare qubits as scratch space. Each block
therefore needs two things:

1. **Enough spare qubits, laid out correctly.** This is a static condition on
   the registers, needed to build the lowered circuit at all.
2. **Those spare qubits in |0⟩ when the block runs.** This is a condition on
   the state, needed for the lowered circuit to act like the block.

Which Toom-Cook table the phase products use is chosen by a
`ShorLoweringPolicy`, a list of tables indexed by operand width. A single table
is the constant policy.

## `Statement.lean`

The following explains each section of the code in the Statement.lean file

**Constant arithmetic.** `lowerCmpGeConst` and `lowerCSubConst`, the lowered
comparison and subtraction described above; `ConstArithmeticWorkspace`, the
spare qubits and layout they need; and `CmpGeConstCleanState` /
`CSubConstCleanState`, the condition that those spare qubits start at zero.

**Static workspace condition.** `Policy.GateWorkspaceOK P G`: every high-level
block in `G` has the spare qubits its lowerer needs under the policy `P`. The
ideal modular multiplication has no lowering, so it never satisfies it.

**The lowering.** `Policy.lowerGate P G hws`: the compiled program. It takes a
proof `hws` of the static condition, since the subroutine lowerers need it to
build their circuits.

**Clean-state precondition.** `Policy.GateWorkspaceCleanState`: the spare
qubits each block will use are in |0⟩ on the state it is applied to. For a
sequence, the second part's condition is checked on the state after the first
part's compiled program.

**Correctness.** `Policy.LowerGateCorrect`: for an admissible policy, on any
state meeting the clean-state precondition,
`⟦Policy.lowerGate P G hws⟧ₗ ψ = ⟦G⟧ ψ`.

## `Main.lean`

Proves `Policy.LowerGateCorrect`.
