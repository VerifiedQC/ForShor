# `Implementation/ModularExponentiation/`

This folder builds the approximate modular-exponentiation circuit of Shor's
algorithm, a chain of in-place modular multiplications built from phase
products and the QFT, and proves that on every valid input it is within
`t · √(2Kη)` of exact modular exponentiation, where `t` is the width of the
exponent register, `η` the per-step precision, and `K ≤ 1600` a constant.

`Statement.lean` is the only file needed to see what is claimed: it holds
every definition the claims depend on and imports nothing else from this
folder. `Main.lean` proves the claims stated in `Statement.lean`; `Proofs/`
holds the lemmas those proofs use.

## Background

**Modular exponentiation.** With exponent register bits x₀, …, x_{t−1},
the map |x⟩|y⟩ ↦ |x⟩|aˣ·y mod N⟩ is a product of t controlled
multiplications: bit xᵢ controls multiplication by cᵢ = a^(2ⁱ) mod N.

**Algorithm 1.** Each controlled multiplication by c is done in place, with a
work register and a comparator flag, in five steps:

1. Load a Fourier packet into the work register and apply a phase product
   controlled by the control bit.
2. Transfer the work register's phase into the data register, extended by one
   carry bit, with a second phase product.
3. Compare the data register against N and conditionally subtract N.
4. Clear the comparison flag with a second comparator, `cmpLtNW`.
5. Uncompute the work register using the inverse constant 1 − c⁻¹ mod N.

**Precision.** The work register has n + ⌈2 · log₂(2 + 1/(2η))⌉ qubits, where n
is the width of the data register. Each multiplication is then within √(2Kη)
of the exact one, and the t multiplications add up to t · √(2Kη).

## `Statement.lean`

The following explains each section of the code in the Statement.lean file

**Precision.** The error scale `stepErr K η = √(2Kη)`, the number of extra
work-register qubits for precision `η`, and `Algorithm1Precision`, which pins
the work register to that width.

**Spare qubits.** Lemmas on `ExtReg.CanGrow` and `ExtReg.OwnedDisjoint` under
growing a register and dropping reserve qubits. The Step 1, 2 and 5 workspaces
below are built from them.

**Workspace.** The register layout one multiplication needs, the spare qubits
its phase products use (`ModMulCircuitWorkspaceOK`, from which the Step 1, 2
and 5 workspaces are built), and the Step-4 comparator's scratch register
(`CmpLtNWWorkspace`).

**The Step-4 comparator.** `cmpLtNW`: compute N times the work register into
the scratch register in Fourier space, subtract it from the data register
shifted by the work register's width, copy the sign bit to the flag, and
uncompute.

**Algorithm 1.** `step1` to `step5`, and `CmodMulInPlaceCore`, the five steps
in sequence. Step 3 uses the `CmpGeConst` and `CSubConst` gates, whose lowering
is in `Compiler/`.

**Modular exponentiation.** `modExpIdeal'`, the exact version built from
`Gate.idealCtrlModMul`, and `modExpApproxValid`, the approximate version built
from `CmodMulInPlaceCore`, one per exponent bit.

**Valid inputs.** The data register holds a value below N, and the work,
scratch and flag qubits start at zero. `ValidAlgorithm1State` is the span of
such basis states.

**Configuration.** `ModExpConfig` bundles the modulus, registers, precision and
layout facts, with the approximate and exact gates it determines.

**Correctness.** `ModExpApproxValidDistUniform`: for some constant `K ≤ 1600`,
on every valid unit state, the approximate and exact gates differ by at most
`regSize x · stepErr K η`. `ModExpApproxValidDist1600`: the same bound at
`K = 1600`.

## `Main.lean`

Proves `ModExpApproxValidDistUniform` and `ModExpApproxValidDist1600`.
