# `Proofs/`

Proof files. Other folders import the lemma libraries below directly;
everything else is reached through `Main.lean`. See `Proofs/Compiler/README.md`,
`Proofs/Lowering/README.md` (and their `Body/`/`PlanReadiness/` subfolders) for
the compiler- and lowering-correctness proofs.

## Lemma libraries: `Registers.lean`, `States.lean`, `GateLaws.lean`, `LowGateEval.lean`

Derived laws of Framework definitions, used here first and imported by `QFT/`,
`Compiler/`, `ModularExponentiation/`, `Shor/` and `Reference/` proofs.

| File | Contents |
|---|---|
| `Registers.lean` | Laws of `Reg`, `RegEncoding`, `ExtReg` and two's complement: split/append arithmetic, bit and basis-write transport, encoding transport across disjoint registers. |
| `States.lean` | Consequences of `GateSemanticsCore`: zero, subtraction, injectivity, adjoint inverse; `QSemantics.*` wrapper names for the class laws; isometry, norm and freshness transport. |
| `GateLaws.lean` | Laws of the per-gate classes of `Framework/Semantics/GateSemantics.lean`: Pauli-X locality, radix reverse, sign extension, and the basis-write arithmetic of `ArithmeticSemantics`. |
| `LowGateEval.lean` | `LowerGateClass.evalL` on zero and on basis-equal circuits, and the `evalL` laws of the unsigned macro gates built from the signed primitives (`LowerGateGateBridge`). |

## `NaiveLeaf.lean`

Correctness of the naive reference circuits defined in `Statement.lean`.

- **`evalL_naive_signedPhaseProd_ket`** — evaluating `Naive_SignedPhaseProd`
  on a basis ket contributes exactly the phase `exp(i·φ·x·z)` (as signed
  integers read off the register) and returns the same ket.
- **`gateCount_Naive_SignedPhaseProd`** — given `x`, `z` own disjoint qubits,
  the naive circuit uses exactly `5 · width(x) · width(z)` gates (one `CPhase`,
  5 primitive gates each, per pair of bit-weighted terms).
- **`evalL_naive_csignedPhaseProd_ket`** / **`gateCount_Naive_CSignedPhaseProd`**
  — the same two results for the controlled circuit (`9` gates per term pair,
  since each `CCPhase` expands to more primitives than `CPhase`).

These four theorems are consumed by `Proofs/Lowering/EvalL.lean` (for the
recursion base case) and `GateCount/PhaseProduct/Lemmas.lean` (for the
asymptotic gate-count bound), which is why they live here rather than in
`Main.lean`.
