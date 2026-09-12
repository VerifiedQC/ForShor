# `Proofs/`

Proof-only files. Nothing outside `Proofs/` or `Main.lean` may import
anything in here. See `Proofs/Compiler/README.md`, `Proofs/Lowering/README.md`
(and their `Body/`/`PlanReadiness/` subfolders) for the compiler- and
lowering-correctness proofs.

## `NaiveLeaf.lean`

Correctness of the naive reference circuits defined in `Gates/NaiveLeaf.lean`.

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
