# `Model/QuantumLib/`

The headline theorems restated so that **every term is a QuantumLib matrix or
vector** — the circuit a `CSquare (2 ^ dim)`, the input the all-zeros
`CVector (2 ^ dim)`, the success probability a weighted sum of squared ℓ² norms
of projected vectors — and proved by *transfer* from
[`../Standard/`](../Standard), re-proving nothing in `Framework/`,
`Implementation/` or `Submission/`.

`Model/Standard/` is a model of every semantic class the development is stated
over. It is infinite-dimensional by necessity: `RegEncoding` admits registers on
arbitrarily large qubit names, so no fixed `dim` can carry the class. That makes
it a witness of consistency but not the finite matrix picture a reader coming
from SQIR expects. This folder supplies that picture, for the sublanguage the
headline theorems actually run on — `LowGate`.

Status: **`ql_submission_correct`, `ql_policy_submission_correct` and
`ql_Shor_correct_approx_lowered` are proved** (`Headline.lean`), and depend on
no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Why QuantumLib is vendored

The natural choice would be to depend on
[inQWIRE/LeanQuantum](https://github.com/inQWIRE/LeanQuantum) as a package.
No commit of it builds on this repository's toolchain. QuantumLib's
`lean-toolchain` history is

| commit | date | toolchain |
|---|---|---|
| `977f1f04` | 2025-05-11 | `v4.20.0-rc5` |
| `6f70dcd1` | 2025-12-10 | `v4.26.0-rc2` |
| `f2af8ad4` | 2026-04-24 | `v4.30.0-rc2` (current `main`) |

and this repository is pinned at `v4.28.0` with Mathlib at `fadcf92b`. It never
passes through `v4.28.0`, so a `require` would mean moving the toolchain, a
development-wide change.

So `Vendored.lean` transcribes the dozen declarations this folder uses, from
`main` at `44fc4eb1f4ba512e659deacd3468fda0a764d162`, with a header naming the
source files. **What this does and does not buy:** the theorems below mention
*these* definitions. They are the upstream ones character-for-character — only
the `import` lines and the surrounding namespaces differ, and the `kron` lemma
proofs are redone locally because the upstream ones use `Quantumlib.Tactic` —
so swapping this file for a real `require` later is mechanical and changes no
statement. Until that swap, the guarantee is "equal to QuantumLib's definitions
as transcribed here", not "shares a kernel object with QuantumLib".

## Bit order

Index `k : Fin (2 ^ dim)` is the basis state whose qubit `i` is
`Nat.testBit k i`. **Qubit `0` is the least significant bit of the index**,
which is `RegEncoding`'s own convention (`bit_eq_testBit_toNat`). QuantumLib's
`kron` makes the *left* factor the high digit, so a gate on qubit `q` of `dim`
pads with high qubits on the left:

```
(1 : CSquare (2 ^ (dim - q - 1))) ⊗ gate ⊗ (1 : CSquare (2 ^ q))
```

## Invariants

- **Outbound.** Files here import `Model/Standard/`, `Framework/`, Mathlib and
  `Vendored.lean`; `Headline.lean` additionally reaches into
  `Implementation/Shor/Main` and `Submission/Correct`, the way
  `Standard/Headline.lean` does.
- **Inbound.** *Nothing outside this folder imports anything in it.*
  ```
  grep -rln "ShorVerification.Model.QuantumLib" FastMultiplication FastMultiplication.lean \
    --include='*.lean' | grep -v "ShorVerification/Model/QuantumLib/"
  ```
  must print nothing.
- **Additive.** Nothing outside this folder is created or edited, including
  `lakefile.lean` and `lake-manifest.json`.

## Building it

```
lake build FastMultiplication.ShorVerification.Model.QuantumLib.Headline
```

`Headline.lean` imports everything else here, so this one command checks the
whole folder. The folder is not in the library root, so
`lake build FastMultiplication` does not see it.

## The files

| file | provides | imports |
|---|---|---|
| `Vendored.lean` | `CMatrix`/`CVector`/`CSquare`, `Matrix.kron` with `⊗`, `hadamard`, `cnot`, `swap`, `phaseShift`, `ket0`/`ket1` | Mathlib |
| `Embed.lean` | `idxBasis`/`basisIdx`, `Below`, the embedding `ι dim : CVector (2 ^ dim) →ₗ[ℂ] State`, `cnorm2`, and the transfer principle `transfer_of_ket` | `Standard/State`, `Vendored` |
| `Denote.lean` | `maxQubit`, `permMatrix`, `diagMatrix`, `hMatrix`, `denote dim : LowGate → CSquare (2 ^ dim)`, and `denote_unitary` | `Embed`, `Standard/LowGates` |
| `Native.lean` | the sanity lemmas: `denote` of `H`, `CNOT` and `Phase` equals the `kron`-padded `hadamard`, `cnot`, `phaseShift` | `Denote` |
| `Transfer.lean` | per-primitive commutation lemmas and `transfer : evalL C (ι v) = ι (denote C * v)` | `Denote` |
| `Measure.lean` | the projector matrices `proj dim r o`, the Born rule `probMeas_ι`, and the bridge `probability_of_success_eq` | `Transfer`, `Framework/Contract` |
| `Headline.lean` | the three headline theorems over matrices | everything, plus `Implementation/` and `Submission/` |

## How it works

- **Embedding.** `ι dim` sends `v : CVector (2 ^ dim)` to
  `∑ k, v k 0 • ket (idxBasis dim k)`. It is injective and ℓ²-isometric
  (`norm_sq_ι`). `Matrix`'s own norm instance is the *sup* norm, so the ℓ²
  quantity is named explicitly as `cnorm2` and never left implicit: `ι` is a
  linear map plus an explicit norm identity rather than a bundled isometry, so
  no statement silently means the wrong norm.
- **Gates by entries, not by padding.** Every primitive's matrix is given
  directly by its entries, reusing the basis maps `Standard/BasisMaps.lean`
  already proves bijective. Padding casts are quarantined in `Native.lean`;
  nothing in `Transfer.lean` or `Headline.lean` depends on that file.
- **Arithmetic gates are permutation matrices.** `ShiftL`, `ShiftR`, `Negate`,
  `AddScaled`, `signExtend`, `signDealloc` and `RadixReverse` are not gates in
  QuantumLib or any other library. They enter as permutation matrices, which
  is faithful: the development charges them through `shorGateCostModel`, not
  as Toffolis. Decomposing them into Toffolis with proofs is a separate
  project.
- **`Below` and `maxQubit`.** A basis permutation restricts to `Fin (2 ^ dim)`
  exactly when it preserves "uses only qubits `< dim`" in both directions
  (`BelowStable`). Every low gate writes one register, so this reduces to
  `mWriteNat_agree_off` once `maxQubit` bounds that register. `maxQubit` counts
  an `ExtReg`'s **reserve** as well as its active part, because `signExtend`
  writes reserve bits.
- **`adj`.** `evalLG (†U)` is `(evalLG U).symm` while `denote (†U)` is
  `(denote U)ᴴ`; they agree because `denote U` is unitary, which is where
  `denote_unitary` is used.
