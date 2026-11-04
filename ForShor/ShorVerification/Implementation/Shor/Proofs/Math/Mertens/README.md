# `Vendor/Mertens/`

Third-party Lean source, vendored. **Delete this directory once the Mertens
pull requests below are merged and the project's Mathlib pin includes them**
(see "Removal").

## What is here and why

The `κ = 1/π²` success constant rests on the Mertens-type totient bound

    φ(r)/r ≥ 1 / (4 · log (log₂ N + 1)).

For `r < 2^2048` that is proved from scratch in
`Implementation/Shor/Math/TotientBounds.lean` with no analytic input beyond
`Real.log_two_gt_d9`. The complementary range needs **Mertens' third theorem
with an explicit error term**, which is
[leanprover-community/mathlib4#41394](https://github.com/leanprover-community/mathlib4/pull/41394)
(stacked on #44061 → #44062) and is **not merged**. Its three files are copied
here. Everything they depend on is in the pinned Mathlib.

## Provenance

| File | Upstream path | Source |
|---|---|---|
| `Weight.lean` | `Mathlib/NumberTheory/Mertens/Weight.lean` | `teorth/mathlib4` branch `mertens-second-theorem`, commit `4d8a5a87c1b30ad9c7a6ce45a5c4aa6e07dd1ddc` (2026-10-01) |
| `Construction.lean` | `Mathlib/NumberTheory/Mertens/Construction.lean` | same |
| `Theorems.lean` | `Mathlib/NumberTheory/Mertens/Theorems.lean` | same |

All of it is Apache-2.0, © the Mathlib contributors; the upstream copyright
headers are preserved verbatim at the top of each file, and authors are named
there.

This project pins Mathlib at master commit
`4dc43842a11f257ffba2a611c943a133a65cb4b2` (Lean v4.36.0-rc1).

## What was changed

Every deviation from the upstream text is marked with a `-- ADAPTED:` comment
naming the upstream spelling. They fall into three groups:

1. **Tactic behaviour.** Where `grw`, `gcongr`, `convert` or `positivity`
   behave differently from the upstream toolchain, the step is written out
   directly. In particular, `gcongr`'s side goals are discharged by trying each
   of the upstream closing terms, so the proofs do not depend on the order in
   which they are emitted, and three `convert … using 1` steps in
   `Construction.lean` are replaced by `HasDerivAt.congr_deriv` or a direct
   limit computation, because `convert` here also splits instance arguments.
2. **Measurability.** `Weight.lean` adds two `@[fun_prop]` lemmas,
   `Measurable.sum_Ioc_floor` and `Measurable.sum_Icc_floor`, stating that
   `x ↦ ∑ n ∈ Icc 0 ⌊h x⌋₊, g n` is measurable when `h` is. Upstream's
   `fun_prop` calls rely on this.
3. **Trimming.** `Theorems.lean` stops after `E₃_bound` and its immediate
   corollaries; the asymptotic results upstream derives from it are unused
   here.

Nothing was weakened: the statements of `prod_prime_one_minus_inv_eq_nat` and
`E₃_bound`, the only two results this repository consumes, are the upstream
statements verbatim.

## Consumers

`Implementation/Shor/Math/TotientBoundsLarge.lean` is the only file that imports
anything here.

## Removal

Once #41394 is merged and the Mathlib pin includes it:

1. delete this directory;
2. in `Math/TotientBoundsLarge.lean`, replace
   `import ...Vendor.Mertens.Theorems` with
   `import Mathlib.NumberTheory.Mertens.Theorems`;
3. `lake build` — the proof should go through unchanged, since it uses only
   `Mertens.prod_prime_one_minus_inv_eq_nat` and `Mertens.E₃_bound`.
