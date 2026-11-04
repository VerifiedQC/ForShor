# SeparationLemmas: zero and integrality criteria for signed sums of powers of two

Machine-checked proof of the separation criteria used in the encoding lemma
(`../../../proof_notes/threshold/ENCODING_LEMMA.2026-10-28.md`, section 3). Informal statement and proof:
`../../../proof_notes/formal/separation_lemmas.tex`.

| Lean theorem | Informal statement |
|---|---|
| `SeparationLemmas.peeling` | if the low part's exponents are at most `A`, the rest's are at least `B ≥ A + H`, there are fewer than `2^H` terms and the total lies in `2^B ℤ`, then the low part sums to `0` |
| `SeparationLemmas.zero_criterion` | for a gap-separated family, the total is `0` iff every cluster sum is `0` |
| `SeparationLemmas.integrality_anchored` | with an anchor term (coefficient `0`, exponent `0`), the total is an integer iff every cluster below the anchor's sums to `0` and the anchor's cluster sum is an integer |
| `SeparationLemmas.definitions_unfold` | the definitions `GapSep`, `clusterSum`, `total` are what the note says |

Scope. This proves the two criteria for an abstract finite family of signed powers of two (exponents in `ℤ`,
values in `ℚ`). It says nothing about tables, the pattern-system encoding or any algorithm; those are paper
or prose proofs. Generated with the autoformalizer; statements read by hand and axioms re-checked (see `Audit.lean`).
