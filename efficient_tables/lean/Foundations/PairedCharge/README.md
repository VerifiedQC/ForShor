# PairedCharge: charge accounting of the paired constructor

Machine-checked **counting** of the charged instructions of the paired constructor's instruction skeleton at
arity `k` (the construction of `../../../proof_notes/formal/paired_charge.tex`; its source is the "paired F2
constructor" of the proof notes). Informal statement and proof: `../../../proof_notes/formal/paired_charge.tex`.

| Lean theorem | Statement |
|---|---|
| `PairedCharge.points_def` | the point list `0, ∞, −1, +1, −2^−j, +2^−j, −2^j, +2^j, …` and the count `fMinus` of negative fractional points are as described |
| `PairedCharge.charge_classes` | positive addition costs 1, negative addition 3, negation 1, shifts and checkpoints 0 |
| `PairedCharge.skeleton_unfold` | the skeleton is the stated concatenation of pair blocks, the singleton block and the negations |
| `PairedCharge.charge_formula` | `cPair k = (k−2)(4k−3) + 4(k−1) + ν = 4k²−7k+2+ν`, with `fMinus k = (k−1)/2` and `ν ≤ k−1` |
| `PairedCharge.charge_le` | `cPair k ≤ 4k²−6k+1 ≤ 6k²` for `k ≥ 2` |

**Scope: counting only.** This proves arithmetic about an explicitly described list of instruction kinds. It does
**not** show that the skeleton is a legal table (registers restored, markers see the required rows), nor anything
about shifts or scan peaks. Legality of the paired constructor remains a paper proof (not independently
reviewed). For a constructor whose legality is machine-checked, see `../../Provider/Ceiling/GroupedCharge.lean`.
