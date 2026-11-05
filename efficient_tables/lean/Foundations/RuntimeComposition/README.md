# RuntimeComposition: arithmetic composition of stage-wise cost bounds

Machine-checked **arithmetic composition**, not a runtime theorem about any algorithm. It takes stage-wise cost
contracts as hypotheses and derives an explicit total bound. Informal statement and proof:
`../../../proof_notes/formal/runtime_composition.tex`.

| Lean theorem | Informal statement |
|---|---|
| `RuntimeComposition.S_le_two_pow` | `S(k) ≤ 2^(70·k²·bl k)` for `k ≥ 2` |
| `RuntimeComposition.tt_le_factorial_sq` | `t^t ≤ (t!)²`, hence `t! ≤ U` gives `t^(c·t) ≤ U^(2c)` |
| `RuntimeComposition.triple_count_le` | the number of triples `(k,d,C)` is at most `28·K⁵` and at most `2^(5+5·bl K)` |
| `RuntimeComposition.local_factor_bound` | the local factor is at most `2^(600·c·k⁴·bl k)·(m+1)^c` under the cutoff contract |
| `RuntimeComposition.composition` | with hypotheses (H1)-(H3): `Total ≤ 2^(611·c·K⁴·bl K)·(n+1)^(e(11+3c)+2c+4)` |

Scope. The hypotheses are contracts on the local-query cost, the width cutoff and the outer integer-program cost
(Kannan's theorem enters only as this contract). Nothing here shows that any algorithm satisfies them. In
particular the `2^{O(K⁴ log K)}·poly(n)` running time of the paper is **not** formalized as a statement about the
algorithm; only this composition is. See `Audit.lean` for axioms.
