# SmallPoint: a small integer point in a polyhedron

Machine-checked proof of the elementary integer-programming bound used for the saturation cutoff `S(k)`.
Informal statement and proof: `../../../proof_notes/formal/small_integer_point.tex`.

| Lean theorem | Informal statement |
|---|---|
| `SmallPoint.cofactor_extreme` | an extreme vector of the cone is a positive multiple of an integer vector with entries in `[0, t!·B^t]` (Lemma 1) |
| `SmallPoint.extreme_decomposition` | every vector of a pointed cone given by finitely many rows is a finite sum of extreme vectors (Lemma 2) |
| `SmallPoint.conic_caratheodory` | a sum of extreme vectors in dimension `t+1` reduces to at most `t+1` of them with positive coefficients (Lemma 3) |
| `SmallPoint.small_integer_point` | **Theorem 1.** If `{x ≥ 0, Ax ≤ b}` (integer `A`, `b`, entries bounded by `B ≥ 1`) has an integer point, it has one with every coordinate in `[0, (t+1)·t!·B^t]` |

Scope. This proves the bound itself and nothing about how it is used: the saturation theorem and its
`2^{O(k² log k)}` cutoff, the pattern-system encoding and the algorithm are paper proofs.
The definitions `coneK`, `IsExtremeVector`, `polyhedronInt`, `HasIntegerPoint` are in `Defs.lean`.
Generated with the autoformalizer, then statements reviewed by hand and axioms re-checked: see `Audit.lean`.
