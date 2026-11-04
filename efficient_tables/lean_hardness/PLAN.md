# Concrete Mahaney / sparsity barrier on complexitylib — DONE 2026-10-12

Headline (no sorry; axioms propext, Classical.choice, Quot.sound only):
- `Mahaney.mahaney : Sparse S → NPHard S → P = NP`            (Mahaney/Theorem.lean)
- `Mahaney.tableOpt_barrier : NPHard TableOptLang → P = NP`    (Mahaney/TableLang.lean)
P, NP, FP, ≤ₚ, NPHard and Cook–Levin are complexitylib's (multi-tape TMs, Arora–Barak style),
pinned at complexitylib 3f4b5fe, Lean v4.35.0-rc3. Contract files are vendored as a snapshot
from ShorTableOptimization main (vendor/).

Files
- Bits.lean       MSB-first `val`/`bits`, lexicographic order = numeric order, bounded form.
- Strings.lean    string equality and the lexicographic test are FPPred.
- Left.lean       the left set of SAT, `LeftSAT_mem_NP` (discharges old `hleft`).
- Core.lean       abstract Ogihara–Watanabe pruning core (port of Workbench MahaneyCore).
- ListAlg.lean    list version of the pruning algorithm; agrees with Core on levels ≤ n.
- Blocks.lean     index forms (fixed-width blocks, filters, children).
- Machine.lean    machine state, stages A/B, `stepS ∈ FP`.
- Step.lean       `stepS_encS`: the step writes the next level's encoding.
- Theorem.lean    loop in FP (`iterS_mem_FP`), `decides_sat`, `mahaney` (discharges `hclosure`).
- SparsityBarrier.lean  port of the Workbench file (table problem, OPT ≤ 15k(2k−1); its abstract
                  `barrier` theorem is superseded).
- TableLang.lean  encoding `pair (modeBit :: 1^k) (K.bits)`, `reduceS ∈ FP`, `CoreL_sparse`,
                  `tableOpt_barrier`.

Modelling choices to state in the paper: k in unary (benchmark size parameter), K in canonical
binary (Nat.bits); malformed strings are NO instances. Sparse = census ≤ polynomial in length.

Build: `lake build` (first build compiles ~2.3k complexitylib modules, ~20 min on this Mac).
Audit: `lake env lean Mahaney/Audit.lean`.
