# Points as input: NP-hardness of GenTableOpt (started 2026-10-12)

Problem GenTableOpt(k, pts, K): the ShorTableOptimization contract and score A + 5L unchanged; the
instance supplies k, a list of distinct points (arbitrary integers/fractions) and K.

Reduction (k = 2): Edge-Hamiltonian path in H (Hamiltonian path of the line graph; Bertossi,
IPL 13 (1981) 157-159) ↦ points {0} ∪ {8^a + 8^b : ab ∈ E(H)}, K = 7(|E|+1).

Key lemmas
- det invariant: every reachable 2×2 state (safe ops) has det ±2^t.
- gap lemma: m ops between markers for a, b ⇒ b − a = y·(±2^t), y an entry of the transfer
  matrix; m ≤ 1 ⇒ W1(b−a) (0 or ±2^p), m = 2 ⇒ W2(b−a) (sum of two signed powers).
- sparse/NAF uniqueness: Σ_{Pos} 8^i − Σ_{Neg} 8^i is W2 only if |Pos|+|Neg| ≤ 2.
- cost: A + 5L ≥ 5n + Σ_steps c(x,y), c = 0 if equal, else 2 + [¬W2]; equality ⇒ Ham path.

Stages
1. Reduction correctness (this folder): EdgeHamPath E ↔ GenTableOpt (2, P_E, 7(|E|+1)).
2. Encodings + reduction ∈ FP (complexitylib).
3. NP-hardness of EdgeHamPath from 3SAT (or another formal source).

## Status 2026-10-12 — Stage 1 DONE
`Pts.reduction_correct : E.Nodup → (∀ e ∈ E, e.card = 2) →
   (EHP E ↔ GenTableOpt 2 (pointsOf E) (7 * (E.length + 1)))` — no sorry, standard axioms.
Files: Weight.lean (W1/W2, NAF uniqueness, base-8 sums, dyadic integrality), Gap.lean (det
invariant, transfer coefficients, gap lemma), LowerBound.lean (GenTableOpt, run_bound, extract),
Reduction.lean (labels 8^a+8^b, explicit 2-ops-per-step schedule, the iff). Audit: Points/Audit.lean.
Next: Stage 2 (encodings, map ∈ FP) and Stage 3 (EHP NP-hard: 3SAT → Ham path → Bertossi gadget).

## Status 2026-10-12 — Stage 2 DONE (Points/Encode.lean)
- Encodings: graph = pair 1^n M (n×n adjacency matrix, edges a<b with M[a n + b], index order);
  table instance = pair 1^k (pair K.bits (encL (pts.map encPt))), encPt = tag/sign bits + |z| bits.
- `Pts.ehp_le_gen : EHPLang ≤ₚ GenLang` (redG ∈ FP, complexitylib TMs), and
  `Pts.genLang_NPHard_of : NPHard EHPLang → NPHard GenLang`. No sorry; standard axioms.
- Stage 3 target: `NPHard EHPLang` for exactly this adjacency-matrix encoding.

## Status 2026-10-12 — Stage 3 underway (see STAGE3_DESIGN.md)
- Design validated by brute force: SAT → DHC₂ (6-node cell + rotating clause cycles), DHC₂ → EHC
  (split + pendant), EHC → GenTableOpt (cycle version).
- DONE: `Pts.cycle_reduction : EHC E ↔ GenTableOpt 2 (pointsC E) (7 * E.length)` (Points/CycleTable.lean).
- NEXT: split/pendant lemma (Points/Split.lean), then SAT → DHC₂, then encodings/FP.
- DONE: `Pts.dhc_iff_ehc` (Points/Split.lean, Cyclic.lean, SplitBack.lean) and the composite
  `Pts.dhc_iff_table : DHC D ↔ GenTableOpt 2 (tableOf D) (7 * (3n + |arcs|))` for out-degree ≤ 2
  digraphs (Points/DhcTable.lean). No sorry; standard axioms.
- NEXT: 3b SAT → DHC₂ (cells + rotating clauses; design/dhc3.py), then 3c encodings/FP.

## Status 2026-10-13 — Stage 3b DONE (SAT → DHC₂ → table, correctness)
- Construction indexed by token positions (design/dhc_tok.py; 480 random CNFs, 0 mismatches):
  rows of T cells per variable x < T, clause cycle r_a…r_b, q_b…q_a per clause span.
- Files: SatGraph.lean (vertices, outs, `dig_ok`, `dig_out2`), DigSigma.lean (DHC ⇔ successor
  maps), SatNo.lean (cycle ⇒ assignment: `cell_cases` finite lemma, rows, `clause_entry`),
  SatYes.lean (assignment ⇒ cycle via orbit segments), SatCnf.lean (`TS.sat_iff_dhc`,
  `sat_iff_table`). No sorry; standard axioms.
- NEXT 3c: FP map from φ.encode to encG 2 (tableOf dig) K; WF test; then NPHard GenLang.

## Status 2026-10-13 — Stage 3c DONE: `Pts.genLang_NPHard : NPHard GenLang`
- SatParse.lean: 4-state scanner for CNF syntax, `valid_iff : z ∈ Valid ↔ ∃ φ, z = φ.encode`,
  `Valid ∈ P` via complexitylib `TM.scannerTM`; `ofBits_encode` (tokens read off bits).
- SatLab.lean: explicit bits of 8^a+8^b−9 (`dBits`, `encPt_dl`).
- SatOuts.lean: out-neighbours in closed form (`outs_eq`).
- SatFP.lean: token predicates / closed forms are FPPred / UnaryFn.
- SatRed.lean: `encL_tableOf`, `satRed`, `satRed_correct`, `satRed_mem_FP`,
  `sat_le_gen : SAT.language ≤ₚ GenLang`, `genLang_NPHard : NPHard GenLang` (from complexitylib's
  Cook–Levin `SAT.NPHard_language`).
- Audit: Points/Audit4.lean — standard axioms only (propext, Classical.choice, Quot.sound), no sorry.
