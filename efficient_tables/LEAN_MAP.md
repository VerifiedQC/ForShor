# Paper-to-Lean map

Which statements of `paper/Exact_Table_Algorithm_Model_and_Limitations.tex` are machine-checked, which are checked only in a different or weaker form, and which are paper-only. Read this together with the "What is and is not claimed" section of the [README](README.md).

**How to read the table.** *Domain* says what the Lean statement quantifies over. *Status* is one of:
**checked** (a Lean theorem states this), **checked, narrower** (a Lean theorem states a restricted or differently packaged version, described in the row), **related** (Lean proves something nearby, not the paper's claim), **paper-only** (no Lean statement).
*Read* is **yes** where the Lean statement itself was read when this map was written, and **name** where it was identified from its name, file and surrounding comments only. Names are fully qualified; the file is given so that `lake env lean` can find it. The declarations in bold, and those named in the audit section at the end, were axiom-audited; see [`scripts/AxiomAudit.lean`](scripts/AxiomAudit.lean) and the audit section below.

No Lean statement in this repository concerns the Fortran solver, the finite macro search as an algorithm, or any running time of an algorithm.

## 1. Model (paper §2)

| Paper | Lean declaration (file) | Domain | Status | Read |
|---|---|---|---|---|
| Legal tables on fixed points (§2.2, §2.3) | `Paper.F2CatalogTransfer.F2Source` (`Provider/Ladders/CatalogTransfer.lean`) | tables of arity `k ≤ K` with a program of any length that is source-legal (legal operations, ordered consumption of points, registers restored, `ProgConsumesPtsSafe`) and whose points are a permutation of `f2Points k`; no interpolation certificate in this domain | definition of the model | yes |
| Child width from the historical scanner (§2.4) | `Paper.F2CatalogTransfer.F2Source.childWidth`; `Paper.ArrayBridge.nextBalancedSignedWidth_eq_scanner` (`Model/Scanner/ArrayScanner.lean`) | any program; the array form of the scanner equals the scanner | checked | name |
| Recursive objective, charges 1/3/1 (§2.5) | `Paper.F2CatalogTransfer.rawProblem`, `Paper.PPEndToEnd.ppProblem`, `PPPolicy.benchmarkCost` | policy cost for a shared ladder; the leaf price is a parameter | definition of the model | yes |
| Rounded rotation price equals its exact integer form (§2.5) | `Paper.PPEndToEnd.tauRS_eq_tauExact` (`Planner/TauPrice.lean`) | all `R : ℕ` | checked | yes |
| A table matters only through its profile and charge (§2.4) | `Paper.Planner.childWidth_eq_of_peaks`, `widthTrace_eq_of_used_peaks`, `planCost_le_of_used_peaks_and_charges` (`Model/Scanner/Planner.lean`) | any profiles `p, q : ℕ → Profile`; equal used peaks give equal child widths and width traces, and a ladder with equal peaks and no larger charges costs no more | checked | yes |
| The level term `8·N·(w'−1)·χ` of the objective | (no Lean statement located) | | paper-only | name |

## 2. Lemmas and theorems (paper §3–§5)

| Paper | Lean declaration (file) | Domain | Status | Read |
|---|---|---|---|---|
| **Lemma 1**, first sentence: every feasible cap has a minimum-charge witness of charge at most `27k³` | `Paper.F3ChargeCeiling.feasible_has_ceiling_grouped`, `minCharge_le_27_cube` (`Provider/Ceiling/FinalCeiling.lean`) | all `k ≥ 2`, all `K`, all feasible caps; no hypothesis on a baseline | checked (unconditional) | yes |
| **Lemma 1**, second sentence: an explicit constructor has profile offsets at most `8k²` | `Paper.F3ChargeCeiling.groupedLiteralBaseline_peaks`, `grouped_bounded_baseline` (`Provider/Ceiling/GroupedPeak.lean`, `Provider/Ceiling/FinalCeiling.lean`) | `2 ≤ k ≤ K`; **for the repository's grouped literal (C1) baseline, not for the paper's paired constructor** | checked, for a different construction | yes |
| **Lemma 1**, second sentence: an explicit constructor has charge `O(k²)` (the grouped literal baseline) | `Paper.F3ChargeCeiling.groupedLiteralBaseline_charge` (`= 4·(k−1)·(2k−3)`, exact) and `…_charge_le` (`≤ 8k²`) (`lean/Provider/Ceiling/GroupedCharge.lean`) | `2 ≤ k ≤ K`; the same baseline whose legality and `8k²` peaks are checked | checked | yes |
| **Lemma 1**, second sentence: the *paired* constructor has charge `c₀ ≤ 6k²` | `PairedCharge.charge_formula`, `PairedCharge.charge_le` (`lean/Foundations/PairedCharge/`): the instruction skeleton has charge `4k²−7k+2+ν ≤ 4k²−6k+1 ≤ 6k²` | counting only: an explicit list of instruction kinds; **not** a legality proof | checked, narrower (counting only) | yes |
| **Lemma 1**, second sentence: the paired constructor is a legal table with offsets `≤ 8k²` | none | | paper-only (not independently reviewed) | yes |
| **Lemma 2** (primitive normalization: rows primitive between charged macros, `O(k³)` instructions, no larger scan peaks) | related: shift compression and exact-profile padding, `Paper.WholeCompression.compressWhole_charge`, `compressWhole_length`, `Paper.CompressionTrace.compressWhole_trace`, `Paper.CompressionComplete.complete_exact_profile`, `complete_charge` | any program; compression preserves charge, trace and scanner caps | related; the primitivity and parity argument has no Lean statement | name |
| **Lemma 3** (threshold saturation, `θ ≤ S(k)`, eq. 13) | none for the lemma. Its integer-programming ingredient is `SmallPoint.small_integer_point` (`lean/Foundations/SmallPoint/`) | integer `A, b` with entries at most `B`: an integer point implies one with coordinates at most `(t+1)·t!·B^t` | paper-only; ingredient checked | yes |
| **Lemma 3**, encoding step (all pattern-system constants at most `8k²`) | the separation criteria it rests on are checked: `SeparationLemmas.peeling`, `zero_criterion`, `integrality_anchored` (`lean/Foundations/SeparationLemmas/`): for a gap-separated finite family of signed powers of two, the total is `0` iff every cluster sum is `0`, and with an anchor it is an integer iff the clusters below the anchor vanish and the anchor's cluster sum is an integer. The rest (occurrence structure of the table templates, the pattern polyhedron, the small constants) is prose in `proof_notes/threshold/ENCODING_LEMMA.2026-10-28.md`, reviewed but not machine-checked | abstract finite families over `ℚ` | checked for the separation criteria; paper-only for the rest | yes |
| **Theorem 4** (finite macro search returns the exact threshold and a minimum-charge table) | none for the algorithm. Related: an exhaustive minimum-profile provider, `Paper.EffectiveProvider.effective_optimal_raw_F2_policy` (`Provider/Effective/Complete.lean`), `Paper.F2CatalogTransfer.optimal_raw_F2_policy_exists` (`Provider/Effective/Existence.lean`) | existence of minimum-profile entries by exhaustive search | related; not the paper's algorithm | name |
| **Theorem 5** (global exactness in the declared model) | **`Paper.ComputableProfileProvider.optimal_raw_F2_exact`** (`Provider/Effective/ProfileExact.lean`); `…optimal_raw_F2_allK` (`Provider/Effective/ProfileAllK.lean`); `Paper.EffectiveProvider.effective_optimal_raw_F2_exact` (`Provider/Effective/ExactPP.lean`) | for every `K ≥ 2`, root width `W` and multiplicity `N`: the policy built from the provider is semantically correct for all `θ` and all signed `W`-bit inputs, its `tauRS` and `tauExact` costs agree, and its cost is at most that of **every** ladder `l : List (F2Source K)` with one table per arity (all source-legal literal-F2 tables of arity `≤ K`, programs of any length) | checked, narrower: a pointwise statement per `(K, W, N)`; it proves the optimum exists and is attained by the provider's policy, not that the paper's FPT algorithm computes it | yes |
| "Complete finite witness through arity `K`" (README's "main theorem") | `Paper.PPEndToEnd.pp_through_arity_K` (`PhaseProduct/Catalog/EndToEnd.lean`) | existential over a catalogue of verified candidates, one per arity `2..K`; optimal only **relative to that catalogue** | checked, narrower (weaker than Theorem 5) | yes |
| Planner as an integer program with one unknown per distinct arity (§5.2) | related: `Paper.AffineILP.step_divisor_residue` (`ILPEncoding/Affine/Core.lean`), `Paper.F6ILP.variable_count` (`ILPEncoding/Labels/ILPChecked.lean`), `ILPEncoding/Affine/Offsets.lean` | the affine width recurrence and the count of variables | related; the equivalence of the optimum with integer-program feasibility and Kannan's theorem have no Lean statement | name |
| Certificates for feasibility and optimality (§5.3, §5.4) | none | | paper-only | n/a |

## 3. Complexity (paper §6)

| Paper | Lean declaration (file) | Domain | Status | Read |
|---|---|---|---|---|
| Local search bound (24), (25) and full bound (26): `2^{O(K⁴ log K)}·poly(n)` | none | | paper-only | n/a |
| Counting lemmas behind the outer search (words, calls, factorial of distinct arities) | `Paper.CountStage.TypedWordRuntime.recursiveCalls_le_enumeratedSize_bound` (`Foundations/Counting/RecursiveCalls.lean`), `Paper.BoundedThreshold.searchEntries_length_le` (`Provider/Effective/Size.lean`), `Paper.CountStage.OuterComplexity.distinct_dimension_power_le_budget_power`, `conditional_solver_cost_le_budget_power` | counting statements; the solver cost is a hypothesis | related | yes |
| Arithmetic composition of stage-wise cost bounds into `2^{611·c·K⁴·bl K}·(n+1)^{e(11+3c)+2c+4}` | `RuntimeComposition.composition` and its lemmas (`lean/Foundations/RuntimeComposition/`) | hypotheses (H1)–(H3) are contracts on stage costs, including Kannan's theorem; nothing shows an algorithm satisfies them | checked, narrower: arithmetic only | yes |

## 4. Hardness and sparsity (README; not in the paper)

The paper does not contain these statements. They live in the separate Lake project `lean_hardness/`.

| Statement | Lean declaration | Status |
|---|---|---|
| Mahaney: a sparse NP-hard set implies P = NP | `Mahaney.mahaney` | checked |
| The structural-score language with `k` in unary has no many-one NP-hardness unless P = NP | `Mahaney.tableOpt_barrier` | checked |
| Same barrier for a unary-`n` policy language whose optimum is polynomially bounded (the bound is a hypothesis; the T-count model is not formalized) | `Mahaney.policyOpt_barrier` | checked, narrower |
| NP-hardness of the structural score when the points are supplied as input, already at arity 2 | `Pts.genLang_NPHard` | checked; not a T-count statement and not for the KMY points |

## 5. Not in Lean

* The Fortran solver and its outputs (the reproducible costs in `REPRODUCING.md`).
* The finite macro search, the saturation bound, the pattern-system encoding and every running-time bound, except the arithmetic composition above.
* The paper's worked examples and the twelve limitations (prose).

## 6. Axiom audit (2026-10-28)

[`scripts/AxiomAudit.lean`](scripts/AxiomAudit.lean) runs `#print axioms` on seventeen declarations from the table above. Result:

* `Paper.ComputableProfileProvider.optimal_raw_F2_exact`, `…optimal_raw_F2_allK`, `Paper.EffectiveProvider.effective_optimal_raw_F2_exact`, `…effective_optimal_raw_F2_policy`, `Paper.F2CatalogTransfer.optimal_raw_F2_policy_exists`, `Paper.PPEndToEnd.pp_through_arity_K`, `…optimized_pp_end_to_end`, `…tauRS_eq_tauExact`, `Paper.F3ChargeCeiling.feasible_has_ceiling_grouped`, `…minCharge_le_27_cube`, `…groupedLiteralBaseline_peaks`, `…grouped_bounded_baseline`: **only `propext`, `Classical.choice`, `Quot.sound`**.
* `Paper.Planner.childWidth_eq_of_peaks`, `…widthTrace_eq_of_used_peaks`, `…planCost_le_of_used_peaks_and_charges`: only `propext`.

`Paper.F3ChargeCeiling.groupedLiteralBaseline_charge` and `…_charge_le`: only the three standard axioms (`scripts/AxiomAudit.lean` therefore audits seventeen declarations).

The new developments `lean/Foundations/SmallPoint/`, `lean/Foundations/RuntimeComposition/`, `lean/Foundations/SeparationLemmas/` and `lean/Foundations/PairedCharge/` carry their own `Audit.lean` files with the same result (`PairedCharge.charge_classes` only `propext`).

**Dependency closure.** The 96 repository modules that `A2Profile.Exact` imports (and five more for the neighbouring theorems) were scanned for `sorry`, `admit`, `axiom`, `native_decide`, `ofReduceBool`, `unsafe`, `opaque`, `partial`, `implemented_by` and `extern`, comments stripped: no hits. Four modules (`Paper.SourceP6Parity`, `Paper.SourcePf4Parity`, `Paper.SourcePf4`, `Paper.BestKnownContract`) set `maxRecDepth 100000`; this raises a recursion limit and does not affect soundness.

**How it was run.** After the reorganization into dependency layers, `lake build EfficientTables EfficientTablesHelpers` completed without errors (8241 jobs, 2026-10-28, Lean 4.28.0, Mathlib `fadcf92b…`), and `lake env lean scripts/AxiomAudit.lean` was run from the repository root. Before that, the 96-module closure of `optimal_raw_F2_exact` had been compiled module by module in a separate workbench with the same toolchain; both runs agree. The Mathlib cache used was a copy built at the same pinned revision. Declarations in the table that are not listed above (for example the compression and shift-compression theorems, the affine integer-program algebra, the counting lemmas, and everything in `lean_hardness/`) were not audited by this procedure; `lean_hardness/` has its own audit files.

## 7. Corrections to earlier statements in this repository's documents

* The charge ceiling `27k³` is proved **unconditionally** (`feasible_has_ceiling_grouped`); it does not depend on a baseline hypothesis.
* `Paper.PPEndToEnd.pp_through_arity_K` is not the strongest optimality theorem here. `optimal_raw_F2_exact` is optimal over all source-legal literal-F2 tables (one table per arity) at fixed `(K, W, N)`.
* **Lemma 1's constructor.** Lean proves the `8k²` offsets and, as of 2026-10-28, the charge `4(k−1)(2k−3) ≤ 8k²` for the repository's grouped literal (C1) baseline. An earlier version of this table credited the offsets bound to the paper's *paired* constructor; that was wrong. The paired constructor's charge bound `6k²` is machine-checked only as a count of its instruction skeleton (`lean/Foundations/PairedCharge/`); its legality is a paper proof that has not been independently reviewed.

