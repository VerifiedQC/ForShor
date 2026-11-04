# proof_notes: the research packages cited by the paper

These are the prose proofs and review records behind the paper's bibliography entries `threshold`, `outer`, `profile` and `normalization` ("Local research package, 15 October 2026"). They were previously not shipped. They are **verbatim copies** of working notes: filenames keep their development timestamps, and relative links between notes may point to files that are not included.

## Status of these proofs (read before citing)

* They are **prose proofs**, not machine-checked. The `FORMAL_CERTIFICATE` files record only a handful of elementary integer implications replayed in a Lean workbench. The saturation theorem, the symbolic threshold reduction, the runtime analysis and the recursive optimizer are **not** formalized.
* Each package was reviewed by independent agent reviewers who recorded "no blocking defect". Those reviews are internal and are not external refereeing. One step, the `8k^2` coefficient bound in `threshold/SATURATION_AND_SINGLE_EXP_FPT…` §4 and `threshold/SATURATION_ADDENDUM…` §2, was stated there without proof; `threshold/ENCODING_LEMMA.2026-10-28.md` (below) supplies it, reviewed by two independent AI reviewers but not machine-checked.
* The results are fixed-parameter results in the arity `K`, with `n` in unary. They do not give a uniform polynomial-time optimizer for growing arity, which remains open.
* Not included: the scanned Kannan (1987) pages and PDF (third-party copyright), helper scripts, run logs and agent transcripts. Kannan's theorem is used as an external citation.

## Mapping to the paper's bibliography

| Paper reference | Folder | Main proof documents |
|---|---|---|
| `threshold` | `threshold/` | `SYMBOLIC_THRESHOLD`, `SATURATION_AND_SINGLE_EXP_FPT`, `SATURATION_CLARIFICATIONS`, `RESULT` |
| `normalization` | `normalization/` | `PRIMITIVE_NORMAL_FORM` |
| `outer` | `outer/` | `OUTER_ILP_REDUCTION`, `CHARGE_STAIRCASES`, `KANNAN_APPLICABILITY`, `RESULT` |
| `profile` | `profile/` | `PROFILE_THEOREMS`, `FINITE_PROFILE_REDUCTION`, `ADDENDUM` |

Review and refutation records: `threshold/INDEPENDENT_REVIEW`, `threshold/SINGLY_EXPONENTIAL_REVIEW`, `threshold/SATURATION_REFINEMENT` (counterexamples to naive polynomial saturation), `outer/REVIEW`, `normalization/PROVENANCE_AND_REVIEW`, `profile/REPORT`. Witness data: `threshold/K3_FULL_WITNESS…json` (a complete k=3 table of charge 14 and profile (8,8)).

## File list (sha256 of the shipped copy)

| Folder | File | sha256 |
|---|---|---|
| `threshold` | `AUDIT_AND_PROVENANCE.2026-10-15.md` | `bc66f2c022567c3f…` |
| `threshold` | `FORMAL_CERTIFICATE.2026-10-15.md` | `a851adfde52d61c7…` |
| `threshold` | `INDEPENDENT_REVIEW.2026-10-15T150700.md` | `04daca5aecc784da…` |
| `threshold` | `K3_FULL_WITNESS.2026-10-15T151501.json` | `85f431943acf4205…` |
| `threshold` | `RESULT.2026-10-15.md` | `1fafe4aeab6a2c33…` |
| `threshold` | `SATURATION_ADDENDUM.2026-10-15T151032.md` | `e9c233bc901227ab…` |
| `threshold` | `SATURATION_AND_SINGLE_EXP_FPT.2026-10-15T190800.md` | `90223bd16d7bfb7d…` |
| `threshold` | `SATURATION_CLARIFICATIONS.2026-10-15T191000.md` | `962a9f465ac8cc5e…` |
| `threshold` | `SATURATION_REFINEMENT.2026-10-15T154500.md` | `54b29078fd1dfd1c…` |
| `threshold` | `SINGLY_EXPONENTIAL_REVIEW.2026-10-15T155500.md` | `5ca9fe5e9b25b682…` |
| `threshold` | `SYMBOLIC_THRESHOLD.2026-10-15T190000.md` | `dbf3ad589d7f7a8b…` |
| `normalization` | `PRIMITIVE_NORMAL_FORM.2026-10-15T145600.md` | `155859656d8d4cc6…` |
| `normalization` | `PROVENANCE_AND_REVIEW.2026-10-15T150200.md` | `22bd2f4520206046…` |
| `outer` | `CHARGE_STAIRCASES.2026-10-15T152500.md` | `15a1a5c6df884844…` |
| `outer` | `FORMAL_CERTIFICATE.2026-10-15.md` | `46c60462eb24b4da…` |
| `outer` | `KANNAN_APPLICABILITY.2026-10-15.md` | `5a5484bcb9081389…` |
| `outer` | `OUTER_ILP_REDUCTION.2026-10-15T144200.md` | `7d3ba5b6b41cbd5d…` |
| `outer` | `RESULT.2026-10-15.md` | `d7f96dc2e0879f68…` |
| `outer` | `REVIEW.2026-10-15T194000.md` | `a14fd5d18896e978…` |
| `profile` | `ADDENDUM.2026-10-15.md` | `6aa06ab28b9fb685…` |
| `profile` | `FINITE_PROFILE_REDUCTION.2026-10-15T150000.md` | `717e4b91288797b9…` |
| `profile` | `PROFILE_THEOREMS.2026-10-15T140100.md` | `c34d60b8f8c2b600…` |
| `profile` | `REPORT.2026-10-15T150000.md` | `5486c016835bf333…` |

Provenance: copied on 2026-10-28 from `ShorOptimization_Polynomial/efficient_tables_2026-10-15/` (`threshold_execution_2026-10-15`, `gap_closure_2026-10-15`, `fixed_execution_2026-10-15`). Licence: text under CC BY 4.0 like the other Markdown documents in this repository; the JSON witness under Apache-2.0 with the code.

## Added 2026-10-28: adjacent-gap encoding lemma (closes the `8k^2` step)

`threshold/ENCODING_LEMMA.2026-10-28.md` proves the step that `threshold/SATURATION_AND_SINGLE_EXP_FPT…` §4 and `threshold/SATURATION_ADDENDUM…` §2 state without proof: every constraint of the symbolic pattern systems has coefficients at most 2 and right sides at most `8k^2`, because integrality and cancellation are encoded by adjacent difference constraints, not by a bound on `ν₂(A)`. Two independent AI reviews are in `threshold/review/` (proof review: correct with minor fixes, applied; numeric test: no violation over about 1.4 million checks, k = 2–4). Not machine-checked; imports the normal-form and scanner results unproved.

| File | sha256 |
|---|---|
| `threshold/ENCODING_LEMMA.2026-10-28.md` | `f5d6a23bdb694ce5…` |
| `threshold/review/review_proof.md` | `7a9178f2bd876b72…` |
| `threshold/review/review_numeric.md` | `85256c5f119bbdc1…` |

## Added 2026-10-28: informal sources of the two newer Lean developments

`formal/small_integer_point.tex` is the informal statement and proof of `lean/Foundations/SmallPoint/`, and `formal/runtime_composition.tex` of `lean/Foundations/RuntimeComposition/` (an arithmetic composition, not a runtime theorem about the algorithm). The Lean files were produced with the autoformalizer, then the statements were read by hand and the axioms re-checked; `lean/Foundations/RuntimeComposition/Cutoff`, `TripleCount` and `Main` were completed by an AI proof agent working in a scratch copy with the statements pinned, after the tool left them unproved; the files were then recompiled and their axioms and statements rechecked independently. The tool's auxiliary `_narrowed` variants, which carried `sorry`, were removed. Both libraries compile in the Lean 4.28.0 / Mathlib `fadcf92b…` workbench; a full repository `lake build` has not been run with them.

| File | sha256 |
|---|---|
| `formal/small_integer_point.tex` | `b1a605b102607490…` |
| `formal/runtime_composition.tex` | `d82639955de68774…` |

## Added 2026-10-28 (later): informal sources of three further Lean developments

`formal/separation_lemmas.tex` is the informal statement and proof of `lean/Foundations/SeparationLemmas/`; `formal/paired_charge.tex` of `lean/Foundations/PairedCharge/` (counting only, not a legality proof). `lean/Provider/Ceiling/GroupedCharge.lean` has no separate informal source: its statement is the exact charge of the repository's grouped literal baseline, `4(k−1)(2k−3)` (see `BRIDGES` B2 in the research notes for the construction). The Lean files for `SeparationLemmas` and `PairedCharge` were produced with the autoformalizer (statements read by hand, axioms re-checked); the `PairedCharge` theorems and `GroupedCharge` were completed by an AI proof agent in a scratch copy with statements pinned, then recompiled and rechecked independently. Tool artifacts (`_narrowed` variants) were not carried over.

| File | sha256 |
|---|---|
| `formal/separation_lemmas.tex` | `dbec92a017b45aa6…` |
| `formal/paired_charge.tex` | `9a43f1302aedc5e1…` |
