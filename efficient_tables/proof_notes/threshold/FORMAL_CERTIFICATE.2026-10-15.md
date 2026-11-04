# Scoped formal certificate

`ThresholdAlgebraRepair20261015.formal.json` records successful Lean checking, module compilation, and autoformalizer trusted replay for all five theorems in `lean/Paper/ThresholdAlgebraRepair20261015.lean`. Every structural-problem entry is null; every theorem is certified; `all_certified` is true.

The statements cover separated-cluster integer cancellation under supplied divisibility and magnitude hypotheses, the anchored version, domination by relaxed scanner addition bounds, unclipped right-subtraction domination under a supplied legality inequality, and a normalization arithmetic inequality.

They do not formalize how signed-power clustering establishes those hypotheses, the complete-table semantics, the small-integer-point lemma, threshold enumeration, the complexity bounds, or the outer optimizer. No whole-theorem formal certification is claimed.

The deterministic driver imports the installed `autoformalizer.formal.leancheck` and `trusted` adapters and uses the existing `_toolkit/autoresearcher/lean_workbench`. The closest exemplar was the prior round's `coordinator/check_gap_formal.2026-10-15.py`; only the research module, output paths, preregistration, and scope changed. Toolkit implementations were not copied or edited. Source and dependency hashes are recorded in the JSON.

The initial `ThresholdAlgebra20261015.lean` failed because an unqualified `dvd_zero` identifier was unavailable under the minimal import. Its source and failed result were retained. The repaired file explicitly constructs the divisibility witness and passes trusted replay. No local model inference was used.
