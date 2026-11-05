# Hardness and sparsity-barrier proofs (separate Lake project)

This folder holds the Lean proofs behind the complexity statements of the paper's hardness appendix.
It is a **separate Lake project** from the main library in `../lean`, because it uses a different toolchain:
Lean `v4.35.0-rc3` and [complexitylib](https://github.com/elazarg/complexitylib) at
`3f4b5fee8bbd49721a5b70473c81bf3db2e7500d` (multi-tape Turing machines in the style of Arora and Barak,
with P, NP, FP, `≤ₚ`, `NPHard` and Cook–Levin). Build it from this folder, not from the repository root.

## What is and is not claimed

* **NP-hardness is shown only for the structural score with supplied points.** The objective here is the
  benchmark's structural score `S = A + 5L`, not the T-count.
* **No NP-hardness of T-count optimization is shown.** No result here says that minimizing the
  end-to-end T-count is NP-hard, in general or for the KMY points.
* The sparsity barriers are **conditional statements**. They say that an NP-hardness proof would imply
  `P = NP`. They are not hardness results, and they do not show membership in P.

| Theorem | File | Statement |
|---|---|---|
| `Mahaney.mahaney` | `Mahaney/Theorem.lean` | `Sparse S → NPHard S → P = NP` (Mahaney's theorem, Ogihara–Watanabe pruning) |
| `Mahaney.tableOpt_barrier` | `Mahaney/TableLang.lean` | `NPHard TableOptLang → P = NP`: the structural-score language with `k` in unary and the table choosing its own points (the paper's `L_S`) |
| `Mahaney.policyOpt_barrier` | `Mahaney/PolicyLang.lean` | `NPHard (PolicyLang opt n0) → P = NP` for a unary-`n` language whose optimum `opt` is bounded by a monotone polynomial. The bound is a **hypothesis** supplied by the caller. The T-count model itself is not formalized here |
| `Pts.genLang_NPHard` | `Points/SatRed.lean` | `NPHard GenLang`: the structural-score table problem with **points supplied as input** (the paper's `PointsTableOpt`), already at `k = 2`, by SAT → DHC₂ → EHC → table |

The reduction chain also yields `Pts.sat_iff_table`, `Pts.TS.sat_iff_dhc`, `Pts.dhc_iff_ehc`,
`Pts.cycle_reduction` and `Pts.sat_le_gen` (see the `Points/Audit*.lean` files).

Each listed theorem depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`. The sources contain no
`sorry`, `admit`, `axiom` or `native_decide`.

## Build and audit

```
lake build                         # first build compiles ~2.3k complexitylib modules (~20 min)
lake env lean Mahaney/Audit.lean
lake env lean Points/Audit.lean
lake env lean Points/Audit3.lean
lake env lean Points/Audit4.lean
```

A clean build of this layout completed with no errors (3440 jobs), and each audit printed only the three axioms above.

## Contents

* `Mahaney/`: the concrete Mahaney theorem and the two sparsity barriers. `PLAN.md` lists the files and the
  modeling choices: `k` or `n` in unary, the budget in canonical binary, malformed strings are no-instances, and
  sparse means the census is at most polynomial in length.
* `Points/`: the points-as-input reduction. `Points/PLAN.md` and `Points/STAGE3_DESIGN.md` record the stages.
  `Points/design/*.py` are the brute-force scripts used to validate the gadgets before formalizing them.
  They are not part of the proof.
* `vendor/ShorTableOptimization/TableGeneration/`: a **snapshot** of the benchmark contract files
  (`Basic`, `Language`, `Spec`, `Metrics`, `ContractSoundness`) from the ShorTableOptimization benchmark repository
  (now `github.com/VerifiedQC/ShorTableOptimization`), taken in October 2026. As checked on 2026-11-04, `Basic` and
  `Language` are identical to that repository's `main`; `Spec` (decidability-instance spelling, `==` versus `=`),
  `Metrics` (one `open Operations`) and `ContractSoundness` (comments) differ, because upstream was ported to Lean
  v4.36.0-rc1 after the snapshot. The proofs here are built against the snapshot and have not been re-checked
  against current `main`. The table problem is stated against this contract.

## License

Apache License 2.0, see [`LICENSE`](LICENSE) (the same license as the repository's code).
