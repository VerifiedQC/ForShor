# Reproducing

Nothing here needs network access except fetching Lean/Mathlib and (optionally) a Fortran compiler.

## 1. Lean library

Requirements: [elan](https://github.com/leanprover/elan) (reads `lean-toolchain`: `leanprover/lean4:v4.28.0`),
about 16 GB of RAM recommended, and enough disk for Mathlib's build cache.

```
lake exe cache get      # fetch the prebuilt Mathlib oleans for the pinned revision
lake build EfficientTables
lake build EfficientTablesHelpers
```

* Mathlib is pinned in `lakefile.toml` to commit `fadcf92bfcfe7575bbdf04c6f83ab3ada53e3d42`.
  `lake-manifest.json` is committed and pins all dependencies.
* `EfficientTables` contains every module listed in `lean/` (167 modules). Several modules are large; build
  with plenty of free RAM (about 16 GB). Do not run several Lean builds at once.
* To audit axioms for the main theorem, add a scratch file containing
  `import PhaseProduct.Catalog.EndToEnd` and `#print axioms Paper.PPEndToEnd.pp_through_arity_K`; the result is only
  `propext`, `Classical.choice`, `Quot.sound` (checked on this packaging).
* `lean/Alignment/SparseThreshold.lean` holds the census and encoding lemmas used in the sparseness
  discussion. It is **not** a sparseness theorem: it proves counting ingredients and that an unclipped binary
  threshold language is not sparse. See `lean/` module docstrings.

A clean `lake build` of the original flat layout (8216 jobs) was run end to end without errors. After the reorganization into dependency layers and the addition of the five newer developments (`lean/Foundations/SmallPoint/`, `RuntimeComposition/`, `SeparationLemmas/`, `PairedCharge/` and `lean/Provider/Ceiling/GroupedCharge.lean`), `lake build EfficientTables EfficientTablesHelpers` was run again on 2026-10-28 with Lean 4.28.0 and the pinned Mathlib and completed without errors (8241 jobs, 192 + 20 root modules). The Mathlib build cache used for that run was a copy of one built at the same pinned revision, so Mathlib itself was not recompiled.

To audit the declarations listed in [`LEAN_MAP.md`](LEAN_MAP.md), run `lake env lean scripts/AxiomAudit.lean` after
`lake build` (run from the repository root). Each result should list only `propext`, `Classical.choice`, `Quot.sound` (the three `Paper.Planner`
theorems list only `propext`). The new developments have their own `Audit.lean` files.

## 1b. Hardness proofs (separate Lake project)

`lean_hardness/` pins its own toolchain (`leanprover/lean4:v4.35.0-rc3`) and complexitylib, so build it from
that folder:

```
cd lean_hardness
lake build
lake env lean Mahaney/Audit.lean
lake env lean Points/Audit4.lean
```

The first build compiles about 2.3k complexitylib modules (about 20 minutes). The audits print only
`propext`, `Classical.choice`, `Quot.sound`. See `lean_hardness/README.md` for the scope: NP-hardness
is shown only for the structural score with supplied points, not for T-count optimization.

## 2. Fortran solver

Requirements: a Fortran 95 compiler (the reference build used GNU Fortran 16.2.0) and Python 3.

```
cd fortran/phaseproduct_saturation_f90
python -B build.py --debug
python -B build.py
echo "&run n=60, kmax=3, use_bounds=.true. /" | build/release/phaseproduct_saturation
```

Output lines are `STATUS OPTIMAL`, `COST`, `LEVEL`, `TABLE/OP` and `END_TABLE`.
`build.py` finds the compiler from `FC`, `--compiler`, or `gfortran` on `PATH`.
Tests need the same: set `FC` to your gfortran, then for example `python -B tests/test_solver.py`.

Timings depend on hardware; the cost values are the reproducible part. For example, n=6, kmax=3 gives COST 1476,
n=40, kmax=5 gives 92750 and n=60, kmax=3 gives 200311.

## 3. Paper

`pdflatex` twice on `paper/Exact_Table_Algorithm_Model_and_Limitations.tex`. The PDF in the repository was
built that way. The paper cites several working notes by relative path; those notes are not part of this repository.
