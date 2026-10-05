# Repo cleanup plan — ALL SEVEN DONE

Closed 2026-10-05. Kept as a record of what was changed and why; nothing
below is open work. The five `scripts/check_*_layers.sh` it refers to have
since been folded into `scripts/check_layers.py`
(`ShorVerification/PLAN.md` item 18).

Findings from a full pass over the repo on 2026-09-28. Every lake target
(`FastMultiplication`, `EmitTests`, `Submission`) builds, the five
`scripts/check_*_layers.sh` pass, and `#print axioms` on `Shor_correct`,
`exists_shorGateCountBound`, `submission_correct` and `referenceProgramAt`
reports only `propext`, `Classical.choice`, `Quot.sound`. The items below are
hygiene, not correctness. Each numbered item is one commit.

Deliberately **not** in this plan: the orphaned `Table_Generation/Generator/`
subtree (nine files, ~2,300 lines, reached by no lake target since
`b4856a5` dropped its imports from `Emit/Table/Source.lean`). Whether to
re-import it from `FastMultiplication.lean` or archive it is a separate
decision. Item 6 below fixes its five unused-simp-arg warnings so it is
clean if it comes back.

## 1. Regenerate the docs graph and fix its annotations

`docs/data/graph.js` still names `Framework/Submission.lean` and
`Framework/Instantiation`, which were renamed to `Framework/Contract.lean`
and `Framework/ToomCookTable.lean`. `scripts/gen_docs_graph.py --check`
fails with eight errors.

- Run `scripts/gen_docs_graph.py` to regenerate `docs/data/graph.js`.
- In `docs/data/annotations.js`:
  - rename `Framework/Submission.lean` → `Framework/Contract.lean` at lines
    90, 101, 115, 119, 121, 122;
  - replace `Framework/Instantiation` → `Framework/ToomCookTable.lean` at
    lines 87 and 115; drop the two edges into it at lines 123–124 unless
    they are real imports (`ToomCookTable.lean` imports only Mathlib, so
    they almost certainly are not);
  - update the two prose summaries at lines 24 and 47 to say `Contract.lean`
    and to describe a submission as a Toom-Cook table, matching
    `Implementation/README.md`.
- Rerun `scripts/gen_docs_graph.py --check` until it exits 0.
- Remove the two `Qualtran/` mentions in the script's comments (lines 4 and
  140); that folder was deleted in `b4856a5`.

## 2. Add CI

There is no `.github/workflows/`. Nothing checks the build, the
`EmitTests`/`Submission` targets, the layer scripts, or the docs graph
except a person remembering to.

- Add `.github/workflows/ci.yml`, one job on `ubuntu-latest`, triggered on
  push to `main` and on pull requests:
  1. install elan (`leanprover/lean-action` or the elan install script);
  2. restore a cache of `.lake/` keyed on `lake-manifest.json` and
     `lean-toolchain`;
  3. `lake exe cache get`;
  4. `lake build FastMultiplication EmitTests Submission`;
  5. run each `scripts/check_*_layers.sh`;
  6. `scripts/gen_docs_graph.py --check`, then `git diff --exit-code
     docs/data/graph.js` so a stale committed graph fails the job.
- `EmitTests` takes ~4 minutes locally; the whole job should stay under
  15 minutes once the cache is warm.

## 3. Untrack `.DS_Store`

- `git rm --cached .DS_Store`
- append `.DS_Store` to `.gitignore`.

## 4. Fix stale file paths in READMEs and docstrings

Top-level `README.md`:
- line 13: `Shor/Proofs/NaiveShor/Main.lean` → `Shor/Proofs/NaiveShor/Correctness.lean`;
- line 81: `Math/Toom_Cook_formula.lean` → `Math/ToomCook.lean`.

Folder READMEs:
- `ModularExponentiation/Proofs/README.md` (lines 92, 133) and
  `ModularExponentiation/Lowering/README.md` (lines 32–33):
  `Shor/Proofs/Readiness.lean` → `Shor/Proofs/Readiness/`,
  `Shor/Proofs/WholeProgramCorrectness.lean` → `Shor/Proofs/Correctness.lean`.
- `QFT/Lowering/README.md` line 64: `Shor/Defs.lean` → the file that now
  imports the lowered QFT (confirm with `grep -rln "lowerQFT" Shor/`;
  expected `Shor/Circuit/OrderFinding.lean` or `Shor/Lowering/LowerGate.lean`).
- `Shor/Math/README.md` line 9: `Proofs/NaiveShor/Lemmas.lean` → the current
  `NaiveShor/` split (`Preliminaries.lean`, `PhaseEstimation.lean`,
  `GoodOutcomeMassLowerBound.lean`).
- `Shared/README.md` lines 41–43: replace the history paragraph citing
  `REORG_COMPILATION.md`, `GateSemanticsLemmas.lean`, `CleanClosure.lean`
  and `Implementation/RegisterLemmas.lean` with one sentence ("this folder
  was assembled from a single lemma file during the reorg; see git
  history").
- `Emit/README.md` line 332: `Table/Decide.lean` →
  `ShorVerification/Submission/Decide.lean`.
- Leave the Emit READMEs' explicit "now deleted" mentions
  (`Symbolic/Template.lean`, `Symbolic/Recursion.lean`,
  `Lower/Instantiate.lean`, `Table/Census.lean`, `Emit/PLAN.md`) alone;
  they are history notes, not links.

Docstrings citing the deleted `Emit/PLAN.md`:
- `Emit/Reflect/Driver.lean:162`, `Targets.lean:9`, `Targets.lean:302`,
  `Extract.lean:13`, `Extract.lean:295`, `Verify.lean:23`, `Verify.lean:363`.
  Reword each `PLAN.md §x.y` to the round/decision label (`R2.1`, `D3`, …)
  that `Emit/README.md`'s "How this folder was built" table defines.

## 5. Bring ARCHITECTURE.md up to date

The file opens by saying none of its paths resolve. Every folder now has its
own README, so it should be shorter and correct rather than long and stale.

- Keep the three narrative sections from line 263 on ("Folder Guide and
  Main Results", "The submission boundary", "Big Picture") and rewrite
  every path in them to the current tree.
- Replace the two `Basic.lean` sections (lines 37–262) with one table:
  concept → the `Framework/` file that now holds it (registers →
  `Quantum/Registers.lean`, `Gate`/`LowGate` → `AbstractMachine/`,
  `QSemantics` and the other classes → `Semantics/`, cost model →
  `Gatecount/`, `ShorImplementation` → `Contract.lean`, `ShorSubmission` →
  `ToomCookTable.lean`).
- Delete the "Note on paths below" disclaimer once every path resolves.
- Re-run the markdown path check (a script that extracts every
  backticked `*.lean` path and tests existence) over the result.

## 6. Small Lean cleanups

- Delete the stale `-- TODO:` comment at
  `PhaseProduct/Math/Table_Generation/Core/RegisterLemmas.lean:323`; the
  proof under it is complete.
- Silence the per-build warning at `Reference/Reference2048Headline.lean:67`
  ("exponent 4097 exceeds the threshold 256") with
  `set_option exponentiation.threshold 4100 in` on `Is2048Bit.tbits_le`.
- Remove the five unused simp arguments the linter reports in
  `Table_Generation/Generator/Correctness.lean` at lines 1500, 1514, 1515,
  1519, 1520 (`streamPoint` / `generatedPoints`).
- Long lines (656 over 100 chars, mostly in
  `ModularExponentiation/Proofs/Step1QPE.lean` and `Step2Bound.lean`) are
  left as they are unless a reflow pass is wanted.

## 7. Rename the package

- `lakefile.lean` line 4: `package «Fast_multiplication»` → `package «ForShor»`.
- `lake-manifest.json` line 94: `"name": "Fast_multiplication"` → `"ForShor"`.
- The `FastMultiplication` module root and `lean_lib` name stay; renaming
  them would touch every import.
- Rebuild to confirm lake accepts the new name.

## Verification (after all seven)

```sh
lake build FastMultiplication EmitTests Submission
for s in scripts/check_*_layers.sh; do bash "$s"; done
scripts/gen_docs_graph.py --check
git status --porcelain docs/data/graph.js   # must be empty
```
