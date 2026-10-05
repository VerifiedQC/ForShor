# ShorVerification: claims, trust boundary, headline statements

Findings from a full pass over the repo on 2026-10-05. Baseline: every lake
target (`FastMultiplication`, `EmitTests`, `Submission`) builds warm with no
warnings, the five `scripts/check_*_layers.sh` pass, the docs graph check
passes, and `#print axioms` on `Shor_correct`, `exists_shorGateCountBound`,
`submission_correct` and `Submission.setup` reports only `propext`,
`Classical.choice`, `Quot.sound`.

The ten items below are the ones that change what the repository *claims*,
or what a submitter can get past the checker. They are ordered by how much
they matter, not by effort. Each numbered item is one commit. Paths are
relative to `FastMultiplication/ShorVerification/` unless they start with
`Emit/`, `scripts/` or a top-level file name.

## 1. Prove the gate-count bound for every admissible table — DONE

`PhaseProductProgramOK` (`Implementation/GateCount/Definitions.lean:55`) is now
exactly C1–C4, and the `O(n^(2+ε))` theorem covers an arbitrary accepted table,
not just the generated one.

- `Implementation/PhaseProduct/Proofs/Compiler/Support.lean:621` — new
  `ProgConsumesPts.phaseProductCount_eq`: ordered point consumption forces
  `phaseProductCount ops = pts.length`, by induction on `ops` generalizing `σ`.
- `Implementation/GateCount/Definitions.lean` — the fifth conjunct
  `phaseProductCount ops = q k` is deleted; new
  `ShorLoweringSetup.programOK (s) : PhaseProductProgramOK s.k s.hk s.pts s.hpts s.ops`
  is `⟨s.good, s.consumes, s.returns⟩`.
- `Implementation/GateCount/PhaseProduct/Main.lean:35` — `hcount` is now derived
  from C3 and `hpts` through the new lemma instead of being assumed.
- `Implementation/GateCount/Shor_GateCount.lean` — `exists_phaseProductProgramOK`
  drops its fourth component; new `shorGateCountBound_of_setup`, which is
  `shorGateCountBound_of_programOK` applied to `s.programOK`.
- Top-level README ("Resource estimation") and
  `Implementation/GateCount/README.md` state both forms and say why the
  "for every ε" form stays existential in `k`.

`#print axioms Shor.shorGateCountBound_of_setup` reports only `propext`,
`Classical.choice`, `Quot.sound`. Add `#assert_axioms` for it to the CI axiom
guard once item 12 of the repo-level list exists.

## 2. Give `ShorCorrectApproxLoweredUniform` a concrete `η(N)` — DONE (reworked)

The threshold is now a closed form. `shorPrecision : ℕ → Reg → ℝ` takes no
`K`, and `ShorCorrectApproxLowered` has no `∃ K` prefix — the uniform constant
`2048` is folded into the numeral `65536 = 32 · 2048`. A circuit builder can
evaluate the precision it needs before building anything.

**The constant, moved down a layer.**
`ModularExponentiation/Proofs/ModExp.lean` gained
`modExpApprox_valid_dist_2048` (the old `referenceK_modExp_bound` proof, with
the literal in place of `referenceK`), surfaced as
`Spec/Assertions.lean`'s `ModExpApproxValidDist2048` and `Main.lean`'s
`modExpApprox_correct_2048`. `Reference` consumes the public form; its private
copy is gone. `referenceK` itself stays — `referenceApproximationErrorAt` and
`Reference2048Headline.lean:149-155` compute with the numeral by name.

**Shor side.** `shorPrecision N x = κ² / (65536 · tbits(x)² · log₂(N)⁸)`;
`ShorCorrectApproxLowered` is a plain `∀` concluding `≥ κ / (2 · log₂(N)⁴)`;
`lowering_loss_le_half` lost its `K` argument and the three `max K 1` facts
along with steps `h1`/`h3` of `hsq`; `Shor_correct_approx_lowered` now goes
through `Shor_correct_approx_lowered_of_modExp_bound_assertion` at `2048`
rather than through the existential theorem.
`Shor_correct_approx_lowered_uniform` stays as the headline but is no longer
on the path to anything.

Arithmetic, for the record: with `S := κ / (4 t L⁴)`,
`4096 · η ≤ 4096 · κ²/(65536 t² L⁸) = κ²/(16 t² L⁸) = S²`, then
`Real.sqrt_le_sqrt`, `Real.sqrt_sq`, and `2 t S = κ / (2 L⁴)`.

**Docs.** All six places the rework listed, plus two the list missed:
`Shor/Main.lean`'s own docstring and `Proofs/Correctness.lean`'s section
banner both still spelled `shorPrecision K N x`. The ModExp READMEs
(folder, `Spec/`, `Proofs/`) gained entries for the three new names.

One deviation from the written rework: `Shor/Main.lean` cites
`modExpApprox_valid_dist_2048` (the `Proofs` lemma, already in scope via
`Proofs.Correctness`) rather than `modExpApprox_correct_2048`, exactly as the
rework's own code block specifies — `Shor/Main.lean` does not import
`ModularExponentiation/Main.lean`. `Reference` uses the `Main` form, so item
6's invariant is unaffected.

### Check — all green

`lake build FastMultiplication`; `grep -rn "shorPrecision K\|max K 1"` over
`FastMultiplication README.md docs` returns nothing;
`#print axioms Shor.Shor_correct_approx_lowered` reports only `propext`,
`Classical.choice`, `Quot.sound`; `check_shor_layers.sh` and
`check_modexp_layers.sh` pass.

## 3. Close the compiled-code gap in the submission pipeline — DONE

The gap was confirmed empirically before documenting it: a declaration
carrying `@[implemented_by]` passes `#assert_axioms` reporting **zero**
axioms, while `#eval` and `native_decide` both see the substituted value.
Two tiers read the table — the kernel reduces C1–C4, while `extract_ir_doc`
(`Lean.Meta.evalExpr`), the two evaluation-tier `example`s and
`lake exe forshor_submission` all run compiled code — and nothing in the
environment marks a disagreement between them.

- `Submission/README.md`, CI step 1: the lexical gate on `Template.lean`,
  with the `grep -E` line. Step 3 gained a paragraph saying what the three
  CI steps divide between them — `lean4checker` and `#assert_axioms` both
  speak only about the kernel tier, so step 1 is the only cover for the
  compiled one.
- `Submission/Audit.lean`: "what it does *not* catch" now has two bullets,
  the compiled-code one explaining why `collectAxioms` cannot see it.
- `Submission/Template.lean`: one paragraph telling the submitter the
  restriction and why a table needs none of it.

Beyond the plan as written:

- **The gate is anchored at code positions**, not a bare token match. The
  first draft (plain alternation) rejected the shipped `Template.lean`,
  because the paragraph documenting the restriction names the tokens.
  Anchoring to `^@[`/`^attribute [`/line-initial commands fixes that.
  Verified: 14/14 attack patterns caught, 0 false positives, clean on the
  shipped template, 2 hits on a tampered copy, and the regex was re-extracted
  from the README and re-run to confirm the published text is what was tested.
- **`Audit.lean`'s test section gained the non-catch**, in the file's
  existing one-declaration-per-class style: `substituted` reduces to
  `realThree` in the kernel, evaluates to `fakeThree` compiled,
  `#assert_axioms` reports `axioms: []`, and a `native_decide` example proves
  the compiled value differs. This pins the gap as a tested fact. Drop it if
  a repo-owned `@[implemented_by]` is unwelcome.
- `csimp` is weaker than the other two: it needs a proof of
  `realOps = fakeOps`, so it is an opening only if that proof is unsound.
  Recorded in both README and `Audit.lean`.

Still open, as the plan says, as a separate item: make `buildDoc` reflect over
the `Expr` of `setup` instead of `evalExpr`-ing it, which removes the second
tier here entirely and the `unsafe` from `elabExtractIrDocImpl`.

## 4. Print the table from `setup`, not from the top-level definitions — DONE

- `Submission/Main.lean` serialises `setup.k`, `setup.pts`, `setup.ops`.
- `Submission/Check.lean` carries the three `example … := rfl` tying the
  template's marked definitions to the record fields.

## 5. Update the sampled-width claims to the ladders — DONE

All five places now describe the ladders, with the reason (`Emit/PLAN.md`
§1.1, §2 T2.1: the top-chunk bug is visible only at a grandchild and only
with slack, hence three levels and two reserve regimes) and the `k ≥ 3` cost.

`Submission/Main.lean`'s `ir_agreement` is now derived rather than restated
— `s!"… {Reflect.submissionPPWidths setup} …"` — so `ir.json` reports the
ladders this table was actually checked at. The shipped table prints
`pp [13, 14, 15, 17]`, slacks `[0, 64]`, leaf pairs `[(13,7), (7,13), (6,5)]`,
`qft [4, 8, 9, 29]`. The old prose said `n = 8, 16` and `w = 4, 8`; neither
number occurs in the ladders, so the sentence was wrong on every count.

## 6. Make `Shor/Main.lean` and `Shor/README.md` agree — DONE, option (a)

Reference now routes through `Main.lean`, so the invariant `Shor/README.md`
states ("nothing outside `Proofs/` or `Main.lean` may import it") is true
again.

- `Shor/Spec/Assertions.lean` — `ShorCorrectApproxLoweredOfModExpBound`: the
  lowered bound at a `K` the caller supplies, against an assumed
  modular-exponentiation distance bound at that `K`.
- `Shor/Main.lean` — `Shor_correct_approx_lowered_of_modExp_bound_assertion`.
- `Reference/ReferenceShorImplementation.lean` imports `Shor.Main` and
  `ModularExponentiation.Main` in place of the two `Proofs` modules.
- `scripts/check_shor_layers.sh` gained a second pass over the whole tree
  that fails on `import … Shor.Proofs.*` from outside `Implementation/Shor/`.
  Negative-tested: reintroducing Reference's old import makes it fail.

**The ModExp public assertion had to be strengthened.** Reference's
`referenceK = 2048` is justified by `K ≤ 2048`, which
`modExpApprox_valid_dist_uniform` proves but `ModExpApproxValidDistUniform`
dropped — so `modExpApprox_correct` was strictly weaker than its own proof
and unusable by Reference. That is *why* Reference reached into `Proofs`.
`K ≤ 2048` is now part of the public Prop.

**Two external `Proofs` imports remain and are allowlisted in the script**,
both documented in `Shor/README.md` as deliberate providers rather than
internal plumbing: `Proofs/Lowering.lean` → `GateCount/Shor_GateCount.lean`
and `Proofs/Readiness/Static.lean` → `Reference/ShorProgram.lean`.

## 7. Fix the documents that contradict the tree — DONE except the commit

- `Emit/README.md` now says the deleted 4 000-line log is in git history and
  the `Emit/PLAN.md` in the tree is a different, shorter T-tier plan.
- The four stale old-plan section numbers are gone (`Verify.lean` §7.1 →
  "before R5", `Targets.lean` §6.2 → "R6", `Tests.lean` §6.7 → "the R6
  `flatten` idiom", `Lower/README.md` §11 → dropped).
- `Submission/README.md` now points at `.github/workflows/ci.yml` and says
  what it does *not* do: no `lean4checker`, no diff rule, no lexical gate —
  steps 1 and 3 are enforced only by a submissions repo.

**Left to the owner:** the untracked paths (`Emit/PLAN.md`,
`Emit/IR/README.md`, `FastMultiplication/PLAN.md`; `Emit/fixtures/` is
deleted by item 14 rather than committed). Committing is a call I did not
make. Note `.github/workflows/ci.yml` runs
`git diff --exit-code docs/data/graph.js`, so `docs/data/graph.js` must be
committed with this work or CI fails.

## 8. `Algorithm1Precision`: docstring says `≥`, definition says `=` — DONE

The equality stays; the docstring was the thing that was wrong. The reason is
sharper than the plan guessed — the width is pinned because **both**
directions are load-bearing, in different proofs:

- `≥` (enough bits) — `pow_bound` → the QPE/Fourier contraction estimate in
  `Proofs/Step1QPE.lean`. This is the direction the paper states.
- `≤` (not too many bits) — `Algorithm1Precision.work_width_le_mul`
  (`GateCount/Shor_GateCount.lean`) rewrites with the equality to bound
  `regSize work ≤ cWork * regSize data`, which the `O(n^(2+ε))` count needs.

So relaxing to `algorithm1ExtraBits η ≤ regSize work - regSize data` would keep
correctness and cost the gate-count theorem. Written into `Precision.lean`'s
docstring and `ModularExponentiation/Spec/README.md`.

The `"uniform in the precision parameter η"` phrasing in the two READMEs is
about the *constant* `K` being η-independent, not about the width condition.
It is accurate and was left alone.

## 9. Remove phantom hypotheses from public statements — DONE, two bullets were wrong

Only one of the four bullets described an actual phantom.

- **`_hxWidth`/`_hyWidth` in `ShorGateCountBound`: not phantom.** Verified by
  deleting them — the build fails with `Unknown identifier 'hxWidth'` at
  `shorGateCountBound_of_components`, which feeds both to
  `ShorApproxSetup.toShorGateCountLayout`. Restored.
- **`_hcWork` on the three lemmas: genuinely phantom.** Each name occurred
  exactly once in the file, at its own binder. Deleted, with the three
  call-site arguments.
- **`shorEta`/`δ`: done as specified.** `ShorGateCountBound` is now
  `∀ cWork, 1 ≤ cWork → ∃ C …` over any `η` with
  `algorithm1ExtraBits η ≤ (cWork - 1) * regSize y.active`, and `δ` is gone
  from `shorGateCountBound_of_components`, `_of_programOK`, `_of_setup`,
  `exists_shorGateCountBound` and `exists_k_shorGateCountBound_of_programOK`.
  The schedule survives as `ShorGateCountBoundShorEta` plus
  `shorGateCountBoundShorEta_of_bound`/`_of_setup`, the only public
  statements left that mention `δ`. Safe because nothing outside this file
  consumed it: `Reference` declares its gate count as the actual
  `LowGate.gateCount` and never touches `ShorGateCountBound`.
- **The eleven binders in `Shor/Spec/Assertions.lean`: not phantom.** `hT`,
  `hm`, `hn` and `hinput` are all consumed by `Shor_correct`'s proof (`hm`/`hn`
  by `basicSetting_of_shor_instance`). Kept.

The premise behind bullets 1 and 4 was a misreading: a leading underscore on a
binder in a **Prop definition** means the binder does not occur in the Prop's
*conclusion*, which is what every hypothesis looks like. Without it Lean's
unused-variable linter fires, and the repo's baseline is warning-free. A note
saying so is now in `Shor_GateCount.lean`'s `ShorGateCountBound` docstring and
at the top of `Shor/Spec/Assertions.lean`.

## 10. Spell out what `Shor_correct` says — DONE

A "What the statement says" block in
`Shor/Proofs/NaiveShor/README.md`, and the same five lines under
"Correctness" in the top-level README: `probability_of_success` as the
weighted sum, `r_found` as the continued-fraction indicator, `T` as a
classical budget costing no gates, `κ = 4e⁻²/π² ≈ 0.0548`, and the register
widths plus `IdealOrderFindingInput`.

## Verification (after items 1–10)

```sh
lake build FastMultiplication EmitTests Submission
for s in scripts/check_*_layers.sh; do bash "$s"; done
python3 scripts/gen_docs_graph.py --check
git status --porcelain docs/data/graph.js   # must be empty
lake exe forshor_submission | python3 -c 'import json,sys; json.load(sys.stdin)'
```

and, in a scratch file under `lake env lean`:

```lean
#print axioms Shor.Shor_correct
#print axioms Shor.Shor_correct_approx_lowered
#print axioms Shor.exists_shorGateCountBound
#print axioms Shor.shorGateCountBound_of_setup
#print axioms Shor.shorGateCountBoundShorEta_of_setup
#print axioms Shor.submission_correct
```

each reporting only `propext`, `Classical.choice`, `Quot.sound`.

---

# Second batch: build, CI, and repository hygiene

Items 11–20 change nothing about what the repository claims. They make the
claims checked by a machine instead of by a person remembering, and they
remove the places where the tree and the build disagree about what is live.
Same conventions as above: one commit per item, paths relative to
`FastMultiplication/ShorVerification/` unless they start with `Emit/`,
`scripts/`, `.github/` or a top-level file name. Line numbers were
re-checked on 2026-10-05 after items 1–10 landed.

## 11. `Table_Generation/Generator/` — DECIDED: leave as is

Ten files are reached by no lake target: `PhaseProduct/Math/Table_Generation.lean`,
`Table_Generation/Generator.lean`, and `Generator/{Correctness,Defs,Examples,
Metrics,Precomputed,Spec,WellFormed}.lean` (about 2 300 lines). They are
the general-`k` parity-reset table generator `generate` /
`generatePointsInOrder`, its well-formedness and consumption proofs, hand
tables for `k = 2, 3`, and metrics. Nothing on the headline path uses them:
`exists_phaseProductProgramOK` and `Reference/` take `genOpsWithProduct`
from `Programs/WithProduct.lean`.

Decision (owner, 2026-10-05): no action. The subtree stays where it is,
unbuilt by any target, neither re-imported nor archived.

Consequences, recorded so they are not rediscovered:

- Nothing in CI compiles these files. They can drift from the rest of the
  tree without a build failure. `lake build
  FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation`
  is the manual check; it passes today.
- `Generator/Correctness.lean:1256,1378,1398` use `native_decide`, so
  `generate_ProgConsumesPtsSafe` (`:1533`) depends on `Lean.ofReduceBool`.
  This does not reach any headline theorem; the axiom audit in item 12
  stays clean.
- `Generator/Examples.lean:49-51` has three top-level `#eval IO.println`
  lines. Harmless while nothing imports the file; the first future import
  will print on every build.
- Items 18, 19 and 20 are written to leave the subtree alone: the root
  module does not import it, and the layer script keeps skipping
  `Generator*` and the two umbrella files `Math/Table_Generation.lean` and
  `Table_Generation/Generator.lean`.
- `scripts/gen_docs_graph.py` still draws these files as live
  architecture. If that bothers anyone, an `"orphan": true` flag in
  `docs/data/annotations.js` is the one-line fix; not planned.

One sentence in `Table_Generation/README.md` and `Generator/README.md` saying
"not built by any lake target; kept as reference" would stop a reader from
assuming otherwise. That is the only edit this item asks for.

## 12. Make CI build and run the executables, and guard the axioms — DONE

`.github/workflows/ci.yml:39` builds `FastMultiplication EmitTests
Submission`. `Submission/Main.lean` is reached only from its own `lean_exe`
root and `Emit/Tests.lean` does not import `Emit/Main.lean`, so
`forshor_emit` and `forshor_submission` can stop compiling without CI
noticing. The README's claim that the headline theorems use only the three
standard axioms is checked by nobody. The lexical gate item 3 documents is
never executed, so the published `grep` can rot.

Add to the `Build` step and after it:

```yaml
      - name: Build executables
        run: lake build forshor_emit forshor_submission

      - name: Smoke-run executables
        run: |
          lake exe forshor_emit 2 2 15 0 > /dev/null
          lake exe forshor_submission | python3 -c 'import json,sys; json.load(sys.stdin)'

      - name: Axiom guard
        run: lake env lean scripts/AxiomCheck.lean

      - name: Lexical gate on the shipped template
        run: bash scripts/check_template_lexical.sh FastMultiplication/ShorVerification/Submission/Template.lean
```

- `scripts/AxiomCheck.lean`: imports `FastMultiplication` and
  `FastMultiplication.ShorVerification.Submission.Audit`, then
  `#assert_axioms` on each name in the verification list above. This is the
  `#assert_axioms` the repo already owns, applied to its own theorems.
- `scripts/check_template_lexical.sh`: the `grep -E` line from
  `Submission/README.md` rule 1, exiting 1 on a match. Running it against
  the shipped template proves the documented command executes and passes
  on the example; the security control still lives in a submissions repo.
- Warnings: add `-KwarningAsError=true` to the `lake build` line, or
  `grep -c 'warning:'` on the build log with `test $? -eq 1`. The main
  library is warning-free today; this keeps it so.
- `lean4checker`: rule 3 of the submission CI, which this repo does not
  run. Add it as a separate, allowed-to-be-slow job on
  `.lake/build/lib/lean/FastMultiplication/ShorVerification/Submission/*.olean`
  so the shipped `Template.lean` is replayed through the kernel somewhere.
  If the runtime is prohibitive, document in `Submission/README.md` that it
  is not run here and why.

## 13. Fix the CI cache, concurrency and the elan pin — DONE

- `.github/workflows/ci.yml:27-33` caches all of `.lake` keyed on
  `lean-toolchain` and `lake-manifest.json`. On a hit the project's own
  stale build is restored under `.lake/build`; on a miss the save includes
  every Mathlib olean and can approach GitHub's 10 GB cap. Cache
  `.lake/packages` only and let `lake exe cache get` (line 36) populate
  Mathlib's build.
- Add at the top level:

  ```yaml
  concurrency:
    group: ${{ github.workflow }}-${{ github.ref }}
    cancel-in-progress: true
  ```

- Line 22 downloads `elan/releases/latest`. Pin a release tag so a new elan
  cannot change the job under you.
- Update the header comment (lines 1-2) and the timeout comment (lines
  13-14) once item 12 adds steps.

## 14. Remove the Emit fixtures — DONE

`Emit/fixtures/` holds six flat `forshor.lowgate/v2` circuits for the
standard `k = 2` table (`pp`/`cpp` at `n = 8, 12`, `qft` at `w = 8, 9`,
about 360 KB) plus a README. They are an answer key for an external IR
reader: a consumer unrolls a template at one of these sizes with its own
code and diffs against the file to confirm it reads the IR the way Lean
does. They test nothing in this repository. The extraction itself is
already checked inside Lean by `Reflect/Verify.lean`'s width-ladder
comparison, in `Emit/Tests.lean` and `Submission/Check.lean`.

No external reader exists yet, nothing regenerates the files, and nothing
diffs them, so today they are committed output that looks authoritative
and is guaranteed by nothing.

Decision (owner, 2026-10-05): delete the directory. When a consumer needs
conformance examples, the six `forshor_emit … --flat` commands produce
them from the current code in seconds.

- `git rm -r FastMultiplication/Emit/fixtures/` (the directory is still
  untracked, so if item 17 has not committed it yet this is `rm -r`).
- `Emit/README.md:265`: delete the `fixtures/` row of the folder table.
- `Emit/IR/README.md:236`: replace the sentence pointing at
  `Emit/fixtures/` with the six commands, so a consumer who reaches the IR
  format spec finds the recipe there:

  ```bash
  lake exe forshor_emit pp  2 8  1/4 --flat   # phase_product, base case
  lake exe forshor_emit pp  2 12 1/4 --flat   # phase_product, first recursive width
  lake exe forshor_emit cpp 2 8  1/4 --flat
  lake exe forshor_emit cpp 2 12 1/4 --flat
  lake exe forshor_emit qft 2 8      --flat
  lake exe forshor_emit qft 2 9      --flat   # odd width: unequal split
  ```

  Keep the register-layout and environment tables from
  `fixtures/README.md` ("The registers, so a diff is possible at all" and
  "The environments") in `IR/README.md`; they describe how to instantiate
  a template, which is the format spec's job, and they are the only place
  that information is written down.
- `Emit/PLAN.md:224` (T4.3): append "— removed 2026-10-05; the recipe
  lives in `IR/README.md`".
- Item 17's commit list and this file's verification block no longer
  mention `Emit/fixtures/` or `check_emit_fixtures.sh`.

If an external reader appears later, the right form is not committed
files but a CI step that runs the six commands and uploads the results as a
build artifact, so the answer key is regenerated from the code on every
run and cannot go stale.

## 15. Pin Mathlib in the lakefile — DONE

`lakefile.lean:11-12` is `require mathlib from git "…"` with no `@ rev`.
`lake-manifest.json` pins `fadcf92b…` (2026-02-16), which carries no tag, so
the build is reproducible only because the manifest is committed; a
`lake update` jumps to Mathlib master.

- `lakefile.lean:11-12`: `require mathlib from git "…" @ "fadcf92bfcfe7575bbdf04c6f83ab3ada53e3d42"`
  (or move to a tagged Mathlib release that matches `lean-toolchain`'s
  `v4.28.0` and update the manifest in the same commit).
- Top-level README, "Building": state the Mathlib commit next to the Lean
  version, and that `lake exe cache get` needs that exact rev.
- Confirm `lake build` is a no-op afterwards (same manifest rev, nothing
  rebuilt).

## 16. Stop the default `pp`/`cpp`/`qft` CLI mode from running the full canary — DONE

`Emit/Lower/PhaseProduct.lean:56,96` and `Emit/Lower/Qft.lean:37` call
`Reflect.runExtractAndVerify k`, and `verifyDoc`
(`Emit/Reflect/Verify.lean`) now iterates the full per-table width ladders.
By `Emit/PLAN.md`'s own measurements that is 28 s at `k = 2` and about 35
minutes at `k = 3`, to print a circuit of a few hundred gates whose only
relevant check, `instantiate_eq_real` at *this* `n`, is computed separately
anyway. A typo in `--flat` (`Emit/Main.lean`, `rest.contains "--flat"`)
silently selects this path.

- In `buildPP`/`buildCPP`/`buildQFT`, replace `runExtractAndVerify k` with
  `runExtract k` followed by a `doc.wellFormed` check; keep the per-width
  `phaseProductAgrees`/`qftAgrees` as the embedded check for the requested
  width. Keep the full canary for `template` and `bundle`, where it is the
  point.
- `Emit/Main.lean`: reject unknown trailing arguments with exit 2 instead
  of `contains`, so `--falt` is an error; match `"shor" :: _` explicitly so
  a wrong arity reports the right message; `template` should use its own
  parser rather than `parseBundleArgs` (today it silently accepts
  `--m-max`, `--check-cramer`, `--no-template`).
- `Emit/README.md` and `Emit/Lower/README.md`: update the description of
  what annotated mode checks.

## 17. Commit the work and prune the branches

Thirty-nine modified files and one untracked path sit on `repo-cleanup`
after items 1–10, on top of the Emit T-tier work that was already
uncommitted. `ci.yml` runs `git diff --exit-code docs/data/graph.js`, so
`docs/data/graph.js` must land with the change that regenerated it.

- Commit in the order the plan items were done, one commit each, so
  `git log` matches this file: the Emit T-tier work first (it predates the
  plan), then items 1–10. Include `Emit/PLAN.md`, `Emit/IR/README.md`,
  `FastMultiplication/PLAN.md` and this file. `Emit/fixtures/` is deleted
  by item 14 and must not be committed.
- `FastMultiplication/PLAN.md` is complete; either delete it or add a
  one-line "all seven done" header so a reader does not take it for open
  work.
- `origin` has about 50 branches. `git branch -r --merged origin/main`
  lists the ones that are safe to delete; prune them, and ask before
  touching any that are unmerged.
- Open the PR from `repo-cleanup` to `main` only after item 12's CI steps
  are in, so the first green run exercises the new checks.

## 18. Fold the five layer scripts into one and fix their blind spots — DONE

`scripts/check_{modexp,phaseproduct,qft,shared,shor}_layers.sh` differ only
in `root`, `prefix`, the `layer()` case table, one allowlist and one
sideways-import rule. Defects shared by all five:

- The umbrella detector (`check_qft_layers.sh:14` and siblings) does not
  recognise `private`, `protected`, `opaque` or `example` as declarations,
  so a file of only `private` lemmas is flagged.
- `grep -oE "^import ${prefix}…"` misses multi-module `import A B` lines.
- `find … -name '*.lean'` is unsorted, so failure output order varies.
- `check_phaseproduct_layers.sh:13` skips `Math.Table_Generation*`
  entirely ("frozen subtree, not inspected"), which is how item 20's
  inversions escape. Narrow the skip to `Math.Table_Generation`,
  `Math.Table_Generation.Generator` and `Math.Table_Generation.Generator.*`
  (the unbuilt subtree item 11 leaves alone) and inspect the rest.
- The Shor script enforces a total order on `Proofs/Readiness/` that the
  real imports do not have: `Step2` and `Step5` are independent, `IQFT`
  does not import `Step2` or `Init`, `ModExp` does not import
  `Primitives`. Describe the real partial order
  (`Static, Sequencing < Primitives < Init, Step1 < {Step2, Step5} <
  {IQFT, ModMul} < ModExp < Dynamic`) in `Shor/README.md:27-31` and
  `Shor/Proofs/Readiness/README.md:5-9`, and enforce that.
- `Shor/Proofs/Readiness/Sequencing.lean:6` imports `Readiness.Static` and
  uses none of its declarations. The READMEs promise "every import is
  justified"; the scripts check ordering, not usage. Drop the import.

Replace the five with `scripts/check_layers.py <folder>` (or one bash
script reading a small table), keeping the per-folder layer tables as
data at the top of the file, and add a `Table_Generation` table
(`Core < Builders < Programs < Examples`; `Generator*` stays skipped per
item 11). Update `ci.yml`'s
loop to the single entry point. If `check_shor_layers.sh` still cites
`REORG_SHOR.md §4` after item 6's edit, drop the citation; the file does
not exist.

## 19. Prune `FastMultiplication.lean` to its real roots — DONE

Twelve of the root module's eighteen imports are in the transitive closure
of the other six: `Shared.Registers`, `PhaseProduct.Proofs.Lowering.Workspace`,
`Shor.Proofs.Budgets`, `Shor.Proofs.Setup`, `Shor.Proofs.Readiness.Dynamic`,
`Shor.Proofs.Correctness`, `PhaseProduct.Main`, `GateCount.QFT_GateCount`,
`Framework.Contract`, `Reference.ReferenceShorImplementation`,
`Framework.ToomCookTable`, `Submission.Correct`. The first two look like
leftovers from when they were leaf files.

Rewrite the file as the minimal set, one comment per line saying what it
roots:

```lean
import FastMultiplication.ShorVerification.Implementation.Shor.Main                 -- correctness theorems
import FastMultiplication.ShorVerification.Implementation.QFT.Main
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Main
import FastMultiplication.ShorVerification.Implementation.GateCount.Shor_GateCount  -- resource bounds
import FastMultiplication.ShorVerification.Submission.Decide                        -- submission surface
import FastMultiplication.ShorVerification.Submission.Score
```

Confirm with `lake build FastMultiplication` that the same module set is
built (compare `ls .lake/build/lib/lean/FastMultiplication -R | wc -l`
before and after). The `Table_Generation/Generator/` subtree is
deliberately not rooted here (item 11).

## 20. Straighten the `Table_Generation` import chain — PARTIAL (step 1 only)

The subtree's real import DAG is a single chain that puts three `Core/`
files above `Builders/` and `Programs/`, and compiles the test file
`Examples.lean` on the headline path:

- `Core/ListHelpers.lean:1` imports `Builders.Fragments` and uses nothing
  from it (its own content restates `List.mem_cons`, `List.nodup_cons`,
  `List.mem_finRange` and re-declares the `<+` notation Mathlib already
  provides for `Sublist`).
- `Core/RunLemmas.lean:1` imports only `Core.ListHelpers`, so it inherits
  the chain.
- `Core/Coverage.lean:2` imports `Programs.WithProduct` and uses nothing
  from Programs or Builders; it needs `NoPhase` from `Core/RunLemmas`.
- `Builders/Fragments.lean:1` imports `Examples` and uses none of its
  eleven declarations.
- `PhaseProduct/Compiler/Layout.lean:6` imports `Core.Coverage` and uses
  only `valid_ops k`, which lives in `Framework/ToomCookTable.lean`. This
  one import drags the whole chain into the compiler layer. The files
  that genuinely use Coverage are all under `Proofs/` (`Compiler/Body/
  Controlled.lean`, `Body/Dealloc.lean`, `Compilation.lean`,
  `Lowering/PlanReadiness/BodyReadiness.lean`, `RecursiveReadiness.lean`).

Fix, in this order so each step builds:

1. `Compiler/Layout.lean:6` → `import …Framework.ToomCookTable`; add
   `import …Core.Coverage` to the five Proofs files that use it.
2. `Builders/Fragments.lean:1` → `import …Core.RegisterLemmas` (or
   `Core.Language`, whichever is the smallest that elaborates).
3. Delete `Core/ListHelpers.lean`; replace its uses with the `List.*`
   names and Mathlib's `<+`. `Core/RunLemmas.lean:1` → `import
   …Core.Language` plus whatever Mathlib list file it needs.
4. `Core/Coverage.lean:2` → `import …Core.RunLemmas`.
5. Move `Examples.lean` and the two elaborators in `Core/Tactics.lean`
   that only it uses (`prove_coverage`, `returns_to_original?`) under a
   `Table_Generation/Tests/` module that nothing on the headline path
   imports; fix `Table_Generation/README.md`'s claim that Examples'
   lemmas "are reused by later synthesis proofs" (they are not).
6. Narrow the `Math.Table_Generation*` skip in the layer script to
   `Generator*` and the two umbrella files (item 18) and let it enforce
   `Core < Builders < Programs < Tests` on the rest.

Then `scripts/gen_docs_graph.py` will stop reporting the
`Builders → Core → Builders` aggregate cycle it prints today.

## Outcomes for items 12–20

Recorded where the plan's premise did not survive contact.

**12.** `scripts/AxiomCheck.lean` (11 theorems) and
`scripts/check_template_lexical.sh` added; `ci.yml` gained *Build executables*,
*Smoke-run executables*, *Axiom guard* and *Lexical gate* steps.

Two corrections. `-KwarningAsError=true` **does not work** — verified by
appending a theorem with an unused binder and watching the build stay green
under the flag; the warnings check greps the build log instead, which was the
plan's own fallback. And building the executables immediately paid for itself:
`Submission/Main.lean` was emitting an `exponent 2047 exceeds the threshold`
warning that CI had never seen because it never built `forshor_submission`.
Fixed with a file-level `set_option exponentiation.threshold 4096`. All five
targets are now warning-free.

`lean4checker` is still not run here; `Submission/README.md` and the workflow
header both say so and say why.

**13.** Cache narrowed to `.lake/packages`, `concurrency` group added, elan
pinned to `v4.0.0` (a version confirmed to exist rather than guessed), header
and timeout comments updated.

**14.** `Emit/fixtures/` deleted. The two sections worth keeping — the register
layout and the environments — moved into `Emit/IR/README.md` alongside the six
regenerating commands, since that is the format spec a consumer reaches.

**16.** `buildPP`/`buildCPP`/`buildQFT` use `runExtract` plus a `wellFormed`
check; the full canary stays on `template`/`bundle`. Measured: annotated
`pp` at `k = 3` went from about 35 minutes to **63 seconds**. At `k = 2` the
gain is small (28 s → 21 s) because `runExtract`'s environment reload
dominates there. Argument parsing is now strict — `--falt` exits 2 instead of
silently selecting the annotated path, `shor` with wrong arity reports its own
message, and `template` has its own parser.

**18.** `scripts/check_layers.py` replaces all five bash scripts. Blind spots
fixed: `private`/`protected`/`opaque`/`example` count as declarations, files
are sorted, and the `Table_Generation` skip is narrowed to `Generator*` plus
the two umbrella files.

The `Readiness/` order is now the real partial order
(`Static, Sequencing < Primitives < {Init, Step1} < {Step2, Step5} <
{IQFT, ModMul} < ModExp < Dynamic`), enforced by making equal ranks forbid
sibling imports. Negative-tested: `Step5` importing `Step2` fails, as does a
`Reference → Shor.Proofs` import and a `Spec → Proofs` import, while a
private-only file is not flagged as an umbrella.

One correction: `Sequencing.lean` does **not** use "none of Static's
declarations" — it needs `GateWorkspaceCleanState` and `lowerGate`. Dropping
the import outright does not compile. It now imports
`Shor.Lowering.LowerGate`, which is where those actually live, so the import
is justified in the sense the READMEs promise.

**19.** Root cut from eighteen imports to six. Verified the module set is
unchanged: 224 oleans and 3302 jobs before and after.

**20 — PARTIAL.** Step 1 landed and is the valuable one:
`Compiler/Layout.lean` imports `Framework.ToomCookTable` instead of
`Core.Coverage`, so the Table_Generation chain no longer reaches the compiler
layer. It took **six** Proofs files, not the five the plan lists —
`Proofs/Compiler/Body/NoPhaseRuns.lean` also needed it, and
`Proofs/Compiler/Support.lean` needed `Core.Registers` and `Builders.Fragments`
directly.

Steps 2–5 were attempted and reverted. They are not import hygiene: the files
depend on each other's *content*, not just on re-exported names.

- `Core/RunLemmas.lean` does not merely "inherit the chain" — it uses
  `computeLocal` from `Builders/Fragments`, so `Core` genuinely sits above
  `Builders` here and the proposed `Core < Builders` table is wrong.
- `Core/Coverage.lean` does not only need `NoPhase`: with
  `Programs.WithProduct` removed, `progConsumesPts_has_blockDecomposition_aux`
  stops typechecking because `ProgConsumesPts` no longer reduces through
  `applyOp?` the way the proof expects. That is a proof change, not an import
  change.

So the aggregate cycle `Builders → Core → Builders` is still reported by
`gen_docs_graph.py`. Straightening it means deciding where `RunLemmas` and
`Coverage` belong and repairing two proofs, which is a separate piece of work
from the import bookkeeping this item assumed.

## Verification (after items 11–20)

```sh
lake build FastMultiplication EmitTests Submission forshor_emit forshor_submission
lake env lean scripts/AxiomCheck.lean
test ! -e FastMultiplication/Emit/fixtures   # item 14
python3 scripts/check_layers.py            # or the single bash entry point
python3 scripts/gen_docs_graph.py --check  # no aggregate-cycle notes
git status --porcelain                     # empty after item 17
```

and the GitHub Actions run on the PR is green on the first try, with the
cache restored from `.lake/packages` only.
