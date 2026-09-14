# REORG_COMPILATION.md — dissolve `Implementation/Compilation/` into `Implementation/Shor/`

Status: Part A is IN PROGRESS in the working tree (uncommitted: `Compilation/*` already moved to `Shor/Lowering/LowerGate.lean` and `Shor/Proofs/Lowering.lean`). Commit Part A before starting Part B. Companion to the completed PhaseProduct, QFT,
ModularExponentiation, and Shor reorganizations. Same rules as those:

* **Pure moves only.** No statement, proof, or definition changes. Only file
  paths, `import` lines, docstrings/READMEs, and the layer-check scripts change.
  (One optional, clearly-marked non-pure step is listed at the end.)
* **Justified imports only.** A file imports module `M` only if it directly uses a
  declaration `M` defines. No umbrella files (a file that only imports).
* **Two gates after every step:**
  1. `lake build` is green.
  2. `#print axioms Shor.Shor_correct` and `#print axioms Shor.exists_shorGateCountBound`
     both print exactly `[propext, Classical.choice, Quot.sound]`.

  Plus, from Step 2 on: `bash scripts/check_shor_layers.sh` exits 0.

All paths below are relative to `FastMultiplication/ShorVerification/` unless they
start with `scripts/` or are `*.md` files at the repo root.

---

## 1. What `Compilation/` is today

Two files, 778 lines, created during the Shor reorganization:

| File | Lines | Declares |
|---|---|---|
| `Implementation/Compilation/LowerGate.lean` | 226 | `GateWorkspaceOK` (static reserve precondition, recursive on `Gate`), `lowerGate k hk ops G h : LowGate` (the whole-`Gate` → `LowGate` compiler; dispatches QFT nodes to `lowerQFT`, signed phase products to `lowerSignedPhaseProdWithWorkspace`, `CmpGeConst`/`CSubConst` to `lowerCmpGeConst`/`lowerCSubConst`, and maps every other constructor to its `LowGate` twin), and `GateWorkspaceCleanState` (the dynamic clean-state precondition, noncomputable, defined by recursion through `lowerGate`). |
| `Implementation/Compilation/Correctness.lean` | 552 | Projection lemmas `GateWorkspaceOK.{left,right,of_adj,qft,signedPhaseProd,cSignedPhaseProd}`, the `@[simp]` definitional equations `lowerGate_id`, …, and the theorem `lowerGate_correctness : evalL (lowerGate k hk ops G h) ψ = qs.eval G ψ` under `GateWorkspaceOK` + `GateWorkspaceCleanState` + the two interpolation-program side conditions (`ProgConsumesPtsSafe`, `run? ops start_state = some start_state`). |

**Its imports** (all downward, none from `Shor/`, `GateCount/`, `Reference/`):

* `LowerGate.lean` ← `QFT/Lowering/{Workspace,PlanBuilders}`, `QFT/Spec/Cleanliness`,
  `PhaseProduct/Compiler/Workspace`, `PhaseProduct/Lowering/Lower`, `PhaseProduct/Spec/Cleanliness`,
  `ModularExponentiation/Circuit/Workspace`, `ModularExponentiation/Lowering/ConstArithmetic`,
  `ModularExponentiation/Spec/Validity`.
* `Correctness.lean` ← `Compilation/LowerGate`, `QFT/Proofs/Lowering/Readiness`,
  `PhaseProduct/Compiler/{Coefficients,Workspace}`, `PhaseProduct/Lowering/Lower`,
  `PhaseProduct/Spec/Cleanliness`, `PhaseProduct/Main`, `ModularExponentiation/Proofs/ConstArithmetic`.

**Its importers** (12 import lines, all in `Shor/` and `GateCount/`):

```
Implementation/Shor/Circuit/OrderFinding.lean:1        Compilation.LowerGate
Implementation/Shor/Proofs/Readiness/Step1.lean:3      Compilation.LowerGate
Implementation/GateCount/Definitions.lean:1            Compilation.LowerGate
Implementation/Shor/Proofs/Readiness/Init.lean:3       Compilation.Correctness
Implementation/Shor/Proofs/Readiness/Primitives.lean:3 Compilation.Correctness
Implementation/Shor/Proofs/Readiness/Step2.lean:2      Compilation.Correctness
Implementation/Shor/Proofs/Readiness/Step5.lean:2      Compilation.Correctness
Implementation/Shor/Proofs/Readiness/IQFT.lean:3       Compilation.Correctness
Implementation/Shor/Proofs/Readiness/Dynamic.lean:12   Compilation.Correctness
Implementation/Shor/Proofs/Correctness.lean:3          Compilation.Correctness
Implementation/GateCount/Shor_GateCount.lean:7         Compilation.Correctness
Implementation/Compilation/Correctness.lean:1          Compilation.LowerGate   (internal)
```

`Reference/ShorProgram.lean` uses `lowerGate` too, but gets it through
`Shor/Circuit/OrderFinding.lean` (`orderFindingApproxLow`), not by importing
`Compilation/` directly.

## 2. Why dissolve it, and where it goes

`lowerGate` is not a fourth subroutine. It is the **whole-program** lowerer of
the Shor source language: it is the one place that knows about all three
subroutine lowerers at once, and its only consumers are the Shor assembly
(`Shor/Circuit/OrderFinding.lean` builds `orderFindingApproxLow` with it), the
Shor readiness/correctness proofs, and the resource-estimation layer that
counts the Shor circuit. A two-file top-level folder for that costs a README, a
dedicated layer script, and one more name for a reader to hold, and its
`Correctness.lean` docstring is a verbatim copy of `LowerGate.lean`'s (never
retitled), which is the usual sign that a folder was created to park files, not
to explain them.

The per-subroutine folders already have the right pattern for this:
`QFT/Lowering/*.lean`, `ModularExponentiation/Lowering/*.lean`,
`PhaseProduct/Lowering/*.lean` hold lowerers; their proofs live under the
folder's `Proofs/`. `Shor/` is the assembly layer and lacks exactly that pair.

**Destination: `Implementation/Shor/`.**

| From | To | Kind |
|---|---|---|
| `Implementation/Compilation/LowerGate.lean` | `Implementation/Shor/Lowering/LowerGate.lean` | pure move |
| `Implementation/Compilation/Correctness.lean` | `Implementation/Shor/Proofs/Lowering.lean` | pure move |
| `Implementation/Compilation/` | (deleted) | |
| `scripts/check_compilation_layers.sh` | (deleted; its rules fold into `check_shor_layers.sh`) | |

Why not the other remaining folders:

* **`Semantics/`** (renamed `Shared/` in Part B) sits *below* the subroutine folders in the import order and admits only files that depend on nothing in them; `lowerGate` depends on all three.
* **`PhaseProduct/`, `QFT/`, `ModularExponentiation/`**: `lowerGate` imports lowerers from all three. Placing it in any one of them makes that folder import its two siblings, breaking each folder's "no sideways imports" layer script.
* **`GateCount/`** is a consumer of `lowerGate`, not its owner; `Shor/Circuit/OrderFinding.lean` would have to import `GateCount`, inverting the dependency.
* **`Reference/`** imports `Shor/Main.lean`; `Shor/Circuit/OrderFinding.lean` needs `lowerGate`, so `Reference/` is also upward of the only sensible owner.

### New `Shor/` layer order

```
Math  <  Lowering  <  Circuit  <  Spec  <  Proofs  <  Main
```

`Lowering/LowerGate.lean` imports nothing from `Shor/` (verified above), so it
can sit below `Circuit/`; it must, because `Circuit/OrderFinding.lean` imports
it. Inside `Proofs/`:

```
Lowering, Budgets, Setup  <  Readiness/*  <  NaiveShor/*  <  Correctness
```

`Proofs/Lowering.lean` imports nothing from `Shor/` either, so it joins the
bottom rung. Every current importer of `Compilation.Correctness` is at
`Readiness/*` or above, so no existing edge is violated.

### The one exception that already exists is unaffected

`Spec/Assertions.lean → Proofs/Readiness/Static.lean` (allowlisted in
`check_shor_layers.sh`) does not involve either moved file. `Static.lean`
imports `Compilation.*`? No — it does not appear in the importer list; it
reaches `GateWorkspaceOK` through `Circuit/OrderFinding.lean`. Nothing to do.

---

## 3. Steps

### Step 1 — move the two files and repoint the 11 external import lines

```bash
cd FastMultiplication/ShorVerification
mkdir -p Implementation/Shor/Lowering
git mv Implementation/Compilation/LowerGate.lean   Implementation/Shor/Lowering/LowerGate.lean
git mv Implementation/Compilation/Correctness.lean Implementation/Shor/Proofs/Lowering.lean
rmdir Implementation/Compilation
```

Rewrite import lines (12 total; the internal one is in the moved
`Proofs/Lowering.lean` itself):

| old module | new module |
|---|---|
| `FastMultiplication.ShorVerification.Implementation.Compilation.LowerGate` | `FastMultiplication.ShorVerification.Implementation.Shor.Lowering.LowerGate` |
| `FastMultiplication.ShorVerification.Implementation.Compilation.Correctness` | `FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Lowering` |

Files to edit: the 12 listed in §1 (after the move, the internal one is
`Implementation/Shor/Proofs/Lowering.lean:1`). Do it with a scoped `sed` and
then confirm nothing is left:

```bash
grep -rl "Implementation\.Compilation\." --include='*.lean' . | xargs sed -i '' \
  -e 's/Implementation\.Compilation\.LowerGate/Implementation.Shor.Lowering.LowerGate/' \
  -e 's/Implementation\.Compilation\.Correctness/Implementation.Shor.Proofs.Lowering/'
grep -rn "Implementation\.Compilation" . && echo "STALE IMPORT" || echo "clean"
```

Then both gates (`lake build`; the two `#print axioms`).

Justified-import check for the moved files: their own import lists are
unchanged and were already justified; only their module names changed. For
the 11 importers, the imported *declarations* are unchanged, so the imports
stay justified.

### Step 2 — fold the layer script

Delete `scripts/check_compilation_layers.sh`. Edit
`scripts/check_shor_layers.sh`:

1. In the `layer()` case table, add two lines (numbers chosen to slot into the
   existing scheme: `Math*` is 10, `Circuit*` is 20, `Proofs.Budgets|Proofs.Setup` is 40):

   ```bash
   Lowering*) echo 15;;
   Proofs.Lowering) echo 40;;
   ```

   Put `Lowering*)` after `Math*)` and `Proofs.Lowering)` on the same line as
   `Proofs.Budgets|Proofs.Setup)` (i.e. `Proofs.Budgets|Proofs.Setup|Proofs.Lowering) echo 40;;`).
   Order matters in a `case`: `Proofs.Lowering` must be matched before any
   `Proofs*` catch-all, and `Lowering*` must not be shadowed by `Proofs.Lowering`
   (it is not, since `Proofs.Lowering` does not start with `Lowering`).

2. Update the header comment's layer order to
   `Math < Lowering < Circuit < Spec < Proofs < Main` and the `Proofs/` rung to
   `Lowering, Budgets, Setup < Readiness/* < NaiveShor/* < Correctness`.

3. The old compilation script also enforced "no file under Compilation/ may import
   Shor.*, GateCount.*, or Reference.*". The `Shor.*` half is now enforced by the
   layer numbers (a `Lowering*` file importing `Shor.Circuit.*` is a layer
   violation). Keep the `GateCount`/`Reference` half by adding, inside the
   per-file loop of `check_shor_layers.sh`, the same forbidden-upward-import
   check the deleted script had, applied to **every** `Shor/` file (the whole of
   `Shor/` sits below `GateCount/` and `Reference/`, so this is a correct
   strengthening, not a new rule for the two moved files only):

   ```bash
   if grep -oE '^import FastMultiplication\.ShorVerification\.Implementation\.(GateCount|Reference)\.[A-Za-z0-9_.]+' "$f" >/dev/null; then
     echo "FORBIDDEN UPWARD IMPORT: $mod imports a GateCount/Reference module"; status=1
   fi
   ```

   Before adding it, confirm it is already true today:
   `grep -rn "Implementation\.\(GateCount\|Reference\)\." Implementation/Shor` must
   print nothing.

Run `bash scripts/check_shor_layers.sh` → exit 0. Then both gates again (the
script edit cannot break the build, but the habit is the point).

### Step 3 — fix the copied docstring (doc-only)

`Implementation/Shor/Proofs/Lowering.lean` opens with the same `/-! # Whole-Program
Lowering … -/` block as `Lowering/LowerGate.lean`. Replace the body of that
docstring (text only, nothing after `-/` changes) with a description of what the
file actually contains:

* the `GateWorkspaceOK` projection lemmas (how a `GateWorkspaceOK` proof for a
  compound gate yields proofs for its parts);
* the `@[simp]` definitional equations for `lowerGate`;
* `lowerGate_correctness`, stating that the lowered program has the same action
  as the source gate whenever the static precondition (`GateWorkspaceOK`) and
  the dynamic one (`GateWorkspaceCleanState`) hold, given the interpolation
  program's `ProgConsumesPtsSafe`/`run?` side conditions (the two fields
  `ShorLoweringSetup.consumes`/`.returns` provide them).

Retitle it `# Whole-program lowering correctness`. Both gates.

### Step 4 — READMEs

1. **New `Implementation/Shor/Lowering/README.md`.** Same shape as
   `Shor/Circuit/README.md`: one paragraph on the folder's role (the whole-`Gate`
   lowerer that dispatches to the three subroutine lowerers; it imports from
   `QFT/`, `PhaseProduct/`, `ModularExponentiation/` and nothing from `Shor/`),
   then bullets for `GateWorkspaceOK`, `lowerGate` (list the dispatch table:
   `QFT ↦ lowerQFT`, `SignedPhaseProd ↦ lowerSignedPhaseProdWithWorkspace`,
   `CSignedPhaseProd ↦ lowerCSignedPhaseProdWithWorkspace`, `CmpGeConst ↦ lowerCmpGeConst`,
   `CSubConst ↦ lowerCSubConst`, all other constructors ↦ their `LowGate` twin), and
   `GateWorkspaceCleanState`. Keep the existing docstring note that the
   controlled-phase-product branch uses the naive controlled leaf pending a
   `CSignedRecursiveWorkspaceOK`-driven plan constructor.

2. **`Implementation/Shor/README.md`:**
   * Paragraph 1: change "pieces proved in `Compilation/`, `QFT/`, `PhaseProduct/`, and `ModularExponentiation/`" to "pieces proved in `QFT/`, `PhaseProduct/`, and `ModularExponentiation/`", and add that the whole-program lowerer itself now lives in `Lowering/`.
   * Delete the sentence beginning "`scripts/check_compilation_layers.sh` enforces the analogous discipline…".
   * Layer order block → `Math < Lowering < Circuit < Spec < Proofs < Main`; `Proofs/` rung → `Lowering, Budgets, Setup < Readiness/* < NaiveShor/* < Correctness`.
   * Add a `## Lowering/ — the whole-program Gate → LowGate lowerer` section between `Math/` and `Circuit/`, with a one-row table for `LowerGate.lean`.
   * In the `## Proofs/` table add a first row `Lowering.lean | Correctness of the whole-program lowerer (`lowerGate_correctness`), the `GateWorkspaceOK` projection lemmas, and the `lowerGate` simp equations. Imports nothing from `Shor/`; consumed by `Readiness/*`, `Correctness.lean`, and `GateCount/`.`
   * In the reading-order paragraph, add `Lowering/` to the list of folders one walks outward into.

3. **`Implementation/Shor/Circuit/README.md`:** in the `orderFindingApproxLow` bullet, "via `lowerGate`" → "via `lowerGate` (`Shor/Lowering/LowerGate.lean`)".

4. **`Implementation/Shor/Proofs/README.md`:** add the `Lowering.lean` row (same text as above). `Proofs/Readiness/README.md` mentions `GateWorkspaceOK`/`GateWorkspaceCleanState` by name only, no paths — no change.

5. **Repo root `ARCHITECTURE.md` line 29** still says
   `Implementation/Shor/Proofs/WholeProgramCorrectness.lean` (already stale from the
   Shor reorg). Change it to `Implementation/Shor/Proofs/Lowering.lean` and add
   `Implementation/Shor/Lowering/LowerGate.lean` for the lowerer itself.
   `README.md`'s `Shor/` row already says "whole-program lowering correctness" — no change.
   `RESTRUCTURE_PLAN.md` line 68 names `Compilation/` as a *planned* folder; that
   file is a historical plan, leave it, or add one line under Phase 4 noting the
   compiler ended up at `Shor/Lowering/`.

Both gates and the layer script.

### Step 5 — final audit

```bash
find FastMultiplication/ShorVerification/Implementation -maxdepth 1 -type d | sort
# expect: GateCount ModularExponentiation PhaseProduct QFT Reference Semantics Shor  (no Compilation)
grep -rn "Compilation" FastMultiplication/ShorVerification/Implementation/Shor --include='*.md' --include='*.lean'
# expect: nothing (PhaseProduct's own Compiler/Compilation.lean is unrelated and untouched)
bash scripts/check_shor_layers.sh && bash scripts/check_qft_layers.sh \
  && bash scripts/check_modexp_layers.sh && bash scripts/check_phaseproduct_layers.sh
lake build
```

and the two `#print axioms`.

---

## 4. Optional Step 6 — split the clean-state predicate out (NOT a pure move; do only if asked)

`GateWorkspaceCleanState` (the last 60 lines of `Lowering/LowerGate.lean`) is a
noncomputable, `QSemantics`-indexed `Prop`, the dynamic twin of the purely
static `GateWorkspaceOK`. Its own docstring in the file header says cleanliness
"belongs in the later semantic-correctness theorem", and `Shor/Spec/Cleanliness.lean`
is exactly the file that collects "static clean-input predicates and dynamic
clean-state invariants". Moving the one declaration there would:

* make `Lowering/LowerGate.lean` entirely computable definitions (`GateWorkspaceOK`,
  `lowerGate`), which is what `GateCount/Definitions.lean` and the JSON emitter
  actually need from it;
* put the dynamic precondition next to `ShorLoweringCleanState`/`ShorConcreteCleanState`,
  which the readiness proofs relate it to.

Layer check: `Spec/Cleanliness.lean` may import `Lowering/LowerGate.lean` (Spec is
above Lowering), and `GateWorkspaceCleanState` needs `lowerGate` for its `seq`
case, so the edge is legal. All 10 users of `GateWorkspaceCleanState` are under
`Shor/Proofs/` and already import `Spec/Cleanliness.lean` or sit above it; each
would need `Spec.Cleanliness` added to its imports only if it does not already
import it (check with `grep -L`). `Lowering/LowerGate.lean` would drop the imports
it only needed for the clean-state case (`QFT/Spec/Cleanliness`,
`PhaseProduct/Spec/Cleanliness`, and whichever `ModularExponentiation` module
defines `CmpGeConstCleanState`/`CSubConstCleanState`) — verify with the
justified-import rule before removing each.

This is a declaration move, so it is outside the "pure file move" contract of
Steps 1–5. Same two gates apply.

---

# Part B — rename `Implementation/Semantics/` to `Implementation/Shared/` and reorganize it by topic

Independent of Part A except that both touch import lines in `Shor/Proofs/`;
commit Part A first. Rules: file moves are pure; the one large file is **split
at its own section banners** into topic files (cut-and-paste of contiguous
blocks, no edits inside a block); the one-definition file is merged into the
topic file it belongs to; import lines are repointed to the specific new file
each importer actually uses. No Framework changes. Two gates after every step.

## 6. What the folder is, and why "Shared"

Today `Implementation/Semantics/` holds four files, and a fifth that belongs
with them sits loose at `Implementation/RegisterLemmas.lean`:

| File | Lines | Decls | About | Imports from `Implementation/` |
|---|---|---|---|---|
| `RegisterLemmas.lean` (stray) | 1,117 | 41 | derived `Reg`/`RegEncoding`/`ExtReg` laws | none |
| `Semantics/CleanClosure.lean` | 26 | 1 | the `zero/ket/add/smul` closure of `P`-clean kets | none |
| `Semantics/GateSemanticsLemmas.lean` | 3,229 | 93 | twelve unrelated topics (below) | `RegisterLemmas`, `CleanClosure` (stale) |
| `Semantics/Measurement.lean` | 621 | 14 | `MeasureClass` → probability estimates | none |
| `Semantics/QftPhase.lean` | 58 | 6 | `qftPhase`/`ωPow` facts | none |

What they have in common is not "semantics" (`RegisterLemmas` and `QftPhase`
contain no `QSemantics` at all). It is their **position**: each is a lemma
library over Framework vocabulary, imports nothing from any subroutine folder,
and is imported by two or more of `PhaseProduct/`, `QFT/`,
`ModularExponentiation/`, `Shor/`. That is an admission rule a script can
check, so name the folder after it:

```
Implementation/Shared/
```

Admission rule (goes in the README and the layer script): a file lives in
`Shared/` iff (a) it imports only `Framework/`, Mathlib, and other `Shared/`
files, and (b) it is imported from at least two different folders among
`PhaseProduct`, `QFT`, `ModularExponentiation`, `Shor`, `GateCount`, `Reference`.
(a) is enforced; (b) is reported. Rejected names: `Common`/`Basic` (say nothing
about the rule), `Semantics` (false for two of five files), `Lemmas` (false for
`CleanClosure`, a definition).

### The big file, section by section

`GateSemanticsLemmas.lean` is twelve banner-delimited sections in two halves
(lines as of commit `854daf9`; **locate blocks by banner text when executing,
not by line number**):

| Lines | Banner | Decls | Namespace(s) opened | Depends on (earlier sections only) |
|---|---|---|---|---|
| 27–553 | Register And Hadamard Support | 6 | `Shor` | — |
| 554–707 | Derived Core Evaluator Laws | 6 | `Shor.GateSemanticsCore` | — |
| 708–964 | Register-Hadamard Span Closure | 5 | `Shor.RegisterHadamardSemantics` | — |
| 965–1055 | QSemantics Projection Wrappers | 9 | `Shor.QSemantics` | Derived Core (`eval_apply_adj`, `eval_zero`) |
| 1056–1267 | Bit And Basis Transport Helpers | 4 | `Shor` | — |
| 1268–1330 | Pauli-X And Extension Locality | 2 | `Shor`, `Shor.PauliXSemantics` | Bit/Basis Transport |
| 1331–1360 | Unsigned Phase-Product Macro Semantics | 1 | `Shor.GateSemanticsFacts` | Pauli-X |
| 1361–1379 | Evaluation Sums | 1 | `Shor` | Wrappers |
| 1380–1391 | Encoding Transport | 1 | `Shor` | — |
| 1392–1515 | Norms, Isometry, And Freshness Transport | 4 | `Shor` | Derived Core, Wrappers |
| 1516–2181 | Framework Gate Semantics Proofs | 16 | `Shor`, `Shor.RadixReverseSemantics`, `Shor.GateSemanticsCore`, `Shor.ExtensionSemantics` | Derived Core, Wrappers, Encoding Transport |
| 2182–2740 | Generic basis-write arithmetic lemmas (first part, through `end ArithmeticSemantics`) | ~24 | `Shor`, `Shor.ArithmeticSemantics` | Wrappers, Encoding Transport, Framework Gate Semantics Proofs |
| 2742–3228 | same section, second part: `namespace LowerGateClass … end LowerGateGateBridge` | ~14 | `Shor.LowerGateClass`, `Shor.LowerGateGateBridge` | the part above, plus Wrappers |

Lean resolves names top-down within a file, so these dependencies are exact in
direction (a section can only use earlier ones) and were confirmed by a
name scan; the scan cannot see `simp`-set use of `@[simp]` lemmas, which is
why every split step below ends with `lake build` as the real check.

Scoping that must be reproduced in every new file (from lines 20–25 and 954–962):

```lean
namespace Shor
universe u
variable {Basis : Type u} [RegEncoding Basis]
open QSemantics
```

and, only where norms/inner products are used (the `Norms…` block and anything
built on it), the two persistent attributes from lines 961–962:

```lean
attribute [instance] QSemantics.instNormed
attribute [instance] QSemantics.instIP
```

Put those two lines in exactly one file (`States.lean`) and let dependants
import it; do not repeat them.

The `section SharedRegisterAndEvalFacts … end SharedRegisterAndEvalFacts`
wrapper around the first half is anonymous scoping only (sections add no name
prefix), so cutting through it changes no declaration name.

## 7. Target layout

```
Implementation/Shared/
  README.md
  Registers.lean      ← RegisterLemmas.lean (whole)
                        + GSL "Bit And Basis Transport Helpers"
                        + GSL "Encoding Transport"
  States.lean         ← GSL "Derived Core Evaluator Laws"
                        + GSL "QSemantics Projection Wrappers"
                        + GSL "Evaluation Sums"
                        + GSL "Norms, Isometry, And Freshness Transport"
                        + CleanClosure.lean (the inductive)
  Hadamard.lean       ← GSL "Register And Hadamard Support"
                        + GSL "Register-Hadamard Span Closure"
  GateLaws.lean       ← GSL "Pauli-X And Extension Locality"
                        + GSL "Unsigned Phase-Product Macro Semantics"
                        + GSL "Framework Gate Semantics Proofs"
                        + GSL "Generic basis-write arithmetic lemmas" (first part, to `end ArithmeticSemantics`)
  LowGateEval.lean    ← GSL "Generic basis-write arithmetic lemmas" (second part: LowerGateClass + LowerGateGateBridge)
  Measurement.lean    ← Semantics/Measurement.lean (unchanged)
  QftPhase.lean       ← Semantics/QftPhase.lean (unchanged; docstring path fixed)
```

Approximate sizes: Registers 1,340 · States 420 · Hadamard 780 · GateLaws 1,320 ·
LowGateEval 490 · Measurement 621 · QftPhase 58. Every file is about one thing
and mirrors one Framework module:

| `Shared/` file | Derived laws of |
|---|---|
| `Registers.lean` | `Framework/Quantum/Registers.lean` (`Reg`, `RegEncoding`, `ExtReg`, two's complement) |
| `States.lean` | `Framework/Quantum/QSemantics.lean` (`eval` algebra, norms, isometry, freshness, `CleanClosure`) |
| `Hadamard.lean` | `H_reg` on a register: uniform superposition, span closure |
| `GateLaws.lean` | `Framework/Semantics/GateSemantics.lean` classes (Pauli-X, extension, radix reverse, arithmetic basis functions) |
| `LowGateEval.lean` | `Framework/Semantics/LowGateSemantics.lean` (`LowerGateClass.evalL` on each primitive, the Gate bridge) |
| `Measurement.lean` | `Framework/Quantum/Measurement.lean` (`MeasureClass`) |
| `QftPhase.lean` | `qftPhase`/`ωPow` from `Framework/AbstractMachine/Gates.lean` |

Internal layer order (from the dependency table):

```
QftPhase, Registers  <  States  <  Hadamard, GateLaws  <  LowGateEval        Measurement (independent)
```

`CleanClosure` goes into `States.lean` because it is a predicate on
`qs.State`. Cost: the four `Spec/` files that import it for that one inductive
will also pull the norm/isometry lemmas and their `InnerProductSpace` import.
If that weight matters, the alternative is a sixth tiny file — which is the
one-definition file you asked to remove, so the plan does not propose it.

### Who imports what afterwards

From the name scan (verify each with the build; add a file only if the build
needs it, per the justified-import rule):

| Importer (today imports `GateSemanticsLemmas`) | Needs |
|---|---|
| `PhaseProduct/Proofs/Compiler/MacroSemantics.lean`, `Proofs/Compiler/Support.lean` | `States` |
| `PhaseProduct/Proofs/Lowering/EvalL.lean` | `States`, `LowGateEval` |
| `PhaseProduct/Proofs/Lowering/Workspace.lean` | `States` |
| `QFT/Proofs/Decomposition.lean` | `States`, `Registers`, `GateLaws` (`eval_RadixReverse_ket`) |
| `QFT/Proofs/Lowering/PlanSemantics.lean` | `States`, `Hadamard` (`eq_qubitReg_lowQubit`, `omega_two`), `LowGateEval` |
| `QFT/Proofs/Lowering/Readiness.lean` | `States`, `Registers` |
| `ModularExponentiation/Proofs/Algorithm1Expansion.lean` | `States`, `Hadamard`, `Registers` |
| `ModularExponentiation/Proofs/Core.lean` | `States`, `Hadamard`, `Registers` |
| `ModularExponentiation/Proofs/Step1QPE.lean`, `Step2Bound.lean` | `States`, `Registers` |
| `Shor/Proofs/Readiness/{Init,Primitives,Step1,Step2,Step5}.lean` | `States`, `Registers` |
| `ModularExponentiation/Spec/Validity.lean` | `States` (it needs `CleanClosure`; whether it needs anything else from the old file is tested in Step 13) |
| `ModularExponentiation/Circuit/Workspace.lean`, `Lowering/ConstArithmetic.lean`, `Proofs/Model.lean` | **possibly nothing** — tested in Step 13 |

Importers of `RegisterLemmas` (14) → `Shared.Registers`, except
`PhaseProduct/Gates/NaiveLeaf.lean` and `Gates/Macros.lean`, which showed no
use and are tested in Step 13. Importers of `CleanClosure` (four `Spec/` files) →
`Shared.States`. `Shor/Proofs/Correctness.lean` → `Shared.Measurement`.
`ModularExponentiation/Proofs/CmpLtNW.lean`, `Shor/Math/OrderFindingAnalysis.lean` → `Shared.QftPhase`.

## 8. Steps

Work bottom-up so every intermediate tree builds. Until Step 12 the old
`GateSemanticsLemmas.lean` keeps existing and keeps compiling with fewer and
fewer sections in it; each step moves blocks *out* of it and repoints nothing
until the file is empty. That way each step is small and the build tells you
immediately if a moved block needed something you did not move.

### Step 7 — rename the folder, move the stray file, fix the two trivial files

```bash
cd FastMultiplication/ShorVerification
git mv Implementation/Semantics Implementation/Shared
git mv Implementation/RegisterLemmas.lean Implementation/Shared/Registers.lean
grep -rl "Implementation\.Semantics\.\|Implementation\.RegisterLemmas" --include='*.lean' . | xargs sed -i '' \
  -e 's/Implementation\.Semantics\./Implementation.Shared./' \
  -e 's/Implementation\.RegisterLemmas/Implementation.Shared.Registers/'
grep -rn "Implementation\.Semantics\|Implementation\.RegisterLemmas" . && echo STALE || echo clean
```

Then, in `Shared/QftPhase.lean`'s docstring, `Shor/Proofs/NaiveShor/Lemmas.lean`
→ `Shor/Math/OrderFindingAnalysis.lean`. In `Shared/Registers.lean` retitle the
header "Implementation-side register laws" → "Register and encoding laws" (body
unchanged). Both gates. (At this point `Shared/` still contains
`GateSemanticsLemmas.lean` and `CleanClosure.lean`; that is expected.)

### Step 8 — create `Shared/States.lean`

1. New file with the imports the moved blocks need. Start from
   `GateSemanticsLemmas.lean`'s import list minus `Shared.Registers` and minus
   `Shared.CleanClosure`; delete any import the build does not need afterwards.
   Preamble: the four scoping lines from §6, then the two `attribute [instance]`
   lines.
2. **Cut** (remove from `GateSemanticsLemmas.lean`, paste unchanged) in this order:
   "Derived Core Evaluator Laws" (`namespace GateSemanticsCore … end GateSemanticsCore`
   inclusive), then "QSemantics Projection Wrappers" (`namespace QSemantics … end QSemantics`),
   then "Evaluation Sums", then "Norms, Isometry, And Freshness Transport". Cut
   each block from its banner comment through the last line before the next banner.
3. In `GateSemanticsLemmas.lean` add `import …Implementation.Shared.States` (its
   remaining sections use the wrappers). Delete the two `attribute [instance]`
   lines from it (they now live in `States.lean`, which it imports).
4. Append the `CleanClosure` inductive **byte-for-byte** from
   `Shared/CleanClosure.lean` at the end of `States.lean` under a banner
   `/-! ### Basis-clean linear closure -/`; `git rm Shared/CleanClosure.lean`;
   repoint the four `Spec/` importers (`…Shared.CleanClosure` → `…Shared.States`);
   delete the stale `import …Shared.CleanClosure` line from `GateSemanticsLemmas.lean`
   (0 uses).
5. `lake build`. Expected failures and fixes: a moved lemma referring to a name
   that is still in the old file → that name's block belongs in an earlier file
   than you thought; check the dependency table, do not re-import the old file
   from `States.lean` (that would be a cycle). Both gates.

### Step 9 — create `Shared/Hadamard.lean`

Imports: `Shared.Registers` (the block uses `toNat_left_write_right` and
`splitLeft_splitRight_disjoint` from it), `Shared.States` only if the build
demands it, plus whatever Framework/Mathlib the block needs. Preamble: the four
scoping lines. Cut "Register And Hadamard Support" and "Register-Hadamard Span
Closure" (`namespace RegisterHadamardSemantics … end RegisterHadamardSemantics`).
After this cut the `section SharedRegisterAndEvalFacts … end` wrapper in the old
file is empty; delete those two lines and the `universe`/`variable`/`open` lines
between them if nothing remains in that section. Both gates.

### Step 10 — create `Shared/GateLaws.lean`

Imports: `Shared.Registers`, `Shared.States`. Preamble: four scoping lines. Cut,
in order: "Bit And Basis Transport Helpers" **into `Registers.lean`** (append at
its end under its own banner; it is pure `RegEncoding` material and Pauli-X
needs it, so `Registers` must own it before `GateLaws` can import it), then
"Encoding Transport" **into `Registers.lean`** likewise; then into `GateLaws.lean`:
"Pauli-X And Extension Locality", "Unsigned Phase-Product Macro Semantics"
(`namespace GateSemanticsFacts` block, with its three `variable` lines), "Framework
Gate Semantics Proofs", and the first part of "Generic basis-write arithmetic
lemmas" from its banner through the line `end ArithmeticSemantics`. Both gates
after the `Registers` appends, and again after the `GateLaws` cut.

Check before appending to `Registers.lean`: the "Encoding Transport" block defines
`toNat_left_write_right` at `Shor` scope while `Registers.lean` already has
`RegEncoding.toNat_left_write_right`. Different namespaces, no clash; but confirm
the block's proof does not itself `open RegEncoding` in a way that makes the name
ambiguous. If the build complains, the fix is a qualified name inside the moved
proof — the only in-block edit this plan permits, and it must be recorded.

### Step 11 — create `Shared/LowGateEval.lean`

Imports: `Shared.GateLaws`, `Shared.States`, `Shared.Registers` (drop any the
build does not need). Preamble: four scoping lines. Cut the remainder:
`namespace LowerGateClass … end LowerGateClass` and
`namespace LowerGateGateBridge … end LowerGateGateBridge` (note the
`open LowerGateClass` on the line after the second `namespace`). Both gates.

### Step 12 — retire `GateSemanticsLemmas.lean`, repoint its 20 importers

The old file must now contain only its header docstring, `namespace Shor`,
scoping lines, and `end Shor`. Confirm with `grep -cE '^(theorem|lemma|def|@\[)'`
→ `0`. `git rm` it. For each of the 20 importers, replace
`import …Shared.GateSemanticsLemmas` with the imports in the "Who imports what"
table, then `lake build`; add a `Shared.*` import only where the build asks for
a name, remove any the build does not need. Both gates.

### Step 13 — test the suspected stale imports (import-line deletions only)

One at a time, delete the import and `lake build`; green → keep deleted, red →
restore exactly. Record outcomes in the commit message.

| File | Suspected stale import of |
|---|---|
| `ModularExponentiation/Circuit/Workspace.lean` | the old `GateSemanticsLemmas` (0 named uses, 5 `simp`) |
| `ModularExponentiation/Lowering/ConstArithmetic.lean` | same (0 named uses, 3 `simp`) |
| `ModularExponentiation/Proofs/Model.lean` | same (0 named uses of its declarations; its 25 `RegEncoding.*` names are Framework's) |
| `ModularExponentiation/Spec/Validity.lean` | same beyond `CleanClosure` (keep `Shared.States`) |
| `PhaseProduct/Gates/NaiveLeaf.lean` | `Shared.Registers` (0 uses, 0 `simp`) |
| `PhaseProduct/Gates/Macros.lean` | `Shared.Registers` (0 named uses; 2 `RegEncoding.*` names may be Framework's) |

### Step 14 — README, layer script, docs

1. **`Shared/README.md`**: the admission rule from §6 verbatim; the table from §7
   ("Derived laws of"); the internal layer order; one line per file on what it
   contains and who imports it (verify with `grep -rl`).
2. **`scripts/check_shared_layers.sh`**, modelled on the existing scripts:
   umbrella detector; internal order `QftPhase=1, Registers=1, Measurement=1,
   States=2, Hadamard=3, GateLaws=3, LowGateEval=4`; **forbidden import** of
   `…Implementation.(PhaseProduct|QFT|ModularExponentiation|Shor|GateCount|Reference).*`
   from any `Shared/` file (rule (a)); and an informational check for rule (b):
   for each `Shared/*.lean`, count the distinct top-level Implementation folders
   that import it and print a `WARNING` if fewer than 2 (not a failure — a file
   can be legitimately shared-in-waiting, but the warning makes it visible).
3. **`Shor/Proofs/README.md` line 77**: "from `Semantics/Measurement.lean`" →
   "from `Shared/Measurement.lean`". Search all READMEs for `Semantics/` (excluding
   `Framework/Semantics`) and `RegisterLemmas.lean` (excluding `Table_Generation`)
   and repoint; the earlier grep found only that one line plus
   `Framework/Quantum/Registers.lean:19`.
4. **`Framework/Quantum/Registers.lean` line 19** (docstring only) cites
   `Implementation/RegisterLemmas.lean`. It is a comment inside the Framework:
   **ask before editing**; otherwise record the stale citation in `Shared/README.md`.
5. **Root `README.md`** folder table (lines 63–69) has no row for the shared
   folder; add `Implementation/Shared/` with one line: "Lemma libraries over
   Framework vocabulary shared by every subroutine folder; imports nothing from
   them."  **`ARCHITECTURE.md`** does not name the folder (checked); no change.

Both gates and all five layer scripts.

### Step 15 — audit

```bash
cd FastMultiplication/ShorVerification
ls Implementation/*.lean 2>/dev/null                       # nothing
ls Implementation/Shared                                   # GateLaws Hadamard LowGateEval Measurement QftPhase README.md Registers States
grep -rn "Implementation\.Semantics\|Implementation\.RegisterLemmas\|GateSemanticsLemmas\|Shared\.CleanClosure" . --include='*.lean' --include='*.md' | grep -v REORG   # nothing
for s in ../../scripts/check_*_layers.sh; do bash "$s" || echo "FAIL $s"; done
lake build
```

and the two `#print axioms`.

## 9. Why this is worth a split rather than a rename

A rename alone leaves a 3,229-line file whose twelve sections have five
different subjects and whose every importer pays for all of it. After the split,
the Shor readiness files import ~1,800 lines (`States` + `Registers`) instead of
~4,350 (`GateSemanticsLemmas` + `RegisterLemmas`), the four `Spec/` files that
only want `CleanClosure` import one 420-line file, and each `Shared/` file has a
name that says which Framework module it is the lemma library for. The section
banners already drew the cut lines; the plan only turns them into files.

---

## 10. Checklist

Part A (in progress in the working tree)
- [ ] Step 1: `git mv` ×2, `rmdir`, 12 import lines rewritten, `grep` shows no `Implementation.Compilation`, build green, axioms unchanged.
- [ ] Step 2: `check_compilation_layers.sh` deleted; `check_shor_layers.sh` has `Lowering*`=15 and `Proofs.Lowering`=40, updated header, GateCount/Reference upward-import check; script exits 0; build green; axioms unchanged.
- [ ] Step 3: `Proofs/Lowering.lean` docstring retitled and describes its contents; build green; axioms unchanged.
- [ ] Step 4: `Shor/Lowering/README.md` created; `Shor/README.md`, `Shor/Circuit/README.md`, `Shor/Proofs/README.md`, root `ARCHITECTURE.md` updated; build green; axioms unchanged.
- [ ] Step 5: audit commands clean. Commit.
- [ ] (optional) Step 6 only on explicit request.

Part B
- [ ] Step 7: folder renamed `Shared/`; `Registers.lean` in it; all `Semantics.`/`RegisterLemmas` imports repointed; `QftPhase` docstring fixed; build green; axioms unchanged.
- [ ] Step 8: `States.lean` created (4 blocks + `CleanClosure`, attributes moved); `CleanClosure.lean` deleted; 4 `Spec` imports repointed; build green; axioms unchanged.
- [ ] Step 9: `Hadamard.lean` created (2 blocks); empty `section` wrapper removed from old file; build green; axioms unchanged.
- [ ] Step 10: 2 blocks appended to `Registers.lean`; `GateLaws.lean` created (4 blocks); any in-block qualified-name edit recorded; build green; axioms unchanged.
- [ ] Step 11: `LowGateEval.lean` created (2 namespaces); build green; axioms unchanged.
- [ ] Step 12: old `GateSemanticsLemmas.lean` empty of declarations, deleted; 20 importers repointed to specific files; build green; axioms unchanged.
- [ ] Step 13: 6 suspected stale imports tested; outcomes recorded.
- [ ] Step 14: `Shared/README.md`, `check_shared_layers.sh`, `Shor/Proofs/README.md`, root `README.md` updated; Framework docstring handled after asking.
- [ ] Step 15: audit clean.
