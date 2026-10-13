# A gate-count bound for a policy

Follow-up plan 2 of the two §9 of [`PLAN_Policy.md`](PLAN_Policy.md) hands
on. That plan carried the *correctness* of a policy-lowered circuit all the
way to `policy_submission_correct`; the asymptotic gate-count theorems were
left stated for a single table, which `PLAN_Policy.md` item 6 made precise by
spelling them at `constPolicy`.

The goal: `shorGateCountBound_of_policy`, the policy analogue of
`shorGateCountBound_of_setup`.

Paths are relative to `FastMultiplication/ShorVerification/`.
`GC/` abbreviates `Implementation/GateCount/`.

---

## 0. What the survey established

### 0.1 The recurrence machinery is already in the right shape

`GC/PhaseProduct/Main.lean:22` assembles
`phaseProductGateCountBound_of_programOK` from four ingredients, and the
third is the one that matters here:

```lean
obtain ⟨C, hC, hbalanced⟩ := balanced_phaseProduct_recurrence_solution …
```

Inside that lemma (`GC/PhaseProduct/Lemmas.lean:2897`) the recursion is
solved from exactly two facts:

```lean
hbounded : ∀ N, ∃ D, ∀ i, size i ≤ N → cost i ≤ D
hstep    : ∀ i, next i < size i → ∀ D, (∀ j, size j = next i → cost j ≤ D) →
             cost i ≤ (A + 4 * k) * next i + B + q k * D
```

`hbounded` is **"below any width bound the cost is bounded by a constant"** —
which is precisely the fact a policy needs below its top threshold, and it
already exists as a standalone lemma,
`signedPhaseProductGateCount_bounded_on_bounded_inputs`
(`Lemmas.lean:2616`), proved by **induction on `N`** and nothing else.

That is the central finding of this survey: the policy proof is not a new
argument. It is the same recurrence with `hbounded` instantiated at
`N := t₀ - 1` and `hstep` restricted to widths `≥ t₀`, where `P.choose`
returns the top table and the step is the top table's step.

### 0.2 The instance type is balanced, and a policy stays balanced

`BalancedPhaseProductInstance` (`GC/Definitions.lean:214`) carries
`hwidth : ExtReg.width x = ExtReg.width z`. The recursion preserves it —
both children grow to `nextWidth`, so once the chain starts it is symmetric,
the same fact `Emit/Symbolic/Width.lean` relies on for its diagonal
`widthTable`. A policy does not change this: `choose` is keyed on
`max wx wz`, which on the diagonal is just the common width. So the
band boundaries are thresholds on `size i` directly, with no asymmetric case
to handle inside the phase-product recurrence.

(`qft`'s call at `(v/2, v - v/2)` *is* asymmetric, but that is one level
outside this recurrence and is already handled where the QFT bound consumes
the phase-product bound.)

### 0.3 The bound predicates already name the policy

`PLAN_Policy.md` item 6 rewrote all four predicates' bodies to
`constPolicy ⟨k, hk, pts, hpts, ops⟩` while keeping their *statements* keyed
on `(k, hk, ops, pts, hpts)` — see `GC/Definitions.lean:88, :260, :286` and
`GC/Shor_GateCount.lean:99`. So a policy predicate is a new definition
alongside them, not a rewrite of them, and the existing published statements
(`exists_shorGateCountBound`, `shorGateCountBound_of_setup`, …) do not move.

### 0.4 `ShorLoweringPolicy` has no `topTable`

`Framework/Policy.lean` has `bands`, `sorted`, `choose`, `Admissible`,
`Stops`, `constPolicy`. There is no accessor for the widest band and no
lemma that `choose n = some P.topTable` for `n ≥ t₀`. Both are new, both are
small, and both belong in `Framework/Policy.lean` — the one file a
submissions repo reads to understand the specification.

The empty policy is the edge case: `bands = []` is admissible (and
quadratic), so `topTable` is an `Option`, or the theorem takes
`P.bands ≠ []` as a hypothesis. Prefer the hypothesis: an all-leaf policy
has no exponent to quote, and `phaseProductExponent` of nothing is not a
number anyone wants to define.

### 0.5 `canonicalSignedStep` is now dead code

`PLAN_Policy.md` §8 deferred deleting it, on the grounds that the GateCount
callers at `Lemmas.lean:2230, :4588` would need porting and `Workspace.lean`
has 19 importers. **Those callers are already ported** — `Lemmas.lean:2196`
and `:4496` now read `Policy.canonicalStep P₀ T₀ x z (constPolicy_choose T₀ _) hrec`,
and a search of the tree finds no remaining use:
`canonicalSignedStep` appears only at its own definition
(`P/Compiler/Workspace.lean:607`) and in docstrings.

So the deletion is now a *pure* deletion with no callers to port. It still
costs the `Workspace.lean` cascade, which is why it belongs in this plan —
item 5 below folds it into a commit that is rebuilding that file anyway.

---

## 1. Discipline

As `PLAN_Policy.md` §1. The file that matters here is
`GC/PhaseProduct/Lemmas.lean` (4 918 lines): new lemmas go at the end, and
the existing recurrence lemmas are **not** restated — item 2 generalises
them by adding hypotheses, never by changing conclusions.

Each item is one commit, green on all four lake targets.

---

## 2. The policy recurrence — `GC/PhaseProduct/PolicyLemmas.lean` (new)

### 2a. The bounded-inputs lemma, for a policy

```lean
lemma policyPhaseProductGateCount_bounded_on_bounded_inputs
    (P : ShorLoweringPolicy) (hP : P.Admissible) (N : ℕ) :
    ∃ D : ℕ, ∀ φ x z (hws : Policy.WorkspaceOK P x z),
      phaseInputSize x z ≤ N →
      policySignedPhaseProductGateCount P φ x z hws ≤ D
```

Induction on `N`, mirroring `Lemmas.lean:2616` line for line. The induction
step splits on `P.choose (max wx wz)`:

- `none` — the leaf, cost is the naive leaf's count at this width, already
  bounded;
- `some T`, shrink test fails — also the leaf;
- `some T`, shrink test holds — one level of `T`'s step plus `T.k` children
  at `nextWidth T.ops wx wz < max wx wz ≤ N`, so the induction hypothesis
  applies.

Note this is where `hP` is *not* needed: the gate count does not care whether
a table is admissible, only what it is. Take it anyway if the statement reads
better, but do not let its absence be mistaken for an oversight.

### 2b. The recurrence above the top threshold

```lean
lemma policy_balanced_recurrence_solution
    (P : ShorLoweringPolicy) (T₀ : ToomCookTable) (t₀ : ℕ)
    (htop : P.bands.head? = some ⟨t₀, T₀⟩)
    (hcount : phaseProductCount T₀.ops = q T₀.k)
    (hwidth …) (hoverhead …) :
    ∃ C, 0 < C ∧ PolicyBalancedBound P T₀ C
```

Proved by handing `balanced_phaseProduct_recurrence_solution`'s own argument
the two facts of §0.1, with:

- `hbounded` := 2a at `N := t₀ - 1`, giving a **single constant** `D₀` for
  the entire sub-threshold region — this is the step that makes the bands
  below the top disappear into a constant;
- `hstep` := the existing step lemma, applicable because for `size i ≥ t₀`
  we have `P.choose (size i) = some T₀` (item 3's lemma), so the level is
  literally `T₀`'s level.

The honest framing for the resulting bound: **a policy's exponent is its
top table's exponent.** The lower bands change the constant, not the
exponent. That is not a weakness of the proof — it is true, and it is
exactly why the score is a gate count at a fixed size rather than an
exponent, which is the motivating sentence of `PLAN_Policy.md`.

---

## 3. `topTable` and the threshold lemma — `Framework/Policy.lean`

```lean
def topBand (P : ShorLoweringPolicy) : Option PolicyBand := P.bands.head?

theorem choose_eq_top (P : ShorLoweringPolicy) {t₀ T₀} 
    (h : P.bands.head? = some ⟨t₀, T₀⟩) {n : ℕ} (hn : t₀ ≤ n) :
    P.choose n = some T₀
```

`choose` is `bands.find? (fun b => decide (b.threshold ≤ n))`, so the first
band matching is the head whenever the head matches, and `hn` is exactly
that. One `simp [choose, List.find?, h, hn]`.

This file is `Framework/`, imported by `Submission/` and by everything —
keep the addition to these two declarations and their docstrings. The
docstring should say what §2b's framing says: the top band is what sets the
exponent.

---

## 4. The public statement — `GC/Shor_GateCount.lean`

```lean
def ShorGateCountBoundPolicy (qs : QSemantics) [RegEncoding qs.Basis]
    (ε : ℝ) (P : ShorLoweringPolicy) : Prop := …

theorem shorGateCountBound_of_policy (qs : QSemantics) [RegEncoding qs.Basis]
    (s : ShorPolicySubmission) (ε : ℝ) {t₀ T₀}
    (htop : s.policy.bands.head? = some ⟨t₀, T₀⟩)
    (hExponent : phaseProductExponent T₀.k ≤ 1 + ε) :
    ShorGateCountBoundPolicy qs ε s.policy
```

keyed on `ShorPolicySubmission` for the same reason
`shorGateCountBound_of_setup` is keyed on `ShorLoweringSetup`: the side
conditions come for free from the record, so a submitter supplies only
`hExponent`.

**`shorGateCountBound_of_setup` must come out as the one-band corollary**,
and its statement must not change — it is published in the top-level
`README.md`. `ShorPolicySubmission.ofSetup` gives `bands = [(0, s)]`, so
`htop` is `rfl` and `T₀.k = s.k`. Verify with a `#check` diff against `HEAD`,
as `PLAN_Policy.md` §5.2 did for `submission_correct`.

`exists_shorGateCountBound` stays existential in `k` and is untouched:
reaching every `ε > 0` still means letting the top table's arity grow, and a
policy does not change that.

---

## 5. Delete `canonicalSignedStep` — `P/Compiler/Workspace.lean`

A pure deletion (§0.5): no callers, docstrings only. Fold it into whichever
item above first rebuilds `Workspace.lean`, since the cascade is paid there
anyway; do not spend a separate commit's rebuild on it.

Then correct the two places that currently explain why it survives —
`P/Compiler/README.md`'s "Why this file is separate, and why
`canonicalSignedStep` survives", and `PolicyWorkspace.lean`'s header table —
and move `PolicyWorkspace.lean`'s contents into `Workspace.lean` in the same
commit if the cascade is already being paid.

The `lowerGate_correctness` duplication (both `Shor.lowerGate_correctness`
and `Shor.Policy.lowerGate_correctness` exist) is a **separate** question and
is *not* resolved here: that one really is blocked on
`Policy.reserveNeed (constPolicy T)` being only propositionally equal to
`RecursivePhaseWorkspace.reserveNeed T.ops`. Leave it, and leave the
`Compiler/README.md` paragraph that explains it.

---

## 6. Risks, in order

1. **`policySignedPhaseProductGateCount` does not exist — it is a
   prerequisite, not part of item 2.** `signedPhaseProductGateCount`
   (`GC/Definitions.lean:156`) is
   `LowGate.gateCount shorGateCostModel (lowerSignedPhaseProdWithWorkspace …)`.
   The policy analogue is the same over `Policy.lowerSignedPhaseProd`
   (`P/Lowering/Lower.lean:53`), which does exist. Define it next to the
   fixed-table one in `GC/Definitions.lean` as item 2's first step; it is two
   declarations (signed and controlled) and no proof.
2. **Well-founded unfolding in 2a's induction step.** `Policy.reserveNeed`
   and the policy planner are two distinct WF fixpoints, and
   `PLAN_Policy.md` item 3 already hit `simp` looping on
   `RecursivePhaseWorkspace.reserveNeed_fst` (it is `@[simp]` and unfolds the
   recurrence forever). Use `rw`/`rwa` with the `_of_choose` projection
   lemmas, never `simpa`; the comment recording this is in
   `PolicyWorkspace.lean` and should be read before starting.
3. **`t₀ - 1` on `ℕ`.** For `t₀ = 0` (the `ofSetup` one-band case) the
   sub-threshold region is empty and `t₀ - 1 = 0` truncates rather than
   erroring — harmless, but the one-band corollary of item 4 goes through
   this path, so check it explicitly rather than assuming.
4. **`hwidth`/`hoverhead` are per-table.** `prog_balanced_nextSignedWidth`
   and `phaseProgramOverhead_linear` are stated for one `ops`. Above `t₀`
   only `T₀.ops` is reached, so only `T₀`'s instances are needed — but the
   *statement* of 2b must say so, or it will look as though a policy needs
   every band's width lemma when it needs one.
5. **Build time of `Lemmas.lean`.** It is 4 918 lines and already the slowest
   file in `GateCount/`. Putting the new lemmas in a *new* file
   (`PolicyLemmas.lean`) rather than appending is what keeps iteration
   survivable; resist consolidating them later for tidiness.

---

## 7. Verification

```bash
lake build FastMultiplication EmitTests Submission PolicySubmission
lake env lean scripts/AxiomCheck.lean
python3 scripts/check_layers.py
python3 scripts/gen_docs_graph.py --check && git diff --exit-code docs/data/graph.js
```

with `scripts/AxiomCheck.lean` gaining `Shor.shorGateCountBound_of_policy`,
and `#check` diffs against `HEAD` showing `exists_shorGateCountBound`,
`shorGateCountBound_of_setup`, `shorGateCountBoundShorEta_of_setup`,
`ShorGateCountBound`, `PhaseProductGateCountBound`,
`CPhaseProductGateCountBound` and `QFTGateCountBound` **unchanged** — the
same seven `PLAN_Policy.md` item 6 pinned.

---

## 8. Relationship to the IR plan

Independent. [`PLAN_PolicyIR.md`](PLAN_PolicyIR.md) makes a policy
submission *scored* — it produces the IR a resource estimator measures, and
the score is that measurement times the trial count, computed outside Lean.
This plan produces an *asymptotic theorem*, which is not the score and never
was (top-level `README.md`: "the single-run gate count … is measured by
Qualtran on the IR, not computed in Lean").

Neither blocks the other, and if only one is done, **the IR plan is the one
that changes what a submitter gets.** This one closes a gap in the stated
theory: today the repository proves an exponent bound for every single-table
submission and none for a policy, which is an asymmetry worth removing but is
not what a submissions repo is waiting on.
