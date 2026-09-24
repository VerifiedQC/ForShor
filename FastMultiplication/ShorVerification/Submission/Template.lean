import FastMultiplication.ShorVerification.Framework.ToomCookTable
import FastMultiplication.ShorVerification.Submission.Decide
import FastMultiplication.ShorVerification.Submission.Correct
import FastMultiplication.ShorVerification.Submission.Score
import FastMultiplication.Emit.Reflect.Driver
import FastMultiplication.Emit.Reflect.Verify
import FastMultiplication.Emit.IR.Json

/-!
# The file a submitter copies

`SUBMISSION_PLAN.md` S4. A submission to this challenge is a Toom-Cook table:
an arithmetic program `ops` over `k` limb registers, plus the interpolation
points `pts` its `phaseProduct` checkpoints evaluate at. Everything else —
the quantum construction, its correctness proof, the precision, the trial
count, the IR the resource estimate is computed from — is fixed by this
repository and is the same for every submission.

So there are exactly **three definitions to edit**, marked below. Change
them, run

```bash
lake build Submission && lake exe forshor_submission > ir.json
```

and if the build is green the submission is admissible. Nothing else in this
file should need touching; in particular every `by native_decide` stays as
it is.

## What the green build means

Two tiers, and it is worth being precise about which is which
(decision P5).

**Kernel-checked.** The four fields of `setup` are the conditions C1-C4 of
`Framework/ToomCookTable.lean`, decided by `Submission/Decide.lean` and
checked by Lean's kernel. Passing them is not evidence about the table, it
*is* the table being admissible — and `Shor.submission_correct` then applies
to it with no further work, giving the same proved success bound every other
submission gets. That theorem is generic in the table; there is no
per-submission correctness proof, which is the entire point of narrowing the
challenge this way.

**Checked by evaluation.** `Shor.Reflect.submissionChecks` compares the
extracted IR against the real compiled circuit at sampled widths (`n = 8, 16`
for the phase products, `w = 4, 8` for the QFT, and the smallest reference
Shor instance). This is evaluation, not a theorem: the IR is not proved
correct at *every* width. That project (R6) concerns the reference table only
and was archived; it is deliberately not a submission requirement. The
extractor is keyed by Lean construct, never by `k` or by a table, which is
why agreement at sampled widths is meaningful evidence rather than a
coincidence.

## The table shipped here

The canonical `k = 2` ladder, with one semantically inert
`shiftL 0 0 ;; shiftR 0 0` pair appended. Shifting by zero is the identity
and never fails, so the pair changes the *list* the extractor walks without
changing what points the program consumes or what state it returns to. It is
therefore a real table, distinct from `Shor.standardLoweringSetup 2`, and a
working example of an edit rather than a copy of the reference.
-/

namespace Submission

open Shor Operations

/-! =========================================================
    EDIT HERE — and nowhere else
========================================================= -/

/-- **Edit me.** The number of limb registers. `k > 1`; `k ≤ 6` is the
supported range (C2 is decided by a determinant over `(2k-1)!` permutations,
which `native_decide` handles instantly through `k = 5` and slowly at
`k = 6`).

An `abbrev`, not a `def`, so that `Fin k` in `ops` below reduces to
`Fin 2` and the register indices can be written as plain numerals. -/
abbrev k : ℕ := 2

/-- **Edit me.** The interpolation points, in the order the `phaseProduct`
checkpoints consume them: leaf `l` receives coefficient `l`. Exactly
`q k = 2k - 1` of them. `Point.frac c` denotes `1/c`, and `Point.frac 0` the
point at infinity.

The order is part of the submission, not a formality: the same points
permuted are a different table, and C3 will reject the mismatch
(`Submission/Decide.lean`'s smoke tests demonstrate exactly that). -/
def pts : List Point :=
  [Point.int 0, Point.int (-1), Point.int 1]

/-- **Edit me.** The table itself. -/
def ops : Prog k :=
  [ valid_ops.phaseProduct 0
  , valid_ops.addScaled 0 1 true 0
  , valid_ops.phaseProduct 0
  , valid_ops.addScaled 0 1 false 0
  , valid_ops.addScaled 0 1 false 0
  , valid_ops.phaseProduct 0
  , valid_ops.addScaled 0 1 true 0
  -- The inert pair described in the module docstring. Delete it, or replace
  -- the whole list, when submitting a table of your own.
  , valid_ops.shiftL 0 0
  , valid_ops.shiftR 0 0
  ]

/-! =========================================================
    Below here: nothing to edit
========================================================= -/

/-- The submission. Each proof field is one of C1-C4; all four are decided,
so `native_decide` closes them for whatever `k`, `pts`, `ops` are written
above. A failure here means the table is not admissible — read it as the
check working, not as the template being broken. -/
def setup : Shor.ShorSubmission where
  k := k
  hk := by decide
  pts := pts
  hpts := by rfl
  good := by native_decide
  ops := ops
  consumes := by native_decide
  returns := by native_decide

/-! `doc` is the IR a resource estimator reads: extracted by reflection from
the reference construction specialised at `setup`, and printed by
`Submission/Main.lean`. -/
set_option maxHeartbeats 4000000 in
extract_ir_doc doc setup

/-- The IR is well-formed: every template's free variables are bound, every
`Node.call` names a template in the document, and so on. -/
example : IR.Doc.wellFormed doc = true := by native_decide

/-! The evaluation tier: `instantiate doc` agrees with the real compiled
circuit at the sampled widths and at the smallest reference Shor instance,
against *this* submission's points. -/
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
example : Shor.Reflect.submissionChecks setup doc = true := by native_decide

/-- The certificate at this submission, as a name the submissions repo can
cite. There is nothing to prove: `Shor.submission_correct` is generic in the
table, so `setup` existing is the whole argument. -/
def correct {qs : QSemantics} [RegEncoding qs.Basis] [MeasureClass qs]
    [GateSemanticsFacts qs] [LowerGateClass qs] [IdealCtrlModMulExactSemantics qs] :=
  Shor.submission_correct (qs := qs) setup

end Submission
