# Plan: a faithful symbolic IR for every admissible table

Status as of 2026-09-30. Tiers 1, 2, 4 and 5 are done; Tier 3's spike ran
and failed, with the result recorded in §7. §6 records a sweep over
generated admissible tables at `k = 2..6` and the one bug it found.

Each item below carries its outcome and the measurement that backs it.

**Goal.** For any `Shor.ShorLoweringSetup`, be able to say with stated,
evidence-backed confidence that instantiating the extracted `Doc` at a
concrete width reproduces the real `LowGate` circuit, and know exactly
where that confidence stops.

## 1. What was wrong

### 1.1 The confirmed bug: top-chunk child capacity — **fixed (T1.1)**

`translateAnnotatedOps` (`Reflect/Extract.lean`, the `.phaseProduct` arm)
passed the recursive `phase_product`/`cphase_product` call the child's
capacity as

    xCap := reserveNeed_x(nextWidth, nextWidth)
    zCap := reserveNeed_z(nextWidth, nextWidth)

for *every* chunk `i`. The real reserve split is
`ReserveBudget.ofRequirements` / `fillSlack`
(`Implementation/PhaseProduct/Compiler/Workspace.lean`): each child gets
`requiredChildReserve i`, and the **top chunk `k-1` additionally receives all
slack** `capacity - Σ required`. After the child is grown to `nextWidth`,
its remaining capacity is therefore

    chunk i < k-1 :  reserveNeed(nextWidth, nextWidth)              (as emitted)
    chunk k-1     :  reserveNeed(nextWidth, nextWidth) + (cap - Σ required)

The emitted value was right for chunks `0..k-2` and for the top chunk
whenever there is no slack. The register expression passed to the call was
*correct* (`precomputePhaseProductSlots` in `Reflect/Targets.lean` already
replicates `fillSlack`); only the capacity *parameter* was wrong, so the
callee's own split of its reserve among grandchildren was computed from too
small a capacity, and every grandchild-level gate that prints a reserve
list differed.

Three conditions must coincide for it to be visible: a `phaseProduct`
checkpoint on register `k-1`, slack in the parent's reserve, and a table
whose width policy makes the child non-base at the sampled width. At
`k = 2`, "register `k-1`" is register 1, which is how the Submission docs
came to describe it as a register-0 rule.

Measurements, re-run against the tree with and without T1.1 (the two tables
are now `Tests.lean`'s `T1_1_TopChunkReserve` section, so this is
reproducible from the suite rather than from a scratch file):

| table | width | slack | before T1.1 | after |
|---|---|---|---|---|
| checkpoints on reg 1, points `0,-1,1` | 8, 16 | 1 | agree | agree |
| same | 32 | 0 | agree | agree |
| same | 32 | 1 | **disagree** | agree |
| points `0,-1,frac 0`, `frac 0` checkpoint on reg 1 | 8 | 1 | agree | agree |
| same | 16 | 0 | agree | agree |
| same | 16 | 1 | **disagree** | agree |
| same | 16 | 84 | **disagree** | agree |

The last row is the one that identified the cause: the IR acted on exactly
the same physical qubits as the real circuit and differed only in how much
*unused* reserve a top-chunk descendant carried — semantically faithful,
syntactically wrong, and the check compares syntax.

### 1.2 Why the evaluation tier did not see more — **addressed (T2.1–T2.6)**

- `submissionPPWidths = [8, 16]`, fixed. Now `ppWidthLadder setup.ops`,
  derived from the table's own `nextWidth` chain.
- `ppRegisters` gave exactly one qubit of slack, always. Now a parameter,
  and both regimes are checked.
- `submissionQFTWidths = [4, 8]`: both even, both with base-case phase
  products. Now `qftWidthLadder setup.ops`, which adds an odd width and an
  odd width that reaches a recursive phase product.
- `canaryInst = (a = 2, N = 15, m = 0)` alone. `shor_gate` now also runs at
  `(a = 2, N = 143), m = 1`.
- The CLI canary `verifyDoc` checked `phase_product` at `4k = 8`, the base
  case at `k = 2`. It now uses the same lists as `submissionChecks`.
- `Tests.lean`'s custom table (R2.7) keeps every checkpoint on register 0.
  The two §1.1 tables are now in the suite alongside it.

A correction to the original note: it said "at `k = 2` the child at 16
recurses at most once, so grandchildren never exist". Measured, the
submission table's chain from 16 is two levels deep and the standard
table's is three (`chain 16 = [13, 12, 11]`). Grandchildren did exist; what
kept the bug invisible is that every checkpoint in those tables sits on
register 0, so no recursing child was ever the top chunk.

### 1.3 The structural reason — **unchanged**

The table-dependent parts of the IR are precisely the parts that are
hand-mirrored rather than reflected (the annotated-ops walk, the slot and
reserve bookkeeping, the loop templates). Reflection covers the recursion
skeleton and the arithmetic; the bookkeeping around it is authored. A hand
mirror is only as complete as the cases its author had in mind, and the
sampled-width comparison is the only detector. Tier 2 widened the detector;
Tier 3 was to shrink the surface, and did not.

## 2. Work items and outcomes

### Tier 1 — the bug

**T1.1 Fix the top-chunk capacity. — done.** `translateAnnotatedOpsGo`
builds `xCap`/`zCap` per chunk, adding `capacity - Σ required` for
`i = k - 1`. The slack term reaches it through two new fields:
`SideSlots.topSlack` (set by `precomputePhaseProductSlots`, which already
computed `usedW`) and `Registry.topChunkSlack`. The chunk index is a
literal at extraction time, so the choice is made in `MetaM`, never in
the IR. Applies to both the plain and controlled call.

Exit, all met: the `frac 0` table agrees at `n = 16` with slack 84; the
reg-1 table agrees at `n = 32` with slack 1; `lake build EmitTests` and
`lake build Submission` pass.

### Tier 2 — widen the evaluation tier

**T2.1 Per-table widths, three levels deep. — done.** `ppWidthLadder ops`
returns the largest base-case width plus the smallest width reaching one,
two and three levels, searched below `widthSearchBound = 1024` via
`ppRecursionDepth`. Submission table: `[13, 14, 15, 17]`, depths
`[0, 1, 2, 3]`. Standard `k = 2`: `[11, 12, 13, 15]`.

Exit: `evaluationChecks` on the `frac 0` table fails before T1.1 and passes
after (pinned as `Tests.lean`'s `T1_1_TopChunkReserve`).

Runtime, measured on this machine:

| build | before | after |
|---|---|---|
| `lake build Submission` (`Check.lean`) | 30 s | **52 s** |
| `lake build EmitTests` (`Tests.lean`) | 247 s | **591 s** |
| `lake exe forshor_emit template 2` | ~5 s | **28 s** |

Per-check costs for the submission table (`k = 2`), each slack regime
separately: `pp`/`cpp` at `n = 13` 0.03 s, `n = 14` 0.19 s, `n = 15` 0.9 s,
`n = 17` 3.3 s; `qft` at `w = 4, 8, 9` under 5 ms, at `w = 29` 3.3 s;
`shor_gate` 0.04–0.07 s; `shor` 0.5 s; the leaf checks under 1 ms.

**The cost does not stay flat in `k`, and this is the open risk.** The
ladder is derived from the table, and the standard table recurses much
later at larger `k`: `k = 3` gives `pp = [26, 27, 29, 35]` and
`qft = [4, 8, 9, 55]`, and one `checkPhaseProductAt` at `n = 35` takes
**400 s** (`n = 29`: 71 s, `n = 27`: 10 s, `qft w = 55`: 73 s). With two
slack regimes and the controlled variant, a `k = 3` submission's acceptance
build is roughly **35 minutes**. At `k = 4` the ladder reaches `n = 87` and
`qft w = 153`, which is not a build anyone will wait for.

Nothing here caps it, deliberately — T2.1 asks for three levels for every
`k` and that is what is implemented — but a cap (or a per-`k` ladder depth)
is the obvious next decision, and it is the owner's to make. The symptom a
submitter would see first is `template`/`bundle` refusing until `--w-max` is
raised past `templateCheckWidth`, which is now derived from the same
ladders (153 at `k = 4`, 521 at `k = 6`, against a default of 64).

**T2.2 Both slack regimes. — done.** `ppRegisters ops n slack` (default 1,
the historical value). `submissionPPSlacks = [0, 64]`, and every
phase-product width runs in both.

**T2.3 QFT depth and parity. — done.** `qftWidthLadder ops` is
`[4, 8, 9] ++ [smallest odd w whose embedded phase product recurses]`.
Submission table: `[4, 8, 9, 29]`. `9` is odd; `29` is odd *and* reaches a
recursive phase product, so one width covers both halves of the criterion.

**T2.4 A second Shor instance. — done.** `largeInst = (a = 2, N = 143)` —
eight bits — at `m = 1`, for both `shor_gate` *and* the fully lowered
`shor`. This initially had to stop at the `Gate` level: `checkShorAt
largeInst 1` did not finish, because the circuit comparison recursed once
per gate. That turned out to be a bug in the comparison rather than a cost
ceiling (§6), and with it fixed both run. The Hadamard loop, the exponent
loop and the `m`-dependent widths are checked at eight bits at both
levels.

**T2.5 CLI canary uses the submission widths. — done.** `verifyDoc`
iterates the same four lists `submissionChecks` uses. `forshor_emit
template 2` now exercises widths `[11, 12, 13, 15]`, i.e. the recursive
case, and exits 0 in 28 s.

**T2.6 Regression anchors in `EmitTests`. — done.** `Tests.lean`'s
`T1_1_TopChunkReserve` section: both §1.1 tables as `extract_ir_doc` +
`native_decide`, at the width/slack pairs that failed. The suite fails on a
checkout without T1.1.

### Tier 3 — shrink the hand-mirrored surface

**T3.1 Spike: controlled reduction for the leaf case. — ran, failed.** See
§6 for the stuck term. `translateAnnotatedOps` stays.

**T3.2 Derive the reserve split instead of restating it. — not attempted**
(conditional on T3.1).

**T3.3 Make the source reflection-friendly. — not attempted.** §6 is the
evidence for it, and it touches the verified core; it needs the owner's
agreement first.

**T3.4 Coverage rule for hand-stated templates. — done.** Added
`checkNaiveLeafAt`/`checkNaiveCLeafAt` to `evaluationChecks` at
`submissionLeafWidths = [(13, 7), (7, 13), (6, 5)]` — unequal, both orders,
past the 1..6 pairs R2.3/R2.4 used. The coverage table (which hand-stated
construct is covered by which check) is in
[`README.md`](README.md)'s "What is hand-stated" section, where a reader
meets it rather than having to find this file.

### Tier 4 — the consumer contract

**T4.1 Off-diagonal widths. — done.** `Symbolic/Width.lean` gains
`splitWidthTable` — `nextWidth`/`reserveNeed` at `(w / 2, w - w / 2)`, the
unequal pair `qft` hands `phase_product` — published as the bundle's
`split_width` section, and `tableOpaqueW`, the `Env.opaqueW` oracle built
from the published rows by lookup alone.

Exit: `Tests.lean`'s `T4_1_TableOracle` instantiates the extracted `qft` at
`w = 8, 9, 13, 25` through `tableOpaqueW` and agrees with the real circuit,
with a companion check that a width past the published range returns `none`
rather than a guess.

**T4.2 Write the IR semantics down. — done.** [`IR/README.md`](IR/README.md):
every `WExpr`/`AExpr`/`RegExpr`/`Prop'`/`Node` constructor and every
`opaqueFns` entry, each naming the Lean definition it comes from, plus the
three things a consumer gets wrong by guessing (truncated `ℕ` subtraction,
`call` not inheriting the caller's environment, right-nested folds).

**T4.3 Conformance fixtures. — done, then removed 2026-10-05.** `fixtures/`
held six flat `forshor.lowgate/v2` circuits (`pp`/`cpp` at `n = 8, 12`, `qft`
at `w = 8, 9`) for an external reader to diff against. Nothing regenerated or
diffed them, so they were committed output guaranteed by nothing. Deleted; the
six regenerating commands and the register-layout and environment tables now
live in [`IR/README.md`](IR/README.md), where a consumer reaching the format
spec finds them.

**T4.4 Drop `pp_body` from the shipped `Doc`. — done.** `buildDoc` takes
`includePPBody := false`; `entry` is `phase_product`. `Tests.lean`'s R2.1
uses the new `extract_ir_doc_with_pp_body` command and still passes.

### Tier 5 — documentation

**T5.1 — done.** `README.md`: the "nothing about a template's shape is
written by hand" claim replaced, and a "What is hand-stated" section added
with the coverage table T3.4 asks for.

**T5.2 — done.** `Submission/README.md` and `Submission/Template.lean`: the
register-0 rule and the `frac`-points caveat removed, replaced by what was
actually wrong and where the anchors are.

**T5.3 — done.** `submissionPPWidths`'s docstring rewritten around the
ladder; the two "observed" measurements now say which was a real extractor
bug and which was a genuine table difference.

## 3. What each tier buys

| after | claim |
|---|---|
| T1 | no known disagreement for any admissible table |
| T1 + T2 | for the submitter's own table: agreement at widths spanning three recursion levels, both slack regimes, a deep and an odd QFT, two Shor instances at the `Gate` level — every failure in §1 would have been caught |
| + T3 | *not reached*: the table-dependent bookkeeping is still authored |
| + T4 | an external consumer can reproduce the Lean-side instantiation and check itself against it |

None of this is a theorem. A statement about every width for every table
needs either the archived per-document proof route (R6, `emit-proofs-archive`)
or a compiler polymorphic in its width type. This plan does not attempt
either.

## 4. What is left

1. **The `k ≥ 3` cost cliff** (T2.1's measurement above). A decision, not a
   bug: cap the ladder, make its depth a function of `k`, or accept the
   build time. Nothing else in this plan depends on the answer.
2. **T3.3**, if the owner wants the hand-mirrored surface shrunk — §6 says
   exactly what blocks the reflective route and what change would unblock
   it.
3. **T3.2**, which only becomes available after T3.3.
4. Recursive-arm coverage at `k ≥ 4`. §6's table shows why it is not
   sampled today: the guard first fires at `n = 56` (`k = 4`), `107`
   (`k = 5`), `208` (`k = 6`), and a single `k = 3` check at `n = 35`
   already costs 400 s. Reaching it needs a cheaper comparison than
   building both circuits in full, or a table whose width policy recurses
   sooner.

## 5. Reproduction recipe

Both §1.1 tables live in `Tests.lean`'s `T1_1_TopChunkReserve` section, so
reproducing the bug is: revert T1.1 in `Reflect/Extract.lean` and
`Reflect/Targets.lean`, then `lake build EmitTests`.

For a scratch run, a file importing `Emit.Reflect.Driver`,
`Emit.Reflect.Verify`, `Emit.Lower.Decide`, `Submission.Decide`, run with
`lake env lean` from the repo root:

```lean
def ptsF : List Point := [Point.int 0, Point.int (-1), Point.frac 0]
def opsF : Prog 2 :=
  [ valid_ops.phaseProduct 0
  , valid_ops.negate 1
  , valid_ops.addScaled 0 1 false 0
  , valid_ops.phaseProduct 0
  , valid_ops.negate 1
  , valid_ops.addScaled 0 1 false 0
  , valid_ops.phaseProduct 1 ]
def setupF : ShorLoweringSetup :=
  { k := 2, hk := by decide, pts := ptsF, hpts := rfl
    good := goodToomCookPoints_of_distinct rfl (by native_decide)
    ops := opsF, consumes := by native_decide, returns := by native_decide }
set_option maxHeartbeats 4000000 in
extract_ir_doc docF setupF
#eval! Reflect.checkPhaseProductAt setupF 16 docF 1   -- disagreed before T1.1
#eval! Reflect.checkPhaseProductAt setupF 16 docF 0   -- agreed either way
```

The third argument is the slack (`ppRegisters`' new parameter); varying it
between `0` and anything positive is what flips the result.

## 6. The table sweep, and the bug it found

After the tiers above, the IR was swept against generated *admissible*
tables — C1-C4 proved by `decide`/`native_decide` per table, not assumed —
at `k = 2, 3, 4, 5, 6`. Each table is checked at many widths, reserve
regimes and width pairs; the counts below are tables, not checks.

### How the tables were generated

Three semantics-preserving transforms of the standard generator
(`genOpsWithProduct`), applied to eight point sets per `k`:

* **Relocate a checkpoint.** `swapRows a b` is four legal ops
  (`addScaled`×3 + `negate`, never `dst = src`) and an involution, so
  wrapping `phaseProduct d` as `swap d r ;; phaseProduct r ;; swap d r`
  leaves the row the checkpoint sees, and the final state, untouched. That
  puts a checkpoint on *any* register — the condition §1.1's bug needed —
  for any `k` and any point list.
* **Widen.** `shiftL i m ;; shiftR i m` is the identity (the right shift is
  exact because the left shift just zeroed the low `m` bits) but moves
  `scanNeededWidths`, and so the whole `nextWidth` chain.
* **Inert pairs.** `negate i ;; negate i`, `addScaled d s false m ;;
  addScaled d s true m`.

Point sets per `k`: the canonical list, rotated, reversed, with `frac 0`
(the point at infinity) first/middle/last, with `frac 3` and `frac (-3)`.
`frac 0`'s fragment is `[phaseProduct (finLast)]`, so any table containing
it puts a checkpoint on register `k - 1` for free.

### What was checked

Per table: `Doc.wellFormed`; `phase_product`/`cphase_product` at every width
`1..16` plus the first two widths at which the recursion fires, in three
reserve regimes (`slack = 0, 1, 7`); `qft` at `w = 1..12`; both leaf
templates at five `(xw, zw)` shapes; `shor_gate` and `shor` at the small
reference instance. A second pass checked every **unequal** width pair with
both sides in `2..14` — the shape `ppRegisters` never produces and the
Lean-side ladder never samples, where `phaseLimbWidth = min (xw / k)
(zw / k)` makes the two sides' top chunks differ in width.

### The bug: the comparison aborted instead of answering

One batch of sixteen `k = 2` tables produced no verdicts at all. Not a
failure — a `SIGABRT`:

    libc++abi: terminating due to uncaught exception of type lean::throwable:
    deep recursion was detected at 'interpreter'
    …
    #8608 List.beq._at_.Shor.Reflect.phaseProductAgrees.spec_0
    #8609 Shor.Reflect.checkShorAt

`Reflect/Verify.lean` compared circuits with `flattenLowGate a ==
flattenLowGate b`. `flattenLowGate` leaves each `.adj` element holding its
whole re-folded body, so the derived `BEq LowGate` walks that subtree **one
stack frame per nested gate** — about 8 600 frames was the ceiling, i.e. a
few thousand gates.

This is the comparison `Submission/Check.lean` runs. Confirmed directly, by
restoring the old comparison and building: `lake build Submission` exits
**134** inside `Submission._example._nativeDecide_1`. A submitted table
whose circuit is merely *large* would have killed the acceptance build with
a C++ abort instead of passing or failing it — and `native_decide`'s
compiled path is no safer than the interpreter here.

**Fix.** `lowGateAgrees`/`gateAgrees` compare a flat stream of **leaf**
tokens with adjoint boundaries marked, built with an explicit work stack.
Every branch is a tail call and `BEq LowGate` only ever sees a leaf. The
induced relation is the one `flattenLowGate`'s comparison had — equal up to
`;;` associativity and `.id` — so no check got weaker.

Measured: the reference Shor circuit at `a = 2, N = 143, m = 1` is 247 428
leaf tokens. It aborted the process before; it now compares in 1.5 s, and
agrees.

**It also closes T2.4's deviation.** The fully lowered `shor` at `largeInst`
was dropped from `submissionShorInstances` for exactly this reason. It is
back, and green. `lake build Submission` went 52 s → 67 s.

Anchored by `Tests.lean`'s `StackSafeComparison` section: the shape that
broke (one adjoint over a 20 000-gate chain, and the same against a 19 999
one, so the comparison still discriminates) and the size that broke (the
flat Shor circuit at the eight-bit instance).

### What the sweep says about the IR itself

Every table that produced a verdict agreed with the real circuit, at every
width, slack regime and width pair checked. **No disagreement was found.**

| k | tables verified | shapes covered |
|---|---|---|
| 2 | 60 | all 8 point sets × 6 transforms, plus asymmetric width pairs and the recursive arm at `[8,10]` and `[20,22]` |
| 3 | 33 | the same 6 transforms over 8 point sets, plus the recursive arm at `[21,23]` with unequal widths |
| 4 | 1 (canonical, 63 ops) | base case, widths 1–8 |
| 5 | 1 (canonical, 101 ops) | base case, widths 1–8 |
| 6 | 1 (canonical, 227 ops) | base case, widths 1–8 — 60 min of checks |

96 tables, **0 failures**. The deep pass below adds further checks at the
recursive end, also with 0 failures.

A second, slower pass drove the recursion as deep as the circuit sizes
allow. The table is the shortest admissible one at each `k` — canonical
points with `frac 0` last, whose fragment is the single op `phaseProduct
(finLast)`, so its last checkpoint sits on the **top chunk** with no
relocation at all: exactly §1.1's shape.

| table | n / w | depth | circuit | pp / cpp |
|---|---|---|---|---|
| `k = 2`, 5 ops, checkpoint on reg 1 | 20 | 4 | | ok at slack 0, 1 **and** 64 |
| | 24, 28, 32 | 5 | | ok |
| | 40 | **6** | | ok, 54 s per comparison |
| | qft 33, 49, 65 | | | ok |
| `k = 2`, 21 ops, **every** checkpoint relocated to reg 1 | 24, 32 | 1 | | ok at slack 0 and 1 |
| | 40 | 4 | | ok, 140 s per comparison |
| | qft 41 | | | ok |
| `k = 3`, 17 ops, checkpoint on reg 2 | 21 | 1 | 10 036 tokens | ok at slack 0 and 3 |
| | 23 | 2 | 50 216 tokens | ok at slack 0 and 3 |
| | 27 | | 50 216 tokens | ok |
| | 29, 35 | | **251 116 tokens** | ok, 215–265 s per comparison |
| `k = 4`, 47 ops, checkpoint on reg 3 | **56** | **1** | 105 971 tokens | **ok** — the first time `k = 4`'s recursive arm has been checked. `pp` 464 s, `cpp` **25.5 min** |

At `k = 3` the circuit grows 10 036 → 50 216 → 251 116 tokens over
`n = 21 → 23 → 29`, and `n = 35` converges back to 251 116 — the width chain
bottoms out. Each comparison there costs 215–265 s.

A projection worth not repeating: from that curve the `k = 4` recursive arm
at `n = 56` looked like tens of millions of gates. Measured, it is **105 971
tokens** — the expensive part at larger `k` is *constructing* the circuit
(480 s to build and tokenize one side), not its size. So the cost barrier at
`k ≥ 4` is real but smaller than the gate-count extrapolation suggests, and
the recursive arm there is reachable with patience rather than out of
reach.

The asymmetry in the counts above is the cost curve, not a choice: see the
recursion thresholds below. At `k = 2` a single table is checked at 16
widths × 3 reserve regimes × 2 (plain and controlled), plus 12 QFT widths,
5 leaf shapes and both Shor targets — so "60 tables" is several thousand
circuit comparisons.

One honest limit on that coverage. The recursion guard is `nextWidth ops
n n < n`, and where it first fires depends on how much width the op list
needs — so on the table, not only on `k`. For the canonical table at each
`k`, and for the shortest *generated* table at that `k` (canonical points
with `frac 0` last, whose fragment is a single op):

| k | canonical: first rec | shortest generated: first rec | depth reached by `n = 16` |
|---|---|---|---|
| 2 | 12 | **8** (5 ops) | **4** |
| 3 | 21 (17-op variant) | 21 | 0 |
| 4 | 77 | 56 | 0 |
| 5 | 117 | 107 | 0 |
| 6 | 261 | 208 | 0 |

and no width *pair* below 30 recurses at `k ≥ 4` either — so the *cheap*
pass, which samples widths `1..16`, reaches the recursive arm only at
`k = 2` and `k = 3`. At `k = 2` it reaches **six** levels, on exactly the
shape §1.1's bug needed: `frac 0` puts the last checkpoint on register
`k - 1` with no relocation at all.

The deep pass then went after `k = 4` directly, at its own first recursive
width, and **reached it**: both `pp` and `cpp` agree at `n = 56` (464 s and
25.5 min respectively — the controlled circuit is the expensive one). So the
recursive arm is covered at `k = 2`, `3` and `4`. What remains uncovered is
the recursive arm at `k = 5` (`n = 107`) and `k = 6` (`n = 208`), which is a
property of the compiler's width policy rather than of the sweep: those
tables simply do not recurse below those widths, and a single comparison
there costs hours of circuit construction.

## 7. T3.1's result: why the reflective route is still blocked

The spike asked whether `planCompileAnnotatedOpsToSignedGateAux`'s match
can be exposed by iota alone, with `nextWidth`/`reserveNeed`/`fillSlack`/
`ofRequirements`/`LayoutState.*` blocked from unfolding. The recorded R2.2
failure attributed the cascade to type-checking the exposed match against
its dependent motive.

**That attribution is wrong, and the match is not the problem.** Rebuilding
the application exactly as `planCompiledSignedPhaseGate` builds it — real
`st`, `x`/`z` free — a plain default-transparency `whnf` exposes
`PhaseLoweringPlan.seq <leaf> <aux … rest>` in **about one millisecond**.
No `withCanUnfoldPred` predicate is needed; nothing cascades. Driving the
whole chain that way is cheap.

What is unaffordable is the `.phaseProduct` **leaf**. It arrives as

    id (Eq.rec (motive := fun x h => x)
               (minor  := Shor.standardSignedPhaseLoweringPlan …)
               (major  := Shor.standardSignedPhaseLoweringPlan._proof_4 …))

and reducing the `id`-wrapped cast far enough to see that head costs
**48 s for the first leaf**; `whnf` on the resulting `Eq.rec` then exhausts
2 000 000 heartbeats. The major premise's type is

    StandardPhaseLoweringPlan 2 … (phaseInputSize (dst.xslot 0) (dst.zslot 0))

— the index is `phaseInputSize` of the **child slots**, so evaluating it is
exactly the `LayoutState`/`canonicalSignedStep`/`ReserveBudget` reduction
the extractor exists to avoid. The cast is `planCompiledSignedPhaseGate`'s
`recurse' := by simpa [src, dst, need] using recurse`, together with the
`hsize` rewrite in `standardSignedPhaseLoweringPlan`'s own step branch.

`translateAnnotatedOps` never touches `recurse`: it synthesises the
recursive `Node.call` from the chunk index directly, which is precisely why
it is affordable and precisely why it has to restate the capacity formula
by hand.

One thing the spike did establish as reusable: registering
`ExtReg.capacity` for each grown child slot in `precomputePhaseProductSlots`
(the same formula T1.1 now threads through `Registry.topChunkSlack`) is
enough for `translatePlan` to read a recursive call's capacity arguments off
the registry rather than reducing them. That removes one of the two
obstacles. The remaining one is the `Eq.rec` above, and T3.3 — giving
`planCompileAnnotatedOpsToSignedGateAux` the slot registers as an explicit
`Fin k → ExtReg` argument, so the motive is non-dependent and no `simpa`
cast is needed — is the change that would remove it.
