import FastMultiplication.ShorVerification.Framework.ToomCookTable

/-!
# Deciding a submission's four side conditions

`SUBMISSION_PLAN.md` S2.1. A submitter packaging their own table as a
`Shor.ShorSubmission` has to discharge C1-C4 (`Framework/ToomCookTable.lean`)
for concrete `k`, `pts` and `ops`. This file makes all four a matter of
computation, so the template's `by native_decide` just works and the kernel,
not a parser, is what checks a submission.

Like the record it is about, this file is implementation-free: it imports
`Framework/ToomCookTable` and Mathlib, and nothing else. It moved here from
`Emit/Table/Decide.lean` (added by the emitter's R5 round), which had to
import the compiler, the plan builders and the standard setup through
`Emit/Table/Source.lean` even though its own code never used any of them;
S2.0 put everything it does use in `Framework/`.

- **C1** `pts.length = q k` is `Nat` equality: decidable already, `rfl` in
  practice.
- **C4** `run? ops State.start_state = some State.start_state` is decidable
  already, via `DecidableEq (State k)` from `Fintype.decidablePiFintype`
  (`State k = Fin k → Fin k → ℤ`).
- **C3** `ProgConsumesPtsSafe` bundles `ProgConsumesPts` and `SafeProg`,
  neither of which had a `Decidable` instance anywhere in the repo: both are
  stated as `Prop`s whose shape (an existential fixed by the data, and a `∀`
  over list decompositions respectively) hides decidability that only becomes
  visible after unfolding. Both are supplied below.
- **C2** `GoodToomCookPoints` unfolds to `Matrix.det (…) ≠ 0` over `ℚ`, which
  is computable outright, so the instance is a one-line `inferInstanceAs`.
-/

namespace Shor

open Operations

/-- Every non-`phaseProduct` op shares the same shape,
`∃ σ', applyOp? σ op = some σ' ∧ ProgConsumesPts hk σ' ops pts` — this
builds `Decidable` for that shape given the recursive result at whatever
`σ'` `applyOp?` produces. Factored out so `decideProgConsumesPts` below can
call it once per concrete constructor (`shiftL`/`shiftR`/`negate`/
`addScaled`) instead of repeating the same `applyOp?`-case-split four times;
`hEq` lets each call site supply the (defeq-`rfl`) proof that
`ProgConsumesPts` really does unfold to this shape at *that* concrete `op`
— which only holds once `op` is a literal constructor, not a bound
variable (an abstract `op` leaves `ProgConsumesPts`'s own internal `match
op with …` stuck, so this cannot be proven once and reused generically
over `op`). -/
def decideProgConsumesPtsOther {k : ℕ} (hk : k > 0) (σ : State k) (op : valid_ops k) (ops : Prog k)
    (pts : List Point)
    (hEq : ProgConsumesPts hk σ (op :: ops) pts ↔
      ∃ σ', applyOp? (k := k) σ op = some σ' ∧ ProgConsumesPts hk σ' ops pts)
    (rec : (σ' : State k) → Decidable (ProgConsumesPts hk σ' ops pts)) :
    Decidable (ProgConsumesPts hk σ (op :: ops) pts) :=
  match h : applyOp? (k := k) σ op with
  | none => isFalse (fun hp => by obtain ⟨σ', heq, _⟩ := hEq.mp hp; rw [h] at heq; cases heq)
  | some σ' =>
      match rec σ' with
      | isTrue hrec => isTrue (hEq.mpr ⟨σ', h, hrec⟩)
      | isFalse hrec =>
          isFalse (fun hp => by
            obtain ⟨σ'', heq, hrec'⟩ := hEq.mp hp; rw [h] at heq; cases heq; exact hrec hrec')

/-- Term-mode `Decidable` construction for `ProgConsumesPts`, mirroring its
own recursion on `ops` exactly: at
`phaseProduct i`, the existential's witness is `pts`'s own head (nothing to
search for); at any other op, `decideProgConsumesPtsOther` handles it (via
whatever `applyOp?` already computes). Built directly against
`ProgConsumesPts`'s definitional unfolding (no `simp` needed — the
anonymous-constructor proofs below typecheck by the same `match`-reduction
the original `def` itself reduces by), rather than via an `Iff` with a
separately-proven Boolean mirror, since `ProgConsumesPts` itself is not an
`inductive` a mirror-and-transport proof would need to fight the shape of. -/
def decideProgConsumesPts {k : ℕ} (hk : k > 0) :
    (σ : State k) → (ops : Prog k) → (pts : List Point) →
      Decidable (ProgConsumesPts hk σ ops pts)
  | _σ, [], pts => decidable_of_iff (pts = []) Iff.rfl
  | σ, .phaseProduct i :: ops, pts =>
      match pts with
      | [] => isFalse (by rintro ⟨_, _, h, _⟩; cases h)
      | pt :: ptsTail =>
          if h : matchesAt_pointRow_state (k := k) hk σ i pt = true then
            match decideProgConsumesPts hk σ ops ptsTail with
            | isTrue hrec => isTrue ⟨pt, ptsTail, rfl, h, hrec⟩
            | isFalse hrec =>
                isFalse (by rintro ⟨pt', ptsTail', heq, _, hrec'⟩; cases heq; exact hrec hrec')
          else
            isFalse (by rintro ⟨pt', ptsTail', heq, hmatch, _⟩; cases heq; exact h hmatch)
  | σ, (.shiftL a b) :: ops, pts =>
      decideProgConsumesPtsOther hk σ (.shiftL a b) ops pts Iff.rfl
        (fun σ' => decideProgConsumesPts hk σ' ops pts)
  | σ, (.shiftR a b) :: ops, pts =>
      decideProgConsumesPtsOther hk σ (.shiftR a b) ops pts Iff.rfl
        (fun σ' => decideProgConsumesPts hk σ' ops pts)
  | σ, (.negate a) :: ops, pts =>
      decideProgConsumesPtsOther hk σ (.negate a) ops pts Iff.rfl
        (fun σ' => decideProgConsumesPts hk σ' ops pts)
  | σ, (.addScaled a b c d) :: ops, pts =>
      decideProgConsumesPtsOther hk σ (.addScaled a b c d) ops pts Iff.rfl
        (fun σ' => decideProgConsumesPts hk σ' ops pts)

instance decidableProgConsumesPts {k : ℕ} (hk : k > 0) (σ : State k) (ops : Prog k)
    (pts : List Point) : Decidable (ProgConsumesPts hk σ ops pts) :=
  decideProgConsumesPts hk σ ops pts

/-- `SafeProg ops` says every `addScaled d s _ _` occurring anywhere in
`ops` has `d ≠ s`; equivalently, every element of `ops` passes this
Boolean scan. -/
def safeProgCheck {k : ℕ} (ops : Prog k) : Bool :=
  ops.all fun op =>
    match op with
    | valid_ops.addScaled d s _ _ => decide (d ≠ s)
    | _ => true

theorem safeProg_iff_check {k : ℕ} (ops : Prog k) : SafeProg ops ↔ safeProgCheck ops = true := by
  simp only [safeProgCheck, List.all_eq_true]
  constructor
  · intro h op hop
    match op, hop with
    | valid_ops.addScaled d s negSrc sh, hop =>
        obtain ⟨pre, rest, heq⟩ := List.mem_iff_append.mp hop
        exact decide_eq_true (h heq)
    | valid_ops.shiftL .., _ => rfl
    | valid_ops.shiftR .., _ => rfl
    | valid_ops.negate _, _ => rfl
    | valid_ops.phaseProduct _, _ => rfl
  · intro h pre rest d s negSrc sh heq
    have hmem : valid_ops.addScaled d s negSrc sh ∈ ops := heq ▸ List.mem_append_right pre List.mem_cons_self
    simpa using h _ hmem

instance decidableSafeProg {k : ℕ} (ops : Prog k) : Decidable (SafeProg ops) :=
  decidable_of_iff _ (safeProg_iff_check ops).symm

instance decidableProgConsumesPtsSafe {k : ℕ} (hk : k > 0) (σ : State k) (ops : Prog k)
    (pts : List Point) : Decidable (ProgConsumesPtsSafe hk σ ops pts) :=
  decidable_of_iff (ProgConsumesPts hk σ ops pts ∧ SafeProg ops)
    ⟨fun ⟨h1, h2⟩ => ⟨h1, h2⟩, fun h => ⟨h.consumes, h.safe_add⟩⟩

/-! =========================================================
    C2: the points interpolate
========================================================= -/

/-- `GoodToomCookPoints k pts hpts` is, by definition,
`Matrix.det (ToomCookMath.interpMatrix (interpEntry k) (listToFin pts hpts)) ≠ 0`.
Nothing about that needs an instance of its own: `Matrix.det` over `ℚ` with a
`Fin (q k)` index is a finite sum over `Equiv.Perm (Fin (q k))`, computable,
and `≠` on `ℚ` is `Decidable` from `DecidableEq ℚ`. What was missing is only
that the definition had to be unfolded before typeclass search could see any
of it.

Cost: the sum has `(2k-1)!` terms, so `native_decide` is instant through
`k = 5` (`9! = 362 880`) and slow but feasible at `k = 6` (`11! = 39 916
800`). Kernel `decide` is not viable at any interesting `k` and is not how
the template discharges this. -/
instance decidableGoodToomCookPoints (k : ℕ) (pts : List Point) (hpts : pts.length = q k) :
    Decidable (GoodToomCookPoints k pts hpts) :=
  inferInstanceAs
    (Decidable
      (Matrix.det (ToomCookMath.interpMatrix (interpEntry k) (ToomCookMath.listToFin pts hpts))
        ≠ 0))

end Shor

/-! =========================================================
    Smoke tests

    `SUBMISSION_PLAN.md` S2.1. Two checks that the four instances above
    actually decide what they claim to, stated over *literals* so this file
    keeps its one import: nothing here names `standardLoweringSetup`,
    `genOpsWithProduct` or the table generator, even though the data is
    theirs.
========================================================= -/

namespace Shor.SubmissionSmokeTest

open Operations

/-! ### The reference table at `k = 3` is admissible

`genInterpolationPoints 3` and `genOpsWithProduct 3` of them, written out.
All four conditions close by computation, and the result assembles into a
`ShorSubmission` — which is what the S4 template will do with a submitter's
own numbers. -/

def refPts : List Point :=
  [Point.int 0, Point.int (-1), Point.int 1, Point.int (-2), Point.int 2]

def refOps : Prog 3 :=
  [ valid_ops.phaseProduct 0
  , valid_ops.addScaled 0 1 true 0
  , valid_ops.addScaled 0 2 false 0
  , valid_ops.phaseProduct 0
  , valid_ops.addScaled 0 2 true 0
  , valid_ops.addScaled 0 1 false 0
  , valid_ops.addScaled 0 1 false 0
  , valid_ops.addScaled 0 2 false 0
  , valid_ops.phaseProduct 0
  , valid_ops.addScaled 0 2 true 0
  , valid_ops.addScaled 0 1 true 0
  , valid_ops.addScaled 0 1 true 1
  , valid_ops.addScaled 0 2 false 2
  , valid_ops.phaseProduct 0
  , valid_ops.addScaled 0 2 true 2
  , valid_ops.addScaled 0 1 false 1
  , valid_ops.addScaled 0 1 false 1
  , valid_ops.addScaled 0 2 false 2
  , valid_ops.phaseProduct 0
  , valid_ops.addScaled 0 2 true 2
  , valid_ops.addScaled 0 1 true 1
  ]

/-- C1, by `rfl`: `q 3 = 5`. -/
theorem refPts_length : refPts.length = q 3 := rfl

/-- C2. -/
example : GoodToomCookPoints 3 refPts refPts_length := by native_decide

/-- C3. -/
example :
    ProgConsumesPtsSafe (k := 3) (by omega) State.start_state refOps refPts := by
  native_decide

/-- C4. -/
example : run? refOps State.start_state = some State.start_state := by native_decide

/-- The four together: a submission, built the way the template builds one. -/
def refSubmission : ShorSubmission where
  k := 3
  hk := by decide
  pts := refPts
  hpts := refPts_length
  good := by native_decide
  ops := refOps
  consumes := by native_decide
  returns := by native_decide

/-! ### C3 is about the point *order*, not the point set

The `k = 3` precomputed table (`Table_Generation.PrecomputedTables.K3Product`)
consumes the same five canonical points, but in its own order. Paired with
that order it is admissible; paired with the canonical ladder — the same
five points, permuted — C3 fails. This is what makes the points genuine
submission data rather than a constant recoverable from `k` alone, and it is
exactly the mistake the retired `TableSource.generate` path hit when it fed
the naive enumeration to its own ordered-coverage check. -/

def k3Ops : Prog 3 :=
  [ valid_ops.addScaled 0 1 false 0
  , valid_ops.addScaled 1 0 false 0
  , valid_ops.addScaled 0 2 false 0
  , valid_ops.addScaled 1 2 false 2
  , valid_ops.phaseProduct 0
  , valid_ops.phaseProduct 1
  , valid_ops.phaseProduct 2
  , valid_ops.addScaled 0 1 true 0
  , valid_ops.addScaled 0 2 false 1
  , valid_ops.addScaled 1 0 false 1
  , valid_ops.addScaled 0 1 false 0
  , valid_ops.addScaled 1 2 true 1
  , valid_ops.phaseProduct 0
  , valid_ops.phaseProduct 1
  , valid_ops.addScaled 0 2 true 0
  , valid_ops.addScaled 1 0 true 0
  , valid_ops.addScaled 0 1 false 0
  ]

/-- The order `k3Ops`'s checkpoints actually see. -/
def k3Pts : List Point :=
  [Point.int 1, Point.int 2, Point.frac 0, Point.int (-1), Point.int 0]

theorem k3Pts_length : k3Pts.length = q 3 := rfl

/-- Accepted against its own point order. -/
example :
    ProgConsumesPtsSafe (k := 3) (by omega) State.start_state k3Ops k3Pts := by
  native_decide

/-- Rejected against the canonical ladder: same five points, wrong order. -/
example :
    ¬ ProgConsumesPtsSafe (k := 3) (by omega) State.start_state k3Ops refPts := by
  native_decide

/-- C2 does not see the order at all — a permutation only changes the
determinant's sign — so the precomputed table's points are good too, and
`k3Ops` paired with `k3Pts` is a second admissible submission. -/
example : GoodToomCookPoints 3 k3Pts k3Pts_length := by native_decide

example : run? k3Ops State.start_state = some State.start_state := by native_decide

end Shor.SubmissionSmokeTest
