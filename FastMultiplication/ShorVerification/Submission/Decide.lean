import FastMultiplication.ShorVerification.Framework.ToomCookTable
import FastMultiplication.ShorVerification.Framework.Policy
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Deciding a submission's four side conditions

A submitter packaging their own table as a `Shor.ShorSubmission` has to
discharge C1-C4 (`Framework/ToomCookTable.lean`) for concrete `k`, `pts` and
`ops`. This file makes all four a matter of computation the *kernel* can do,
so `by decide +kernel` closes them and the kernel, not a parser and not the
compiled evaluator, is what checks a submission. `Submission/Audit.lean` is
what holds a submission to that; see `Submission/Template.lean` for the five
lines this buys.

Like the record it is about, this file is implementation-free: it imports
`Framework/ToomCookTable`, `Framework/Policy` and Mathlib, and nothing else.
(`Policy.lean` is for the policy smoke tests at the end; the four
single-table decision procedures need nothing from it.)

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
- **C2** `GoodToomCookPoints` unfolds to `Matrix.det (…) ≠ 0` over `ℚ`. That
  determinant is computable, but it is a sum over `(2k-1)!` permutations, so
  evaluating it is not something the kernel will do. The interpolation matrix
  is Mathlib's `Matrix.projVandermonde` in the projective coordinates of
  `projV`/`projW`, and `Matrix.det_projVandermonde` factors it, so C2 is
  *equivalent* to the points being pairwise distinct as projective points
  (`goodToomCookPoints_iff_distinct`) — a quadratic scan the kernel reduces
  instantly at every supported `k`.
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

/-- The first projective coordinate of an interpolation point.

`interpEntry k p j` is `z ^ j` for `int z` and `c ^ (q k - 1 - j)` for
`frac c`, so writing `int z` as the projective point `(z : 1)` and `frac c`
as `(1 : c)` makes the interpolation matrix *literally* Mathlib's
`Matrix.projVandermonde` (`interpMatrix_eq_projVandermonde`). `frac 0` is
then `(1 : 0)`, the point at infinity, exactly as `Framework`'s table says. -/
def projV : Point → ℤ
  | .int z  => z
  | .frac _ => 1

/-- The second projective coordinate; see `projV`. -/
def projW : Point → ℤ
  | .int _  => 1
  | .frac c => c

/-- `p` and `p'` are different *projective* points: their coordinate vectors
are not proportional. Written out for the three shapes,

* `int z` and `int z'`: `z' - z ≠ 0`;
* `frac c` and `frac c'`: `c - c' ≠ 0`;
* `int z` and `frac c`: `1 - z * c ≠ 0`, i.e. `z ≠ 1 / c`.

The last line is why `frac 0` — the point at infinity — is distinct from
every `int`, and why `int 1` and `frac 1` are the *same* point and are
rejected. -/
def DistinctPair (p p' : Point) : Prop :=
  projV p' * projW p - projV p * projW p' ≠ 0

/-- **C2, restated as a check a submitter can read.** The points are
pairwise distinct as projective points. `goodToomCookPoints_iff_distinct`
proves this equivalent to `GoodToomCookPoints`, and unlike the determinant it
costs one integer subtraction of two products per pair — `q k * (q k - 1) / 2`
of them — rather than `(2k-1)!` permutation terms. That is what makes C2
viable in the kernel. -/
def PointsDistinct (pts : List Point) : Prop := pts.Pairwise DistinctPair

/-- `DistinctPair` as a `Bool`. -/
def distinctPairCheck (p p' : Point) : Bool :=
  decide (projV p' * projW p - projV p * projW p' ≠ 0)

/-- The pairwise scan behind `decidablePointsDistinct`: head against every
later point, then recurse. Same pattern as `safeProgCheck` — a `Bool` the
kernel reduces, plus the transport lemma below — rather than Mathlib's
generic `List.Pairwise` instance, so that what `decide +kernel` has to
evaluate is visible here. -/
def pointsDistinctCheck : List Point → Bool
  | []      => true
  | p :: ps => ps.all (distinctPairCheck p) && pointsDistinctCheck ps

theorem pointsDistinct_iff_check (pts : List Point) :
    PointsDistinct pts ↔ pointsDistinctCheck pts = true := by
  induction pts with
  | nil => simp [PointsDistinct, pointsDistinctCheck]
  | cons p ps ih =>
      simp only [PointsDistinct, List.pairwise_cons, pointsDistinctCheck, Bool.and_eq_true,
        List.all_eq_true] at *
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨fun p' hp' => by simpa [distinctPairCheck, DistinctPair] using h1 p' hp', ih.mp h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨fun p' hp' => by simpa [distinctPairCheck, DistinctPair] using h1 p' hp', ih.mpr h2⟩

instance decidablePointsDistinct (pts : List Point) : Decidable (PointsDistinct pts) :=
  decidable_of_iff _ (pointsDistinct_iff_check pts).symm

/-- `interpEntry` is a `projVandermonde` row in the coordinates of `projV`
and `projW`. `Fin.rev j` is `q k - 1 - j`, which is the exponent
`interpEntry` already uses for `frac`. -/
theorem interpEntry_eq_projVandermonde_entry (k : ℕ) (p : Point) (j : Fin (q k)) :
    interpEntry k p j = (projV p : ℚ) ^ (j : ℕ) * (projW p : ℚ) ^ (j.rev : ℕ) := by
  cases p with
  | int z => simp [interpEntry, projV, projW]
  | frac c =>
      simp only [interpEntry, projV, projW, Int.cast_one, one_pow, one_mul, Fin.val_rev]
      congr 1
      omega

/-- C2's matrix *is* a projective Vandermonde matrix. -/
theorem interpMatrix_eq_projVandermonde (k : ℕ) (pts : List Point) (hpts : pts.length = q k) :
    ToomCookMath.interpMatrix (interpEntry k) (ToomCookMath.listToFin pts hpts) =
      Matrix.projVandermonde
        (fun i => (projV (ToomCookMath.listToFin pts hpts i) : ℚ))
        (fun i => (projW (ToomCookMath.listToFin pts hpts i) : ℚ)) := by
  ext i j
  simp [ToomCookMath.interpMatrix, Matrix.projVandermonde_apply,
    interpEntry_eq_projVandermonde_entry]

/-- `DistinctPair` is stated over `ℤ`; this is the same statement about the
`ℚ`-valued factor `Matrix.det_projVandermonde` produces. -/
theorem distinctPair_iff_cast (p p' : Point) :
    DistinctPair p p' ↔
      (projV p' : ℚ) * (projW p : ℚ) - (projV p : ℚ) * (projW p' : ℚ) ≠ 0 := by
  rw [show ((projV p' : ℚ) * (projW p : ℚ) - (projV p : ℚ) * (projW p' : ℚ))
        = ((projV p' * projW p - projV p * projW p' : ℤ) : ℚ) by push_cast; ring,
    DistinctPair, ne_eq, ne_eq, Int.cast_eq_zero]

/-- **C2 is pairwise distinctness.** `Matrix.det_projVandermonde` writes the
determinant as `∏_{i < j} (v j * w i - v i * w j)`, and `ℚ` is a domain, so
the determinant is nonzero exactly when every factor is — which is
`PointsDistinct` read through `List.pairwise_iff_get`.

This replaces the `(2k-1)!`-term determinant with a quadratic scan, and it is
an equivalence, not merely a sufficient condition: a table `PointsDistinct`
rejects is genuinely inadmissible, not just unproven. -/
theorem goodToomCookPoints_iff_distinct {k : ℕ} {pts : List Point} (hpts : pts.length = q k) :
    GoodToomCookPoints k pts hpts ↔ PointsDistinct pts := by
  rw [GoodToomCookPoints, ToomCookMath.GoodInterpolationPoints,
    interpMatrix_eq_projVandermonde, Matrix.det_projVandermonde, PointsDistinct,
    List.pairwise_iff_get]
  constructor
  · intro h i j hij
    refine (distinctPair_iff_cast _ _).mpr ?_
    have hi := Finset.prod_ne_zero_iff.mp h ⟨i.1, by omega⟩ (Finset.mem_univ _)
    exact Finset.prod_ne_zero_iff.mp hi ⟨j.1, by omega⟩ (Finset.mem_Ioi.mpr (Fin.lt_def.mpr hij))
  · intro h
    refine Finset.prod_ne_zero_iff.mpr (fun i _ => Finset.prod_ne_zero_iff.mpr (fun j hj => ?_))
    have hij : i.1 < j.1 := Fin.lt_def.mp (Finset.mem_Ioi.mp hj)
    exact (distinctPair_iff_cast _ _).mp
      (h ⟨i.1, by omega⟩ ⟨j.1, by omega⟩ (Fin.lt_def.mpr hij))

/-- The direction a submission uses: prove the cheap check, get C2. -/
theorem goodToomCookPoints_of_distinct {k : ℕ} {pts : List Point} (hpts : pts.length = q k)
    (h : PointsDistinct pts) : GoodToomCookPoints k pts hpts :=
  (goodToomCookPoints_iff_distinct hpts).mpr h

/-- C2's `Decidable` instance, routed through `PointsDistinct` rather than
through `Matrix.det`.

The determinant is computable outright — `Matrix.det` over `ℚ` with a
`Fin (q k)` index is a finite sum over `Equiv.Perm (Fin (q k))` — but it has
`(2k-1)!` terms, which is 39 916 800 at `k = 6` and not something the kernel
will evaluate. Going through `goodToomCookPoints_iff_distinct` instead makes
`by decide +kernel` the normal way to discharge C2 at every supported `k`. -/
instance decidableGoodToomCookPoints (k : ℕ) (pts : List Point) (hpts : pts.length = q k) :
    Decidable (GoodToomCookPoints k pts hpts) :=
  decidable_of_iff _ (goodToomCookPoints_iff_distinct hpts).symm

end Shor

/-! =========================================================
    Smoke tests

    Checks that the instances above actually decide what they claim to,
    stated over *literals* so this file keeps its one import: nothing here
    names `standardLoweringSetup`, `genOpsWithProduct` or the table
    generator, even though the data is theirs.

    Every proof below is `decide +kernel`, never `native_decide`: these are
    the same lines a submitter writes, so they are also the evidence that a
    submission can be discharged by the kernel alone. `Submission/Audit.lean`
    is what enforces that on a submission.
========================================================= -/

namespace Shor.SubmissionSmokeTest

open Operations

/-! ### The reference table at `k = 3` is admissible

`genInterpolationPoints 3` and `genOpsWithProduct 3` of them, written out.
All four conditions close by computation, and the result assembles into a
`ShorSubmission` — which is what `Template.lean` does with a submitter's
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

/-- C2, through `PointsDistinct`: five distinct integer points. -/
example : GoodToomCookPoints 3 refPts refPts_length :=
  goodToomCookPoints_of_distinct refPts_length (by decide +kernel)

/-- C3. -/
example :
    ProgConsumesPtsSafe (k := 3) (by omega) State.start_state refOps refPts := by
  decide +kernel

/-- C4. -/
example : run? refOps State.start_state = some State.start_state := by decide +kernel

/-- The four together: a submission, built the way the template builds one. -/
def refSubmission : ShorSubmission where
  k := 3
  hk := by decide
  pts := refPts
  hpts := refPts_length
  good := goodToomCookPoints_of_distinct refPts_length (by decide +kernel)
  ops := refOps
  consumes := by decide +kernel
  returns := by decide +kernel

/-! ### C3 is about the point *order*, not the point set

The `k = 3` precomputed table (`Table_Generation.PrecomputedTables.K3Product`)
consumes the same five canonical points, but in its own order. Paired with
that order it is admissible; paired with the canonical ladder — the same
five points, permuted — C3 fails. This is what makes the points genuine
submission data rather than a constant recoverable from `k` alone, and it is
the mistake an earlier second table source hit when it fed
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
  decide +kernel

/-- Rejected against the canonical ladder: same five points, wrong order. -/
example :
    ¬ ProgConsumesPtsSafe (k := 3) (by omega) State.start_state k3Ops refPts := by
  decide +kernel

/-- C2 does not see the order at all — a permutation only changes the
determinant's sign — so the precomputed table's points are good too, and
`k3Ops` paired with `k3Pts` is a second admissible submission. -/
example : GoodToomCookPoints 3 k3Pts k3Pts_length :=
  goodToomCookPoints_of_distinct k3Pts_length (by decide +kernel)

example : run? k3Ops State.start_state = some State.start_state := by decide +kernel

/-! ### C2 at the largest supported `k`, and what it rejects

The canonical ladder at `k = 6` is eleven points, so the determinant C2 is
*defined* as has `11! = 39 916 800` terms. `PointsDistinct` scans 55 pairs
instead, and the kernel closes it outright. -/

def ladder6 : List Point :=
  [Point.int 0, Point.int (-1), Point.int 1, Point.int (-2), Point.int 2,
   Point.int (-3), Point.int 3, Point.int (-4), Point.int 4, Point.int (-5),
   Point.int 5]

theorem ladder6_length : ladder6.length = q 6 := rfl

example : GoodToomCookPoints 6 ladder6 ladder6_length :=
  goodToomCookPoints_of_distinct ladder6_length (by decide +kernel)

/-- `frac c` is the point `1 / c`, so `int 1` and `frac 1` are the same
point and the pair is rejected — as is `int (-1)` with `frac (-1)`. This is
the failure a determinant would report only as `det = 0`. -/
example : ¬ PointsDistinct [Point.int 1, Point.frac 1] := by decide +kernel

example : ¬ PointsDistinct [Point.int (-1), Point.frac (-1)] := by decide +kernel

/-- `frac 0` is the point at infinity: distinct from every `int`, and from
every other `frac`. -/
example : PointsDistinct [Point.frac 0, Point.int 0, Point.int 7, Point.frac 3] := by
  decide +kernel

/-- The equivalence runs backwards too, so rejection is a real verdict: a
list with a repeated point is not merely unproven but inadmissible. -/
example : ¬ GoodToomCookPoints 2 [Point.int 1, Point.frac 1, Point.int 0] rfl := by
  rw [goodToomCookPoints_iff_distinct]
  decide +kernel

/-! ### A policy submission

A policy is a list of `(threshold, ShorLoweringSetup)` bands with strictly
decreasing thresholds (`Framework/Policy.lean`). Nothing new has to be
decided: each band is a table submission, carrying exactly the C1–C4 above,
and the one extra field — that the thresholds strictly decrease — is closed
by Batteries' `Decidable (l.IsChain R)` instance over `Nat.decLt`.

The policy below is the `k = 3` reference table above width 40 and the
`k = 2` table `Submission/Template.lean` ships between 12 and 40, with the
schoolbook leaf below 12. (`Template.lean` imports this file, so its table is
restated here rather than referenced.) -/

/-- The `k = 2` table of `Submission/Template.lean`: canonical points
`0, -1, 1`, reached by negating register 1 rather than subtracting. -/
def tmplPts : List Point :=
  [Point.int 0, Point.int (-1), Point.int 1]

theorem tmplPts_length : tmplPts.length = q 2 := rfl

def tmplOps : Prog 2 :=
  [ valid_ops.phaseProduct 0
  , valid_ops.negate 1
  , valid_ops.addScaled 0 1 false 0
  , valid_ops.phaseProduct 0
  , valid_ops.negate 1
  , valid_ops.addScaled 0 1 false 0
  , valid_ops.addScaled 0 1 false 0
  , valid_ops.phaseProduct 0
  , valid_ops.addScaled 0 1 true 0
  ]

def tmplSubmission : ShorSubmission where
  k := 2
  hk := by decide
  pts := tmplPts
  hpts := tmplPts_length
  good := goodToomCookPoints_of_distinct tmplPts_length (by decide +kernel)
  ops := tmplOps
  consumes := by decide +kernel
  returns := by decide +kernel

/-- Two bands: Toom-3 above 40, Karatsuba from 12 to 39, leaf below 12. The
`sorted` field is the whole of what a policy adds to its bands. -/
def refPolicySubmission : ShorPolicySubmission where
  bands := [(40, refSubmission), (12, tmplSubmission)]
  sorted := by decide

/-- Above the top threshold the widest band wins. -/
example : refPolicySubmission.policy.choose 100 = some refSubmission.table := rfl

/-- At `40` itself, too: a band covers `[threshold, _)`. -/
example : refPolicySubmission.policy.choose 40 = some refSubmission.table := rfl

/-- Between the thresholds, the second band. -/
example : refPolicySubmission.policy.choose 20 = some tmplSubmission.table := rfl

/-- Below the last threshold there is no table, which *is* the leaf. -/
example : refPolicySubmission.policy.choose 5 = none := rfl

/-- And the policy is admissible, because its bands are submissions. -/
example : refPolicySubmission.policy.Admissible :=
  refPolicySubmission.policy_admissible

/-- The sort check is a real verdict: the same two thresholds the other way
round are rejected, so a policy cannot list a narrow band before a wide one
and have the wide one shadowed. -/
example : ¬ List.IsChain (· > ·) [12, 40] := by decide

/-- Equal thresholds are rejected too — the decrease is strict, so a width is
covered by exactly one band. -/
example : ¬ List.IsChain (· > ·) [40, 40] := by decide

/-- A table submission is the one-band policy at threshold `0`, and that
policy picks the same table at every width. -/
example (n : ℕ) : (ShorPolicySubmission.ofSetup refSubmission).policy.choose n
    = some refSubmission.table := by simp

end Shor.SubmissionSmokeTest
