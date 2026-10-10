import FastMultiplication.ShorVerification.Framework.ToomCookTable

/-!
# What a lowering policy is, and what makes one admissible

The second kind of submission. A table submission
(`Framework/ToomCookTable.lean`) is one Toom-Cook table used at every level
of the recursive phase product. A **policy** chooses a table by operand
width — Toom-6 at the top, Toom-3 in the middle, Karatsuba near the leaves,
the schoolbook leaf below an explicit threshold — and each table it can pick
carries its own C1–C4. The score is a gate count at one fixed size, not an
asymptotic exponent, and at a fixed size the optimum is a cascade rather
than a single radix; that is the whole motivation.

Like the file it imports, this one is implementation-free: it imports
`Framework/ToomCookTable.lean` and nothing else (not even Mathlib directly),
so each kind of submission can be read on its own. The import rule is
one-directional — `Policy.lean` imports `ToomCookTable.lean`, never the
reverse — because a reader of the single-table specification should not have
to read the policy to understand a table.

The split between data and proof mirrors the one the plan type already
makes. `PhaseLoweringPlan` needs only `(k, hk, pts, hpts, ops)`; C2–C4 are
hypotheses of the correctness theorem, not fields of the object being built.
So:

| | what it is |
|---|---|
| `ToomCookTable` | the data `(k, hk, pts, hpts, ops)`, no side conditions |
| `ToomCookTable.Admissible` | C2–C4 for one table |
| `ShorLoweringPolicy` | a list of `(threshold, table)` bands, strictly decreasing in threshold |
| `ShorLoweringPolicy.Admissible` | every table the policy can pick is admissible |
| `ShorPolicySubmission` | a list of `(threshold, ShorLoweringSetup)`: the bands *with* their proofs |

Three design points, each load-bearing downstream:

- **The policy is keyed on width, not depth.** `choose` is applied to a plan
  node's `initSize` (`= max x.width z.width`). The width at depth 3 depends
  on the choices made at depths 1 and 2, so a depth-indexed policy could not
  be reasoned about without simulating the chain. Width-indexing also makes
  the leaf threshold explicit: `choose n = none` *is* the leaf.
- **The shrink test stays.** Within a band the recursion still falls to the
  leaf when the chosen table does not shrink the width (`Stops`). Termination
  stays free and no fifth side condition is introduced.
- **A table submission is the one-band policy at threshold `0`.**
  `constPolicy` and `ShorPolicySubmission.ofSetup` are what make the existing
  single-table path a special case rather than a parallel one.
-/

namespace Shor

open Operations

/-! =========================================================
    One table: data, and what makes it admissible
========================================================= -/

/-- The data of a Toom-Cook table: what the plan type needs, without C2–C4.

The same five components `ShorLoweringSetup` carries, with the three proof
fields dropped. A policy is built out of these, and admissibility is asked of
them separately (`Admissible`) so that the plan type can be indexed by data
alone. -/
structure ToomCookTable where
  /-- Number of synthesis registers used by the lowering program. -/
  k    : ℕ
  /-- At least two synthesis registers are available. -/
  hk   : 1 < k
  /-- Interpolation points the table is built against. -/
  pts  : List Point
  /-- One point per product coefficient. (C1) -/
  hpts : pts.length = q k
  /-- The table itself. -/
  ops  : Prog k

/-- C2–C4 for one table. The same three conjuncts as `PhaseProductProgramOK`
(`Implementation/GateCount/Definitions.lean`), stated here so the
specification does not import GateCount; the two are related by
`ToomCookTable.admissible_iff_programOK` on that side of the import. C1 is
not a conjunct because it is already the field `hpts`. -/
def ToomCookTable.Admissible (T : ToomCookTable) : Prop :=
  GoodToomCookPoints T.k T.pts T.hpts ∧
  ProgConsumesPtsSafe (k := T.k) (by have := T.hk; omega) State.start_state T.ops T.pts ∧
  run? T.ops State.start_state = some State.start_state

/-- The table underlying a submission: a `ShorLoweringSetup` with its proofs
forgotten.

This projection lives here rather than next to the record, because the record
does not need to know that policies exist. -/
def ShorLoweringSetup.table (s : ShorLoweringSetup) : ToomCookTable :=
  ⟨s.k, s.hk, s.pts, s.hpts, s.ops⟩

/-- A submission's table is admissible: that is exactly what its `good`,
`consumes` and `returns` fields say. -/
theorem ShorLoweringSetup.table_admissible (s : ShorLoweringSetup) : s.table.Admissible :=
  ⟨s.good, s.consumes, s.returns⟩

@[simp] theorem ShorLoweringSetup.table_k (s : ShorLoweringSetup) : s.table.k = s.k := rfl

@[simp] theorem ShorLoweringSetup.table_pts (s : ShorLoweringSetup) : s.table.pts = s.pts := rfl

@[simp] theorem ShorLoweringSetup.table_ops (s : ShorLoweringSetup) : s.table.ops = s.ops := rfl

/-! =========================================================
    The policy
========================================================= -/

/-- One band of a policy: use `table` whenever `threshold ≤ max xw zw`. -/
structure PolicyBand where
  /-- The smallest operand width this band covers. -/
  threshold : ℕ
  /-- The table to use on that band. -/
  table     : ToomCookTable

/-- A width-indexed choice of table.

The bands are a step function, given as a list whose thresholds are
*strictly decreasing*, so that band `i` covers `[tᵢ, tᵢ₋₁)` literally and the
extracted width dispatcher is a clean chain of guards. Widths below the last
threshold take the leaf. `bands = []` is the all-leaf policy: admissible, and
quadratic. -/
structure ShorLoweringPolicy where
  /-- The bands, widest first. -/
  bands  : List PolicyBand
  /-- Thresholds strictly decrease, so the bands partition the widths. -/
  sorted : (bands.map PolicyBand.threshold).IsChain (· > ·)

namespace ShorLoweringPolicy

/-- The table the policy uses at operand width `n`: the first band whose
threshold is `≤ n`. `none` is the leaf. -/
def choose (P : ShorLoweringPolicy) (n : ℕ) : Option ToomCookTable :=
  (P.bands.find? (fun b => decide (b.threshold ≤ n))).map PolicyBand.table

/-- Every table the policy can pick is admissible.

Stated over the bands rather than over the range of `choose` so that a
submission discharges it band by band. `Admissible.of_choose` is the
direction the correctness proof uses. -/
def Admissible (P : ShorLoweringPolicy) : Prop :=
  ∀ b ∈ P.bands, b.table.Admissible

/-- What an admissible policy gives the lowering proof at one node: whatever
table got chosen there satisfies C2–C4. -/
theorem Admissible.of_choose {P : ShorLoweringPolicy} (hP : P.Admissible) {n : ℕ}
    {T : ToomCookTable} (h : P.choose n = some T) : T.Admissible := by
  unfold choose at h
  rcases hb : P.bands.find? (fun b => decide (b.threshold ≤ n)) with _ | b
  · rw [hb] at h; exact absurd h (by simp)
  · rw [hb] at h
    have hT : b.table = T := by simpa using h
    exact hT ▸ hP b (List.mem_of_find?_eq_some hb)

/-- The recursion at `initSize` takes the leaf: either the policy picks no
table there, or the table it picks does not shrink the width.

The next-width function is abstracted because `nextSignedWidth` lives in
`Implementation/`; the plan type instantiates
`nextW := fun T => nextSignedWidth x z T.ops`. This is the side condition
`PhaseLoweringPlan.signedBase` carries, and it is a *consequence* of the
width-keyed shape rather than a fifth admissibility condition: no submitter
proves it. -/
def Stops (P : ShorLoweringPolicy) (initSize : ℕ) (nextW : ToomCookTable → ℕ) : Prop :=
  ∀ T, P.choose initSize = some T → ¬ nextW T < initSize

/-! ### The constant policy

Today's single-table submission, viewed as a policy. Everything the
single-table path proves is the `constPolicy` case of what the policy path
proves. -/

/-- One table at every width: today's submission, as a policy. -/
def constPolicy (T : ToomCookTable) : ShorLoweringPolicy :=
  ⟨[⟨0, T⟩], by simp⟩

@[simp] theorem constPolicy_choose (T : ToomCookTable) (n : ℕ) :
    (constPolicy T).choose n = some T := by
  simp [constPolicy, choose]

@[simp] theorem constPolicy_bands (T : ToomCookTable) :
    (constPolicy T).bands = [⟨0, T⟩] := rfl

theorem constPolicy_admissible {T : ToomCookTable} (h : T.Admissible) :
    (constPolicy T).Admissible := by
  simp [constPolicy, Admissible, h]

end ShorLoweringPolicy

/-! =========================================================
    The submission
========================================================= -/

/-- A policy submission: each band is a `ShorLoweringSetup`, i.e. a table
*with* its C1–C4, exactly as a table submission is.

The only thing a policy adds on top of the per-band obligations a submitter
already knows how to discharge is `sorted`, which `decide` closes. -/
structure ShorPolicySubmission where
  /-- The bands, widest first: a threshold and the setup to use above it. -/
  bands  : List (ℕ × ShorLoweringSetup)
  /-- Thresholds strictly decrease. -/
  sorted : (bands.map Prod.fst).IsChain (· > ·)

namespace ShorPolicySubmission

/-- The policy a submission denotes: its bands with the proofs forgotten. -/
def policy (s : ShorPolicySubmission) : ShorLoweringPolicy :=
  ⟨s.bands.map (fun b => ⟨b.1, b.2.table⟩), by
    simpa [List.map_map, Function.comp_def] using s.sorted⟩

@[simp] theorem policy_bands (s : ShorPolicySubmission) :
    s.policy.bands = s.bands.map (fun b => ⟨b.1, b.2.table⟩) := rfl

/-- A policy submission's policy is admissible. This is the whole content of
the acceptance check for a policy: the per-band records already carry C1–C4,
and `sorted` is decidable. -/
theorem policy_admissible (s : ShorPolicySubmission) : s.policy.Admissible := by
  intro b hb
  rw [policy_bands, List.mem_map] at hb
  obtain ⟨a, _, rfl⟩ := hb
  exact a.2.table_admissible

/-- A table submission is the one-band policy submission at threshold `0`. -/
def ofSetup (s : ShorLoweringSetup) : ShorPolicySubmission := ⟨[(0, s)], by simp⟩

@[simp] theorem ofSetup_policy (s : ShorLoweringSetup) :
    (ofSetup s).policy = ShorLoweringPolicy.constPolicy s.table := rfl

end ShorPolicySubmission

end Shor
