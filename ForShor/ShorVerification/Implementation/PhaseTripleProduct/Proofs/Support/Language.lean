import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Statement

/-!
# The table language: Boolean checkers against the Framework's propositions

`Statement.lean` decides admissibility of a table with Boolean checkers (`progConsumesPts?`,
`safeProg?`, `returnsToStartCheck`), because a policy is checked by `decide`. The Framework
(`ToomCookTable.lean`) states the same conditions as propositions (`ProgConsumesPts`,
`SafeProg`, `run? … = some …`). This file proves the two agree, and collects the small lemmas
about the checkers that the later proofs use:

* `statesEqual_iff`, `returnsToStartCheck_iff`: the Boolean C4 is `run? ops σ = some σ`.
* `safeProg?_iff`, `progConsumesPts?_iff`: the Boolean C3 is the Framework's `SafeProg` and
  `ProgConsumesPts`.
* `CheckedProg`: the three Boolean checks together (the PTP analogue of the Framework's
  `ProgConsumesPtsSafe`, which has no round-trip field).
* `regEqExpected_eq`, `checkpointRows`, `checkpointRows_of_consumes`: consumption pins every
  checkpoint register to the row of its point.
* `sortedDesc_iff`: thresholds strictly decrease.
-/

namespace Shor
namespace PTP

open Operations

/-! ## C4: the table returns to its start -/

/-- `statesEqual` decides equality of states: it compares every register at every index, and
`State k` is a function, so agreement everywhere is equality. -/
theorem statesEqual_iff {k : ℕ} (a b : State k) :
    statesEqual a b = true ↔ a = b := by
  constructor
  · intro h
    have h' := List.all_eq_true.mp h
    funext i j
    have hi := h' i (List.mem_finRange i)
    have hj := List.all_eq_true.mp hi j (List.mem_finRange j)
    exact of_decide_eq_true hj
  · rintro rfl
    simp [statesEqual]

/-- The Boolean round-trip check says exactly that running the program from `σ` succeeds and
lands back on `σ`. At `σ = State.start_state` this is the Framework's C4. -/
theorem returnsToStartCheck_iff {k : ℕ} (ops : Prog k) (σ : State k) :
    returnsToStartCheck ops σ = true ↔ run? ops σ = some σ := by
  unfold returnsToStartCheck
  cases hrun : run? ops σ with
  | none => simp
  | some σ' =>
      constructor
      · intro h
        rw [(statesEqual_iff σ' σ).mp h]
      · intro h
        have hEq : σ' = σ := by
          simp only [Option.some.injEq] at h
          exact h
        rw [hEq]
        exact (statesEqual_iff σ σ).mpr rfl

/-! ## C3: safety and consumption -/

theorem opOK?_iff {k : ℕ} (op : valid_ops k) :
    opOK? op = true ↔ ∀ {d s : Fin k} {negSrc : Bool} {sh : ℕ},
      op = valid_ops.addScaled d s negSrc sh → d ≠ s := by
  cases op with
  | addScaled dst src negSrc shift =>
      simp only [opOK?, decide_eq_true_eq, valid_ops.addScaled.injEq]
      constructor
      · rintro h d s negSrc sh ⟨rfl, rfl, -, -⟩
        exact h
      · intro h
        exact h ⟨rfl, rfl, rfl, rfl⟩
  | shiftL i n => simp [opOK?]
  | shiftR i n => simp [opOK?]
  | negate i => simp [opOK?]
  | phaseProduct i => simp [opOK?]

/-- The Boolean safety check is the Framework's `SafeProg`: no `addScaled` adds a register to
itself. -/
theorem safeProg?_iff {k : ℕ} (ops : Prog k) : safeProg? ops = true ↔ SafeProg ops := by
  unfold safeProg? SafeProg
  induction ops with
  | nil =>
      simp only [wellFormed?, true_iff]
      intro pre rest d s negSrc sh h
      exact absurd h (by simp)
  | cons op ops ih =>
      simp only [wellFormed?, Bool.and_eq_true, opOK?_iff, ih]
      constructor
      · rintro ⟨h1, h2⟩ pre rest d s negSrc sh h
        cases pre with
        | nil =>
            simp only [List.nil_append, List.cons.injEq] at h
            exact h1 h.1
        | cons p pre =>
            simp only [List.cons_append, List.cons.injEq] at h
            exact h2 h.2
      · intro h
        refine ⟨fun {d s negSrc sh} hop => ?_, fun {pre rest d s negSrc sh} hops => ?_⟩
        · exact h (pre := []) (rest := ops) (d := d) (s := s) (negSrc := negSrc) (sh := sh)
            (by simp [hop])
        · exact h (pre := op :: pre) (rest := rest) (d := d) (s := s) (negSrc := negSrc)
            (sh := sh) (by simp [hops])

/-- The Boolean consumption check is the Framework's `ProgConsumesPts`. -/
theorem progConsumesPts?_iff {k : ℕ} (hk : k > 0) :
    ∀ (σ : State k) (ops : Prog k) (pts : List Point),
      progConsumesPts? hk σ ops pts = true ↔ ProgConsumesPts hk σ ops pts
  | σ, [], pts => by
      cases pts <;> simp [progConsumesPts?, ProgConsumesPts]
  | σ, op :: ops, pts => by
      cases op with
      | phaseProduct i =>
          cases pts with
          | nil => simp [progConsumesPts?, ProgConsumesPts]
          | cons pt rest =>
              simp only [progConsumesPts?, ProgConsumesPts, Bool.and_eq_true,
                progConsumesPts?_iff hk σ ops rest, List.cons.injEq]
              constructor
              · rintro ⟨h1, h2⟩
                exact ⟨pt, rest, ⟨rfl, rfl⟩, h1, h2⟩
              · rintro ⟨pt', rest', ⟨rfl, rfl⟩, h1, h2⟩
                exact ⟨h1, h2⟩
      | shiftL i n =>
          simp only [progConsumesPts?, ProgConsumesPts, applyOp?]
          constructor
          · intro h
            exact ⟨_, rfl, (progConsumesPts?_iff hk _ ops pts).mp h⟩
          · rintro ⟨σ', hσ, h⟩
            cases hσ
            exact (progConsumesPts?_iff hk _ ops pts).mpr h
      | shiftR i n =>
          simp only [progConsumesPts?, ProgConsumesPts]
          cases hσ : applyOp? σ (.shiftR i n) with
          | none => simp
          | some σ' =>
              simp only [Option.some.injEq, exists_eq_left']
              exact progConsumesPts?_iff hk σ' ops pts
      | negate i =>
          simp only [progConsumesPts?, ProgConsumesPts, applyOp?]
          constructor
          · intro h
            exact ⟨_, rfl, (progConsumesPts?_iff hk _ ops pts).mp h⟩
          · rintro ⟨σ', hσ, h⟩
            cases hσ
            exact (progConsumesPts?_iff hk _ ops pts).mpr h
      | addScaled d s n sh =>
          simp only [progConsumesPts?, ProgConsumesPts, applyOp?]
          constructor
          · intro h
            exact ⟨_, rfl, (progConsumesPts?_iff hk _ ops pts).mp h⟩
          · rintro ⟨σ', hσ, h⟩
            cases hσ
            exact (progConsumesPts?_iff hk _ ops pts).mpr h

/-- The three Boolean checks a table's program must pass (C3 and C4). -/
structure CheckedProg {k : ℕ} (hk : k > 0) (σ : State k) (ops : Prog k) (pts : List Point) :
    Prop where
  consumes : progConsumesPts? hk σ ops pts = true
  safe_add : safeProg? ops = true
  returns_start : returnsToStartCheck ops σ = true

theorem checkedProg_of_checks {k : ℕ} {hk : k > 0} {σ : State k} {ops : Prog k}
    {pts : List Point} (hconsumes : progConsumesPts? hk σ ops pts = true)
    (hsafe : safeProg? ops = true) (hreturns : returnsToStartCheck ops σ = true) :
    CheckedProg hk σ ops pts where
  consumes := hconsumes
  safe_add := hsafe
  returns_start := hreturns

theorem positive_of_ge_two {k : ℕ} (hk : k ≥ 2) : k > 0 :=
  Nat.lt_of_lt_of_le (by decide : 0 < 2) hk

/-- The Framework's admissibility of a program (`ProgConsumesPtsSafe` plus the round trip) is
`CheckedProg`. -/
theorem checkedProg_iff_framework {k : ℕ} (hk : k > 0) (σ : State k) (ops : Prog k)
    (pts : List Point) :
    CheckedProg hk σ ops pts ↔
      (ProgConsumesPtsSafe hk σ ops pts ∧ run? ops σ = some σ) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨(progConsumesPts?_iff hk σ ops pts).mp h1, (safeProg?_iff ops).mp h2⟩,
      (returnsToStartCheck_iff ops σ).mp h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨(progConsumesPts?_iff hk σ ops pts).mpr h1, (safeProg?_iff ops).mpr h2,
      (returnsToStartCheck_iff ops σ).mpr h3⟩

/-! ## Checkpoints -/

theorem regEqExpected_eq {k : ℕ} {r : Register k} {pt : Point}
    (h : regEqExpected r pt = true) : r = expectedRow pt := by
  unfold regEqExpected at h
  funext j
  exact of_decide_eq_true (List.all_eq_true.mp h j (List.mem_finRange j))

/-- The register contents at each `phaseProduct` checkpoint, running the program from `σ`;
`none` when a right shift is inexact. -/
def checkpointRows {k : ℕ} : State k → Prog k → Option (List (Register k))
  | _, [] => some []
  | σ, op :: ops =>
      match op with
      | .phaseProduct i => (checkpointRows σ ops).map (fun rows => σ i :: rows)
      | _ =>
          match applyOp? σ op with
          | none => none
          | some σ' => checkpointRows σ' ops

/-- The point-consumption check pins every checkpoint: the `t`-th `phaseProduct` finds its
register holding exactly `expectedRow pts[t]`. -/
theorem checkpointRows_of_consumes {k : ℕ} (hk : k > 0) :
    ∀ (ops : Prog k) (σ : State k) (pts : List Point),
      progConsumesPts? hk σ ops pts = true →
        checkpointRows σ ops = some (pts.map expectedRow)
  | [], σ, pts, h => by
      cases pts with
      | nil => rfl
      | cons _ _ => simp [progConsumesPts?] at h
  | op :: ops, σ, pts, h => by
      cases op with
      | phaseProduct i =>
          cases pts with
          | nil => simp [progConsumesPts?] at h
          | cons pt rest =>
              simp only [progConsumesPts?, Bool.and_eq_true] at h
              obtain ⟨hm, hr⟩ := h
              have hrow : σ i = expectedRow pt := regEqExpected_eq hm
              simp [checkpointRows, checkpointRows_of_consumes hk ops σ rest hr, hrow]
      | shiftL i n =>
          simp only [progConsumesPts?, applyOp?] at h
          simp only [checkpointRows, applyOp?]
          exact checkpointRows_of_consumes hk ops _ pts h
      | shiftR i n =>
          simp only [progConsumesPts?] at h
          simp only [checkpointRows]
          cases hσ : applyOp? σ (.shiftR i n) with
          | none => rw [hσ] at h; cases h
          | some σ' =>
              rw [hσ] at h
              exact checkpointRows_of_consumes hk ops σ' pts h
      | negate i =>
          simp only [progConsumesPts?, applyOp?] at h
          simp only [checkpointRows, applyOp?]
          exact checkpointRows_of_consumes hk ops _ pts h
      | addScaled d s n sh =>
          simp only [progConsumesPts?, applyOp?] at h
          simp only [checkpointRows, applyOp?]
          exact checkpointRows_of_consumes hk ops _ pts h

/-! ## Thresholds -/

theorem sortedDesc_iff (l : List ℕ) : sortedDesc l = true ↔ l.IsChain (· > ·) := by
  induction l with
  | nil => simp [sortedDesc]
  | cons a t ih =>
    cases t with
    | nil => simp [sortedDesc]
    | cons b rest =>
      simp only [sortedDesc, Bool.and_eq_true, decide_eq_true_eq, List.isChain_cons_cons]
      rw [ih]

end PTP
end Shor
