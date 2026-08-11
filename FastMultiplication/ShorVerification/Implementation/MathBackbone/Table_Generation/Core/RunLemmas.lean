import FastMultiplication.ShorVerification.Implementation.MathBackbone.Table_Generation.Core.ListHelpers

/-!
# Generic coverage and execution lemmas

Program-agnostic material quarried verbatim from the former
`One_register_synthesis_combined.lean` (Sections 2-4): coverage bookkeeping
and list-level erasure, coverage composition for concatenated programs, and
the `NoPhase` framework. No statements changed.
-/

open Operations

/-! =========================================================
    Section 2: Coverage bookkeeping and list-level erasure

How this section contributes to the final theorem:
- `List.eraseFirstMatch?_append_hit` is the base list lemma that lets a
  successful point-consumption step survive when more points are appended to
  the right.
- That bookkeeping fact is used directly in the append-style coverage theorems
  that later stitch together the build, phase, and inverse blocks.
========================================================= -/

namespace List
/-- If `eraseFirstMatch? p xs = some ys` then also
    `eraseFirstMatch? p (xs ++ zs) = some (ys ++ zs)`. -/
lemma eraseFirstMatch?_append_hit {α} (p : α → Bool) :
  ∀ {xs ys zs}, eraseFirstMatch? p xs = some ys →
    eraseFirstMatch? p (xs ++ zs) = some (ys ++ zs)
| [],      ys, zs, h => by cases h
| x :: xs, ys, zs, h => by
  dsimp [eraseFirstMatch?] at h ⊢
  by_cases hx : p x
  · simp [hx] at h; cases h; simp [hx]
  · cases hxs : eraseFirstMatch? p xs with
    | none    => simp [hx, hxs] at h
    | some t  =>
      have : ys = x :: t := by aesop
      subst this
      have ih := eraseFirstMatch?_append_hit (xs := xs) (ys := t) (zs := zs)
                    (by simpa [hxs])
      simp [hx, hxs, ih]
end List



/-! =========================================================
    Section 3: Coverage composition for concatenated programs

How these lemmas contribute to `genOpsWithProduct_PhaseProductCoverage`:
- `phaseProduct_coverage_check_append_aux` is the main composition theorem for
  `PhaseProductCoverage`; it is the core engine used whenever two verified
  program fragments are concatenated.
- `phaseProduct_coverage_check_append` is the specialization used when a prefix
  returns to the same state, which is exactly the shape needed for the final
  list-of-points induction.
- `phaseProduct_coverage_check_append_general` keeps the same idea for arbitrary
  intermediate states.
- `PhaseProductCoverage_exists_state_any` and `PhaseProductCoverage_exists_state`
  extract successful executions from coverage proofs, so later append arguments
  can name the intermediate state explicitly.
- `phaseProduct_coverage_check_append_nil` is the empty-point specialization used
  when composing arithmetic-only fragments that should not consume any points.
========================================================= -/

lemma phaseProduct_coverage_check_append_aux
  {k : ℕ} (hk:k>0) (p q : Prog k) (σ : State k) (a b : List Point)
  (hp : PhaseProductCoverage hk p σ a) :
  ∀ (σret : State k),
    run? p σ = some σret →
    PhaseProductCoverage hk q σret b →
    PhaseProductCoverage hk (p ++ q) σ (a ++ b) := by
    let M := matchesAt_pointRow_state (k := k)
    -- do the same structure as the M1 proof
    revert q b
    refine
      (show ∀ {p σ a}, PhaseProductCoverage hk p σ a →
              ∀ (q : Prog k) (b : List Point),
                ∀ (σret : State k),
                  run? p σ = some σret →
                  PhaseProductCoverage hk q σret b →
                  PhaseProductCoverage hk (p ++ q) σ (a ++ b) from
        ?_) hp
    intro p σ a hp
    induction hp with
    | nil =>
        intro q b σret hrun hq
        -- run? [] σ = some σret forces σret = σ
        cases hrun
        simpa using hq

    | @step_op op ps σ τ pts hops hstep hrest ih =>
        intro q b σret hrun hq
        -- From `run? (op::ps) σ = some σret` get `run? ps τ = some σret`.
        have hrun_ps : run? ps τ = some σret := by
          simpa [run?, hstep] using hrun
        -- Build head step and recurse
        refine PhaseProductCoverageM.step_op
          (M := M hk) (op := op) (ps := ps ++ q) (σ := σ) (τ := τ) (pts := pts ++ b)
          (hops := hops) (hstep := hstep) ?_
        simpa [List.cons_append] using ih q b σret hrun_ps hq

    | @step_phase i ps σ pts pts' hcons hrest ih =>
        intro q b σret hrun hq
        have hcons' :
          List.eraseFirstMatch? (fun pt => M hk σ i pt) (pts ++ b) = some (pts' ++ b) :=
          List.eraseFirstMatch?_append_hit _ hcons
        have hrun_ps : run? ps σ = some σret := by
          simpa [run?, applyOp?] using hrun
        refine PhaseProductCoverageM.step_phase
          (M := M hk) (i := i) (ps := ps ++ q) (σ := σ)
          (pts := pts ++ b) (pts' := pts' ++ b) hcons' ?_
        simpa [List.cons_append] using ih q b σret hrun_ps hq

/-- “Returns to σ” corollary with the same hypothesis order as your goal. -/
lemma phaseProduct_coverage_check_append
  {k : ℕ} (hk:k>0) (p q : Prog k) (σ : State k) (a b : List Point)
  (hret : run? p σ = some σ)
  (hp   : PhaseProductCoverage hk p σ a)
  (hq   : PhaseProductCoverage hk q σ b) :
  PhaseProductCoverage hk (p ++ q) σ (a ++ b) :=
  phaseProduct_coverage_check_append_aux hk p q σ a b hp σ hret hq

lemma phaseProduct_coverage_check_append_general
  {k : ℕ} (hk:k>0) (p q : Prog k) (σ σ₁: State k) (a b : List Point)
  (hret : run? p σ = some σ₁)
  (hp   : PhaseProductCoverage hk p σ a)
  (hq   : PhaseProductCoverage hk q σ₁ b) :
  PhaseProductCoverage hk (p ++ q) σ (a ++ b) :=
  phaseProduct_coverage_check_append_aux hk p q σ a b hp σ₁ hret hq

lemma PhaseProductCoverage_exists_state_any
  {k : ℕ} {p : Prog k} {σ₁ : State k} {pts : List Point}
  (hk:k>0)
  (hp : PhaseProductCoverage (k := k) hk p σ₁ pts) :
  ∃ σ₂, run? p σ₁ = some σ₂ := by
  -- Unfold the def-alias so we can induct on the *inductive* itself.
  change
    PhaseProductCoverageM (k := k) (matchesAt_pointRow_state (k := k) hk) p σ₁ pts
    at hp
  induction hp with
  | nil =>
      aesop
  | @step_op op ps σ τ pts hstep hrest ih =>
      rcases ih with ⟨σ₂, hrun⟩
      simp_all
      simp_all
      simp_all
  | @step_phase i ps σ pts pts' hcons hrest ih =>
      rcases ih with ⟨σ₂, hrun⟩
      exact ⟨σ₂, by simp [run?, applyOp?, hrun]⟩

-- Your specialized version for [] is now immediate:
lemma PhaseProductCoverage_exists_state
  {k : ℕ} {p : Prog k} {σ₁ : State k}
  (hk:k>0)
  (hp : PhaseProductCoverage (k := k) hk p σ₁ []) :
  ∃ σ₂, run? p σ₁ = some σ₂ :=
  PhaseProductCoverage_exists_state_any (k := k) (p := p) (σ₁ := σ₁) (pts := []) hk hp

/-- “Returns to σ” corollary with the same hypothesis order as your goal. -/
lemma phaseProduct_coverage_check_append_nil
  {k : ℕ}
  (hk:k>0)
  (p q : Prog k) (σ₁ σ₂ : State k)
  (hret : run? p σ₁ = some σ₂)
  (hp   : PhaseProductCoverage hk p σ₁ [])
  (hq   : PhaseProductCoverage hk q σ₂ []) :
  PhaseProductCoverage hk (p ++ q) σ₁ ([]) :=by {
    apply phaseProduct_coverage_check_append_aux
      (k := k) (p := p) (q := q) (σ := σ₁) (a := []) (b := [])
      hk hp σ₂ hret hq
  }

/-! =========================================================
    Section 4: Programs with no `phaseProduct`

How this section contributes to the final theorem:
- `NoPhase` marks arithmetic-only programs that cannot consume a target point.
- `loop_append_through_nonphase`, `loop_no_phase_todo_eq`,
  `loop_no_phase_nil_todo_eq`, and `loop_no_phase_nil_todo_success` explain how
  coverage behaves when such a program is executed inside the coverage loop.
- `eraseFirstMatch_head_true` and `loop_single_phase_consumes_head` isolate the
  opposite situation: the single `phaseProduct` step that really does consume
  the intended point.
- `NoPhase_append`, `NoPhase_map_pairToOp`, `NoPhase_reverse`, and
  `NoPhase_map_inv_of_NoPhase` show that the `NoPhase` invariant is preserved by
  the program constructors used in synthesis.
- `computeLocal_NoPhase` and `computeLocal_NoPhase_2` prove that both the build
  program and its inverse are arithmetic-only, which is exactly what the final
  theorem needs for the build/phase/unbuild pattern.
========================================================= -/

/-- Abbreviation for the loop so we can state lemmas succinctly. -/
local notation "Loop" => phaseCoverageFrom?.loop

/-- No `phaseProduct` appears in a program. -/
def NoPhase {k} (p : Prog k) : Prop :=
  ∀ i, (valid_ops.phaseProduct (k := k) i) ∉ p

/-- If the left segment `p` contains **no** `phaseProduct`, the loop just
    runs the state through `p` and proceeds to `q` with the same todo. -/
lemma loop_append_through_nonphase {k}
    (m : MatchesAt k) (p q : Prog k) (σ : State k) (todo : List Point)
    (hNP : NoPhase p) :
  phaseCoverageFrom?.loop m (p ++ q) σ todo =
    match run? p σ with
    | none     => none
    | some σ'  => Loop m q σ' todo := by {
      revert σ q todo
      induction p with
      | nil =>
          intro σ q todo; simp [run?, List.nil_append]
      | cons op ps ih =>
          intro σ q todo
          have hNP_op : ∀ i, op ≠ valid_ops.phaseProduct i := by
            intro i
            have := hNP i
            -- `phaseProduct i ∉ op :: ps`
            -- so it cannot be the head
            exact by
              intro h; apply this; simp [h]
          have hNP_ps : NoPhase ps := by
            intro i; have := hNP i; simpa using (by
              -- not in tail if not in cons
              have := this; exact (by
                -- simple membership reasoning
                classical
                by_contra hmem; exact this (by simp [hmem]) ) )
          -- Unfold a single step of the loop/run
          simp [phaseCoverageFrom?.loop, run?, List.cons_append]
          cases applyOp? q op
          simp
          aesop
    }

/-- If a program has no `phaseProduct`, looping with empty todo stays empty. -/
lemma loop_no_phase_todo_eq {k}
    (m : MatchesAt k) (p : Prog k) (σ : State k) (todo : List Point)
    (hNP : NoPhase p) :
  Loop m p σ todo =
    match run? p σ with
    | none    => none
    | some _  => some todo := by
  induction p generalizing σ with
  | nil => simp [phaseCoverageFrom?.loop ]
  | cons op ps ih =>
      have : ∀ i, op ≠ valid_ops.phaseProduct i := by
        intro i; have := hNP i; intro h; exact this (by simp [h])
      have hNP' : NoPhase ps := by
        intro i; have := hNP i; exact by
          classical
          have : valid_ops.phaseProduct i ∉ (op :: ps) := this
          exact by
            intro hmem; exact this (by simp [hmem])
      simp [phaseCoverageFrom?.loop]  -- step through a non-phase op
      cases h : applyOp? σ op with
      | none    => simp
      | some σ' => simpa [h] using ih σ' hNP'

/-- Specialization to the empty todo-list. -/
lemma loop_no_phase_nil_todo_eq {k}
    (m : MatchesAt k) (p : Prog k) (σ : State k) (hNP : NoPhase p) :
  Loop m p σ [] =
    match run? p σ with
    | none    => none
    | some _  => some [] :=
  loop_no_phase_todo_eq (m := m) (p := p) (σ := σ) (todo := []) hNP

/-- Usable corollary when you *know* `run? p σ` succeeds. -/
lemma loop_no_phase_nil_todo_success {k}
    (m : MatchesAt k) (p : Prog k) (σ σ' : State k)
    (hNP : NoPhase p)
    (hrun : run? p σ = some σ') :
  Loop m p σ [] = some [] := by
  simp [loop_no_phase_nil_todo_eq (m := m) (p := p) (σ := σ) hNP, hrun]

/-- `eraseFirstMatch?` removes the head if the predicate is true on it. -/
@[simp] lemma eraseFirstMatch_head_true {α}
    (p : α → Bool) (x : α) (xs : List α) (hx : p x = true) :
  List.eraseFirstMatch? p (x :: xs) = some xs := by
  simp [List.eraseFirstMatch?, hx]

/-- If the predicate is true on the head, a singleton `phaseProduct`
    consumes it and leaves `[]`. -/
lemma loop_single_phase_consumes_head {k}
    (m : MatchesAt k) (i : Fin k) (σ : State k) (head : Point)
    (hmatch : m (σ i) head = true) :
  Loop m [valid_ops.phaseProduct i] σ [head] = some [] := by
  simp [phaseCoverageFrom?.loop, eraseFirstMatch_head_true (p := fun pt => m (σ i) pt) head _ hmatch]

lemma NoPhase_append {k} {p q : Prog k}
  (hp : NoPhase p) (hq : NoPhase q) : NoPhase (p ++ q) := by
  intro i  hmem
  -- membership in append splits
  have : (valid_ops.phaseProduct (k := k) i ∈ p) ∨ (valid_ops.phaseProduct i ∈ q):= (by
    simpa [List.mem_append] using hmem
  )
  cases this with
  | inl hp' => exact (hp i) hp'
  | inr hq' => exact (hq i) hq'

/-- A mapped list of `pairToOp` never produces a `phaseProduct`. -/
lemma NoPhase_map_pairToOp {k}
  (dst src : Fin k) (ps : List (Bool × Nat)) : NoPhase (ps.map (pairToOp dst src)) := by
  intro i  hmem
  rcases List.mem_map.mp hmem with ⟨p, _hp_in, hEq⟩
  cases p with
  | mk neg' sh => simp [pairToOp] at hEq

/-- Reversing doesn’t introduce a `phaseProduct`. -/
lemma NoPhase_reverse {k} {p : Prog k} (hp : NoPhase p) : NoPhase p.reverse := by
  intro i  hmem
  have : valid_ops.phaseProduct (k := k) i ∈ p := by
    simpa [List.mem_reverse] using hmem
  exact (hp i) this

/-- Mapping `inv` doesn’t introduce a `phaseProduct` if there wasn’t one:
    `inv` preserves the `phaseProduct` constructor (and flips others to non-`phaseProduct`). -/
lemma NoPhase_map_inv_of_NoPhase {k} {p : Prog k}
  (hp : NoPhase p) : NoPhase (p.map inv) := by
  intro i hmem
  rcases List.mem_map.mp hmem with ⟨op, hop, hEq⟩
  cases op with
  | shiftL _ _  => simp [inv] at hEq
  | shiftR _ _  => simp [inv] at hEq
  | negate _    => simp [inv] at hEq
  | addScaled _ _ _ _ => simp [inv] at hEq
  | phaseProduct j =>
      have hij : j = i := by simpa [inv] using hEq
      have : valid_ops.phaseProduct (k := k) i ∈ p := by
        simpa [hij] using hop
      exact (hp i) this

lemma computeLocal_NoPhase {k} (hk : 0 < k) (z : Int) :
   NoPhase (computeLocal hk z):=by {
    unfold computeLocal
    set dst := finZero hk
    let step :
        Prog k → Fin k → Prog k :=
      fun acc j =>
        let c : Int := z ^ (j : Nat)
        if c = 0 then acc
        else acc ++ (signedPow2Decomp c).map (pairToOp (k := k) dst j)

    -- Step preserves NoPhase.
    have step_pres :
        ∀ acc, NoPhase acc → ∀ j, NoPhase (step acc j) := by
      intro acc hacc j
      dsimp [step]
      by_cases hc : z ^ (j : Nat) = 0
      · simpa [hc] using hacc
      ·
        have hmap :
            NoPhase ((signedPow2Decomp (z ^ (j : Nat))).map (pairToOp (k := k) dst j)) := by simp[NoPhase_map_pairToOp]
        simp[hc,(NoPhase_append hacc hmap)]
    have base : NoPhase ([] : Prog k) := by intro i; simp
    have fold_pres :
        ∀ (xs : List (Fin k)) (acc : Prog k), NoPhase acc →
          NoPhase (xs.foldl step acc) := by
      intro xs; induction xs with
      | nil =>
          intro acc hacc; simpa [List.foldl] using hacc
      | cons j js ih =>
          intro acc hacc
          have hacc' : NoPhase (step acc j) := step_pres acc hacc j
          simpa [List.foldl] using ih (step acc j) hacc'

    have :=fold_pres (nonzeroFins hk) ([] : Prog k) base
    aesop
   }

/-- Main: `computeLocal` and its inverse contain no `phaseProduct`. -/
lemma computeLocal_NoPhase_2 {k} (hk : 0 < k) (z : Int) :
  NoPhase (computeLocal hk z) ∧ NoPhase (apply_Op_inverse (computeLocal hk z)) := by
  -- First, prove `NoPhase (computeLocal hk z)` by induction over the fold.
  have nop :=  computeLocal_NoPhase hk z
  have nop_inv : NoPhase (apply_Op_inverse (computeLocal hk z)) := by
    unfold apply_Op_inverse
    -- Reverse: preserves NoPhase
    have := NoPhase_reverse (k := k) nop
    -- Map inv: preserves NoPhase
    exact NoPhase_map_inv_of_NoPhase (k := k) this

  exact ⟨nop, nop_inv⟩

