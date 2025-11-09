import FastMultiplication.Synthesis_programs

open Operations

-- lemma phaseProduct_coverage_check_append_cons_of_returns {k : ℕ}
--     (p q : Prog k) (σ : State k)
--     (head : Point) (tail : List Point)
--     (hret : run? p σ = some σ)
--     (hp   : phaseProduct_coverage_check p σ [head] = true)
--     (hq   : phaseProduct_coverage_check q σ tail   = true) :
--   phaseProduct_coverage_check (p ++ q) σ (head :: tail) = true := by {
--     sorry
--   }

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


lemma phaseProduct_coverage_check_append_aux
  {k : ℕ} (hk:k>0) (p q : Prog k) (σ : State k) (a b : List Point)
  (hp : PhaseProductCoverage hk p σ a) :
  ∀ (σret : State k),
    run? p σ = some σret →
    PhaseProductCoverage hk q σret b →
    PhaseProductCoverage hk (p ++ q) σ (a ++ b) := by {
      let M := matchesAt_pointRow_state (k := k)
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
          aesop
      | @step_op op ps σ τ a hstep hrest ih =>
          intro q b σret hrun hq
          -- From `run? (op::ps) σ = some σret` get `run? ps τ = some σret`.
          have hrun_ps : run? ps τ = some σret := by simpa [run?, hstep] using hrun
          -- Build head step and recurse on `(ps ++ q)`.
          refine PhaseProductCoverageM.step_op
            (M := M hk) (op := op) (ps := ps ++ q) (σ := σ) (τ := τ) (pts := a ++ b)
            (by simpa [applyOp?] using hstep) ?_
          simpa [List.cons_append] using ih q b σret hrun_ps hq
      | @step_phase i ps σ a a' hcons hrest ih =>
          intro q b σret hrun hq
          -- Lift the consumption from `a` to `a ++ b`.
          have hcons' :
            List.eraseFirstMatch? (fun pt => M hk σ i pt) (a ++ b) = some (a' ++ b) :=
            List.eraseFirstMatch?_append_hit _ hcons
          -- Push `run?` through the phase (no-op).
          have hrun_ps : run? ps σ = some σret := by
            simpa [run?, applyOp?] using hrun
          -- Phase step then recurse.
          refine PhaseProductCoverageM.step_phase
            (M := M hk) (i := i) (ps := ps ++ q) (σ := σ)
            (pts := a ++ b) (pts' := a' ++ b) hcons' ?_
          simpa [List.cons_append] using ih q b σret hrun_ps hq
    }

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
      exact ⟨σ₂, by simp [run?, hstep, hrun]⟩
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

-- lemma phaseProduct_coverage_check_append_nil_reverse
--   {k : ℕ} (p q : Prog k) (σ₁ σ₂ : State k)
--   (hret : run? p σ₁ = some σ₂)
--   (hp:PhaseProductCoverage (p ++ q) σ₁ ([]))
--    :((PhaseProductCoverage q σ₂ [])) :=by {
--     sorry
--   }


-- theorem genOpsWithProduct_append (hk : 0 < k)(h:Point)(t:List Point):
--   genOpsWithProduct hk (h::t)=genOpsWithProduct hk [h]++genOpsWithProduct hk t:= by
--     sorry



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

-- lemma singleton_inf_covers {k} (hk : 0 < k) :
--   phaseCoverageFrom? (fun r pt ↦ regEqExpected r pt)
--     (opsForPointWithProduct hk .inf) State.start_state [.inf] = true := by
--   simp [opsForPointWithProduct, phaseCoverageFrom?, phaseCoverageFrom?.loop,
--         regEqExpected, expectedRow, State.start_state, List.eraseFirstMatch?]
--   sorry

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

  -- Second, show `NoPhase (apply_Op_inverse (computeLocal hk z))`.
  -- `apply_Op_inverse p = p.reverse.map inv`, and both `reverse` and `map inv`
  -- preserve `NoPhase` given the first result.
  have nop_inv : NoPhase (apply_Op_inverse (computeLocal hk z)) := by
    unfold apply_Op_inverse
    -- Reverse: preserves NoPhase
    have := NoPhase_reverse (k := k) nop
    -- Map inv: preserves NoPhase
    exact NoPhase_map_inv_of_NoPhase (k := k) this

  exact ⟨nop, nop_inv⟩







-- theorem genOpsWithProduct_phase_coverage
--   {k : Nat} (hk : 0 < k) (pts : List Point) :
--   phaseProduct_coverage_check (genOpsWithProduct hk pts) State.start_state pts := by {
--     induction pts with
--     | nil=>{
--       unfold genOpsWithProduct phaseProduct_coverage_check phaseCoverageFrom? matchesAt_pointRow phaseCoverageFrom?.loop
--       simp
--     }
--     | cons head tail ih=>{
--       rw[genOpsWithProduct_append,phaseProduct_coverage_check_append_cons_of_returns]
--       {
--         sorry
--       }
--       {
--         unfold genOpsWithProduct opsForPointWithProduct-- phaseProduct_coverage_check matchesAt_pointRow phaseCoverageFrom? phaseCoverageFrom?.loop --matchesAt_pointRow phaseCoverageFrom?.loop opsForPointWithProduct
--         cases head with
--         | int x => {
--           simp
--         }
--         | inf=> {

--           sorry
--         }
--       }
--       {
--         rw[ih]
--       }
--     }
--   }

/-- A single `addScaled` always succeeds and consumes no points. -/
lemma cover_addScaled_nil {k} (hk:k>0) (σ : State k) (dst src : Fin k) (neg' : Bool) (sh : ℕ) :
  PhaseProductCoverage (hk:k>0) [valid_ops.addScaled dst src (negSrc := neg') sh] σ [] := by
  refine PhaseProductCoverageM.step_op
    (M := matchesAt_pointRow_state (k := k) (hk:k>0))
    (op := valid_ops.addScaled dst src (negSrc := neg') sh)
    (ps := []) (σ := σ)
    (τ := State.addScaledReg σ dst src (negSrc := neg') sh)
    (pts := []) ?hstep ?tail
  · simp [applyOp?]
  · simpa using PhaseProductCoverageM.nil (M := matchesAt_pointRow_state (k := k) (hk)) (σ := _)

/-- A mapped list of `(neg,shift)` pairs to `addScaled` ops consumes no points. -/
lemma cover_map_pairToOp_nil {k} (hk:k>0) (σ : State k) (dst src : Fin k) (pairs : List (Bool × Nat)) :
  PhaseProductCoverage hk (pairs.map (pairToOp (k := k) dst src)) σ [] := by
  classical
  revert σ
  induction pairs with
  | nil =>
      intro σ; apply PhaseProductCoverageM.nil
  | cons p ps ih =>
      intro σ
      refine
        PhaseProductCoverageM.step_op
          (M := matchesAt_pointRow_state hk (k := k))
          (op := pairToOp (k := k) dst src p)
          (ps := ps.map (pairToOp (k := k) dst src)) (σ := σ)
          (τ := State.addScaledReg σ dst src (negSrc := p.1) p.2)
          (pts := []) ?h ?t
      · simp [applyOp?, pairToOp]
      · simpa using ih _

-- 1) Fold-left with "append-on-the-right" form:  foldl (λ acc a, acc ++ H a)
lemma foldl_append_hom {α β} :
  ∀ (H : α → List β) (acc : List β) (xs : List α),
    List.foldl (fun acc a => acc ++ H a) acc xs
      = acc ++ List.foldl (fun acc a => acc ++ H a) [] xs
| H, acc, []      => by simp
| H, acc, a::xs   => by
  simp [foldl_append_hom H (acc ++ H a) xs, List.append_assoc]

-- -- 2) `run?` never fails on a block made of `addScaled` ops (like map pairToOp …)
-- lemma run_some_of_map_pairToOp {k} (dst src : Fin k)
--   : ∀ (pairs : List (Bool × Nat)) (σ : State k),
--       ∃ σ', run? (pairs.map (pairToOp (k := k) dst src)) σ = some σ'
-- | [],      σ => ⟨σ, by simp⟩
-- | p :: ps, σ => by {
--   unfold run?
--   simp
--   sorry
-- }

lemma run_some_of_map_pairToOp {k} (dst src : Fin k) :
  ∀ (pairs : List (Bool × Nat)) (σ : State k),
    ∃ σ', run? (pairs.map (pairToOp (k := k) dst src)) σ = some σ'
| [],      σ => ⟨σ, by simp⟩
| p :: ps, σ =>
  by
    -- recursive call with *named arguments* so Lean doesn't try to infer dst/src from σ
    rcases run_some_of_map_pairToOp (k := k) (dst := dst) (src := src) ps
            (State.addScaledReg σ dst src (negSrc := p.1) p.2) with ⟨σ', ih⟩
    refine ⟨σ', ?_⟩
    -- one addScaled step, then the IH on the tail
    simp [ applyOp?, pairToOp, ih]

/-- If the head step succeeds and the whole run of `(op :: ps)` returns `σ₂`,
    then the tail `ps` run from the post-state `τ` also returns `σ₂`. -/
lemma run_tail_of_head {k}
  {op : valid_ops k} {ps : Prog k}
  {σ τ σ₂ : State k}
  (hstep : applyOp? (k := k) σ op = some τ)
  (hrun  : run? (op :: ps) σ = some σ₂) :
  run? ps τ = some σ₂ := by
  simpa [run?, hstep] using hrun

/-- Build coverage for `(op :: ps) ++ q` from a single successful head step
    and coverage of the rest `(ps ++ q)`. -/
lemma step_op_append {k}
  {op : valid_ops k} {ps q : Prog k}
  {σ τ : State k}
  (hk:k>0)
  (hstep : applyOp? (k := k) σ op = some τ)
  (hrest : PhaseProductCoverage hk (ps ++ q) τ []) :
  PhaseProductCoverage hk ((op :: ps) ++ q) σ [] := by
  refine PhaseProductCoverageM.step_op
    (M := matchesAt_pointRow_state (k := k) hk)
    (op := op) (ps := ps ++ q) (σ := σ) (τ := τ) (pts := [])
    (by simpa [applyOp?] using hstep) ?_
  -- `ps` appended under the cons:
  simpa [List.cons_append] using hrest



lemma phaseCoverage_append_nil
  {k} (p q : Prog k) {σ σ₂ : State k}
  (hk:k>0)
  (hp  : PhaseProductCoverage hk p σ [])
  (hr  : run? p σ = some σ₂)
  (hq  : PhaseProductCoverage hk q σ₂ []) :
  PhaseProductCoverage hk (p ++ q) σ [] := by
  have aux :
    ∀ {p σ pts}, PhaseProductCoverage hk p σ pts → pts = [] →
      ∀ (q : Prog k) (σ₂ : State k),
        run? p σ = some σ₂ →
        PhaseProductCoverage hk q σ₂ [] →
        PhaseProductCoverage hk (p ++ q) σ [] := by
    intro p σ pts hcov hpts q σ₂ hr hq
    revert q σ₂
    induction hcov generalizing q σ₂ with
    | nil =>
        intro q σ₂ hrun hq
        aesop
    | @step_op op ps σ τ pts hstep hrest ih =>
        intro q σ₂ hrun hq
        -- push run? through the head step
        have htail : run? ps τ = some σ₂ := by
          simpa [run?, hstep] using hrun
        -- recurse on (ps ++ q); use pts = [] via `hpts`
        have hrest' :
          PhaseProductCoverage hk (ps ++ q) τ [] := by
          aesop
        -- rebuild ((op :: ps) ++ q)
        refine PhaseProductCoverageM.step_op
          (M := matchesAt_pointRow_state (k := k) hk)
          (op := op) (ps := ps ++ q) (σ := σ) (τ := τ) (pts := [])
          (by simpa [applyOp?] using hstep) ?_
        simpa using hrest'
    | @step_phase i ps σ pts pts' hcons hrest ih =>
        intro q σ₂ hrun hq
        -- impossible when pts = []
        cases hpts
        have : False := by simp [List.eraseFirstMatch?] at hcons
        exact this.elim
  exact aux hp rfl q σ₂ hr hq

/-- The fold-step function used inside `computeLocal`. -/
private def step {k} (hk : 0 < k) (z : Int) :
    Prog k → Fin k → Prog k :=
  fun acc j =>
    let dst := finZero hk
    let c   : Int := z ^ (j : Nat)
    if c = 0 then acc
    else acc ++ (signedPow2Decomp c).map (pairToOp (k := k) dst j)


lemma cover_computeLocal_nil {k} (hk : 0 < k) (σ : State k) (z : Int) :
  PhaseProductCoverage hk (computeLocal (k := k) hk z) σ [] := by
  unfold computeLocal
  set dst := finZero hk
  -- We prove a paired property across the fold:
  --   (COV) for all σ, the accumulated program covers []
  --   (RUN) for all σ, run? succeeds (exists σ')
  have main :
    ∀ (xs : List (Fin k)) (acc : Prog k),
      (∀ σ, PhaseProductCoverage hk acc σ []) →
      (∀ σ, ∃ σ', run? acc σ = some σ') →
      (∀ σ, PhaseProductCoverage hk (xs.foldl (step (k := k) hk z) acc) σ [])
      ∧
      (∀ σ, ∃ σ', run? (xs.foldl (step (k := k) hk z) acc) σ = some σ') := by
      intro xs
      induction xs with
      | nil =>
          intro acc Hcov Hrun
          simpa using And.intro (Hcov) (Hrun)
      | cons j js ih =>
          intro acc Hcov Hrun
          -- analyze the step at head j
          dsimp [step]
          by_cases hc : z ^ (j : Nat) = 0
          · -- nothing appended; fold just continues with `acc`
            simpa [List.foldl, hc] using ih acc Hcov Hrun
          · -- append one mapped block of addScaled ops
            have Hblk_cov :
              ∀ σ, PhaseProductCoverage
                hk ((signedPow2Decomp (z ^ (j : Nat))).map (pairToOp (k := k) dst j)) σ [] :=
              by intro σ0; simpa using cover_map_pairToOp_nil hk (k := k) σ0 dst j _
            -- COV for `acc ++ block` using append lemma
            have Hcov' :
              ∀ σ, PhaseProductCoverage hk
                (acc ++ (signedPow2Decomp (z ^ (j : Nat))).map (pairToOp (k := k) dst j)) σ [] :=
            by
              intro σ0
              obtain ⟨σ1, hrun1⟩ := Hrun σ0
              exact phaseCoverage_append_nil
                (hp := Hcov σ0) (hr := hrun1) (hq := Hblk_cov σ1)
            -- RUN for `acc ++ block`: combine `run?` on `acc` and on the block
            have Hrun' :
              ∀ σ, ∃ σ', run? (acc ++ (signedPow2Decomp (z ^ (j : Nat))).map (pairToOp (k := k) dst j)) σ = some σ' :=
            by
              intro σ0
              obtain ⟨σ1, hrun1⟩ := Hrun σ0
              obtain ⟨σ2, hrun2⟩ :=
                run_some_of_map_pairToOp (k := k) dst j (signedPow2Decomp (z ^ (j : Nat))) σ1
              refine ⟨σ2, ?_⟩
              simp [run?_append, hrun1, hrun2]
            -- continue the fold on the tail with the enlarged accumulator
            simpa [List.foldl, hc, List.append_assoc]
              using ih (acc ++ (signedPow2Decomp (z ^ (j : Nat))).map (pairToOp (k := k) dst j)) Hcov' Hrun'
  -- Base accumulator is `[]`.
  have base_cov : ∀ σ, PhaseProductCoverage hk ([] : Prog k) σ [] :=
    by intro σ0; simpa using PhaseProductCoverageM.nil (M := matchesAt_pointRow_state hk (k := k)) (σ := σ0)
  have base_run : ∀ σ, ∃ σ', run? ([] : Prog k) σ = some σ' :=
    by intro σ0; exact ⟨σ0, by simp [run?]⟩
  -- Apply the fold result to `nonzeroFins hk` and your given `σ`.
  have cov_all := (main (nonzeroFins (k := k) hk) [] base_cov base_run).1
  unfold step at cov_all
  simp at cov_all
  simp
  unfold dst
  simp[cov_all]


/-- Existence: `computeLocal hk z` never fails; it returns *some* state from any input. -/
lemma run_some_computeLocal {k : ℕ} (hk : 0 < k) (z : Int) (σ : State k) :
  ∃ σ', run? (computeLocal (k := k) hk z) σ = some σ' := by {
    let step :
        Prog k → Fin k → Prog k :=
      fun acc j =>
        let dst := finZero (k := k) hk
        let c   : Int := z ^ (j : Nat)
        if c = 0 then acc
        else acc ++ (signedPow2Decomp c).map (pairToOp (k := k) dst j)

    -- Block: a mapped list of `(neg,shift)` to `addScaled` never fails to run.
    have run_some_of_block :
        ∀ (dst src : Fin k) (pairs : List (Bool × Nat)) (σ : State k),
          ∃ σ', run? (pairs.map (pairToOp (k := k) dst src)) σ = some σ'
      := by
        intro dst src
        intro pairs σ0
        revert σ0
        induction pairs with
        | nil =>
            intro σ0; exact ⟨σ0, by simp⟩
        | cons p ps ih =>
            intro σ0
            rcases ih (State.addScaledReg σ0 dst src (negSrc := p.1) p.2) with ⟨σ', ih'⟩
            refine ⟨σ', ?_⟩
            simp [applyOp?, pairToOp, ih']
    have main :
      ∀ (xs : List (Fin k)) (acc : Prog k),
        (∀ σ, ∃ σ', run? acc σ = some σ') →
        (∀ σ, ∃ σ', run? (xs.foldl step acc) σ = some σ')
    := by
      intro xs
      induction xs with
      | nil =>
          intro acc Hrun σ0; simpa using Hrun σ0
      | cons j js ih =>
          intro acc Hrun σ0
          -- analyze the head `j`
          dsimp [step]
          by_cases hc : z ^ (j : Nat) = 0
          · -- nothing appended at this `j`
            have :=ih acc Hrun σ0
            simp_all only [pow_eq_zero_iff', ne_eq, true_and, ite_not, pow_zero, not_false_eq_true, zero_pow,
              ↓reduceIte, step]
          · -- append one mapped block, then continue
            obtain ⟨σ1, hacc⟩ := Hrun σ0
            obtain ⟨σ2, hblk⟩ :=
              run_some_of_block (finZero (k := k) hk) j (signedPow2Decomp (z ^ (j : Nat))) σ1
            have Hrun' :
                ∀ σ, ∃ σ', run? (acc ++ (signedPow2Decomp (z ^ (j : Nat))).map
                                   (pairToOp (k := k) (finZero (k := k) hk) j)) σ
                            = some σ'
              := by
                intro σx
                -- run `acc` to σ1, then run the block to σ2
                -- the exact σ1/σ2 depend on σx but we just need existence
                obtain ⟨σ1x, h1⟩ := Hrun σx
                obtain ⟨σ2x, h2⟩ :=
                  run_some_of_block (finZero (k := k) hk) j
                                    (signedPow2Decomp (z ^ (j : Nat))) σ1x
                exact ⟨σ2x, by simp [run?_append, h1, h2]⟩
            simp_all only [pow_eq_zero_iff', ne_eq, not_and, Decidable.not_not, step]
            split
            next h => simp_all only [true_and, ite_not, pow_zero, imp_false, not_true_eq_false]
            next h => simp_all only [not_and, not_true_eq_false, not_false_eq_true, implies_true]
    -- Base: `[]` always runs (returns the input state).
    have base_run : ∀ σ, ∃ σ', run? ([] : Prog k) σ = some σ' :=
      by intro σ0; exact ⟨σ0, by simp [run?]⟩

    -- Apply to `computeLocal` = fold over `nonzeroFins hk`.
    simpa [computeLocal, step] using main (nonzeroFins (k := k) hk) [] base_run σ
  }


/-- Pull a single membership out of `xs.all p = true`. -/
private lemma all_true_of_mem {α} (p : α → Bool) :
  ∀ {xs : List α} {x : α}, xs.all p = true → x ∈ xs → p x = true
| [],      x, hall, hx => by cases hx
| y :: ys, x, hall, hx => by
  simp_all only [List.all_cons, Bool.and_eq_true, List.all_eq_true, List.mem_cons]
  obtain ⟨left, right⟩ := hall
  cases hx with
  | inl h =>
    subst h
    simp_all only
  | inr h_1 => simp_all only


-- @[simp] lemma State.addScaledReg_apply
--   (σ : State k) (dst src : Fin k) (b : Bool) (sh : ℕ) (t : Fin k) :
--   (State.addScaledReg σ dst src (negSrc := b) sh) t =
--     if t = dst then
--       fun u => if u = dst then
--         σ dst u + ((if b then (-1 : ℤ) else 1) * ((σ src u) * (2 : ℤ)^sh))
--       else σ dst u
--     else σ t := by sorry


open Operations

@[simp] lemma pairToOp_unfold {k} (dst src : Fin k) (p : Bool × Nat) :
  pairToOp (k := k) dst src p
    = valid_ops.addScaled dst src (negSrc := p.1) p.2 := by
  cases p ; simp [pairToOp]

@[simp] lemma applyOp?_addScaled {k} (σ : State k)
    (dst src : Fin k) (neg' : Bool) (sh : ℕ) :
  applyOp? (k := k) σ (valid_ops.addScaled dst src (negSrc := neg') sh)
    = some (State.addScaledReg σ dst src (negSrc := neg') sh) := rfl

/-- `0 : Fin k` packaged with the proof `0 < k`. -/
@[simp] lemma finZero_val {k} (hk : 0 < k) :
  (finZero (k := k) hk).val = 0 := rfl

/-- `nonzeroFins hk` excludes `0`. -/
@[simp] lemma nonzeroFins_excludes_zero {k} (hk : 0 < k) :
  finZero (k := k) hk ∉ nonzeroFins (k := k) hk := by
  classical
  unfold nonzeroFins
  -- filtered by predicate (· ≠ finZero hk)
  simp [finZero]


/-- Start state is the “basis”: register `i` is the unit vector `e_i`. -/
@[simp] lemma State.start_state_apply {k} (i j : Fin k) :
  (State.start_state (k := k)) i j = (if j = i then (1 : Int) else 0) := rfl

--/****************  BIT-DECOMP: SHIFTS LIST SUMS TO N  **************/

-- private def sumPow2 (ls : List Nat) : Int :=
--   ls.foldl (fun acc s => acc + (2 : Int) ^ s) 0

-- /-- Key arithmetic identity used by `shiftsOfAux` recursion:
--     the sum of powers-of-two at offsets `sh` enumerated by `shiftsOfAux`
--     equals `2^sh * n`. -/
-- lemma shiftsOfAux_sumPow2 :
--   ∀ (n sh : Nat), sumPow2 (shiftsOfAux n sh) = ((2 : Int) ^ sh) * (n : Int)
-- | 0,      sh => by
--   simp [shiftsOfAux, sumPow2]
-- | (n+1),  sh => by
--   -- matches the recursive definition in your file
--   simp [shiftsOfAux, sumPow2] -- splits on `Nat.bodd (n+1)`
--   have ih := shiftsOfAux_sumPow2 ((n+1)/2) (sh+1)
--   sorry
-- /-- Sum of the powers-of-two at positions given by `shiftsOf n` equals `n`. -/
-- lemma shiftsOf_sumPow2 (n : Nat) :
--   sumPow2 (shiftsOf n) = (n : Int) := by
--   simpa [shiftsOf] using shiftsOfAux_sumPow2 n 0

--/****************  SIGNED POW2 DECOMP: EVALUATION  ******************/

/-- “Numeric value” of a `(neg,shift)` list as an integer sum. -/
private def evalPairs : List (Bool × Nat) → Int
| []        => 0
| (b,s)::ps => (if b then (-1 : Int) else 1) * (2 : Int) ^ s + evalPairs ps

@[simp] lemma evalPairs_nil : evalPairs [] = 0 := rfl
@[simp] lemma evalPairs_cons (b : Bool) (s : Nat) (ps : List (Bool × Nat)) :
  evalPairs ((b,s)::ps) = (if b then (-1 : Int) else 1) * (2 : Int) ^ s + evalPairs ps := rfl

-- ---------- scalar “weight” of a (neg,shift) pair and its list-sum ----------
/-- Weight of a `(neg, shift)` pair as an integer. -/
def wsum1 (p : Bool × Nat) : Int :=
  (if p.1 then (-1 : Int) else 1) * (2 : Int) ^ p.2

/-- Sum of weights. -/
def wsum : List (Bool × Nat) → Int
| []      => 0
| p :: ps => wsum1 p + wsum ps

@[simp] lemma wsum_nil : wsum ([] : List (Bool × Nat)) = 0 := rfl
@[simp] lemma wsum_cons (p : Bool × Nat) (ps) :
  wsum (p :: ps) = wsum1 p + wsum ps := rfl

-- /-- Numeric value of `signedPow2Decomp` equals the original integer. -/
-- lemma signedPow2Decomp_wsum (c : Int) : wsum (signedPow2Decomp c) = c := by
--   unfold signedPow2Decomp
--   by_cases hc : c = 0
--   · simp [hc]
--   ·
--     set neg' := (c < 0)
--     set m   := Int.natAbs c
--     have hw :
--       wsum ((shiftsOf m).map (fun s => (neg', s)))
--         = (if neg' then (-1 : Int) else 1) *
--             ( (shiftsOf m).foldl (fun acc s => acc + (2 : Int) ^ s) 0 ) := by
--       -- rewrite w.r.t. map; easy induction on `shiftsOf m`
--       revert neg'
--       induction (shiftsOf m) with
--       | nil =>
--           intro; simp
--       | cons s ss ih =>
--           intro; simp [wsum1];aesop;sorry;sorry
--     have hsum :
--       ( (shiftsOf m).foldl (fun acc s => acc + (2 : Int) ^ s) 0 ) = (m : Int) := by
--       -- you already have this as `shiftsOf_sumPow2`
--       simpa using shiftsOf_sumPow2 m
--     have hmag : (m : Int) = |c| := by aesop
--     have sgn :
--         (if neg' then (-1 : Int) else 1) * (m : Int) = c := by
--       by_cases hlt : c < 0
--       · have : (m : Int) = -c := by simp [hmag];simp[le_of_lt hlt]
--         simp [neg', hlt, this]            -- (-1)*(-c) = c
--       · have : (m : Int) = c := by aesop
--         simp [neg', hlt, this]
--     aesop

/-- One mapped block affects only `dst`, and linearly by `wsum` on each coordinate. -/
lemma run_map_pairToOp_coord
    (dst src : Fin k) (pairs : List (Bool × Nat))
    {σ τ : State k}
    (hr : run? (pairs.map (pairToOp (k := k) dst src)) σ = some τ)
    (hsd:¬src=dst)
     :
    ∀ u, τ dst u = σ dst u + wsum pairs * σ src u := by
  classical
  revert σ τ hr
  induction pairs with
  | nil =>
      intro σ τ hr u; aesop
  | cons p ps ih =>
      intro σ τ hr u
      -- split head and tail
      have hstep :
        ∃ σ₁, applyOp? (k := k) σ (pairToOp (k := k) dst src p) = some σ₁
            ∧ run? (ps.map (pairToOp (k := k) dst src)) σ₁ = some τ := by
        refine ⟨State.addScaledReg σ dst src (negSrc := p.1) p.2, ?_, ?_⟩
        · simp [applyOp?, pairToOp]
        · simp_all only [List.map_cons, pairToOp_unfold, run?_cons, applyOp?_addScaled]
      rcases hstep with ⟨σ₁, hhd, htl⟩
      -- apply IH on the tail starting from σ₁
      have tail := ih htl u
      -- compute the head step on coordinate u
      have head :
        (State.addScaledReg σ dst src (negSrc := p.1) p.2) dst u
          = σ dst u + wsum1 p * σ src u := by
        -- expand `addScaledReg` on the destination
        simp [State.addScaledReg, State.setReg, Register.addScaled, wsum1]
        simp[Int.mul_comm]

      -- compute that the source register is not changed by the head step
      have src_unch :
        (State.addScaledReg σ dst src (negSrc := p.1) p.2) src u = σ src u := by
        -- because `setReg` only overwrites `dst`
        by_cases h : src = dst
        · contradiction

        · simp [State.addScaledReg, State.setReg, h]
      -- combine head + tail
      simp_all only [List.map_cons, pairToOp_unfold, run?_cons, applyOp?_addScaled, Option.some.injEq,
        State.addScaledReg_self, Register.addScaled_apply, Int.reduceNeg, ite_mul, neg_mul, one_mul, add_right_inj,
        ne_eq, not_false_eq_true, State.addScaledReg_other, wsum_cons]
      subst hhd
      simp_all only [State.addScaledReg_self, Register.addScaled_apply, Int.reduceNeg, ite_mul, neg_mul, one_mul,
        ne_eq, not_false_eq_true, State.addScaledReg_other]
      obtain ⟨fst, snd⟩ := p
      simp_all only
      split at head
      next h =>
        subst h
        linarith
      next h =>
        simp_all only [Bool.not_eq_true]
        subst h
        linarith

/-- The same mapped block preserves all non-`dst` registers. -/
lemma run_map_pairToOp_preserve
    (dst src : Fin k) (pairs : List (Bool × Nat))
    {σ τ : State k}
    (hr : run? (pairs.map (pairToOp (k := k) dst src)) σ = some τ)
    {t : Fin k} (ht : t ≠ dst) :
  τ t = σ t := by
  classical
  revert σ τ hr
  induction pairs with
  | nil =>
      intro σ τ hr; aesop
  | cons p ps ih =>
      intro σ τ hr
      have hstep :
        ∃ σ₁, applyOp? (k := k) σ (pairToOp (k := k) dst src p) = some σ₁
            ∧ run? (ps.map (pairToOp (k := k) dst src)) σ₁ = some τ := by
        refine ⟨State.addScaledReg σ dst src (negSrc := p.1) p.2, ?_, ?_⟩
        · simp [applyOp?, pairToOp]
        ·
          have : run? ((pairToOp (k := k) dst src p) ::
                       ps.map (pairToOp (k := k) dst src)) σ = some τ := by
            simpa using hr
          exact this
      rcases hstep with ⟨σ₁, hhd, htl⟩
      have tail := ih htl
      -- head preserves non-dst register `t`
      have head_pres :
        (State.addScaledReg σ dst src (negSrc := p.1) p.2) t = σ t := by
        simp [State.addScaledReg, State.setReg, ht]
      aesop
-- /******************************************************************************/
-- /*                         One block (for a single j)                         */
-- /******************************************************************************/

-- Your block for source j with weight c going into dst
def Block {k} (dst src : Fin k) (c : Int) : Prog k :=
  if c = 0 then [] else (signedPow2Decomp c).map (pairToOp (k := k) dst src)

-- /-- Effect of a single Block on coordinates of `dst`. -/
-- lemma run_Block_dst_coord {k}
--   {dst src : Fin k} {c : Int} {σ τ : State k}
--   (hr : run? (Block (k := k) dst src c) σ = some τ)
--   (hsd : src ≠ dst) :
--   ∀ u, τ dst u = σ dst u + c * σ src u := by
--   classical
--   unfold Block at hr
--   by_cases hc : c = 0
--   · simp [hc];simp[hc] at hr;simp[hr]
--   ·
--     have h := run_map_pairToOp_coord (k := k) dst src (signedPow2Decomp c)
--                  (σ := σ) (τ := τ)
--                  (by simpa [hc, Block] using hr) (by simpa using hsd)
--     intro u
--     aesop
--     by_cases hb:σ src u = 0
--     simp[hb]
--     simp[hb]
--     unfold wsum signedPow2Decomp
--     simp[hc]
--     sorry

/-- `Block` preserves all non-`dst` registers. -/
lemma run_Block_preserve {k}
  {dst src : Fin k} {c : Int} {σ τ : State k}
  (hr : run? (Block (k := k) dst src c) σ = some τ)
  {t : Fin k} (ht : t ≠ dst) :
  τ t = σ t := by
  classical
  unfold Block at hr
  by_cases hc : c = 0
  · simp [hc] at hr
    have hr2:some σ = some τ:=by simp[hr]
    exact (Option.some.inj hr2).symm ▸ rfl
  ·
    exact
      run_map_pairToOp_preserve (k := k) dst src (signedPow2Decomp c)
        (by simpa [hc, Block] using hr) ht



/-- Expose `computeLocal` as a left-fold of `Block`s. -/
lemma computeLocal_eq_foldBlocks {k} (hk : 0 < k) (z : Int) :
  computeLocal (k := k) hk z
    =
  (nonzeroFins (k := k) hk).foldl
    (fun acc j => acc ++ Block (k := k) (finZero hk) j (z ^ (j : Nat))) [] := by
  classical
  unfold computeLocal Block
  simp_all only [pow_eq_zero_iff', ne_eq, List.foldl_append_eq_append, List.nil_append]
  have step_eta :
    (fun acc (j : Fin k) =>
      if z = 0 ∧ ¬(j : Nat) = 0 then acc
      else acc ++ List.map (pairToOp (finZero hk) j) (signedPow2Decomp (z ^ (j : Nat))))
    =
    (fun acc (j : Fin k) =>
      acc ++ (if z = 0 ∧ ¬(j : Nat) = 0 then []
              else List.map (pairToOp (finZero hk) j) (signedPow2Decomp (z ^ (j : Nat))))) := by
    funext acc j
    by_cases h : z = 0 ∧ ¬(j : Nat) = 0
    · simp [h]
    · simp [h]
  -- 2) Put it in the `foldl (λ acc j, acc ++ G j) []` form.
  simp [step_eta]


-- -- Sum of contributions of sources S into coordinate u
-- def contrib (k : Nat) (z : Int) (S : List (Fin k)) (u : Fin k) : Int :=
--   S.foldl (fun acc j => acc + z ^ (j : Nat) * (State.start_state (k := k) j u)) 0

-- /-- Main fold lemma: running the Blocks for `S` from `start_state` gives
--     (i) non-dst regs unchanged, (ii) dst-coord = base + contrib(S). -/
-- lemma run_blocks_from_start {k} (hk : 0 < k) (z : Int)
--   (S : List (Fin k)) {σ : State k}
--   (hr : run?
--           (S.foldl (fun acc j => acc ++ Block (k := k) (finZero hk) j (z ^ (j : Nat))) [])
--           (State.start_state (k := k)) = some σ) :
--   (∀ t, t ≠ finZero hk → σ t = State.start_state (k := k) t)
--   ∧ (∀ u, σ (finZero hk) u =
--           State.start_state (k := k) (finZero hk) u + contrib (k := k) z S u) := by
--   classical
--   revert σ hr
--   induction S with
--   | nil =>
--       intro σ hr
--       refine ⟨?pres, ?dst⟩
--       · intro t ht; simpa using (Option.some.inj hr).symm ▸ rfl
--       · intro u; aesop
--   | cons j js ih =>
--       intro σ hr
--       sorry


-- lemma regEqExpected_after_computeLocal_of_run
--     {k : ℕ} (hk : 0 < k) (z : ℤ) {σ₁ : State k}
--     (hrun : run? (computeLocal (k := k) hk z) (State.start_state (k := k)) = some σ₁) :
--     regEqExpected (k := k) (σ₁ (finZero hk)) (Point.int z) := by {
--       unfold computeLocal regEqExpected at *
--       simp_all
--       sorry
--     }





-- /-- Algebraic correctness of the `computeLocal` builder:
--     starting from `start_state`, after running `computeLocal hk z`
--     the destination register `0` equals the Vandermonde row for `z`. --/


-- lemma computeLocal_matches_row_start {k} (hk : 0 < k) (z : Int) :
--   ∃ σ₁, run? (computeLocal (k := k) hk z) (State.start_state (k := k)) = some σ₁
--       ∧ matchesAt_pointRow_state (k := k) σ₁ (finZero hk) (Point.int z) = true := by {
--         -- 1) Existence of a post-state
--         obtain ⟨σ₁, hrun⟩ := run_some_computeLocal (k := k) hk z (State.start_state (k := k))
--         -- 2) Show register `0` is exactly the Vandermonde row for `z`
--         --    i.e., `regEqExpected (σ₁ (finZero hk)) (.int z) = true`.
--         -- We discharge this by unfolding `regEqExpected` and reasoning componentwise
--         -- over `List.finRange k`. The key facts used by `simp` here are:
--         --   • `nonzeroFins hk` excludes `0` (so coordinate 0 stays 1),
--         --   • at start-state, register `j` is the basis vector `e_j`,
--         --   • `addScaled` into destination `0` adds (± 2^sh)·(basis j) componentwise,
--         --   • the mapped block for `z^j` sums to `z^j` at coordinate `j`,
--         --   • the fold accumulates those per-index contributions independently.
--         -- All of these are definitional in your `Basic` module and `simp` can use them.
--         have hrow :
--           regEqExpected (k := k) (σ₁ (finZero hk)) (Point.int z) = true := by
--              exact regEqExpected_after_computeLocal_of_run (k := k) hk z hrun

--           -- ...continue your proof, e.g.
--           -- simpa [regEqExpected, expectedRow, hP, computeLocal, finZero] using ...

--         exact ⟨σ₁, hrun, by simpa [matchesAt_pointRow_state] using hrow⟩
--   }



-- lemma cover_applyInverse {k} (hk : 0 < k) (p:Prog k) (σ : State k) (hp:PhaseProductCoverage p σ []) :
--   PhaseProductCoverage (apply_Op_inverse p) σ [] := by
--   cases hp with
--   |nil=>{
--     simp[apply_Op_inverse]
--     apply PhaseProductCoverageM.nil
--   }
--   |step_op=>{
--     aesop
--     sorry
--   }
--   |step_phase=>{
--     sorry
--   }



-- lemma cover_applyInverse_computeLocal_nil {k} (hk : 0 < k) (σ : State k) (z : Int) :
--   PhaseProductCoverage (apply_Op_inverse (computeLocal (k := k) hk z)) σ [] := by
--   apply cover_applyInverse hk
--   apply cover_computeLocal_nil




-- theorem genOpsWithProduct_PhaseProductCoverage
--   {k : Nat} (hk : 0 < k) (pts : List Point) :
--   PhaseProductCoverage (genOpsWithProduct hk pts) State.start_state pts := by
--     induction pts with
--     | nil=>{
--       unfold genOpsWithProduct
--       apply PhaseProductCoverageM.nil
--     }
--     | cons head tail ih=>{
--       unfold genOpsWithProduct
--       simp
--       change PhaseProductCoverage (opsForPointWithProduct hk head ++ (List.map (opsForPointWithProduct hk) tail).flatten) State.start_state ([head] ++ tail)
--       apply phaseProduct_coverage_check_append
--       {
--         sorry
--       }
--       {
--         simp[opsForPointWithProduct]
--         cases head with
--         |int x => {
--           simp
--           -- simp
--           -- apply phaseCoverage_bypass_NoPhase
--           -- apply PhaseProductCovergae_on_computeLocal
--           -- sorry
--           -- unfold PhaseProductCoverage
--           -- apply PhaseProductCoverageM.step_phase
--           have hbuild : PhaseProductCoverage (computeLocal (k := k) hk x) (State.start_state (k := k)) [] :=
--             cover_computeLocal_nil (k := k) hk (State.start_state (k := k)) x
--           -- 2) compute the mid-state and the matcher fact (one line, from your algebra lemma)
--           obtain ⟨σ₁, hrun₁, hmatch⟩ := computeLocal_matches_row_start (k := k) hk x

--           -- 3) the single marker consumes `[Point.int x]` at σ₁
--           have hphase :
--               PhaseProductCoverage ([valid_ops.phaseProduct (finZero hk)]) σ₁ [Point.int x] := by
--             refine PhaseProductCoverageM.step_phase
--               (M := matchesAt_pointRow_state (k := k))
--               (i := finZero hk) (ps := []) (σ := σ₁)
--               (pts := [Point.int x]) (pts' := []) ?erase ?tail
--             · -- erase the head because the matcher is true at this site
--               simpa [List.eraseFirstMatch?] using
--                 eraseFirstMatch?_head_true
--                   (fun pt => matchesAt_pointRow_state (k := k) σ₁ (finZero hk) pt)
--                   (Point.int x) [] hmatch
--             · simpa using PhaseProductCoverageM.nil (M := matchesAt_pointRow_state (k := k)) (σ := σ₁)
--           -- 4) coverage of the inverse suffix (no markers)
--           have huncompute : PhaseProductCoverage
--                   (apply_Op_inverse (computeLocal (k := k) hk x)) σ₁ [] :=
--             cover_applyInverse_computeLocal_nil (k := k) hk σ₁ x

--           -- 5) stitch: (build) ++ (phase) covers [] ++ [x] = [x]
--           have hprefix :
--               PhaseProductCoverage
--                 (computeLocal (k := k) hk x ++ [valid_ops.phaseProduct (finZero hk)])
--                 (State.start_state (k := k)) [Point.int x] :=
--             phaseProduct_coverage_check_append_general
--               (p := computeLocal (k := k) hk x)
--               (q := [valid_ops.phaseProduct (finZero hk)])
--               (σ := State.start_state (k := k)) (σret := σ₁)
--               (a := []) (b := [Point.int x])
--               (hp := hbuild) (hrun₁) (hphase)
--           -- 6) stitch: … ++ (uncompute) covers [x] ++ [] = [x]
--           simpa [List.append_assoc]
--             using phaseProduct_coverage_check_append_general
--               (p := computeLocal (k := k) hk x ++ [valid_ops.phaseProduct (finZero hk)])
--               (q := apply_Op_inverse (computeLocal (k := k) hk x))
--               (σ := State.start_state (k := k)) (σret := σ₁)
--               (a := [Point.int x]) (b := [])
--               (hp := hprefix) (by simp[run?_append,hrun₁,applyOp?])
--               (huncompute)
--         }
--         |inf => {
--           simp
--           sorry
--         }
--       }
--       {
--         unfold genOpsWithProduct at ih
--         simp at ih
--         apply ih
--       }
--     }
