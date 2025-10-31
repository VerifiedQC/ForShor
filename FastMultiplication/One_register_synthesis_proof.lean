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


lemma phaseProduct_coverage_check_append_general
  {k : ℕ} (p q : Prog k) (σ : State k) (a b : List Point)
  (hp : PhaseProductCoverage p σ a) :
  ∀ (σret : State k),
    run? p σ = some σret →
    PhaseProductCoverage q σret b →
    PhaseProductCoverage (p ++ q) σ (a ++ b) := by {
      let M := matchesAt_pointRow_state (k := k)
      revert q b
      refine
        (show ∀ {p σ a}, PhaseProductCoverage p σ a →
                ∀ (q : Prog k) (b : List Point),
                  ∀ (σret : State k),
                    run? p σ = some σret →
                    PhaseProductCoverage q σret b →
                    PhaseProductCoverage (p ++ q) σ (a ++ b) from
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
            (M := M) (op := op) (ps := ps ++ q) (σ := σ) (τ := τ) (pts := a ++ b)
            (by simpa [applyOp?] using hstep) ?_
          simpa [List.cons_append] using ih q b σret hrun_ps hq
      | @step_phase i ps σ a a' hcons hrest ih =>
          intro q b σret hrun hq
          -- Lift the consumption from `a` to `a ++ b`.
          have hcons' :
            List.eraseFirstMatch? (fun pt => M σ i pt) (a ++ b) = some (a' ++ b) :=
            List.eraseFirstMatch?_append_hit _ hcons
          -- Push `run?` through the phase (no-op).
          have hrun_ps : run? ps σ = some σret := by
            simpa [run?, applyOp?] using hrun
          -- Phase step then recurse.
          refine PhaseProductCoverageM.step_phase
            (M := M) (i := i) (ps := ps ++ q) (σ := σ)
            (pts := a ++ b) (pts' := a' ++ b) hcons' ?_
          simpa [List.cons_append] using ih q b σret hrun_ps hq
    }

/-- “Returns to σ” corollary with the same hypothesis order as your goal. -/
lemma phaseProduct_coverage_check_append
  {k : ℕ} (p q : Prog k) (σ : State k) (a b : List Point)
  (hret : run? p σ = some σ)
  (hp   : PhaseProductCoverage p σ a)
  (hq   : PhaseProductCoverage q σ b) :
  PhaseProductCoverage (p ++ q) σ (a ++ b) :=
  phaseProduct_coverage_check_append_general p q σ a b hp σ hret hq




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
lemma cover_addScaled_nil {k} (σ : State k) (dst src : Fin k) (neg' : Bool) (sh : ℕ) :
  PhaseProductCoverage [valid_ops.addScaled dst src (negSrc := neg') sh] σ [] := by
  refine PhaseProductCoverageM.step_op
    (M := matchesAt_pointRow_state (k := k))
    (op := valid_ops.addScaled dst src (negSrc := neg') sh)
    (ps := []) (σ := σ)
    (τ := State.addScaledReg σ dst src (negSrc := neg') sh)
    (pts := []) ?hstep ?tail
  · simp [applyOp?]
  · simpa using PhaseProductCoverageM.nil (M := matchesAt_pointRow_state (k := k)) (σ := _)

/-- A mapped list of `(neg,shift)` pairs to `addScaled` ops consumes no points. -/
lemma cover_map_pairToOp_nil {k} (σ : State k) (dst src : Fin k) (pairs : List (Bool × Nat)) :
  PhaseProductCoverage (pairs.map (pairToOp (k := k) dst src)) σ [] := by
  classical
  revert σ
  induction pairs with
  | nil =>
      intro σ; apply PhaseProductCoverageM.nil
  | cons p ps ih =>
      intro σ
      refine
        PhaseProductCoverageM.step_op
          (M := matchesAt_pointRow_state (k := k))
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
  (hstep : applyOp? (k := k) σ op = some τ)
  (hrest : PhaseProductCoverage (ps ++ q) τ []) :
  PhaseProductCoverage ((op :: ps) ++ q) σ [] := by
  refine PhaseProductCoverageM.step_op
    (M := matchesAt_pointRow_state (k := k))
    (op := op) (ps := ps ++ q) (σ := σ) (τ := τ) (pts := [])
    (by simpa [applyOp?] using hstep) ?_
  -- `ps` appended under the cons:
  simpa [List.cons_append] using hrest



lemma phaseCoverage_append_nil
  {k} (p q : Prog k) {σ σ₂ : State k}
  (hp  : PhaseProductCoverage p σ [])
  (hr  : run? p σ = some σ₂)
  (hq  : PhaseProductCoverage q σ₂ []) :
  PhaseProductCoverage (p ++ q) σ [] := by
  have aux :
    ∀ {p σ pts}, PhaseProductCoverage p σ pts → pts = [] →
      ∀ (q : Prog k) (σ₂ : State k),
        run? p σ = some σ₂ →
        PhaseProductCoverage q σ₂ [] →
        PhaseProductCoverage (p ++ q) σ [] := by
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
          PhaseProductCoverage (ps ++ q) τ [] := by
          aesop
        -- rebuild ((op :: ps) ++ q)
        refine PhaseProductCoverageM.step_op
          (M := matchesAt_pointRow_state (k := k))
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
  PhaseProductCoverage (computeLocal (k := k) hk z) σ [] := by
  unfold computeLocal
  set dst := finZero hk
  -- We prove a paired property across the fold:
  --   (COV) for all σ, the accumulated program covers []
  --   (RUN) for all σ, run? succeeds (exists σ')
  have main :
    ∀ (xs : List (Fin k)) (acc : Prog k),
      (∀ σ, PhaseProductCoverage acc σ []) →
      (∀ σ, ∃ σ', run? acc σ = some σ') →
      (∀ σ, PhaseProductCoverage (xs.foldl (step (k := k) hk z) acc) σ [])
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
                ((signedPow2Decomp (z ^ (j : Nat))).map (pairToOp (k := k) dst j)) σ [] :=
              by intro σ0; simpa using cover_map_pairToOp_nil (k := k) σ0 dst j _
            -- COV for `acc ++ block` using append lemma
            have Hcov' :
              ∀ σ, PhaseProductCoverage
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
  have base_cov : ∀ σ, PhaseProductCoverage ([] : Prog k) σ [] :=
    by intro σ0; simpa using PhaseProductCoverageM.nil (M := matchesAt_pointRow_state (k := k)) (σ := σ0)
  have base_run : ∀ σ, ∃ σ', run? ([] : Prog k) σ = some σ' :=
    by intro σ0; exact ⟨σ0, by simp [run?]⟩
  -- Apply the fold result to `nonzeroFins hk` and your given `σ`.
  have cov_all := (main (nonzeroFins (k := k) hk) [] base_cov base_run).1
  unfold step at cov_all
  simp at cov_all
  simp
  unfold dst
  simp[cov_all]


/-- Algebraic correctness of the `computeLocal` builder:
    starting from `start_state`, after running `computeLocal hk z`
    the destination register `0` equals the Vandermonde row for `z`. --/
lemma computeLocal_matches_row_start {k} (hk : 0 < k) (z : Int) :
  ∃ σ₁, run? (computeLocal (k := k) hk z) (State.start_state (k := k)) = some σ₁
      ∧ matchesAt_pointRow_state (k := k) σ₁ (finZero hk) (Point.int z) = true := by {
        sorry
  }



lemma cover_applyInverse {k} (hk : 0 < k) (p:Prog k) (σ : State k) (hp:PhaseProductCoverage p σ []) :
  PhaseProductCoverage (apply_Op_inverse p) σ [] := by
  unfold apply_Op_inverse
  sorry


lemma cover_applyInverse_computeLocal_nil {k} (hk : 0 < k) (σ : State k) (z : Int) :
  PhaseProductCoverage (apply_Op_inverse (computeLocal (k := k) hk z)) σ [] := by
  apply cover_applyInverse hk
  apply cover_computeLocal_nil




theorem genOpsWithProduct_PhaseProductCoverage
  {k : Nat} (hk : 0 < k) (pts : List Point) :
  PhaseProductCoverage (genOpsWithProduct hk pts) State.start_state pts := by
    induction pts with
    | nil=>{
      unfold genOpsWithProduct
      simp
      apply PhaseProductCoverageM.nil
    }
    | cons head tail ih=>{
      unfold genOpsWithProduct
      simp
      change PhaseProductCoverage (opsForPointWithProduct hk head ++ (List.map (opsForPointWithProduct hk) tail).flatten) State.start_state ([head] ++ tail)
      apply phaseProduct_coverage_check_append
      {
        sorry
      }
      {
        simp[opsForPointWithProduct]
        cases head with
        |int x => {
          simp
          -- simp
          -- apply phaseCoverage_bypass_NoPhase
          -- apply PhaseProductCovergae_on_computeLocal
          -- sorry
          -- unfold PhaseProductCoverage
          -- apply PhaseProductCoverageM.step_phase
          have hbuild : PhaseProductCoverage (computeLocal (k := k) hk x) (State.start_state (k := k)) [] :=
            cover_computeLocal_nil (k := k) hk (State.start_state (k := k)) x
          -- 2) compute the mid-state and the matcher fact (one line, from your algebra lemma)
          obtain ⟨σ₁, hrun₁, hmatch⟩ := computeLocal_matches_row_start (k := k) hk x

          -- 3) the single marker consumes `[Point.int x]` at σ₁
          have hphase :
              PhaseProductCoverage ([valid_ops.phaseProduct (finZero hk)]) σ₁ [Point.int x] := by
            refine PhaseProductCoverageM.step_phase
              (M := matchesAt_pointRow_state (k := k))
              (i := finZero hk) (ps := []) (σ := σ₁)
              (pts := [Point.int x]) (pts' := []) ?erase ?tail
            · -- erase the head because the matcher is true at this site
              simpa [List.eraseFirstMatch?] using
                eraseFirstMatch?_head_true
                  (fun pt => matchesAt_pointRow_state (k := k) σ₁ (finZero hk) pt)
                  (Point.int x) [] hmatch
            · simpa using PhaseProductCoverageM.nil (M := matchesAt_pointRow_state (k := k)) (σ := σ₁)
          -- 4) coverage of the inverse suffix (no markers)
          have huncompute : PhaseProductCoverage
                  (apply_Op_inverse (computeLocal (k := k) hk x)) σ₁ [] :=
            cover_applyInverse_computeLocal_nil (k := k) hk σ₁ x

          -- 5) stitch: (build) ++ (phase) covers [] ++ [x] = [x]
          have hprefix :
              PhaseProductCoverage
                (computeLocal (k := k) hk x ++ [valid_ops.phaseProduct (finZero hk)])
                (State.start_state (k := k)) [Point.int x] :=
            phaseProduct_coverage_check_append_general
              (p := computeLocal (k := k) hk x)
              (q := [valid_ops.phaseProduct (finZero hk)])
              (σ := State.start_state (k := k)) (σret := σ₁)
              (a := []) (b := [Point.int x])
              (hp := hbuild) (hrun₁) (hphase)
          -- 6) stitch: … ++ (uncompute) covers [x] ++ [] = [x]
          simpa [List.append_assoc]
            using phaseProduct_coverage_check_append_general
              (p := computeLocal (k := k) hk x ++ [valid_ops.phaseProduct (finZero hk)])
              (q := apply_Op_inverse (computeLocal (k := k) hk x))
              (σ := State.start_state (k := k)) (σret := σ₁)
              (a := [Point.int x]) (b := [])
              (hp := hprefix) (by simp[run?_append,hrun₁,applyOp?])
              (huncompute)
        }
        |inf => {
          simp
          sorry
        }
      }
      {
        unfold genOpsWithProduct at ih
        simp at ih
        apply ih
      }
    }
