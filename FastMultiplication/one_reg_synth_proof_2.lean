import FastMultiplication.One_register_synthesis_proof

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


/-- A single `addScaled` always succeeds and consumes no points. -/
lemma cover_addScaled_nil {k} (hk:k>0) (σ : State k) (dst src : Fin k) (neg' : Bool) (sh : ℕ) :
  PhaseProductCoverage hk [valid_ops.addScaled dst src (negSrc := neg') sh] σ [] := by
  refine PhaseProductCoverageM.step_op
    (M := matchesAt_pointRow_state hk (k := k))
    (op := valid_ops.addScaled dst src (negSrc := neg') sh)
    (ps := []) (σ := σ)
    (τ := State.addScaledReg σ dst src (negSrc := neg') sh)
    (pts := []) ?hstep ?tail
  · simp [applyOp?]
  · simpa using PhaseProductCoverageM.nil (M := matchesAt_pointRow_state hk (k := k)) (σ := _)

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
    (M := matchesAt_pointRow_state hk (k := k))
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
          (M := matchesAt_pointRow_state hk (k := k))
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
/-- “IsAddScaled” = the op is of the form `addScaled _ _ _ _`. -/

-- private def IsAddScaled {k : ℕ} (op : valid_ops k) : Prop :=
--   ∃ (dst src : Fin k) (neg' : Bool) (sh : Nat),
--     op = valid_ops.addScaled dst src (negSrc := neg') sh



lemma cover_computeLocal2_nil {k} (hk : 0 < k) (σ : State k) (z : Int) :
  PhaseProductCoverage hk (computeLocal2 (k := k) hk z) σ [] := by {
    rw[computeLocal_eq]
    apply cover_computeLocal_nil
  }



/-- Existence: `computeLocal hk z` never fails; it returns *some* state from any input. -/
lemma run_some_computeLocal2 {k : ℕ} (hk : 0 < k) (z : Int) (σ : State k) :
  ∃ σ', run? (computeLocal2 (k := k) hk z) σ = some σ' := by {
    rw[computeLocal_eq]
    apply run_some_computeLocal
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

private def sumPow2 (ls : List Nat) : Int :=
  ls.foldl (fun acc s => acc + (2 : Int) ^ s) 0

-- /-- Key arithmetic identity used by `shiftsOfAux` recursion:
--     the sum of powers-of-two at offsets `sh` enumerated by `shiftsOfAux`
--     equals `2^sh * n`. -/
-- -- lemma shiftsOfAux_sumPow2 :
-- --   ∀ (n sh : Nat), sumPow2 (shiftsOfAux n sh) = ((2 : Int) ^ sh) * (n : Int)
-- -- | 0,      sh => by
-- --   simp [shiftsOfAux, sumPow2]
-- -- | (n+1),  sh => by
-- --   -- matches the recursive definition in your file
-- --   simp [shiftsOfAux, sumPow2] -- splits on `Nat.bodd (n+1)`
-- --   have ih := shiftsOfAux_sumPow2 ((n+1)/2) (sh+1)
-- --   sorry
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

/-- Contribution at coordinate `u` from a list of source registers. -/
def contrib {k : Nat} (z : Int) : List (Fin k) → (Fin k) → Int
| [],      _ => 0
| j :: js, u => z ^ (j : Nat) * (State.start_state (k := k) j u) + contrib z js u


@[simp] lemma addScaled_other {k}
  (σ : State k) (dst src : Fin k) (b : Bool) (sh : ℕ) {t : Fin k}
  (hne : t ≠ dst) :
  (State.addScaledReg σ dst src (negSrc := b) sh) t = σ t := by
  simp [State.addScaledReg, hne]

lemma addScaled_dst {k}
  (σ : State k) (dst src : Fin k) (b : Bool) (sh : ℕ) (u : Fin k) :
  (State.addScaledReg σ dst src (negSrc := b) sh) dst u
    = σ dst u + ((if b then (-1 : ℤ) else 1) * σ src u * (2 : ℤ)^sh) := by
  simp [State.addScaledReg]

lemma run_addConstAux_preserve_non_dst
  {k : ℕ} (dst src : Fin k) (neg' : Bool) :
  ∀ n sh {σ τ : State k},
    run? (k := k) (addConstAux (k := k) dst src neg' n sh) σ = some τ →
    ∀ t, t ≠ dst → τ t = σ t := by
  intro n
  refine Nat.strong_induction_on n ?step
  intro n ih sh σ τ hrun t hne
  cases n with
  | zero =>
      simp[addConstAux] at hrun
      rw[hrun]
  | succ m =>
      -- Definition of addConstAux at n = m+1
      by_cases hb : Nat.bodd (m+1)
      ·
        -- Head present: one addScaled at `sh`, then tail at (sh+1)
        -- Peel the head and name the post-state
        have htail :
          run? (k := k)
                (addConstAux (k := k) dst src neg' ((m+1)/2) (sh+1))
                (State.addScaledReg σ dst src (negSrc := neg') sh)
            = some τ := by
          -- Unroll run? once using the head step
          have hb:m.bodd = false:=by aesop
          simp [addConstAux, hb, applyOp?] at hrun
          simp[hrun]

        -- Strong IH applies to strictly smaller index ((m+1)/2) < (m+1)
        have hlt : ((m+1)/2) < (m+1) :=
          Nat.div_lt_self (Nat.succ_pos _) (by decide)
        have ihTail :
          ∀ t, t ≠ dst →
            τ t
              = (State.addScaledReg σ dst src (negSrc := neg') sh) t :=
          by
            intro t' hne'
            -- tail preserves non-dst by IH
            exact ih ((m+1)/2) hlt (sh+1) htail t' hne'
        -- Head preserves non-dst registers by definition of addScaledReg
        have headPres :
          (State.addScaledReg σ dst src (negSrc := neg') sh) t = σ t := by
          simp [State.addScaledReg, hne]
        -- Combine: τ t = (post-head) t = σ t
        simpa [headPres] using ihTail t hne
      ·
        -- Even case: no head, only tail at (sh+1)
        have htail :
          run? (k := k)
              (addConstAux (k := k) dst src neg' ((m+1)/2) (sh+1)) σ
            = some τ := by
          have hb:m.bodd = true:=by aesop
          simp [addConstAux, hb] at hrun
          simp[hrun]
        have hlt : ((m+1)/2) < (m+1) :=
          Nat.div_lt_self (Nat.succ_pos _) (by decide)
        -- Directly apply IH to the tail
        exact ih ((m+1)/2) hlt (sh+1) htail t hne

lemma run_addConstFrom_effect_1
  {k : ℕ} (dst src : Fin k) (c : Int) {σ τ : State k}
    (hr : run? (addConstFrom (k := k) dst src c) σ = some τ) :
  (∀ t, t ≠ dst → τ t = σ t) := by
  classical
  by_cases hc : c = 0
  · -- trivial: program is []
    subst hc
    simp [addConstFrom] at hr
    simp[hr]
  ·
    -- nonzero: `addConstFrom` delegates to `addConstAux` with `n = natAbs c`, `sh = 0`
    have := run_addConstAux_preserve_non_dst (k := k) dst src (c < 0)
              (n := Int.natAbs c) (sh := 0) (σ := σ) (τ := τ)
    -- the `run?` equation matches by unfolding `addConstFrom`
    simp[addConstFrom,hc] at hr
    simp[hr] at this
    simp
    apply this

-- lemma run_addConstAux_effect_dst
--   {k : ℕ} (dst src : Fin k) (neg' : Bool) (hsd : src ≠ dst) :
--   ∀ n sh {σ τ : State k},
--     run? (k := k) (addConstAux (k := k) dst src neg' n sh) σ = some τ →
--     ∀ u, τ dst u
--             = σ dst u
--               + ((if neg' then (-1 : ℤ) else 1) * (2 : ℤ)^sh * (n : ℤ)) * σ src u
-- := by sorry

-- lemma run_addConstFrom_effect_2
--     {k : ℕ} (dst src : Fin k) (c : Int) {σ τ : State k}
--     (hr : run? (addConstFrom (k := k) dst src c) σ = some τ) (hsd:src≠dst):
--   (∀ u, τ dst u = σ dst u + c * σ src u) := by
--   by_cases hc : c = 0
--   · -- trivial: program is []
--     subst hc
--     simp [addConstFrom] at hr
--     simp[hr]
--   ·
--     have h :=
--       run_addConstAux_effect_dst (k := k) dst src (c < 0) hsd
--         (n := Int.natAbs c) (sh := 0) (σ := σ) (τ := τ)
--     have h' := h (by simpa [addConstFrom, hc] using hr)
--     -- (if c<0 then -1 else 1) · 2^0 · natAbs c  =  c
--     have sgn_abs :
--       ((if c < 0 then (-1 : ℤ) else 1) * (2 : ℤ)^0 * (Int.ofNat (Int.natAbs c)))
--         = c := by
--       -- `2^0 = 1`; the remaining identity is standard: sign·natAbs = c
--       have : (2 : ℤ)^0 = 1 := by simp
--       -- `Int.mul_natAbs_sign c : (if c<0 then -1 else 1) * (Int.ofNat (Int.natAbs c)) = c`
--       aesop
--       sorry
--     intro u
--     have:= h' u
--     simp[pow_zero] at this
--     sorry


-- lemma run_addConstFrom_effect
--     {k : ℕ} (dst src : Fin k) (c : Int) {σ τ : State k}
--     (hr : run? (addConstFrom (k := k) dst src c) σ = some τ) (hsd:src≠dst):
--   (∀ t, t ≠ dst → τ t = σ t)
--   ∧ (∀ u, τ dst u = σ dst u + c * σ src u) := by
--   have := run_addConstFrom_effect_1 dst src c hr
--   apply And.intro
--   apply this
--   apply run_addConstFrom_effect_2 dst src c hr hsd


-- lemma computeLocalAux_implies_addConstFrom
--   (hk:k>0)
--   (hr:run? (computeLocalAux hk z s) State.start_state = some σ):
--   run? (addConstFrom (finZero hk) j z) State.start_state = some σ:=by {
--     induction s with
--     |nil=>{
--       simp_all[computeLocalAux,addConstFrom]
--       aesop
--     }
--     |cons head tail ih=>{}
--   }

lemma run_computeLocalAux_preserve_non_dst
  {k : ℕ} (hk : 0 < k) (z : ℤ) :
  ∀ (S : List (Fin k)) {σ σ' : State k},
    run? (computeLocalAux (k := k) hk z S) σ = some σ' →
    (∀ t, t ≠ finZero (k := k) hk → σ t = State.start_state (k := k) t) →
    (∀ t, t ≠ finZero (k := k) hk → σ' t = State.start_state (k := k) t)
:= by
  intro S
  induction S with
  | nil =>
      intro σ σ' hrun hσ t ht
      simp [computeLocalAux] at hrun
      subst hrun
      exact hσ t ht
  | cons j js ih =>
      intro σ σ' hrun hσ
      have def2 :
        computeLocalAux (k := k) hk z (j :: js)
          = addConstFrom (k := k) (finZero (k := k) hk) j (z ^ (j : Nat))
              ++ computeLocalAux (k := k) hk z js := by
        simp [computeLocalAux]

      have hrun' :
        run? (addConstFrom (k := k) (finZero (k := k) hk) j (z ^ (j : Nat))
                ++ computeLocalAux (k := k) hk z js) σ
          = some σ' := by
        simpa [def2] using hrun

      rcases run?_append_some
        (p := addConstFrom (k := k) (finZero (k := k) hk) j (z ^ (j : Nat)))
        (q := computeLocalAux (k := k) hk z js)
        (σ := σ) hrun' with ⟨τ, hhead, htail⟩

      -- Head block: addConstFrom only touches dst, so non-dst are preserved.
      have hτ :
        ∀ t, t ≠ finZero (k := k) hk →
          τ t = State.start_state (k := k) t := by
        intro t ht
        -- First: τ t = σ t for t ≠ dst
        have hpres :=
          run_addConstFrom_effect_1
            (dst := finZero (k := k) hk)
            (src := j)
            (c := z ^ (j : Nat))
            (σ := σ) (τ := τ) hhead t ht
        -- Then use the hypothesis about σ
        simpa [hσ t ht] using hpres

      -- Tail: apply IH from τ to σ'
      intro t ht
      exact ih (σ := τ) (σ' := σ') htail hτ t ht

lemma run_computeLocalAux_from_start_1
  {k : ℕ} (hk : 0 < k) (z : ℤ)
  : ∀ (S : List (Fin k)) {σ : State k},
      run? (computeLocalAux (k := k) hk z S) (State.start_state (k := k)) = some σ →
      (∀ t, t ≠ finZero hk → σ t = State.start_state (k := k) t)
    :=by {
      intro S σ hrun t ht
      -- apply the general lemma with σ = start_state, whose non-dst property is trivial
      have h :=
        run_computeLocalAux_preserve_non_dst (k := k) hk z
          S (σ := State.start_state (k := k)) (σ' := σ)
          hrun
          (by intro t _; rfl)
      exact h t ht
    }

open Operations

lemma run_append_exists
  {k : ℕ} {p q : Prog k} {σ σ₂ : State k}
  (h : run? (p ++ q) σ = some σ₂) :
  ∃ τ, run? p σ = some τ ∧ run? q τ = some σ₂ := by
  revert σ σ₂ h
  induction p with
  | nil =>
      intro σ σ₂ h
      -- p = [], so p ++ q = q
      simp at h
      -- choose τ = σ
      exact ⟨σ, by simp[run?], h⟩
  | cons op ps ih =>
      intro σ σ₂ h
      -- p = op :: ps, so p ++ q = op :: (ps ++ q)
      -- inspect the first step
      cases hstep : applyOp? (k := k) σ op with
      | none =>
          -- then run? (op :: ps ++ q) σ = none, contradicting h = some σ₂
          simp [hstep, List.cons_append] at h
      | some τ =>
          -- from h we get success on ps ++ q starting from τ
          have h' : run? (ps ++ q) τ = some σ₂ := by
            simp [hstep, List.cons_append] at h
            exact h
          -- apply IH to ps, q, starting from τ
          rcases ih (σ := τ) (σ₂ := σ₂) h' with ⟨τ', hps, hq⟩
          -- reconstruct run? (op :: ps) σ = some τ'
          refine ⟨τ', ?hp, hq⟩
          simp [run?, hstep, hps]


lemma run_append_split {k} {p q : Prog k} {σ σ' : State k}
  (h : run? (p ++ q) σ = some σ') :
  ∃ τ, run? p σ = some τ ∧ run? q τ = some σ' := by
  revert σ σ'
  induction p with
  | nil =>
      intro σ σ' h
      simp at h
      exact ⟨σ, rfl, h⟩
  | cons op ps ih =>
      intro σ σ' h
      simp [List.cons_append] at h
      aesop




def AllNe {k} (dst : Fin k) : List (Fin k) → Prop
| []      => True
| j :: js => j ≠ dst ∧ AllNe dst js

lemma nonzeroFins_allNe {k} (hk : 0 < k) :
  AllNe (finZero (k := k) hk) (nonzeroFins (k := k) hk) := by
  classical
  unfold nonzeroFins
  -- filtered by (· ≠ finZero hk)
  unfold AllNe
  sorry



/-- Semantics of `computeLocalAux hk z` as a relational big-step. -/
inductive ExecCL {k : ℕ} (hk : 0 < k) (z : ℤ) :
    List (Fin k) → State k → State k → Prop
| nil {σ} :
    ExecCL hk z [] σ σ
| cons {j js σ σ₁ σ₂} :
    run? (addConstFrom (finZero hk) j (z ^ (j : ℕ))) σ = some σ₁ →
    ExecCL hk z js σ₁ σ₂ →
    ExecCL hk z (j :: js) σ σ₂

/-- Semantics of `computeLocalAux hk z` as a relational big-step. -/
inductive ExecCL_start {k : ℕ} (hk : 0 < k) (z : ℤ) :
    List (Fin k) → State k → Prop
| nil :
    ExecCL_start hk z [] State.start_state
| cons {j js σ₁ σ₂} :
    run? (addConstFrom (finZero hk) j (z ^ (j : ℕ))) State.start_state = some σ₁ →
    ExecCL hk z js σ₁ σ₂ →
    ExecCL_start hk z (j :: js) σ₂

lemma ExecCL_implies_ExecCL_start
    {k : ℕ} (hk : 0 < k) (z : ℤ) :
    ∀ {S : List (Fin k)} {σ : State k},
       ExecCL (k := k) hk z S (State.start_state) σ →
      AllNe (finZero (k := k) hk) S →
      ExecCL_start (k := k) hk z S σ:=by
  intro S σ h
  cases h with
  | nil =>
      simp[AllNe]
      apply ExecCL_start.nil
  | cons hhead htail =>
      -- computeLocalAux hk z (j :: js) = addConstFrom … ++ computeLocalAux hk z js
      intro a
      apply ExecCL_start.cons
      rw[hhead]
      apply htail




lemma ExecCL_run {z}
  (hk: 0 < k)
  (h : ExecCL hk z S σ₀ σ) :
  run? (computeLocalAux hk z S) σ₀ = some σ := by
  induction h with
  | nil =>
      simp [computeLocalAux]
  | cons hhead htail ih =>
      -- computeLocalAux hk z (j :: js) = addConstFrom … ++ computeLocalAux hk z js
      simp [computeLocalAux]
      simp[run?_append]
      simp_all


/-- General form: starting from arbitrary σ₀. -/
lemma run_ExecCL_aux
    {k : ℕ} (hk : 0 < k) (z : ℤ) :
    ∀ {S : List (Fin k)} {σ₀ σ : State k},
      run? (computeLocalAux hk z S) σ₀ = some σ →
      AllNe (finZero (k := k) hk) S →
      ExecCL (k := k) hk z S σ₀ σ
  | [], σ₀, σ, hrun, _ => by
      -- computeLocalAux hk z [] = []
      -- run? [] σ₀ = some σ ⇒ σ = σ₀
      have hσ : σ₀ = σ := by
        simpa [computeLocalAux, run?] using hrun
      subst hσ
      exact ExecCL.nil
  | j :: js, σ₀, σ, hrun, hs => by
      -- AllNe dst (j :: js) = (j ≠ dst ∧ AllNe dst js)
      rcases hs with ⟨_hj_ne, hs_tail⟩
      -- unfold computeLocalAux on cons
      have hdecomp :
        run? (addConstFrom (finZero (k := k) hk) j (z ^ (j : ℕ))
                ++ computeLocalAux hk z js) σ₀ = some σ := by
        simpa [computeLocalAux] using hrun
      -- split run over the append
      have := run?_append_some
        (p := addConstFrom (finZero (k := k) hk) j (z ^ (j : ℕ)))
        (q := computeLocalAux hk z js)
        (σ := σ₀) (τ := σ) hdecomp
      rcases this with ⟨σ₁, hhead, htail⟩
      -- IH on the tail js starting from σ₁
      have hExec_tail :
        ExecCL (k := k) hk z js σ₁ σ :=
        run_ExecCL_aux (hk := hk) (z := z)
          (S := js) (σ₀ := σ₁) (σ := σ) htail hs_tail
      -- stitch head + tail
      exact ExecCL.cons (hk := hk) (z := z)
        (j := j) (js := js) hhead hExec_tail


lemma run_ExecCL {z}
  (hk: 0 < k)
  (hrun : run? (computeLocalAux hk z S) State.start_state = some σ)
  (hs : AllNe (finZero hk) S) :
  ExecCL hk z S State.start_state σ := by
  have :=run_ExecCL_aux (hk := hk) (z := z)
    (S := S) (σ₀ := State.start_state) (σ := σ) hrun hs
  simp[this]




lemma addConstFrom_effect
    {k : ℕ} (hk : 0 < k) (z : ℤ)
    (j : Fin k)
    {σ₀ σ₁ : State k}
    (h :
      run? (addConstFrom (finZero hk) j (z ^ (j : ℕ))) σ₀ = some σ₁) :
    (∀ t ≠ finZero hk, σ₁ t = σ₀ t) ∧
    (∀ u : Fin k,
      σ₁ (finZero hk) u
        = σ₀ (finZero hk) u + z ^ (j : ℕ) * σ₀ j u) :=
by sorry


def contribFrom (σ₀ : State k) (z : ℤ) :
    List (Fin k) → Fin k → ℤ
| [],      _ => 0
| j :: js, u => z^(j : ℕ) * σ₀ j u + contribFrom σ₀ z js u


lemma helper1
(hσ₀ : ∀ (t : Fin k), t ≠ finZero hk → σ₀ t = State.start_state t)
(hhead : run? (addConstFrom (finZero hk) j (z ^ j.val)) σ₀ = some σ₁)
:(∀ (t : Fin k), ¬t = finZero hk → σ₁ t = State.start_state t):=by {
  intro t ht
  have h_preserves : σ₁ t = σ₀ t := by
    apply run_addConstFrom_effect_1
    · exact hhead
    · exact ht
  rw [h_preserves]
  exact hσ₀ t ht
}

lemma contribFrom_eq_of_regs_eq
    {k : ℕ} {σ₀ σ₁ : State k} {z : ℤ} {s : List (Fin k)} {u : Fin k}
    (h_regs : ∀ j ∈ s, σ₁ j u = σ₀ j u) :
    contribFrom σ₁ z s u = contribFrom σ₀ z s u := by
    induction s with
  | nil =>
      simp [contribFrom]
  | cons j js ih =>
      simp [contribFrom]
      have h_j : σ₁ j u = σ₀ j u := by
        apply h_regs
        simp
      have h_js : contribFrom σ₁ z js u = contribFrom σ₀ z js u := by
        apply ih
        intro j' hj'
        apply h_regs
        simp [hj']
      rw [h_j, h_js]

/--
If a list `s` is certified by `AllNe` to not contain `dst`, then any
element `j` that is a member of `s` cannot be equal to `dst`.
-/
lemma AllNe_implies_mem_ne {k} {dst : Fin k} {s : List (Fin k)}
    (hAll : AllNe dst s) :
    ∀ j ∈ s, j ≠ dst := by
  -- We proceed by induction on the list 's'
  induction s with
  | nil =>
      simp
  | cons j' js ih =>
      rcases hAll with ⟨hj'_ne, hjs_allne⟩
      intro j hj_mem
      by_cases hj:j=j'
      subst hj
      simp_all only [ne_eq, forall_const, mem_cons, true_or, not_false_eq_true]
      simp_all only [ne_eq, forall_const, mem_cons, false_or, not_false_eq_true]

lemma ExecCL_contrib_inductive_step_equality
    {k : ℕ} (hk : 0 < k) (z : ℤ)
    (j : Fin k) (js : List (Fin k))
    {σ₀ σ₁ : State k} (u : Fin k)
    (hhead : run? (addConstFrom (finZero hk) j (z ^ (j : ℕ))) σ₀ = some σ₁)
    (hs_js : AllNe (finZero hk) js) :
    σ₁ (finZero hk) u + contribFrom σ₁ z js u = σ₀ (finZero hk) u + contribFrom σ₀ z (j :: js) u := by

  have h_effect : (∀ t ≠ finZero hk, σ₁ t = σ₀ t) ∧
                  (∀ u, σ₁ (finZero hk) u = σ₀ (finZero hk) u + z ^ (j : ℕ) * σ₀ j u) := by
    exact addConstFrom_effect (k := k) hk z j hhead

  rcases h_effect with ⟨h_pres, h_update⟩
  simp only [contribFrom]
  rw [h_update]
  have h_contrib_eq : contribFrom σ₁ z js u = contribFrom σ₀ z js u := by
    apply contribFrom_eq_of_regs_eq
    intro j' hj'
    have hj'_ne : j' ≠ finZero hk := by
      apply AllNe_implies_mem_ne hs_js
      assumption
    rw [h_pres j' hj'_ne]
  rw [h_contrib_eq]
  ring


lemma ExecCL_contrib
    {k : ℕ} (hk : 0 < k) (z : ℤ)
    {s : List (Fin k)} {σ₀ σ : State k}
    (hs : AllNe (finZero hk) s)
    (hσ₀ : ∀ t ≠ finZero hk, σ₀ t = State.start_state t)
    (hExec : ExecCL hk z s σ₀ σ) :
    ∀ u, σ (finZero hk) u = σ₀ (finZero hk) u + contribFrom σ₀ z s u := by
  -- we want hs, hσ₀ as parameters to the IH, so revert them
  revert hs hσ₀
  -- induct on the ExecCL derivation
  induction hExec with
  | nil =>
      intro _hs _hσ₀ u
      simp [contribFrom]
  | @cons j js σ₀ σ₁ σ hhead htail ih =>
      intro hs hσ₀ u
      -- Split AllNe for (j :: js)
      have dst := finZero hk
      rcases hs with ⟨hj_ne, hs_js⟩
      simp_all only [ne_eq, forall_const]
      have h1:=helper1 hσ₀ hhead
      have:=ih h1 u
      simp[this]
      have := ExecCL_contrib_inductive_step_equality hk z j js u hhead hs_js
      assumption




@[simp] lemma contribFrom_start_eq_contrib
    {k : ℕ} (z : ℤ) (s : List (Fin k)) (u : Fin k) :
    contribFrom (State.start_state (k := k)) z s u
      = contrib z s u := by
  induction s with
  | nil =>
      simp [contribFrom, contrib]
  | cons j js ih =>
      simp [contribFrom, contrib, ih]


lemma run_computeLocalAux_from_start
  {k : ℕ} (hk : 0 < k) (z : ℤ)
  : ∀ (s : List (Fin k)) (_ : AllNe (finZero (k := k) hk) s) {σ : State k},
      run? (computeLocalAux (k := k) hk z s) (State.start_state (k := k)) = some σ →
      (∀ t, t ≠ finZero hk → σ t = State.start_state (k := k) t)
      ∧ (∀ u, σ (finZero hk) u =
              State.start_state (k := k) (finZero hk) u + contrib (k := k) z s u):=by
intro s hs σ hrun
have:=run_computeLocalAux_from_start_1 hk z s (σ:=σ) hrun
apply And.intro
assumption
intro u
have hExecCL:=run_ExecCL hk hrun hs
have := ExecCL_contrib hk z hs (σ₀:=State.start_state) (σ:=σ)
simp at this
rw[this hExecCL u]
simp

/-- Specialization to `nonzeroFins hk`: `u` is in the list iff `u ≠ 0`. -/
lemma contrib_nonzeroFins_eval {k : ℕ} (hk : 0 < k) (z : ℤ) (u : Fin k) :
  contrib (k := k) z (nonzeroFins (k := k) hk) u
    = (if u ≠ finZero hk then z ^ (u : Nat) else 0) := by
    unfold contrib nonzeroFins
    simp
    sorry


lemma regEqExpected_after_computeLocal2_of_run
    {k : ℕ} (hk : 0 < k) (z : ℤ) {σ₁ : State k}
    (hrun : run? (computeLocal2 (k := k) hk z) (State.start_state (k := k)) = some σ₁) :
    regEqExpected (k := k) (σ₁ (finZero hk)) (Point.int z) := by
  -- invariant from the start state on the concrete list `nonzeroFins hk`
  have inv := run_computeLocalAux_from_start (k := k) hk z
                (s := nonzeroFins (k := k) hk) (nonzeroFins_allNe hk) hrun
  rcases inv with ⟨pres, dst⟩
  -- check all coordinates u : Fin k
  -- regEqExpected means:  ∀ u, σ₁ dst u = z^u
  -- and we know:          σ₁ dst u = 1_{u=0} + contrib(nonzeroFins) u
  -- but contrib(nonzeroFins) u = if u ≠ 0 then z^u else 0.
  -- Put together, use z^0 = 1.
  have : (List.finRange k).all
          (fun j => decide (σ₁ (finZero hk) j = expectedRow (k := k) (Point.int z) j)) = true := by
    -- show each coordinate holds
    refine List.all_eq_true.2 ?_
    intro u hu
    have hcontrib := contrib_nonzeroFins_eval (k := k) hk z u
    have hdst := dst u
    -- expand expectedRow .int z
    simp [expectedRow, finZero] at *
    aesop
  -- finish: regEqExpected is exactly that `all = true`
  simpa [regEqExpected]





-- lemma cover_applyInverse {k} (hk : 0 < k) (p:Prog k) (σ : State k) (hp:PhaseProductCoverage p σ []) (hpWF:p.WellFormed):
--   PhaseProductCoverage (apply_Op_inverse p) σ [] := by {
--   -- have hrun:=PhaseProductCoverage_exists_state_any hp
--   -- rcases hrun with ⟨σ₁, hrun⟩
--   sorry
--   }
/-- Every element of `addConstAux … n sh` is an `addScaled`.
    (We prove this by strong induction on `n` because the recursive call uses `(n+1)/2`.) -/

private def IsAddScaled {k : ℕ} (op : valid_ops k) : Prop :=
  ∃ (dst src : Fin k) (b : Bool) (sh : Nat),
    op = valid_ops.addScaled dst src (negSrc := b) sh

/-- Every element of `addConstAux … n sh` is an `addScaled`.
    (We prove this by strong induction on `n` because the recursive call uses `(n+1)/2`.) -/
lemma onlyAddScaled_addConstAux {k : ℕ}
  (dst src : Fin k) (neg' : Bool) :
  ∀ n sh (op : valid_ops k),
    op ∈ addConstAux (k := k) dst src neg' n sh → IsAddScaled op := by
  intro n
  refine Nat.strong_induction_on n ?step
  clear n
  intro n ih sh op hmem
  cases n with
  | zero =>
      -- addConstAux _ _ _ 0 _ = []
      simp [addConstAux] at hmem
  | succ m =>
      -- For the recursive call we need ((m+1)/2) < (m+1)
      have hlt : ((m+1) / 2) < (m+1) :=
        Nat.div_lt_self (Nat.succ_pos _) (by decide)
      -- Split on the `bodd` branch
      by_cases hb : Nat.bodd (m+1)
      · -- Head present (the addScaled at shift `sh`) plus tail at (sh+1)
        have hb':m.bodd=false:=by aesop
        simp [addConstAux,hb'] at hmem
        rcases hmem with hhead | htail
        · -- at head
          subst hhead
          exact ⟨dst, src, neg', sh, rfl⟩
        · -- in tail: invoke strong IH at the strictly-smaller index ((m+1)/2)
          exact ih ((m+1)/2) hlt (sh+1) op htail
      · -- No head, only the tail at (sh+1)
        have hb':m.bodd=true:=by aesop
        simp [addConstAux,hb'] at hmem
        exact ih ((m+1)/2) hlt (sh+1) op hmem


/-- Every element of `addConstFrom … c` is an `addScaled`. -/
lemma onlyAddScaled_addConstFrom {k : ℕ}
  (dst src : Fin k) (c : Int) :
  ∀ op ∈ addConstFrom (k := k) dst src c, IsAddScaled op := by
  classical
  intro op hmem
  by_cases hc : c = 0
  · simp [addConstFrom, hc] at hmem
  ·
    -- addConstFrom reduces to addConstAux with `Int.natAbs c`
    have := hmem
    have h2:=(onlyAddScaled_addConstAux (k := k) dst src (c < 0) (Int.natAbs c) 0 op)
    simp_all
    unfold addConstFrom at *
    simp[hc] at this
    apply h2 this
/-- Every element of `computeLocalAux hk z js` is an `addScaled`. -/


lemma onlyAddScaled_computeLocalAux {k : ℕ}
  (hk : 0 < k) (z : Int) :
  ∀ (js : List (Fin k)) (op : valid_ops k),
    op ∈ computeLocalAux (k := k) hk z js → IsAddScaled op := by
    intro js
    induction js with
    | nil =>
        intro op hmem
        simp [computeLocalAux] at hmem
    | cons j js ih =>
        intro op hmem
        -- computeLocalAux hk z (j :: js) = head ++ tail
        -- where head = addConstFrom dst j (z^j), tail = computeLocalAux hk z js
        simp [computeLocalAux] at hmem
        rcases hmem with hhead | htail
        · -- from the head block
          exact
            (onlyAddScaled_addConstFrom (k := k) (finZero (k := k) hk) j (z ^ (j : Nat)) op hhead)
        · -- from the tail
          exact ih op htail


lemma onlyAddScaled_computeLocal2
  {k : ℕ} (hk : 0 < k) (z : Int) :
  ∀ op ∈ computeLocal2 (k := k) hk z, IsAddScaled op := by
  -- Fill in from your definition of `computeLocal2`.
  -- Typical proof outline:
  --   * unfold `computeLocal2` to your “aux over (nonzeroFins hk)”;
  --   * prove `onlyAddScaled_addConstFrom` by recursion on `addConstAux`;
  --   * finish by list induction over sources and `List.mem_append`.
  --
  -- I’m writing it as `aesop` placeholder because the structure is project-specific.
  -- Replace the following line with your concrete proof.
  intro op hmem
  -- Unfold to `computeLocalAux` on `nonzeroFins hk` and reuse the lemma above.
  simpa [computeLocal2] using
    (onlyAddScaled_computeLocalAux (k := k) hk z (nonzeroFins (k := k) hk) op hmem)

@[simp] lemma inv_isAddScaled {k}
  {dst src : Fin k} {b : Bool} {sh : Nat} :
  IsAddScaled (Operations.inv (valid_ops.addScaled dst src (negSrc := b) sh)) := by
  -- for your `Operations.inv`, this flips the sign; adjust the `simp` if your name differs
  refine ⟨dst, src, !b, sh, ?_⟩
  simp [Operations.inv]

lemma onlyAddScaled_applyInverse
  {k : ℕ} {p : Prog k}
  (hall : ∀ op ∈ p, IsAddScaled op) :
  ∀ op ∈ apply_Op_inverse (k := k) p, IsAddScaled op := by
  classical
  intro op hop
  -- `apply_Op_inverse p = p.reverse.map inv`
  unfold apply_Op_inverse at hop
  rcases List.mem_map.1 hop with ⟨o, ho, rfl⟩
  -- membership travels through reverse
  have ho' : o ∈ p := by simpa [List.mem_reverse] using ho
  -- `o` was addScaled; its inverse is addScaled too
  rcases hall o ho' with ⟨dst, src, b, sh, rfl⟩
  simp[inv_isAddScaled (k := k) (dst := dst) (src := src) (b := b) (sh := sh)]

lemma cover_onlyAddScaled_nil
  {k : ℕ} {p : Prog k} (σ : State k)
  (hk:k>0)
  (hall : ∀ op ∈ p, IsAddScaled op) :
  PhaseProductCoverage (k := k) hk p σ [] := by
  classical
  revert σ
  induction p with
  | nil =>
      intro σ; exact PhaseProductCoverageM.nil
  | cons op ps ih =>
      intro σ
      rcases hall op (by simp) with ⟨dst, src, b, sh, rfl⟩
      refine
        PhaseProductCoverageM.step_op
          (M := matchesAt_pointRow_state hk (k := k))
          (op := valid_ops.addScaled dst src (negSrc := b) sh)
          (ps := ps) (σ := σ)
          (τ := State.addScaledReg σ dst src (negSrc := b) sh)
          (pts := []) ?hstep ?hrest
      · -- one addScaled always succeeds
        simp [applyOp?]            -- uses your `@[simp] lemma applyOp?_addScaled`
      · -- recurse on the tail
        apply ih
        intro o ho
        exact hall o (by simp [ho])

lemma cover_applyInverse_computeLocal2_nil {k} (hk : 0 < k) (σ : State k) (z : Int) :
  PhaseProductCoverage hk (apply_Op_inverse (computeLocal2 (k := k) hk z)) σ [] := by
  -- 1) every op inside `computeLocal2` is addScaled …
  have hOnly :
    ∀ op ∈ computeLocal2 (k := k) hk z, IsAddScaled op :=
    onlyAddScaled_computeLocal2 (k := k) hk z
  -- 2) … so every op inside its inverse is addScaled too.
  have hOnlyInv :
    ∀ op ∈ apply_Op_inverse (k := k) (computeLocal2 (k := k) hk z), IsAddScaled op :=
    onlyAddScaled_applyInverse (k := k) (p := computeLocal2 (k := k) hk z) hOnly
  -- 3) An all-addScaled program covers [] from ANY σ (step_op only).
  exact cover_onlyAddScaled_nil (k := k) (p := apply_Op_inverse (computeLocal2 (k := k) hk z))
           σ hk hOnlyInv
/-- Append lemma for `run?`: running `p ++ q` equals running `p`
    to some σ' and then running `q` from σ'. -/
lemma run_append_eq {k} {p q : Prog k} {σ σ' : State k}
  (h : run? p σ = some σ') :
  run? (p ++ q) σ = run? q σ' := by
  revert σ σ' h
  induction p with
  | nil =>
      intro σ σ' h; simp[run?] at h;simp[h]
  | cons op ps ih =>
      intro σ σ' h
      cases hstep : applyOp? (k := k) σ op <;> simp [run?, hstep] at h
      · aesop
@[simp] lemma run_single_phase {k} (i : Fin k) (σ : State k) :
  run? [valid_ops.phaseProduct i] σ = some σ := by
  simp [run?,applyOp?]
/-- Prepend a run-able prefix to an existing coverage proof. -/
lemma coverage_of_run_prefixM {k M}
  {ops ps : Prog k} {σ σ' : State k} {pts : List Operations.Point}
  (hrun : run? ops σ = some σ')
  (hcov : PhaseProductCoverageM M ps σ' pts) :
  PhaseProductCoverageM M (ops ++ ps) σ pts := by
  revert σ σ' pts hrun hcov
  induction ops with
  | nil =>
      intro σ σ' pts h hcov; unfold run? at h; aesop
  | cons op ops ih =>
      intro σ σ' pts h hcov
      cases hstep : applyOp? (k := k) σ op <;> simp [run?, hstep] at h
      {
        simp_all only [List.cons_append]
        have rf:=ih h hcov
        apply PhaseProductCoverageM.step_op
        simp[hstep]
        rfl
        apply rf
      }




/-- On a singleton list, `eraseFirstMatch?` removes the head when the predicate is true. -/
@[simp] lemma eraseFirstMatch?_singleton_true {α}
  (p : α → Bool) (x : α) (hx : p x = true) :
  List.eraseFirstMatch? p [x] = some [] := by
  simp [List.eraseFirstMatch?, hx]


/-- If every op in `p` is `addScaled`, then `run? p σ` succeeds from any `σ`. -/
lemma run_some_of_onlyAddScaled {k : ℕ}
  : ∀ (p : Prog k) (σ : State k),
      (∀ op ∈ p, IsAddScaled op) →
      ∃ σ', run? (k := k) p σ = some σ'
| [],      σ, _    => ⟨σ, by simp [run?]⟩
| op :: ps, σ, hall =>
  by
    -- head is addScaled
    rcases hall op (by simp) with ⟨dst, src, b, sh, rfl⟩
    -- run the head (always succeeds), then the tail by IH
    rcases run_some_of_onlyAddScaled ps
            (State.addScaledReg σ dst src (negSrc := b) sh)
            (by intro o ho; exact hall o (by simp [ho])) with ⟨σ', ih⟩
    exact ⟨σ', by simp [run?, applyOp?, ih]⟩


lemma computeLocal2_some_state
(k : ℕ)
(hk : 0 < k)
(z : ℤ)
(σ : State k):
 ∃ σ₁, run? (computeLocal2 hk z) σ = some σ₁:=by
 classical
  -- all ops are addScaled ⇒ run? cannot fail
  refine run_some_of_onlyAddScaled (k := k)
            (p := computeLocal2 (k := k) hk z) (σ := σ) ?hall
  exact onlyAddScaled_computeLocal2 (k := k) hk z



lemma computeLocal2_some_state_value
(k : ℕ)
(hk : 0 < k)
(z : ℤ)
(σ₁: State k)
(hs: run? (computeLocal2 hk z) State.start_state = some σ₁)
(j: Fin k)
:
  σ₁ ⟨0, hk⟩ j = z ^ j.val
 :=by
  have:=regEqExpected_after_computeLocal2_of_run (hrun:=hs)
  unfold regEqExpected expectedRow at this
  simp_all
  apply this j


theorem matchesAt_pointRow_state3_eq_matchesAt_pointRow_state
  {k : ℕ} (hk : 0 < k) :
  matchesAt_pointRow_state3 (k := k) hk = matchesAt_pointRow_state (k := k) hk := by
  unfold matchesAt_pointRow_state3 matchesAt_pointRow_state regEqExpected expectedRow regEqReg
  simp
  funext σ i pt
  cases pt with
  |int z=>{
    simp
    have h:=computeLocal2_some_state k hk z State.start_state
    rcases h with ⟨σ₁,h⟩
    simp[h]
    congr
    funext j
    simp[finZero]
    apply Iff.intro
    · intro a
      simp_all
      apply computeLocal2_some_state_value k hk z σ₁ h
    · intro a
      simp_all
      have := computeLocal2_some_state_value k hk z σ₁ h
      simp[this]
  }
  |inf=>{
    simp
    split
    next k => simp_all only [List.finRange_zero, zero_tsub, List.all_nil]
    next k k_1 => simp_all only [Nat.succ_eq_add_one, add_tsub_cancel_right]
  }


lemma computeLocal2_some_state_matches
(k : ℕ)
(hk : 0 < k)
(σ₁:State k)
(z : ℤ)
(hrun: run? (computeLocal2 hk z) State.start_state = some σ₁):
matchesAt_pointRow_state hk σ₁ (finZero hk) (Point.int z)=true
:=by
  rw[← matchesAt_pointRow_state3_eq_matchesAt_pointRow_state]
  unfold matchesAt_pointRow_state3
  simp[hrun,regEqReg]

/-- Algebraic correctness of the `computeLocal` builder:
    starting from `start_state`, after running `computeLocal hk z`
    the destination register `0` equals the Vandermonde row for `z`. --/


lemma computeLocal2_matches_row_start {k} (hk : 0 < k) (z : Int) :
  ∃ σ₁, run? (computeLocal2 (k := k) hk z) (State.start_state (k := k)) = some σ₁
      ∧ matchesAt_pointRow_state (k := k) hk σ₁ (finZero hk) (Point.int z) = true := by {
        -- 1) Existence of a post-state
        obtain ⟨σ₁, hrun⟩ := computeLocal2_some_state k hk z State.start_state
        use σ₁
        have := computeLocal2_some_state_matches k hk σ₁ z hrun
        simp[this,hrun]
  }





open Operations
theorem genOpsWithProduct_PhaseProductCoverage
  {k : Nat} (hk : 0 < k) (pts : List Point) :
  PhaseProductCoverage hk (genOpsWithProduct hk pts) State.start_state pts := by
    induction pts with
    | nil=>{
      unfold genOpsWithProduct
      apply PhaseProductCoverageM.nil
    }
    | cons head tail ih=>{
      unfold genOpsWithProduct
      change PhaseProductCoverage hk (opsForPointWithProduct hk head ++ genOpsWithProduct hk tail) State.start_state ([head] ++ tail)
      apply phaseProduct_coverage_check_append
      {
        cases head with
        | inf =>
            -- opsForPointWithProduct .inf = [phaseProduct last]
            simp [opsForPointWithProduct, run?]         -- done
            unfold applyOp?
            simp
        | int x =>
            sorry
      }
      {
        unfold PhaseProductCoverage opsForPointWithProduct
        cases head with
        |int x=> {
          -- simp
            -- apply phaseCoverage_bypass_NoPhase
            -- apply PhaseProductCovergae_on_computeLocal
            -- sorry
            -- unfold PhaseProductCoverage
            -- apply PhaseProductCoverageM.step_phase
            have hbuild : PhaseProductCoverage hk (computeLocal2 (k := k) hk x) (State.start_state (k := k)) [] := by {
              rw[computeLocal_eq]
              apply cover_computeLocal_nil (k := k) hk (State.start_state (k := k)) x
            }

            -- 2) compute the mid-state and the matcher fact (one line, from your algebra lemma)
            obtain ⟨σ₁, hrun₁, hmatch⟩ := computeLocal2_matches_row_start (k := k) hk x

            -- 3) the single marker consumes `[Point.int x]` at σ₁
            have hphase :
                PhaseProductCoverage hk ([valid_ops.phaseProduct (finZero hk)]) σ₁ [Point.int x] := by
              refine PhaseProductCoverageM.step_phase
                (M := matchesAt_pointRow_state hk (k := k))
                (i := finZero hk) (ps := []) (σ := σ₁)
                (pts := [Point.int x]) (pts' := []) ?erase ?tail
              · -- erase the head because the matcher is true at this site
                simpa [List.eraseFirstMatch?] using
                  eraseFirstMatch?_head_true
                    (fun pt => matchesAt_pointRow_state hk (k := k) σ₁ (finZero hk) pt)
                    (Point.int x) [] hmatch
              · simpa using PhaseProductCoverageM.nil (M := matchesAt_pointRow_state hk (k := k)) (σ := σ₁)
            -- 4) coverage of the inverse suffix (no markers)
            have huncompute : PhaseProductCoverage hk
                    (apply_Op_inverse (computeLocal2 (k := k) hk x)) σ₁ [] :=
              cover_applyInverse_computeLocal2_nil (k := k) hk σ₁ x

            -- 5) stitch: (build) ++ (phase) covers [] ++ [x] = [x]
            have hprefix :
                PhaseProductCoverage hk
                  (computeLocal2 (k := k) hk x ++ [valid_ops.phaseProduct (finZero hk)])
                  (State.start_state (k := k)) [Point.int x] :=
              phaseProduct_coverage_check_append_general hk
                (p := computeLocal2 (k := k) hk x)
                (q := [valid_ops.phaseProduct (finZero hk)])
                (σ := State.start_state (k := k)) (σret := σ₁)
                (a := []) (b := [Point.int x])
                (hp := hbuild) (hrun₁) (hphase)
            -- 6) stitch: … ++ (uncompute) covers [x] ++ [] = [x]
            simpa [List.append_assoc]
              using phaseProduct_coverage_check_append_general hk
                (p := computeLocal2 (k := k) hk x ++ [valid_ops.phaseProduct (finZero hk)])
                (q := apply_Op_inverse (computeLocal2 (k := k) hk x))
                (σ := State.start_state (k := k)) (σret := σ₁)
                (a := [Point.int x]) (b := [])
                (hp := hprefix) (by simp[run?_append,hrun₁,applyOp?])
                (huncompute)
        }
        |inf => {
          simp
          apply PhaseProductCoverageM.step_phase
          -- unfold eraseFirstMatch?
          -- unfold matchesAt_pointRow_state regEqExpected expectedRow
          -- simp
          all_goals sorry
        }
      }
      {
        assumption
      }
    }
