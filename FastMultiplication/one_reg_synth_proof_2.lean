import FastMultiplication.One_register_synthesis_proof


open Operations

namespace List


-- /-- A single `addScaled` always succeeds and consumes no points. -/
-- lemma cover_addScaled_nil {k} (hk:k>0) (σ : State k) (dst src : Fin k) (neg' : Bool) (sh : ℕ) :
--   PhaseProductCoverage hk [valid_ops.addScaled dst src (negSrc := neg') sh] σ [] := by
--   refine PhaseProductCoverageM.step_op
--     (M := matchesAt_pointRow_state hk (k := k))
--     (op := valid_ops.addScaled dst src (negSrc := neg') sh)
--     (ps := []) (σ := σ)
--     (τ := State.addScaledReg σ dst src (negSrc := neg') sh)
--     (pts := []) ?hstep ?tail
--   · simp [applyOp?]
--   · simpa using PhaseProductCoverageM.nil (M := matchesAt_pointRow_state hk (k := k)) (σ := _)

-- /-- A mapped list of `(neg,shift)` pairs to `addScaled` ops consumes no points. -/
-- lemma cover_map_pairToOp_nil {k} (hk:k>0) (σ : State k) (dst src : Fin k) (pairs : List (Bool × Nat)) :
--   PhaseProductCoverage hk (pairs.map (pairToOp (k := k) dst src)) σ [] := by
--   classical
--   revert σ
--   induction pairs with
--   | nil =>
--       intro σ; apply PhaseProductCoverageM.nil
--   | cons p ps ih =>
--       intro σ
--       refine
--         PhaseProductCoverageM.step_op
--           (M := matchesAt_pointRow_state hk (k := k))
--           (op := pairToOp (k := k) dst src p)
--           (ps := ps.map (pairToOp (k := k) dst src)) (σ := σ)
--           (τ := State.addScaledReg σ dst src (negSrc := p.1) p.2)
--           (pts := []) ?h ?t
--       · simp [applyOp?, pairToOp]
--       · simpa using ih _

-- 1) Fold-left with "append-on-the-right" form:  foldl (λ acc a, acc ++ H a)
lemma foldl_append_hom {α β} :
  ∀ (H : α → List β) (acc : List β) (xs : List α),
    List.foldl (fun acc a => acc ++ H a) acc xs
      = acc ++ List.foldl (fun acc a => acc ++ H a) [] xs
| H, acc, []      => by simp
| H, acc, a::xs   => by
  simp [foldl_append_hom H (acc ++ H a) xs, List.append_assoc]



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

-- /-- Build coverage for `(op :: ps) ++ q` from a single successful head step
--     and coverage of the rest `(ps ++ q)`. -/
-- lemma step_op_append {k}
--   {op : valid_ops k} {ps q : Prog k}
--   {σ τ : State k}
--   (hk:k>0)
--   (hstep : applyOp? (k := k) σ op = some τ)
--   (hrest : PhaseProductCoverage hk (ps ++ q) τ []) :
--   PhaseProductCoverage hk ((op :: ps) ++ q) σ [] := by
--   refine PhaseProductCoverageM.step_op
--     (M := matchesAt_pointRow_state hk (k := k))
--     (op := op) (ps := ps ++ q) (σ := σ) (τ := τ) (pts := [])
--     (by simpa [applyOp?] using hstep) ?_
--   -- `ps` appended under the cons:
--   simpa [List.cons_append] using hrest



-- lemma phaseCoverage_append_nil
--   {k} (p q : Prog k) {σ σ₂ : State k}
--   (hk:k>0)
--   (hp  : PhaseProductCoverage hk p σ [])
--   (hr  : run? p σ = some σ₂)
--   (hq  : PhaseProductCoverage hk q σ₂ []) :
--   PhaseProductCoverage hk (p ++ q) σ [] := by
--   have aux :
--     ∀ {p σ pts}, PhaseProductCoverage hk p σ pts → pts = [] →
--       ∀ (q : Prog k) (σ₂ : State k),
--         run? p σ = some σ₂ →
--         PhaseProductCoverage hk q σ₂ [] →
--         PhaseProductCoverage hk (p ++ q) σ [] := by
--     intro p σ pts hcov hpts q σ₂ hr hq
--     revert q σ₂
--     induction hcov generalizing q σ₂ with
--     | nil =>
--         intro q σ₂ hrun hq
--         aesop
--     | @step_op op ps σ τ pts hstep hrest ih =>
--         intro q σ₂ hrun hq
--         -- push run? through the head step
--         have htail : run? ps τ = some σ₂ := by
--           simpa [run?, hstep] using hrun
--         -- recurse on (ps ++ q); use pts = [] via `hpts`
--         have hrest' :
--           PhaseProductCoverage hk (ps ++ q) τ [] := by
--           aesop
--         -- rebuild ((op :: ps) ++ q)
--         refine PhaseProductCoverageM.step_op
--           (M := matchesAt_pointRow_state hk (k := k))
--           (op := op) (ps := ps ++ q) (σ := σ) (τ := τ) (pts := [])
--           (by simpa [applyOp?] using hstep) ?_
--         simpa using hrest'
--     | @step_phase i ps σ pts pts' hcons hrest ih =>
--         intro q σ₂ hrun hq
--         -- impossible when pts = []
--         cases hpts
--         have : False := by simp [List.eraseFirstMatch?] at hcons
--         exact this.elim
--   exact aux hp rfl q σ₂ hr hq

/-- The fold-step function used inside `computeLocal`. -/
private def step {k} (hk : 0 < k) (z : Int) :
    Prog k → Fin k → Prog k :=
  fun acc j =>
    let dst := finZero hk
    let c   : Int := z ^ (j : Nat)
    if c = 0 then acc
    else acc ++ (signedPow2Decomp c).map (pairToOp (k := k) dst j)


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
      by_cases hb : Odd (m+1)
      ·
        -- Head present: one addScaled at `sh`, then tail at (sh+1)
        -- Peel the head and name the post-state
        have htail :
          run? (k := k)
                (addConstAux (k := k) dst src neg' ((m+1)/2) (sh+1))
                (State.addScaledReg σ dst src (negSrc := neg') sh)
            = some τ := by
          -- Unroll run? once using the head step
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

inductive ExecAddConstAux {k : ℕ}
    (dst src : Fin k) (neg' : Bool) :
    ℕ → ℕ → State k → State k → Prop
| zero {sh σ} :
    ExecAddConstAux dst src neg' 0 sh σ σ

| succ_even {n sh σ σ₂}
    (hb : Even (n + 1))
    (htail :
      ExecAddConstAux dst src neg' ((n + 1) / 2) (sh + 1) σ σ₂) :
    ExecAddConstAux dst src neg' (n + 1) sh σ σ₂

| succ_odd {n sh σ σ₁ σ₂}
    (hb : Odd (n + 1))
    (hstep :
      applyOp? σ (valid_ops.addScaled dst src (negSrc := neg') sh)
        = some σ₁)
    (htail :
      ExecAddConstAux dst src neg' ((n + 1) / 2) (sh + 1) σ₁ σ₂) :
    ExecAddConstAux dst src neg' (n + 1) sh σ σ₂


lemma ExecAddConstAux_run?
    {k : ℕ} {dst src : Fin k} {neg' : Bool}
    {n sh : ℕ} {σ τ : State k}
    (h : ExecAddConstAux dst src neg' n sh σ τ) :
    run? (addConstAux dst src neg' n sh) σ = some τ := by
  classical
  induction h with
  | zero =>
      simp [addConstAux]
  | succ_even hb htail ih =>
      unfold addConstAux; rename_i n sh σ σ₁; have :¬ Odd (n+1):=by simp[hb]
      simp[this];simp_all
  | succ_odd hb hstep htail ih =>
      simp [addConstAux];simp_all

lemma ExecAddConstAux.of_run?
    {k : ℕ} {dst src : Fin k} {neg' : Bool} :
  ∀ n sh {σ τ : State k},
    run? (addConstAux dst src neg' n sh) σ = some τ →
    ExecAddConstAux dst src neg' n sh σ τ := by
  classical
  -- strong recursion on n, with sh/σ/τ generalized inside motive
  refine fun n => Nat.strongRecOn n ?step
  intro n ih sh σ τ h
  cases n with
  | zero =>
      -- n = 0
      simp [addConstAux] at h
      subst τ
      exact ExecAddConstAux.zero
  | succ n =>
      -- n.succ case
      -- Expand addConstAux at (n+1, sh)
      unfold addConstAux at h
      -- name the tail program
      set rest :=
        addConstAux dst src neg' ((n + 1) / 2) (sh + 1)
        with hrest

      by_cases hb : Odd (n + 1)
      · -- ODD CASE: addScaled :: rest
        -- run? (addScaled :: rest) σ = some τ
        unfold run? at h
        simp [hb, hrest] at h


        --rcases h with ⟨σ₁, hstep, hrest_run⟩

        -- m = (n+1)/2 is smaller than n+1
        have hm : (n + 1) / 2 < Nat.succ n :=
          Nat.div_lt_self (Nat.succ_pos _) (by decide)
        apply ExecAddConstAux.succ_odd hb (by simp;rfl)
        aesop

      · -- EVEN CASE: just rest
        simp [hb, hrest] at h

        have hm : (n + 1) / 2 < Nat.succ n :=
          Nat.div_lt_self (Nat.succ_pos _) (by decide)

        have htail :
          ExecAddConstAux dst src neg' ((n + 1) / 2) (sh + 1) σ τ :=
          ih ((n + 1) / 2) hm (sh + 1)
            (by simpa [hrest] using h)

        apply ExecAddConstAux.succ_even
        simp at hb;assumption
        simp_all only



lemma run_addConstAux_effect_dst
  {k : ℕ} (_:k>0)(dst src : Fin k) (neg' : Bool) (hsd : src ≠ dst) :
  ∀ n sh {σ τ : State k},
    run? (k := k) (addConstAux (k := k) dst src neg' n sh) σ = some τ →
    ∀ u, τ dst u
            = σ dst u
              + ((if neg' then (-1 : ℤ) else 1) * (2 : ℤ)^sh * (n : ℤ)) * σ src u
:= by {
  intro n sh σ τ h u
  have h2:=ExecAddConstAux.of_run? n sh h
  induction h2 with
  | zero =>
      simp at *
  | succ_even =>
      rename_i n sh σ σ₂ hb htail htail_ih
      have htail2:=ExecAddConstAux_run? htail
      have ih' := htail_ih htail2
      simp_all
      have : 2 ^ (sh + 1) * (((n:ℤ) + 1) / 2) = 2 ^ sh * ((n:ℤ) + 1):=by
        rcases hb with ⟨m, hm⟩

        -- Cast hm to ℤ and rewrite as (↑n + 1) = 2 * m
        have hEq : (n + 1 : ℤ) = (2 : ℤ) * (m : ℤ) := by
          -- hm : n + 1 = m + m
          have := congrArg (fun x : ℕ => (x : ℤ)) hm
          -- LHS: ↑(n + 1) = ↑n + 1
          -- RHS: ↑(m + m) = ↑m + ↑m = 2 * ↑m
          simpa [Nat.cast_add, two_mul, add_comm, add_left_comm, add_assoc] using this

        -- So 2 ∣ (↑n + 1)
        have hdiv : (2 : ℤ) ∣ (n + 1) := by
          refine ⟨↑m, ?_⟩
          exact hEq

        -- Exact division: ((↑n + 1) / 2) * 2 = ↑n + 1
        have hmul : (↑n + 1) / 2 * 2 = (↑n + 1) :=by
          omega

        -- Now just algebra
        calc
          (2 : ℤ) ^ (sh + 1) * ((↑n + 1) / 2)
              = (2 : ℤ) ^ sh * 2 * ((↑n + 1) / 2) := by
                    -- 2^(sh+1) = 2^sh * 2
                    simp [pow_succ, mul_comm, mul_left_comm]
          _   = (2 : ℤ) ^ sh * (((↑n + 1) / 2) * 2) := by
                    ac_rfl
          _   = (2 : ℤ) ^ sh * (↑n + 1) := by
                    simp;omega
      split
      next h_1 =>
        subst h_1
        simp[this]
      next h_1 =>
        simp[this]
  | succ_odd=>
      rename_i n sh σ σ₁ σ₂ hb hstep htail htail_ih
      have htail2:=ExecAddConstAux_run? htail
      have ih' := htail_ih htail2
      have htail_run :
      run? (addConstAux dst src neg' ((n + 1) / 2) (sh + 1)) σ₁ = some σ₂ := by
        unfold addConstAux at h
        simp_all only
      have h_tail_spec :=
        htail_ih htail_run

      have hσ₁ :
          σ₁ = State.addScaledReg σ dst src neg' sh := by
        simp [applyOp?] at hstep
        simp_all only

      have h_dst₁ :
          σ₁ dst u =
            σ dst u
              + (if neg' = true then -1 else 1)
                * 2 ^ sh * σ src u := by
        simp_all
        rw[Int.mul_comm]


      have h_src₁ :
          σ₁ src u = σ src u := by
        have hneq : src ≠ dst := hsd
        simp_all
      have hmod1 : (n + 1) % 2 = 1 := by
        apply Nat.odd_iff.mp hb

      have hdecomp_nat :
          n + 1 = 2 * ((n + 1) / 2) + 1 := by
        -- n+1 = 2 * (div) + mod ; here mod = 1
        have := Nat.div_add_mod (n + 1) 2
        -- rewrite mod with hmod1
        -- (n + 1) = (n + 1) / 2 * 2 + 1
        simpa [two_mul, hmod1] using this.symm

      have hdecomp_int :
          (n + 1 : ℤ)
            = 2 * ((n + 1) / 2 : ℤ) + 1 := by
        exact_mod_cast hdecomp_nat

      calc
    σ₂ dst u
        = σ₁ dst u
          + (if neg' = true then -1 else 1)
              * 2 ^ (sh + 1) * ((n + 1) / 2 : ℤ) * σ₁ src u :=
          h_tail_spec
    _   = σ₁ dst u
          + (if neg' = true then -1 else 1)
              * (2 ^ sh * 2) * ((n + 1) / 2 : ℤ) * σ src u := by
          -- use pow_succ and h_src₁
          simp [pow_succ, h_src₁, mul_comm, mul_left_comm]
    _   = (σ dst u
            + (if neg' = true then -1 else 1)
                * 2 ^ sh * σ src u)
          + (if neg' = true then -1 else 1)
              * 2 ^ (sh + 1) * ((n + 1) / 2 : ℤ) * σ src u := by
          -- expand σ₁ dst u via head step
          simp [h_dst₁, add_assoc]
          congr
    _   =
          σ dst u
            + (if neg' = true then -1 else 1)
                * 2 ^ sh
                * ((2 * ((n + 1) / 2 : ℤ) + 1)) * σ src u := by
          -- factor out sgn * 2^sh * σ src u; use 2^(sh+1) = 2^sh*2
          ring_nf
    _   =
          σ dst u
            + (if neg' = true then -1 else 1)
                * 2 ^ sh * (n + 1 : ℤ) * σ src u := by
          -- substitute decomposition of (n+1)
          congr
          omega
}


lemma neg_abs_pow_mul_eq_pow_mul
    {z : ℤ} {j : Fin k} {σ₀: State k}
    {u : Fin k}
    (hzj : z ^ (↑j : ℕ) < 0) :
    - (|z| ^ (↑j : ℕ) * σ₀ j u)
      = z ^ (↑j : ℕ) * σ₀ j u := by
  classical

  -- First: |z|^n = |z^n| for n = ↑j
  have h_abs_pow :
      (|z| : ℤ) ^ (↑j : ℕ) = |z ^ (↑j : ℕ)| := by
    -- prove by induction on n = ↑j
    induction' (↑j : ℕ) with n ih
    · -- n = 0
      simp
    · -- n.succ
      -- z^(n+1) = z^n * z, abs (z^(n+1)) = abs(z^n) * abs(z)
      simp

  -- Second: since z^j < 0, |z^j| = - z^j
  have h_abs_neg : |z ^ (↑j : ℕ)| = - (z ^ (↑j : ℕ)) :=
    abs_of_neg hzj

  -- So |z|^j = - z^j
  have h1 :
      (|z| : ℤ) ^ (↑j : ℕ) = - (z ^ (↑j : ℕ)) := by
    simp at h_abs_neg
    rw[h_abs_neg]

  -- Hence -(|z|^j) = z^j
  have h2 :
      - ((|z| : ℤ) ^ (↑j : ℕ)) = z ^ (↑j : ℕ) := by
    calc
      - ((|z| : ℤ) ^ (↑j : ℕ))
          = - (- (z ^ (↑j : ℕ))) := by simp[h1]
      _   = z ^ (↑j : ℕ) := by simp

  -- Push the negation inside the product and use h2
  calc
    - (|z| ^ (↑j : ℕ) * σ₀ j u)
        = - ((|z| : ℤ) ^ (↑j : ℕ)) * σ₀ j u := by
            -- -(a*b) = (-a)*b
            simp [neg_mul]
    _   = (z ^ (↑j : ℕ)) * σ₀ j u := by
            simp [h2]


lemma addConstFrom_effect
    {k : ℕ} (hk : 0 < k) (z : ℤ)
    (j : Fin k)
    (h_j_ne_dst : j ≠ finZero hk) -- The required hypothesis
    {σ₀ σ₁ : State k}
    (h :
      run? (addConstFrom (finZero hk) j (z ^ (j : ℕ))) σ₀ = some σ₁) :
    (∀ t ≠ finZero hk, σ₁ t = σ₀ t) ∧
    (∀ u : Fin k,
      σ₁ (finZero hk) u
        = σ₀ (finZero hk) u + z ^ (j : ℕ) * σ₀ j u) :=
by
  -- Define aliases for clarity
  let dst := finZero hk
  let c := z ^ (j : ℕ)

  -- The definition of 'addConstFrom' splits on c = 0
  by_cases hc : c = 0
  · -- Case 1: c = 0
    change z ^ j.val = 0 at hc
    rw[hc]
    -- The program is '[]', so 'addConstFrom' is the empty list.
    -- 'run? [] σ₀ = some σ₁' implies σ₁ = σ₀
    have h_run_eq : σ₁ = σ₀ := by
      simp [addConstFrom, hc] at h
      rw[h]
    subst h_run_eq
    apply And.intro
    · -- 1. Preservation: 'σ₀ t = σ₀ t'
      intro t ht; rfl
    · -- 2. Update: 'σ₀ dst u = σ₀ dst u + 0 * σ₀ j u'
      intro u; simp [add_zero]

  · -- Case 2: c ≠ 0
    -- 'addConstFrom' is defined as 'addConstAux ...'
    apply And.intro
    · -- Goal 1: Preservation (∀ t ≠ dst, σ₁ t = σ₀ t)
      -- This is exactly what 'run_addConstFrom_effect_1' proves.
      apply run_addConstFrom_effect_1
      exact h
    · -- Goal 2: Update (∀ u, σ₁ dst u = σ₀ dst u + c * σ₀ j u)
      intro u
      -- We use the lemma we just proved: 'run_addConstAux_effect_dst'
      have hc1:=hc
      change ¬z ^ j.val = 0 at hc
      unfold addConstFrom at h
      simp[hc] at h
      have := run_addConstAux_effect_dst hk (finZero hk) j (decide (z ^ j.val < 0)) h_j_ne_dst (z.natAbs ^ j.val) 0 (σ:=σ₀) (τ:=σ₁) h u
      by_cases hzj:z^(j.val)<0
      ·
        simp[hzj] at this
        simp_all only [ne_eq, not_false_eq_true, pow_eq_zero_iff', not_and, Decidable.not_not, decide_true,
          add_right_inj, c]
        have h_abs_pow :
          (|z| : ℤ) ^ (j.val) = - (z ^ (j.val)) := by
          have h_abs_neg : |z ^ (↑j : ℕ)| = - (z ^ (↑j : ℕ)) :=
            abs_of_neg hzj
          -- And |z ^ n| = |z| ^ n
          have h_abs_pow' : |z ^ (↑j : ℕ)| = (|z| : ℤ) ^ (↑j : ℕ) :=
            abs_pow z (↑j : ℕ)
          simp_all only [abs_pow]
        calc
        -(|z| ^ ↑j * σ₀ j u)
            = -((|z| : ℤ) ^ (↑j : ℕ)) * σ₀ j u := by
                  -- - (a * b) = (-a) * b
                  simp[neg_mul]  -- or `simp [neg_mul, mul_comm, mul_left_comm, mul_assoc]`
        _   = (z ^ (↑j : ℕ)) * σ₀ j u := by
                  -- since (|z|^n) = - z^n, we have -(|z|^n) = z^n
                  have h_neg :
                      -((|z| : ℤ) ^ (↑j : ℕ))
                        = z ^ (↑j : ℕ) := by
                        calc
                          -((|z| : ℤ) ^ (↑j : ℕ))
                              = -(- (z ^ (↑j : ℕ))) := by simp[h_abs_pow]
                          _   = z ^ (↑j : ℕ) := by simp
                  simp[h_neg]

      · simp[hzj] at this
        simp_all only [ne_eq, not_false_eq_true, pow_eq_zero_iff', not_and, Decidable.not_not, decide_false, not_lt,
          add_right_inj, mul_eq_mul_right_iff,  c]
        have h_abs_of_nonneg : |z ^ (↑j : ℕ)| = z ^ (↑j : ℕ) :=
          abs_of_nonneg hzj

        -- And from the helper we know |z|^n = |z^n|
        have h_abs_pow :
            (|z| : ℤ) ^ (↑j : ℕ) = |z ^ (↑j : ℕ)| :=
          by simp_all only [abs_pow]

        -- Combine to get |z|^n = z^n
        have h_eq : (|z| : ℤ) ^ (↑j : ℕ) = z ^ (↑j : ℕ) := by
          simpa [h_abs_of_nonneg] using h_abs_pow

        -- So the left disjunct holds; no need for the right one.
        exact Or.inl h_eq

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
    (j : Fin k) (hj:j≠finZero hk) (js : List (Fin k))
    {σ₀ σ₁ : State k} (u : Fin k)
    (hhead : run? (addConstFrom (finZero hk) j (z ^ (j : ℕ))) σ₀ = some σ₁)
    (hs_js : AllNe (finZero hk) js) :
    σ₁ (finZero hk) u + contribFrom σ₁ z js u = σ₀ (finZero hk) u + contribFrom σ₀ z (j :: js) u := by

  have h_effect : (∀ t ≠ finZero hk, σ₁ t = σ₀ t) ∧
                  (∀ u, σ₁ (finZero hk) u = σ₀ (finZero hk) u + z ^ (j : ℕ) * σ₀ j u) := by
    exact addConstFrom_effect (k := k) hk z j hj hhead

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
      have := ExecCL_contrib_inductive_step_equality hk z j hj_ne js u hhead hs_js
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

/-- Elements of `nonzeroFins hk` are never `finZero hk`. -/
lemma mem_nonzeroFins_ne {k : ℕ} (hk : 0 < k) {j : Fin k}
    (hj : j ∈ nonzeroFins hk) :
    j ≠ finZero hk := by
  unfold nonzeroFins at hj
  rcases List.mem_filter.1 hj with ⟨_, hjne⟩
  aesop

/-- `nonzeroFins hk` has no duplicates. -/
lemma nodup_nonzeroFins {k : ℕ} (hk : 0 < k) :
    (nonzeroFins hk).Nodup :=by
  unfold nonzeroFins
  have hsub :
      ((List.finRange k).filter (fun j : Fin k => j ≠ finZero (k := k) hk))
        <+ List.finRange k :=
    by aesop
  exact (List.nodup_finRange k).sublist hsub

/-- If every index in `js` is different from `u`, then the contribution at `u` is `0`. -/
lemma contrib_eq_zero_of_all_ne
    {k : ℕ} (z : ℤ) (js : List (Fin k)) (u : Fin k)
    (hall : ∀ j ∈ js, j ≠ u) :
    contrib z js u = 0 := by
  classical
  induction js with
  | nil =>
      simp [contrib]
  | cons j js ih =>
      have hju : j ≠ u := hall j (by simp)
      have hall' : ∀ j' ∈ js, j' ≠ u :=
        fun j' hj' => hall j' (by simp [hj'])
      simp[contrib]
      aesop

lemma contrib_of_unique
    {k : ℕ} (z : ℤ) (js : List (Fin k)) (u : Fin k)
    (hnd : js.Nodup) (hu : u ∈ js) :
    contrib z js u = z ^ (u.val) := by
  classical
  induction js with
  | nil =>
      cases hu
  | cons j js ih =>
      have hnd' : js.Nodup := (List.nodup_cons.mp hnd).2
      have hnot : j ∉ js := (List.nodup_cons.mp hnd).1
      cases hu with
      | head hju =>
          -- show that `u` does not appear in `js`
          have hall : ∀ j' ∈ js, j' ≠ u := by
            aesop
          have hzero := contrib_eq_zero_of_all_ne (z := z) (js := js) (u := u) hall
          simp [contrib, hzero]
      | tail hu_js =>
          -- case `u ∈ js` and hence `j ≠ u`
          have hju : j ≠ u := by
            intro h; subst h
            have hj : j ∈ js := by
              simp_all only [nodup_cons, not_false_eq_true, and_self, IsEmpty.forall_iff, imp_self];rename_i a
              exact hnot a
            exact hnot hj
          have ih' := ih hnd'
          simp [contrib]
          aesop


/-- If `u ≠ finZero hk`, then `u` is in `nonzeroFins hk`. -/
lemma mem_nonzeroFins_of_ne_zero {k : ℕ} (hk : 0 < k)
    {u : Fin k} (hnez : u ≠ finZero hk) :
    u ∈ nonzeroFins hk := by
  unfold nonzeroFins
  have hrange : u ∈ List.finRange k := by
    aesop
  aesop


/-- Final lemma: contribution from all nonzero registers. -/
lemma contrib_nonzeroFins
    {k : ℕ} (hk : 0 < k) (z : ℤ) (u : Fin k) :
    contrib z (nonzeroFins hk) u =
      if u ≠ finZero hk then z ^ (u.val) else 0 := by
  classical
  by_cases hnez : u ≠ finZero hk
  · -- `u` is nonzero: exactly one contributing index `u`
    have hu : u ∈ nonzeroFins hk :=
      mem_nonzeroFins_of_ne_zero hk hnez
    have hnd := nodup_nonzeroFins (k := k) hk
    have h := contrib_of_unique (z := z)
                 (js := nonzeroFins hk) (u := u) hnd hu
    simp [hnez, h]
  · -- `u = finZero hk`: all indices in the list are ≠ u, so sum is 0
    have hu0 : u = finZero hk := by
      push_neg at hnez; exact hnez
    subst hu0
    have hall : ∀ j ∈ nonzeroFins hk, j ≠ finZero hk :=
      fun j hj => mem_nonzeroFins_ne (hk := hk) hj
    have hzero :=
      contrib_eq_zero_of_all_ne (z := z)
        (js := nonzeroFins hk) (u := finZero hk) hall
    simp [hzero, hnez]

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
    unfold expectedRow
    simp_all only [ne_eq, start_state_entry, mem_finRange, decide_eq_true_eq]
    split
    next h =>
      subst h
      simp_all only [_root_.finZero_val, pow_zero, add_eq_left]
      apply contrib_nonzeroFins
    next h =>
      simp_all only [zero_add]
      have:=contrib_nonzeroFins hk z u
      rw[this]
      simp[h]
  -- finish: regEqExpected is exactly that `all = true`
  simpa [regEqExpected]



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
      by_cases hb : Odd (m+1)
      · -- Head present (the addScaled at shift `sh`) plus tail at (sh+1)

        simp [addConstAux,hb] at hmem
        rcases hmem with hhead | htail
        · -- at head
          subst hhead
          exact ⟨dst, src, neg', sh, rfl⟩
        · -- in tail: invoke strong IH at the strictly-smaller index ((m+1)/2)
          exact ih ((m+1)/2) hlt (sh+1) op htail
      · -- No head, only the tail at (sh+1)
        simp [addConstAux,hb] at hmem
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
  revert σ
  induction p with
  | nil =>
      intro σ; exact PhaseProductCoverageM.nil
  | cons op ps ih =>
      intro σ
      rcases hall op (by simp) with ⟨dst, src, b, sh, rfl⟩
      have:=PhaseProductCoverageM.step_op
          (M := matchesAt_pointRow_state hk (k := k))
          (op := valid_ops.addScaled dst src (negSrc := b) sh)
          (ps := ps) (σ := σ)
          (τ := State.addScaledReg σ dst src (negSrc := b) sh)
          (pts := []) ?hstep ?hrest
      apply this
      all_goals try simp
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
-- /-- Prepend a run-able prefix to an existing coverage proof. -/
-- lemma coverage_of_run_prefixM {k M}
--   {ops ps : Prog k} {σ σ' : State k} {pts : List Operations.Point}
--   (hrun : run? ops σ = some σ')
--   (hcov : PhaseProductCoverageM M ps σ' pts) :
--   PhaseProductCoverageM M (ops ++ ps) σ pts := by
--   revert σ σ' pts hrun hcov
--   induction ops with
--   | nil =>
--       intro σ σ' pts h hcov; unfold run? at h; aesop
--   | cons op ops ih =>
--       intro σ σ' pts h hcov
--       cases hstep : applyOp? (k := k) σ op <;> simp [run?, hstep] at h
--       {
--         simp_all only [List.cons_append]
--         have rf:=ih h hcov
--         apply PhaseProductCoverageM.step_op
--         simp[hstep]
--         rfl
--         apply rf
--       }




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



lemma last_lt {k : ℕ} (hk : 0 < k) : k - 1 < k := by
  cases h : k with
  | zero =>
      have : (0 : ℕ) < 0 := by simp[h] at hk
      simp at this
  | succ n =>
      simp

open Operations

theorem opsForPointWithProduct_returns_to_original
  {k : Nat} (hk : 0 < k) (head : Point) :
  run? (opsForPointWithProduct hk head) State.start_state = some State.start_state := by {
    cases head with
        | inf =>
            -- opsForPointWithProduct .inf = [phaseProduct last]
            simp [opsForPointWithProduct, run?]         -- done
            unfold applyOp?
            simp
        | int x =>
            unfold opsForPointWithProduct
            simp
            simp[run?_append]
            have:= computeLocal2_some_state k hk x State.start_state
            rcases this with ⟨σ₁,this⟩
            simp[this,applyOp?]
            apply State.run?_inverse_undoes_WF
            apply computeLocal2_Valid
            apply this
  }

theorem genOpsWithProduct_returns_to_original
  {k : Nat} (hk : 0 < k) (pts : List Point) :
  run? (genOpsWithProduct hk pts) State.start_state = some State.start_state := by {
    induction pts with
    |nil=>{
      unfold genOpsWithProduct
      simp_all
    }
    |cons head tail ih =>{
      simp [genOpsWithProduct]

      -- head block returns to start_state
      have hhead :
        run? (opsForPointWithProduct hk head) State.start_state
          = some State.start_state :=
        opsForPointWithProduct_returns_to_original (k := k) hk head

      -- tail block (by IH) also returns to start_state when started at start_state
      have htail :
        run? (genOpsWithProduct hk tail) State.start_state
          = some State.start_state :=
        ih

      -- compose them with the helper lemma
      simp[run?_append,hhead,htail]
    }
  }

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
        apply opsForPointWithProduct_returns_to_original
      }
      {
        unfold PhaseProductCoverage opsForPointWithProduct
        cases head with
        |int x=> {
            have hbuild : PhaseProductCoverage hk (computeLocal2 (k := k) hk x) (State.start_state (k := k)) [] := by {
              rw[computeLocal_eq]
              apply cover_computeLocal_nil (k := k) hk (State.start_state (k := k)) x
            }

            obtain ⟨σ₁, hrun₁, hmatch⟩ := computeLocal2_matches_row_start (k := k) hk x

            have hphase :
                PhaseProductCoverage hk ([valid_ops.phaseProduct (finZero hk)]) σ₁ [Point.int x] := by
              refine PhaseProductCoverageM.step_phase
                (M := matchesAt_pointRow_state hk (k := k))
                (i := finZero hk) (ps := []) (σ := σ₁)
                (pts := [Point.int x]) (pts' := []) ?erase ?tail
              ·
                simpa [List.eraseFirstMatch?] using
                  eraseFirstMatch?_head_true
                    (fun pt => matchesAt_pointRow_state hk (k := k) σ₁ (finZero hk) pt)
                    (Point.int x) [] hmatch
              · simpa using PhaseProductCoverageM.nil (M := matchesAt_pointRow_state hk (k := k)) (σ := σ₁)
            have huncompute : PhaseProductCoverage hk
                    (apply_Op_inverse (computeLocal2 (k := k) hk x)) σ₁ [] :=
              cover_applyInverse_computeLocal2_nil (k := k) hk σ₁ x

            have hprefix :
                PhaseProductCoverage hk
                  (computeLocal2 (k := k) hk x ++ [valid_ops.phaseProduct (finZero hk)])
                  (State.start_state (k := k)) [Point.int x] :=
              phaseProduct_coverage_check_append_aux hk
                (p := computeLocal2 (k := k) hk x)
                (q := [valid_ops.phaseProduct (finZero hk)])
                (σ := State.start_state (k := k)) (σret := σ₁)
                (a := []) (b := [Point.int x])
                (hp := hbuild) (hrun₁) (hphase)

            simpa [List.append_assoc]
              using phaseProduct_coverage_check_append_aux hk
                (p := computeLocal2 (k := k) hk x ++ [valid_ops.phaseProduct (finZero hk)])
                (q := apply_Op_inverse (computeLocal2 (k := k) hk x))
                (σ := State.start_state (k := k)) (σret := σ₁)
                (a := [Point.int x]) (b := [])
                (hp := hprefix) (by simp[run?_append,hrun₁,applyOp?])
                (huncompute)
        }
        |inf => {
          simp
          let i : Fin k := ⟨k - 1, last_lt hk⟩
          have hmatch :
              matchesAt_pointRow_state (k := k) hk (State.start_state (k := k)) i Point.inf
              = true := by
            unfold matchesAt_pointRow_state
            apply List.all_eq_true.mpr
            intro j _
            apply decide_eq_true_iff.mpr
            have hne0 : k ≠ 0 := ne_of_gt hk
            simp [expectedRow, i]
            aesop
          refine PhaseProductCoverageM.step_phase
            (M := matchesAt_pointRow_state hk)
            (i := i)
            (ps := [])
            (σ := State.start_state (k := k))
            (pts := [Point.inf])
            (pts' := []) ?consume ?rest
          · -- eraseFirstMatch? consumes Point.inf using hmatch
            simp [List.eraseFirstMatch?, hmatch]
          · -- tail: empty program, empty point list
            exact PhaseProductCoverageM.nil
        }
      }
      {
        assumption
      }
    }
