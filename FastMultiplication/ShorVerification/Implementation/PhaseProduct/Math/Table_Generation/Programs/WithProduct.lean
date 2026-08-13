import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Builders.FragmentLemmas

/-!
# `genOpsWithProduct`: certification

The generator-specific final assembly (matching and the two headline
theorems `genOpsWithProduct_returns_to_original` and
`genOpsWithProduct_PhaseProductCoverage`). Generic material now lives in
`Core/ListHelpers`, `Core/RunLemmas`, and `Builders/FragmentLemmas`.
-/

open Operations

/-! =========================================================
    Section 13: Matching and final assembly

How this section contributes to the final theorem:
- `computeLocal2_some_state` is reused from `Synthesis_programs` to produce a
  post-state for the build phase.
- `computeLocal2_some_state_value`,
  `matchesAt_pointRow_state3_eq_matchesAt_pointRow_state`,
  `computeLocal2_some_state_matches`, and `computeLocal2_matches_row_start` turn
  semantic correctness into the exact matcher fact needed for a successful
  `phaseProduct` consumption step.
- `last_lt` supplies the witness used in the `Point.inf` branch.
- `opsForPointWithProduct_returns_to_original` proves that a single generated
  point block returns to the start state.
- `genOpsWithProduct_returns_to_original` lifts that reversibility to a whole
  list of points.
- `genOpsWithProduct_PhaseProductCoverage` is the final theorem, combining the
  build, consume, cleanup, and append lemmas above into the full correctness
  statement.
-/

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

lemma computeLocal2_some_state_matches
    (k : ℕ)
    (hk : 0 < k)
    (σ₁ : State k)
    (z : ℤ)
    (hrun :
      run? (computeLocal2 hk z) State.start_state = some σ₁) :
    matchesAt_pointRow_state hk σ₁ (finZero hk) (Point.int z) = true := by
  simpa [matchesAt_pointRow_state] using
    regEqExpected_after_computeLocal2_of_run
      (k := k) hk z hrun

lemma regEqExpected_after_computeFracLocal2_of_run
    {k : ℕ} (hk : 0 < k) (c : ℤ) {σ₁ : State k}
    (hrun :
      run? (computeFracLocal2 (k := k) hk c)
        (State.start_state (k := k)) = some σ₁) :
    regEqExpected (k := k) (σ₁ (finLast hk)) (Point.frac c) := by
  have hAll : AllNe (finLast (k := k) hk) (nonlastFins (k := k) hk) :=
    nonlastFins_allNe (k := k) hk
  have inv :=
    run_computeFracLocalAux_from_start (k := k) hk c
      (nonlastFins (k := k) hk) hAll (by
        simpa [computeFracLocal2] using hrun)
  rcases inv with ⟨_pres, hdst⟩
  have :
      (List.finRange k).all
        (fun j =>
          decide (σ₁ (finLast hk) j = expectedRow (k := k) (Point.frac c) j))
        = true := by
    refine List.all_eq_true.2 ?_
    intro u hu
    apply decide_eq_true_iff.mpr
    unfold expectedRow
    rw [hdst u]
    have hcontrib := fracContrib_nonlastFins (k := k) hk c u
    by_cases hul : u = finLast hk
    · have hnot : ¬u ≠ finLast hk := by simp [hul]
      have hcontribLast :
          fracContrib (k := k) c (nonlastFins hk) u = 0 := by
        simpa [hnot] using hcontrib
      rw [hcontribLast]
      simp [hul, finLast]
    · have hcontribU :
          fracContrib (k := k) c (nonlastFins hk) u =
            fracCoeff (k := k) c u := by
        simpa [hul] using hcontrib
      simp [hcontribU, fracCoeff, hul]
  simpa [regEqExpected] using this

lemma computeFracLocal2_matches_row_start
    {k : ℕ} (hk : 0 < k) (c : ℤ) :
    ∃ σ₁,
      run? (computeFracLocal2 (k := k) hk c)
        (State.start_state (k := k)) = some σ₁
      ∧
      matchesAt_pointRow_state hk σ₁ (finLast hk) (Point.frac c) = true := by
  obtain ⟨σ₁, hrun⟩ :=
    computeFracLocal2_some_state k hk c State.start_state
  refine ⟨σ₁, hrun, ?_⟩
  simpa [matchesAt_pointRow_state] using
    regEqExpected_after_computeFracLocal2_of_run
      (k := k) hk c hrun

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

theorem opsForPointWithProduct_returns_to_original
  {k : Nat} (hk : 0 < k) (head : Point) :
  run? (opsForPointWithProduct hk head) State.start_state = some State.start_state := by {
    cases head with
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
        | frac c =>
            unfold opsForPointWithProduct
            by_cases hc : c = 0
            · simp [hc, run?, applyOp?]
            · simp [hc, run?_append]
              have:= computeFracLocal2_some_state k hk c State.start_state
              rcases this with ⟨σ₁,this⟩
              simp[this,applyOp?]
              apply State.run?_inverse_undoes_WF
              apply computeFracLocal2_Valid
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

lemma progConsumesPts_append
  {k : Nat} (hk : 0 < k)
  {p q : Prog k} {σ σret : State k} {a b : List Point}
  (hp : ProgConsumesPts hk σ p a)
  (hrun : run? p σ = some σret)
  (hq : ProgConsumesPts hk σret q b) :
  ProgConsumesPts hk σ (p ++ q) (a ++ b) := by
  revert σ a
  induction p with
  | nil =>
      intro σ a hp hrun
      simp [ProgConsumesPts] at hp hrun ⊢
      subst hp
      subst hrun
      simpa using hq
  | cons op ps ih =>
      intro σ a hp hrun
      cases op with
      | shiftL i n =>
          simp [ProgConsumesPts] at hp ⊢
          rcases hp with ⟨σ', hstep, htail⟩
          refine ⟨σ', hstep, ?_⟩
          apply ih htail
          simpa [run?, hstep] using hrun
      | shiftR i n =>
          simp [ProgConsumesPts] at hp ⊢
          rcases hp with ⟨σ', hstep, htail⟩
          refine ⟨σ', hstep, ?_⟩
          apply ih htail
          simpa [run?, hstep] using hrun
      | negate i =>
          simp [ProgConsumesPts] at hp ⊢
          rcases hp with ⟨σ', hstep, htail⟩
          refine ⟨σ', hstep, ?_⟩
          apply ih htail
          simpa [run?, hstep] using hrun
      | addScaled dst src negSrc sh =>
          simp [ProgConsumesPts] at hp ⊢
          refine ih hp ?_
          simpa [run?, applyOp?] using hrun
      | phaseProduct i =>
          simp [ProgConsumesPts] at hp ⊢
          rcases hp with ⟨pt, ptsTail, hpts, hmatch, htail⟩
          subst hpts
          refine ⟨pt, ptsTail ++ b, by simp, hmatch, ?_⟩
          apply ih htail
          simpa [run?, applyOp?] using hrun

lemma progConsumesPts_of_noPhase_run
  {k : Nat} (hk : 0 < k)
  {p : Prog k} {σ σ' : State k}
  (hNP : NoPhase p)
  (hrun : run? p σ = some σ') :
  ProgConsumesPts hk σ p [] := by
  revert σ
  induction p with
  | nil =>
      intro σ hrun
      simp [ProgConsumesPts]
  | cons op ps ih =>
      intro σ hrun
      have hNP_tail : NoPhase ps := by
        intro i hi
        exact hNP i (by simp [hi])
      cases op with
      | shiftL i n =>
          cases hstep : applyOp? (k := k) σ (valid_ops.shiftL i n) with
          | none =>
              simp [run?, hstep] at hrun
          | some τ =>
              simp [ProgConsumesPts]
              exact ⟨τ, hstep, ih hNP_tail (by simpa [run?, hstep] using hrun)⟩
      | shiftR i n =>
          cases hstep : applyOp? (k := k) σ (valid_ops.shiftR i n) with
          | none =>
              simp [run?, hstep] at hrun
          | some τ =>
              simp [ProgConsumesPts]
              exact ⟨τ, hstep, ih hNP_tail (by simpa [run?, hstep] using hrun)⟩
      | negate i =>
          cases hstep : applyOp? (k := k) σ (valid_ops.negate i) with
          | none =>
              simp [run?, hstep] at hrun
          | some τ =>
              simp [ProgConsumesPts]
              exact ⟨τ, hstep, ih hNP_tail (by simpa [run?, hstep] using hrun)⟩
      | addScaled dst src negSrc sh =>
          simp [ProgConsumesPts, applyOp?]
          exact ih hNP_tail (by simpa [run?, applyOp?] using hrun)
      | phaseProduct i =>
          have : valid_ops.phaseProduct (k := k) i ∉ valid_ops.phaseProduct i :: ps :=
            hNP i
          simp at this

lemma opsForPointWithProduct_ProgConsumesPts
  {k : Nat} (hk : 0 < k) (head : Point) :
  ProgConsumesPts hk State.start_state (opsForPointWithProduct hk head) [head] := by
  cases head with
  | int x =>
      unfold opsForPointWithProduct
      let l : Prog k := computeLocal2 (k := k) hk x
      obtain ⟨σ₁, hrun₁, hmatch⟩ := computeLocal2_matches_row_start (k := k) hk x
      have hbuildNP : NoPhase l := by
        dsimp [l]
        rw [computeLocal_eq]
        exact computeLocal_NoPhase (k := k) hk x
      have hbuildC : ProgConsumesPts hk (State.start_state (k := k)) l [] :=
        progConsumesPts_of_noPhase_run (k := k) hk hbuildNP (by simpa [l] using hrun₁)
      have hphaseC :
          ProgConsumesPts hk σ₁ [valid_ops.phaseProduct (finZero hk)] [Point.int x] := by
        simp [ProgConsumesPts, hmatch]
      have hprefixC :
          ProgConsumesPts hk (State.start_state (k := k))
            (l ++ [valid_ops.phaseProduct (finZero hk)]) [Point.int x] := by
        simpa using
          progConsumesPts_append (k := k) hk
            (p := l) (q := [valid_ops.phaseProduct (finZero hk)])
            (σ := State.start_state (k := k)) (σret := σ₁)
            (a := []) (b := [Point.int x])
            hbuildC (by simpa [l] using hrun₁) hphaseC
      have hprefixRun :
          run? (l ++ [valid_ops.phaseProduct (finZero hk)]) (State.start_state (k := k))
            = some σ₁ := by
        simp [run?_append, hrun₁, l, applyOp?]
      have hcleanupRun :
          run? (apply_Op_inverse l) σ₁ = some (State.start_state (k := k)) := by
        dsimp [l]
        exact
          State.run?_inverse_undoes_WF
            (computeLocal2 (k := k) hk x)
            (computeLocal2_Valid (k := k) (z := x) hk)
            (State.start_state (k := k)) σ₁ hrun₁
      have hcleanupNP : NoPhase (apply_Op_inverse l) := by
        dsimp [l]
        rw [computeLocal_eq]
        exact (computeLocal_NoPhase_2 (k := k) hk x).2
      have hcleanupC : ProgConsumesPts hk σ₁ (apply_Op_inverse l) [] :=
        progConsumesPts_of_noPhase_run (k := k) hk hcleanupNP hcleanupRun
      simpa [l, List.append_assoc] using
        progConsumesPts_append (k := k) hk
          (p := l ++ [valid_ops.phaseProduct (finZero hk)])
          (q := apply_Op_inverse l)
          (σ := State.start_state (k := k)) (σret := σ₁)
          (a := [Point.int x]) (b := [])
          hprefixC hprefixRun hcleanupC
  | frac c =>
      unfold opsForPointWithProduct
      by_cases hc : c = 0
      · subst c
        simp [ProgConsumesPts]
        let i : Fin k := finLast hk
        have hmatch :
            matchesAt_pointRow_state (k := k) hk (State.start_state (k := k)) i (Point.frac 0)
            = true := by
          unfold matchesAt_pointRow_state
          apply List.all_eq_true.mpr
          intro j _
          apply decide_eq_true_iff.mpr
          by_cases hj : j = i
          · subst j
            simp [expectedRow, i, finLast]
          · have hjlt : j.val < k - 1 := by
              have hjle : j.val ≤ k - 1 := Nat.le_pred_of_lt j.isLt
              have hjne : j.val ≠ k - 1 := by
                intro hv
                apply hj
                apply Fin.ext
                simpa [i, finLast] using hv
              omega
            have hpos : 0 < k - 1 - j.val := by omega
            have hpow : (0 : Int) ^ (k - 1 - j.val) = 0 :=
              zero_pow (Nat.ne_of_gt hpos)
            have hjLast : ¬j = ⟨k - 1, last_lt hk⟩ := by
              intro hEq
              apply hj
              apply Fin.ext
              simpa [i, finLast] using congrArg Fin.val hEq
            simp [expectedRow, i, finLast, hjLast, hpow]
        exact hmatch
      · simp [hc]
        let l : Prog k := computeFracLocal2 (k := k) hk c
        obtain ⟨σ₁, hrun₁, hmatch⟩ := computeFracLocal2_matches_row_start (k := k) hk c
        have hbuildNP : NoPhase l := by
          dsimp [l]
          exact computeFracLocal2_NoPhase (k := k) hk c
        have hbuildC : ProgConsumesPts hk (State.start_state (k := k)) l [] :=
          progConsumesPts_of_noPhase_run (k := k) hk hbuildNP (by simpa [l] using hrun₁)
        have hphaseC :
            ProgConsumesPts hk σ₁ [valid_ops.phaseProduct (finLast hk)] [Point.frac c] := by
          simp [ProgConsumesPts, hmatch]
        have hprefixC :
            ProgConsumesPts hk (State.start_state (k := k))
              (l ++ [valid_ops.phaseProduct (finLast hk)]) [Point.frac c] := by
          simpa using
            progConsumesPts_append (k := k) hk
              (p := l) (q := [valid_ops.phaseProduct (finLast hk)])
              (σ := State.start_state (k := k)) (σret := σ₁)
              (a := []) (b := [Point.frac c])
              hbuildC (by simpa [l] using hrun₁) hphaseC
        have hprefixRun :
            run? (l ++ [valid_ops.phaseProduct (finLast hk)]) (State.start_state (k := k))
              = some σ₁ := by
          simp [run?_append, hrun₁, l, applyOp?]
        have hcleanupRun :
            run? (apply_Op_inverse l) σ₁ = some (State.start_state (k := k)) := by
          dsimp [l]
          exact
            State.run?_inverse_undoes_WF
              (computeFracLocal2 (k := k) hk c)
              (computeFracLocal2_Valid (k := k) (c := c) hk)
              (State.start_state (k := k)) σ₁ hrun₁
        have hcleanupNP : NoPhase (apply_Op_inverse l) := by
          dsimp [l]
          exact (computeFracLocal2_NoPhase_2 (k := k) hk c).2
        have hcleanupC : ProgConsumesPts hk σ₁ (apply_Op_inverse l) [] :=
          progConsumesPts_of_noPhase_run (k := k) hk hcleanupNP hcleanupRun
        simpa [l, List.append_assoc] using
          progConsumesPts_append (k := k) hk
            (p := l ++ [valid_ops.phaseProduct (finLast hk)])
            (q := apply_Op_inverse l)
            (σ := State.start_state (k := k)) (σret := σ₁)
            (a := [Point.frac c]) (b := [])
            hprefixC hprefixRun hcleanupC

theorem genOpsWithProduct_ProgConsumesPts
  {k : Nat} (hk : 0 < k) (pts : List Point) :
  ProgConsumesPts hk State.start_state (genOpsWithProduct hk pts) pts := by
  induction pts with
  | nil =>
      simp [genOpsWithProduct, ProgConsumesPts]
  | cons head tail ih =>
      simp [genOpsWithProduct]
      simpa using
        progConsumesPts_append (k := k) hk
          (p := opsForPointWithProduct hk head)
          (q := genOpsWithProduct hk tail)
          (σ := State.start_state (k := k))
          (σret := State.start_state (k := k))
          (a := [head]) (b := tail)
          (opsForPointWithProduct_ProgConsumesPts (k := k) hk head)
          (opsForPointWithProduct_returns_to_original (k := k) hk head)
          ih

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
        |frac c => {
          by_cases hc : c = 0
          · subst c
            simp
            let i : Fin k := finLast hk
            have hmatch :
                matchesAt_pointRow_state (k := k) hk (State.start_state (k := k)) i (Point.frac 0)
                = true := by
              unfold matchesAt_pointRow_state
              apply List.all_eq_true.mpr
              intro j _
              apply decide_eq_true_iff.mpr
              by_cases hj : j = i
              · subst j
                simp [expectedRow, i, finLast]
              · have hjlt : j.val < k - 1 := by
                  have hjle : j.val ≤ k - 1 := Nat.le_pred_of_lt j.isLt
                  have hjne : j.val ≠ k - 1 := by
                    intro hv
                    apply hj
                    apply Fin.ext
                    simpa [i, finLast] using hv
                  omega
                have hpos : 0 < k - 1 - j.val := by omega
                have hpow : (0 : Int) ^ (k - 1 - j.val) = 0 :=
                  zero_pow (Nat.ne_of_gt hpos)
                have hjLast : ¬j = ⟨k - 1, last_lt hk⟩ := by
                  intro hEq
                  apply hj
                  apply Fin.ext
                  simpa [i, finLast] using congrArg Fin.val hEq
                simp [expectedRow, i, finLast, hjLast, hpow]
            refine PhaseProductCoverageM.step_phase
              (M := matchesAt_pointRow_state hk)
              (i := i)
              (ps := [])
              (σ := State.start_state (k := k))
              (pts := [Point.frac 0])
              (pts' := []) ?consume ?rest
            · simp [List.eraseFirstMatch?, hmatch]
            · exact PhaseProductCoverageM.nil
          · simp [hc]
            have hbuild :
                PhaseProductCoverage hk
                  (computeFracLocal2 (k := k) hk c)
                  (State.start_state (k := k)) [] :=
              cover_computeFracLocal2_nil (k := k) hk (State.start_state (k := k)) c

            obtain ⟨σ₁, hrun₁, hmatch⟩ := computeFracLocal2_matches_row_start (k := k) hk c

            have hphase :
                PhaseProductCoverage hk ([valid_ops.phaseProduct (finLast hk)]) σ₁ [Point.frac c] := by
              refine PhaseProductCoverageM.step_phase
                (M := matchesAt_pointRow_state hk (k := k))
                (i := finLast hk) (ps := []) (σ := σ₁)
                (pts := [Point.frac c]) (pts' := []) ?eraseFrac ?tailFrac
              ·
                simpa [List.eraseFirstMatch?] using
                  eraseFirstMatch?_head_true
                    (fun pt => matchesAt_pointRow_state hk (k := k) σ₁ (finLast hk) pt)
                    (Point.frac c) [] hmatch
              · simpa using PhaseProductCoverageM.nil (M := matchesAt_pointRow_state hk (k := k)) (σ := σ₁)
            have huncompute : PhaseProductCoverage hk
                    (apply_Op_inverse (computeFracLocal2 (k := k) hk c)) σ₁ [] :=
              cover_applyInverse_computeFracLocal2_nil (k := k) hk σ₁ c

            have hprefix :
                PhaseProductCoverage hk
                  (computeFracLocal2 (k := k) hk c ++ [valid_ops.phaseProduct (finLast hk)])
                  (State.start_state (k := k)) [Point.frac c] :=
              phaseProduct_coverage_check_append_aux hk
                (p := computeFracLocal2 (k := k) hk c)
                (q := [valid_ops.phaseProduct (finLast hk)])
                (σ := State.start_state (k := k)) (σret := σ₁)
                (a := []) (b := [Point.frac c])
                (hp := hbuild) (hrun₁) (hphase)

            simpa [List.append_assoc]
              using phaseProduct_coverage_check_append_aux hk
                (p := computeFracLocal2 (k := k) hk c ++ [valid_ops.phaseProduct (finLast hk)])
                (q := apply_Op_inverse (computeFracLocal2 (k := k) hk c))
                (σ := State.start_state (k := k)) (σret := σ₁)
                (a := [Point.frac c]) (b := [])
                (hp := hprefix) (by simp[run?_append,hrun₁,applyOp?])
                (huncompute)
        }
      }
      {
        assumption
      }
    }
