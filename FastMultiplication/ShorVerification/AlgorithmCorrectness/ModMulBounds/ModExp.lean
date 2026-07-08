import FastMultiplication.ShorVerification.AlgorithmCorrectness.ModMulBounds.FinalModMul

open Shor

universe v

/-!
# Modular-Exponentiation Bound

Focus theorem: `modExpApprox_valid_dist`.

This file lifts the modular-multiplication bound through the tail recursion for
modular exponentiation and packages the final modular-exponentiation config.
-/

/-! =========================================================
    Tail side-condition reindexing
========================================================= -/

lemma modExpTailLayout_tail
    (x data work : Reg) (flag q n : ℕ)
    (h : ModExpTailLayout x data work flag q (n + 1)) :
    ModExpTailLayout x data work flag (q + 1) n := by
  rcases h with ⟨hxq, hqhi, hctrl⟩
  refine ⟨?_, ?_, ?_⟩
  · omega
  · omega
  · intro j hj
    have h' := hctrl (j + 1) (by omega)
    have hq :
        q + (j + 1) = (q + 1) + j := by
      omega
    simpa [hq] using h'

lemma modExpTailArithmeticOK_tail
    (a N : ℕ) (x : Reg)
    (q n : ℕ)
    (h : ModExpTailArithmeticOK a N x q (n + 1)) :
    ModExpTailArithmeticOK a N x (q + 1) n := by
  intro j hj
  have h' := h (j + 1) (by omega)
  dsimp at h' ⊢
  have hq :
      q + (j + 1) = (q + 1) + j := by
    omega
  simpa [hq] using h'

/--
The ideal controlled multiplication preserves the valid modular-input
subspace described by this configuration.
-/
theorem ideal_preserves_valid
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [Spec]
    [IdealCtrlModMulExactSemantics qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (ψ : qs.State)
    (hψ : cfg.ValidState qs ψ) :
    cfg.ValidState qs
      (qs.eval (ModMulConfig.idealGate cfg) ψ) := by
  simpa [ModMulConfig.ValidState, ModMulConfig.idealGate] using
    (idealCtrlModMul_preserves_valid
      qs
      cfg.c
      cfg.env.N
      cfg.env.data
      cfg.env.work
      cfg.flag
      cfg.ctrl
      cfg.env.modulus_gt_one
      cfg.env.data_capacity
      cfg.coprime
      cfg.layout
      ψ
      hψ)


/-- Uniform hybrid bound for a tail of modular exponentiation. -/
theorem modExpApproxSteps_valid_dist_uniform
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [Spec]
    [IdealCtrlModMulExactSemantics qs]
    [GateSemanticsFacts qs]
    [ModMulPrimitiveSemantics qs] :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (η : ℝ)
        (a N : ℕ) (x data work : Reg) (flag q n : ℕ) (ψ : qs.State),
        1 < N →
        N ≤ ASize data →
        Algorithm1Precision η data work →
        ModExpTailLayout x data work flag q n →
        ModExpTailArithmeticOK a N x q n →
        ψ ∈ ValidModMulState qs N data work flag →
        ‖ψ‖ = 1 →
        ‖
          qs.eval
            (modExpApproxStepsValid
              (Basis := qs.Basis)
              a N x data work flag q n)
            ψ
          -
          qs.eval
            (modExpIdealSteps qs a N x data q n)
            ψ‖
          ≤ (n : ℝ) * stepErr K η := by
  rcases modMul_approx_valid_dist_uniform (qs := qs) with
    ⟨K, hK_nonneg, hmodMul⟩

  refine ⟨K, hK_nonneg, ?_⟩
  intro η a N x data work flag q n ψ
    hN hsize hprecision hLayout hArithmetic hValid hNorm

  revert q ψ
  induction n with
  | zero =>
      intro q ψ hLayout hArithmetic hValid hNorm
      simp [modExpApproxStepsValid, modExpIdealSteps, qs.eval_id]

  | succ n ih =>
      intro q ψ hLayout hArithmetic hValid hNorm

      have hTailLayout :
          ModExpTailLayout x data work flag (q + 1) n :=
        modExpTailLayout_tail x data work flag q n hLayout

      have hTailArithmetic :
          ModExpTailArithmeticOK a N x (q + 1) n :=
        modExpTailArithmeticOK_tail a N x q n hArithmetic

      rcases hLayout with ⟨hxq, hqhi, hControls⟩

      let e : ℕ := q - x.lo
      let c : ℕ := (a ^ (2 ^ e)) % N

      have hHeadLayout :
          ModMulCoreLayout data work flag q :=
        hControls 0 (by omega)

      have hHeadArithmetic :
          Nat.Coprime c N := by
        have h0 := hArithmetic 0 (by omega)
        simpa [c, e] using h0

      let headEnv : Algorithm1Env η :=
        { N := N
          data := data
          work := work
          modulus_gt_one := hN
          data_capacity := hsize
          precision := hprecision }

      let headCfg : ModMulConfig η :=
        { env := headEnv
          c := c
          flag := flag
          ctrl := q
          coprime := hHeadArithmetic
          layout := hHeadLayout }

      let A : Gate :=
        CmodMulInPlaceCore
          (Basis := qs.Basis)
          c N q data work flag

      let I : Gate :=
        Spec.idealCtrlModMul c N data q

      let RA : Gate :=
        modExpApproxStepsValid
          (Basis := qs.Basis)
          a N x data work flag (q + 1) n

      let RI : Gate :=
        modExpIdealSteps qs a N x data (q + 1) n

      have hApprox :
          modExpApproxStepsValid
              (Basis := qs.Basis)
              a N x data work flag q (n + 1)
            =
          A ;; RA := by
        simp [modExpApproxStepsValid, A, RA, c, e]

      have hIdeal :
          modExpIdealSteps qs a N x data q (n + 1)
            =
          I ;; RI := by
        simp [modExpIdealSteps, I, RI, c, e]

      let ψA0 : qs.State := qs.eval A ψ
      let ψI0 : qs.State := qs.eval I ψ

      have hHeadValid :
          ModMulConfig.ValidState qs headCfg ψ := by
        simpa [
          ModMulConfig.ValidState,
          headCfg,
          headEnv
        ] using hValid

      have hHeadUnit :
          ModMulConfig.ValidUnitState qs headCfg ψ :=
        ⟨hHeadValid, hNorm⟩

      have hHead :
          ‖ψA0 - ψI0‖ ≤ stepErr K η := by
        simpa [
          ψA0,
          ψI0,
          A,
          I,
          ModMulConfig.approxGate,
          ModMulConfig.idealGate,
          headCfg,
          headEnv
        ] using
          (hmodMul η headCfg ψ hHeadUnit)

      have hψI0Norm : ‖ψI0‖ = 1 := by
        calc
          ‖ψI0‖ = ‖ψ‖ := by
            simpa [ψI0] using
              (eval_norm_preserved qs I ψ)
          _ = 1 := hNorm

      have hψI0ValidCfg :
          ModMulConfig.ValidState qs headCfg ψI0 := by
        simpa [
          ψI0,
          I,
          ModMulConfig.idealGate,
          headCfg,
          headEnv
        ] using
          (ideal_preserves_valid qs headCfg ψ hHeadValid)

      have hψI0Valid :
          ψI0 ∈ ValidModMulState qs N data work flag := by
        simpa [
          ModMulConfig.ValidState,
          headCfg,
          headEnv
        ] using hψI0ValidCfg

      have hTail :
          ‖qs.eval RA ψI0 - qs.eval RI ψI0‖
            ≤ (n : ℝ) * stepErr K η := by
        have h :=
          ih
            (q := q + 1)
            (ψ := ψI0)
            hTailLayout
            hTailArithmetic
            hψI0Valid
            hψI0Norm
        simpa [RA, RI] using h

      have hIso :
          ‖qs.eval RA ψA0 - qs.eval RA ψI0‖
            =
          ‖ψA0 - ψI0‖ := by
        exact
          eval_isometry
            qs
            RA
            (by
              intro φ χ
              simpa using qs.inner_preserved RA φ χ)
            ψA0
            ψI0

      have hTriangle :
          ‖qs.eval RA ψA0 - qs.eval RI ψI0‖
            ≤
          ‖qs.eval RA ψA0 - qs.eval RA ψI0‖
            +
            ‖qs.eval RA ψI0 - qs.eval RI ψI0‖ := by
        rw [
          show
            qs.eval RA ψA0 - qs.eval RI ψI0
              =
            (qs.eval RA ψA0 - qs.eval RA ψI0)
              +
            (qs.eval RA ψI0 - qs.eval RI ψI0)
          by abel
        ]
        exact norm_add_le _ _

      have hMain :
          ‖qs.eval RA ψA0 - qs.eval RI ψI0‖
            ≤ ((n + 1 : ℕ) : ℝ) * stepErr K η := by
        calc
          ‖qs.eval RA ψA0 - qs.eval RI ψI0‖
              ≤
            ‖qs.eval RA ψA0 - qs.eval RA ψI0‖
              +
              ‖qs.eval RA ψI0 - qs.eval RI ψI0‖ := hTriangle
          _ =
            ‖ψA0 - ψI0‖
              +
              ‖qs.eval RA ψI0 - qs.eval RI ψI0‖ := by
              rw [hIso]
          _ ≤
            stepErr K η
              +
              (n : ℝ) * stepErr K η := by
              exact add_le_add hHead hTail
          _ =
            ((n + 1 : ℕ) : ℝ) * stepErr K η := by
              push_cast
              ring

      simpa [
        hApprox,
        hIdeal,
        ψA0,
        ψI0,
        qs.eval_seq
      ] using hMain

/-- Uniform approximation theorem for full modular exponentiation. -/
theorem modExpApprox_valid_dist_uniform
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [Spec]
    [IdealCtrlModMulExactSemantics qs]
    [GateSemanticsFacts qs]
    [ModMulPrimitiveSemantics qs] :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (η : ℝ) (cfg : ModExpConfig η) (ψ : qs.State),
        ModExpConfig.ValidUnitState qs cfg ψ →
        ‖qs.eval (ModExpConfig.approxGate (Basis := qs.Basis) cfg) ψ
          -
          qs.eval (ModExpConfig.idealGate qs cfg) ψ‖
        ≤ (tbits cfg.x : ℝ) * stepErr K η := by
  rcases modExpApproxSteps_valid_dist_uniform (qs := qs) with
    ⟨K, hK_nonneg, hSteps⟩

  refine ⟨K, hK_nonneg, ?_⟩
  intro η cfg ψ hψ
  rcases hψ with ⟨hValid, hNorm⟩

  have hTailLayout :
      ModExpTailLayout
        cfg.x
        cfg.env.data
        cfg.env.work
        cfg.flag
        cfg.x.lo
        (tbits cfg.x) := by
    simpa [ModExpLayout] using cfg.layout

  have hTailArithmetic :
      ModExpTailArithmeticOK
        cfg.a
        cfg.env.N
        cfg.x
        cfg.x.lo
        (tbits cfg.x) := by
    simpa [ModExpArithmeticOK] using cfg.arithmetic

  have h :=
    hSteps
      η
      cfg.a
      cfg.env.N
      cfg.x
      cfg.env.data
      cfg.env.work
      cfg.flag
      cfg.x.lo
      (tbits cfg.x)
      ψ
      cfg.env.modulus_gt_one
      cfg.env.data_capacity
      cfg.env.precision
      hTailLayout
      hTailArithmetic
      hValid
      hNorm

  simpa [
    ModExpConfig.approxGate,
    ModExpConfig.idealGate,
    modExpApproxValid,
    modExpIdeal'
  ] using h

-- /--
-- Real-overlap consequence of the uniform tail distance bound.

-- If the approximate and ideal modular-exponentiation tails differ by at most
-- `n * stepErr K η` in norm, their real overlap differs from `1` by at most
-- `n^2 * K * η`.
-- -/
-- theorem modExpApproxSteps_valid_re_overlap_uniform
--     (qs : QSemantics)
--     [RegEncoding qs.Basis]
--     [ExtRegEncoding qs.Basis]
--     [Spec]
--     [IdealCtrlModMulExactSemantics qs]
--     [GateSemanticsFacts qs]
--     [ModMulPrimitiveSemantics qs] :
--     ∃ K : ℝ, 0 ≤ K ∧
--       ∀ (η : ℝ)
--         (a N : ℕ) (x data work : Reg) (flag q n : ℕ) (ψ : qs.State),
--         1 < N →
--         N ≤ ASize data →
--         Algorithm1Precision η data work →
--         ModExpTailLayout x data work flag q n →
--         ModExpTailArithmeticOK a N x q n →
--         ψ ∈ ValidModMulState qs N data work flag →
--         ‖ψ‖ = 1 →
--         1 -
--             Complex.re
--               (inner ℂ
--                 (qs.eval (modExpApproxStepsValid (Basis := qs.Basis) a N x data work flag q n) ψ)
--                 (qs.eval (modExpIdealSteps qs a N x data q n) ψ))
--           ≤
--         ((n : ℝ) ^ 2 * K) * η := by
--   rcases modExpApproxSteps_valid_dist_uniform qs with
--     ⟨K, hK, hdist⟩

--   refine ⟨K, hK, ?_⟩
--   intro η a N x data work flag q n ψ
--     hN hcap hprecision hlayout harith hvalid hnorm

--   let A : qs.State :=
--     qs.eval
--       (modExpApproxStepsValid
--         (Basis := qs.Basis)
--         a N x data work flag q n)
--       ψ

--   let I : qs.State :=
--     qs.eval
--       (modExpIdealSteps qs a N x data q n)
--       ψ

--   have hη : 0 ≤ η :=
--     le_of_lt hprecision.1

--   have hdistAI :
--       ‖A - I‖ ≤ (n : ℝ) * stepErr K η := by
--     simpa [A, I] using
--       hdist η a N x data work flag q n ψ
--         hN hcap hprecision hlayout harith hvalid hnorm

--   have eval_norm
--       (G : Gate) (φ : qs.State) :
--       ‖qs.eval G φ‖ = ‖φ‖ := by
--     have hIso :
--         ‖qs.eval G φ - qs.eval G 0‖
--           =
--         ‖φ - 0‖ := by
--       exact
--         eval_isometry qs G
--           (by
--             intro ξ ζ
--             simpa using qs.inner_preserved G ξ ζ)
--           φ 0
--     simpa[QSemantics.eval_zero] using hIso

--   have hA : ‖A‖ = 1 := by
--     dsimp [A]
--     calc
--       ‖qs.eval
--           (modExpApproxStepsValid
--             (Basis := qs.Basis)
--             a N x data work flag q n)
--           ψ‖
--           =
--         ‖ψ‖ :=
--         eval_norm
--           (modExpApproxStepsValid
--             (Basis := qs.Basis)
--             a N x data work flag q n)
--           ψ
--       _ = 1 := hnorm

--   have hI : ‖I‖ = 1 := by
--     dsimp [I]
--     calc
--       ‖qs.eval (modExpIdealSteps qs a N x data q n) ψ‖
--           =
--         ‖ψ‖ :=
--         eval_norm (modExpIdealSteps qs a N x data q n) ψ
--       _ = 1 := hnorm

--   have hbound_nonneg :
--       0 ≤ (n : ℝ) * stepErr K η := by
--     apply mul_nonneg
--     · positivity
--     · unfold stepErr
--       exact Real.sqrt_nonneg _

--   have hdistSq :
--       ‖A - I‖ ^ 2
--         ≤
--       ((n : ℝ) * stepErr K η) ^ 2 := by
--     have hfactor :
--         0 ≤
--           ((n : ℝ) * stepErr K η - ‖A - I‖) *
--             ((n : ℝ) * stepErr K η + ‖A - I‖) := by
--       apply mul_nonneg
--       · exact sub_nonneg.mpr hdistAI
--       · exact add_nonneg hbound_nonneg (norm_nonneg _)
--     nlinarith

--   have hrad : 0 ≤ 2 * (K * η) := by
--     exact mul_nonneg (by norm_num) (mul_nonneg hK hη)

--   have hstepSq :
--       (stepErr K η) ^ 2 = 2 * (K * η) := by
--     unfold stepErr
--     simpa using Real.sq_sqrt hrad

--   have hnormSub :
--       ‖A - I‖ ^ 2
--         =
--       2 * (1 - Complex.re (inner ℂ A I)) := by
--     have h :=
--       norm_sub_sq (𝕜 := ℂ) A I
--     rw [hA, hI] at h
--     simp[h]
--     nlinarith [h]

--   change
--     1 - Complex.re (inner ℂ A I)
--       ≤ ((n : ℝ) ^ 2 * K) * η

--   calc
--     1 - Complex.re (inner ℂ A I)
--         =
--       ‖A - I‖ ^ 2 / 2 := by
--         rw [hnormSub]
--         ring
--     _ ≤
--       ((n : ℝ) * stepErr K η) ^ 2 / 2 := by
--         nlinarith
--     _ =
--       ((n : ℝ) ^ 2 * (stepErr K η) ^ 2) / 2 := by
--         ring
--     _ =
--       ((n : ℝ) ^ 2 * K) * η := by
--         rw [hstepSq]
--         ring
