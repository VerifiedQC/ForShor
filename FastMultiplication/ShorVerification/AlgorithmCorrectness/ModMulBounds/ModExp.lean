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
        ‖qs.eval
            (ModExpConfig.approxGate
              (Basis := qs.Basis) cfg) ψ
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

