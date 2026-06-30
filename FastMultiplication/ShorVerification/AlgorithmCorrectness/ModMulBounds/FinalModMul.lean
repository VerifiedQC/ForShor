import FastMultiplication.ShorVerification.AlgorithmCorrectness.ModMulBounds.Step34Exact

open Shor

universe v

/-!
# Final Modular-Multiplication Bound

Focus theorem: `modMul_approx_valid_dist`.

This file combines the Step 1, Step 2, and Step 5 budgets into the final
Algorithm-1 modular-multiplication distance bound.
-/

lemma three_stepErr_le
    {K₁ K₂ K₅ η : ℝ}
    (hη : 0 ≤ η)
    (hK₁ : 0 ≤ K₁)
    (hK₂ : 0 ≤ K₂)
    (hK₅ : 0 ≤ K₅) :
    stepErr K₁ η + stepErr K₂ η + stepErr K₅ η
      ≤
    stepErr (3 * (K₁ + K₂ + K₅)) η := by
  unfold stepErr
  let a : ℝ := 2 * (K₁ * η)
  let b : ℝ := 2 * (K₂ * η)
  let c : ℝ := 2 * (K₅ * η)
  have ha : 0 ≤ a := by
    dsimp [a]
    nlinarith [mul_nonneg hK₁ hη]
  have hb : 0 ≤ b := by
    dsimp [b]
    nlinarith [mul_nonneg hK₂ hη]
  have hc : 0 ≤ c := by
    dsimp [c]
    nlinarith [mul_nonneg hK₅ hη]
  have htarget :
      2 * ((3 * (K₁ + K₂ + K₅)) * η) = 3 * (a + b + c) := by
    dsimp [a, b, c]
    ring
  change Real.sqrt a + Real.sqrt b + Real.sqrt c
      ≤ Real.sqrt (2 * ((3 * (K₁ + K₂ + K₅)) * η))
  rw [htarget]
  apply Real.le_sqrt_of_sq_le
  have hsqa : (Real.sqrt a) ^ 2 = a := by
    simpa [pow_two] using Real.sq_sqrt ha
  have hsqb : (Real.sqrt b) ^ 2 = b := by
    simpa [pow_two] using Real.sq_sqrt hb
  have hsqc : (Real.sqrt c) ^ 2 = c := by
    simpa [pow_two] using Real.sq_sqrt hc
  nlinarith
    [sq_nonneg (Real.sqrt a - Real.sqrt b),
     sq_nonneg (Real.sqrt a - Real.sqrt c),
     sq_nonneg (Real.sqrt b - Real.sqrt c)]

lemma norm_chain_three
    {E : Type*}
    [NormedAddCommGroup E]
    (x₀ x₁ x₂ x₃ : E) :
    ‖x₀ - x₃‖
      ≤
    ‖x₀ - x₁‖
      + ‖x₁ - x₂‖
      + ‖x₂ - x₃‖ := by
  calc
    ‖x₀ - x₃‖
        =
      ‖(x₀ - x₁) + (x₁ - x₂) + (x₂ - x₃)‖ := by
        congr 1
        abel
    _ ≤
      ‖(x₀ - x₁) + (x₁ - x₂)‖ + ‖x₂ - x₃‖ := by
        simpa using
          norm_add_le
            ((x₀ - x₁) + (x₁ - x₂))
            (x₂ - x₃)
    _ ≤
      (‖x₀ - x₁‖ + ‖x₁ - x₂‖) + ‖x₂ - x₃‖ := by
        gcongr
        exact norm_add_le _ _
    _ =
      ‖x₀ - x₁‖ + ‖x₁ - x₂‖ + ‖x₂ - x₃‖ := by
        ring

/--
Uniform quantitative modular-multiplication approximation bound.
-/
theorem modMul_approx_valid_dist_uniform
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [Spec]
    [GateSemanticsFacts qs]
    [IdealCtrlModMulExactSemantics qs]
    [ModMulPrimitiveSemantics qs] :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (η : ℝ) (cfg : ModMulConfig η) (ψ : qs.State),
        ModMulConfig.ValidUnitState qs cfg ψ →
        ‖qs.eval
            (ModMulConfig.approxGate (Basis := qs.Basis) cfg) ψ
          -
          qs.eval
            (ModMulConfig.idealGate cfg) ψ‖
        ≤ stepErr K η := by
  classical

  rcases alg1_qpe_tail_uniform qs with
    ⟨Cpe, hCpe, _hTail, hStep1Sq, hStep5Sq⟩

  rcases alg1_step2_good_label_branch_uniform qs with
    ⟨Cstep2, hCstep2, _hBranch, hStep2Sq⟩

  let K₁ : ℝ := Cpe / 2
  let K₂ : ℝ := Cstep2 / 2
  let K₅ : ℝ := Cpe / 2

  have hK₁ : 0 ≤ K₁ := by
    dsimp [K₁]
    exact div_nonneg hCpe (by norm_num)

  have hK₂ : 0 ≤ K₂ := by
    dsimp [K₂]
    exact div_nonneg hCstep2 (by norm_num)

  have hK₅ : 0 ≤ K₅ := by
    dsimp [K₅]
    exact div_nonneg hCpe (by norm_num)

  refine ⟨3 * (K₁ + K₂ + K₅), ?_, ?_⟩
  · nlinarith [hK₁, hK₂, hK₅]

  intro η cfg ψ hψ
  rcases hψ with ⟨hValid, hNorm⟩

  have hUnit : cfg.ValidUnitState qs ψ := ⟨hValid, hNorm⟩

  have hη : 0 ≤ η :=
    le_of_lt cfg.env.precision.1

  have sq_to_stepErr
      {C : ℝ} (hC : 0 ≤ C) {x : qs.State}
      (hsq : ‖x‖ ^ 2 ≤ C * η) :
      ‖x‖ ≤ stepErr (C / 2) η := by
    have hCη : 0 ≤ C * η :=
      mul_nonneg hC hη

    have hrad :
        2 * ((C / 2) * η) = C * η := by
      ring

    rw [stepErr, hrad]

    have hsqrt_sq :
        (Real.sqrt (C * η)) ^ 2 = C * η := by
      simpa [pow_two] using Real.sq_sqrt hCη

    nlinarith [
      norm_nonneg x,
      Real.sqrt_nonneg (C * η)
    ]

  rcases alg1_trace_of_valid qs cfg ψ hValid with
    ⟨tr, _⟩

  have hStep1Bound :
      ‖qs.eval (ModMulConfig.U1 (Basis := qs.Basis) cfg) ψ
          - tr.goodStep1‖
        ≤ stepErr K₁ η := by
    simpa [K₁] using
      (sq_to_stepErr hCpe
        (hStep1Sq η cfg ψ tr hUnit))

  have hStep2Bound :
      ‖qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
          tr.goodStep1
        - tr.afterStep2Ref‖
        ≤ stepErr K₂ η := by
    simpa [K₂] using
      (sq_to_stepErr hCstep2
        (hStep2Sq η cfg ψ tr hUnit))

  have hStep5Bound :
      ‖qs.eval (ModMulConfig.U5 (Basis := qs.Basis) cfg)
          tr.afterStep34Ref
        - qs.eval (ModMulConfig.idealGate cfg) ψ‖
        ≤ stepErr K₅ η := by
    simpa [K₅] using
      (sq_to_stepErr hCpe
        (hStep5Sq η cfg ψ tr hUnit))

  let U1 := ModMulConfig.U1 (Basis := qs.Basis) cfg
  let U2 := ModMulConfig.U2 (Basis := qs.Basis) cfg
  let U34 := ModMulConfig.U34 (Basis := qs.Basis) cfg
  let U5 := ModMulConfig.U5 (Basis := qs.Basis) cfg

  let post1 : Gate := U2 ;; U34 ;; U5
  let post2 : Gate := U34 ;; U5

  let ψ0 : qs.State :=
    qs.eval post1 (qs.eval U1 ψ)

  let ψ1 : qs.State :=
    qs.eval post1 tr.goodStep1

  let ψ2 : qs.State :=
    qs.eval post2 tr.afterStep2Ref

  let ψI : qs.State :=
    qs.eval (ModMulConfig.idealGate cfg) ψ

  have h1 :
      ‖ψ0 - ψ1‖ ≤ stepErr K₁ η := by
    have hIso :
        ‖qs.eval post1 (qs.eval U1 ψ)
            - qs.eval post1 tr.goodStep1‖
          =
        ‖qs.eval U1 ψ - tr.goodStep1‖ := by
      exact
        eval_isometry
          qs
          post1
          (by
            intro φ χ
            simpa using qs.inner_preserved post1 φ χ)
          (qs.eval U1 ψ)
          tr.goodStep1

    calc
      ‖ψ0 - ψ1‖
          =
        ‖qs.eval U1 ψ - tr.goodStep1‖ := by
          simpa [ψ0, ψ1] using hIso
      _ ≤ stepErr K₁ η := by
          simpa [U1] using hStep1Bound

  have h2 :
      ‖ψ1 - ψ2‖ ≤ stepErr K₂ η := by
    have hIso :
        ‖qs.eval post2 (qs.eval U2 tr.goodStep1)
            - qs.eval post2 tr.afterStep2Ref‖
          =
        ‖qs.eval U2 tr.goodStep1
            - tr.afterStep2Ref‖ := by
      exact
        eval_isometry
          qs
          post2
          (by
            intro φ χ
            simpa using qs.inner_preserved post2 φ χ)
          (qs.eval U2 tr.goodStep1)
          tr.afterStep2Ref

    calc
      ‖ψ1 - ψ2‖
          =
        ‖qs.eval post2 (qs.eval U2 tr.goodStep1)
            - qs.eval post2 tr.afterStep2Ref‖ := by
          simp [ψ1, ψ2, post1, post2, qs.eval_seq]
      _ =
        ‖qs.eval U2 tr.goodStep1
            - tr.afterStep2Ref‖ := hIso
      _ ≤ stepErr K₂ η := by
          simpa [U2] using hStep2Bound

  have h34 :
      qs.eval U34 tr.afterStep2Ref
        =
      tr.afterStep34Ref := by
    simpa [U34] using
      alg1_step34_reference_exact qs cfg ψ tr

  have h3 :
      ‖ψ2 - ψI‖ ≤ stepErr K₅ η := by
    calc
      ‖ψ2 - ψI‖
          =
        ‖qs.eval U5 tr.afterStep34Ref
            -
            qs.eval (ModMulConfig.idealGate cfg) ψ‖ := by
          simp [ψ2, ψI, post2, qs.eval_seq, h34]
      _ ≤ stepErr K₅ η := by
          simpa [U5] using hStep5Bound

  have hChain :
      ‖ψ0 - ψI‖
        ≤
      stepErr K₁ η
        + stepErr K₂ η
        + stepErr K₅ η := by
    calc
      ‖ψ0 - ψI‖
          ≤ ‖ψ0 - ψ1‖ + ‖ψ1 - ψ2‖ + ‖ψ2 - ψI‖ :=
            norm_chain_three ψ0 ψ1 ψ2 ψI
      _ ≤
        stepErr K₁ η
          + stepErr K₂ η
          + stepErr K₅ η := by
            gcongr

  have hBudget :
      stepErr K₁ η + stepErr K₂ η + stepErr K₅ η
        ≤
      stepErr (3 * (K₁ + K₂ + K₅)) η :=
    three_stepErr_le hη hK₁ hK₂ hK₅

  have hCore :
      qs.eval
          (ModMulConfig.approxGate (Basis := qs.Basis) cfg)
          ψ
        =
      ψ0 := by
    rw [ModMulConfig.eval_approxGate_eq_staged qs cfg ψ]
    simp [
      ModMulConfig.stagedGate,
      ψ0,
      post1,
      U1,
      U2,
      U34,
      U5,
      qs.eval_seq
    ]

  calc
    ‖qs.eval
        (ModMulConfig.approxGate (Basis := qs.Basis) cfg) ψ
      -
      qs.eval (ModMulConfig.idealGate cfg) ψ‖
        =
      ‖ψ0 - ψI‖ := by
        rw [hCore]
    _ ≤
      stepErr K₁ η
        + stepErr K₂ η
        + stepErr K₅ η := hChain
    _ ≤
      stepErr (3 * (K₁ + K₂ + K₅)) η := hBudget



