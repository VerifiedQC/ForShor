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

lemma alg1_good_badStep1_orthogonal
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (ψ : qs.State)
    (tr : Alg1Trace qs cfg ψ) :
    inner ℂ tr.goodStep1 tr.badStep1 = 0 := by
  classical

  let Sgood : Finset (Σ b : qs.Basis, Fin (ASize cfg.env.work)) :=
    tr.support.sigma fun b => alg1GoodLabels cfg b

  let Sbad : Finset (Σ b : qs.Basis, Fin (ASize cfg.env.work)) :=
    tr.support.sigma fun b =>
      Finset.univ.filter (fun t => t ∉ alg1GoodLabels cfg b)

  let α : (Σ _b : qs.Basis, Fin (ASize cfg.env.work)) → ℂ :=
    fun i => tr.inputCoeff i.1 * tr.phaseCoeff i.1 i.2

  let label : (Σ _b : qs.Basis, Fin (ASize cfg.env.work)) → qs.Basis :=
    fun i => RegEncoding.writeNat cfg.env.work i.2.1 i.1

  have hgood_flat :
      tr.goodStep1 =
        ∑ i ∈ Sgood, α i • qs.ket (label i) := by
    simp [Sgood, α, label, Alg1Trace.goodStep1, Finset.sum_sigma, Finset.smul_sum,smul_smul]

  have hbad_flat :
      tr.badStep1 =
        ∑ i ∈ Sbad, α i • qs.ket (label i) := by
    simp [Sbad, α, label, Alg1Trace.badStep1, Finset.sum_sigma, Finset.smul_sum,smul_smul]

  have hlabel_ne :
      ∀ i ∈ Sgood, ∀ j ∈ Sbad, label i ≠ label j := by
    intro i hi j hj hEq

    rcases i with ⟨b, t⟩
    rcases j with ⟨b', u⟩

    rcases Finset.mem_sigma.mp hi with ⟨hbmem, htgood⟩
    rcases Finset.mem_sigma.mp hj with ⟨hbmem', htbad⟩

    rcases
        alg1_work_label_injective
          qs cfg
          b b'
          (tr.input_good b hbmem)
          (tr.input_good b' hbmem')
          t u
          (by simpa [label] using hEq)
      with ⟨hbb, htu⟩

    subst b'
    subst u

    exact (Finset.mem_filter.mp htbad).2 htgood

  rw [hgood_flat, hbad_flat, sum_inner]
  simp[inner_sum]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  rw [inner_smul_left, inner_smul_right, qs.ket_inner_eq_zero_of_ne (hlabel_ne i hi j hj)]
  simp

/--
The coherent Step-2 replacement is genuinely `O(η)` in state norm.
-/
lemma alg1_step2_good_packet_norm_le
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [Spec]
    [GateSemanticsFacts qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (ψ : qs.State)
    (tr : Alg1Trace qs cfg ψ)
    (hunit : cfg.ValidUnitState qs ψ) :
    ‖qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
          tr.goodStep1
        - tr.afterStep2Ref‖
      ≤ 2 * Real.pi * η := by
  classical

  let Sgood : Finset (Σ _b : qs.Basis, Fin (ASize cfg.env.work)) :=
    tr.support.sigma fun b => alg1GoodLabels cfg b

  let α : (Σ _b : qs.Basis, Fin (ASize cfg.env.work)) → ℂ :=
    fun i => tr.inputCoeff i.1 * tr.phaseCoeff i.1 i.2

  let E : Fin (ASize cfg.env.work) → qs.State :=
    fun t =>
      ∑ i ∈ Sgood.filter (fun i => i.2 = t),
        α i • alg1Step2Error qs cfg i.1 i.2

  let C : ℝ := 2 * Real.pi * η

  have hη_nonneg : 0 ≤ η :=
    le_of_lt cfg.env.precision.1

  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity

  have hSgood :
      ∀ i ∈ Sgood,
        GoodModMulBasisInput
          qs cfg.env.N cfg.env.data cfg.env.work cfg.flag i.1
        ∧ i.2 ∈ alg1GoodLabels cfg i.1 := by
    intro i hi
    rcases Finset.mem_sigma.mp hi with ⟨hbmem, ht⟩
    exact ⟨tr.input_good i.1 hbmem, ht⟩

  have hflat :
      qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
          tr.goodStep1
        - tr.afterStep2Ref
      =
      ∑ i ∈ Sgood, α i • alg1Step2Error qs cfg i.1 i.2 := by
    simpa [Sgood, α, alg1Step2Error] using
      (alg1_step2_trace_error_eq_good_branch_sum qs cfg ψ tr)

  have hsplit :
      ∑ i ∈ Sgood, α i • alg1Step2Error qs cfg i.1 i.2
        =
      ∑ t : Fin (ASize cfg.env.work), E t := by
    simpa [E] using
      (alg1_step2_error_eq_sum_work_fibers qs cfg Sgood α)

  have horth :
      ∀ t ∈ (Finset.univ : Finset (Fin (ASize cfg.env.work))),
        ∀ u ∈ (Finset.univ : Finset (Fin (ASize cfg.env.work))),
          t ≠ u →
          inner ℂ (E t) (E u) = 0 := by
    simpa [E] using
      alg1_step2_work_fiber_orthogonal qs cfg Sgood α

  have hparseval :
      ‖∑ t : Fin (ASize cfg.env.work), E t‖ ^ 2
        =
      ∑ t : Fin (ASize cfg.env.work), ‖E t‖ ^ 2 :=
    norm_sq_sum_eq_sum_norm_sq_of_orthogonal_qpe
      (qs := qs)
      (Finset.univ : Finset (Fin (ASize cfg.env.work)))
      E
      horth

  have hfiber :
      ∀ t : Fin (ASize cfg.env.work),
        ‖E t‖ ^ 2
          ≤
        C ^ 2 *
          ∑ i ∈ Sgood.filter (fun i => i.2 = t), ‖α i‖ ^ 2 := by
    intro t
    by_cases hfiber : (Sgood.filter fun i => i.2 = t).Nonempty
    · rcases hfiber with ⟨i₀, hi₀⟩
      let r : ℕ := alg1TargetResidue cfg i₀.1

      have hfixed :
          ∀ i ∈ Sgood.filter (fun i => i.2 = t),
            i.2 = t ∧
            GoodModMulBasisInput
              qs cfg.env.N cfg.env.data cfg.env.work cfg.flag i.1 ∧
            i.2 ∈ alg1GoodLabels cfg i.1 ∧
            alg1TargetResidue cfg i.1 = r := by
        intro i hi
        have hiS : i ∈ Sgood := (Finset.mem_filter.mp hi).1
        have hit : i.2 = t := (Finset.mem_filter.mp hi).2
        have hiGood := hSgood i hiS

        have hi₀S : i₀ ∈ Sgood := (Finset.mem_filter.mp hi₀).1
        have hi₀t : i₀.2 = t := (Finset.mem_filter.mp hi₀).2
        have hi₀Good := hSgood i₀ hi₀S

        refine ⟨hit, hiGood.1, hiGood.2, ?_⟩
        dsimp [r]
        have hit_good : t ∈ alg1GoodLabels cfg i.1 := by
          simpa [hit] using hiGood.2
        have hi₀t_good : t ∈ alg1GoodLabels cfg i₀.1 := by
          simpa [hi₀t] using hi₀Good.2
        exact alg1_good_labels_same_work_residue
          cfg i.1 i₀.1 t hit_good hi₀t_good

      have hgood_fiber :
          ∀ i ∈ Sgood.filter (fun i => i.2 = t),
            GoodModMulBasisInput
              qs cfg.env.N cfg.env.data cfg.env.work cfg.flag i.1 := by
        intro i hi
        exact (hfixed i hi).2.1

      have hcontract :
          ‖∑ i ∈ Sgood.filter (fun i => i.2 = t),
              α i • alg1Step2Error qs cfg i.1 i.2‖ ^ 2
            ≤
          C ^ 2 *
            ‖∑ i ∈ Sgood.filter (fun i => i.2 = t),
              α i •
                qs.ket
                  (RegEncoding.writeNat cfg.env.work i.2.1 i.1)‖ ^ 2 := by
        simpa [C] using
          (alg1_step2_fixed_work_fourier_contraction
            qs η cfg
            (Sgood.filter fun i => i.2 = t)
            α t r hfixed)

      have hsource :
          ‖∑ i ∈ Sgood.filter (fun i => i.2 = t),
              α i •
                qs.ket
                  (RegEncoding.writeNat cfg.env.work i.2.1 i.1)‖ ^ 2
            =
          ∑ i ∈ Sgood.filter (fun i => i.2 = t), ‖α i‖ ^ 2 :=
        alg1_step2_fixed_work_source_energy
          qs cfg
          (Sgood.filter fun i => i.2 = t)
          α
          hgood_fiber

      calc
        ‖E t‖ ^ 2
            =
          ‖∑ i ∈ Sgood.filter (fun i => i.2 = t),
              α i • alg1Step2Error qs cfg i.1 i.2‖ ^ 2 := by
            rfl
        _ ≤
          C ^ 2 *
            ‖∑ i ∈ Sgood.filter (fun i => i.2 = t),
              α i •
                qs.ket
                  (RegEncoding.writeNat cfg.env.work i.2.1 i.1)‖ ^ 2 :=
            hcontract
        _ =
          C ^ 2 *
            ∑ i ∈ Sgood.filter (fun i => i.2 = t), ‖α i‖ ^ 2 := by
            rw [hsource]

    · have hempty : Sgood.filter (fun i => i.2 = t) = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hfiber
      simp [E, hempty]

  have henergy :
      ∑ i ∈ Sgood, ‖α i‖ ^ 2 ≤ 1 := by
    simpa [Sgood, α] using
      (alg1_step2_good_coeff_energy_le_one qs cfg ψ tr hunit)

  have henergy_fibers :
      (∑ t : Fin (ASize cfg.env.work),
        ∑ i ∈ Sgood.filter (fun i => i.2 = t), ‖α i‖ ^ 2)
        =
      ∑ i ∈ Sgood, ‖α i‖ ^ 2 :=
    alg1_step2_energy_eq_sum_work_fibers qs cfg Sgood α

  have hsq :
      ‖qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
          tr.goodStep1
        - tr.afterStep2Ref‖ ^ 2
        ≤ C ^ 2 := by
    calc
      ‖qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
          tr.goodStep1
        - tr.afterStep2Ref‖ ^ 2
          =
        ‖∑ t : Fin (ASize cfg.env.work), E t‖ ^ 2 := by
          rw [hflat, hsplit]
      _ =
        ∑ t : Fin (ASize cfg.env.work), ‖E t‖ ^ 2 :=
          hparseval
      _ ≤
        ∑ t : Fin (ASize cfg.env.work),
          C ^ 2 *
            ∑ i ∈ Sgood.filter (fun i => i.2 = t), ‖α i‖ ^ 2 := by
          exact Finset.sum_le_sum fun t _ => hfiber t
      _ =
        C ^ 2 *
          ∑ t : Fin (ASize cfg.env.work),
            ∑ i ∈ Sgood.filter (fun i => i.2 = t), ‖α i‖ ^ 2 := by
          rw [Finset.mul_sum]
      _ =
        C ^ 2 * ∑ i ∈ Sgood, ‖α i‖ ^ 2 := by
          rw [henergy_fibers]
      _ ≤ C ^ 2 * 1 := by
          gcongr
      _ = C ^ 2 := by
          ring

  nlinarith [norm_nonneg
    (qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
      tr.goodStep1 - tr.afterStep2Ref)]

/-- The retained and discarded post-Step-3/4 reference packets are orthogonal. -/
lemma alg1_afterStep34_good_bad_orthogonal
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [Spec]
    [IdealCtrlModMulExactSemantics qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (ψ : qs.State)
    (tr : Alg1Trace qs cfg ψ) :
    inner ℂ tr.afterStep34Ref tr.afterStep34Bad = 0 := by
  classical

  let Sgood : Finset (Σ _b : qs.Basis, Fin (ASize cfg.env.work)) :=
    tr.support.sigma fun b => alg1GoodLabels cfg b

  let Sbad : Finset (Σ _b : qs.Basis, Fin (ASize cfg.env.work)) :=
    tr.support.sigma fun b =>
      Finset.univ.filter (fun t => t ∉ alg1GoodLabels cfg b)

  let α : (Σ _b : qs.Basis, Fin (ASize cfg.env.work)) → ℂ :=
    fun i => tr.inputCoeff i.1 * tr.phaseCoeff i.1 i.2

  let labelStep34 :
      (Σ _b : qs.Basis, Fin (ASize cfg.env.work)) → qs.Basis :=
    fun i =>
      RegEncoding.writeNat
        (extendHi cfg.env.data)
        (alg1OutputValue cfg i.1)
        (RegEncoding.writeNat cfg.env.work i.2.1 i.1)

  have hgood_flat :
      tr.afterStep34Ref
        =
      ∑ i ∈ Sgood, α i • qs.ket (labelStep34 i) := by
    simp [
      Sgood, α, labelStep34,
      Alg1Trace.afterStep34Ref,
      Finset.sum_sigma,
      Finset.smul_sum,
      smul_smul
    ]

  have hbad_flat :
      tr.afterStep34Bad
        =
      ∑ i ∈ Sbad, α i • qs.ket (labelStep34 i) := by
    simp [
      Sbad, α, labelStep34,
      Alg1Trace.afterStep34Bad,
      Finset.sum_sigma,
      Finset.smul_sum,
      smul_smul
    ]

  rw [hgood_flat, hbad_flat]
  rw [inner_sum]
  refine Finset.sum_eq_zero ?_
  intro j hj
  rw [sum_inner]
  refine Finset.sum_eq_zero ?_
  intro i hi

  have hlabel_ne : labelStep34 i ≠ labelStep34 j := by
    intro hEq
    rcases i with ⟨b, t⟩
    rcases j with ⟨b', u⟩

    rcases Finset.mem_sigma.mp hi with ⟨hbmem, ht_good⟩
    rcases Finset.mem_sigma.mp hj with ⟨hbmem', hu_bad_mem⟩
    have hu_not_good : u ∉ alg1GoodLabels cfg b' :=
      (Finset.mem_filter.mp hu_bad_mem).2

    rcases
      alg1_step34_label_injective
        qs cfg b b'
        (tr.input_good b hbmem)
        (tr.input_good b' hbmem')
        t u
        (by simpa [labelStep34] using hEq)
      with ⟨hbb, htu⟩

    subst b'
    subst u
    exact hu_not_good ht_good

  rw [inner_smul_left, inner_smul_right]
  rw [qs.ket_inner_eq_zero_of_ne hlabel_ne]
  simp

/--
The final complex-overlap estimate, expressed in terms of the bad QPE mass
and the coherent Step-2 state error.
-/
lemma alg1_final_overlap_le
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [Spec]
    [GateSemanticsFacts qs]
    [IdealCtrlModMulExactSemantics qs]
    [ModMulPrimitiveSemantics qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (ψ : qs.State)
    (tr : Alg1Trace qs cfg ψ)
    (hunit : cfg.ValidUnitState qs ψ)
    (hstep2 :
      ‖qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
            tr.goodStep1
          - tr.afterStep2Ref‖
        ≤ 2 * Real.pi * η) :
    ‖(1 : ℂ) -
        inner ℂ
          (qs.eval
            (ModMulConfig.approxGate (Basis := qs.Basis) cfg)
            ψ)
          (qs.eval (ModMulConfig.idealGate cfg) ψ)‖
      ≤
    2 * alg1TraceBadMass qs cfg tr
      + 3 * (2 * Real.pi * η) := by
  classical

  let U1 : Gate := ModMulConfig.U1 (Basis := qs.Basis) cfg
  let U2 : Gate := ModMulConfig.U2 (Basis := qs.Basis) cfg
  let U34 : Gate := ModMulConfig.U34 (Basis := qs.Basis) cfg
  let U5 : Gate := ModMulConfig.U5 (Basis := qs.Basis) cfg
  let post1 : Gate := U2 ;; U34 ;; U5

  let A : qs.State :=
    qs.eval (ModMulConfig.approxGate (Basis := qs.Basis) cfg) ψ
  let I : qs.State :=
    qs.eval (ModMulConfig.idealGate cfg) ψ

  let ag : qs.State := qs.eval post1 tr.goodStep1
  let ab : qs.State := qs.eval post1 tr.badStep1
  let ig : qs.State := qs.eval U5 tr.afterStep34Ref
  let ib : qs.State := qs.eval U5 tr.afterStep34Bad

  let m : ℝ := alg1TraceBadMass qs cfg tr
  let ε : ℝ := 2 * Real.pi * η

  have hε_nonneg : 0 ≤ ε := by
    dsimp [ε]
    have hη : 0 ≤ η := le_of_lt cfg.env.precision.1
    positivity

  have hU1_decomp :
      qs.eval U1 ψ = tr.goodStep1 + tr.badStep1 := by
    have hstep1 :
        qs.eval U1 ψ - tr.goodStep1 = tr.badStep1 := by
      simpa [U1] using
        (alg1_step1_error_eq_bad_packet qs cfg ψ tr)
    calc
      qs.eval U1 ψ
          =
        (qs.eval U1 ψ - tr.goodStep1) + tr.goodStep1 := by
          abel
      _ = tr.badStep1 + tr.goodStep1 := by
          rw [hstep1]
      _ = tr.goodStep1 + tr.badStep1 := by
          abel

  have hA_decomp : A = ag + ab := by
    calc
      A =
        qs.eval (ModMulConfig.stagedGate (Basis := qs.Basis) cfg) ψ := by
          simpa [A] using
            (ModMulConfig.eval_approxGate_eq_staged qs cfg ψ)
      _ =
        qs.eval post1 (qs.eval U1 ψ) := by
          simp [
            post1, U1, U2, U34, U5,
            ModMulConfig.stagedGate,
            qs.eval_seq
          ]
      _ =
        qs.eval post1 (tr.goodStep1 + tr.badStep1) := by
          rw [hU1_decomp]
      _ = ag + ab := by
          simp [ag, ab, qs.eval_add]

  have hcleanup :
      ig - I = -ib := by
    simpa [ig, ib, I, U5] using
      (alg1_step5_cleanup_error_eq_neg_bad_packet qs cfg ψ tr)

  have hI_decomp : I = ig + ib := by
    calc
      I = ig - (ig - I) := by
          abel
      _ = ig - (-ib) := by
          rw [hcleanup]
      _ = ig + ib := by
          abel

  have hA_unit : ‖A‖ = 1 := by
    dsimp [A]
    calc
      ‖qs.eval (ModMulConfig.approxGate (Basis := qs.Basis) cfg) ψ‖
          = ‖ψ‖ := by
            exact eval_norm_preserved
              (qs := qs)
              (ModMulConfig.approxGate (Basis := qs.Basis) cfg)
              ψ
      _ = 1 := hunit.2

  have hI_unit : ‖I‖ = 1 := by
    dsimp [I]
    calc
      ‖qs.eval (ModMulConfig.idealGate cfg) ψ‖
          = ‖ψ‖ := by
            exact eval_norm_preserved
              (qs := qs)
              (ModMulConfig.idealGate cfg)
              ψ
      _ = 1 := hunit.2

  have hstep34 :
      qs.eval U34 tr.afterStep2Ref = tr.afterStep34Ref := by
    simpa [U34] using
      (alg1_step34_reference_exact qs cfg ψ tr)

  have hgood_dist : ‖ag - ig‖ ≤ ε := by
    have hIso5 :
        ‖qs.eval U5 (qs.eval U34 (qs.eval U2 tr.goodStep1))
            - qs.eval U5 (qs.eval U34 tr.afterStep2Ref)‖
          =
        ‖qs.eval U34 (qs.eval U2 tr.goodStep1)
            - qs.eval U34 tr.afterStep2Ref‖ := by
      exact
        eval_isometry
          qs
          U5
          (by
            intro φ χ
            simpa using qs.inner_preserved U5 φ χ)
          (qs.eval U34 (qs.eval U2 tr.goodStep1))
          (qs.eval U34 tr.afterStep2Ref)

    have hIso34 :
        ‖qs.eval U34 (qs.eval U2 tr.goodStep1)
            - qs.eval U34 tr.afterStep2Ref‖
          =
        ‖qs.eval U2 tr.goodStep1 - tr.afterStep2Ref‖ := by
      exact
        eval_isometry
          qs
          U34
          (by
            intro φ χ
            simpa using qs.inner_preserved U34 φ χ)
          (qs.eval U2 tr.goodStep1)
          tr.afterStep2Ref

    calc
      ‖ag - ig‖
          =
        ‖qs.eval U5 (qs.eval U34 (qs.eval U2 tr.goodStep1))
            - qs.eval U5 (qs.eval U34 tr.afterStep2Ref)‖ := by
          rw [hstep34]
          simp [ag, ig, post1, U2, U34, U5, qs.eval_seq]
      _ =
        ‖qs.eval U34 (qs.eval U2 tr.goodStep1)
            - qs.eval U34 tr.afterStep2Ref‖ := hIso5
      _ =
        ‖qs.eval U2 tr.goodStep1 - tr.afterStep2Ref‖ := hIso34
      _ ≤ ε := by
        simpa [ε, U2] using hstep2

  have hgood_dist_rev : ‖ig - ag‖ ≤ ε := by
    simpa [norm_sub_rev] using hgood_dist

  have hstep1_orth :
      inner ℂ tr.goodStep1 tr.badStep1 = 0 :=
    alg1_good_badStep1_orthogonal qs cfg ψ tr

  have hstep1_orth_symm :
      inner ℂ tr.badStep1 tr.goodStep1 = 0 := by
    calc
      inner ℂ tr.badStep1 tr.goodStep1
          =
        star (inner ℂ tr.goodStep1 tr.badStep1) := by
          exact
            (inner_conj_symm
              (𝕜 := ℂ) tr.badStep1 tr.goodStep1).symm
      _ = 0 := by
          rw [hstep1_orth]
          simp

  have hactual_orth :
      inner ℂ ag ab = 0 := by
    calc
      inner ℂ ag ab
          =
        inner ℂ tr.goodStep1 tr.badStep1 := by
          simpa [ag, ab] using
            (qs.inner_preserved post1 tr.goodStep1 tr.badStep1)
      _ = 0 := hstep1_orth

  have hactual_orth_symm :
      inner ℂ ab ag = 0 := by
    calc
      inner ℂ ab ag
          =
        inner ℂ tr.badStep1 tr.goodStep1 := by
          simpa [ag, ab] using
            (qs.inner_preserved post1 tr.badStep1 tr.goodStep1)
      _ = 0 := hstep1_orth_symm

  have hideal_orth :
      inner ℂ ig ib = 0 := by
    calc
      inner ℂ ig ib
          =
        inner ℂ tr.afterStep34Ref tr.afterStep34Bad := by
          simpa [ig, ib] using
            (qs.inner_preserved U5 tr.afterStep34Ref tr.afterStep34Bad)
      _ = 0 := alg1_afterStep34_good_bad_orthogonal qs cfg ψ tr

  have hbad_sq : ‖ab‖ ^ 2 = m := by
    have hnorm :
        ‖ab‖ = ‖tr.badStep1‖ := by
      simpa [ab] using
        (eval_norm_preserved (qs := qs) post1 tr.badStep1)
    calc
      ‖ab‖ ^ 2 = ‖tr.badStep1‖ ^ 2 := by
          rw [hnorm]
      _ = m := by
          simpa [m] using
            (alg1_badStep1_norm_sq_eq_trace_bad_mass qs cfg ψ tr)

  have hideal_bad_sq : ‖ib‖ ^ 2 = m := by
    have hnorm :
        ‖ib‖ = ‖tr.afterStep34Bad‖ := by
      simpa [ib] using
        (eval_norm_preserved (qs := qs) U5 tr.afterStep34Bad)
    calc
      ‖ib‖ ^ 2 = ‖tr.afterStep34Bad‖ ^ 2 := by
          rw [hnorm]
      _ = m := by
          simpa [m] using
            (alg1_afterStep34Bad_norm_sq_eq_trace_bad_mass qs cfg ψ tr)

  have hA_sq :
      ‖ag‖ ^ 2 + ‖ab‖ ^ 2 = 1 := by
    have hpy :
        ‖ag + ab‖ ^ 2 = ‖ag‖ ^ 2 + ‖ab‖ ^ 2 := by
      calc
        ‖ag + ab‖ ^ 2
            =
          ‖ag‖ ^ 2
            + 2 * Complex.re (inner ℂ ag ab)
            + ‖ab‖ ^ 2 := by
              exact norm_add_sq (𝕜 := ℂ) ag ab
        _ = ‖ag‖ ^ 2 + ‖ab‖ ^ 2 := by
              rw [hactual_orth]
              simp
    have hunitA :
        ‖ag + ab‖ ^ 2 = 1 := by
      rw [← hA_decomp, hA_unit]
      norm_num
    linarith

  have hI_sq :
      ‖ig‖ ^ 2 + ‖ib‖ ^ 2 = 1 := by
    have hpy :
        ‖ig + ib‖ ^ 2 = ‖ig‖ ^ 2 + ‖ib‖ ^ 2 := by
      calc
        ‖ig + ib‖ ^ 2
            =
          ‖ig‖ ^ 2
            + 2 * Complex.re (inner ℂ ig ib)
            + ‖ib‖ ^ 2 := by
              exact norm_add_sq (𝕜 := ℂ) ig ib
        _ = ‖ig‖ ^ 2 + ‖ib‖ ^ 2 := by
              rw [hideal_orth]
              simp
    have hunitI :
        ‖ig + ib‖ ^ 2 = 1 := by
      rw [← hI_decomp, hI_unit]
      norm_num
    linarith

  have hag_le_one : ‖ag‖ ≤ 1 := by
    have : ‖ag‖ ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg ‖ab‖]
    nlinarith [norm_nonneg ag]

  have hab_le_one : ‖ab‖ ≤ 1 := by
    have : ‖ab‖ ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg ‖ag‖]
    nlinarith [norm_nonneg ab]

  have hib_le_one : ‖ib‖ ≤ 1 := by
    have : ‖ib‖ ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg ‖ig‖]
    nlinarith [norm_nonneg ib]

  have hgood_term :
      ‖inner ℂ ag ag - inner ℂ ag ig‖ ≤ ε := by
    calc
      ‖inner ℂ ag ag - inner ℂ ag ig‖
          =
        ‖inner ℂ ag (ag - ig)‖ := by
          rw [inner_sub_right]
      _ ≤ ‖ag‖ * ‖ag - ig‖ :=
          norm_inner_le_norm ag (ag - ig)
      _ ≤ 1 * ε := by
          exact mul_le_mul hag_le_one hgood_dist
            (norm_nonneg _) (by norm_num)
      _ = ε := by ring

  have hbad_self :
      ‖inner ℂ ab ab‖ = m := by
    rw [inner_self_eq_norm_sq_to_K]
    simp[hbad_sq]

  have hbad_cross :
      ‖inner ℂ ab ib‖ ≤ m := by
    have hcauchy : ‖inner ℂ ab ib‖ ≤ ‖ab‖ * ‖ib‖ :=
      norm_inner_le_norm ab ib
    have hprod : ‖ab‖ * ‖ib‖ ≤ m := by
      nlinarith [hbad_sq, hideal_bad_sq,
        norm_nonneg ab, norm_nonneg ib,
        sq_nonneg (‖ab‖ - ‖ib‖)]
    exact le_trans hcauchy hprod

  have hbad_term :
      ‖inner ℂ ab ab - inner ℂ ab ib‖ ≤ 2 * m := by
    calc
      ‖inner ℂ ab ab - inner ℂ ab ib‖
          ≤ ‖inner ℂ ab ab‖ + ‖inner ℂ ab ib‖ :=
            norm_sub_le _ _
      _ ≤ m + m := by
          exact add_le_add (le_of_eq hbad_self) hbad_cross
      _ = 2 * m := by ring

  have hcross_good_bad :
      ‖inner ℂ ag ib‖ ≤ ε := by
    calc
      ‖inner ℂ ag ib‖
          =
        ‖inner ℂ (ag - ig) ib‖ := by
          rw [inner_sub_left, hideal_orth, sub_zero]
      _ ≤ ‖ag - ig‖ * ‖ib‖ :=
          norm_inner_le_norm (ag - ig) ib
      _ ≤ ε * 1 := by
          exact mul_le_mul hgood_dist hib_le_one
            (norm_nonneg _) hε_nonneg
      _ = ε := by ring

  have hcross_bad_good :
      ‖inner ℂ ab ig‖ ≤ ε := by
    calc
      ‖inner ℂ ab ig‖
          =
        ‖inner ℂ ab (ig - ag)‖ := by
          rw [inner_sub_right, hactual_orth_symm, sub_zero]
      _ ≤ ‖ab‖ * ‖ig - ag‖ :=
          norm_inner_le_norm ab (ig - ag)
      _ ≤ 1 * ε := by
          exact mul_le_mul hab_le_one hgood_dist_rev
            (norm_nonneg _) (by norm_num)
      _ = ε := by ring

  have hAA :
      inner ℂ A A = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hA_unit]
    norm_num

  have hactual_inner_self :
      inner ℂ (ag + ab) (ag + ab)
        =
      inner ℂ ag ag + inner ℂ ab ab := by
    rw [inner_add_left, inner_add_right, inner_add_right]
    rw [hactual_orth, hactual_orth_symm]
    ring

  let x : ℂ := inner ℂ ag ag - inner ℂ ag ig
  let y : ℂ := inner ℂ ab ab - inner ℂ ab ib
  let z : ℂ := inner ℂ ag ib
  let w : ℂ := inner ℂ ab ig

  have hoverlap_decomp :
      (1 : ℂ) - inner ℂ A I = x + y - z - w := by
    rw [← hAA, hA_decomp, hI_decomp]
    rw [hactual_inner_self]
    simp [
      x, y, z, w,
      inner_add_left,
      inner_add_right
    ]
    ring

  have htri :
      ‖x + y - z - w‖ ≤ ‖x‖ + ‖y‖ + ‖z‖ + ‖w‖ := by
    calc
      ‖x + y - z - w‖
          =
        ‖(x + y - z) + (-w)‖ := by
          abel
      _ ≤ ‖x + y - z‖ + ‖-w‖ :=
          norm_add_le _ _
      _ = ‖x + y - z‖ + ‖w‖ := by
          rw [norm_neg]
      _ ≤ (‖x + y‖ + ‖z‖) + ‖w‖ := by
          gcongr
          calc
            ‖x + y - z‖
                ≤ ‖x + y‖ + ‖-z‖ := by
                  simpa [sub_eq_add_neg] using
                    (norm_add_le (x + y) (-z))
            _ = ‖x + y‖ + ‖z‖ := by
                  rw [norm_neg]
      _ ≤ ((‖x‖ + ‖y‖) + ‖z‖) + ‖w‖ := by
          gcongr
          exact norm_add_le x y
      _ = ‖x‖ + ‖y‖ + ‖z‖ + ‖w‖ := by
          simp [add_assoc]

  calc
    ‖(1 : ℂ) - inner ℂ A I‖
        =
      ‖x + y - z - w‖ := by
        rw [hoverlap_decomp]
    _ ≤ ‖x‖ + ‖y‖ + ‖z‖ + ‖w‖ := htri
    _ ≤ ε + 2 * m + ε + ε := by
        nlinarith [
          hgood_term,
          hbad_term,
          hcross_good_bad,
          hcross_bad_good
        ]
    _ =
      2 * m + 3 * ε := by
        ring
    _ =
      2 * alg1TraceBadMass qs cfg tr
        + 3 * (2 * Real.pi * η) := by
        simp [m, ε]

theorem modMul_theorem1_overlap_uniform
    (qs : QSemantics)
    [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [Spec] [GateSemanticsFacts qs] [IdealCtrlModMulExactSemantics qs] [ModMulPrimitiveSemantics qs] :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (η : ℝ) (cfg : ModMulConfig η) (ψ : qs.State),
        cfg.ValidUnitState qs ψ →
        ‖(1 : ℂ) -
            inner ℂ
              (qs.eval (ModMulConfig.approxGate (Basis := qs.Basis) cfg) ψ)
              (qs.eval (ModMulConfig.idealGate cfg) ψ)‖
          ≤ K * η := by
  classical

  rcases alg1_qpe_tail_uniform qs with
    ⟨Cpe, hCpe, hTail, _hStep1Sq, _hStep5Sq⟩

  refine ⟨2 * Cpe + 6 * Real.pi, ?_, ?_⟩
  · positivity

  intro η cfg ψ hunit
  rcases hunit with ⟨hvalid, hnorm⟩
  have hunit' : cfg.ValidUnitState qs ψ := ⟨hvalid, hnorm⟩

  rcases alg1_trace_of_valid qs cfg ψ hvalid with ⟨tr, _⟩

  have hbad :
      alg1TraceBadMass qs cfg tr ≤ Cpe * η :=
    alg1_trace_bad_mass_le_of_basis_tail
      qs hTail cfg ψ tr hunit'

  have hstep2 :
      ‖qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
            tr.goodStep1
          - tr.afterStep2Ref‖
        ≤ 2 * Real.pi * η :=
    alg1_step2_good_packet_norm_le qs cfg ψ tr hunit'

  have hfinal :=
    alg1_final_overlap_le qs cfg ψ tr hunit' hstep2

  calc
    ‖(1 : ℂ) -
        inner ℂ
          (qs.eval
            (ModMulConfig.approxGate (Basis := qs.Basis) cfg)
            ψ)
          (qs.eval (ModMulConfig.idealGate cfg) ψ)‖
      ≤
        2 * alg1TraceBadMass qs cfg tr
          + 3 * (2 * Real.pi * η) :=
      hfinal
    _ ≤
        2 * (Cpe * η)
          + 3 * (2 * Real.pi * η) := by
      gcongr
    _ =
        (2 * Cpe + 6 * Real.pi) * η := by
      ring
