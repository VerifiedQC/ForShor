import FastMultiplication.ShorVerification.AlgorithmCorrectness.ModMulBounds.Step1Bound
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
open Shor

universe v


/-! =========================================================
    Step-2 quantitative Fourier stability
========================================================= -/

private lemma alg1_step2_norm_sq_sum_eq_sum_norm_sq_of_orthogonal
    {qs : QSemantics}
    {ι : Type v}
    (s : Finset ι)
    (f : ι → qs.State)
    (horth :
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        inner ℂ (f i) (f j) = 0) :
    ‖∑ i ∈ s, f i‖ ^ 2
      =
    ∑ i ∈ s, ‖f i‖ ^ 2 := by
  classical
  revert horth
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simp
  | insert a s ha ih =>
      intro horth

      have horth_s :
          ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
            inner ℂ (f i) (f j) = 0 := by
        intro i hi j hj hij
        exact horth i
          (Finset.mem_insert_of_mem hi)
          j
          (Finset.mem_insert_of_mem hj)
          hij

      have hih :
          ‖∑ i ∈ s, f i‖ ^ 2
            =
          ∑ i ∈ s, ‖f i‖ ^ 2 :=
        ih horth_s

      have hcross :
          inner ℂ (f a) (∑ i ∈ s, f i) = 0 := by
        rw [inner_sum]
        refine Finset.sum_eq_zero ?_
        intro i hi
        apply horth a (by simp) i (Finset.mem_insert_of_mem hi)
        intro hai
        subst i
        exact ha hi

      calc
        ‖∑ i ∈ insert a s, f i‖ ^ 2
            =
          ‖f a + ∑ i ∈ s, f i‖ ^ 2 := by
            rw [Finset.sum_insert ha]
        _ =
          ‖f a‖ ^ 2
            + 2 * Complex.re (inner ℂ (f a) (∑ i ∈ s, f i))
            + ‖∑ i ∈ s, f i‖ ^ 2 := by
              exact norm_add_sq (𝕜 := ℂ) _ _
        _ =
          ‖f a‖ ^ 2 + ‖∑ i ∈ s, f i‖ ^ 2 := by
              rw [hcross]
              simp
        _ =
          ‖f a‖ ^ 2 + ∑ i ∈ s, ‖f i‖ ^ 2 := by
              rw [hih]
        _ =
          ∑ i ∈ insert a s, ‖f i‖ ^ 2 := by
              rw [Finset.sum_insert ha]

lemma alg1_step2_source_label_injective_on_good
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (ψ : qs.State)
    (tr : Alg1Trace qs cfg ψ) :
    let Sgood : Finset (Σ _b : qs.Basis, Fin (ASize cfg.env.work)) :=
      tr.support.sigma fun b => alg1GoodLabels cfg b
    let labelGood :
        (Σ _b : qs.Basis, Fin (ASize cfg.env.work)) → qs.Basis :=
      fun i =>
        RegEncoding.writeNat cfg.env.work i.2.1 i.1
    ∀ i ∈ Sgood, ∀ j ∈ Sgood, i ≠ j →
      labelGood i ≠ labelGood j := by
  classical
  dsimp only

  intro i hi j hj hij hEq
  rcases i with ⟨b, t⟩
  rcases j with ⟨b', u⟩

  rcases Finset.mem_sigma.mp hi with ⟨hbmem, _⟩
  rcases Finset.mem_sigma.mp hj with ⟨hbmem', _⟩

  have hb :
      GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b :=
    tr.input_good b hbmem

  have hb' :
      GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b' :=
    tr.input_good b' hbmem'

  have htu_val : t.1 = u.1 := by
    calc
      t.1
          =
        RegEncoding.toNat cfg.env.work
          (RegEncoding.writeNat cfg.env.work t.1 b) := by
            symm
            exact
              RegEncoding.toNat_writeNat_of_lt
                cfg.env.work t.1 b t.isLt
      _ =
        RegEncoding.toNat cfg.env.work
          (RegEncoding.writeNat cfg.env.work u.1 b') := by
            rw [hEq]
      _ = u.1 :=
        RegEncoding.toNat_writeNat_of_lt
          cfg.env.work u.1 b' u.isLt

  have htu : t = u :=
    Fin.ext htu_val

  have hb_work : RegEncoding.toNat cfg.env.work b = 0 :=
    hb.2.2.1

  have hb'_work : RegEncoding.toNat cfg.env.work b' = 0 :=
    hb'.2.2.1

  have hb_zero :
      RegEncoding.writeNat cfg.env.work 0 b = b := by
    simpa [hb_work] using
      (RegEncoding.writeNat_toNat cfg.env.work b)

  have hb'_zero :
      RegEncoding.writeNat cfg.env.work 0 b' = b' := by
    simpa [hb'_work] using
      (RegEncoding.writeNat_toNat cfg.env.work b')

  have hbb : b = b' := by
    calc
      b =
          RegEncoding.writeNat cfg.env.work 0 b := hb_zero.symm
      _ =
          RegEncoding.writeNat cfg.env.work 0
            (RegEncoding.writeNat cfg.env.work t.1 b) := by
              symm
              exact
                writeNat_overwrite_same_reg
                  cfg.env.work 0 t.1 b
      _ =
          RegEncoding.writeNat cfg.env.work 0
            (RegEncoding.writeNat cfg.env.work u.1 b') := by
              exact congrArg (RegEncoding.writeNat cfg.env.work 0) hEq
      _ =
          RegEncoding.writeNat cfg.env.work 0 b' := by
              exact
                writeNat_overwrite_same_reg
                  cfg.env.work 0 u.1 b'
      _ = b' := hb'_zero

  apply hij
  cases hbb
  cases htu
  rfl

lemma alg1_step2_trace_error_eq_good_branch_sum
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (ψ : qs.State)
    (tr : Alg1Trace qs cfg ψ) :
    let Sgood : Finset (Σ _b : qs.Basis, Fin (ASize cfg.env.work)) :=
      tr.support.sigma fun b => alg1GoodLabels cfg b
    let α : (Σ _b : qs.Basis, Fin (ASize cfg.env.work)) → ℂ :=
      fun i => tr.inputCoeff i.1 * tr.phaseCoeff i.1 i.2
    qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg) tr.goodStep1
      - tr.afterStep2Ref
      =
    ∑ i ∈ Sgood,
      α i •
        (qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
          (qs.ket
            (RegEncoding.writeNat cfg.env.work i.2.1 i.1))
          -
          qs.ket
            (RegEncoding.writeNat
              (extendHi cfg.env.data)
              (alg1Step2Value cfg i.1)
              (RegEncoding.writeNat cfg.env.work i.2.1 i.1))) := by
  classical
  dsimp only

  let Sgood : Finset (Σ _b : qs.Basis, Fin (ASize cfg.env.work)) :=
    tr.support.sigma fun b => alg1GoodLabels cfg b

  let α : (Σ _b : qs.Basis, Fin (ASize cfg.env.work)) → ℂ :=
    fun i => tr.inputCoeff i.1 * tr.phaseCoeff i.1 i.2

  change
    qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg) tr.goodStep1
      - tr.afterStep2Ref
      =
    ∑ i ∈ Sgood,
      α i •
        (qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
          (qs.ket
            (RegEncoding.writeNat cfg.env.work i.2.1 i.1))
          -
          qs.ket
            (RegEncoding.writeNat
              (extendHi cfg.env.data)
              (alg1Step2Value cfg i.1)
              (RegEncoding.writeNat cfg.env.work i.2.1 i.1)))

  have hgood_flat :
      tr.goodStep1 =
      ∑ i ∈ Sgood,
        α i •
          qs.ket (RegEncoding.writeNat cfg.env.work i.2.1 i.1) := by
    simp [
      Sgood, α,
      Alg1Trace.goodStep1,
      Finset.sum_sigma,
      Finset.smul_sum,
      smul_smul
    ]

  have href_flat :
      tr.afterStep2Ref =
      ∑ i ∈ Sgood,
        α i •
          qs.ket
            (RegEncoding.writeNat
              (extendHi cfg.env.data)
              (alg1Step2Value cfg i.1)
              (RegEncoding.writeNat cfg.env.work i.2.1 i.1)) := by
    simp [
      Sgood, α,
      Alg1Trace.afterStep2Ref,
      Finset.sum_sigma,
      Finset.smul_sum,
      smul_smul
    ]

  calc
    qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg) tr.goodStep1
        - tr.afterStep2Ref
      =
    qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
        (∑ i ∈ Sgood,
          α i • qs.ket
            (RegEncoding.writeNat cfg.env.work i.2.1 i.1))
        -
      ∑ i ∈ Sgood,
        α i •
          qs.ket
            (RegEncoding.writeNat
              (extendHi cfg.env.data)
              (alg1Step2Value cfg i.1)
              (RegEncoding.writeNat cfg.env.work i.2.1 i.1)) := by
        rw [hgood_flat, href_flat]

    _ =
    (∑ i ∈ Sgood,
      qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
        (α i • qs.ket
          (RegEncoding.writeNat cfg.env.work i.2.1 i.1)))
      -
    ∑ i ∈ Sgood,
      α i •
        qs.ket
          (RegEncoding.writeNat
            (extendHi cfg.env.data)
            (alg1Step2Value cfg i.1)
            (RegEncoding.writeNat cfg.env.work i.2.1 i.1)) := by
        rw [eval_finset_sum]

    _ =
    (∑ i ∈ Sgood,
      α i •
        qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
          (qs.ket
            (RegEncoding.writeNat cfg.env.work i.2.1 i.1)))
      -
    ∑ i ∈ Sgood,
      α i •
        qs.ket
          (RegEncoding.writeNat
            (extendHi cfg.env.data)
            (alg1Step2Value cfg i.1)
            (RegEncoding.writeNat cfg.env.work i.2.1 i.1)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        rw [qs.eval_smul]

    _ =
    ∑ i ∈ Sgood,
      α i •
        (qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
          (qs.ket
            (RegEncoding.writeNat cfg.env.work i.2.1 i.1))
          -
          qs.ket
            (RegEncoding.writeNat
              (extendHi cfg.env.data)
              (alg1Step2Value cfg i.1)
              (RegEncoding.writeNat cfg.env.work i.2.1 i.1))) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        rw [smul_sub]

/--
The squared coefficient energy of the retained packet is exactly the squared
norm of `goodStep1`.

This uses `alg1_step2_source_label_injective_on_good` and orthogonality of
distinct computational-basis kets.
-/
lemma alg1_step2_good_coeff_energy_eq_norm_sq
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (ψ : qs.State)
    (tr : Alg1Trace qs cfg ψ) :
    let Sgood : Finset (Σ _b : qs.Basis, Fin (ASize cfg.env.work)) :=
      tr.support.sigma fun b => alg1GoodLabels cfg b
    let α : (Σ _b : qs.Basis, Fin (ASize cfg.env.work)) → ℂ :=
      fun i => tr.inputCoeff i.1 * tr.phaseCoeff i.1 i.2
    ∑ i ∈ Sgood, ‖α i‖ ^ 2
      =
    ‖tr.goodStep1‖ ^ 2 := by
  classical
  dsimp only

  let Sgood : Finset (Σ _b : qs.Basis, Fin (ASize cfg.env.work)) :=
    tr.support.sigma fun b => alg1GoodLabels cfg b

  let α : (Σ _b : qs.Basis, Fin (ASize cfg.env.work)) → ℂ :=
    fun i => tr.inputCoeff i.1 * tr.phaseCoeff i.1 i.2

  let labelGood :
      (Σ _b : qs.Basis, Fin (ASize cfg.env.work)) → qs.Basis :=
    fun i => RegEncoding.writeNat cfg.env.work i.2.1 i.1

  change
    (∑ i ∈ Sgood, ‖α i‖ ^ 2)
      =
    ‖tr.goodStep1‖ ^ 2

  have hflat :
      tr.goodStep1 =
      ∑ i ∈ Sgood, α i • qs.ket (labelGood i) := by
    simp [
      Sgood, α, labelGood,
      Alg1Trace.goodStep1,
      Finset.sum_sigma,
      Finset.smul_sum,
      smul_smul
    ]

  have hinj :
      ∀ i ∈ Sgood, ∀ j ∈ Sgood, i ≠ j →
        labelGood i ≠ labelGood j := by
    simpa [Sgood, labelGood] using
      alg1_step2_source_label_injective_on_good qs cfg ψ tr

  have horth :
      ∀ i ∈ Sgood, ∀ j ∈ Sgood, i ≠ j →
        inner ℂ
          (α i • qs.ket (labelGood i))
          (α j • qs.ket (labelGood j))
          =
        0 := by
    intro i hi j hj hij
    rw [
      inner_smul_left,
      inner_smul_right,
      qs.ket_inner_eq_zero_of_ne (hinj i hi j hj hij)
    ]
    simp

  have hsq :
      ‖∑ i ∈ Sgood, α i • qs.ket (labelGood i)‖ ^ 2
        =
      ∑ i ∈ Sgood, ‖α i • qs.ket (labelGood i)‖ ^ 2 :=
    alg1_step2_norm_sq_sum_eq_sum_norm_sq_of_orthogonal
      (qs := qs)
      Sgood
      (fun i => α i • qs.ket (labelGood i))
      horth

  calc
    ∑ i ∈ Sgood, ‖α i‖ ^ 2
        =
      ∑ i ∈ Sgood, ‖α i • qs.ket (labelGood i)‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [norm_smul, ket_norm_one qs]
    _ =
      ‖∑ i ∈ Sgood, α i • qs.ket (labelGood i)‖ ^ 2 :=
        hsq.symm
    _ = ‖tr.goodStep1‖ ^ 2 := by
        rw [hflat]

lemma alg1_step2_good_coeff_energy_le_one
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (ψ : qs.State)
    (tr : Alg1Trace qs cfg ψ) :
    cfg.ValidUnitState qs ψ →
      let Sgood : Finset (Σ _b : qs.Basis, Fin (ASize cfg.env.work)) :=
        tr.support.sigma fun b => alg1GoodLabels cfg b
      let α : (Σ _b : qs.Basis, Fin (ASize cfg.env.work)) → ℂ :=
        fun i => tr.inputCoeff i.1 * tr.phaseCoeff i.1 i.2
      ∑ i ∈ Sgood, ‖α i‖ ^ 2 ≤ 1 := by
  intro hunit
  dsimp only
  rw [alg1_step2_good_coeff_energy_eq_norm_sq qs cfg ψ tr]

  have hgood : ‖tr.goodStep1‖ ≤ 1 :=
    alg1_goodStep1_norm_le_one qs cfg ψ tr hunit

  have hnonneg : 0 ≤ ‖tr.goodStep1‖ :=
    norm_nonneg _

  nlinarith


/-! =========================================================
    Step-2 one-label Fourier stability
========================================================= -/

lemma alg1_step2_good_label_shift_discrepancy_lt
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : QSemantics.Basis)
    (t : Fin (ASize cfg.env.work))
    (ht : t ∈ alg1GoodLabels cfg b) :
    |alg1Step2ShiftDiscrepancy cfg b t| < η := by
  let N : ℕ := cfg.env.N
  let A : ℕ := ASize cfg.env.data
  let M : ℕ := ASize cfg.env.work
  let r : ℕ := alg1TargetResidue cfg b

  have hNpos : 0 < N := by
    dsimp [N]
    exact Nat.lt_trans Nat.zero_lt_one cfg.env.modulus_gt_one

  have hApos : 0 < A := by
    dsimp [A, ASize]
    positivity

  have hMpos : 0 < M := by
    dsimp [M, ASize]
    positivity

  have hNposR : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast hNpos

  have hAposR : (0 : ℝ) < (A : ℝ) := by
    exact_mod_cast hApos

  have hMposR : (0 : ℝ) < (M : ℝ) := by
    exact_mod_cast hMpos

  have hNneR : (N : ℝ) ≠ 0 :=
    ne_of_gt hNposR

  have hMneR : (M : ℝ) ≠ 0 :=
    ne_of_gt hMposR

  have hAneR : (A : ℝ) ≠ 0 :=
    ne_of_gt hAposR

  have hη : 0 < η :=
    cfg.env.precision.1

  have hNA : (N : ℝ) ≤ (A : ℝ) := by
    exact_mod_cast cfg.env.data_capacity

  have hmem :
      t ∈ Finset.univ.filter
        (fun s =>
          |alg1TargetFraction cfg b - alg1WorkFraction cfg s|
            < η / (ASize cfg.env.data : ℝ)) := by
    simpa [alg1GoodLabels] using ht

  have hgood_raw :=
    (Finset.mem_filter.mp hmem).2

  have hgood :
      |(r : ℝ) / (N : ℝ) - (t.1 : ℝ) / (M : ℝ)|
        <
      η / (A : ℝ) := by
    simpa [
      alg1TargetFraction,
      alg1WorkFraction,
      N, A, M, r
    ] using hgood_raw

  have hmul :
      (N : ℝ) *
          |(r : ℝ) / (N : ℝ) - (t.1 : ℝ) / (M : ℝ)|
        <
      (N : ℝ) * (η / (A : ℝ)) :=
    mul_lt_mul_of_pos_left hgood hNposR

  have hratio :
      (N : ℝ) / (A : ℝ) ≤ 1 :=
    (div_le_one₀ hAposR).mpr hNA

  have hbound :
      (N : ℝ) * (η / (A : ℝ)) ≤ η := by
    calc
      (N : ℝ) * (η / (A : ℝ))
          = ((N : ℝ) / (A : ℝ)) * η := by
              field_simp [hAneR]
      _ ≤ 1 * η :=
        mul_le_mul_of_nonneg_right hratio (le_of_lt hη)
      _ = η := one_mul _

  have hident :
      (N : ℝ) * ((t.1 : ℝ) / (M : ℝ)) - (r : ℝ)
        =
      -((N : ℝ) *
        ((r : ℝ) / (N : ℝ) - (t.1 : ℝ) / (M : ℝ))) := by
    field_simp [hNneR, hMneR]
    ring

  have hfinal :
      |(N : ℝ) * ((t.1 : ℝ) / (M : ℝ) - 0) - (r : ℝ)|
        <
      η := by
    rw [show
      (N : ℝ) * ((t.1 : ℝ) / (M : ℝ) - 0) - (r : ℝ)
        =
      (N : ℝ) * ((t.1 : ℝ) / (M : ℝ)) - (r : ℝ) by ring]
    rw [hident, abs_neg, abs_mul, abs_of_pos hNposR]
    exact lt_of_lt_of_le hmul hbound

  simpa [
    alg1Step2ShiftDiscrepancy,
    alg1WorkFraction,
    N, M, r
  ] using hfinal


lemma alg1_step2_input_xext_value
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis)
    (t : Fin (ASize cfg.env.work))
    (hb :
      GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b) :
    RegEncoding.toNat (extendHi cfg.env.data)
      (RegEncoding.writeNat cfg.env.work t.1 b)
      =
    RegEncoding.toNat cfg.env.data b := by
  let m : SplitPoint (extendHi cfg.env.data) :=
    ⟨regSize cfg.env.data, by
      change cfg.env.data.size ≤ cfg.env.data.size + 1
      omega⟩

  have hwrite :
      RegEncoding.toNat (extendHi cfg.env.data)
        (RegEncoding.writeNat cfg.env.work t.1 b)
      =
      RegEncoding.toNat (extendHi cfg.env.data) b :=
    RegEncoding.toNat_left_write_right
      (extendHi cfg.env.data)
      cfg.env.work
      cfg.layout.1
      b
      t.1

  have hsplit :
      RegEncoding.toNat (extendHi cfg.env.data) b
        =
      RegEncoding.toNat cfg.env.data b
        +
      ASize cfg.env.data *
        RegEncoding.toNat (qubitReg cfg.env.data.hi) b := by
    simpa [
      m,
      splitLeft,
      splitRight,
      extendHi,
      qubitReg,
      Reg.hi,
      regSize,
      ASize
    ] using
      (RegEncoding.toNat_split (extendHi cfg.env.data) m b)

  calc
    RegEncoding.toNat (extendHi cfg.env.data)
        (RegEncoding.writeNat cfg.env.work t.1 b)
      =
    RegEncoding.toNat (extendHi cfg.env.data) b := hwrite
    _ =
    RegEncoding.toNat cfg.env.data b
      +
    ASize cfg.env.data *
      RegEncoding.toNat (qubitReg cfg.env.data.hi) b := hsplit
    _ =
    RegEncoding.toNat cfg.env.data b := by
      rw [hb.2.1]
      simp

lemma alg1_step2_phase_normalization
    {η : ℝ}
    (cfg : ModMulConfig η)
    (t : Fin (ASize cfg.env.work))
    (y : Fin (ASize (extendHi cfg.env.data))) :
    alg1Step2Phase cfg * Complex.I *
        ((t.1 : ℂ) * (y.1 : ℂ))
      =
    (((2 * Real.pi) /
        (ASize (extendHi cfg.env.data) : ℝ)) * Complex.I) *
      (((cfg.env.N : ℝ) * alg1WorkFraction cfg t : ℝ) : ℂ) *
      (y.1 : ℂ) := by
  have hMpos : (0 : ℝ) < (ASize cfg.env.work : ℝ) := by
    simp[ASize]

  have hLpos : (0 : ℝ) < (ASize (extendHi cfg.env.data) : ℝ) := by
    simp[ASize]

  have hMne : (ASize cfg.env.work : ℝ) ≠ 0 :=
    ne_of_gt hMpos

  have hLne : (ASize (extendHi cfg.env.data) : ℝ) ≠ 0 :=
    ne_of_gt hLpos

  have hMneC : ((ASize cfg.env.work : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hMne

  have hLneC : ((ASize (extendHi cfg.env.data) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hLne

  have hpow :
      (2 : ℝ) ^
          (regSize cfg.env.work + regSize (extendHi cfg.env.data))
        =
      (ASize cfg.env.work : ℝ) *
        (ASize (extendHi cfg.env.data) : ℝ) := by
    simp [ASize, pow_add]

  simp only [alg1Step2Phase, alg1WorkFraction]
  rw [hpow]
  push_cast
  field_simp [hMne, hLne, hMneC, hLneC]


lemma alg1_step2_actual_preIQFT_packet
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis)
    (t : Fin (ASize cfg.env.work))
    (hb :
      GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b) :
    qs.eval
        (Gate.PhaseProd
          (alg1Step2Phase cfg)
          cfg.env.work
          (extendHi cfg.env.data))
        (qs.eval
          (Gate.QFT (extendHi cfg.env.data))
          (qs.ket (RegEncoding.writeNat cfg.env.work t.1 b)))
      =
    ∑ y : Fin (ASize (extendHi cfg.env.data)),
      alg1Step2ActualFourierCoeff cfg b t y •
        qs.ket
          (RegEncoding.writeNat
            (extendHi cfg.env.data)
            y.1
            (RegEncoding.writeNat cfg.env.work t.1 b)) := by
  classical

  have hdisj :
      Disjoint cfg.env.work (extendHi cfg.env.data) := by
    rcases cfg.layout.1 with h | h
    · exact Or.inr h
    · exact Or.inl h

  have hxbase :
      RegEncoding.toNat (extendHi cfg.env.data)
        (RegEncoding.writeNat cfg.env.work t.1 b)
      =
      RegEncoding.toNat cfg.env.data b :=
    alg1_step2_input_xext_value qs cfg b t hb

  rw [QFTSemantics.eval_QFT_ket]
  rw [qs.eval_smul, eval_finset_sum, Finset.smul_sum]

  apply Finset.sum_congr rfl
  intro y hy

  rw [qs.eval_smul]
  rw [
    GateSemanticsFacts.eval_PhaseProd_ket
      qs
      (alg1Step2Phase cfg)
      cfg.env.work
      (extendHi cfg.env.data)
      (RegEncoding.writeNat
        (extendHi cfg.env.data)
        y.1
        (RegEncoding.writeNat cfg.env.work t.1 b))
      hdisj
  ]

  have hwork :
      RegEncoding.toNat cfg.env.work
        (RegEncoding.writeNat
          (extendHi cfg.env.data)
          y.1
          (RegEncoding.writeNat cfg.env.work t.1 b))
        =
      t.1 := by
    calc
      RegEncoding.toNat cfg.env.work
          (RegEncoding.writeNat
            (extendHi cfg.env.data)
            y.1
            (RegEncoding.writeNat cfg.env.work t.1 b))
        =
      RegEncoding.toNat cfg.env.work
        (RegEncoding.writeNat cfg.env.work t.1 b) := by
          exact
            RegEncoding.toNat_left_write_right
              cfg.env.work
              (extendHi cfg.env.data)
              hdisj
              (RegEncoding.writeNat cfg.env.work t.1 b)
              y.1
      _ = t.1 :=
        RegEncoding.toNat_writeNat_of_lt
          cfg.env.work
          t.1
          b
          t.isLt

  have hxext :
      RegEncoding.toNat (extendHi cfg.env.data)
        (RegEncoding.writeNat
          (extendHi cfg.env.data)
          y.1
          (RegEncoding.writeNat cfg.env.work t.1 b))
        =
      y.1 :=
    RegEncoding.toNat_writeNat_of_lt
      (extendHi cfg.env.data)
      y.1
      (RegEncoding.writeNat cfg.env.work t.1 b)
      y.isLt

  rw [smul_smul, smul_smul]
  simp [
    alg1Step2ActualFourierCoeff,
    alg1Step2QFTScale,
    ASize,
    hxbase,
    hwork,
    hxext,
    mul_assoc
  ]

lemma alg1_step2_ideal_preIQFT_packet
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis)
    (t : Fin (ASize cfg.env.work))
    (hb :
      GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b) :
    qs.eval
        (Gate.QFT (extendHi cfg.env.data))
        (qs.ket
          (RegEncoding.writeNat
            (extendHi cfg.env.data)
            (alg1Step2Value cfg b)
            (RegEncoding.writeNat cfg.env.work t.1 b)))
      =
    ∑ y : Fin (ASize (extendHi cfg.env.data)),
      alg1Step2IdealFourierCoeff cfg b y •
        qs.ket
          (RegEncoding.writeNat
            (extendHi cfg.env.data)
            y.1
            (RegEncoding.writeNat cfg.env.work t.1 b)) := by
  classical

  have hslt :
      alg1Step2Value cfg b < ASize (extendHi cfg.env.data) :=
    alg1Step2Value_lt_extendHi_capacity cfg b hb

  rw [QFTSemantics.eval_QFT_ket]
  rw [Finset.smul_sum]

  apply Finset.sum_congr rfl
  intro y hy

  have hread :
      RegEncoding.toNat (extendHi cfg.env.data)
        (RegEncoding.writeNat
          (extendHi cfg.env.data)
          (alg1Step2Value cfg b)
          (RegEncoding.writeNat cfg.env.work t.1 b))
        =
      alg1Step2Value cfg b :=
    RegEncoding.toNat_writeNat_of_lt
      (extendHi cfg.env.data)
      (alg1Step2Value cfg b)
      (RegEncoding.writeNat cfg.env.work t.1 b)
      hslt

  have hover :
      RegEncoding.writeNat
          (extendHi cfg.env.data)
          y.1
          (RegEncoding.writeNat
            (extendHi cfg.env.data)
            (alg1Step2Value cfg b)
            (RegEncoding.writeNat cfg.env.work t.1 b))
        =
      RegEncoding.writeNat
        (extendHi cfg.env.data)
        y.1
        (RegEncoding.writeNat cfg.env.work t.1 b) :=
    writeNat_overwrite_same_reg
      (extendHi cfg.env.data)
      y.1
      (alg1Step2Value cfg b)
      (RegEncoding.writeNat cfg.env.work t.1 b)

  rw [smul_smul]
  simp [
    alg1Step2IdealFourierCoeff,
    alg1Step2QFTScale,
    ASize,
    hread,
    hover
  ]

lemma alg1_step2_branch_norm_eq_preIQFT_norm
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis)
    (t : Fin (ASize cfg.env.work)) :
    ‖qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
        (qs.ket (RegEncoding.writeNat cfg.env.work t.1 b))
        -
        qs.ket
          (RegEncoding.writeNat
            (extendHi cfg.env.data)
            (alg1Step2Value cfg b)
            (RegEncoding.writeNat cfg.env.work t.1 b))‖
      =
    ‖
      qs.eval
        (Gate.PhaseProd
          (alg1Step2Phase cfg)
          cfg.env.work
          (extendHi cfg.env.data))
        (qs.eval
          (Gate.QFT (extendHi cfg.env.data))
          (qs.ket (RegEncoding.writeNat cfg.env.work t.1 b)))
      -
      qs.eval
        (Gate.QFT (extendHi cfg.env.data))
        (qs.ket
          (RegEncoding.writeNat
            (extendHi cfg.env.data)
            (alg1Step2Value cfg b)
            (RegEncoding.writeNat cfg.env.work t.1 b)))‖ := by
  let xext : Reg := extendHi cfg.env.data

  let source : qs.State :=
    qs.eval
      (Gate.PhaseProd
        (alg1Step2Phase cfg)
        cfg.env.work
        xext)
      (qs.eval
        (Gate.QFT xext)
        (qs.ket (RegEncoding.writeNat cfg.env.work t.1 b)))

  let targetFourier : qs.State :=
    qs.eval
      (Gate.QFT xext)
      (qs.ket
        (RegEncoding.writeNat
          xext
          (alg1Step2Value cfg b)
          (RegEncoding.writeNat cfg.env.work t.1 b)))

  have hU2 :
      qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
        (qs.ket (RegEncoding.writeNat cfg.env.work t.1 b))
      =
      qs.eval (IQFT xext) source := by
    simp [
      ModMulConfig.U2,
      step2,
      alg1Step2Phase,
      xext,
      source,
      qs.eval_seq
    ]

  have htarget :
      qs.eval (IQFT xext) targetFourier
        =
      qs.ket
        (RegEncoding.writeNat
          xext
          (alg1Step2Value cfg b)
          (RegEncoding.writeNat cfg.env.work t.1 b)) := by
    simpa [IQFT, targetFourier] using
      qs.eval_adj_apply
        (Gate.QFT xext)
        (qs.ket
          (RegEncoding.writeNat
            xext
            (alg1Step2Value cfg b)
            (RegEncoding.writeNat cfg.env.work t.1 b)))

  calc
    ‖qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
        (qs.ket (RegEncoding.writeNat cfg.env.work t.1 b))
        -
        qs.ket
          (RegEncoding.writeNat
            xext
            (alg1Step2Value cfg b)
            (RegEncoding.writeNat cfg.env.work t.1 b))‖
      =
    ‖qs.eval (IQFT xext) source
        - qs.eval (IQFT xext) targetFourier‖ := by
        rw [hU2, ← htarget]
    _ =
    ‖qs.eval (IQFT xext) (source - targetFourier)‖ := by
        rw [qs.hsub]
    _ =
    ‖source - targetFourier‖ :=
        eval_norm_preserved qs (IQFT xext) (source - targetFourier)
    _ =
    ‖
      qs.eval
        (Gate.PhaseProd
          (alg1Step2Phase cfg)
          cfg.env.work
          (extendHi cfg.env.data))
        (qs.eval
          (Gate.QFT (extendHi cfg.env.data))
          (qs.ket (RegEncoding.writeNat cfg.env.work t.1 b)))
      -
      qs.eval
        (Gate.QFT (extendHi cfg.env.data))
        (qs.ket
          (RegEncoding.writeNat
            (extendHi cfg.env.data)
            (alg1Step2Value cfg b)
            (RegEncoding.writeNat cfg.env.work t.1 b)))‖ := by
        rfl

/-! =========================================================
    Fourier phase stability
========================================================= -/
private lemma qftPhase_eq_exp_I
    (L x y : ℕ)
    (hL : 0 < L) :
    qftPhase L x y =
      Complex.exp
        (Complex.I *
          (((2 * Real.pi / (L : ℝ)) *
              (x : ℝ) *
              (y : ℝ) : ℝ) : ℂ)) := by
  have hL0C : (L : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hL

  rw [qftPhase, ωPow, ω, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp [hL0C]

private lemma qftPhase_add_left_eq
    (L x r y : ℕ)
    (hL : 0 < L) :
    qftPhase L (x + r) y =
      qftPhase L x y *
        Complex.exp
          (Complex.I *
            (((2 * Real.pi / (L : ℝ)) *
                (r : ℝ) *
                (y : ℝ) : ℝ) : ℂ)) := by
  rw [
    qftPhase_eq_exp_I L (x + r) y hL,
    qftPhase_eq_exp_I L x y hL,
    ← Complex.exp_add
  ]
  congr 1
  push_cast
  ring

private lemma norm_exp_I_sub_exp_I_le
    (a b : ℝ) :
    ‖Complex.exp (Complex.I * (a : ℂ))
        - Complex.exp (Complex.I * (b : ℂ))‖
      ≤
    |a - b| := by
  have hfactor :
      Complex.exp (Complex.I * (a : ℂ))
          - Complex.exp (Complex.I * (b : ℂ))
        =
      Complex.exp (Complex.I * (b : ℂ)) *
        (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
    calc
      Complex.exp (Complex.I * (a : ℂ))
          - Complex.exp (Complex.I * (b : ℂ))
        =
      Complex.exp (Complex.I * (b : ℂ)) *
          Complex.exp (Complex.I * ((a - b : ℝ) : ℂ))
          -
          Complex.exp (Complex.I * (b : ℂ)) := by
            rw [← Complex.exp_add]
            congr 1
            push_cast
            ring_nf
      _ =
      Complex.exp (Complex.I * (b : ℂ)) *
        (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
          ring

  rw [
    hfactor,
    norm_mul,
    Complex.norm_exp_I_mul_ofReal,
    one_mul,
    Complex.norm_exp_I_mul_ofReal_sub_one
  ]

  change |2 * Real.sin ((a - b) / 2)| ≤ |a - b|

  calc
    |2 * Real.sin ((a - b) / 2)|
        =
      2 * |Real.sin ((a - b) / 2)| := by
        rw [abs_mul, abs_of_nonneg]
        norm_num
    _ ≤
      2 * |(a - b) / 2| :=
      mul_le_mul_of_nonneg_left
        Real.abs_sin_le_abs
        (by norm_num)
    _ = |a - b| := by
      rw [abs_div]
      have htwo_abs : |(2 : ℝ)| = 2 := by norm_num
      rw [htwo_abs]
      ring_nf

lemma alg1_step2_fourier_coeff_error_bound
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis)
    (t : Fin (ASize cfg.env.work))
    (_hb :
      GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b)
    (ht : t ∈ alg1GoodLabels cfg b)
    (y : Fin (ASize (extendHi cfg.env.data))) :
    ‖alg1Step2ActualFourierCoeff cfg b t y
        - alg1Step2IdealFourierCoeff cfg b y‖
      ≤
    (2 * Real.pi * η) /
      Real.sqrt (ASize (extendHi cfg.env.data) : ℝ) := by
  let L : ℕ := ASize (extendHi cfg.env.data)
  let x : ℕ := RegEncoding.toNat cfg.env.data b
  let r : ℕ := alg1TargetResidue cfg b
  let a : ℝ := (cfg.env.N : ℝ) * alg1WorkFraction cfg t

  let θa : ℝ :=
    (2 * Real.pi / (L : ℝ)) * a * (y.1 : ℝ)

  let θr : ℝ :=
    (2 * Real.pi / (L : ℝ)) * (r : ℝ) * (y.1 : ℝ)

  have hL : 0 < L := by
    dsimp [L, ASize]
    positivity

  have hLR : (0 : ℝ) < (L : ℝ) := by
    exact_mod_cast hL

  have hLne : (L : ℝ) ≠ 0 :=
    ne_of_gt hLR

  have hsqrtpos : 0 < Real.sqrt (L : ℝ) :=
    Real.sqrt_pos.2 hLR

  have hη : 0 < η :=
    cfg.env.precision.1

  have hdelta :
      |a - (r : ℝ)| < η := by
    simpa [a, r, alg1Step2ShiftDiscrepancy] using
      (alg1_step2_good_label_shift_discrepancy_lt cfg b t ht)

  have hylt : (y.1 : ℝ) < (L : ℝ) := by
    dsimp [L]
    exact_mod_cast y.isLt

  have hydiv_nonneg :
      0 ≤ (y.1 : ℝ) / (L : ℝ) :=
    div_nonneg (by positivity) hLR.le

  have hydiv_le_one :
      (y.1 : ℝ) / (L : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hLR).2
    nlinarith [hylt.le]

  have hprod :
      ((y.1 : ℝ) / (L : ℝ)) * |a - (r : ℝ)| ≤ η := by
    calc
      ((y.1 : ℝ) / (L : ℝ)) * |a - (r : ℝ)|
          ≤
        ((y.1 : ℝ) / (L : ℝ)) * η :=
        mul_le_mul_of_nonneg_left hdelta.le hydiv_nonneg
      _ ≤ 1 * η :=
        mul_le_mul_of_nonneg_right hydiv_le_one hη.le
      _ = η := one_mul _

  have hθsub :
      θa - θr =
        (2 * Real.pi) *
          (((y.1 : ℝ) / (L : ℝ)) *
            (a - (r : ℝ))) := by
    dsimp [θa, θr]
    field_simp [hLne]

  have htwopi_nonneg : 0 ≤ 2 * Real.pi := by
    positivity

  have hθbound :
      |θa - θr| ≤ 2 * Real.pi * η := by
    rw [
      hθsub,
      abs_mul,
      abs_of_nonneg htwopi_nonneg,
      abs_mul,
      abs_of_nonneg hydiv_nonneg
    ]
    exact mul_le_mul_of_nonneg_left hprod htwopi_nonneg

  have hphasebound :
      ‖Complex.exp (Complex.I * (θa : ℂ))
          - Complex.exp (Complex.I * (θr : ℂ))‖
        ≤
      2 * Real.pi * η := by
    calc
      ‖Complex.exp (Complex.I * (θa : ℂ))
          - Complex.exp (Complex.I * (θr : ℂ))‖
        ≤ |θa - θr| :=
          norm_exp_I_sub_exp_I_le θa θr
      _ ≤ 2 * Real.pi * η := hθbound

  have hactual :
      alg1Step2Phase cfg * Complex.I *
          ((t.1 : ℂ) * (y.1 : ℂ))
        =
      Complex.I * (θa : ℂ) := by
    rw [alg1_step2_phase_normalization cfg t y]
    dsimp [θa, a, L]
    push_cast
    ring

  have hshift :
      qftPhase L (x + r) y.1 =
        qftPhase L x y.1 *
          Complex.exp (Complex.I * (θr : ℂ)) := by
    simpa [θr] using
      (qftPhase_add_left_eq L x r y.1 hL)

  have hqft_norm :
      ‖qftPhase L x y.1‖ = 1 := by
    rw [qftPhase_eq_exp_I L x y.1 hL]
    exact Complex.norm_exp_I_mul_ofReal _

  have hscale_norm :
      ‖alg1Step2QFTScale cfg‖ =
        1 / Real.sqrt (L : ℝ) := by
    dsimp [alg1Step2QFTScale, L]
    rw [Complex.norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos hsqrtpos]

  change
    ‖alg1Step2QFTScale cfg *
        qftPhase L x y.1 *
        Complex.exp
          (alg1Step2Phase cfg * Complex.I *
            ((t.1 : ℂ) * (y.1 : ℂ)))
        -
        alg1Step2QFTScale cfg *
          qftPhase L (x + r) y.1‖
      ≤
    (2 * Real.pi * η) / Real.sqrt (L : ℝ)

  rw [hactual, hshift]

  calc
    ‖alg1Step2QFTScale cfg *
        qftPhase L x y.1 *
        Complex.exp (Complex.I * (θa : ℂ))
        -
        alg1Step2QFTScale cfg *
          (qftPhase L x y.1 *
            Complex.exp (Complex.I * (θr : ℂ)))‖
      =
    ‖(alg1Step2QFTScale cfg * qftPhase L x y.1) *
        (Complex.exp (Complex.I * (θa : ℂ))
          - Complex.exp (Complex.I * (θr : ℂ)))‖ := by
        congr 1
        ring
    _ =
      ‖alg1Step2QFTScale cfg‖ *
        ‖qftPhase L x y.1‖ *
        ‖Complex.exp (Complex.I * (θa : ℂ))
          - Complex.exp (Complex.I * (θr : ℂ))‖ := by
        rw [norm_mul, norm_mul]
    _ =
      (1 / Real.sqrt (L : ℝ)) *
        ‖Complex.exp (Complex.I * (θa : ℂ))
          - Complex.exp (Complex.I * (θr : ℂ))‖ := by
        rw [hscale_norm, hqft_norm]
        ring
    _ ≤
      (1 / Real.sqrt (L : ℝ)) *
        (2 * Real.pi * η) :=
      mul_le_mul_of_nonneg_left
        hphasebound
        (le_of_lt (div_pos zero_lt_one hsqrtpos))
    _ =
      (2 * Real.pi * η) / Real.sqrt (L : ℝ) := by
      ring

/--
The labels of the Fourier packet are pairwise distinct.

This is the elementary injectivity of writing different values to the same
whole register.
-/
lemma alg1_step2_xext_fourier_label_injective
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis)
    (t : Fin (ASize cfg.env.work)) :
    ∀ y z : Fin (ASize (extendHi cfg.env.data)),
      RegEncoding.writeNat
          (extendHi cfg.env.data)
          y.1
          (RegEncoding.writeNat cfg.env.work t.1 b)
        =
      RegEncoding.writeNat
          (extendHi cfg.env.data)
          z.1
          (RegEncoding.writeNat cfg.env.work t.1 b) →
      y = z := by
  intro y z hEq
  apply Fin.ext
  calc
    y.1
        =
      RegEncoding.toNat (extendHi cfg.env.data)
        (RegEncoding.writeNat
          (extendHi cfg.env.data)
          y.1
          (RegEncoding.writeNat cfg.env.work t.1 b)) := by
            symm
            exact
              RegEncoding.toNat_writeNat_of_lt
                (extendHi cfg.env.data)
                y.1
                (RegEncoding.writeNat cfg.env.work t.1 b)
                y.isLt
    _ =
      RegEncoding.toNat (extendHi cfg.env.data)
        (RegEncoding.writeNat
          (extendHi cfg.env.data)
          z.1
          (RegEncoding.writeNat cfg.env.work t.1 b)) := by
            rw [hEq]
    _ = z.1 :=
      RegEncoding.toNat_writeNat_of_lt
        (extendHi cfg.env.data)
        z.1
        (RegEncoding.writeNat cfg.env.work t.1 b)
        z.isLt

/--
The normalized orthogonal Fourier packet has norm at most `2π η`.
-/
lemma alg1_step2_normalized_fourier_packet_bound
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis)
    (t : Fin (ASize cfg.env.work))
    (hb :
      GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b)
    (ht : t ∈ alg1GoodLabels cfg b) :
    ‖(∑ y : Fin (ASize (extendHi cfg.env.data)),
        alg1Step2ActualFourierCoeff cfg b t y •
          qs.ket
            (RegEncoding.writeNat
              (extendHi cfg.env.data)
              y.1
              (RegEncoding.writeNat cfg.env.work t.1 b)))
      -
      ∑ y : Fin (ASize (extendHi cfg.env.data)),
        alg1Step2IdealFourierCoeff cfg b y •
          qs.ket
            (RegEncoding.writeNat
              (extendHi cfg.env.data)
              y.1
              (RegEncoding.writeNat cfg.env.work t.1 b))‖
      ≤ 2 * Real.pi * η := by
  classical

  let L : ℕ := ASize (extendHi cfg.env.data)

  let C : ℝ := 2 * Real.pi * η

  let ε : ℝ := C / Real.sqrt (L : ℝ)

  let label : Fin L → qs.Basis :=
    fun y =>
      RegEncoding.writeNat
        (extendHi cfg.env.data)
        y.1
        (RegEncoding.writeNat cfg.env.work t.1 b)

  let δ : Fin L → ℂ :=
    fun y =>
      alg1Step2ActualFourierCoeff cfg b t y
        - alg1Step2IdealFourierCoeff cfg b y

  let P : qs.State :=
    ∑ y : Fin L, δ y • qs.ket (label y)

  have hflat :
      (∑ y : Fin (ASize (extendHi cfg.env.data)),
        alg1Step2ActualFourierCoeff cfg b t y •
          qs.ket
            (RegEncoding.writeNat
              (extendHi cfg.env.data)
              y.1
              (RegEncoding.writeNat cfg.env.work t.1 b)))
      -
      ∑ y : Fin (ASize (extendHi cfg.env.data)),
        alg1Step2IdealFourierCoeff cfg b y •
          qs.ket
            (RegEncoding.writeNat
              (extendHi cfg.env.data)
              y.1
              (RegEncoding.writeNat cfg.env.work t.1 b))
      =
      P := by
    dsimp [P, δ, label, L]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y hy
    rw [← sub_smul]

  have hLposN : 0 < L := by
    dsimp [L, ASize]
    positivity

  have hLpos : (0 : ℝ) < (L : ℝ) := by
    exact_mod_cast hLposN

  have hLne : (L : ℝ) ≠ 0 :=
    ne_of_gt hLpos

  have hsqrtpos : 0 < Real.sqrt (L : ℝ) :=
    Real.sqrt_pos.2 hLpos

  have hsqrt_sq :
      (Real.sqrt (L : ℝ)) ^ 2 = (L : ℝ) :=
    Real.sq_sqrt hLpos.le

  have hη : 0 < η :=
    cfg.env.precision.1

  have hCpos : 0 < C := by
    dsimp [C]
    exact mul_pos (mul_pos (by norm_num) Real.pi_pos) hη

  have hεnonneg : 0 ≤ ε := by
    dsimp [ε]
    exact div_nonneg hCpos.le hsqrtpos.le

  have hlabel_ne :
      ∀ y z : Fin L, y ≠ z → label y ≠ label z := by
    intro y z hyz hEq
    apply hyz
    apply alg1_step2_xext_fourier_label_injective qs cfg b t y z
    simpa [label] using hEq

  have horth :
      ∀ y ∈ (Finset.univ : Finset (Fin L)),
        ∀ z ∈ (Finset.univ : Finset (Fin L)),
          y ≠ z →
          inner ℂ
            (δ y • qs.ket (label y))
            (δ z • qs.ket (label z))
            =
          0 := by
    intro y hy z hz hyz
    rw [
      inner_smul_left,
      inner_smul_right,
      qs.ket_inner_eq_zero_of_ne (hlabel_ne y z hyz)
    ]
    simp

  have hsq :
      ‖P‖ ^ 2
        =
      ∑ y : Fin L, ‖δ y • qs.ket (label y)‖ ^ 2 := by
    dsimp [P]
    exact
      alg1_step2_norm_sq_sum_eq_sum_norm_sq_of_orthogonal
        (qs := qs)
        (Finset.univ : Finset (Fin L))
        (fun y => δ y • qs.ket (label y))
        horth

  have hcoeff :
      ∀ y : Fin L, ‖δ y‖ ≤ ε := by
    intro y
    simpa [δ, ε, C, L] using
      (alg1_step2_fourier_coeff_error_bound
        qs cfg b t hb ht y)

  have hterm_bound :
      ∀ y : Fin L,
        ‖δ y • qs.ket (label y)‖ ^ 2 ≤ ε ^ 2 := by
    intro y

    have hδnonneg : 0 ≤ ‖δ y‖ :=
      norm_nonneg _

    have hdiff : 0 ≤ ε - ‖δ y‖ :=
      sub_nonneg.mpr (hcoeff y)

    have hsum : 0 ≤ ε + ‖δ y‖ :=
      add_nonneg hεnonneg hδnonneg

    have hsq_le : ‖δ y‖ ^ 2 ≤ ε ^ 2 := by
      nlinarith [mul_nonneg hdiff hsum]

    calc
      ‖δ y • qs.ket (label y)‖ ^ 2
          =
        ‖δ y‖ ^ 2 := by
          simp [norm_smul, ket_norm_one qs]
      _ ≤ ε ^ 2 := hsq_le

  have hsum_bound :
      ∑ y : Fin L, ‖δ y • qs.ket (label y)‖ ^ 2
        ≤
      (L : ℝ) * ε ^ 2 := by
    calc
      ∑ y : Fin L, ‖δ y • qs.ket (label y)‖ ^ 2
          ≤
        ∑ y : Fin L, ε ^ 2 := by
          exact Finset.sum_le_sum fun y hy => hterm_bound y
      _ = (L : ℝ) * ε ^ 2 := by
          simp

  have hscale :
      (L : ℝ) * ε ^ 2 = C ^ 2 := by
    dsimp [ε]
    rw [div_pow, hsqrt_sq]
    field_simp [hLne]

  have henergy : ‖P‖ ^ 2 ≤ C ^ 2 := by
    calc
      ‖P‖ ^ 2
          =
        ∑ y : Fin L, ‖δ y • qs.ket (label y)‖ ^ 2 := hsq
      _ ≤ (L : ℝ) * ε ^ 2 := hsum_bound
      _ = C ^ 2 := hscale

  have hnorm : ‖P‖ ≤ C := by
    by_contra hnot

    have hlt : C < ‖P‖ :=
      lt_of_not_ge hnot

    have hPpos : 0 < ‖P‖ :=
      lt_of_le_of_lt hCpos.le hlt

    have hprod :
        0 < (‖P‖ - C) * (‖P‖ + C) := by
      exact
        mul_pos
          (sub_pos.mpr hlt)
          (add_pos_of_pos_of_nonneg hPpos hCpos.le)

    nlinarith [henergy, hprod]

  calc
    ‖(∑ y : Fin (ASize (extendHi cfg.env.data)),
        alg1Step2ActualFourierCoeff cfg b t y •
          qs.ket
            (RegEncoding.writeNat
              (extendHi cfg.env.data)
              y.1
              (RegEncoding.writeNat cfg.env.work t.1 b)))
      -
      ∑ y : Fin (ASize (extendHi cfg.env.data)),
        alg1Step2IdealFourierCoeff cfg b y •
          qs.ket
            (RegEncoding.writeNat
              (extendHi cfg.env.data)
              y.1
              (RegEncoding.writeNat cfg.env.work t.1 b))‖
        =
      ‖P‖ := by
        rw [hflat]
    _ ≤ C := hnorm
    _ = 2 * Real.pi * η := by
      rfl

/-! =========================================================
    Final one-label Step-2 theorem
========================================================= -/

/--
Single retained-label fractional-shift stability.
-/
lemma alg1_step2_single_label_fourier_stability
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [Spec]
    [GateSemanticsFacts qs] :
    ∃ Cbranch : ℝ, 0 ≤ Cbranch ∧
      ∀ (η : ℝ) (cfg : ModMulConfig η)
        (b : qs.Basis)
        (t : Fin (ASize cfg.env.work)),
        GoodModMulBasisInput
          qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b →
        t ∈ alg1GoodLabels cfg b →
        ‖qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
            (qs.ket
              (RegEncoding.writeNat cfg.env.work t.1 b))
            -
            qs.ket
              (RegEncoding.writeNat
                (extendHi cfg.env.data)
                (alg1Step2Value cfg b)
                (RegEncoding.writeNat cfg.env.work t.1 b))‖
          ≤ Cbranch * η := by
  refine ⟨2 * Real.pi, ?_, ?_⟩
  · exact mul_nonneg (by norm_num) (le_of_lt Real.pi_pos)

  · intro η cfg b t hb ht
    rw [alg1_step2_branch_norm_eq_preIQFT_norm qs cfg b t]
    rw [
      alg1_step2_actual_preIQFT_packet qs cfg b t hb,
      alg1_step2_ideal_preIQFT_packet qs cfg b t hb
    ]
    simpa using
      (alg1_step2_normalized_fourier_packet_bound
        qs cfg b t hb ht)


/-! =========================================================
    Coherent Step-2 operator bound
========================================================= -/

lemma alg1_good_labels_same_work_residue
    [QSemantics] [RegEncoding QSemantics.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b b' : QSemantics.Basis)
    (t : Fin (ASize cfg.env.work))
    (ht : t ∈ alg1GoodLabels cfg b)
    (ht' : t ∈ alg1GoodLabels cfg b') :
    alg1TargetResidue cfg b = alg1TargetResidue cfg b' := by
  let r : ℕ := alg1TargetResidue cfg b
  let r' : ℕ := alg1TargetResidue cfg b'
  let d : ℝ := (cfg.env.N : ℝ) * alg1WorkFraction cfg t

  have hδ :
      |d - (r : ℝ)| < η := by
    simpa [d, r, alg1Step2ShiftDiscrepancy] using
      (alg1_step2_good_label_shift_discrepancy_lt cfg b t ht)

  have hδ' :
      |d - (r' : ℝ)| < η := by
    simpa [d, r', alg1Step2ShiftDiscrepancy] using
      (alg1_step2_good_label_shift_discrepancy_lt cfg b' t ht')

  have hδr :
      |(r : ℝ) - d| < η := by
    rw [show (r : ℝ) - d = -(d - (r : ℝ)) by ring, abs_neg]
    exact hδ

  have hdist :
      |(r : ℝ) - (r' : ℝ)| < 1 := by
    calc
      |(r : ℝ) - (r' : ℝ)|
          =
        |((r : ℝ) - d) + (d - (r' : ℝ))| := by
          congr 1
          ring
      _ ≤ |(r : ℝ) - d| + |d - (r' : ℝ)| :=
        abs_add_le _ _
      _ < η + η :=
        add_lt_add hδr hδ'
      _ < 1 := by
        nlinarith [cfg.env.precision.2.1]

  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  ·
    have hnonpos : (r : ℝ) - (r' : ℝ) ≤ 0 := by
      apply sub_nonpos.mpr
      exact_mod_cast Nat.le_of_lt hlt

    have hone : (1 : ℝ) ≤ (r' : ℝ) - (r : ℝ) := by
      have hsucc : r + 1 ≤ r' :=
        Nat.succ_le_iff.mpr hlt
      have hcast : (r : ℝ) + 1 ≤ (r' : ℝ) := by
        exact_mod_cast hsucc
      linarith

    rw [abs_of_nonpos hnonpos] at hdist
    linarith

  ·
    have hnonneg : 0 ≤ (r : ℝ) - (r' : ℝ) := by
      apply sub_nonneg.mpr
      exact_mod_cast Nat.le_of_lt hgt

    have hone : (1 : ℝ) ≤ (r : ℝ) - (r' : ℝ) := by
      have hsucc : r' + 1 ≤ r :=
        Nat.succ_le_iff.mpr hgt
      have hcast : (r' : ℝ) + 1 ≤ (r : ℝ) := by
        exact_mod_cast hsucc
      linarith

    rw [abs_of_nonneg hnonneg] at hdist
    linarith

private lemma alg1_work_sector_inner_zero
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    (xext work : Reg)
    (hXW : Disjoint xext work)
    (b b' : qs.Basis)
    (t u : Fin (ASize work))
    (htu : t ≠ u)
    (α β : Fin (ASize xext) → ℂ) :
    inner ℂ
      (∑ y : Fin (ASize xext),
        α y •
          qs.ket
            (RegEncoding.writeNat xext y.1
              (RegEncoding.writeNat work t.1 b)))
      (∑ z : Fin (ASize xext),
        β z •
          qs.ket
            (RegEncoding.writeNat xext z.1
              (RegEncoding.writeNat work u.1 b')))
      =
    0 := by
  classical

  have hWX : Disjoint work xext := by
    rcases hXW with h | h
    · exact Or.inr h
    · exact Or.inl h

  rw [sum_inner]
  refine Finset.sum_eq_zero ?_
  intro y hy
  rw [inner_sum]
  refine Finset.sum_eq_zero ?_
  intro z hz

  have hlabel :
      RegEncoding.writeNat xext y.1
          (RegEncoding.writeNat work t.1 b)
        ≠
      RegEncoding.writeNat xext z.1
          (RegEncoding.writeNat work u.1 b') := by
    intro hEq
    apply htu
    apply Fin.ext

    calc
      t.1
          =
        RegEncoding.toNat work
          (RegEncoding.writeNat xext y.1
            (RegEncoding.writeNat work t.1 b)) := by
              symm
              calc
                RegEncoding.toNat work
                    (RegEncoding.writeNat xext y.1
                      (RegEncoding.writeNat work t.1 b))
                    =
                  RegEncoding.toNat work
                    (RegEncoding.writeNat work t.1 b) :=
                  RegEncoding.toNat_left_write_right
                    work xext hWX
                    (RegEncoding.writeNat work t.1 b) y.1
                _ = t.1 :=
                  RegEncoding.toNat_writeNat_of_lt
                    work t.1 b t.isLt
      _ =
        RegEncoding.toNat work
          (RegEncoding.writeNat xext z.1
            (RegEncoding.writeNat work u.1 b')) := by
              rw [hEq]
      _ = u.1 := by
              calc
                RegEncoding.toNat work
                    (RegEncoding.writeNat xext z.1
                      (RegEncoding.writeNat work u.1 b'))
                    =
                  RegEncoding.toNat work
                    (RegEncoding.writeNat work u.1 b') :=
                  RegEncoding.toNat_left_write_right
                    work xext hWX
                    (RegEncoding.writeNat work u.1 b') z.1
                _ = u.1 :=
                  RegEncoding.toNat_writeNat_of_lt
                    work u.1 b' u.isLt

  rw [
    inner_smul_left,
    inner_smul_right,
    qs.ket_inner_eq_zero_of_ne hlabel
  ]
  simp

private lemma alg1_step2_preIQFT_work_packet
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis)
    (t : Fin (ASize cfg.env.work)) :
    ∃ α : Fin (ASize (extendHi cfg.env.data)) → ℂ,
      qs.eval
          (Gate.PhaseProd
            (alg1Step2Phase cfg)
            cfg.env.work
            (extendHi cfg.env.data))
          (qs.eval
            (Gate.QFT (extendHi cfg.env.data))
            (qs.ket (RegEncoding.writeNat cfg.env.work t.1 b)))
        =
      ∑ y : Fin (ASize (extendHi cfg.env.data)),
        α y •
          qs.ket
            (RegEncoding.writeNat
              (extendHi cfg.env.data)
              y.1
              (RegEncoding.writeNat cfg.env.work t.1 b)) := by
  classical

  let xext : Reg := extendHi cfg.env.data
  let base : qs.Basis :=
    RegEncoding.writeNat cfg.env.work t.1 b

  have hXW : Disjoint xext cfg.env.work := by
    simpa [xext] using cfg.layout.1

  have hWX : Disjoint cfg.env.work xext := by
    rcases hXW with h | h
    · exact Or.inr h
    · exact Or.inl h

  refine ⟨
    fun y =>
      ((1 / Real.sqrt ((ASize xext : ℕ) : ℝ) : ℂ) *
        qftPhase
          (ASize xext)
          (RegEncoding.toNat xext base)
          y.1 *
        Complex.exp
          (alg1Step2Phase cfg * Complex.I *
            ((t.1 : ℂ) * (y.1 : ℂ)))),
    ?_
  ⟩

  have hphase :
      ∀ y : Fin (ASize xext),
        qs.eval
            (Gate.PhaseProd
              (alg1Step2Phase cfg)
              cfg.env.work
              xext)
            (qs.ket
              (RegEncoding.writeNat xext y.1 base))
          =
        Complex.exp
          (alg1Step2Phase cfg * Complex.I *
            ((t.1 : ℂ) * (y.1 : ℂ))) •
          qs.ket
            (RegEncoding.writeNat xext y.1 base) := by
    intro y

    have hwork :
        RegEncoding.toNat cfg.env.work
          (RegEncoding.writeNat xext y.1 base)
          =
        t.1 := by
      calc
        RegEncoding.toNat cfg.env.work
            (RegEncoding.writeNat xext y.1 base)
            =
          RegEncoding.toNat cfg.env.work base :=
          RegEncoding.toNat_left_write_right
            cfg.env.work xext hWX base y.1
        _ = t.1 :=
          RegEncoding.toNat_writeNat_of_lt
            cfg.env.work t.1 b t.isLt

    have hxext :
        RegEncoding.toNat xext
          (RegEncoding.writeNat xext y.1 base)
          =
        y.1 :=
      RegEncoding.toNat_writeNat_of_lt
        xext y.1 base y.isLt

    simpa [hwork, hxext] using
      (GateSemanticsFacts.eval_PhaseProd_ket
        qs
        (alg1Step2Phase cfg)
        cfg.env.work
        xext
        (RegEncoding.writeNat xext y.1 base)
        hWX)

  change
    qs.eval
        (Gate.PhaseProd
          (alg1Step2Phase cfg)
          cfg.env.work
          xext)
        (qs.eval (Gate.QFT xext) (qs.ket base))
      =
    _

  rw [QFTSemantics.eval_QFT_ket]
  rw [qs.eval_smul, eval_finset_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [qs.eval_smul, hphase y]
  simp [xext, base, ASize, smul_smul, mul_assoc]

/-- A QFT of an `extendHi data` write remains in the same work sector. -/
private lemma alg1_qft_xext_work_packet
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (xext work : Reg)
    (b : qs.Basis)
    (u : Fin (ASize work))
    (v : ℕ) :
    ∃ β : Fin (ASize xext) → ℂ,
      qs.eval
          (Gate.QFT xext)
          (qs.ket
            (RegEncoding.writeNat xext v
              (RegEncoding.writeNat work u.1 b)))
        =
      ∑ z : Fin (ASize xext),
        β z •
          qs.ket
            (RegEncoding.writeNat xext z.1
              (RegEncoding.writeNat work u.1 b)) := by
  classical

  let base : qs.Basis :=
    RegEncoding.writeNat xext v
      (RegEncoding.writeNat work u.1 b)

  refine ⟨
    fun z =>
      (1 / Real.sqrt ((ASize xext : ℕ) : ℝ) : ℂ) *
        qftPhase
          (ASize xext)
          (RegEncoding.toNat xext base)
          z.1,
    ?_
  ⟩

  change
    qs.eval (Gate.QFT xext) (qs.ket base)
      =
    _

  rw [QFTSemantics.eval_QFT_ket, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  rw [smul_smul]
  simp [base, ASize, writeNat_overwrite_same_reg]


private lemma alg1_step2_actual_ref_work_cross_zero
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b b' : qs.Basis)
    (t u : Fin (ASize cfg.env.work))
    (htu : t ≠ u) :
    inner ℂ
      (qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
        (qs.ket (RegEncoding.writeNat cfg.env.work t.1 b)))
      (qs.ket
        (RegEncoding.writeNat
          (extendHi cfg.env.data)
          (alg1Step2Value cfg b')
          (RegEncoding.writeNat cfg.env.work u.1 b')))
      =
    0 := by
  classical

  let xext : Reg := extendHi cfg.env.data

  have hXW : Disjoint xext cfg.env.work := by
    simpa [xext] using cfg.layout.1

  have hU2 :
      qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
        (qs.ket (RegEncoding.writeNat cfg.env.work t.1 b))
      =
      qs.eval (IQFT xext)
        (qs.eval
          (Gate.PhaseProd
            (alg1Step2Phase cfg)
            cfg.env.work
            xext)
          (qs.eval
            (Gate.QFT xext)
            (qs.ket (RegEncoding.writeNat cfg.env.work t.1 b)))) := by
    simp [ModMulConfig.U2, step2, xext, alg1Step2Phase, qs.eval_seq]

  have hrestore :
      qs.eval (IQFT xext)
        (qs.eval
          (Gate.QFT xext)
          (qs.ket
            (RegEncoding.writeNat
              xext
              (alg1Step2Value cfg b')
              (RegEncoding.writeNat cfg.env.work u.1 b'))))
        =
      qs.ket
        (RegEncoding.writeNat
          xext
          (alg1Step2Value cfg b')
          (RegEncoding.writeNat cfg.env.work u.1 b')) := by
    simpa [IQFT] using
      qs.eval_adj_apply
        (Gate.QFT xext)
        (qs.ket
          (RegEncoding.writeNat
            xext
            (alg1Step2Value cfg b')
            (RegEncoding.writeNat cfg.env.work u.1 b')))

  rcases alg1_step2_preIQFT_work_packet qs cfg b t with
    ⟨α, hα⟩

  rcases
      alg1_qft_xext_work_packet
        qs xext cfg.env.work b' u
        (alg1Step2Value cfg b') with
    ⟨β, hβ⟩

  calc
    inner ℂ
        (qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
          (qs.ket (RegEncoding.writeNat cfg.env.work t.1 b)))
        (qs.ket
          (RegEncoding.writeNat
            xext
            (alg1Step2Value cfg b')
            (RegEncoding.writeNat cfg.env.work u.1 b')))
      =
    inner ℂ
      (qs.eval (IQFT xext)
        (qs.eval
          (Gate.PhaseProd
            (alg1Step2Phase cfg)
            cfg.env.work
            xext)
          (qs.eval
            (Gate.QFT xext)
            (qs.ket (RegEncoding.writeNat cfg.env.work t.1 b)))))
      (qs.eval (IQFT xext)
        (qs.eval
          (Gate.QFT xext)
          (qs.ket
            (RegEncoding.writeNat
              xext
              (alg1Step2Value cfg b')
              (RegEncoding.writeNat cfg.env.work u.1 b'))))) := by
        rw [hU2, hrestore]
    _ =
    inner ℂ
      (qs.eval
        (Gate.PhaseProd
          (alg1Step2Phase cfg)
          cfg.env.work
          xext)
        (qs.eval
          (Gate.QFT xext)
          (qs.ket (RegEncoding.writeNat cfg.env.work t.1 b))))
      (qs.eval
        (Gate.QFT xext)
        (qs.ket
          (RegEncoding.writeNat
            xext
            (alg1Step2Value cfg b')
            (RegEncoding.writeNat cfg.env.work u.1 b')))) :=
      qs.inner_preserved _ _ _
    _ = 0 := by
      rw [hα, hβ]
      exact
        alg1_work_sector_inner_zero
          qs xext cfg.env.work hXW b b' t u htu α β

lemma alg1_step2_error_work_orthogonal
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b b' : qs.Basis)
    (t u : Fin (ASize cfg.env.work))
    (htu : t ≠ u) :
    inner ℂ
      (alg1Step2Error qs cfg b t)
      (alg1Step2Error qs cfg b' u)
      =
    0 := by
  classical

  let xext : Reg := extendHi cfg.env.data

  have hXW : Disjoint xext cfg.env.work := by
    simpa [xext] using cfg.layout.1

  have hWX : Disjoint cfg.env.work xext := by
    rcases hXW with h | h
    · exact Or.inr h
    · exact Or.inl h

  have hsource_ne :
      RegEncoding.writeNat cfg.env.work t.1 b
        ≠
      RegEncoding.writeNat cfg.env.work u.1 b' := by
    intro hEq
    apply htu
    apply Fin.ext
    calc
      t.1
          =
        RegEncoding.toNat cfg.env.work
          (RegEncoding.writeNat cfg.env.work t.1 b) := by
            symm
            exact
              RegEncoding.toNat_writeNat_of_lt
                cfg.env.work t.1 b t.isLt
      _ =
        RegEncoding.toNat cfg.env.work
          (RegEncoding.writeNat cfg.env.work u.1 b') := by
            rw [hEq]
      _ = u.1 :=
        RegEncoding.toNat_writeNat_of_lt
          cfg.env.work u.1 b' u.isLt

  have href_ne :
      RegEncoding.writeNat xext
          (alg1Step2Value cfg b)
          (RegEncoding.writeNat cfg.env.work t.1 b)
        ≠
      RegEncoding.writeNat xext
          (alg1Step2Value cfg b')
          (RegEncoding.writeNat cfg.env.work u.1 b') := by
    intro hEq
    apply htu
    apply Fin.ext

    calc
      t.1
          =
        RegEncoding.toNat cfg.env.work
          (RegEncoding.writeNat xext
            (alg1Step2Value cfg b)
            (RegEncoding.writeNat cfg.env.work t.1 b)) := by
              symm
              calc
                RegEncoding.toNat cfg.env.work
                    (RegEncoding.writeNat xext
                      (alg1Step2Value cfg b)
                      (RegEncoding.writeNat cfg.env.work t.1 b))
                    =
                  RegEncoding.toNat cfg.env.work
                    (RegEncoding.writeNat cfg.env.work t.1 b) :=
                  RegEncoding.toNat_left_write_right
                    cfg.env.work xext hWX
                    (RegEncoding.writeNat cfg.env.work t.1 b)
                    (alg1Step2Value cfg b)
                _ = t.1 :=
                  RegEncoding.toNat_writeNat_of_lt
                    cfg.env.work t.1 b t.isLt
      _ =
        RegEncoding.toNat cfg.env.work
          (RegEncoding.writeNat xext
            (alg1Step2Value cfg b')
            (RegEncoding.writeNat cfg.env.work u.1 b')) := by
              rw [hEq]
      _ = u.1 := by
              calc
                RegEncoding.toNat cfg.env.work
                    (RegEncoding.writeNat xext
                      (alg1Step2Value cfg b')
                      (RegEncoding.writeNat cfg.env.work u.1 b'))
                    =
                  RegEncoding.toNat cfg.env.work
                    (RegEncoding.writeNat cfg.env.work u.1 b') :=
                  RegEncoding.toNat_left_write_right
                    cfg.env.work xext hWX
                    (RegEncoding.writeNat cfg.env.work u.1 b')
                    (alg1Step2Value cfg b')
                _ = u.1 :=
                  RegEncoding.toNat_writeNat_of_lt
                    cfg.env.work u.1 b' u.isLt

  have hactual_actual :
      inner ℂ
        (qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
          (qs.ket (RegEncoding.writeNat cfg.env.work t.1 b)))
        (qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
          (qs.ket (RegEncoding.writeNat cfg.env.work u.1 b')))
        =
      0 := by
    calc
      inner ℂ
          (qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
            (qs.ket (RegEncoding.writeNat cfg.env.work t.1 b)))
          (qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
            (qs.ket (RegEncoding.writeNat cfg.env.work u.1 b')))
        =
      inner ℂ
        (qs.ket (RegEncoding.writeNat cfg.env.work t.1 b))
        (qs.ket (RegEncoding.writeNat cfg.env.work u.1 b')) :=
      qs.inner_preserved _ _ _
    _ = 0 :=
      qs.ket_inner_eq_zero_of_ne hsource_ne

  have href_ref :
      inner ℂ
        (qs.ket
          (RegEncoding.writeNat xext
            (alg1Step2Value cfg b)
            (RegEncoding.writeNat cfg.env.work t.1 b)))
        (qs.ket
          (RegEncoding.writeNat xext
            (alg1Step2Value cfg b')
            (RegEncoding.writeNat cfg.env.work u.1 b')))
        =
      0 :=
    qs.ket_inner_eq_zero_of_ne href_ne

  have hactual_ref :
      inner ℂ
        (qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
          (qs.ket (RegEncoding.writeNat cfg.env.work t.1 b)))
        (qs.ket
          (RegEncoding.writeNat xext
            (alg1Step2Value cfg b')
            (RegEncoding.writeNat cfg.env.work u.1 b')))
        =
      0 :=
    alg1_step2_actual_ref_work_cross_zero
      qs cfg b b' t u htu

  have href_actual :
      inner ℂ
        (qs.ket
          (RegEncoding.writeNat xext
            (alg1Step2Value cfg b)
            (RegEncoding.writeNat cfg.env.work t.1 b)))
        (qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
          (qs.ket (RegEncoding.writeNat cfg.env.work u.1 b')))
        =
      0 := by
    have hswap :=
      alg1_step2_actual_ref_work_cross_zero
        qs cfg b' b u t htu.symm

    calc
      inner ℂ
          (qs.ket
            (RegEncoding.writeNat xext
              (alg1Step2Value cfg b)
              (RegEncoding.writeNat cfg.env.work t.1 b)))
          (qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
            (qs.ket (RegEncoding.writeNat cfg.env.work u.1 b')))
        =
      star
        (inner ℂ
          (qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
            (qs.ket (RegEncoding.writeNat cfg.env.work u.1 b')))
          (qs.ket
            (RegEncoding.writeNat xext
              (alg1Step2Value cfg b)
              (RegEncoding.writeNat cfg.env.work t.1 b)))) :=
        (inner_conj_symm _ _).symm
      _ = 0 := by
        rw [hswap]
        simp

  unfold alg1Step2Error
  rw [inner_sub_left, inner_sub_right]
  simp [xext, hactual_actual, hactual_ref, href_actual, href_ref, inner_sub_right]


/-! =========================================================
    Fixed-work coherent Step-2 bound
========================================================= -/

/--
The source labels `writeNat work t b` are injective on a finite family of
clean-work basis inputs.
-/
lemma alg1_step2_source_label_injective_of_good
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (S : Finset (Σ _b : qs.Basis, Fin (ASize cfg.env.work)))
    (hgood :
      ∀ i ∈ S,
        GoodModMulBasisInput
          qs cfg.env.N cfg.env.data cfg.env.work cfg.flag i.1) :
    ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      RegEncoding.writeNat cfg.env.work i.2.1 i.1
        ≠
      RegEncoding.writeNat cfg.env.work j.2.1 j.1 := by
  classical
  intro i hi j hj hij hEq

  have hi_good := hgood i hi
  have hj_good := hgood j hj

  have ht_val : i.2.1 = j.2.1 := by
    calc
      i.2.1 =
          RegEncoding.toNat cfg.env.work
            (RegEncoding.writeNat cfg.env.work i.2.1 i.1) := by
              symm
              exact
                RegEncoding.toNat_writeNat_of_lt
                  cfg.env.work i.2.1 i.1 i.2.isLt
      _ =
          RegEncoding.toNat cfg.env.work
            (RegEncoding.writeNat cfg.env.work j.2.1 j.1) := by
              rw [hEq]
      _ = j.2.1 :=
        RegEncoding.toNat_writeNat_of_lt
          cfg.env.work j.2.1 j.1 j.2.isLt

  have ht : i.2 = j.2 :=
    Fin.ext ht_val

  have hi_zero :
      RegEncoding.writeNat cfg.env.work 0 i.1 = i.1 := by
    simpa [hi_good.2.2.1] using
      (RegEncoding.writeNat_toNat cfg.env.work i.1)

  have hj_zero :
      RegEncoding.writeNat cfg.env.work 0 j.1 = j.1 := by
    simpa [hj_good.2.2.1] using
      (RegEncoding.writeNat_toNat cfg.env.work j.1)

  have hb : i.1 = j.1 := by
    calc
      i.1 =
          RegEncoding.writeNat cfg.env.work 0 i.1 := hi_zero.symm
      _ =
          RegEncoding.writeNat cfg.env.work 0
            (RegEncoding.writeNat cfg.env.work i.2.1 i.1) := by
              symm
              exact
                writeNat_overwrite_same_reg
                  cfg.env.work 0 i.2.1 i.1
      _ =
          RegEncoding.writeNat cfg.env.work 0
            (RegEncoding.writeNat cfg.env.work j.2.1 j.1) := by
              exact congrArg (RegEncoding.writeNat cfg.env.work 0) hEq
      _ =
          RegEncoding.writeNat cfg.env.work 0 j.1 := by
              exact
                writeNat_overwrite_same_reg
                  cfg.env.work 0 j.2.1 j.1
      _ = j.1 := hj_zero

  apply hij
  cases i
  cases j
  simp at hb ht ⊢
  exact ⟨hb, ht⟩

lemma alg1_step2_fixed_work_source_energy
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (S : Finset (Σ _b : qs.Basis, Fin (ASize cfg.env.work)))
    (α : (Σ _b : qs.Basis, Fin (ASize cfg.env.work)) → ℂ)
    (hgood :
      ∀ i ∈ S,
        GoodModMulBasisInput
          qs cfg.env.N cfg.env.data cfg.env.work cfg.flag i.1) :
    ‖∑ i ∈ S,
        α i •
          qs.ket
            (RegEncoding.writeNat cfg.env.work i.2.1 i.1)‖ ^ 2
      =
    ∑ i ∈ S, ‖α i‖ ^ 2 := by
  classical

  have hinj :=
    alg1_step2_source_label_injective_of_good
      qs cfg S hgood

  have horth :
      ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
        inner ℂ
          (α i •
            qs.ket
              (RegEncoding.writeNat cfg.env.work i.2.1 i.1))
          (α j •
            qs.ket
              (RegEncoding.writeNat cfg.env.work j.2.1 j.1))
          =
        0 := by
    intro i hi j hj hij
    rw [
      inner_smul_left,
      inner_smul_right,
      qs.ket_inner_eq_zero_of_ne (hinj i hi j hj hij)
    ]
    simp

  have hsq :=
    alg1_step2_norm_sq_sum_eq_sum_norm_sq_of_orthogonal
      (qs := qs)
      S
      (fun i =>
        α i •
          qs.ket
            (RegEncoding.writeNat cfg.env.work i.2.1 i.1))
      horth

  calc
    ‖∑ i ∈ S,
        α i •
          qs.ket
            (RegEncoding.writeNat cfg.env.work i.2.1 i.1)‖ ^ 2
      =
    ∑ i ∈ S,
      ‖α i •
        qs.ket
          (RegEncoding.writeNat cfg.env.work i.2.1 i.1)‖ ^ 2 := hsq
    _ =
    ∑ i ∈ S, ‖α i‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [norm_smul, ket_norm_one qs]

/-! =========================================================
    Fixed-work coherent Fourier contraction
========================================================= -/

private lemma alg1_qftPhase_add_left
    (L x r y : ℕ) :
    qftPhase L (x + r) y
      =
    qftPhase L x y * qftPhase L r y := by
  unfold qftPhase ωPow
  rw [← pow_add]
  congr 1
  ring


/-! =========================================================
    Step-2 fixed-work Fourier packet contraction
========================================================= -/

private lemma norm_sq_sum_ket_mul_le_of_label_constant
    (qs : QSemantics)
    {ι : Type v}
    (s : Finset ι)
    (a L : ι → ℂ)
    (label : ι → qs.Basis)
    (C : ℝ)
    (hC : 0 ≤ C)
    (hbound : ∀ i ∈ s, ‖L i‖ ≤ C)
    (hconstant :
      ∀ i ∈ s, ∀ j ∈ s,
        label i = label j → L i = L j) :
    ‖∑ i ∈ s, (a i * L i) • qs.ket (label i)‖ ^ 2
      ≤
    C ^ 2 *
      ‖∑ i ∈ s, a i • qs.ket (label i)‖ ^ 2 := by
  classical
  by_cases hs : s.Nonempty
  · rcases hs with ⟨i0, hi0⟩

    let B : Finset qs.Basis := s.image label
    let repr : qs.Basis → ι :=
      fun b =>
        if hb : b ∈ B then
          (Finset.mem_image.mp (by simpa [B] using hb)).choose
        else
          i0

    let A : qs.Basis → ℂ :=
      fun b => ∑ i ∈ s.filter (fun i => label i = b), a i

    let μ : qs.Basis → ℂ :=
      fun b => L (repr b)

    have hrepr_mem :
        ∀ b ∈ B, repr b ∈ s := by
      intro b hb
      dsimp [repr]
      rw [dif_pos hb]
      exact
        (Finset.mem_image.mp (by simpa [B] using hb)).choose_spec.1

    have hrepr_label :
        ∀ b ∈ B, label (repr b) = b := by
      intro b hb
      dsimp [repr]
      rw [dif_pos hb]
      exact
        (Finset.mem_image.mp (by simpa [B] using hb)).choose_spec.2

    have hμ :
        ∀ i ∈ s, μ (label i) = L i := by
      intro i hi
      dsimp [μ]
      apply hconstant
      · exact hrepr_mem (label i)
          (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      · exact hi
      · exact hrepr_label (label i)
          (Finset.mem_image.mpr ⟨i, hi, rfl⟩)

    have hμ_bound :
        ∀ b ∈ B, ‖μ b‖ ≤ C := by
      intro b hb
      dsimp [μ]
      exact hbound (repr b) (hrepr_mem b hb)

    have hplain_group :
        ∑ i ∈ s, a i • qs.ket (label i)
          =
        ∑ b ∈ B, A b • qs.ket b := by
      symm
      calc
        ∑ b ∈ B, A b • qs.ket b
            =
          ∑ b ∈ B,
            ∑ i ∈ s.filter (fun i => label i = b),
              a i • qs.ket b := by
              apply Finset.sum_congr rfl
              intro b hb
              dsimp [A]
              rw [Finset.sum_smul]
        _ =
          ∑ b ∈ B,
            ∑ i ∈ s.filter (fun i => label i = b),
              a i • qs.ket (label i) := by
              apply Finset.sum_congr rfl
              intro b hb
              apply Finset.sum_congr rfl
              intro i hi
              have hilabel : label i = b :=
                (Finset.mem_filter.mp hi).2
              rw [hilabel]
        _ =
          ∑ i ∈ s, a i • qs.ket (label i) := by
              exact
                Finset.sum_fiberwise_of_maps_to
                  (s := s)
                  (t := B)
                  (g := label)
                  (fun i hi =>
                    Finset.mem_image.mpr ⟨i, hi, rfl⟩)
                  (fun i => a i • qs.ket (label i))

    have hmult_group :
        ∑ i ∈ s, (a i * L i) • qs.ket (label i)
          =
        ∑ b ∈ B, (A b * μ b) • qs.ket b := by
      symm
      calc
        ∑ b ∈ B, (A b * μ b) • qs.ket b
            =
          ∑ b ∈ B,
            (∑ i ∈ s.filter (fun i => label i = b),
              a i * μ b) • qs.ket b := by
              apply Finset.sum_congr rfl
              intro b hb
              dsimp [A]
              rw [Finset.sum_mul]
        _ =
          ∑ b ∈ B,
            ∑ i ∈ s.filter (fun i => label i = b),
              (a i * μ b) • qs.ket b := by
              apply Finset.sum_congr rfl
              intro b hb
              rw [Finset.sum_smul]
        _ =
          ∑ b ∈ B,
            ∑ i ∈ s.filter (fun i => label i = b),
              (a i * L i) • qs.ket (label i) := by
              apply Finset.sum_congr rfl
              intro b hb
              apply Finset.sum_congr rfl
              intro i hi
              have hiS : i ∈ s :=
                (Finset.mem_filter.mp hi).1
              have hilabel : label i = b :=
                (Finset.mem_filter.mp hi).2
              rw [← hilabel, hμ i hiS]
        _ =
          ∑ i ∈ s, (a i * L i) • qs.ket (label i) := by
              exact
                Finset.sum_fiberwise_of_maps_to
                  (s := s)
                  (t := B)
                  (g := label)
                  (fun i hi =>
                    Finset.mem_image.mpr ⟨i, hi, rfl⟩)
                  (fun i => (a i * L i) • qs.ket (label i))

    have horth_plain :
        ∀ b ∈ B, ∀ c ∈ B, b ≠ c →
          inner ℂ
            (A b • qs.ket b)
            (A c • qs.ket c)
            =
          0 := by
      intro b hb c hc hbc
      rw [
        inner_smul_left,
        inner_smul_right,
        qs.ket_inner_eq_zero_of_ne hbc
      ]
      simp

    have horth_mult :
        ∀ b ∈ B, ∀ c ∈ B, b ≠ c →
          inner ℂ
            ((A b * μ b) • qs.ket b)
            ((A c * μ c) • qs.ket c)
            =
          0 := by
      intro b hb c hc hbc
      rw [
        inner_smul_left,
        inner_smul_right,
        qs.ket_inner_eq_zero_of_ne hbc
      ]
      simp

    have hplain_sq :
        ‖∑ b ∈ B, A b • qs.ket b‖ ^ 2
          =
        ∑ b ∈ B, ‖A b • qs.ket b‖ ^ 2 :=
      alg1_step2_norm_sq_sum_eq_sum_norm_sq_of_orthogonal
        (qs := qs)
        B
        (fun b => A b • qs.ket b)
        horth_plain

    have hmult_sq :
        ‖∑ b ∈ B, (A b * μ b) • qs.ket b‖ ^ 2
          =
        ∑ b ∈ B, ‖(A b * μ b) • qs.ket b‖ ^ 2 :=
      alg1_step2_norm_sq_sum_eq_sum_norm_sq_of_orthogonal
        (qs := qs)
        B
        (fun b => (A b * μ b) • qs.ket b)
        horth_mult

    have hterm :
        ∀ b ∈ B,
          ‖(A b * μ b) • qs.ket b‖ ^ 2
            ≤
          C ^ 2 * ‖A b • qs.ket b‖ ^ 2 := by
      intro b hb

      have hμ_nonneg : 0 ≤ ‖μ b‖ :=
        norm_nonneg _

      have hμ_sq :
          ‖μ b‖ ^ 2 ≤ C ^ 2 := by
        have hdiff : 0 ≤ C - ‖μ b‖ :=
          sub_nonneg.mpr (hμ_bound b hb)
        have hsum : 0 ≤ C + ‖μ b‖ :=
          add_nonneg hC hμ_nonneg
        have hprod :
            0 ≤ (C - ‖μ b‖) * (C + ‖μ b‖) :=
          mul_nonneg hdiff hsum
        nlinarith

      calc
        ‖(A b * μ b) • qs.ket b‖ ^ 2
            =
          ‖A b * μ b‖ ^ 2 := by
            simp [norm_smul, ket_norm_one qs]
        _ =
          ‖A b‖ ^ 2 * ‖μ b‖ ^ 2 := by
            rw [norm_mul]
            ring
        _ ≤
          ‖A b‖ ^ 2 * C ^ 2 :=
          mul_le_mul_of_nonneg_left hμ_sq (sq_nonneg _)
        _ =
          C ^ 2 * ‖A b • qs.ket b‖ ^ 2 := by
            simp [norm_smul, ket_norm_one qs]
            ring

    have hsum_bound :
        ∑ b ∈ B, ‖(A b * μ b) • qs.ket b‖ ^ 2
          ≤
        C ^ 2 * ∑ b ∈ B, ‖A b • qs.ket b‖ ^ 2 := by
      calc
        ∑ b ∈ B, ‖(A b * μ b) • qs.ket b‖ ^ 2
            ≤
          ∑ b ∈ B, C ^ 2 * ‖A b • qs.ket b‖ ^ 2 := by
            exact Finset.sum_le_sum fun b hb => hterm b hb
        _ =
          C ^ 2 * ∑ b ∈ B, ‖A b • qs.ket b‖ ^ 2 := by
            rw [Finset.mul_sum]

    calc
      ‖∑ i ∈ s, (a i * L i) • qs.ket (label i)‖ ^ 2
          =
        ‖∑ b ∈ B, (A b * μ b) • qs.ket b‖ ^ 2 := by
          rw [hmult_group]
      _ =
        ∑ b ∈ B, ‖(A b * μ b) • qs.ket b‖ ^ 2 :=
        hmult_sq
      _ ≤
        C ^ 2 * ∑ b ∈ B, ‖A b • qs.ket b‖ ^ 2 :=
        hsum_bound
      _ =
        C ^ 2 * ‖∑ b ∈ B, A b • qs.ket b‖ ^ 2 := by
        rw [hplain_sq]
      _ =
        C ^ 2 * ‖∑ i ∈ s, a i • qs.ket (label i)‖ ^ 2 := by
        rw [hplain_group]

  · have hs_empty : s = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hs
    simp [hs_empty]

private lemma alg1_step2_fourier_multiplier_constant_on_labels
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (r : ℕ)
    (p q : Alg1Step2FourierIndex qs cfg)
    (hlabel :
      alg1Step2FourierLabel qs cfg p
        =
      alg1Step2FourierLabel qs cfg q) :
    alg1Step2FourierMultiplier qs cfg r p
      =
    alg1Step2FourierMultiplier qs cfg r q := by
  have hy : p.2.1 = q.2.1 := by
    calc
      p.2.1
          =
        RegEncoding.toNat
          (extendHi cfg.env.data)
          (alg1Step2FourierLabel qs cfg p) := by
            symm
            exact
              RegEncoding.toNat_writeNat_of_lt
                (extendHi cfg.env.data)
                p.2.1
                (RegEncoding.writeNat cfg.env.work p.1.2.1 p.1.1)
                p.2.isLt
      _ =
        RegEncoding.toNat
          (extendHi cfg.env.data)
          (alg1Step2FourierLabel qs cfg q) := by
            rw [hlabel]
      _ = q.2.1 :=
        RegEncoding.toNat_writeNat_of_lt
          (extendHi cfg.env.data)
          q.2.1
          (RegEncoding.writeNat cfg.env.work q.1.2.1 q.1.1)
          q.2.isLt

  have hpwork : p.1.2.1 = q.1.2.1 := by
    have hXW : Disjoint (extendHi cfg.env.data) cfg.env.work := by
      simpa using cfg.layout.1
    have hWX : Disjoint cfg.env.work (extendHi cfg.env.data) := by
      rcases hXW with h | h
      · exact Or.inr h
      · exact Or.inl h
    calc
      p.1.2.1
          =
        RegEncoding.toNat
          cfg.env.work
          (alg1Step2FourierLabel qs cfg p) := by
            symm
            calc
              RegEncoding.toNat
                  cfg.env.work
                  (alg1Step2FourierLabel qs cfg p)
                  =
                RegEncoding.toNat
                  cfg.env.work
                  (RegEncoding.writeNat cfg.env.work p.1.2.1 p.1.1) := by
                    exact
                      RegEncoding.toNat_left_write_right
                        cfg.env.work
                        (extendHi cfg.env.data)
                        hWX
                        (RegEncoding.writeNat cfg.env.work p.1.2.1 p.1.1)
                        p.2.1
              _ = p.1.2.1 :=
                    RegEncoding.toNat_writeNat_of_lt
                      cfg.env.work
                      p.1.2.1
                      p.1.1
                      p.1.2.isLt
      _ =
        RegEncoding.toNat
          cfg.env.work
          (alg1Step2FourierLabel qs cfg q) := by
            rw [hlabel]
      _ = q.1.2.1 := by
            calc
              RegEncoding.toNat
                  cfg.env.work
                  (alg1Step2FourierLabel qs cfg q)
                  =
                RegEncoding.toNat
                  cfg.env.work
                  (RegEncoding.writeNat cfg.env.work q.1.2.1 q.1.1) := by
                    exact
                      RegEncoding.toNat_left_write_right
                        cfg.env.work
                        (extendHi cfg.env.data)
                        hWX
                        (RegEncoding.writeNat cfg.env.work q.1.2.1 q.1.1)
                        q.2.1
              _ = q.1.2.1 :=
                    RegEncoding.toNat_writeNat_of_lt
                      cfg.env.work
                      q.1.2.1
                      q.1.1
                      q.1.2.isLt

  simp [alg1Step2FourierMultiplier, hy, hpwork]

private lemma alg1_qftPhase_eq_exp_I
    (L x y : ℕ)
    (hL : 0 < L) :
    qftPhase L x y =
      Complex.exp
        (Complex.I *
          (((2 * Real.pi / (L : ℝ)) *
              (x : ℝ) *
              (y : ℝ) : ℝ) : ℂ)) := by
  have hL0 : (L : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hL

  rw [qftPhase, ωPow, ω, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp [hL0]

private lemma alg1_norm_exp_I_sub_exp_I_le
    (a b : ℝ) :
    ‖Complex.exp (Complex.I * (a : ℂ))
        - Complex.exp (Complex.I * (b : ℂ))‖
      ≤
    |a - b| := by
  have hfactor :
      Complex.exp (Complex.I * (a : ℂ))
          - Complex.exp (Complex.I * (b : ℂ))
        =
      Complex.exp (Complex.I * (b : ℂ)) *
        (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
    calc
      Complex.exp (Complex.I * (a : ℂ))
          - Complex.exp (Complex.I * (b : ℂ))
        =
      Complex.exp (Complex.I * (b : ℂ)) *
          Complex.exp (Complex.I * ((a - b : ℝ) : ℂ))
          -
          Complex.exp (Complex.I * (b : ℂ)) := by
            rw [← Complex.exp_add]
            congr 1
            push_cast
            ring_nf
      _ =
      Complex.exp (Complex.I * (b : ℂ)) *
        (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
          ring

  rw [
    hfactor,
    norm_mul,
    Complex.norm_exp_I_mul_ofReal,
    one_mul,
    Complex.norm_exp_I_mul_ofReal_sub_one
  ]

  change |2 * Real.sin ((a - b) / 2)| ≤ |a - b|

  calc
    |2 * Real.sin ((a - b) / 2)|
        =
      2 * |Real.sin ((a - b) / 2)| := by
        rw [abs_mul, abs_of_nonneg]
        norm_num
    _ ≤
      2 * |(a - b) / 2| :=
      mul_le_mul_of_nonneg_left
        Real.abs_sin_le_abs
        (by norm_num)
    _ = |a - b| := by
      rw [abs_div]
      have htwo_abs : |(2 : ℝ)| = 2 := by norm_num
      rw [htwo_abs]
      ring_nf

private lemma alg1_step2_fixed_work_multiplier_bound
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (S : Finset (Alg1Step2SourceIndex qs cfg))
    (t : Fin (ASize cfg.env.work))
    (r : ℕ)
    (hfixed :
      ∀ i ∈ S,
        i.2 = t ∧
        GoodModMulBasisInput
          qs cfg.env.N cfg.env.data cfg.env.work cfg.flag i.1 ∧
        i.2 ∈ alg1GoodLabels cfg i.1 ∧
        alg1TargetResidue cfg i.1 = r)
    (p : Alg1Step2FourierIndex qs cfg)
    (hp : p ∈ alg1Step2FourierIndices qs cfg S) :
    ‖alg1Step2FourierMultiplier qs cfg r p‖
      ≤
    2 * Real.pi * η := by
  classical

  have hp' :
      p ∈ S.sigma
        (fun _ : Alg1Step2SourceIndex qs cfg =>
          (Finset.univ :
            Finset (Fin (ASize (extendHi cfg.env.data))))) := by
    simpa [alg1Step2FourierIndices] using hp

  rcases Finset.mem_sigma.mp hp' with ⟨hpS, _⟩
  rcases hfixed p.1 hpS with ⟨hpt, hp_good, hp_label, hp_residue⟩

  let L : ℕ := ASize (extendHi cfg.env.data)
  let a : ℝ :=
    (cfg.env.N : ℝ) * alg1WorkFraction cfg p.1.2
  let θa : ℝ :=
    (2 * Real.pi / (L : ℝ)) * a * (p.2.1 : ℝ)
  let θr : ℝ :=
    (2 * Real.pi / (L : ℝ)) * (r : ℝ) * (p.2.1 : ℝ)

  have hLposN : 0 < L := by
    dsimp [L, ASize]
    positivity

  have hLpos : (0 : ℝ) < (L : ℝ) := by
    exact_mod_cast hLposN

  have hLne : (L : ℝ) ≠ 0 :=
    ne_of_gt hLpos

  have hη : 0 < η :=
    cfg.env.precision.1

  have hdelta :
      |a - (r : ℝ)| < η := by
    simpa [
      a,
      alg1Step2ShiftDiscrepancy,
      hp_residue
    ] using
      (alg1_step2_good_label_shift_discrepancy_lt
        cfg p.1.1 p.1.2 hp_label)

  have hylt : (p.2.1 : ℝ) < (L : ℝ) := by
    dsimp [L]
    exact_mod_cast p.2.isLt

  have hydiv_nonneg :
      0 ≤ (p.2.1 : ℝ) / (L : ℝ) :=
    div_nonneg (by positivity) hLpos.le

  have hydiv_le_one :
      (p.2.1 : ℝ) / (L : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hLpos).2
    linarith

  have hprod :
      ((p.2.1 : ℝ) / (L : ℝ)) * |a - (r : ℝ)| ≤ η := by
    calc
      ((p.2.1 : ℝ) / (L : ℝ)) * |a - (r : ℝ)|
          ≤
        ((p.2.1 : ℝ) / (L : ℝ)) * η :=
        mul_le_mul_of_nonneg_left hdelta.le hydiv_nonneg
      _ ≤ 1 * η :=
        mul_le_mul_of_nonneg_right hydiv_le_one hη.le
      _ = η := one_mul _

  have htheta :
      θa - θr =
        (2 * Real.pi) *
          (((p.2.1 : ℝ) / (L : ℝ)) * (a - (r : ℝ))) := by
    dsimp [θa, θr]
    field_simp [hLne]

  have htwopi_nonneg : 0 ≤ 2 * Real.pi := by
    positivity

  have htheta_bound :
      |θa - θr| ≤ 2 * Real.pi * η := by
    rw [
      htheta,
      abs_mul,
      abs_of_nonneg htwopi_nonneg,
      abs_mul,
      abs_of_nonneg hydiv_nonneg
    ]
    exact mul_le_mul_of_nonneg_left hprod htwopi_nonneg

  have hactual :
      alg1Step2Phase cfg * Complex.I *
          ((p.1.2.1 : ℂ) * (p.2.1 : ℂ))
        =
      Complex.I * (θa : ℂ) := by
    rw [alg1_step2_phase_normalization cfg p.1.2 p.2]
    dsimp [θa, a, L, alg1WorkFraction]
    push_cast
    ring

  have hideal :
      qftPhase L r p.2.1 =
        Complex.exp (Complex.I * (θr : ℂ)) := by
    simpa [θr] using
      (alg1_qftPhase_eq_exp_I L r p.2.1 hLposN)

  change
    ‖Complex.exp
        (alg1Step2Phase cfg * Complex.I *
          ((p.1.2.1 : ℂ) * (p.2.1 : ℂ)))
      - qftPhase L r p.2.1‖
      ≤ 2 * Real.pi * η

  rw [hactual, hideal]

  calc
    ‖Complex.exp (Complex.I * (θa : ℂ))
        - Complex.exp (Complex.I * (θr : ℂ))‖
      ≤ |θa - θr| :=
        alg1_norm_exp_I_sub_exp_I_le θa θr
    _ ≤ 2 * Real.pi * η :=
      htheta_bound

private lemma alg1_step2_fixed_work_qft_packet
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (S : Finset (Alg1Step2SourceIndex qs cfg))
    (α : Alg1Step2SourceIndex qs cfg → ℂ)
    (hgood :
      ∀ i ∈ S,
        GoodModMulBasisInput
          qs cfg.env.N cfg.env.data cfg.env.work cfg.flag i.1) :
    qs.eval (Gate.QFT (extendHi cfg.env.data))
      (∑ i ∈ S,
        α i •
          qs.ket
            (RegEncoding.writeNat cfg.env.work i.2.1 i.1))
      =
    ∑ p ∈ alg1Step2FourierIndices qs cfg S,
      alg1Step2FourierBaseCoeff qs cfg α p •
        qs.ket (alg1Step2FourierLabel qs cfg p) := by
  classical

  let xext : Reg := extendHi cfg.env.data

  have hqft :
      ∀ i ∈ S,
        qs.eval (Gate.QFT xext)
          (qs.ket
            (RegEncoding.writeNat cfg.env.work i.2.1 i.1))
          =
        ∑ y : Fin (ASize xext),
          (alg1Step2QFTScale cfg *
            qftPhase
              (ASize xext)
              (RegEncoding.toNat cfg.env.data i.1)
              y.1) •
            qs.ket
              (RegEncoding.writeNat
                xext
                y.1
                (RegEncoding.writeNat cfg.env.work i.2.1 i.1)) := by
    intro i hi

    have hxext :
        RegEncoding.toNat xext
          (RegEncoding.writeNat cfg.env.work i.2.1 i.1)
          =
        RegEncoding.toNat cfg.env.data i.1 := by
      simpa [xext] using
        (alg1_step2_input_xext_value
          qs cfg i.1 i.2 (hgood i hi))

    rw [QFTSemantics.eval_QFT_ket]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    rw [smul_smul]
    simp [
      xext,
      alg1Step2QFTScale,
      ASize,
      hxext,
    ]

  calc
    qs.eval (Gate.QFT xext)
        (∑ i ∈ S,
          α i •
            qs.ket
              (RegEncoding.writeNat cfg.env.work i.2.1 i.1))
      =
    ∑ i ∈ S,
      α i •
        qs.eval (Gate.QFT xext)
          (qs.ket
            (RegEncoding.writeNat cfg.env.work i.2.1 i.1)) := by
      rw [eval_finset_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [qs.eval_smul]

    _ =
    ∑ i ∈ S,
      α i •
        ∑ y : Fin (ASize xext),
          (alg1Step2QFTScale cfg *
            qftPhase
              (ASize xext)
              (RegEncoding.toNat cfg.env.data i.1)
              y.1) •
            qs.ket
              (RegEncoding.writeNat
                xext
                y.1
                (RegEncoding.writeNat cfg.env.work i.2.1 i.1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hqft i hi]

    _ =
    ∑ i ∈ S,
      ∑ y : Fin (ASize xext),
        (α i *
          alg1Step2QFTScale cfg *
          qftPhase
            (ASize xext)
            (RegEncoding.toNat cfg.env.data i.1)
            y.1) •
          qs.ket
            (RegEncoding.writeNat
              xext
              y.1
              (RegEncoding.writeNat cfg.env.work i.2.1 i.1)) := by
      simp only [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro y hy
      rw [smul_smul]
      ring_nf

    _ =
    ∑ p ∈ alg1Step2FourierIndices qs cfg S,
      alg1Step2FourierBaseCoeff qs cfg α p •
        qs.ket (alg1Step2FourierLabel qs cfg p) := by
      simp [
        alg1Step2FourierIndices,
        alg1Step2FourierBaseCoeff,
        alg1Step2FourierLabel,
        xext,
        Finset.sum_sigma,
        mul_assoc
      ]

private lemma alg1_step2_branch_error_eq_iqft_packet
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis)
    (t : Fin (ASize cfg.env.work))
    (hb :
      GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b) :
    alg1Step2Error qs cfg b t
      =
    qs.eval (IQFT (extendHi cfg.env.data))
      (∑ y : Fin (ASize (extendHi cfg.env.data)),
        (alg1Step2ActualFourierCoeff cfg b t y
          - alg1Step2IdealFourierCoeff cfg b y) •
          qs.ket
            (RegEncoding.writeNat
              (extendHi cfg.env.data)
              y.1
              (RegEncoding.writeNat cfg.env.work t.1 b))) := by
  let xext : Reg := extendHi cfg.env.data
  let source : qs.Basis :=
    RegEncoding.writeNat cfg.env.work t.1 b
  let target : qs.Basis :=
    RegEncoding.writeNat
      xext
      (alg1Step2Value cfg b)
      source

  let actualPre : qs.State :=
    qs.eval
      (Gate.PhaseProd
        (alg1Step2Phase cfg)
        cfg.env.work
        xext)
      (qs.eval (Gate.QFT xext) (qs.ket source))

  let idealPre : qs.State :=
    qs.eval (Gate.QFT xext) (qs.ket target)

  have hU2 :
      qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg) (qs.ket source)
        =
      qs.eval (IQFT xext) actualPre := by
    simp [
      ModMulConfig.U2,
      step2,
      alg1Step2Phase,
      xext,
      source,
      actualPre,
      qs.eval_seq
    ]

  have htarget :
      qs.eval (IQFT xext) idealPre
        =
      qs.ket target := by
    simpa [IQFT, idealPre] using
      qs.eval_adj_apply (Gate.QFT xext) (qs.ket target)

  have hactual :
      actualPre
        =
      ∑ y : Fin (ASize xext),
        alg1Step2ActualFourierCoeff cfg b t y •
          qs.ket
            (RegEncoding.writeNat
              xext y.1 source) := by
    simpa [actualPre, xext, source] using
      alg1_step2_actual_preIQFT_packet qs cfg b t hb

  have hideal :
      idealPre
        =
      ∑ y : Fin (ASize xext),
        alg1Step2IdealFourierCoeff cfg b y •
          qs.ket
            (RegEncoding.writeNat
              xext y.1 source) := by
    simpa [idealPre, xext, source, target] using
      alg1_step2_ideal_preIQFT_packet qs cfg b t hb

  calc
    alg1Step2Error qs cfg b t
        =
      qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg) (qs.ket source)
        - qs.ket target := by
          rfl
    _ =
      qs.eval (IQFT xext) actualPre
        - qs.eval (IQFT xext) idealPre := by
          rw [hU2, htarget]
    _ =
      qs.eval (IQFT xext) (actualPre - idealPre) :=
        (qs.hsub (IQFT xext) actualPre idealPre).symm
    _ =
      qs.eval (IQFT xext)
        ((∑ y : Fin (ASize xext),
          alg1Step2ActualFourierCoeff cfg b t y •
            qs.ket
              (RegEncoding.writeNat xext y.1 source))
        -
        ∑ y : Fin (ASize xext),
          alg1Step2IdealFourierCoeff cfg b y •
            qs.ket
              (RegEncoding.writeNat xext y.1 source)) := by
          rw [hactual, hideal]
    _ =
      qs.eval (IQFT xext)
        (∑ y : Fin (ASize xext),
          (alg1Step2ActualFourierCoeff cfg b t y
            - alg1Step2IdealFourierCoeff cfg b y) •
            qs.ket
              (RegEncoding.writeNat xext y.1 source)) := by
          congr 1
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro y hy
          rw [← sub_smul]
    _ =
      qs.eval (IQFT (extendHi cfg.env.data))
        (∑ y : Fin (ASize (extendHi cfg.env.data)),
          (alg1Step2ActualFourierCoeff cfg b t y
            - alg1Step2IdealFourierCoeff cfg b y) •
            qs.ket
              (RegEncoding.writeNat
                (extendHi cfg.env.data)
                y.1
                (RegEncoding.writeNat cfg.env.work t.1 b))) := by
          rfl


private lemma alg1_step2_fixed_work_coeff_factor
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (S : Finset (Alg1Step2SourceIndex qs cfg))
    (α : Alg1Step2SourceIndex qs cfg → ℂ)
    (t : Fin (ASize cfg.env.work))
    (r : ℕ)
    (hfixed :
      ∀ i ∈ S,
        i.2 = t ∧
        GoodModMulBasisInput
          qs cfg.env.N cfg.env.data cfg.env.work cfg.flag i.1 ∧
        i.2 ∈ alg1GoodLabels cfg i.1 ∧
        alg1TargetResidue cfg i.1 = r)
    (i : Alg1Step2SourceIndex qs cfg)
    (hi : i ∈ S)
    (y : Fin (ASize (extendHi cfg.env.data))) :
    α i *
        (alg1Step2ActualFourierCoeff cfg i.1 i.2 y
          - alg1Step2IdealFourierCoeff cfg i.1 y)
      =
    alg1Step2FourierBaseCoeff qs cfg α ⟨i, y⟩ *
      alg1Step2FourierMultiplier qs cfg r ⟨i, y⟩ := by
  have hr : alg1TargetResidue cfg i.1 = r :=
    (hfixed i hi).2.2.2

  have hstep2 :
      alg1Step2Value cfg i.1
        =
      RegEncoding.toNat cfg.env.data i.1 + r := by
    simp [alg1Step2Value, hr]

  simp only [
    alg1Step2ActualFourierCoeff,
    alg1Step2IdealFourierCoeff,
    alg1Step2FourierBaseCoeff,
    alg1Step2FourierMultiplier
  ]

  rw [hstep2, alg1_qftPhase_add_left]
  ring

lemma alg1_step2_fixed_work_error_eq_iqft_multiplier_packet
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [Spec]
    [GateSemanticsFacts qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (S : Finset (Alg1Step2SourceIndex qs cfg))
    (α : Alg1Step2SourceIndex qs cfg → ℂ)
    (t : Fin (ASize cfg.env.work))
    (r : ℕ)
    (hfixed :
      ∀ i ∈ S,
        i.2 = t ∧
        GoodModMulBasisInput
          qs cfg.env.N cfg.env.data cfg.env.work cfg.flag i.1 ∧
        i.2 ∈ alg1GoodLabels cfg i.1 ∧
        alg1TargetResidue cfg i.1 = r) :
    ∑ i ∈ S, α i • alg1Step2Error qs cfg i.1 i.2
      =
    qs.eval (IQFT (extendHi cfg.env.data))
      (∑ p ∈ alg1Step2FourierIndices qs cfg S,
        (alg1Step2FourierBaseCoeff qs cfg α p *
          alg1Step2FourierMultiplier qs cfg r p) •
          qs.ket (alg1Step2FourierLabel qs cfg p)) := by
  classical

  let xext : Reg := extendHi cfg.env.data

  let packet : Alg1Step2SourceIndex qs cfg → qs.State :=
    fun i =>
      ∑ y : Fin (ASize xext),
        (alg1Step2ActualFourierCoeff cfg i.1 i.2 y
          - alg1Step2IdealFourierCoeff cfg i.1 y) •
          qs.ket
            (RegEncoding.writeNat
              xext
              y.1
              (RegEncoding.writeNat cfg.env.work i.2.1 i.1))

  have hbranch :
      ∀ i ∈ S,
        alg1Step2Error qs cfg i.1 i.2
          =
        qs.eval (IQFT xext) (packet i) := by
    intro i hi
    have hgood :
        GoodModMulBasisInput
          qs cfg.env.N cfg.env.data cfg.env.work cfg.flag i.1 :=
      (hfixed i hi).2.1

    simpa [packet, xext] using
      alg1_step2_branch_error_eq_iqft_packet
        qs cfg i.1 i.2 hgood

  have hdistribute :
      (∑ i ∈ S, α i • packet i)
        =
      ∑ i ∈ S,
        ∑ y : Fin (ASize xext),
          (α i *
            (alg1Step2ActualFourierCoeff cfg i.1 i.2 y
              - alg1Step2IdealFourierCoeff cfg i.1 y)) •
            qs.ket
              (RegEncoding.writeNat
                xext
                y.1
                (RegEncoding.writeNat cfg.env.work i.2.1 i.1)) := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [packet]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    rw [smul_smul]

  have hcoeff :
      ∀ i ∈ S,
        ∀ y : Fin (ASize xext),
          α i *
              (alg1Step2ActualFourierCoeff cfg i.1 i.2 y
                - alg1Step2IdealFourierCoeff cfg i.1 y)
            =
          alg1Step2FourierBaseCoeff qs cfg α ⟨i, y⟩ *
            alg1Step2FourierMultiplier qs cfg r ⟨i, y⟩ := by
    intro i hi y
    simpa [xext] using
      alg1_step2_fixed_work_coeff_factor
        qs cfg S α t r hfixed i hi y

  have hflatten :
      (∑ i ∈ S,
        ∑ y : Fin (ASize xext),
          (α i *
            (alg1Step2ActualFourierCoeff cfg i.1 i.2 y
              - alg1Step2IdealFourierCoeff cfg i.1 y)) •
            qs.ket
              (RegEncoding.writeNat
                xext
                y.1
                (RegEncoding.writeNat cfg.env.work i.2.1 i.1)))
        =
      ∑ p ∈ alg1Step2FourierIndices qs cfg S,
        (alg1Step2FourierBaseCoeff qs cfg α p *
          alg1Step2FourierMultiplier qs cfg r p) •
          qs.ket (alg1Step2FourierLabel qs cfg p) := by
    simp only [alg1Step2FourierIndices, Finset.sum_sigma]

    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro y hy

    rw [hcoeff i hi y]
    rfl

  calc
    ∑ i ∈ S, α i • alg1Step2Error qs cfg i.1 i.2
        =
      ∑ i ∈ S,
        qs.eval (IQFT xext) (α i • packet i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hbranch i hi, qs.eval_smul]
    _ =
      qs.eval (IQFT xext) (∑ i ∈ S, α i • packet i) := by
          symm
          exact
            eval_finset_sum
              qs
              (IQFT xext)
              S
              (fun i => α i • packet i)
    _ =
      qs.eval (IQFT xext)
        (∑ i ∈ S,
          ∑ y : Fin (ASize xext),
            (α i *
              (alg1Step2ActualFourierCoeff cfg i.1 i.2 y
                - alg1Step2IdealFourierCoeff cfg i.1 y)) •
              qs.ket
                (RegEncoding.writeNat
                  xext
                  y.1
                  (RegEncoding.writeNat cfg.env.work i.2.1 i.1))) := by
          rw [hdistribute]
    _ =
      qs.eval (IQFT xext)
        (∑ p ∈ alg1Step2FourierIndices qs cfg S,
          (alg1Step2FourierBaseCoeff qs cfg α p *
            alg1Step2FourierMultiplier qs cfg r p) •
            qs.ket (alg1Step2FourierLabel qs cfg p)) := by
          rw [hflatten]
    _ =
      qs.eval (IQFT (extendHi cfg.env.data))
        (∑ p ∈ alg1Step2FourierIndices qs cfg S,
          (alg1Step2FourierBaseCoeff qs cfg α p *
            alg1Step2FourierMultiplier qs cfg r p) •
            qs.ket (alg1Step2FourierLabel qs cfg p)) := by
          rfl



lemma alg1_step2_fixed_work_fourier_contraction
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [Spec]
    [GateSemanticsFacts qs] :
    ∀ (η : ℝ) (cfg : ModMulConfig η)
      (S : Finset (Σ _b : qs.Basis, Fin (ASize cfg.env.work)))
      (α : (Σ _b : qs.Basis, Fin (ASize cfg.env.work)) → ℂ)
      (t : Fin (ASize cfg.env.work))
      (r : ℕ),
      (∀ i ∈ S,
        i.2 = t ∧
        GoodModMulBasisInput
          qs cfg.env.N cfg.env.data cfg.env.work cfg.flag i.1 ∧
        i.2 ∈ alg1GoodLabels cfg i.1 ∧
        alg1TargetResidue cfg i.1 = r) →
      ‖∑ i ∈ S, α i • alg1Step2Error qs cfg i.1 i.2‖ ^ 2
        ≤
      (2 * Real.pi * η) ^ 2 *
        ‖∑ i ∈ S,
          α i •
            qs.ket
              (RegEncoding.writeNat cfg.env.work i.2.1 i.1)‖ ^ 2 := by
  intro η cfg S α t r hfixed
  classical

  have hgood :
      ∀ i ∈ S,
        GoodModMulBasisInput
          qs cfg.env.N cfg.env.data cfg.env.work cfg.flag i.1 := by
    intro i hi
    exact (hfixed i hi).2.1

  have hC :
      0 ≤ 2 * Real.pi * η := by
    have hη : 0 ≤ η :=
      le_of_lt cfg.env.precision.1
    positivity

  have herror :=
    alg1_step2_fixed_work_error_eq_iqft_multiplier_packet
      qs cfg S α t r hfixed

  have hmult :
      ∀ p ∈ alg1Step2FourierIndices qs cfg S,
        ‖alg1Step2FourierMultiplier qs cfg r p‖
          ≤
        2 * Real.pi * η := by
    intro p hp
    exact
      alg1_step2_fixed_work_multiplier_bound
        qs cfg S t r hfixed p hp

  have hconst :
      ∀ p ∈ alg1Step2FourierIndices qs cfg S,
        ∀ q ∈ alg1Step2FourierIndices qs cfg S,
          alg1Step2FourierLabel qs cfg p
            =
          alg1Step2FourierLabel qs cfg q →
          alg1Step2FourierMultiplier qs cfg r p
            =
          alg1Step2FourierMultiplier qs cfg r q := by
    intro p hp q hq hpq
    apply alg1_step2_fourier_multiplier_constant_on_labels qs cfg r p q hpq

  have hdiag :
      ‖∑ p ∈ alg1Step2FourierIndices qs cfg S,
          (alg1Step2FourierBaseCoeff qs cfg α p *
            alg1Step2FourierMultiplier qs cfg r p) •
            qs.ket (alg1Step2FourierLabel qs cfg p)‖ ^ 2
        ≤
      (2 * Real.pi * η) ^ 2 *
        ‖∑ p ∈ alg1Step2FourierIndices qs cfg S,
          alg1Step2FourierBaseCoeff qs cfg α p •
            qs.ket (alg1Step2FourierLabel qs cfg p)‖ ^ 2 :=
    norm_sq_sum_ket_mul_le_of_label_constant
      qs
      (alg1Step2FourierIndices qs cfg S)
      (alg1Step2FourierBaseCoeff qs cfg α)
      (alg1Step2FourierMultiplier qs cfg r)
      (alg1Step2FourierLabel qs cfg)
      (2 * Real.pi * η)
      hC
      hmult
      hconst

  have hqft :=
    alg1_step2_fixed_work_qft_packet
      qs cfg S α hgood

  calc
    ‖∑ i ∈ S, α i • alg1Step2Error qs cfg i.1 i.2‖ ^ 2
        =
      ‖qs.eval (IQFT (extendHi cfg.env.data))
        (∑ p ∈ alg1Step2FourierIndices qs cfg S,
          (alg1Step2FourierBaseCoeff qs cfg α p *
            alg1Step2FourierMultiplier qs cfg r p) •
            qs.ket (alg1Step2FourierLabel qs cfg p))‖ ^ 2 := by
          rw [herror]
    _ =
      ‖∑ p ∈ alg1Step2FourierIndices qs cfg S,
          (alg1Step2FourierBaseCoeff qs cfg α p *
            alg1Step2FourierMultiplier qs cfg r p) •
            qs.ket (alg1Step2FourierLabel qs cfg p)‖ ^ 2 := by
          rw [eval_norm_preserved]
    _ ≤
      (2 * Real.pi * η) ^ 2 *
        ‖∑ p ∈ alg1Step2FourierIndices qs cfg S,
          alg1Step2FourierBaseCoeff qs cfg α p •
            qs.ket (alg1Step2FourierLabel qs cfg p)‖ ^ 2 :=
      hdiag
    _ =
      (2 * Real.pi * η) ^ 2 *
        ‖qs.eval (Gate.QFT (extendHi cfg.env.data))
          (∑ i ∈ S,
            α i •
              qs.ket
                (RegEncoding.writeNat cfg.env.work i.2.1 i.1))‖ ^ 2 := by
          rw [hqft]
    _ =
      (2 * Real.pi * η) ^ 2 *
        ‖∑ i ∈ S,
          α i •
            qs.ket
              (RegEncoding.writeNat cfg.env.work i.2.1 i.1)‖ ^ 2 := by
          rw [eval_norm_preserved]

lemma alg1_step2_fixed_work_packet_sq_bound
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [Spec]
    [GateSemanticsFacts qs] :
    ∀ (η : ℝ) (cfg : ModMulConfig η)
      (S : Finset (Σ _b : qs.Basis, Fin (ASize cfg.env.work)))
      (α : (Σ _b : qs.Basis, Fin (ASize cfg.env.work)) → ℂ)
      (t : Fin (ASize cfg.env.work))
      (r : ℕ),
      (∀ i ∈ S,
        i.2 = t ∧
        GoodModMulBasisInput
          qs cfg.env.N cfg.env.data cfg.env.work cfg.flag i.1 ∧
        i.2 ∈ alg1GoodLabels cfg i.1 ∧
        alg1TargetResidue cfg i.1 = r) →
      ‖∑ i ∈ S, α i • alg1Step2Error qs cfg i.1 i.2‖ ^ 2
        ≤
      (2 * Real.pi ^ 2 * η) *
        ∑ i ∈ S, ‖α i‖ ^ 2 := by
  intro η cfg S α t r hfixed

  have hgood :
      ∀ i ∈ S,
        GoodModMulBasisInput
          qs cfg.env.N cfg.env.data cfg.env.work cfg.flag i.1 := by
    intro i hi
    exact (hfixed i hi).2.1

  have hcontract :
      ‖∑ i ∈ S, α i • alg1Step2Error qs cfg i.1 i.2‖ ^ 2
        ≤
      (2 * Real.pi * η) ^ 2 *
        ‖∑ i ∈ S,
          α i •
            qs.ket
              (RegEncoding.writeNat cfg.env.work i.2.1 i.1)‖ ^ 2 :=
    alg1_step2_fixed_work_fourier_contraction
      qs η cfg S α t r hfixed

  have hsource :
      ‖∑ i ∈ S,
          α i •
            qs.ket
              (RegEncoding.writeNat cfg.env.work i.2.1 i.1)‖ ^ 2
        =
      ∑ i ∈ S, ‖α i‖ ^ 2 :=
    alg1_step2_fixed_work_source_energy
      qs cfg S α hgood

  have hη_nonneg : 0 ≤ η :=
    le_of_lt cfg.env.precision.1

  have hη_half : 2 * η ≤ 1 := by
    have hlt : η < (1 / 2 : ℝ) :=
      cfg.env.precision.2.1
    linarith

  have hscale_nonneg : 0 ≤ 2 * Real.pi ^ 2 * η := by
    positivity

  have hscale :
      (2 * Real.pi * η) ^ 2
        ≤
      2 * Real.pi ^ 2 * η := by
    calc
      (2 * Real.pi * η) ^ 2
          =
        (2 * Real.pi ^ 2 * η) * (2 * η) := by
          ring
      _ ≤
        (2 * Real.pi ^ 2 * η) * 1 :=
          mul_le_mul_of_nonneg_left hη_half hscale_nonneg
      _ = 2 * Real.pi ^ 2 * η := by ring

  have henergy_nonneg :
      0 ≤ ∑ i ∈ S, ‖α i‖ ^ 2 := by
    exact Finset.sum_nonneg fun i hi => sq_nonneg _

  calc
    ‖∑ i ∈ S, α i • alg1Step2Error qs cfg i.1 i.2‖ ^ 2
        ≤
      (2 * Real.pi * η) ^ 2 *
        ‖∑ i ∈ S,
          α i •
            qs.ket
              (RegEncoding.writeNat cfg.env.work i.2.1 i.1)‖ ^ 2 :=
      hcontract
    _ =
      (2 * Real.pi * η) ^ 2 *
        ∑ i ∈ S, ‖α i‖ ^ 2 := by
      rw [hsource]
    _ ≤
      (2 * Real.pi ^ 2 * η) *
        ∑ i ∈ S, ‖α i‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hscale henergy_nonneg

lemma alg1_step2_work_fiber_sq_bound
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [Spec]
    [GateSemanticsFacts qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (S : Finset (Σ _b : qs.Basis, Fin (ASize cfg.env.work)))
    (α : (Σ _b : qs.Basis, Fin (ASize cfg.env.work)) → ℂ)
    (hgood :
      ∀ i ∈ S,
        GoodModMulBasisInput
          qs cfg.env.N cfg.env.data cfg.env.work cfg.flag i.1 ∧
        i.2 ∈ alg1GoodLabels cfg i.1)
    (t : Fin (ASize cfg.env.work)) :
    ‖∑ i ∈ S.filter (fun i => i.2 = t),
        α i • alg1Step2Error qs cfg i.1 i.2‖ ^ 2
      ≤
    (2 * Real.pi ^ 2 * η) *
      ∑ i ∈ S.filter (fun i => i.2 = t), ‖α i‖ ^ 2 := by
  classical
  by_cases hfiber : (S.filter fun i => i.2 = t).Nonempty
  · rcases hfiber with ⟨i₀, hi₀⟩
    let r : ℕ := alg1TargetResidue cfg i₀.1

    apply alg1_step2_fixed_work_packet_sq_bound qs η cfg
      (S.filter fun i => i.2 = t) α t r

    intro i hi
    have hiS : i ∈ S :=
      (Finset.mem_filter.mp hi).1
    have hit : i.2 = t :=
      (Finset.mem_filter.mp hi).2
    have hiGood := hgood i hiS

    have hi₀S : i₀ ∈ S :=
      (Finset.mem_filter.mp hi₀).1
    have hi₀t : i₀.2 = t :=
      (Finset.mem_filter.mp hi₀).2
    have hi₀Good := hgood i₀ hi₀S

    refine ⟨hit, hiGood.1, hiGood.2, ?_⟩
    dsimp [r]
    have hit_good : t ∈ alg1GoodLabels cfg i.1 := by
      simpa [hit] using hiGood.2
    have hi₀t_good : t ∈ alg1GoodLabels cfg i₀.1 := by
      simpa [hi₀t] using hi₀Good.2
    exact alg1_good_labels_same_work_residue
      cfg i.1 i₀.1 t hit_good hi₀t_good

  · have hempty : S.filter (fun i => i.2 = t) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hfiber
    simp [hempty]

/--
Split a coherent Step-2 error packet into its work-label fibers.
-/
lemma alg1_step2_error_eq_sum_work_fibers
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (S : Finset (Σ _b : qs.Basis, Fin (ASize cfg.env.work)))
    (α : (Σ _b : qs.Basis, Fin (ASize cfg.env.work)) → ℂ) :
    ∑ i ∈ S, α i • alg1Step2Error qs cfg i.1 i.2
      =
    ∑ t : Fin (ASize cfg.env.work),
      ∑ i ∈ S.filter (fun i => i.2 = t),
        α i • alg1Step2Error qs cfg i.1 i.2 := by
  classical
  symm
  calc
    ∑ t : Fin (ASize cfg.env.work),
      ∑ i ∈ S.filter (fun i => i.2 = t),
        α i • alg1Step2Error qs cfg i.1 i.2
        =
      ∑ t : Fin (ASize cfg.env.work),
        ∑ i ∈ S,
          if i.2 = t then
            α i • alg1Step2Error qs cfg i.1 i.2
          else
            0 := by
        simp_rw [Finset.sum_filter]
    _ =
      ∑ i ∈ S,
        ∑ t : Fin (ASize cfg.env.work),
          if i.2 = t then
            α i • alg1Step2Error qs cfg i.1 i.2
          else
            0 := by
        rw [Finset.sum_comm]
    _ =
      ∑ i ∈ S, α i • alg1Step2Error qs cfg i.1 i.2 := by
        apply Finset.sum_congr rfl
        intro i hi
        simp

/--
Distinct work-label fibers are orthogonal.
-/
lemma alg1_step2_work_fiber_orthogonal
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (S : Finset (Σ _b : qs.Basis, Fin (ASize cfg.env.work)))
    (α : (Σ _b : qs.Basis, Fin (ASize cfg.env.work)) → ℂ) :
    ∀ t ∈ (Finset.univ : Finset (Fin (ASize cfg.env.work))),
      ∀ u ∈ (Finset.univ : Finset (Fin (ASize cfg.env.work))),
        t ≠ u →
        inner ℂ
          (∑ i ∈ S.filter (fun i => i.2 = t),
            α i • alg1Step2Error qs cfg i.1 i.2)
          (∑ j ∈ S.filter (fun j => j.2 = u),
            α j • alg1Step2Error qs cfg j.1 j.2)
          =
        0 := by
  intro t _ u _ htu
  rw [inner_sum]
  refine Finset.sum_eq_zero ?_
  intro j hj
  rw [sum_inner]
  refine Finset.sum_eq_zero ?_
  intro i hi
  rw [inner_smul_left, inner_smul_right]
  have hit : i.2 = t :=
    (Finset.mem_filter.mp hi).2
  have hju : j.2 = u :=
    (Finset.mem_filter.mp hj).2
  rw [hit, hju]
  simp [alg1_step2_error_work_orthogonal qs cfg i.1 j.1 t u htu]

/--
The coefficient energy is the sum of its disjoint work-label fiber energies.
-/
lemma alg1_step2_energy_eq_sum_work_fibers
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (S : Finset (Σ _b : qs.Basis, Fin (ASize cfg.env.work)))
    (α : (Σ _b : qs.Basis, Fin (ASize cfg.env.work)) → ℂ) :
    ∑ t : Fin (ASize cfg.env.work),
      ∑ i ∈ S.filter (fun i => i.2 = t), ‖α i‖ ^ 2
      =
    ∑ i ∈ S, ‖α i‖ ^ 2 := by
  classical
  calc
    ∑ t : Fin (ASize cfg.env.work),
      ∑ i ∈ S.filter (fun i => i.2 = t), ‖α i‖ ^ 2
        =
      ∑ t : Fin (ASize cfg.env.work),
        ∑ i ∈ S,
          if i.2 = t then ‖α i‖ ^ 2 else 0 := by
        simp_rw [Finset.sum_filter]
    _ =
      ∑ i ∈ S,
        ∑ t : Fin (ASize cfg.env.work),
          if i.2 = t then ‖α i‖ ^ 2 else 0 := by
        rw [Finset.sum_comm]
    _ =
      ∑ i ∈ S, ‖α i‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        simp


lemma alg1_step2_good_packet_operator_sq_bound
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [Spec]
    [GateSemanticsFacts qs] :
    ∃ Ccoh : ℝ, 0 ≤ Ccoh ∧
      ∀ (η : ℝ) (cfg : ModMulConfig η)
        (S : Finset (Σ _b : qs.Basis, Fin (ASize cfg.env.work)))
        (α : (Σ _b : qs.Basis, Fin (ASize cfg.env.work)) → ℂ),
        (∀ i ∈ S,
          GoodModMulBasisInput
            qs cfg.env.N cfg.env.data cfg.env.work cfg.flag i.1
            ∧ i.2 ∈ alg1GoodLabels cfg i.1) →
        ‖∑ i ∈ S,
          α i •
            (qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
              (qs.ket
                (RegEncoding.writeNat cfg.env.work i.2.1 i.1))
              -
              qs.ket
                (RegEncoding.writeNat
                  (extendHi cfg.env.data)
                  (alg1Step2Value cfg i.1)
                  (RegEncoding.writeNat cfg.env.work i.2.1 i.1)))‖ ^ 2
          ≤
        (Ccoh * η) *
          ∑ i ∈ S, ‖α i‖ ^ 2 := by
  classical
  refine ⟨2 * Real.pi ^ 2, ?_, ?_⟩
  · positivity

  intro η cfg S α hgood

  let E : Fin (ASize cfg.env.work) → qs.State :=
    fun t =>
      ∑ i ∈ S.filter (fun i => i.2 = t),
        α i • alg1Step2Error qs cfg i.1 i.2

  have hsplit :
      ∑ i ∈ S,
        α i •
          (qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
            (qs.ket (RegEncoding.writeNat cfg.env.work i.2.1 i.1))
            -
            qs.ket
              (RegEncoding.writeNat
                (extendHi cfg.env.data)
                (alg1Step2Value cfg i.1)
                (RegEncoding.writeNat cfg.env.work i.2.1 i.1)))
      =
      ∑ t : Fin (ASize cfg.env.work), E t := by
    simpa [E, alg1Step2Error] using
      alg1_step2_error_eq_sum_work_fibers qs cfg S α

  have horth :
      ∀ t ∈ (Finset.univ : Finset (Fin (ASize cfg.env.work))),
        ∀ u ∈ (Finset.univ : Finset (Fin (ASize cfg.env.work))),
          t ≠ u →
          inner ℂ (E t) (E u) = 0 := by
    simpa [E] using
      alg1_step2_work_fiber_orthogonal qs cfg S α

  have hparseval :
      ‖∑ t : Fin (ASize cfg.env.work), E t‖ ^ 2
        =
      ∑ t : Fin (ASize cfg.env.work), ‖E t‖ ^ 2 :=
    alg1_step2_norm_sq_sum_eq_sum_norm_sq_of_orthogonal
      (qs := qs)
      (Finset.univ : Finset (Fin (ASize cfg.env.work)))
      E
      horth

  have hfiber :
      ∀ t : Fin (ASize cfg.env.work),
        ‖E t‖ ^ 2
          ≤
        (2 * Real.pi ^ 2 * η) *
          ∑ i ∈ S.filter (fun i => i.2 = t), ‖α i‖ ^ 2 := by
    intro t
    simpa [E] using
      alg1_step2_work_fiber_sq_bound qs cfg S α hgood t

  have hη : 0 ≤ η :=
    le_of_lt cfg.env.precision.1

  have hCη : 0 ≤ 2 * Real.pi ^ 2 * η := by
    positivity

  have hsum :
      ∑ t : Fin (ASize cfg.env.work), ‖E t‖ ^ 2
        ≤
      ∑ t : Fin (ASize cfg.env.work),
        (2 * Real.pi ^ 2 * η) *
          ∑ i ∈ S.filter (fun i => i.2 = t), ‖α i‖ ^ 2 := by
    exact Finset.sum_le_sum fun t _ => hfiber t

  have hfactor :
      (∑ t : Fin (ASize cfg.env.work),
        (2 * Real.pi ^ 2 * η) *
          ∑ i ∈ S.filter (fun i => i.2 = t), ‖α i‖ ^ 2)
      =
      (2 * Real.pi ^ 2 * η) *
        ∑ i ∈ S, ‖α i‖ ^ 2 := by
    rw [← Finset.mul_sum]
    rw [alg1_step2_energy_eq_sum_work_fibers qs cfg S α]

  calc
    ‖∑ i ∈ S,
      α i •
        (qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
          (qs.ket (RegEncoding.writeNat cfg.env.work i.2.1 i.1))
          -
          qs.ket
            (RegEncoding.writeNat
              (extendHi cfg.env.data)
              (alg1Step2Value cfg i.1)
              (RegEncoding.writeNat cfg.env.work i.2.1 i.1)))‖ ^ 2
        =
      ‖∑ t : Fin (ASize cfg.env.work), E t‖ ^ 2 := by
        rw [hsplit]
    _ =
      ∑ t : Fin (ASize cfg.env.work), ‖E t‖ ^ 2 := hparseval
    _ ≤
      ∑ t : Fin (ASize cfg.env.work),
        (2 * Real.pi ^ 2 * η) *
          ∑ i ∈ S.filter (fun i => i.2 = t), ‖α i‖ ^ 2 := hsum
    _ =
      (2 * Real.pi ^ 2 * η) *
        ∑ i ∈ S, ‖α i‖ ^ 2 := hfactor





/--
Uniform Step-2 approximation theorem.
-/
lemma alg1_step2_good_label_branch_uniform
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [Spec]
    [GateSemanticsFacts qs] :
    ∃ Cstep2 : ℝ, 0 ≤ Cstep2 ∧
      (∀ (η : ℝ) (cfg : ModMulConfig η)
          (b : qs.Basis)
          (t : Fin (ASize cfg.env.work)),
          GoodModMulBasisInput
            qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b →
          t ∈ alg1GoodLabels cfg b →
          ‖qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
              (qs.ket
                (RegEncoding.writeNat cfg.env.work t.1 b))
            -
            qs.ket
              (RegEncoding.writeNat
                (extendHi cfg.env.data)
                (alg1Step2Value cfg b)
                (RegEncoding.writeNat cfg.env.work t.1 b))‖
          ≤ Cstep2 * η) ∧
      (∀ (η : ℝ) (cfg : ModMulConfig η)
          (ψ : qs.State)
          (tr : Alg1Trace qs cfg ψ),
          cfg.ValidUnitState qs ψ →
          ‖qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
              tr.goodStep1
            - tr.afterStep2Ref‖ ^ 2
          ≤ Cstep2 * η) := by
  classical

  rcases alg1_step2_single_label_fourier_stability qs with
    ⟨Cbranch, hCbranch, hbranch⟩

  rcases alg1_step2_good_packet_operator_sq_bound qs with
    ⟨Ccoh, hCcoh, hcoh⟩

  let Cstep2 : ℝ := Cbranch + Ccoh

  have hCstep2 : 0 ≤ Cstep2 := by
    dsimp [Cstep2]
    linarith

  refine ⟨Cstep2, hCstep2, ?_, ?_⟩

  · intro η cfg b t hb ht
    have hη : 0 ≤ η :=
      le_of_lt cfg.env.precision.1

    have hbase :
        ‖qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
            (qs.ket
              (RegEncoding.writeNat cfg.env.work t.1 b))
            -
            qs.ket
              (RegEncoding.writeNat
                (extendHi cfg.env.data)
                (alg1Step2Value cfg b)
                (RegEncoding.writeNat cfg.env.work t.1 b))‖
          ≤ Cbranch * η :=
      hbranch η cfg b t hb ht

    calc
      ‖qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
          (qs.ket
            (RegEncoding.writeNat cfg.env.work t.1 b))
          -
          qs.ket
            (RegEncoding.writeNat
              (extendHi cfg.env.data)
              (alg1Step2Value cfg b)
              (RegEncoding.writeNat cfg.env.work t.1 b))‖
        ≤ Cbranch * η := hbase
      _ ≤ (Cbranch + Ccoh) * η := by
        nlinarith [mul_nonneg hCcoh hη]
      _ = Cstep2 * η := by rfl

  · intro η cfg ψ tr hunit

    let Sgood : Finset (Σ _b : qs.Basis, Fin (ASize cfg.env.work)) :=
      tr.support.sigma fun b => alg1GoodLabels cfg b

    let α : (Σ _b : qs.Basis, Fin (ASize cfg.env.work)) → ℂ :=
      fun i => tr.inputCoeff i.1 * tr.phaseCoeff i.1 i.2

    have hη : 0 ≤ η :=
      le_of_lt cfg.env.precision.1

    have hSgood :
        ∀ i ∈ Sgood,
          GoodModMulBasisInput
            qs cfg.env.N cfg.env.data cfg.env.work cfg.flag i.1
            ∧ i.2 ∈ alg1GoodLabels cfg i.1 := by
      intro i hi
      rcases Finset.mem_sigma.mp hi with ⟨hbmem, ht⟩
      exact ⟨tr.input_good i.1 hbmem, ht⟩

    have henergy :
        ∑ i ∈ Sgood, ‖α i‖ ^ 2 ≤ 1 := by
      simpa [Sgood, α] using
        (alg1_step2_good_coeff_energy_le_one qs cfg ψ tr hunit)

    have hflat :
        qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
            tr.goodStep1
          - tr.afterStep2Ref
          =
        ∑ i ∈ Sgood,
          α i •
            (qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
              (qs.ket
                (RegEncoding.writeNat cfg.env.work i.2.1 i.1))
              -
              qs.ket
                (RegEncoding.writeNat
                  (extendHi cfg.env.data)
                  (alg1Step2Value cfg i.1)
                  (RegEncoding.writeNat cfg.env.work i.2.1 i.1))) := by
      simpa [Sgood, α] using
        (alg1_step2_trace_error_eq_good_branch_sum qs cfg ψ tr)

    have hoperator :
        ‖∑ i ∈ Sgood,
          α i •
            (qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
              (qs.ket
                (RegEncoding.writeNat cfg.env.work i.2.1 i.1))
              -
              qs.ket
                (RegEncoding.writeNat
                  (extendHi cfg.env.data)
                  (alg1Step2Value cfg i.1)
                  (RegEncoding.writeNat cfg.env.work i.2.1 i.1)))‖ ^ 2
          ≤
        (Ccoh * η) * ∑ i ∈ Sgood, ‖α i‖ ^ 2 :=
      hcoh η cfg Sgood α hSgood

    have hCcohη : 0 ≤ Ccoh * η :=
      mul_nonneg hCcoh hη

    calc
      ‖qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
          tr.goodStep1
        - tr.afterStep2Ref‖ ^ 2
        =
      ‖∑ i ∈ Sgood,
        α i •
          (qs.eval (ModMulConfig.U2 (Basis := qs.Basis) cfg)
            (qs.ket
              (RegEncoding.writeNat cfg.env.work i.2.1 i.1))
            -
            qs.ket
              (RegEncoding.writeNat
                (extendHi cfg.env.data)
                (alg1Step2Value cfg i.1)
                (RegEncoding.writeNat cfg.env.work i.2.1 i.1)))‖ ^ 2 := by
          rw [hflat]
      _ ≤ (Ccoh * η) * ∑ i ∈ Sgood, ‖α i‖ ^ 2 :=
        hoperator
      _ ≤ (Ccoh * η) * 1 := by
        gcongr
      _ ≤ (Cbranch + Ccoh) * η := by
        nlinarith [mul_nonneg hCbranch hη]
      _ = Cstep2 * η := by rfl
