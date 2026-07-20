import FastMultiplication.ShorVerification.AlgorithmCorrectness.ModMulBounds.Algorithm1Expansion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Step-1 Quantum Phase Estimation Bounds

This file contains the setup and analytic estimates needed to view the
fractional work-register load in Step 1 as a QPE kernel, then bound its tail
uniformly over valid basis inputs.
-/

open Shor

universe u v

/-! ## Shared Linear-Algebra And Register Helpers -/

lemma sum_filter_add_sum_filter_not
    {α β : Type*}
    [AddCommMonoid β]
    (s : Finset α)
    (p : α → Prop)
    [DecidablePred p]
    (f : α → β) :
    (∑ x ∈ s.filter p, f x)
      +
    ∑ x ∈ s.filter (fun x => ¬ p x), f x
      =
    ∑ x ∈ s, f x := by
  classical
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hp : p x <;> simp [hp]

lemma norm_sq_sum_eq_sum_norm_sq_of_orthogonal_qpe
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
          inner ℂ (f a) (∑ b ∈ s, f b) = 0 := by
        rw [inner_sum]
        refine Finset.sum_eq_zero ?_
        intro b hb
        apply horth a (by simp) b (Finset.mem_insert_of_mem hb)
        intro hab
        subst b
        exact ha hb

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



lemma writeNat_overwrite_same_reg
    {Basis : Type u} [RegEncoding Basis]
    (r : Reg) (v w : ℕ) (b : Basis) :
    RegEncoding.writeNat r v (RegEncoding.writeNat r w b)
      =
    RegEncoding.writeNat r v b := by
  apply RegEncoding.basis_ext
  intro q
  by_cases hqin : r.lo ≤ q ∧ q < r.hi
  · exact
      RegEncoding.bit_writeNat_in
        (r := r)
        (v := v)
        (b1 := RegEncoding.writeNat r w b)
        (b2 := b)
        (q := q)
        hqin.1
        hqin.2
  ·
    have hqout : q < r.lo ∨ r.hi ≤ q := by
      rcases not_and_or.mp hqin with h | h
      · exact Or.inl (lt_of_not_ge h)
      · exact Or.inr (le_of_not_gt h)
    rw [
      RegEncoding.bit_writeNat_out
        (r := r) (v := v) (b := RegEncoding.writeNat r w b)
        (q := q) hqout,
      RegEncoding.bit_writeNat_out
        (r := r) (v := v) (b := b)
        (q := q) hqout,
      RegEncoding.bit_writeNat_out
        (r := r) (v := w) (b := b)
        (q := q) hqout
    ]

lemma norm_sum_reindex_ket_eq
    (qs : QSemantics)
    {ι : Type v}
    (s : Finset ι)
    (α : ι → ℂ)
    (f g : ι → qs.Basis)
    (hf :
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i ≠ f j)
    (hg :
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j → g i ≠ g j) :
    ‖∑ i ∈ s, α i • qs.ket (f i)‖
      =
    ‖∑ i ∈ s, α i • qs.ket (g i)‖ := by
  classical
  have horth_f :
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        inner ℂ (α i • qs.ket (f i)) (α j • qs.ket (f j)) = 0 := by
    intro i hi j hj hij
    rw [inner_smul_left, inner_smul_right,
      qs.ket_inner_eq_zero_of_ne (hf i hi j hj hij)]
    simp
  have horth_g :
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        inner ℂ (α i • qs.ket (g i)) (α j • qs.ket (g j)) = 0 := by
    intro i hi j hj hij
    rw [inner_smul_left, inner_smul_right,
      qs.ket_inner_eq_zero_of_ne (hg i hi j hj hij)]
    simp
  have hsq_f :=
    norm_sq_sum_eq_sum_norm_sq_of_orthogonal_qpe
      (qs := qs) s (fun i => α i • qs.ket (f i)) horth_f
  have hsq_g :=
    norm_sq_sum_eq_sum_norm_sq_of_orthogonal_qpe
      (qs := qs) s (fun i => α i • qs.ket (g i)) horth_g
  have hterms :
      (∑ i ∈ s, ‖α i • qs.ket (f i)‖ ^ 2)
        =
      ∑ i ∈ s, ‖α i • qs.ket (g i)‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [norm_smul, ket_norm_one qs]
  have hsquares :
      ‖∑ i ∈ s, α i • qs.ket (f i)‖ ^ 2
        =
      ‖∑ i ∈ s, α i • qs.ket (g i)‖ ^ 2 := by
    rw [hsq_f, hsq_g, hterms]
  have hn1 : 0 ≤ ‖∑ i ∈ s, α i • qs.ket (f i)‖ := norm_nonneg _
  have hn2 : 0 ≤ ‖∑ i ∈ s, α i • qs.ket (g i)‖ := norm_nonneg _
  nlinarith

lemma alg1_reset_extendHi_work_write
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (z : qs.Basis)
    (w y : ℕ)
    (hz :
      GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag z) :
    RegEncoding.writeNat
      (extendHi cfg.env.data)
      (RegEncoding.toNat cfg.env.data z)
      (RegEncoding.writeNat
        cfg.env.work
        0
        (RegEncoding.writeNat
          (extendHi cfg.env.data)
          y
          (RegEncoding.writeNat cfg.env.work w z)))
      =
    z := by
  let m : SplitPoint (extendHi cfg.env.data) :=
    ⟨regSize cfg.env.data, by
      simp [extendHi, regSize]⟩

  have hxlt :
      RegEncoding.toNat cfg.env.data z
        <
      ASize (splitLeft (extendHi cfg.env.data) m) := by
    simpa [m, splitLeft, extendHi, regSize] using
      RegEncoding.toNat_lt_ASize cfg.env.data z

  have h0lt :
      0 < ASize (splitRight (extendHi cfg.env.data) m) := by
    simp [m, splitRight, extendHi, regSize, ASize]

  have hsplit :=
    RegEncoding.writeNat_split
      (extendHi cfg.env.data)
      m
      0
      (RegEncoding.toNat cfg.env.data z)
      z
      hxlt
      h0lt

  have hrestore_ext :
      RegEncoding.writeNat
        (extendHi cfg.env.data)
        (RegEncoding.toNat cfg.env.data z)
        z
        =
      z := by
    calc
      RegEncoding.writeNat
          (extendHi cfg.env.data)
          (RegEncoding.toNat cfg.env.data z)
          z
          =
        RegEncoding.writeNat
          (qubitReg cfg.env.data.hi)
          0
          (RegEncoding.writeNat
            cfg.env.data
            (RegEncoding.toNat cfg.env.data z)
            z) := by
          simpa [m, splitLeft, splitRight, extendHi,
            qubitReg, Reg.hi, regSize, ASize] using hsplit
      _ =
        RegEncoding.writeNat
          (qubitReg cfg.env.data.hi)
          0
          z := by
          rw [RegEncoding.writeNat_toNat]
      _ =
        RegEncoding.writeNat
          (qubitReg cfg.env.data.hi)
          (RegEncoding.toNat (qubitReg cfg.env.data.hi) z)
          z := by
          rw [hz.2.1]
      _ = z :=
        RegEncoding.writeNat_toNat
          (qubitReg cfg.env.data.hi)
          z

  calc
    RegEncoding.writeNat
        (extendHi cfg.env.data)
        (RegEncoding.toNat cfg.env.data z)
        (RegEncoding.writeNat
          cfg.env.work
          0
          (RegEncoding.writeNat
            (extendHi cfg.env.data)
            y
            (RegEncoding.writeNat cfg.env.work w z)))
        =
      RegEncoding.writeNat
        (extendHi cfg.env.data)
        (RegEncoding.toNat cfg.env.data z)
        (RegEncoding.writeNat
          (extendHi cfg.env.data)
          y
          (RegEncoding.writeNat
            cfg.env.work
            0
            (RegEncoding.writeNat cfg.env.work w z))) := by
        rw [← writeNat_comm_of_disjoint
          (extendHi cfg.env.data)
          cfg.env.work
          cfg.layout.1
          y
          0
          (RegEncoding.writeNat cfg.env.work w z)]
    _ =
      RegEncoding.writeNat
        (extendHi cfg.env.data)
        (RegEncoding.toNat cfg.env.data z)
        (RegEncoding.writeNat cfg.env.work 0 z) := by
        rw [writeNat_overwrite_same_reg]
        rw [writeNat_overwrite_same_reg]
    _ =
      RegEncoding.writeNat
        cfg.env.work
        0
        (RegEncoding.writeNat
          (extendHi cfg.env.data)
          (RegEncoding.toNat cfg.env.data z)
          z) :=
        writeNat_comm_of_disjoint
          (extendHi cfg.env.data)
          cfg.env.work
          cfg.layout.1
          (RegEncoding.toNat cfg.env.data z)
          0
          z
    _ = RegEncoding.writeNat cfg.env.work 0 z := by
        rw [hrestore_ext]
    _ = z := by
        simpa [hz.2.2.1] using
          RegEncoding.writeNat_toNat cfg.env.work z

/--
A normalized valid trace has total input probability one.
-/
lemma alg1_trace_input_mass_one
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (ψ : qs.State)
    (tr : Alg1Trace qs cfg ψ) :
    cfg.ValidUnitState qs ψ →
      ∑ b ∈ tr.support, ‖tr.inputCoeff b‖ ^ 2 = 1 := by
  classical
  intro hunit

  have horth :
      ∀ b ∈ tr.support, ∀ b' ∈ tr.support, b ≠ b' →
        inner ℂ
          (tr.inputCoeff b • qs.ket b)
          (tr.inputCoeff b' • qs.ket b')
          =
        0 := by
    intro b hb b' hb' hne
    rw [
      inner_smul_left,
      inner_smul_right,
      qs.ket_inner_eq_zero_of_ne hne
    ]
    simp

  have hsq :
      ‖∑ b ∈ tr.support, tr.inputCoeff b • qs.ket b‖ ^ 2
        =
      ∑ b ∈ tr.support, ‖tr.inputCoeff b • qs.ket b‖ ^ 2 :=
    norm_sq_sum_eq_sum_norm_sq_of_orthogonal_qpe
      (qs := qs)
      tr.support
      (fun b => tr.inputCoeff b • qs.ket b)
      horth

  calc
    ∑ b ∈ tr.support, ‖tr.inputCoeff b‖ ^ 2
        =
      ∑ b ∈ tr.support, ‖tr.inputCoeff b • qs.ket b‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro b hb
        simp [norm_smul, ket_norm_one qs]
    _ =
      ‖∑ b ∈ tr.support, tr.inputCoeff b • qs.ket b‖ ^ 2 :=
        hsq.symm
    _ = ‖ψ‖ ^ 2 := by
      exact (congrArg (fun φ : qs.State => ‖φ‖ ^ 2) tr.input_eq).symm
    _ = 1 := by
      rw [hunit.2]
      norm_num


private lemma qpe_writeNat_overwrite_same_reg
    {Basis : Type u} [RegEncoding Basis]
    (r : Reg) (v w : ℕ) (b : Basis) :
    RegEncoding.writeNat r v (RegEncoding.writeNat r w b)
      =
    RegEncoding.writeNat r v b := by
  apply RegEncoding.basis_ext
  intro q
  by_cases hqin : r.lo ≤ q ∧ q < r.hi
  · exact
      RegEncoding.bit_writeNat_in
        (r := r)
        (v := v)
        (b1 := RegEncoding.writeNat r w b)
        (b2 := b)
        (q := q)
        hqin.1
        hqin.2
  ·
    have hqout : q < r.lo ∨ r.hi ≤ q := by
      rcases not_and_or.mp hqin with h | h
      · exact Or.inl (lt_of_not_ge h)
      · exact Or.inr (le_of_not_gt h)
    rw [
      RegEncoding.bit_writeNat_out
        (r := r) (v := v) (b := RegEncoding.writeNat r w b)
        (q := q) hqout,
      RegEncoding.bit_writeNat_out
        (r := r) (v := v) (b := b)
        (q := q) hqout,
      RegEncoding.bit_writeNat_out
        (r := r) (v := w) (b := b)
        (q := q) hqout
    ]

private lemma qpe_work_write_injective_of_good
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b b' : qs.Basis)
    (hb :
      GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b)
    (hb' :
      GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b')
    (t u : Fin (ASize cfg.env.work))
    (hEq :
      RegEncoding.writeNat cfg.env.work t.1 b
        =
      RegEncoding.writeNat cfg.env.work u.1 b') :
    b = b' ∧ t = u := by
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
                qpe_writeNat_overwrite_same_reg
                  cfg.env.work 0 t.1 b
      _ =
          RegEncoding.writeNat cfg.env.work 0
            (RegEncoding.writeNat cfg.env.work u.1 b') := by
              exact congrArg (RegEncoding.writeNat cfg.env.work 0) hEq
      _ =
          RegEncoding.writeNat cfg.env.work 0 b' := by
              exact
                qpe_writeNat_overwrite_same_reg
                  cfg.env.work 0 u.1 b'
      _ = b' := hb'_zero

  exact ⟨hbb, htu⟩

private lemma qpe_inner_trace_work_packet
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (ψ : qs.State)
    (tr : Alg1Trace qs cfg ψ)
    (coeff : qs.Basis → Fin (ASize cfg.env.work) → ℂ)
    (b : qs.Basis)
    (hb : b ∈ tr.support)
    (t : Fin (ASize cfg.env.work)) :
    inner ℂ
      (qs.ket (RegEncoding.writeNat cfg.env.work t.1 b))
      (∑ b' ∈ tr.support,
        tr.inputCoeff b' •
          ∑ u : Fin (ASize cfg.env.work),
            coeff b' u •
              qs.ket
                (RegEncoding.writeNat cfg.env.work u.1 b'))
      =
    tr.inputCoeff b * coeff b t := by
  classical

  rw [inner_sum]
  rw [Finset.sum_eq_single b]
  ·
    rw [inner_smul_right, inner_sum]
    rw [Finset.sum_eq_single t]
    ·
      rw [inner_smul_right, ket_inner_self]
      simp
    ·
      intro u _hu hut
      have hneq :
          RegEncoding.writeNat cfg.env.work t.1 b
            ≠
          RegEncoding.writeNat cfg.env.work u.1 b := by
        intro hEq
        rcases
            qpe_work_write_injective_of_good
              qs cfg b b
              (tr.input_good b hb)
              (tr.input_good b hb)
              t u hEq with
          ⟨_, htu⟩
        exact hut htu.symm
      rw [inner_smul_right, qs.ket_inner_eq_zero_of_ne hneq]
      simp
    ·
      intro ht
      simp at ht
  ·
    intro b' hb' hne
    rw [inner_smul_right, inner_sum]
    have hsum :
        ∑ i : Fin (ASize cfg.env.work),
          inner ℂ
            (qs.ket (RegEncoding.writeNat cfg.env.work t.1 b))
            (coeff b' i •
              qs.ket (RegEncoding.writeNat cfg.env.work i.1 b'))
          =
        0 := by
      apply Finset.sum_eq_zero
      intro u hu
      have hneq :
          RegEncoding.writeNat cfg.env.work t.1 b
            ≠
          RegEncoding.writeNat cfg.env.work u.1 b' := by
        intro hEq
        rcases
            qpe_work_write_injective_of_good
              qs cfg b b'
              (tr.input_good b hb)
              (tr.input_good b' hb')
              t u hEq with
          ⟨hbb, _⟩
        exact hne hbb.symm
      rw [inner_smul_right, qs.ket_inner_eq_zero_of_ne hneq]
      simp
    rw [hsum, mul_zero]
  ·
    intro hnot
    exact False.elim (hnot hb)

lemma alg1_trace_phaseCoeff_eq_alg1PhaseCoeff
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (ψ : qs.State)
    (tr : Alg1Trace qs cfg ψ)
    (b : qs.Basis)
    (hb : b ∈ tr.support)
    (hcoeff : tr.inputCoeff b ≠ 0)
    (t : Fin (ASize cfg.env.work)) :
    tr.phaseCoeff b t = alg1PhaseCoeff qs cfg b t := by
  classical

  have htrace :
      qs.eval (ModMulConfig.U1 (Basis := qs.Basis) cfg) ψ
        =
      ∑ b' ∈ tr.support,
        tr.inputCoeff b' •
          ∑ u : Fin (ASize cfg.env.work),
            tr.phaseCoeff b' u •
              qs.ket
                (RegEncoding.writeNat cfg.env.work u.1 b') := by
    simpa [ModMulConfig.U1] using tr.full_step1_eq

  have hcanonical :
      qs.eval (ModMulConfig.U1 (Basis := qs.Basis) cfg) ψ
        =
      ∑ b' ∈ tr.support,
        tr.inputCoeff b' •
          ∑ u : Fin (ASize cfg.env.work),
            alg1PhaseCoeff qs cfg b' u •
              qs.ket
                (RegEncoding.writeNat cfg.env.work u.1 b') := by
    calc
      qs.eval (ModMulConfig.U1 (Basis := qs.Basis) cfg) ψ
          =
        qs.eval (ModMulConfig.U1 (Basis := qs.Basis) cfg)
          (∑ b' ∈ tr.support, tr.inputCoeff b' • qs.ket b') := by
          exact
            congrArg
              (fun φ : qs.State =>
                qs.eval (ModMulConfig.U1 (Basis := qs.Basis) cfg) φ)
              tr.input_eq
      _ =
        ∑ b' ∈ tr.support,
          tr.inputCoeff b' •
            ∑ u : Fin (ASize cfg.env.work),
              alg1PhaseCoeff qs cfg b' u •
                qs.ket
                  (RegEncoding.writeNat cfg.env.work u.1 b') := by
          rw [eval_finset_sum]
          apply Finset.sum_congr rfl
          intro b' hb'
          rw [
            qs.eval_smul,
            alg1_step1_ket_qpe_expansion
              qs cfg b' (tr.input_good b' hb')
          ]

  have hpackets :
      (∑ b' ∈ tr.support,
        tr.inputCoeff b' •
          ∑ u : Fin (ASize cfg.env.work),
            tr.phaseCoeff b' u •
              qs.ket
                (RegEncoding.writeNat cfg.env.work u.1 b'))
        =
      ∑ b' ∈ tr.support,
        tr.inputCoeff b' •
          ∑ u : Fin (ASize cfg.env.work),
            alg1PhaseCoeff qs cfg b' u •
              qs.ket
                (RegEncoding.writeNat cfg.env.work u.1 b') :=
    htrace.symm.trans hcanonical

  have hprojected :=
    congrArg
      (fun ξ : qs.State =>
        inner ℂ
          (qs.ket (RegEncoding.writeNat cfg.env.work t.1 b))
          ξ)
      hpackets

  have hmul :
      tr.inputCoeff b * tr.phaseCoeff b t
        =
      tr.inputCoeff b * alg1PhaseCoeff qs cfg b t := by
    calc
      tr.inputCoeff b * tr.phaseCoeff b t
          =
        inner ℂ
          (qs.ket (RegEncoding.writeNat cfg.env.work t.1 b))
          (∑ b' ∈ tr.support,
            tr.inputCoeff b' •
              ∑ u : Fin (ASize cfg.env.work),
                tr.phaseCoeff b' u •
                  qs.ket
                    (RegEncoding.writeNat cfg.env.work u.1 b')) := by
              symm
              exact
                qpe_inner_trace_work_packet
                  qs cfg ψ tr tr.phaseCoeff b hb t
      _ =
        inner ℂ
          (qs.ket (RegEncoding.writeNat cfg.env.work t.1 b))
          (∑ b' ∈ tr.support,
            tr.inputCoeff b' •
              ∑ u : Fin (ASize cfg.env.work),
                alg1PhaseCoeff qs cfg b' u •
                  qs.ket
                    (RegEncoding.writeNat cfg.env.work u.1 b')) :=
        hprojected
      _ =
        tr.inputCoeff b * alg1PhaseCoeff qs cfg b t :=
        qpe_inner_trace_work_packet
          qs cfg ψ tr
          (fun b' u => alg1PhaseCoeff qs cfg b' u)
          b hb t

  exact mul_left_cancel₀ hcoeff hmul


/--
Rewrite the trace bad mass using canonical QPE coefficients.

Branches with zero input coefficient contribute zero, so canonicality is only
needed on nonzero branches.
-/
lemma alg1_trace_bad_mass_eq_weighted_qpe_bad_mass
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (ψ : qs.State)
    (tr : Alg1Trace qs cfg ψ) :
    alg1TraceBadMass qs cfg tr
      =
    ∑ b ∈ tr.support,
      ‖tr.inputCoeff b‖ ^ 2 * alg1QpeBadMass qs cfg b := by
  classical
  unfold alg1TraceBadMass alg1QpeBadMass
  apply Finset.sum_congr rfl
  intro b hb

  by_cases hzero : tr.inputCoeff b = 0
  · simp [hzero]
  ·
    apply congrArg (fun r : ℝ => ‖tr.inputCoeff b‖ ^ 2 * r)
    apply Finset.sum_congr rfl
    intro t ht
    rw [alg1_trace_phaseCoeff_eq_alg1PhaseCoeff
      qs cfg ψ tr b hb hzero t]

/--
Lift the basis tail estimate coherently across a normalized valid trace.

This is just finite weighted averaging: all weights are nonnegative and sum
to one by `alg1_trace_input_mass_one`.
-/
lemma alg1_trace_bad_mass_le_of_basis_tail
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {Ctail : ℝ}
    (hTail :
      ∀ (η : ℝ) (cfg : ModMulConfig η) (b : qs.Basis),
        GoodModMulBasisInput
          qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b →
        alg1QpeBadMass qs cfg b ≤ Ctail * η)
    {η : ℝ}
    (cfg : ModMulConfig η)
    (ψ : qs.State)
    (tr : Alg1Trace qs cfg ψ) :
    cfg.ValidUnitState qs ψ →
      alg1TraceBadMass qs cfg tr ≤ Ctail * η := by
  intro hunit
  rw [alg1_trace_bad_mass_eq_weighted_qpe_bad_mass qs cfg ψ tr]

  have hmass :
      ∑ b ∈ tr.support, ‖tr.inputCoeff b‖ ^ 2 = 1 :=
    alg1_trace_input_mass_one qs cfg ψ tr hunit

  have hpoint :
      ∀ b ∈ tr.support,
        ‖tr.inputCoeff b‖ ^ 2 * alg1QpeBadMass qs cfg b
          ≤
        ‖tr.inputCoeff b‖ ^ 2 * (Ctail * η) := by
    intro b hb
    exact
      mul_le_mul_of_nonneg_left
        (hTail η cfg b (tr.input_good b hb))
        (sq_nonneg _)

  calc
    ∑ b ∈ tr.support,
      ‖tr.inputCoeff b‖ ^ 2 * alg1QpeBadMass qs cfg b
        ≤
      ∑ b ∈ tr.support,
        ‖tr.inputCoeff b‖ ^ 2 * (Ctail * η) := by
          exact Finset.sum_le_sum fun b hb => hpoint b hb
    _ =
      (∑ b ∈ tr.support, ‖tr.inputCoeff b‖ ^ 2) * (Ctail * η) := by
        rw [Finset.sum_mul]
    _ = Ctail * η := by rw [hmass, one_mul]

/--
The Step-1 difference is exactly the discarded QPE packet.

Proof: expand `tr.full_step1_eq`, partition `Finset.univ` into good and bad
labels, and subtract the definition of `tr.goodStep1`.
-/
lemma alg1_step1_error_eq_bad_packet
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (ψ : qs.State)
    (tr : Alg1Trace qs cfg ψ) :
    qs.eval (ModMulConfig.U1 (Basis := qs.Basis) cfg) ψ
      - tr.goodStep1
      =
    tr.badStep1 := by
  classical

  change
    qs.eval
        (step1
          (Basis := qs.Basis)
          cfg.c cfg.env.N cfg.ctrl cfg.env.data cfg.env.work)
        ψ
      -
      tr.goodStep1
      =
      tr.badStep1

  rw [tr.full_step1_eq]
  simp only [Alg1Trace.goodStep1, Alg1Trace.badStep1]

  have hsplit :
      ∀ b : qs.Basis,
        (∑ t : Fin (ASize cfg.env.work),
          tr.phaseCoeff b t •
            qs.ket (RegEncoding.writeNat cfg.env.work t.1 b))
          =
        (∑ t ∈ alg1GoodLabels cfg b,
          tr.phaseCoeff b t •
            qs.ket (RegEncoding.writeNat cfg.env.work t.1 b))
          +
        ∑ t ∈ Finset.univ.filter
            (fun t => t ∉ alg1GoodLabels cfg b),
          tr.phaseCoeff b t •
            qs.ket (RegEncoding.writeNat cfg.env.work t.1 b) := by
    intro b

    let p : Fin (ASize cfg.env.work) → Prop :=
      fun t => t ∈ alg1GoodLabels cfg b

    have hgood :
        Finset.univ.filter p = alg1GoodLabels cfg b := by
      ext t
      simp [p]

    have h :=
      sum_filter_add_sum_filter_not
        Finset.univ
        p
        (fun t =>
          tr.phaseCoeff b t •
            qs.ket (RegEncoding.writeNat cfg.env.work t.1 b))

    rw [hgood] at h
    exact h.symm

  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  rw [hsplit b, smul_add]
  abel

lemma alg1_trace_afterStep34Full_eq_canonical
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (ψ : qs.State)
    (tr : Alg1Trace qs cfg ψ) :
    tr.afterStep34Full
      =
    ∑ b ∈ tr.support,
      tr.inputCoeff b •
        ∑ t : Fin (ASize cfg.env.work),
          alg1PhaseCoeff qs cfg b t •
            qs.ket
              (RegEncoding.writeNat
                (extendHi cfg.env.data)
                (alg1OutputValue cfg b)
                (RegEncoding.writeNat cfg.env.work t.1 b)) := by
  classical
  simp only [Alg1Trace.afterStep34Full]
  apply Finset.sum_congr rfl
  intro b hb

  by_cases hzero : tr.inputCoeff b = 0
  · simp [hzero]
  ·
    congr 1
    apply Finset.sum_congr rfl
    intro t ht
    rw [alg1_trace_phaseCoeff_eq_alg1PhaseCoeff
      qs cfg ψ tr b hb hzero t]

private lemma qpe_norm_sq_sum_eq_sum_norm_sq_of_orthogonal
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
        intro b hb
        apply horth a (by simp) b (Finset.mem_insert_of_mem hb)
        intro hab
        subst b
        exact ha hb

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

lemma alg1_badStep1_norm_sq_eq_trace_bad_mass
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (ψ : qs.State)
    (tr : Alg1Trace qs cfg ψ) :
    ‖tr.badStep1‖ ^ 2 = alg1TraceBadMass qs cfg tr := by
  classical

  let Sbad : Finset (Σ b : qs.Basis, Fin (ASize cfg.env.work)) :=
    tr.support.sigma fun b =>
      Finset.univ.filter (fun t => t ∉ alg1GoodLabels cfg b)

  let α : (Σ _b : qs.Basis, Fin (ASize cfg.env.work)) → ℂ :=
    fun i => tr.inputCoeff i.1 * tr.phaseCoeff i.1 i.2

  let label : (Σ _b : qs.Basis, Fin (ASize cfg.env.work)) → qs.Basis :=
    fun i =>
      RegEncoding.writeNat cfg.env.work i.2.1 i.1

  have hflat :
      tr.badStep1
        =
      ∑ i ∈ Sbad, α i • qs.ket (label i) := by
    simp [
      Sbad, α, label,
      Alg1Trace.badStep1,
      Finset.sum_sigma,
      Finset.smul_sum,
      smul_smul
    ]

  have hwrite_inj :
      ∀ i ∈ Sbad, ∀ j ∈ Sbad,
        label i = label j → i = j := by
    intro i hi j hj hEq

    rcases Finset.mem_sigma.mp hi with ⟨hi_b, _hi_t⟩
    rcases Finset.mem_sigma.mp hj with ⟨hj_b, _hj_t⟩

    have ht_val : i.2.1 = j.2.1 := by
      calc
        i.2.1
            =
          RegEncoding.toNat cfg.env.work
            (RegEncoding.writeNat cfg.env.work i.2.1 i.1) := by
              symm
              exact
                RegEncoding.toNat_writeNat_of_lt
                  cfg.env.work i.2.1 i.1 i.2.isLt
        _ =
          RegEncoding.toNat cfg.env.work
            (RegEncoding.writeNat cfg.env.work j.2.1 j.1) := by
              simpa [label] using
                congrArg (RegEncoding.toNat cfg.env.work) hEq
        _ = j.2.1 := by
              exact
                RegEncoding.toNat_writeNat_of_lt
                  cfg.env.work j.2.1 j.1 j.2.isLt

    have ht : i.2 = j.2 :=
      Fin.ext ht_val

    have hi_work :
        RegEncoding.toNat cfg.env.work i.1 = 0 :=
      (tr.input_good i.1 hi_b).2.2.1

    have hj_work :
        RegEncoding.toNat cfg.env.work j.1 = 0 :=
      (tr.input_good j.1 hj_b).2.2.1

    have hi_zero :
        RegEncoding.writeNat cfg.env.work 0 i.1 = i.1 := by
      simpa [hi_work] using
        (RegEncoding.writeNat_toNat cfg.env.work i.1)

    have hj_zero :
        RegEncoding.writeNat cfg.env.work 0 j.1 = j.1 := by
      simpa [hj_work] using
        (RegEncoding.writeNat_toNat cfg.env.work j.1)

    have hb : i.1 = j.1 := by
      calc
        i.1
            =
          RegEncoding.writeNat cfg.env.work 0 i.1 := hi_zero.symm
        _ =
          RegEncoding.writeNat cfg.env.work 0
            (RegEncoding.writeNat cfg.env.work i.2.1 i.1) := by
              symm
              exact
                qpe_writeNat_overwrite_same_reg
                  cfg.env.work 0 i.2.1 i.1
        _ =
          RegEncoding.writeNat cfg.env.work 0
            (RegEncoding.writeNat cfg.env.work j.2.1 j.1) := by
              exact
                congrArg (RegEncoding.writeNat cfg.env.work 0) hEq
        _ =
          RegEncoding.writeNat cfg.env.work 0 j.1 := by
              exact
                qpe_writeNat_overwrite_same_reg
                  cfg.env.work 0 j.2.1 j.1
        _ = j.1 := hj_zero

    cases i
    cases j
    simp at hb ht ⊢
    exact ⟨hb, ht⟩

  have hlabel_inj :
      ∀ i ∈ Sbad, ∀ j ∈ Sbad, i ≠ j →
        label i ≠ label j := by
    intro i hi j hj hij hEq
    exact hij (hwrite_inj i hi j hj hEq)

  have horth :
      ∀ i ∈ Sbad, ∀ j ∈ Sbad, i ≠ j →
        inner ℂ
          (α i • qs.ket (label i))
          (α j • qs.ket (label j))
          =
        0 := by
    intro i hi j hj hij
    rw [
      inner_smul_left,
      inner_smul_right,
      qs.ket_inner_eq_zero_of_ne (hlabel_inj i hi j hj hij)
    ]
    simp

  have hsq :
      ‖∑ i ∈ Sbad, α i • qs.ket (label i)‖ ^ 2
        =
      ∑ i ∈ Sbad, ‖α i • qs.ket (label i)‖ ^ 2 :=
    qpe_norm_sq_sum_eq_sum_norm_sq_of_orthogonal
      (qs := qs)
      Sbad
      (fun i => α i • qs.ket (label i))
      horth

  calc
    ‖tr.badStep1‖ ^ 2
        =
      ‖∑ i ∈ Sbad, α i • qs.ket (label i)‖ ^ 2 := by
        rw [hflat]
    _ =
      ∑ i ∈ Sbad, ‖α i • qs.ket (label i)‖ ^ 2 :=
        hsq
    _ =
      ∑ i ∈ Sbad,
        ‖tr.inputCoeff i.1‖ ^ 2
          *
        ‖tr.phaseCoeff i.1 i.2‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [α, norm_smul, ket_norm_one qs, mul_one]
        rw [norm_mul]
        ring
    _ = alg1TraceBadMass qs cfg tr := by
        unfold alg1TraceBadMass
        simp only [Sbad, Finset.sum_sigma]
        apply Finset.sum_congr rfl
        intro b hb
        rw [Finset.mul_sum]

lemma alg1_step1_error_sq_eq_trace_bad_mass
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (ψ : qs.State)
    (tr : Alg1Trace qs cfg ψ) :
    ‖qs.eval (ModMulConfig.U1 (Basis := qs.Basis) cfg) ψ
        - tr.goodStep1‖ ^ 2
      =
    alg1TraceBadMass qs cfg tr := by
  rw [
    alg1_step1_error_eq_bad_packet qs cfg ψ tr,
    alg1_badStep1_norm_sq_eq_trace_bad_mass qs cfg ψ tr
  ]

private lemma step5Constant_mul_output_mod_eq_target
    (c N x : ℕ)
    (hN : 1 < N)
    (hcoprime : Nat.Coprime c N) :
    (step5Constant c N * ((c * x) % N)) % N
      =
    (((c + N - 1) % N) * x) % N := by
  classical

  rcases step5Constant_ok c N hN hcoprime with
    ⟨cinv, hcinv_lt, hcinv, hk⟩

  let k : ℕ := step5Constant c N
  let d : ℕ := (c + N - 1) % N

  have hNpos : 0 < N :=
    Nat.lt_trans Nat.zero_lt_one hN

  have hcinv_mod :
      Nat.ModEq N (c * cinv) 1 := by
    change (c * cinv) % N = 1 % N
    exact hcinv

  have hk_mod :
      Nat.ModEq N k (1 + N - cinv) := by
    change k % N = (1 + N - cinv) % N
    exact hk

  have hsum :
      Nat.ModEq N (k + cinv) 1 := by
    calc
      k + cinv
          ≡ (1 + N - cinv) + cinv [MOD N] :=
        Nat.ModEq.add_right cinv hk_mod
      _ = 1 + N := by
        omega
      _ ≡ 1 [MOD N] := by
        change (1 + N) % N = 1 % N
        simp

  have hsum_mul :
      Nat.ModEq N (k * c + cinv * c) c := by
    have h := Nat.ModEq.mul_right c hsum
    simpa [Nat.add_mul, Nat.mul_one] using h

  have hcinv_comm :
      Nat.ModEq N (cinv * c) 1 := by
    simpa [Nat.mul_comm] using hcinv_mod

  have hk_mul_add_one :
      Nat.ModEq N (k * c + 1) c := by
    calc
      k * c + 1
          ≡ k * c + cinv * c [MOD N] :=
        Nat.ModEq.add_left (k * c) hcinv_comm.symm
      _ ≡ c [MOD N] := hsum_mul

  have hd_add_one :
      Nat.ModEq N (d + 1) c := by
    calc
      d + 1
          ≡ (c + N - 1) + 1 [MOD N] :=
        Nat.ModEq.add_right 1 (Nat.mod_modEq (c + N - 1) N)
      _ = c + N := by
        omega
      _ ≡ c [MOD N] := by
        change (c + N) % N = c % N
        simp

  have hkc :
      Nat.ModEq N (k * c) d := by
    apply Nat.ModEq.add_right_cancel' 1
    calc
      k * c + 1
          ≡ c [MOD N] := hk_mul_add_one
      _ ≡ d + 1 [MOD N] := hd_add_one.symm

  have hfinal :
      Nat.ModEq N (k * ((c * x) % N)) (d * x) := by
    calc
      k * ((c * x) % N)
          ≡ k * (c * x) [MOD N] :=
        Nat.ModEq.mul_left k (Nat.mod_modEq (c * x) N)
      _ = (k * c) * x := by
        ring
      _ ≡ d * x [MOD N] :=
        Nat.ModEq.mul_right x hkc

  change Nat.ModEq N (k * ((c * x) % N)) (d * x)
  exact hfinal


lemma alg1_step5_cleanup_residue_eq_target
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis):
    (if RegEncoding.bit cfg.ctrl b then
        (step5Constant cfg.c cfg.env.N * alg1OutputValue cfg b) % cfg.env.N
      else
        0)
      =
    alg1TargetResidue cfg b := by
  classical
  by_cases hctrl : RegEncoding.bit cfg.ctrl b
  ·
    simpa [alg1OutputValue, alg1TargetResidue, hctrl] using
      step5Constant_mul_output_mod_eq_target
        cfg.c
        cfg.env.N
        (RegEncoding.toNat cfg.env.data b)
        cfg.env.modulus_gt_one
        cfg.coprime
  ·
    simp [alg1TargetResidue, hctrl]

/-! =========================================================
    Atomic encoding and phase lemmas
========================================================= -/


lemma alg1_write_data_eq_extendHi_output
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis)
    (hb :
      GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b) :
    RegEncoding.writeNat
        cfg.env.data
        (alg1OutputValue cfg b)
        b
      =
    RegEncoding.writeNat
        (extendHi cfg.env.data)
        (alg1OutputValue cfg b)
        b := by
  let m : SplitPoint (extendHi cfg.env.data) :=
    ⟨regSize cfg.env.data, by
      change cfg.env.data.size ≤ cfg.env.data.size + 1
      omega⟩

  have hout_data :
      alg1OutputValue cfg b < ASize cfg.env.data :=
    alg1OutputValue_lt_data_capacity cfg b hb

  have hout_left :
      alg1OutputValue cfg b
        <
      ASize (splitLeft (extendHi cfg.env.data) m) := by
    simpa [m, splitLeft, extendHi, regSize, ASize] using hout_data

  have hzero_right :
      0 < ASize (splitRight (extendHi cfg.env.data) m) := by
    simp [m, splitRight, extendHi, regSize, ASize]

  have hsplit_raw :=
    RegEncoding.writeNat_split
      (extendHi cfg.env.data)
      m
      0
      (alg1OutputValue cfg b)
      b
      hout_left
      hzero_right

  have hsplit :
      RegEncoding.writeNat
          (extendHi cfg.env.data)
          (alg1OutputValue cfg b)
          b
        =
      RegEncoding.writeNat
          (qubitReg cfg.env.data.hi)
          0
          (RegEncoding.writeNat
            cfg.env.data
            (alg1OutputValue cfg b)
            b) := by
    simpa [
      m,
      splitLeft,
      splitRight,
      extendHi,
      qubitReg,
      Reg.hi,
      regSize,
      ASize
    ] using hsplit_raw

  have hcarry_disjoint :
      Disjoint (qubitReg cfg.env.data.hi) cfg.env.data := by
    right
    simp [qubitReg, Reg.hi]

  have hcarry_zero_after_data_write :
      RegEncoding.toNat
          (qubitReg cfg.env.data.hi)
          (RegEncoding.writeNat
            cfg.env.data
            (alg1OutputValue cfg b)
            b)
        =
      0 := by
    calc
      RegEncoding.toNat
          (qubitReg cfg.env.data.hi)
          (RegEncoding.writeNat
            cfg.env.data
            (alg1OutputValue cfg b)
            b)
        =
      RegEncoding.toNat (qubitReg cfg.env.data.hi) b := by
        exact
          RegEncoding.toNat_left_write_right
            (qubitReg cfg.env.data.hi)
            cfg.env.data
            hcarry_disjoint
            b
            (alg1OutputValue cfg b)
      _ = 0 := hb.2.1

  have hclear_carry :
      RegEncoding.writeNat
          (qubitReg cfg.env.data.hi)
          0
          (RegEncoding.writeNat
            cfg.env.data
            (alg1OutputValue cfg b)
            b)
        =
      RegEncoding.writeNat
        cfg.env.data
        (alg1OutputValue cfg b)
        b := by
    rw [← hcarry_zero_after_data_write]
    exact
      RegEncoding.writeNat_toNat
        (qubitReg cfg.env.data.hi)
        (RegEncoding.writeNat
          cfg.env.data
          (alg1OutputValue cfg b)
          b)

  calc
    RegEncoding.writeNat
        cfg.env.data
        (alg1OutputValue cfg b)
        b
      =
    RegEncoding.writeNat
        (qubitReg cfg.env.data.hi)
        0
        (RegEncoding.writeNat
          cfg.env.data
          (alg1OutputValue cfg b)
          b) := hclear_carry.symm
    _ =
    RegEncoding.writeNat
        (extendHi cfg.env.data)
        (alg1OutputValue cfg b)
        b := hsplit.symm


lemma alg1_ideal_ket_eq_extended_output
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [Spec]
    [IdealCtrlModMulExactSemantics qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis)
    (hb :
      GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b) :
    qs.eval (ModMulConfig.idealGate cfg) (qs.ket b)
      =
    qs.ket
      (RegEncoding.writeNat
        (extendHi cfg.env.data)
        (alg1OutputValue cfg b)
        b) := by
  rw [IdealCtrlModMulExactSemantics.eval_idealCtrlModMul_good_cfg qs cfg b hb]
  congr 1
  exact alg1_write_data_eq_extendHi_output qs cfg b hb

lemma alg1_exp_phase_eq_of_modEq
    (N u v z : ℕ)
    (hN : 0 < N)
    (huv : Nat.ModEq N u v) :
    Complex.exp
      (((2 * Real.pi) / (N : ℝ)) * Complex.I *
        ((u : ℂ) * (z : ℂ)))
      =
    Complex.exp
      (((2 * Real.pi) / (N : ℝ)) * Complex.I *
        ((v : ℂ) * (z : ℂ))) := by
  have hphase (x y : ℕ) :
      Complex.exp
        (((2 * Real.pi) / (N : ℝ)) * Complex.I *
          ((x : ℂ) * (y : ℂ)))
        =
      qftPhase N x y := by
    simp [qftPhase, ωPow, ω, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring

  have hroot : (ω N) ^ N = 1 := by
    have hN0 : (N : ℂ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hN
    unfold ω
    rw [← Complex.exp_nat_mul]
    have harg :
        (N : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))
          =
        Complex.I * ((Real.pi : ℂ) * 2) := by
      field_simp [hN0, mul_assoc, mul_left_comm, mul_comm]
    rw [harg]
    simpa [mul_assoc, mul_left_comm, mul_comm] using Complex.exp_two_pi_mul_I

  have hpow_mod :
      ∀ a b : ℕ, Nat.ModEq N a b → (ω N) ^ a = (ω N) ^ b := by
    intro a b hab
    have hrem : a % N = b % N := by
      simpa [Nat.ModEq] using hab
    calc
      (ω N) ^ a
          =
        (ω N) ^ (a % N + N * (a / N)) := by
          rw [Nat.mod_add_div a N]
      _ =
        (ω N) ^ (a % N) := by
          rw [pow_add, pow_mul, hroot]
          simp
      _ =
        (ω N) ^ (b % N) := by
          rw [hrem]
      _ =
        (ω N) ^ (b % N + N * (b / N)) := by
          rw [pow_add, pow_mul, hroot]
          simp
      _ =
        (ω N) ^ b := by
          rw [Nat.mod_add_div b N]

  have hpow :
      (ω N) ^ (u * z) = (ω N) ^ (v * z) :=
    hpow_mod (u * z) (v * z) (Nat.ModEq.mul_right z huv)

  calc
    Complex.exp
        (((2 * Real.pi) / (N : ℝ)) * Complex.I *
          ((u : ℂ) * (z : ℂ)))
      =
    qftPhase N u z := hphase u z
    _ =
    qftPhase N v z := by
      simpa [qftPhase, ωPow] using hpow
    _ =
    Complex.exp
        (((2 * Real.pi) / (N : ℝ)) * Complex.I *
          ((v : ℂ) * (z : ℂ))) :=
      (hphase v z).symm


lemma alg1_step1_phase_scalar_eq_target
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis)
    (z : Fin (ASize cfg.env.work)) :
    alg1Step1PhaseScalar cfg b z
      =
    alg1TargetPhaseScalar cfg b z := by
  classical
  by_cases hctrl : RegEncoding.bit cfg.ctrl b
  ·
    let a : ℕ := (cfg.c + cfg.env.N - 1) % cfg.env.N
    let x : ℕ := RegEncoding.toNat cfg.env.data b
    let r : ℕ := alg1TargetResidue cfg b
    let N : ℕ := cfg.env.N

    have hNpos : 0 < N := by
      dsimp [N]
      exact Nat.lt_trans Nat.zero_lt_one cfg.env.modulus_gt_one

    have hr :
        r = (a * x) % N := by
      simp [r, a, x, N, alg1TargetResidue, hctrl]

    have hmod :
        Nat.ModEq N (a * x) r := by
      rw [hr]
      exact (Nat.mod_modEq (a * x) N).symm

    have hphase :
        alg1Step1Phase cfg
          =
        (2 * Real.pi * (a : ℝ)) / (N : ℝ) := by
      dsimp [alg1Step1Phase, a, N]

    simp only [
      alg1Step1PhaseScalar,
      alg1TargetPhaseScalar,
      hctrl,
      if_true
    ]

    calc
      Complex.exp
          (alg1Step1Phase cfg * Complex.I *
            ((RegEncoding.toNat cfg.env.data b : ℂ) * (z.1 : ℂ)))
        =
      Complex.exp
        (((2 * Real.pi) / (N : ℝ)) *
          Complex.I *
          (((a * x : ℕ) : ℂ) * (z.1 : ℂ))) := by
          congr 1
          rw [hphase]
          dsimp [x]
          push_cast
          ring
      _ =
      Complex.exp
        (((2 * Real.pi) / (N : ℝ)) *
          Complex.I *
          ((r : ℂ) * (z.1 : ℂ))) :=
        alg1_exp_phase_eq_of_modEq N (a * x) r z.1 hNpos hmod

  ·
    simp [
      alg1Step1PhaseScalar,
      alg1TargetPhaseScalar,
      hctrl
    ]


lemma alg1_step5_phase_scalar_eq_target
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis)
    (_hb :
      GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b)
    (z : Fin (ASize cfg.env.work)) :
    (if RegEncoding.bit cfg.ctrl b then
      Complex.exp
        (alg1Step5Phase cfg * Complex.I *
          ((alg1OutputValue cfg b : ℂ) * (z.1 : ℂ)))
    else
      1)
      =
    alg1TargetPhaseScalar cfg b z := by
  classical
  by_cases hctrl : RegEncoding.bit cfg.ctrl b
  ·
    let k : ℕ := step5Constant cfg.c cfg.env.N
    let x : ℕ := alg1OutputValue cfg b
    let r : ℕ := alg1TargetResidue cfg b
    let N : ℕ := cfg.env.N

    have hNpos : 0 < N := by
      dsimp [N]
      exact Nat.lt_trans Nat.zero_lt_one cfg.env.modulus_gt_one

    have hr_lt : r < N := by
      dsimp [r, N]
      exact alg1TargetResidue_lt_N cfg b

    have hcleanup :
        (k * x) % N = r := by
      have h :=
        alg1_step5_cleanup_residue_eq_target
          qs
          cfg
          b
      simpa [k, x, r, N, hctrl] using h

    have hraw :
        Nat.ModEq N (k * x) r := by
      change (k * x) % N = r % N
      rw [hcleanup, Nat.mod_eq_of_lt hr_lt]

    have hmod_left :
        Nat.ModEq N ((k % N) * x) (k * x) :=
      Nat.ModEq.mul_right x (Nat.mod_modEq k N)

    have hmod :
        Nat.ModEq N ((k % N) * x) r :=
      hmod_left.trans hraw

    have hphase :
        alg1Step5Phase cfg
          =
        (2 * Real.pi * ((k % N : ℕ) : ℝ)) / (N : ℝ) := by
      dsimp [alg1Step5Phase, k, N]

    simp only [
      alg1TargetPhaseScalar,
      hctrl,
      if_true
    ]

    calc
      Complex.exp
          (alg1Step5Phase cfg * Complex.I *
            ((alg1OutputValue cfg b : ℂ) * (z.1 : ℂ)))
        =
      Complex.exp
        (((2 * Real.pi) / (N : ℝ)) *
          Complex.I *
          ((((k % N) * x : ℕ) : ℂ) * (z.1 : ℂ))) := by
          congr 1
          rw [hphase]
          dsimp [x]
          push_cast
          ring
      _ =
      Complex.exp
        (((2 * Real.pi) / (N : ℝ)) *
          Complex.I *
          ((r : ℂ) * (z.1 : ℂ))) :=
        alg1_exp_phase_eq_of_modEq N ((k % N) * x) r z.1 hNpos hmod

  ·
    simp [
      alg1TargetPhaseScalar,
      hctrl
    ]


lemma alg1_step5_phase_scalar_eq_step1
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis)
    (hb :
      GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b)
    (z : Fin (ASize cfg.env.work)) :
    (if RegEncoding.bit cfg.ctrl b then
      Complex.exp
        (alg1Step5Phase cfg * Complex.I *
          ((alg1OutputValue cfg b : ℂ) * (z.1 : ℂ)))
    else
      1)
      =
    alg1Step1PhaseScalar cfg b z := by
  rw [
    alg1_step5_phase_scalar_eq_target qs cfg b hb z,
    alg1_step1_phase_scalar_eq_target qs cfg b z
  ]




/-! =========================================================
    Local diagonal semantics
========================================================= -/

/--
The Step-1 CPhaseProd action on one work basis label.

Proof: apply `GateSemanticsFacts.eval_CPhaseProd_ket`, then use:
* `data` and `work` disjoint;
* `ctrl` outside `work`;
* `toNat work (write work z b) = z`.
-/
lemma alg1_step1_cphase_on_work_label
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis)
    (z : Fin (ASize cfg.env.work)) :
    qs.eval
        (Gate.CPhaseProd
          cfg.ctrl
          (alg1Step1Phase cfg)
          cfg.env.data
          cfg.env.work)
        (qs.ket
          (RegEncoding.writeNat cfg.env.work z.1 b))
      =
    alg1Step1PhaseScalar cfg b z •
      qs.ket
        (RegEncoding.writeNat cfg.env.work z.1 b) := by
  have hdatawork : Disjoint cfg.env.data cfg.env.work := by
    rcases cfg.layout.1 with h | h
    · left
      change cfg.env.data.lo + cfg.env.data.size ≤ cfg.env.work.lo
      have h' :
          cfg.env.data.lo + (cfg.env.data.size + 1)
            ≤ cfg.env.work.lo := by
        simpa [extendHi, Reg.hi] using h
      omega
    · exact Or.inr h

  have hctrl :
      RegEncoding.bit cfg.ctrl
          (RegEncoding.writeNat cfg.env.work z.1 b)
        =
      RegEncoding.bit cfg.ctrl b :=
    RegEncoding.bit_writeNat_out
      (r := cfg.env.work)
      (v := z.1)
      (b := b)
      (q := cfg.ctrl)
      cfg.layout.2.2.2.2.1

  have hdata :
      RegEncoding.toNat cfg.env.data
          (RegEncoding.writeNat cfg.env.work z.1 b)
        =
      RegEncoding.toNat cfg.env.data b :=
    RegEncoding.toNat_left_write_right
      cfg.env.data
      cfg.env.work
      hdatawork
      b
      z.1

  have hwork :
      RegEncoding.toNat cfg.env.work
          (RegEncoding.writeNat cfg.env.work z.1 b)
        =
      z.1 :=
    RegEncoding.toNat_writeNat_of_lt
      cfg.env.work
      z.1
      b
      z.isLt

  rw [
    GateSemanticsFacts.eval_CPhaseProd_ket
      qs
      cfg.ctrl
      (alg1Step1Phase cfg)
      cfg.env.data
      cfg.env.work
      (RegEncoding.writeNat cfg.env.work z.1 b)
      hdatawork
  ]
  simp [alg1Step1PhaseScalar, hctrl, hdata, hwork]

/--
The forward Step-5 CPhaseProd action on one work label.

The output basis has the desired modular result in `extendHi data`; this
lemma identifies its diagonal scalar with the original Step-1 scalar.
-/
lemma alg1_step5_cphase_on_output_work_label
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis)
    (hb :
      GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b)
    (z : Fin (ASize cfg.env.work)) :
    qs.eval
        (Gate.CPhaseProd
          cfg.ctrl
          (alg1Step5Phase cfg)
          (extendHi cfg.env.data)
          cfg.env.work)
        (qs.ket
          (RegEncoding.writeNat cfg.env.work z.1
            (RegEncoding.writeNat
              (extendHi cfg.env.data)
              (alg1OutputValue cfg b)
              b)))
      =
    alg1Step1PhaseScalar cfg b z •
      qs.ket
        (RegEncoding.writeNat cfg.env.work z.1
          (RegEncoding.writeNat
            (extendHi cfg.env.data)
            (alg1OutputValue cfg b)
            b)) := by
  have hout_lt :
      alg1OutputValue cfg b < ASize (extendHi cfg.env.data) := by
    have hout_data :
        alg1OutputValue cfg b < ASize cfg.env.data :=
      alg1OutputValue_lt_data_capacity cfg b hb
    have hle :
        ASize cfg.env.data ≤ ASize (extendHi cfg.env.data) := by
      simp [ASize, regSize, extendHi, Nat.pow_succ]
    exact lt_of_lt_of_le hout_data hle

  have hctrl_ext :
      RegEncoding.bit cfg.ctrl
          (RegEncoding.writeNat
            (extendHi cfg.env.data)
            (alg1OutputValue cfg b)
            b)
        =
      RegEncoding.bit cfg.ctrl b :=
    RegEncoding.bit_writeNat_out
      (r := extendHi cfg.env.data)
      (v := alg1OutputValue cfg b)
      (b := b)
      (q := cfg.ctrl)
      cfg.layout.2.2.2.1

  have hctrl :
      RegEncoding.bit cfg.ctrl
          (RegEncoding.writeNat cfg.env.work z.1
            (RegEncoding.writeNat
              (extendHi cfg.env.data)
              (alg1OutputValue cfg b)
              b))
        =
      RegEncoding.bit cfg.ctrl b := by
    calc
      RegEncoding.bit cfg.ctrl
          (RegEncoding.writeNat cfg.env.work z.1
            (RegEncoding.writeNat
              (extendHi cfg.env.data)
              (alg1OutputValue cfg b)
              b))
        =
      RegEncoding.bit cfg.ctrl
        (RegEncoding.writeNat
          (extendHi cfg.env.data)
          (alg1OutputValue cfg b)
          b) :=
        RegEncoding.bit_writeNat_out
          (r := cfg.env.work)
          (v := z.1)
          (b := RegEncoding.writeNat
            (extendHi cfg.env.data)
            (alg1OutputValue cfg b)
            b)
          (q := cfg.ctrl)
          cfg.layout.2.2.2.2.1
      _ = RegEncoding.bit cfg.ctrl b := hctrl_ext

  have hdata :
      RegEncoding.toNat (extendHi cfg.env.data)
          (RegEncoding.writeNat cfg.env.work z.1
            (RegEncoding.writeNat
              (extendHi cfg.env.data)
              (alg1OutputValue cfg b)
              b))
        =
      alg1OutputValue cfg b := by
    calc
      RegEncoding.toNat (extendHi cfg.env.data)
          (RegEncoding.writeNat cfg.env.work z.1
            (RegEncoding.writeNat
              (extendHi cfg.env.data)
              (alg1OutputValue cfg b)
              b))
        =
      RegEncoding.toNat (extendHi cfg.env.data)
        (RegEncoding.writeNat
          (extendHi cfg.env.data)
          (alg1OutputValue cfg b)
          b) := by
        exact
          RegEncoding.toNat_left_write_right
            (extendHi cfg.env.data)
            cfg.env.work
            cfg.layout.1
            (RegEncoding.writeNat
              (extendHi cfg.env.data)
              (alg1OutputValue cfg b)
              b)
            z.1
      _ = alg1OutputValue cfg b :=
        RegEncoding.toNat_writeNat_of_lt
          (extendHi cfg.env.data)
          (alg1OutputValue cfg b)
          b
          hout_lt

  have hwork :
      RegEncoding.toNat cfg.env.work
          (RegEncoding.writeNat cfg.env.work z.1
            (RegEncoding.writeNat
              (extendHi cfg.env.data)
              (alg1OutputValue cfg b)
              b))
        =
      z.1 :=
    RegEncoding.toNat_writeNat_of_lt
      cfg.env.work
      z.1
      (RegEncoding.writeNat
        (extendHi cfg.env.data)
        (alg1OutputValue cfg b)
        b)
      z.isLt

  rw [
    GateSemanticsFacts.eval_CPhaseProd_ket
      qs
      cfg.ctrl
      (alg1Step5Phase cfg)
      (extendHi cfg.env.data)
      cfg.env.work
      (RegEncoding.writeNat cfg.env.work z.1
        (RegEncoding.writeNat
          (extendHi cfg.env.data)
          (alg1OutputValue cfg b)
          b))
      cfg.layout.1
  ]

  have hphase :
      (if RegEncoding.bit cfg.ctrl
          (RegEncoding.writeNat cfg.env.work z.1
            (RegEncoding.writeNat
              (extendHi cfg.env.data)
              (alg1OutputValue cfg b)
              b)) then
        Complex.exp
          (alg1Step5Phase cfg * Complex.I *
            ((RegEncoding.toNat (extendHi cfg.env.data)
                (RegEncoding.writeNat cfg.env.work z.1
                  (RegEncoding.writeNat
                    (extendHi cfg.env.data)
                    (alg1OutputValue cfg b)
                    b)) : ℂ) *
             (RegEncoding.toNat cfg.env.work
                (RegEncoding.writeNat cfg.env.work z.1
                  (RegEncoding.writeNat
                    (extendHi cfg.env.data)
                    (alg1OutputValue cfg b)
                    b)) : ℂ)))
      else
        1)
        =
      alg1Step1PhaseScalar cfg b z := by
    rw [hctrl, hdata, hwork]
    exact alg1_step5_phase_scalar_eq_step1 qs cfg b hb z

  rw [hphase]


/-! =========================================================
    Exact packet algebra
========================================================= -/

private lemma writeNat_overwrite_same_reg_step5
    {Basis : Type*} [RegEncoding Basis]
    (r : Reg) (v w : ℕ) (b : Basis) :
    RegEncoding.writeNat r v (RegEncoding.writeNat r w b)
      =
    RegEncoding.writeNat r v b := by
  apply RegEncoding.basis_ext
  intro q
  by_cases hqin : r.lo ≤ q ∧ q < r.hi
  · exact
      RegEncoding.bit_writeNat_in
        (r := r)
        (v := v)
        (b1 := RegEncoding.writeNat r w b)
        (b2 := b)
        (q := q)
        hqin.1
        hqin.2
  ·
    have hqout : q < r.lo ∨ r.hi ≤ q := by
      rcases not_and_or.mp hqin with h | h
      · exact Or.inl (lt_of_not_ge h)
      · exact Or.inr (le_of_not_gt h)
    rw [
      RegEncoding.bit_writeNat_out
        (r := r) (v := v) (b := RegEncoding.writeNat r w b)
        (q := q) hqout,
      RegEncoding.bit_writeNat_out
        (r := r) (v := v) (b := b)
        (q := q) hqout,
      RegEncoding.bit_writeNat_out
        (r := r) (v := w) (b := b)
        (q := q) hqout
    ]

/--
Explicit inverse-QFT evaluation on an arbitrary finite work packet.

Unlike `eval_iqft_work_expansion`, this specifies the coefficient exactly.
-/
lemma eval_IQFT_work_packet
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (work : Reg)
    (base : qs.Basis)
    (β : Fin (ASize work) → ℂ) :
    qs.eval (IQFT work)
      (∑ z : Fin (ASize work),
        β z • qs.ket (RegEncoding.writeNat work z.1 base))
      =
    ∑ t : Fin (ASize work),
      (∑ z : Fin (ASize work),
        β z * alg1IQFTCoeff work z t) •
        qs.ket (RegEncoding.writeNat work t.1 base) := by
  classical

  have hsingle :
      ∀ z : Fin (ASize work),
        qs.eval (IQFT work)
          (qs.ket (RegEncoding.writeNat work z.1 base))
        =
        ∑ t : Fin (ASize work),
          alg1IQFTCoeff work z t •
            qs.ket (RegEncoding.writeNat work t.1 base) := by
    intro z
    rw [IQFT, QFTSemantics.eval_adj_QFT_ket]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    rw [smul_smul]
    simp [
      alg1IQFTCoeff,
      RegEncoding.toNat_writeNat_of_lt work z.1 base z.isLt,
      writeNat_overwrite_same_reg_step5
    ]

  calc
    qs.eval (IQFT work)
        (∑ z : Fin (ASize work),
          β z • qs.ket (RegEncoding.writeNat work z.1 base))
      =
    ∑ z : Fin (ASize work),
      β z •
        qs.eval (IQFT work)
          (qs.ket (RegEncoding.writeNat work z.1 base)) := by
        rw [eval_finset_sum]
        apply Finset.sum_congr rfl
        intro z hz
        rw [qs.eval_smul]

    _ =
    ∑ z : Fin (ASize work),
      β z •
        ∑ t : Fin (ASize work),
          alg1IQFTCoeff work z t •
            qs.ket (RegEncoding.writeNat work t.1 base) := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [hsingle z]

    _ =
    ∑ t : Fin (ASize work),
      (∑ z : Fin (ASize work),
        β z * alg1IQFTCoeff work z t) •
        qs.ket (RegEncoding.writeNat work t.1 base) := by
        calc
          ∑ z : Fin (ASize work),
            β z •
              ∑ t : Fin (ASize work),
                alg1IQFTCoeff work z t •
                  qs.ket (RegEncoding.writeNat work t.1 base)
              =
            ∑ z : Fin (ASize work),
              ∑ t : Fin (ASize work),
                (β z * alg1IQFTCoeff work z t) •
                  qs.ket (RegEncoding.writeNat work t.1 base) := by
              apply Finset.sum_congr rfl
              intro z hz
              rw [Finset.smul_sum]
              apply Finset.sum_congr rfl
              intro t ht
              rw [smul_smul]
          _ =
            ∑ t : Fin (ASize work),
              ∑ z : Fin (ASize work),
                (β z * alg1IQFTCoeff work z t) •
                  qs.ket (RegEncoding.writeNat work t.1 base) := by
              rw [Finset.sum_comm]
          _ =
            ∑ t : Fin (ASize work),
              (∑ z : Fin (ASize work),
                β z * alg1IQFTCoeff work z t) •
                qs.ket (RegEncoding.writeNat work t.1 base) := by
              apply Finset.sum_congr rfl
              intro t ht
              rw [← Finset.sum_smul]


/--
The pre-IQFT Step-1 packet.

This is proved entirely from `eval_Hreg_zero_uniform_sum`, diagonal CPhaseProd
semantics, and linearity.
-/
lemma alg1_step1_preIQFT_packet
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis)
    (hb :
      GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b) :
    qs.eval
        ((H_reg cfg.env.work) ;;
          (Gate.CPhaseProd
            cfg.ctrl
            (alg1Step1Phase cfg)
            cfg.env.data
            cfg.env.work))
        (qs.ket b)
      =
    ∑ z : Fin (ASize cfg.env.work),
      alg1LoadPreCoeff cfg b z •
        qs.ket (RegEncoding.writeNat cfg.env.work z.1 b) := by
  classical

  rw [qs.eval_seq, eval_Hreg_zero_uniform_sum qs cfg.env.work b hb.2.2.1]
  rw [qs.eval_smul, eval_finset_sum, Finset.smul_sum]

  apply Finset.sum_congr rfl
  intro z hz
  rw [alg1_step1_cphase_on_work_label qs cfg b z]
  rw [smul_smul]
  rfl


/--
The pre-IQFT forward Step-5 packet, still expressed relative to the ideal
output basis state.
-/
lemma alg1_step5_forward_preIQFT_packet
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis)
    (hb :
      GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b) :
    qs.eval
        ((H_reg cfg.env.work) ;;
          (Gate.CPhaseProd
            cfg.ctrl
            (alg1Step5Phase cfg)
            (extendHi cfg.env.data)
            cfg.env.work))
        (qs.ket
          (RegEncoding.writeNat
            (extendHi cfg.env.data)
            (alg1OutputValue cfg b)
            b))
      =
    ∑ z : Fin (ASize cfg.env.work),
      alg1LoadPreCoeff cfg b z •
        qs.ket
          (RegEncoding.writeNat cfg.env.work z.1
            (RegEncoding.writeNat
              (extendHi cfg.env.data)
              (alg1OutputValue cfg b)
              b)) := by
  classical

  have hwork0 :
      RegEncoding.toNat cfg.env.work
        (RegEncoding.writeNat
          (extendHi cfg.env.data)
          (alg1OutputValue cfg b)
          b)
        =
      0 := by
    calc
      RegEncoding.toNat cfg.env.work
          (RegEncoding.writeNat
            (extendHi cfg.env.data)
            (alg1OutputValue cfg b)
            b)
        =
      RegEncoding.toNat cfg.env.work b := by
        exact
          RegEncoding.toNat_right_write_left
            (extendHi cfg.env.data)
            cfg.env.work
            cfg.layout.1
            b
            (alg1OutputValue cfg b)
      _ = 0 := hb.2.2.1

  rw [qs.eval_seq]
  rw [
    eval_Hreg_zero_uniform_sum
      qs
      cfg.env.work
      (RegEncoding.writeNat
        (extendHi cfg.env.data)
        (alg1OutputValue cfg b)
        b)
      hwork0
  ]
  rw [qs.eval_smul, eval_finset_sum, Finset.smul_sum]

  apply Finset.sum_congr rfl
  intro z hz
  rw [alg1_step5_cphase_on_output_work_label qs cfg b hb z]
  rw [smul_smul]
  rfl


/--
The original canonical QPE coefficient is the explicit Fourier coefficient.

Proof: combine `alg1_step1_preIQFT_packet` with `eval_IQFT_work_packet`, then
project both sides onto `ket (writeNat work t b)`.
-/
lemma alg1PhaseCoeff_eq_fractionalLoadCoeff
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis)
    (hb :
      GoodModMulBasisInput
        qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b)
    (t : Fin (ASize cfg.env.work)) :
    alg1PhaseCoeff qs cfg b t
      =
    alg1FractionalLoadCoeff cfg b t := by
  classical

  have hlabel_inj :
      ∀ s u : Fin (ASize cfg.env.work),
        RegEncoding.writeNat cfg.env.work s.1 b
          =
        RegEncoding.writeNat cfg.env.work u.1 b →
        s = u := by
    intro s u hEq
    apply Fin.ext
    calc
      s.1
          =
        RegEncoding.toNat cfg.env.work
          (RegEncoding.writeNat cfg.env.work s.1 b) := by
            symm
            exact
              RegEncoding.toNat_writeNat_of_lt
                cfg.env.work s.1 b s.isLt
      _ =
        RegEncoding.toNat cfg.env.work
          (RegEncoding.writeNat cfg.env.work u.1 b) := by
            rw [hEq]
      _ = u.1 :=
        RegEncoding.toNat_writeNat_of_lt
          cfg.env.work u.1 b u.isLt

  have hU1 :
      qs.eval
          (ModMulConfig.U1 (Basis := qs.Basis) cfg)
          (qs.ket b)
        =
      ∑ s : Fin (ASize cfg.env.work),
        alg1FractionalLoadCoeff cfg b s •
          qs.ket
            (RegEncoding.writeNat cfg.env.work s.1 b) := by
    calc
      qs.eval
          (ModMulConfig.U1 (Basis := qs.Basis) cfg)
          (qs.ket b)
        =
      qs.eval
        (IQFT cfg.env.work)
        (qs.eval
          ((H_reg cfg.env.work) ;;
            Gate.CPhaseProd
              cfg.ctrl
              (alg1Step1Phase cfg)
              cfg.env.data
              cfg.env.work)
          (qs.ket b)) := by
            simp [ModMulConfig.U1, step1, qs.eval_seq]
            congr

      _ =
      qs.eval
        (IQFT cfg.env.work)
        (∑ z : Fin (ASize cfg.env.work),
          alg1LoadPreCoeff cfg b z •
            qs.ket
              (RegEncoding.writeNat cfg.env.work z.1 b)) := by
            rw [alg1_step1_preIQFT_packet qs cfg b hb]

      _ =
      ∑ s : Fin (ASize cfg.env.work),
        alg1FractionalLoadCoeff cfg b s •
          qs.ket
            (RegEncoding.writeNat cfg.env.work s.1 b) := by
            simpa [alg1FractionalLoadCoeff] using
              (eval_IQFT_work_packet
                qs
                cfg.env.work
                b
                (alg1LoadPreCoeff cfg b))

  unfold alg1PhaseCoeff
  rw [hU1]
  rw [inner_sum]
  rw [Finset.sum_eq_single t]
  · rw [inner_smul_right, ket_inner_self]
    simp
  · intro u _hu htu
    have hneq :
        RegEncoding.writeNat cfg.env.work t.1 b
          ≠
        RegEncoding.writeNat cfg.env.work u.1 b := by
      intro hEq
      exact htu ((hlabel_inj t u hEq).symm)

    rw [
      inner_smul_right,
      qs.ket_inner_eq_zero_of_ne hneq
    ]
    simp
  · intro ht
    simp at ht

/-! =========================================================
    Analytic QPE tail bound
========================================================= -/

/--
The normalized Fourier kernel for a phase `θ`, sampled on an `M`-point
inverse-QFT grid.

For Algorithm 1 we use `θ = alg1TargetResidue / N`.
-/
noncomputable def qpeKernel
    (M : ℕ)
    (θ : ℝ)
    (t : Fin M) : ℂ :=
  (1 / (M : ℂ)) *
    ∑ z : Fin M,
      Complex.exp
        (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
          (((θ : ℂ) - ((t.1 : ℂ) / (M : ℂ))) * (z.1 : ℂ)))

/--
Rewrite the Step-1 phase as the continuous QPE source phase centred at
`alg1TargetFraction cfg b`.
-/
private lemma alg1Step1PhaseScalar_eq_qpe_source_phase
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis)
    (z : Fin (ASize cfg.env.work)) :
    alg1Step1PhaseScalar cfg b z
      =
    Complex.exp
      (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
        ((alg1TargetFraction cfg b : ℂ) * (z.1 : ℂ))) := by
  rw [alg1_step1_phase_scalar_eq_target qs cfg b z]
  classical
  by_cases hctrl : RegEncoding.bit cfg.ctrl b
  ·
    simp only [
      alg1TargetPhaseScalar,
      alg1TargetFraction,
      alg1TargetResidue,
      hctrl,
      if_true
    ]
    congr 1
    push_cast
    simp [div_eq_mul_inv]
    ring
  ·
    simp [
      alg1TargetPhaseScalar,
      alg1TargetFraction,
      alg1TargetResidue,
      hctrl
    ]

/--
Write the QFT matrix entry as an ordinary complex exponential.

This is the same `qftPhase` expansion already used inside
`alg1_exp_phase_eq_of_modEq`.
-/
private lemma qftPhase_eq_exp_grid
    (M z t : ℕ) :
    qftPhase M z t
      =
    Complex.exp
      (((2 * Real.pi) / (M : ℝ)) * Complex.I *
        ((z : ℂ) * (t : ℂ))) := by
  simp [
    qftPhase,
    ωPow,
    ω,
    div_eq_mul_inv,
    mul_assoc,
    mul_left_comm,
    mul_comm
  ]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/--
The conjugated inverse-QFT phase is the negative grid phase.
-/
private lemma star_qftPhase_eq_negative_grid_phase
    (M z t : ℕ) :
    star (qftPhase M z t)
      =
    Complex.exp
      (-(((2 * Real.pi : ℝ) : ℂ) * Complex.I *
        (((z : ℂ) * (t : ℂ)) / (M : ℂ)))) := by
  rw [qftPhase_eq_exp_grid]
  simp
  rw [← Complex.exp_conj]
  congr 1
  simp [div_eq_mul_inv]
  simp[starRingEnd]
  ring

/--
The two QFT/H normalizers multiply to the usual `1 / M` QPE normalizer.

This is only square-root algebra; it is independent of Algorithm 1.
-/
private lemma qpe_normalizer_sq
    (M : ℕ)
    (hM : 0 < M) :
    (1 / Real.sqrt (M : ℝ) : ℂ) *
      (1 / Real.sqrt (M : ℝ) : ℂ)
      =
    1 / (M : ℂ) := by
  have hMr : 0 < (M : ℝ) := by
    exact_mod_cast hM
  have hsqrt :
      (Real.sqrt (M : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 hMr))
  have hM0 : (M : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hM
  field_simp [hsqrt, hM0]
  norm_cast
  nlinarith [Real.sq_sqrt (le_of_lt hMr)]

/--
One source label contributes exactly the corresponding summand of the
standard finite QPE kernel.

This is the key algebraic bridge. It contains no state semantics.
-/
private lemma alg1FractionalLoadCoeff_summand_eq_qpeKernel_summand
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis)
    (z t : Fin (ASize cfg.env.work)) :
    alg1LoadPreCoeff cfg b z *
        alg1IQFTCoeff cfg.env.work z t
      =
    (1 / (ASize cfg.env.work : ℂ)) *
      Complex.exp
        (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
          (((alg1TargetFraction cfg b : ℂ) -
              ((t.1 : ℂ) / (ASize cfg.env.work : ℂ))) *
            (z.1 : ℂ))) := by
  have hM : 0 < ASize cfg.env.work := by
    unfold ASize
    positivity

  have hnorm :
      (1 / Real.sqrt (ASize cfg.env.work : ℝ) : ℂ) *
        (1 / Real.sqrt (ASize cfg.env.work : ℝ) : ℂ)
        =
      1 / (ASize cfg.env.work : ℂ) :=
    qpe_normalizer_sq (ASize cfg.env.work) hM

  rw [
    alg1LoadPreCoeff,
    alg1IQFTCoeff,
    alg1Step1PhaseScalar_eq_qpe_source_phase qs cfg b z,
    star_qftPhase_eq_negative_grid_phase
  ]

  let α : ℂ :=
    ((2 * Real.pi : ℝ) : ℂ) * Complex.I *
      ((alg1TargetFraction cfg b : ℂ) * (z.1 : ℂ))

  let β : ℂ :=
    -(((2 * Real.pi : ℝ) : ℂ) * Complex.I *
      (((z.1 : ℂ) * (t.1 : ℂ)) /
        (ASize cfg.env.work : ℂ)))

  let γ : ℂ :=
    ((2 * Real.pi : ℝ) : ℂ) * Complex.I *
      (((alg1TargetFraction cfg b : ℂ) -
          ((t.1 : ℂ) / (ASize cfg.env.work : ℂ))) *
        (z.1 : ℂ))

  change
    ((1 / Real.sqrt (ASize cfg.env.work : ℝ) : ℂ) *
        Complex.exp α) *
      ((1 / Real.sqrt (ASize cfg.env.work : ℝ) : ℂ) *
        Complex.exp β)
      =
    (1 / (ASize cfg.env.work : ℂ)) * Complex.exp γ

  calc
    ((1 / Real.sqrt (ASize cfg.env.work : ℝ) : ℂ) *
        Complex.exp α) *
      ((1 / Real.sqrt (ASize cfg.env.work : ℝ) : ℂ) *
        Complex.exp β)
        =
      ((1 / Real.sqrt (ASize cfg.env.work : ℝ) : ℂ) *
        (1 / Real.sqrt (ASize cfg.env.work : ℝ) : ℂ)) *
        (Complex.exp α * Complex.exp β) := by
          ring
    _ =
      ((1 / Real.sqrt (ASize cfg.env.work : ℝ) : ℂ) *
        (1 / Real.sqrt (ASize cfg.env.work : ℝ) : ℂ)) *
        Complex.exp (α + β) := by
          rw [← Complex.exp_add]
    _ =
      ((1 / Real.sqrt (ASize cfg.env.work : ℝ) : ℂ) *
        (1 / Real.sqrt (ASize cfg.env.work : ℝ) : ℂ)) *
        Complex.exp γ := by
          congr 2
          dsimp [α, β, γ]
          simp [div_eq_mul_inv]
          ring
    _ =
      (1 / (ASize cfg.env.work : ℂ)) * Complex.exp γ := by
          rw [hnorm]
/--
Rewrite the set of discarded labels into the numerical QPE-window predicate.

This is just unfolding `alg1GoodLabels`; no Fourier estimate occurs here.
-/
lemma alg1_bad_label_set_eq_qpe_bad_set
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis) :
    Finset.univ.filter
      (fun t : Fin (ASize cfg.env.work) =>
        t ∉ alg1GoodLabels cfg b)
      =
    Finset.univ.filter
      (fun t : Fin (ASize cfg.env.work) =>
        ¬
          |alg1TargetFraction cfg b -
              ((t.1 : ℝ) / (ASize cfg.env.work : ℝ))|
            <
          η / (ASize cfg.env.data : ℝ)) := by
  classical
  ext t
  simp [alg1GoodLabels, alg1WorkFraction]

/--
Convert `Algorithm1Precision` into the ratio of the actual QPE grid size
to the data-register capacity.

The nontrivial arithmetic fact is

`ASize work / ASize data = 2^(regSize work - regSize data)`,

where the precision hypothesis itself forces `regSize data ≤ regSize work`.
-/
lemma alg1_precision_grid_ratio
    {η : ℝ}
    (cfg : ModMulConfig η) :
    0 < η ∧
    η < (1 / 2 : ℝ) ∧
    0 < (ASize cfg.env.data : ℝ) ∧
    0 < (ASize cfg.env.work : ℝ) ∧
    (2 + 1 / (2 * η)) ^ 2
      ≤
    (ASize cfg.env.work : ℝ) /
      (ASize cfg.env.data : ℝ) := by
  rcases cfg.env.precision with ⟨hη, hηhalf, hprec⟩

  have hprec:= pow_bound cfg.env.precision

  let n : ℕ := regSize cfg.env.data
  let m : ℕ := regSize cfg.env.work

  have hdata_nat : 0 < ASize cfg.env.data := by
    unfold ASize
    positivity

  have hwork_nat : 0 < ASize cfg.env.work := by
    unfold ASize
    positivity

  have hdata : 0 < (ASize cfg.env.data : ℝ) := by
    exact_mod_cast hdata_nat

  have hwork : 0 < (ASize cfg.env.work : ℝ) := by
    exact_mod_cast hwork_nat

  have hinv_pos : 0 < 1 / (2 * η) := by
    positivity

  have htarget_gt_one :
      1 < (2 + 1 / (2 * η)) ^ 2 := by
    nlinarith [sq_nonneg (1 / (2 * η))]

  have hnm : n ≤ m := by
    by_contra hnot
    have hmn : m < n := Nat.lt_of_not_ge hnot
    have hsub : m - n = 0 :=
      Nat.sub_eq_zero_of_le (Nat.le_of_lt hmn)

    change
      (2 : ℝ) ^ (m - n)
        ≥
      (2 + 1 / (2 * η)) ^ 2 at hprec

    rw [hsub] at hprec
    norm_num at hprec
    simp_all [n, m]

  have hpow :
      (2 : ℝ) ^ m
        =
      (2 : ℝ) ^ n * (2 : ℝ) ^ (m - n) := by
    rw [← pow_add]
    congr
    omega

  have hratio :
      (ASize cfg.env.work : ℝ) /
          (ASize cfg.env.data : ℝ)
        =
      (2 : ℝ) ^ (m - n) := by
    calc
      (ASize cfg.env.work : ℝ) /
          (ASize cfg.env.data : ℝ)
          =
        (2 : ℝ) ^ m / (2 : ℝ) ^ n := by
          simp [ASize, m, n]
      _ =
        ((2 : ℝ) ^ n * (2 : ℝ) ^ (m - n)) /
          (2 : ℝ) ^ n := by
          rw [hpow]
      _ = (2 : ℝ) ^ (m - n) := by
          have hnz : (2 : ℝ) ^ n ≠ 0 := by positivity
          field_simp [hnz]

  refine ⟨hη, hηhalf, hdata, hwork, ?_⟩
  calc
    (2 + 1 / (2 * η)) ^ 2
        ≤
      (2 : ℝ) ^ (m - n) := by
        simpa [m, n] using hprec
    _ =
      (ASize cfg.env.work : ℝ) /
        (ASize cfg.env.data : ℝ) :=
      hratio.symm

lemma qpe_precision_tail_scale
    {η D M : ℝ}
    (hη : 0 < η)
    (hD : 0 < D)
    (hM : 0 < M)
    (hgrid :
      (2 + 1 / (2 * η)) ^ 2 ≤ M / D) :
    D / (M * η) ≤ 4 * η := by
  have h2η : 0 < 2 * η := by positivity

  have hinv : 0 < 1 / (2 * η) := by
    exact one_div_pos.mpr h2η

  have hsmall :
      (1 / (2 * η)) ^ 2
        ≤
      (2 + 1 / (2 * η)) ^ 2 := by
    nlinarith [sq_nonneg (1 / (2 * η))]

  have hrearrange :
      1 / (4 * η ^ 2)
        =
      (1 / (2 * η)) ^ 2 := by
    field_simp [ne_of_gt hη]
    ring

  have hquad :
      1 / (4 * η ^ 2)
        ≤
      (2 + 1 / (2 * η)) ^ 2 := by
    rw [hrearrange]
    exact hsmall

  have hMD :
      1 / (4 * η ^ 2) ≤ M / D :=
    le_trans hquad hgrid

  have hprod :
      (1 / (4 * η ^ 2)) * D ≤ M :=
    (le_div_iff₀ hD).mp hMD

  have hscale_pos : 0 < 4 * η ^ 2 := by
    positivity

  have hmul :
      (4 * η ^ 2) *
          ((1 / (4 * η ^ 2)) * D)
        ≤
      (4 * η ^ 2) * M :=
    mul_le_mul_of_nonneg_left hprod (le_of_lt hscale_pos)

  have hcancel :
      (4 * η ^ 2) *
          ((1 / (4 * η ^ 2)) * D)
        =
      D := by
    field_simp [ne_of_gt hscale_pos]

  have hmain :
      D ≤ 4 * M * η ^ 2 := by
    calc
      D =
          (4 * η ^ 2) *
            ((1 / (4 * η ^ 2)) * D) :=
        hcancel.symm
      _ ≤ (4 * η ^ 2) * M := hmul
      _ = 4 * M * η ^ 2 := by ring

  have hden : 0 < M * η := mul_pos hM hη

  apply (div_le_iff₀ hden).2
  calc
    D ≤ 4 * M * η ^ 2 := hmain
    _ = (4 * η) * (M * η) := by ring

/-! =========================================================
    Pure finite-QPE analysis
========================================================= -/

/--
Distance on the `M`-point QPE circle between a phase `θ ∈ [0,1)` and
the output label `t / M`.

The absolute value around the second term keeps the definition nonnegative
without making any range assumption in the definition itself.
-/
noncomputable def qpeCircularDistance
    (M : ℕ)
    (θ : ℝ)
    (t : Fin M) : ℝ :=
  min
    |θ - ((t.1 : ℝ) / (M : ℝ))|
    |1 - (|θ - ((t.1 : ℝ) / (M : ℝ))|)|


noncomputable def qpeCircularTail
    (M : ℕ)
    (θ δ : ℝ) : Finset (Fin M) :=
  Finset.univ.filter
    (fun t => δ ≤ qpeCircularDistance M θ t)

private lemma qpeKernel_zero_phase_eq_geometric_sum
    (M : ℕ)
    (t : Fin M)
    (_hM : 0 < (M : ℝ)) :
    qpeKernel M 0 t
      =
    (1 / (M : ℂ)) *
      ∑ z : Fin M,
        (Complex.exp
          (-(((2 * Real.pi : ℝ) : ℂ) * Complex.I *
            ((t.1 : ℂ) / (M : ℂ)))) ^ z.1) := by
  unfold qpeKernel
  apply congrArg (fun S : ℂ => (1 / (M : ℂ)) * S)
  apply Finset.sum_congr rfl
  intro z hz
  simp
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

private lemma qpe_zero_phase_root_pow_M
    (M j : ℕ)
    (hM : 0 < (M : ℝ)) :
    (Complex.exp
      (-(((2 * Real.pi : ℝ) : ℂ) * Complex.I *
        ((j : ℂ) / (M : ℂ)))) ^ M)
      =
    1 := by
  have hMnat : 0 < M := by
    exact_mod_cast hM

  have hM0 : (M : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hMnat

  rw [← Complex.exp_nat_mul]

  have harg :
      (M : ℂ) *
          (-(((2 * Real.pi : ℝ) : ℂ) * Complex.I *
            ((j : ℂ) / (M : ℂ))))
        =
      -((j : ℂ) *
        (2 * (Real.pi : ℂ) * Complex.I)) := by
    field_simp [hM0]
    push_cast
    ring

  rw [harg]

  have hbase :
      Complex.exp
        (-(2 * (Real.pi : ℂ) * Complex.I))
        =
      1 := by
    rw [Complex.exp_neg, Complex.exp_two_pi_mul_I]
    simp

  calc
    Complex.exp
        (-((j : ℂ) *
          (2 * (Real.pi : ℂ) * Complex.I)))
        =
      Complex.exp
        ((j : ℂ) *
          (-(2 * (Real.pi : ℂ) * Complex.I))) := by
          congr 1
          ring
    _ =
      (Complex.exp
        (-(2 * (Real.pi : ℂ) * Complex.I))) ^ j := by
          rw [Complex.exp_nat_mul]
    _ = 1 := by simp [hbase]

private lemma qpe_zero_phase_root_ne_one
    (M j : ℕ)
    (hM : 0 < (M : ℝ))
    (hjpos : 0 < j)
    (hjlt : j < M) :
    Complex.exp
      (-(((2 * Real.pi : ℝ) : ℂ) * Complex.I *
        ((j : ℂ) / (M : ℂ))))
      ≠
    1 := by
  intro hroot

  have hMnat : 0 < M := by
    exact_mod_cast hM

  have hM0 : (M : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hMnat

  rcases Complex.exp_eq_one_iff.mp hroot with ⟨k, hk⟩

  have hfactor :
      (-((j : ℝ) / (M : ℝ)) : ℂ) *
          (2 * (Real.pi : ℂ) * Complex.I)
        =
      (k : ℂ) *
          (2 * (Real.pi : ℂ) * Complex.I) := by
    calc
      (-((j : ℝ) / (M : ℝ)) : ℂ) *
          (2 * (Real.pi : ℂ) * Complex.I)
          =
        -(((2 * Real.pi : ℝ) : ℂ) * Complex.I *
          ((j : ℂ) / (M : ℂ))) := by
            field_simp [hM0]
            push_cast
            ring
      _ =
        (k : ℂ) *
          (2 * (Real.pi : ℂ) * Complex.I) := by
            simpa using hk

  have hscalarC :
      (-((j : ℝ) / (M : ℝ)) : ℂ)
        =
      (k : ℂ) := by
    exact
      mul_right_cancel₀
        Complex.two_pi_I_ne_zero
        hfactor

  have hscalar :
      -((j : ℝ) / (M : ℝ))
        =
      (k : ℝ) := by
    simpa using congrArg Complex.re hscalarC

  have hjRpos : 0 < (j : ℝ) := by
    exact_mod_cast hjpos

  have hjRlt : (j : ℝ) < (M : ℝ) := by
    exact_mod_cast hjlt

  have hfrac_pos :
      0 < (j : ℝ) / (M : ℝ) :=
    div_pos hjRpos hM

  have hfrac_lt_one :
      (j : ℝ) / (M : ℝ) < 1 :=
    (div_lt_one hM).2 hjRlt

  have hk_lt_zero : (k : ℝ) < 0 := by
    linarith

  have hminus_one_lt_k : (-1 : ℝ) < (k : ℝ) := by
    linarith

  have hk_lt_zero_int : k < 0 := by
    exact_mod_cast hk_lt_zero

  have hminus_one_lt_k_int : (-1 : ℤ) < k := by
    exact_mod_cast hminus_one_lt_k

  omega

private lemma qpe_zero_phase_geometric_sum_eq_zero
    (M : ℕ)
    (ζ : ℂ)
    (hζM : ζ ^ M = 1)
    (hζne : ζ ≠ 1) :
    ∑ z : Fin M, ζ ^ z.1 = 0 := by
  have hgeom :
      (∑ z : Fin M, ζ ^ z.1) * (ζ - 1)
        =
      ζ ^ M - 1 := by
    simpa only [Fin.sum_univ_eq_sum_range] using
      (geom_sum_mul ζ M)

  have hzero :
      (∑ z : Fin M, ζ ^ z.1) * (ζ - 1) = 0 := by
    simpa [hζM] using hgeom

  exact
    (mul_eq_zero.mp hzero).resolve_right
      (sub_ne_zero.mpr hζne)

private lemma qpeKernel_zero_phase_eq_zero_of_nonzero_label
    (M : ℕ)
    (t : Fin M)
    (hM : 0 < (M : ℝ))
    (ht : t.1 ≠ 0) :
    qpeKernel M 0 t = 0 := by
  let ζ : ℂ :=
    Complex.exp
      (-(((2 * Real.pi : ℝ) : ℂ) * Complex.I *
        ((t.1 : ℂ) / (M : ℂ))))

  have htpos : 0 < t.1 :=
    Nat.pos_of_ne_zero ht

  have hpow : ζ ^ M = 1 := by
    simpa [ζ] using
      qpe_zero_phase_root_pow_M M t.1 hM

  have hne : ζ ≠ 1 := by
    simpa [ζ] using
      qpe_zero_phase_root_ne_one
        M t.1 hM htpos t.isLt

  calc
    qpeKernel M 0 t
        =
      (1 / (M : ℂ)) *
        ∑ z : Fin M, ζ ^ z.1 := by
          simpa [ζ] using
            qpeKernel_zero_phase_eq_geometric_sum M t hM
    _ = 0 := by
      rw [qpe_zero_phase_geometric_sum_eq_zero M ζ hpow hne]
      simp

/--
For zero phase, the finite QPE kernel is exactly the computational-basis
delta distribution: its only nonzero amplitude is label zero.
-/
lemma qpeKernel_zero_phase_bad_mass_zero
    (M : ℕ)
    (δ : ℝ)
    (hM : 0 < (M : ℝ))
    (hδ : 0 < δ) :
    ∑ t ∈ Finset.univ.filter
        (fun t : Fin M =>
          ¬
            |(0 : ℝ) - ((t.1 : ℝ) / (M : ℝ))|
              <
            δ),
      ‖qpeKernel M 0 t‖ ^ 2
      =
    0 := by
  classical
  apply Finset.sum_eq_zero
  intro t ht

  have ht_bad :
      ¬ |(0 : ℝ) - ((t.1 : ℝ) / (M : ℝ))| < δ :=
    (Finset.mem_filter.mp ht).2

  have ht_nonzero : t.1 ≠ 0 := by
    intro ht0
    apply ht_bad
    simp [ht0, hδ]

  rw [qpeKernel_zero_phase_eq_zero_of_nonzero_label M t hM ht_nonzero]
  simp

private noncomputable def qpeOffset
    (M : ℕ) (θ : ℝ) (t : Fin M) : ℝ :=
  θ - ((t.1 : ℝ) / (M : ℝ))

private noncomputable def qpeRoot
    (M : ℕ) (θ : ℝ) (t : Fin M) : ℂ :=
  Complex.exp
    (Complex.I *
      ((2 * Real.pi * qpeOffset M θ t : ℝ) : ℂ))

private lemma qpeKernel_mul_root_chord
    (M : ℕ)
    (θ : ℝ)
    (t : Fin M)
    (hM : 0 < (M : ℝ)) :
    qpeKernel M θ t *
        ((M : ℂ) * (qpeRoot M θ t - 1))
      =
    (qpeRoot M θ t) ^ M - 1 := by
  classical
  let ζ : ℂ := qpeRoot M θ t

  change
    qpeKernel M θ t * ((M : ℂ) * (ζ - 1))
      =
    ζ ^ M - 1

  have hM0R : (M : ℝ) ≠ 0 :=
    ne_of_gt hM

  have hM0 : (M : ℂ) ≠ 0 := by
    exact_mod_cast hM0R

  have hfrac :
      (((t.1 : ℝ) / (M : ℝ) : ℂ))
        =
      (t.1 : ℂ) / (M : ℂ) := by
    norm_cast

  have hterm :
      ∀ z : Fin M,
        Complex.exp
          (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
            (((θ : ℂ) - ((t.1 : ℂ) / (M : ℂ))) * (z.1 : ℂ)))
          =
        ζ ^ z.1 := by
    intro z
    dsimp [ζ, qpeRoot, qpeOffset]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring

  have hkernel :
      qpeKernel M θ t
        =
      (1 / (M : ℂ)) *
        ∑ z : Fin M, ζ ^ z.1 := by
    unfold qpeKernel
    apply congrArg (fun S : ℂ => (1 / (M : ℂ)) * S)
    apply Finset.sum_congr rfl
    intro z hz
    exact hterm z

  have hgeom :
      (∑ z : Fin M, ζ ^ z.1) * (ζ - 1)
        =
      ζ ^ M - 1 := by
    rw [Fin.sum_univ_eq_sum_range]
    exact geom_sum_mul ζ M

  have hcancel :
      (1 / (M : ℂ)) * (M : ℂ) = 1 := by
    field_simp [hM0]

  calc
    qpeKernel M θ t * ((M : ℂ) * (ζ - 1))
        =
      ((1 / (M : ℂ)) * ∑ z : Fin M, ζ ^ z.1) *
        ((M : ℂ) * (ζ - 1)) := by
          rw [hkernel]
    _ =
      ((1 / (M : ℂ)) * (M : ℂ)) *
        ((∑ z : Fin M, ζ ^ z.1) * (ζ - 1)) := by
          ring
    _ =
      (∑ z : Fin M, ζ ^ z.1) * (ζ - 1) := by
          rw [hcancel]
          simp
    _ = ζ ^ M - 1 := hgeom

private lemma qpe_two_mul_min_le_abs_sin
    (u : ℝ)
    (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1) :
    2 * min u (1 - u)
      ≤
    |Real.sin (Real.pi * u)| := by
  by_cases hhalf : u ≤ (1 / 2 : ℝ)
  ·
    have hmin : min u (1 - u) = u := by
      apply min_eq_left
      linarith

    have harg_nonneg : 0 ≤ Real.pi * u :=
      mul_nonneg (le_of_lt Real.pi_pos) hu0

    have harg_le : Real.pi * u ≤ Real.pi / 2 := by
      have hprod :
          0 ≤ Real.pi * ((1 / 2 : ℝ) - u) :=
        mul_nonneg (le_of_lt Real.pi_pos) (by linarith)
      nlinarith

    have hJordan :=
      Real.mul_abs_le_abs_sin
        (x := Real.pi * u)
        (by
          rw [abs_of_nonneg harg_nonneg]
          exact harg_le)

    rw [abs_of_nonneg harg_nonneg] at hJordan

    calc
      2 * min u (1 - u)
          = 2 * u := by rw [hmin]
      _ =
          (2 / Real.pi) * (Real.pi * u) := by
            field_simp [Real.pi_ne_zero]
      _ ≤ |Real.sin (Real.pi * u)| := hJordan

  ·
    have hhalf' : (1 / 2 : ℝ) < u :=
      lt_of_not_ge hhalf

    have hcomp0 : 0 ≤ 1 - u := by
      linarith

    have hcomp_half : 1 - u ≤ (1 / 2 : ℝ) := by
      linarith

    have hmin : min u (1 - u) = 1 - u := by
      apply min_eq_right
      linarith

    have harg_nonneg :
        0 ≤ Real.pi * (1 - u) :=
      mul_nonneg (le_of_lt Real.pi_pos) hcomp0

    have harg_le :
        Real.pi * (1 - u) ≤ Real.pi / 2 := by
      have hprod :
          0 ≤ Real.pi * ((1 / 2 : ℝ) - (1 - u)) :=
        mul_nonneg (le_of_lt Real.pi_pos) (by linarith)
      nlinarith

    have hJordan :=
      Real.mul_abs_le_abs_sin
        (x := Real.pi * (1 - u))
        (by
          rw [abs_of_nonneg harg_nonneg]
          exact harg_le)

    rw [abs_of_nonneg harg_nonneg] at hJordan

    have hsin :
        Real.sin (Real.pi * (1 - u))
          =
        Real.sin (Real.pi * u) := by
      calc
        Real.sin (Real.pi * (1 - u))
            =
          Real.sin (Real.pi - Real.pi * u) := by
            congr 1
            ring
        _ = Real.sin (Real.pi * u) :=
          Real.sin_pi_sub _

    calc
      2 * min u (1 - u)
          = 2 * (1 - u) := by rw [hmin]
      _ =
          (2 / Real.pi) * (Real.pi * (1 - u)) := by
            field_simp [Real.pi_ne_zero]
      _ ≤
          |Real.sin (Real.pi * (1 - u))| := hJordan
      _ =
          |Real.sin (Real.pi * u)| := by
            rw [hsin]

private lemma qpeRoot_chord_lower_bound
    (x : ℝ)
    (hxlo : -1 ≤ x)
    (hxhi : x ≤ 1) :
    4 * min |x| |(1 - |x|)|
      ≤
    ‖Complex.exp
        (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)) - 1‖ := by
  let u : ℝ := |x|

  have hu0 : 0 ≤ u := by
    dsimp [u]
    exact abs_nonneg _

  have hu1 : u ≤ 1 := by
    dsimp [u]
    exact (abs_le).2 ⟨by linarith, hxhi⟩

  have hone : 0 ≤ 1 - |x| := by
    simpa [u] using sub_nonneg.mpr hu1

  have hdist :
      min |x| |(1 - |x|)|
        =
      min u (1 - u) := by
    dsimp [u]
    rw [abs_of_nonneg hone]

  have hsin_abs :
      |Real.sin (Real.pi * u)|
        =
      |Real.sin (Real.pi * x)| := by
    dsimp [u]
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
    ·
      have hx' : x ≤ 0 :=
        le_of_lt (lt_of_not_ge hx)
      rw [abs_of_nonpos hx']
      rw [
        show Real.pi * (-x) = -(Real.pi * x) by ring,
        Real.sin_neg,
        abs_neg
      ]

  have hsin_lower :
      2 * min u (1 - u)
        ≤
      |Real.sin (Real.pi * x)| := by
    calc
      2 * min u (1 - u)
          ≤
        |Real.sin (Real.pi * u)| :=
          qpe_two_mul_min_le_abs_sin u hu0 hu1
      _ =
        |Real.sin (Real.pi * x)| :=
          hsin_abs

  have hchord :
      ‖Complex.exp
          (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)) - 1‖
        =
      2 * |Real.sin (Real.pi * x)| := by
    rw [Complex.norm_exp_I_mul_ofReal_sub_one]
    rw [Real.norm_eq_abs]
    have hangle :
        (2 * Real.pi * x) / 2 = Real.pi * x := by
      ring
    rw [hangle, abs_mul]
    norm_num

  calc
    4 * min |x| |(1 - |x|)|
        =
      2 * (2 * min u (1 - u)) := by
        rw [hdist]
        ring
    _ ≤
      2 * |Real.sin (Real.pi * x)| :=
        mul_le_mul_of_nonneg_left hsin_lower (by norm_num)
    _ =
      ‖Complex.exp
          (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)) - 1‖ :=
        hchord.symm

private lemma norm_natCast_complex
    (M : ℕ) :
    ‖(M : ℂ)‖ = (M : ℝ) := by
  simp

lemma qpeKernel_norm_sq_le_circular_majorant
    (M : ℕ)
    (θ : ℝ)
    (t : Fin M)
    (hM : 0 < (M : ℝ))
    (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1)
    (hpos : 0 < qpeCircularDistance M θ t) :
    ‖qpeKernel M θ t‖ ^ 2
      ≤
    1 /
      (4 *
        (((M : ℝ) * qpeCircularDistance M θ t) ^ 2)) := by
  classical

  let x : ℝ := qpeOffset M θ t
  let ζ : ℂ := qpeRoot M θ t
  let d : ℝ := qpeCircularDistance M θ t
  let A : ℝ := (M : ℝ) * d

  have hMnat : 0 < M := by
    exact_mod_cast hM

  have hM0 : 0 ≤ (M : ℝ) :=
    le_of_lt hM

  have hy0 : 0 ≤ (t.1 : ℝ) / (M : ℝ) := by
    positivity

  have hty : (t.1 : ℝ) < (M : ℝ) := by
    exact_mod_cast t.isLt

  have hy1 : (t.1 : ℝ) / (M : ℝ) < 1 :=
    (div_lt_one hM).2 hty

  have hxlo : -1 ≤ x := by
    dsimp [x, qpeOffset]
    linarith

  have hxhi : x ≤ 1 := by
    dsimp [x, qpeOffset]
    linarith

  have hd : 0 < d := by
    simpa [d] using hpos

  have hA : 0 < A := by
    dsimp [A]
    exact mul_pos hM hd

  have hroot_norm : ‖ζ‖ = 1 := by
    dsimp [ζ, qpeRoot]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      Complex.norm_exp_I_mul_ofReal
        (2 * Real.pi * qpeOffset M θ t)

  have hgeom :
      qpeKernel M θ t *
          ((M : ℂ) * (ζ - 1))
        =
      ζ ^ M - 1 := by
    simpa [ζ] using qpeKernel_mul_root_chord M θ t hM

  have hnumerator :
      ‖ζ ^ M - 1‖ ≤ 2 := by
    calc
      ‖ζ ^ M - 1‖
          ≤ ‖ζ ^ M‖ + ‖(1 : ℂ)‖ :=
        norm_sub_le _ _
      _ = 2 := by
        rw [norm_pow, hroot_norm]
        norm_num

  have hchord :
      4 * d ≤ ‖ζ - 1‖ := by
    simpa [
      ζ,
      d,
      x,
      qpeRoot,
      qpeCircularDistance,
      qpeOffset
    ] using
      qpeRoot_chord_lower_bound x hxlo hxhi

  have hscaled_chord :
      4 * A ≤ ‖(M : ℂ)‖ * ‖ζ - 1‖ := by
    rw [norm_natCast_complex]
    calc
      4 * A
          =
        (M : ℝ) * (4 * d) := by
          dsimp [A]
          ring
      _ ≤ (M : ℝ) * ‖ζ - 1‖ :=
        mul_le_mul_of_nonneg_left hchord hM0

  have hproduct :
      ‖qpeKernel M θ t‖ *
          (‖(M : ℂ)‖ * ‖ζ - 1‖)
        =
      ‖ζ ^ M - 1‖ := by
    have := congrArg norm hgeom
    simpa [norm_mul, mul_assoc] using this

  have hmain :
      ‖qpeKernel M θ t‖ * (4 * A) ≤ 2 := by
    calc
      ‖qpeKernel M θ t‖ * (4 * A)
          ≤
        ‖qpeKernel M θ t‖ *
          (‖(M : ℂ)‖ * ‖ζ - 1‖) :=
        mul_le_mul_of_nonneg_left hscaled_chord (norm_nonneg _)
      _ = ‖ζ ^ M - 1‖ := hproduct
      _ ≤ 2 := hnumerator

  have hhalf :
      ‖qpeKernel M θ t‖ * (2 * A) ≤ 1 := by
    nlinarith

  have hbound :
      ‖qpeKernel M θ t‖ ≤ 1 / (2 * A) := by
    exact (le_div_iff₀ (by positivity : 0 < 2 * A)).2 hhalf

  have hsquare :
      ‖qpeKernel M θ t‖ ^ 2
        ≤
      (1 / (2 * A)) ^ 2 := by
    simpa [pow_two] using
      mul_self_le_mul_self (norm_nonneg _) hbound

  calc
    ‖qpeKernel M θ t‖ ^ 2
        ≤
      (1 / (2 * A)) ^ 2 := hsquare
    _ =
      1 / (4 * A ^ 2) := by
      field_simp [ne_of_gt hA]
      ring
    _ =
      1 /
        (4 *
          (((M : ℝ) * qpeCircularDistance M θ t) ^ 2)) := by
      simp [A, d]

private lemma reciprocal_square_Icc_le
    (L M : ℕ)
    (hL : 2 ≤ L) :
    ∑ n ∈ Finset.Icc L M,
      1 / ((n : ℝ) ^ 2)
      ≤
    1 / (((L - 1 : ℕ) : ℝ)) := by
  classical
  by_cases hLM : L ≤ M
  ·
    let f : ℕ → ℝ :=
      fun n => -(1 / (((n - 1 : ℕ) : ℝ)))

    have hpoint :
        ∀ n ∈ Finset.Icc L M,
          1 / ((n : ℝ) ^ 2)
            ≤
          f (n + 1) - f n := by
      intro n hn
      have hnL : L ≤ n :=
        (Finset.mem_Icc.mp hn).1

      have hn2 : 2 ≤ n :=
        le_trans hL hnL

      have hn1 : 1 ≤ n := by
        omega

      have hnSubPosNat : 0 < n - 1 := by
        omega

      have hnPos : 0 < (n : ℝ) := by
        norm_num
        omega
      have hnSubPos : 0 < (((n - 1 : ℕ) : ℝ)) := by
        exact_mod_cast hnSubPosNat

      dsimp [f]
      simp
      rw [Nat.cast_sub hn1]
      field_simp [ne_of_gt hnPos, ne_of_gt hnSubPos]
      have hn_gt_one : (1 : ℝ) < (n : ℝ) := by
        exact_mod_cast (by omega : 1 < n)
      have hden : 0 < (n : ℝ) - ((1 : ℕ) : ℝ) := by
        norm_num
        omega
      exact
        (le_div_iff₀
          (a := (n : ℝ) + 1)
          (b := (n : ℝ) ^ 2)
          (c := (n : ℝ) - ((1 : ℕ) : ℝ))
          hden).2 (by
        ring_nf
        linarith)


    have hsum :
        ∑ n ∈ Finset.Icc L M,
          1 / ((n : ℝ) ^ 2)
          ≤
        ∑ n ∈ Finset.Icc L M,
          (f (n + 1) - f n) :=
      Finset.sum_le_sum hpoint

    have htel :
        ∑ n ∈ Finset.Icc L M,
          (f (n + 1) - f n)
          =
        f (M + 1) - f L :=
      by
        rw [← Finset.Ico_add_one_right_eq_Icc L M]
        exact Finset.sum_Ico_sub f (Nat.le_succ_of_le hLM)

    have htail :
        f (M + 1) - f L
          ≤
        1 / (((L - 1 : ℕ) : ℝ)) := by
      have hnonneg : 0 ≤ 1 / (M : ℝ) := by
        positivity
      simp only [f, Nat.succ_sub_one]
      linarith

    calc
      ∑ n ∈ Finset.Icc L M,
          1 / ((n : ℝ) ^ 2)
        ≤
      ∑ n ∈ Finset.Icc L M,
          (f (n + 1) - f n) := hsum
      _ = f (M + 1) - f L := htel
      _ ≤ 1 / (((L - 1 : ℕ) : ℝ)) := htail

  ·
    have hML : M < L :=
      Nat.lt_of_not_ge hLM

    have hempty : Finset.Icc L M = ∅ := by
      exact Finset.Icc_eq_empty_of_lt hML

    have hsubPosNat : 0 < L - 1 := by
      omega

    have hsubPos : 0 < (((L - 1 : ℕ) : ℝ)) := by
      exact_mod_cast hsubPosNat

    rw [hempty]
    positivity

private lemma reciprocal_square_floor_tail_le
    (a : ℝ)
    (M : ℕ)
    (ha : 4 ≤ a) :
    2 *
      ∑ n ∈ Finset.Icc ⌊a⌋₊ M,
        1 / ((n : ℝ) ^ 2)
      ≤
    128 / a := by
  let L : ℕ := ⌊a⌋₊

  have haPos : 0 < a := by
    linarith

  have hL4 : 4 ≤ L := by
    apply (Nat.le_floor_iff' (by norm_num : (4 : ℕ) ≠ 0)).2
    simpa [L] using ha

  have hL2 : 2 ≤ L := by
    omega

  have hLsubPosNat : 0 < L - 1 := by
    omega

  have hLsubPos : 0 < (((L - 1 : ℕ) : ℝ)) := by
    exact_mod_cast hLsubPosNat

  have hsum :
      ∑ n ∈ Finset.Icc L M,
        1 / ((n : ℝ) ^ 2)
      ≤
      1 / (((L - 1 : ℕ) : ℝ)) :=
    reciprocal_square_Icc_le L M hL2

  have hfloorLt :
      a < (L : ℝ) + 1 := by
    simpa [L] using (Nat.lt_floor_add_one a)

  have hL4Real : (4 : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast hL4

  have hscale :
      a ≤ 64 * (((L - 1 : ℕ) : ℝ)) := by
    rw [Nat.cast_sub (by omega : 1 ≤ L)]
    have hsmall : (L : ℝ) + 1 ≤ 64 * ((L : ℝ) - 1) := by
      nlinarith
    norm_num at hsmall ⊢
    linarith

  have hfrac :
      2 / (((L - 1 : ℕ) : ℝ))
        ≤
      128 / a := by
    apply (div_le_div_iff₀ hLsubPos haPos).2
    nlinarith [hscale]

  calc
    2 *
        ∑ n ∈ Finset.Icc ⌊a⌋₊ M,
          1 / ((n : ℝ) ^ 2)
      =
    2 *
        ∑ n ∈ Finset.Icc L M,
          1 / ((n : ℝ) ^ 2) := by
        simp [L]
    _ ≤
      2 * (1 / (((L - 1 : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = 2 / (((L - 1 : ℕ) : ℝ)) := by
      ring
    _ ≤ 128 / a := hfrac

private noncomputable def qpeCircularFloorShell
    (M : ℕ)
    (θ δ : ℝ)
    (n : ℕ) : Finset (Fin M) :=
  (qpeCircularTail M θ δ).filter
    (fun t =>
      ⌊(M : ℝ) * qpeCircularDistance M θ t⌋₊ = n)

private lemma qpeCircularDistance_nonneg
    (M : ℕ)
    (θ : ℝ)
    (t : Fin M) :
    0 ≤ qpeCircularDistance M θ t := by
  unfold qpeCircularDistance
  simp_all only [le_inf_iff, abs_nonneg, and_self]

private noncomputable def qpeGridPoint
    (M : ℕ)
    (t : Fin M) : ℝ :=
  (t.1 : ℝ) / (M : ℝ)

private noncomputable def qpeRawDistance
    (M : ℕ)
    (θ : ℝ)
    (t : Fin M) : ℝ :=
  |θ - qpeGridPoint M t|

private noncomputable def qpeShellTag
    (M : ℕ)
    (θ : ℝ)
    (t : Fin M) : Bool × Bool :=
  ( decide (qpeRawDistance M θ t ≤ (1 / 2 : ℝ)),
    decide (qpeGridPoint M t ≤ θ) )

private lemma qpeGridPoint_bounds
    (M : ℕ)
    (t : Fin M)
    (hM : 0 < (M : ℝ)) :
    0 ≤ qpeGridPoint M t ∧
    qpeGridPoint M t < 1 := by
  constructor
  ·
    unfold qpeGridPoint
    positivity
  ·
    unfold qpeGridPoint
    apply (div_lt_one hM).2
    exact_mod_cast t.isLt


private lemma qpeRawDistance_le_one
    (M : ℕ)
    (θ : ℝ)
    (t : Fin M)
    (hM : 0 < (M : ℝ))
    (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) :
    qpeRawDistance M θ t ≤ 1 := by
  rcases qpeGridPoint_bounds M t hM with ⟨hy0, hy1⟩
  unfold qpeRawDistance
  apply (abs_le).2
  constructor <;> linarith

private lemma qpeCircularDistance_direct_left
    (M : ℕ)
    (θ : ℝ)
    (t : Fin M)
    (hM : 0 < (M : ℝ))
    (hθ1 : θ < 1)
    (hdirect : qpeRawDistance M θ t ≤ (1 / 2 : ℝ))
    (hleft : qpeGridPoint M t ≤ θ) :
    qpeCircularDistance M θ t
      =
    θ - qpeGridPoint M t := by
  rcases qpeGridPoint_bounds M t hM with ⟨hy0, _hy1⟩

  have habs :
      |θ - qpeGridPoint M t|
        =
      θ - qpeGridPoint M t :=
    abs_of_nonneg (sub_nonneg.mpr hleft)

  have hle_one :
      θ - qpeGridPoint M t ≤ 1 := by
    linarith

  have houter :
      |1 - (θ - qpeGridPoint M t)|
        =
      1 - (θ - qpeGridPoint M t) :=
    abs_of_nonneg (sub_nonneg.mpr hle_one)

  have hdirect' :
      θ - qpeGridPoint M t ≤ (1 / 2 : ℝ) := by
    simpa [qpeRawDistance, habs] using hdirect

  unfold qpeCircularDistance
  unfold qpeGridPoint at *
  rw [habs, houter]
  exact min_eq_left (by linarith)

private lemma qpeCircularDistance_direct_right
    (M : ℕ)
    (θ : ℝ)
    (t : Fin M)
    (hM : 0 < (M : ℝ))
    (hθ0 : 0 ≤ θ)
    (hdirect : qpeRawDistance M θ t ≤ (1 / 2 : ℝ))
    (hright : θ ≤ qpeGridPoint M t) :
    qpeCircularDistance M θ t
      =
    qpeGridPoint M t - θ := by
  rcases qpeGridPoint_bounds M t hM with ⟨_hy0, hy1⟩

  have habs :
      |θ - qpeGridPoint M t|
        =
      qpeGridPoint M t - θ := by
    rw [abs_of_nonpos (sub_nonpos.mpr hright)]
    ring

  have hle_one :
      qpeGridPoint M t - θ ≤ 1 := by
    linarith

  have houter :
      |1 - (qpeGridPoint M t - θ)|
        =
      1 - (qpeGridPoint M t - θ) :=
    abs_of_nonneg (sub_nonneg.mpr hle_one)

  have hdirect' :
      qpeGridPoint M t - θ ≤ (1 / 2 : ℝ) := by
    simpa [qpeRawDistance, habs] using hdirect

  unfold qpeCircularDistance qpeGridPoint at *
  rw [habs, houter]
  exact min_eq_left (by linarith)

private lemma qpeCircularDistance_wrap_left
    (M : ℕ)
    (θ : ℝ)
    (t : Fin M)
    (hM : 0 < (M : ℝ))
    (hθ1 : θ < 1)
    (hwrap : ¬ qpeRawDistance M θ t ≤ (1 / 2 : ℝ))
    (hleft : qpeGridPoint M t ≤ θ) :
    qpeCircularDistance M θ t
      =
    1 - (θ - qpeGridPoint M t) := by
  rcases qpeGridPoint_bounds M t hM with ⟨hy0, _hy1⟩

  have habs :
      |θ - qpeGridPoint M t|
        =
      θ - qpeGridPoint M t :=
    abs_of_nonneg (sub_nonneg.mpr hleft)

  have hle_one :
      θ - qpeGridPoint M t ≤ 1 := by
    linarith

  have houter :
      |1 - (θ - qpeGridPoint M t)|
        =
      1 - (θ - qpeGridPoint M t) :=
    abs_of_nonneg (sub_nonneg.mpr hle_one)

  have hwrap' :
      ¬ θ - qpeGridPoint M t ≤ (1 / 2 : ℝ) := by
    simpa [qpeRawDistance, habs] using hwrap

  unfold qpeCircularDistance qpeGridPoint at *
  rw [habs, houter]
  exact min_eq_right (by linarith)

private lemma qpeCircularDistance_wrap_right
    (M : ℕ)
    (θ : ℝ)
    (t : Fin M)
    (hM : 0 < (M : ℝ))
    (hθ0 : 0 ≤ θ)
    (hwrap : ¬ qpeRawDistance M θ t ≤ (1 / 2 : ℝ))
    (hright : θ ≤ qpeGridPoint M t) :
    qpeCircularDistance M θ t
      =
    1 - (qpeGridPoint M t - θ) := by
  rcases qpeGridPoint_bounds M t hM with ⟨_hy0, hy1⟩

  have habs :
      |θ - qpeGridPoint M t|
        =
      qpeGridPoint M t - θ := by
    rw [abs_of_nonpos (sub_nonpos.mpr hright)]
    ring

  have hle_one :
      qpeGridPoint M t - θ ≤ 1 := by
    linarith

  have houter :
      |1 - (qpeGridPoint M t - θ)|
        =
      1 - (qpeGridPoint M t - θ) :=
    abs_of_nonneg (sub_nonneg.mpr hle_one)

  have hwrap' :
      ¬ qpeGridPoint M t - θ ≤ (1 / 2 : ℝ) := by
    simpa [qpeRawDistance, habs] using hwrap

  unfold qpeCircularDistance qpeGridPoint at *
  rw [habs, houter]
  exact min_eq_right (by linarith)

private lemma qpe_same_floor_shell_distance_close
    (M : ℕ)
    (θ : ℝ)
    (a b : Fin M)
    (n : ℕ)
    (hM : 0 < (M : ℝ))
    (ha :
      ⌊(M : ℝ) * qpeCircularDistance M θ a⌋₊ = n)
    (hb :
      ⌊(M : ℝ) * qpeCircularDistance M θ b⌋₊ = n) :
    |qpeCircularDistance M θ a - qpeCircularDistance M θ b|
      <
    1 / (M : ℝ) := by
  have ha_nonneg :
      0 ≤ (M : ℝ) * qpeCircularDistance M θ a :=
    mul_nonneg
      (le_of_lt hM)
      (qpeCircularDistance_nonneg M θ a)

  have hb_nonneg :
      0 ≤ (M : ℝ) * qpeCircularDistance M θ b :=
    mul_nonneg
      (le_of_lt hM)
      (qpeCircularDistance_nonneg M θ b)

  have ha_bounds :
      (n : ℝ)
        ≤
      (M : ℝ) * qpeCircularDistance M θ a
        ∧
      (M : ℝ) * qpeCircularDistance M θ a
        <
      (n : ℝ) + 1 := by
    simpa [ha] using
      (Nat.floor_eq_iff ha_nonneg).mp ha

  have hb_bounds :
      (n : ℝ)
        ≤
      (M : ℝ) * qpeCircularDistance M θ b
        ∧
      (M : ℝ) * qpeCircularDistance M θ b
        <
      (n : ℝ) + 1 := by
    simpa [hb] using
      (Nat.floor_eq_iff hb_nonneg).mp hb

  have ha_upper :
      qpeCircularDistance M θ a
        <
      ((n : ℝ) + 1) / (M : ℝ) :=
    (lt_div_iff₀ hM).2 (by
      simpa [mul_comm] using ha_bounds.2)

  have hb_upper :
      qpeCircularDistance M θ b
        <
      ((n : ℝ) + 1) / (M : ℝ) :=
    (lt_div_iff₀ hM).2 (by
      simpa [mul_comm] using hb_bounds.2)

  have ha_lower :
      (n : ℝ) / (M : ℝ)
        ≤
      qpeCircularDistance M θ a :=
    (div_le_iff₀ hM).2 (by
      simpa [mul_comm] using ha_bounds.1)

  have hb_lower :
      (n : ℝ) / (M : ℝ)
        ≤
      qpeCircularDistance M θ b :=
    (div_le_iff₀ hM).2 (by
      simpa [mul_comm] using hb_bounds.1)

  have hwidth :
      ((n : ℝ) + 1) / (M : ℝ) - (n : ℝ) / (M : ℝ)
        =
      1 / (M : ℝ) := by
    field_simp [ne_of_gt hM]
    ring

  apply (abs_lt).2
  constructor
  · nlinarith [ha_upper, hb_lower, hwidth]
  · nlinarith [hb_upper, ha_lower, hwidth]

private lemma qpe_grid_labels_eq_of_fraction_close
    (M : ℕ)
    (a b : Fin M)
    (hM : 0 < (M : ℝ))
    (hclose :
      |qpeGridPoint M a - qpeGridPoint M b|
        <
      1 / (M : ℝ)) :
    a = b := by
  have hfrac :
      |(a.1 : ℝ) - (b.1 : ℝ)| / (M : ℝ)
        <
      1 / (M : ℝ) := by
    calc
      |(a.1 : ℝ) - (b.1 : ℝ)| / (M : ℝ)
          =
        |qpeGridPoint M a - qpeGridPoint M b| := by
          symm
          unfold qpeGridPoint
          calc
            |(a.1 : ℝ) / (M : ℝ) - (b.1 : ℝ) / (M : ℝ)|
                =
              |((a.1 : ℝ) - (b.1 : ℝ)) / (M : ℝ)| := by
                congr 1
                ring
            _ =
              |(a.1 : ℝ) - (b.1 : ℝ)| / (M : ℝ) := by
                rw [abs_div, abs_of_pos hM]
      _ < 1 / (M : ℝ) := hclose

  have hval :
      |(a.1 : ℝ) - (b.1 : ℝ)| < 1 :=
    (div_lt_div_iff_of_pos_right hM).mp hfrac

  have hab : a.1 = b.1 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hab | hba
    ·
      have hcast :
          (a.1 : ℝ) + 1 ≤ (b.1 : ℝ) := by
        exact_mod_cast (Nat.succ_le_of_lt hab)

      have hlarge :
          1 ≤ |(a.1 : ℝ) - (b.1 : ℝ)| := by
        rw [abs_of_nonpos]
        · linarith
        · linarith

      linarith
    ·
      have hcast :
          (b.1 : ℝ) + 1 ≤ (a.1 : ℝ) := by
        exact_mod_cast (Nat.succ_le_of_lt hba)

      have hlarge :
          1 ≤ |(a.1 : ℝ) - (b.1 : ℝ)| := by
        rw [abs_of_nonneg]
        · linarith
        · linarith

      linarith

  exact Fin.ext hab

private lemma qpe_same_floor_shell_same_tag
    (M : ℕ)
    (θ : ℝ)
    (a b : Fin M)
    (n : ℕ)
    (hM : 0 < (M : ℝ))
    (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1)
    (ha :
      ⌊(M : ℝ) * qpeCircularDistance M θ a⌋₊ = n)
    (hb :
      ⌊(M : ℝ) * qpeCircularDistance M θ b⌋₊ = n)
    (htag : qpeShellTag M θ a = qpeShellTag M θ b) :
    a = b := by
  have hclose :
      |qpeCircularDistance M θ a - qpeCircularDistance M θ b|
        <
      1 / (M : ℝ) :=
    qpe_same_floor_shell_distance_close M θ a b n hM ha hb

  have hdirect_tag :
      decide (qpeRawDistance M θ a ≤ (1 / 2 : ℝ))
        =
      decide (qpeRawDistance M θ b ≤ (1 / 2 : ℝ)) := by
    simpa [qpeShellTag] using congrArg Prod.fst htag

  have hside_tag :
      decide (qpeGridPoint M a ≤ θ)
        =
      decide (qpeGridPoint M b ≤ θ) := by
    simpa [qpeShellTag] using congrArg Prod.snd htag

  by_cases ha_direct :
      qpeRawDistance M θ a ≤ (1 / 2 : ℝ)
  ·
    have hb_direct :
        qpeRawDistance M θ b ≤ (1 / 2 : ℝ) := by
      have hbool :
          decide (qpeRawDistance M θ b ≤ (1 / 2 : ℝ)) = true := by
        calc
          decide (qpeRawDistance M θ b ≤ (1 / 2 : ℝ))
              =
          decide (qpeRawDistance M θ a ≤ (1 / 2 : ℝ)) :=
              hdirect_tag.symm
          _ = true := by
            exact decide_eq_true ha_direct
      simpa using hbool

    by_cases ha_left : qpeGridPoint M a ≤ θ
    ·
      have hb_left : qpeGridPoint M b ≤ θ := by
        have hbool :
            decide (qpeGridPoint M b ≤ θ) = true := by
          calc
            decide (qpeGridPoint M b ≤ θ)
                =
              decide (qpeGridPoint M a ≤ θ) :=
                hside_tag.symm
            _ = true := by simp [ha_left]
        simpa using hbool

      have hda :=
        qpeCircularDistance_direct_left
          M θ a hM hθ1 ha_direct ha_left

      have hdb :=
        qpeCircularDistance_direct_left
          M θ b hM hθ1 hb_direct hb_left

      apply qpe_grid_labels_eq_of_fraction_close M a b hM
      calc
        |qpeGridPoint M a - qpeGridPoint M b|
            =
          |qpeCircularDistance M θ a -
            qpeCircularDistance M θ b| := by
              rw [hda, hdb]
              rw [show
                (θ - qpeGridPoint M a) -
                    (θ - qpeGridPoint M b)
                  =
                -(qpeGridPoint M a - qpeGridPoint M b) by ring]
              rw [abs_neg]
        _ < 1 / (M : ℝ) := hclose

    ·
      have ha_right : θ ≤ qpeGridPoint M a :=
        le_of_lt (lt_of_not_ge ha_left)

      have hb_right : θ ≤ qpeGridPoint M b := by
        have hb_not_left : ¬ qpeGridPoint M b ≤ θ := by
          have hbool :
              decide (qpeGridPoint M b ≤ θ) = false := by
            calc
              decide (qpeGridPoint M b ≤ θ)
                  =
                decide (qpeGridPoint M a ≤ θ) :=
                  hside_tag.symm
              _ = false := by simp [ha_left]
          simpa using hbool
        exact le_of_lt (lt_of_not_ge hb_not_left)

      have hda :=
        qpeCircularDistance_direct_right
          M θ a hM hθ0 ha_direct ha_right

      have hdb :=
        qpeCircularDistance_direct_right
          M θ b hM hθ0 hb_direct hb_right

      apply qpe_grid_labels_eq_of_fraction_close M a b hM
      calc
        |qpeGridPoint M a - qpeGridPoint M b|
            =
          |qpeCircularDistance M θ a -
            qpeCircularDistance M θ b| := by
              rw [hda, hdb]
              congr 1
              ring
        _ < 1 / (M : ℝ) := hclose

  ·
    have hb_wrap :
        ¬ qpeRawDistance M θ b ≤ (1 / 2 : ℝ) := by
      intro hb_direct
      have hbool :
          decide (qpeRawDistance M θ a ≤ (1 / 2 : ℝ)) = true := by
        calc
          decide (qpeRawDistance M θ a ≤ (1 / 2 : ℝ))
              =
            decide (qpeRawDistance M θ b ≤ (1 / 2 : ℝ)) :=
              hdirect_tag
          _ = true := by
            exact decide_eq_true hb_direct
      exact ha_direct (by simpa using hbool)

    by_cases ha_left : qpeGridPoint M a ≤ θ
    ·
      have hb_left : qpeGridPoint M b ≤ θ := by
        have hbool :
            decide (qpeGridPoint M b ≤ θ) = true := by
          calc
            decide (qpeGridPoint M b ≤ θ)
                =
              decide (qpeGridPoint M a ≤ θ) :=
                hside_tag.symm
            _ = true := by simp [ha_left]
        simpa using hbool

      have hda :=
        qpeCircularDistance_wrap_left
          M θ a hM hθ1 ha_direct ha_left

      have hdb :=
        qpeCircularDistance_wrap_left
          M θ b hM hθ1 hb_wrap hb_left

      apply qpe_grid_labels_eq_of_fraction_close M a b hM
      calc
        |qpeGridPoint M a - qpeGridPoint M b|
            =
          |qpeCircularDistance M θ a -
            qpeCircularDistance M θ b| := by
              rw [hda, hdb]
              congr 1
              ring
        _ < 1 / (M : ℝ) := hclose

    ·
      have ha_right : θ ≤ qpeGridPoint M a :=
        le_of_lt (lt_of_not_ge ha_left)

      have hb_right : θ ≤ qpeGridPoint M b := by
        have hb_not_left : ¬ qpeGridPoint M b ≤ θ := by
          intro hb_left
          have hbool :
              decide (qpeGridPoint M a ≤ θ) = true := by
            calc
              decide (qpeGridPoint M a ≤ θ)
                  =
                decide (qpeGridPoint M b ≤ θ) :=
                  hside_tag
              _ = true := by simp [hb_left]
          exact ha_left (by simpa using hbool)
        exact le_of_lt (lt_of_not_ge hb_not_left)

      have hda :=
        qpeCircularDistance_wrap_right
          M θ a hM hθ0 ha_direct ha_right

      have hdb :=
        qpeCircularDistance_wrap_right
          M θ b hM hθ0 hb_wrap hb_right

      apply qpe_grid_labels_eq_of_fraction_close M a b hM
      calc
        |qpeGridPoint M a - qpeGridPoint M b|
            =
          |qpeCircularDistance M θ a -
            qpeCircularDistance M θ b| := by
              rw [hda, hdb]
              rw [show
                (1 - (qpeGridPoint M a - θ)) -
                    (1 - (qpeGridPoint M b - θ))
                  =
                -(qpeGridPoint M a - qpeGridPoint M b) by ring]
              rw [abs_neg]
        _ < 1 / (M : ℝ) := hclose
/--
Reindex the tail by the natural floor shell of `M * circularDistance`.

Every tail label lies in one such shell, and its shell index lies between
`⌊M * δ⌋₊` and `M`.
-/
private lemma qpeCircular_tail_floor_shell_partition
    (M : ℕ)
    (θ δ : ℝ)
    (hM : 0 < (M : ℝ))
    (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1)
    (f : Fin M → ℝ) :
    ∑ t ∈ qpeCircularTail M θ δ, f t
      =
    ∑ n ∈ Finset.Icc ⌊(M : ℝ) * δ⌋₊ M,
      ∑ t ∈ qpeCircularFloorShell M θ δ n, f t := by
  classical
  let s : Finset (Fin M) := qpeCircularTail M θ δ
  let I : Finset ℕ := Finset.Icc ⌊(M : ℝ) * δ⌋₊ M
  let shell : Fin M → ℕ :=
    fun t => ⌊(M : ℝ) * qpeCircularDistance M θ t⌋₊

  have hshell_mem :
      ∀ t ∈ s, shell t ∈ I := by
    intro t ht
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩

    · have ht' : t ∈ qpeCircularTail M θ δ := by
        simpa [s] using ht

      have htail :
          δ ≤ qpeCircularDistance M θ t := by
        simpa [qpeCircularTail] using (Finset.mem_filter.mp ht').2

      have hmul :
          (M : ℝ) * δ
            ≤
          (M : ℝ) * qpeCircularDistance M θ t :=
        mul_le_mul_of_nonneg_left htail (le_of_lt hM)

      simpa [shell, I] using Nat.floor_le_floor hmul

    ·
      let y : ℝ := (t.1 : ℝ) / (M : ℝ)

      have hy0 : 0 ≤ y := by
        dsimp [y]
        positivity

      have htM : (t.1 : ℝ) < (M : ℝ) := by
        exact_mod_cast t.isLt

      have hy1 : y < 1 := by
        dsimp [y]
        exact (div_lt_one hM).2 htM

      have hdiff :
          |θ - y| ≤ 1 := by
        apply (abs_le).2
        constructor <;> linarith

      have hdist_le_one :
          qpeCircularDistance M θ t ≤ 1 := by
        unfold qpeCircularDistance
        exact le_trans (min_le_left _ _) hdiff

      have hscaled :
          (M : ℝ) * qpeCircularDistance M θ t
            ≤
          (M : ℝ) := by
        calc
          (M : ℝ) * qpeCircularDistance M θ t
              ≤
            (M : ℝ) * 1 :=
              mul_le_mul_of_nonneg_left hdist_le_one (le_of_lt hM)
          _ = (M : ℝ) := by ring

      simpa [shell, I] using Nat.floor_le_of_le hscaled

  have hpartition :
      ∑ t ∈ s, f t
        =
      ∑ n ∈ I,
        ∑ t ∈ s.filter (fun t => shell t = n), f t := by
    calc
      ∑ t ∈ s, f t
          =
        ∑ t ∈ s,
          ∑ n ∈ I,
            if shell t = n then f t else 0 := by
          apply Finset.sum_congr rfl
          intro t ht
          symm
          simp
          simp[hshell_mem t ht]

      _ =
        ∑ n ∈ I,
          ∑ t ∈ s,
            if shell t = n then f t else 0 := by
          rw [Finset.sum_comm]

      _ =
        ∑ n ∈ I,
          ∑ t ∈ s.filter (fun t => shell t = n), f t := by
          apply Finset.sum_congr rfl
          intro n hn
          change
            (∑ t ∈ s, if shell t = n then f t else 0)
              =
            ∑ t ∈ s.filter (fun t => shell t = n), f t
          exact
            (Finset.sum_filter
              (s := s)
              (fun t => shell t = n)
              f).symm

  simpa [s, I, shell, qpeCircularFloorShell] using hpartition

private lemma qpeCircular_floor_shell_card_le_eight
    (M : ℕ)
    (θ δ : ℝ)
    (n : ℕ)
    (hM : 0 < (M : ℝ))
    (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) :
    (qpeCircularFloorShell M θ δ n).card ≤ 8 := by
  classical

  let S : Finset (Fin M) :=
    qpeCircularFloorShell M θ δ n

  let tag : Fin M → Bool × Bool :=
    qpeShellTag M θ

  have hinj : Set.InjOn tag (↑S : Set (Fin M)) := by
    intro a ha b hb hab

    have ha_floor :
        ⌊(M : ℝ) * qpeCircularDistance M θ a⌋₊ = n := by
      have ha' :
          a ∈ qpeCircularTail M θ δ ∧
          ⌊(M : ℝ) * qpeCircularDistance M θ a⌋₊ = n := by
        simpa [S, qpeCircularFloorShell] using ha
      exact ha'.2

    have hb_floor :
        ⌊(M : ℝ) * qpeCircularDistance M θ b⌋₊ = n := by
      have hb' :
          b ∈ qpeCircularTail M θ δ ∧
          ⌊(M : ℝ) * qpeCircularDistance M θ b⌋₊ = n := by
        simpa [S, qpeCircularFloorShell] using hb
      exact hb'.2

    exact
      qpe_same_floor_shell_same_tag
        M θ a b n hM hθ0 hθ1
        ha_floor hb_floor
        (by simpa [tag] using hab)

  have hmaps :
      Set.MapsTo tag
        (↑S : Set (Fin M))
        (↑(Finset.univ : Finset (Bool × Bool)) : Set (Bool × Bool)) := by
    intro x hx
    simp

  have hcard :
      S.card
        ≤
      (Finset.univ : Finset (Bool × Bool)).card :=
    Finset.card_le_card_of_injOn tag hmaps hinj

  have htag_card :
      (Finset.univ : Finset (Bool × Bool)).card = 4 := by
    decide

  have hfour : S.card ≤ 4 := by
    simpa [htag_card] using hcard

  have height : S.card ≤ 8 := by
    omega

  simpa [S] using height

private lemma qpeCircular_floor_shell_majorant_le
    (M : ℕ)
    (θ δ : ℝ)
    (hM : 0 < (M : ℝ))
    (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1)
    (hcutoff : 4 ≤ (M : ℝ) * δ)
    (n : ℕ)
    (hn : n ∈ Finset.Icc ⌊(M : ℝ) * δ⌋₊ M) :
    ∑ t ∈ qpeCircularFloorShell M θ δ n,
      1 /
        (4 *
          (((M : ℝ) * qpeCircularDistance M θ t) ^ 2))
      ≤
    2 / ((n : ℝ) ^ 2) := by
  classical
  let S : Finset (Fin M) := qpeCircularFloorShell M θ δ n
  let c : ℝ := 1 / (4 * ((n : ℝ) ^ 2))

  have hfloor_four :
      4 ≤ ⌊(M : ℝ) * δ⌋₊ := by
    apply (Nat.le_floor_iff' (by norm_num : (4 : ℕ) ≠ 0)).2
    simpa using hcutoff

  have hn_four : 4 ≤ n :=
    le_trans hfloor_four (Finset.mem_Icc.mp hn).1

  have hn_pos : 0 < n := by
    omega

  have hnR_pos : 0 < (n : ℝ) := by
    exact_mod_cast hn_pos

  have hpoint :
      ∀ t ∈ S,
        1 /
          (4 *
            (((M : ℝ) * qpeCircularDistance M θ t) ^ 2))
          ≤
        c := by
    intro t ht

    have ht' : t ∈ qpeCircularFloorShell M θ δ n := by
      simpa [S] using ht

    have hfilter :
        t ∈
          (qpeCircularTail M θ δ).filter
            (fun t =>
              ⌊(M : ℝ) * qpeCircularDistance M θ t⌋₊ = n) := by
      simpa [qpeCircularFloorShell] using ht'

    have hfloor :
        ⌊(M : ℝ) * qpeCircularDistance M θ t⌋₊ = n :=
      (Finset.mem_filter.mp hfilter).2

    have hscaled_nonneg :
        0 ≤ (M : ℝ) * qpeCircularDistance M θ t :=
      mul_nonneg
        (le_of_lt hM)
        (qpeCircularDistance_nonneg M θ t)

    have hfloor_le :
        (n : ℝ)
          ≤
        (M : ℝ) * qpeCircularDistance M θ t := by
      have h :=
        Nat.floor_le hscaled_nonneg
      simpa [hfloor] using h

    have hscaled_pos :
        0 <
          (M : ℝ) * qpeCircularDistance M θ t :=
      lt_of_lt_of_le hnR_pos hfloor_le

    have hsq :
        (n : ℝ) ^ 2
          ≤
        ((M : ℝ) * qpeCircularDistance M θ t) ^ 2 := by
      nlinarith [sq_nonneg ((M : ℝ) * qpeCircularDistance M θ t - (n : ℝ))]

    have hden :
        4 * ((n : ℝ) ^ 2)
          ≤
        4 * (((M : ℝ) * qpeCircularDistance M θ t) ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (by norm_num)

    have hden_pos :
        0 < 4 * ((n : ℝ) ^ 2) := by
      positivity

    change
      1 /
          (4 *
            (((M : ℝ) * qpeCircularDistance M θ t) ^ 2))
        ≤
      1 / (4 * ((n : ℝ) ^ 2))

    exact one_div_le_one_div_of_le hden_pos hden

  have hsum :
      ∑ t ∈ S,
        1 /
          (4 *
            (((M : ℝ) * qpeCircularDistance M θ t) ^ 2))
        ≤
      ∑ _t ∈ S, c := by
    apply Finset.sum_le_sum
    intro t ht
    exact hpoint t ht

  have hcard : S.card ≤ 8 := by
    simpa [S] using
      qpeCircular_floor_shell_card_le_eight
        M θ δ n hM hθ0 hθ1

  have hcardR : (S.card : ℝ) ≤ 8 := by
    exact_mod_cast hcard

  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity

  have hconst :
      ∑ _t ∈ S, c = (S.card : ℝ) * c := by
    simp [nsmul_eq_mul]

  have hnR_ne : (n : ℝ) ≠ 0 :=
    ne_of_gt hnR_pos

  calc
    ∑ t ∈ qpeCircularFloorShell M θ δ n,
      1 /
        (4 *
          (((M : ℝ) * qpeCircularDistance M θ t) ^ 2))
      =
    ∑ t ∈ S,
      1 /
        (4 *
          (((M : ℝ) * qpeCircularDistance M θ t) ^ 2)) := by
      simp [S]

    _ ≤ ∑ _t ∈ S, c := hsum
    _ = (S.card : ℝ) * c := hconst
    _ ≤ 8 * c :=
      mul_le_mul_of_nonneg_right hcardR hc_nonneg
    _ = 2 / ((n : ℝ) ^ 2) := by
      dsimp [c]
      field_simp [hnR_ne]
      ring

private lemma qpeCircular_tail_majorized_by_floor_shells
    (M : ℕ)
    (θ δ : ℝ)
    (hM : 0 < (M : ℝ))
    (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1)
    (hcutoff : 4 ≤ (M : ℝ) * δ) :
    ∑ t ∈ qpeCircularTail M θ δ,
      1 /
        (4 *
          (((M : ℝ) * qpeCircularDistance M θ t) ^ 2))
      ≤
    2 *
      ∑ n ∈ Finset.Icc ⌊(M : ℝ) * δ⌋₊ M,
        1 / ((n : ℝ) ^ 2) := by
  calc
    ∑ t ∈ qpeCircularTail M θ δ,
      1 /
        (4 *
          (((M : ℝ) * qpeCircularDistance M θ t) ^ 2))
      =
    ∑ n ∈ Finset.Icc ⌊(M : ℝ) * δ⌋₊ M,
      ∑ t ∈ qpeCircularFloorShell M θ δ n,
        1 /
          (4 *
            (((M : ℝ) * qpeCircularDistance M θ t) ^ 2)) := by
      exact
        qpeCircular_tail_floor_shell_partition
          M θ δ hM hθ0 hθ1
          (fun t =>
            1 /
              (4 *
                (((M : ℝ) * qpeCircularDistance M θ t) ^ 2)))

    _ ≤
      ∑ n ∈ Finset.Icc ⌊(M : ℝ) * δ⌋₊ M,
        2 / ((n : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro n hn
      exact
        qpeCircular_floor_shell_majorant_le
          M θ δ hM hθ0 hθ1 hcutoff n hn
    _ =
      2 *
        ∑ n ∈ Finset.Icc ⌊(M : ℝ) * δ⌋₊ M,
          1 / ((n : ℝ) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring

lemma qpeCircular_majorant_tail_le
    (M : ℕ)
    (θ δ : ℝ)
    (hM : 0 < (M : ℝ))
    (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1)
    (hcutoff : 4 ≤ (M : ℝ) * δ) :
    ∑ t ∈ qpeCircularTail M θ δ,
      1 /
        (4 *
          (((M : ℝ) * qpeCircularDistance M θ t) ^ 2))
      ≤
    128 / ((M : ℝ) * δ) := by
  let a : ℝ := (M : ℝ) * δ

  have hshell :
      ∑ t ∈ qpeCircularTail M θ δ,
        1 /
          (4 *
            (((M : ℝ) * qpeCircularDistance M θ t) ^ 2))
        ≤
      2 *
        ∑ n ∈ Finset.Icc ⌊a⌋₊ M,
          1 / ((n : ℝ) ^ 2) := by
    simpa [a] using
      qpeCircular_tail_majorized_by_floor_shells
        M θ δ hM hθ0 hθ1 hcutoff

  have hrecip :
      2 *
        ∑ n ∈ Finset.Icc ⌊a⌋₊ M,
          1 / ((n : ℝ) ^ 2)
        ≤
      128 / a := by
    exact reciprocal_square_floor_tail_le a M (by simpa [a] using hcutoff)

  calc
    ∑ t ∈ qpeCircularTail M θ δ,
      1 /
        (4 *
          (((M : ℝ) * qpeCircularDistance M θ t) ^ 2))
      ≤
    2 *
      ∑ n ∈ Finset.Icc ⌊a⌋₊ M,
        1 / ((n : ℝ) ^ 2) :=
      hshell
    _ ≤ 128 / a :=
      hrecip
    _ = 128 / ((M : ℝ) * δ) := by
      simp [a]
/--
Combine the pointwise sine estimate with the reciprocal-square tail sum.
-/
lemma qpeKernel_circular_tail_le
    (M : ℕ)
    (θ δ : ℝ)
    (hM : 0 < (M : ℝ))
    (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1)
    (hδ : 0 < δ)
    (hcutoff : 4 ≤ (M : ℝ) * δ) :
    ∑ t ∈ qpeCircularTail M θ δ,
      ‖qpeKernel M θ t‖ ^ 2
      ≤
    128 / ((M : ℝ) * δ) := by
  calc
    ∑ t ∈ qpeCircularTail M θ δ,
      ‖qpeKernel M θ t‖ ^ 2
        ≤
    ∑ t ∈ qpeCircularTail M θ δ,
      1 /
        (4 *
          (((M : ℝ) * qpeCircularDistance M θ t) ^ 2)) := by
      apply Finset.sum_le_sum
      intro t ht
      have htail :
          δ ≤ qpeCircularDistance M θ t := by
        simpa [qpeCircularTail] using
          (Finset.mem_filter.mp ht).2
      have hpos :
          0 < qpeCircularDistance M θ t :=
        lt_of_lt_of_le hδ htail
      exact
        qpeKernel_norm_sq_le_circular_majorant
          M θ t hM hθ0 hθ1 hpos

    _ ≤ 128 / ((M : ℝ) * δ) :=
      qpeCircular_majorant_tail_le
        M θ δ hM hθ0 hθ1 hcutoff

private lemma qpe_ordinary_bad_mem_circularTail
    (η : ℝ)
    (N D M r : ℕ)
    (hηhalf : η < (1 / 2 : ℝ))
    (hN : 0 < (N : ℝ))
    (hD : 0 < (D : ℝ))
    (hND : N ≤ D)
    (hrpos : 0 < r)
    (hr : r < N)
    (t : Fin M)
    (ht :
      t ∈ Finset.univ.filter
        (fun t : Fin M =>
          ¬
            |((r : ℝ) / (N : ℝ)) -
                ((t.1 : ℝ) / (M : ℝ))|
              <
            η / (D : ℝ))) :
    t ∈ qpeCircularTail
      M
      ((r : ℝ) / (N : ℝ))
      (η / (D : ℝ)) := by
  classical

  let θ : ℝ := (r : ℝ) / (N : ℝ)
  let y : ℝ := (t.1 : ℝ) / (M : ℝ)
  let δ : ℝ := η / (D : ℝ)

  have hNleD : (N : ℝ) ≤ (D : ℝ) := by
    exact_mod_cast hND

  have hηlt_one : η < 1 := by
    linarith

  have hηN_lt_N :
      η * (N : ℝ) < 1 * (N : ℝ) :=
    mul_lt_mul_of_pos_right hηlt_one hN

  have hηN_lt_D :
      η * (N : ℝ) < (D : ℝ) := by
    calc
      η * (N : ℝ) < 1 * (N : ℝ) := hηN_lt_N
      _ = (N : ℝ) := by ring
      _ ≤ (D : ℝ) := hNleD

  have hδ_lt_invN :
      δ < 1 / (N : ℝ) := by
    dsimp [δ]
    apply (div_lt_div_iff₀ hD hN).2
    simpa using hηN_lt_D

  have hMnat : 0 < M := by
    by_contra hMnot
    have hMzero : M = 0 :=
      Nat.eq_zero_of_not_pos hMnot
    subst M
    exact (Nat.not_lt_zero t.1) t.isLt

  have hM : 0 < (M : ℝ) := by
    exact_mod_cast hMnat

  have hr_real : (r : ℝ) < (N : ℝ) := by
    exact_mod_cast hr

  have hθ0 : 0 ≤ θ := by
    dsimp [θ]
    positivity

  have hθ1 : θ < 1 := by
    dsimp [θ]
    exact (div_lt_one hN).2 hr_real

  have hy0 : 0 ≤ y := by
    dsimp [y]
    positivity

  have hty : (t.1 : ℝ) < (M : ℝ) := by
    exact_mod_cast t.isLt

  have hy1 : y < 1 := by
    dsimp [y]
    exact (div_lt_one hM).2 hty

  have hbad : ¬ |θ - y| < δ := by
    simpa [θ, y, δ] using (Finset.mem_filter.mp ht).2

  have hord : δ ≤ |θ - y| :=
    le_of_not_gt hbad

  have hwrap : δ ≤ |1 - (|θ - y|)| := by
    by_cases hyθ : y ≤ θ
    ·
      have habs :
          |θ - y| = θ - y :=
        abs_of_nonneg (sub_nonneg.mpr hyθ)

      have hrsucc : (r : ℝ) + 1 ≤ (N : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr hr)

      have hrle :
          (r : ℝ) ≤ (N : ℝ) - 1 := by
        linarith

      have hθle :
          θ ≤ 1 - 1 / (N : ℝ) := by
        dsimp [θ]
        calc
          (r : ℝ) / (N : ℝ)
              ≤ ((N : ℝ) - 1) / (N : ℝ) :=
            (div_le_div_iff_of_pos_right hN).2 hrle
          _ = 1 - 1 / (N : ℝ) := by
            field_simp [ne_of_gt hN]


      have houter_nonneg :
          0 ≤ 1 - (θ - y) := by
        linarith

      have hinv_le :
          1 / (N : ℝ) ≤ 1 - (θ - y) := by
        linarith

      calc
        δ ≤ 1 / (N : ℝ) := le_of_lt hδ_lt_invN
        _ ≤ 1 - (θ - y) := hinv_le
        _ = |1 - (|θ - y|)| := by
          rw [habs]
          exact (abs_of_nonneg houter_nonneg).symm

    ·
      have hθy : θ ≤ y :=
        le_of_lt (lt_of_not_ge hyθ)

      have habs :
          |θ - y| = y - θ := by
        rw [abs_of_nonpos (sub_nonpos.mpr hθy)]
        ring

      have h1le_r : (1 : ℝ) ≤ (r : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr hrpos)

      have hinv_le_θ :
          1 / (N : ℝ) ≤ θ := by
        dsimp [θ]
        exact (div_le_div_iff_of_pos_right hN).2 h1le_r

      have houter_nonneg :
          0 ≤ 1 - (y - θ) := by
        linarith

      have hinv_le :
          1 / (N : ℝ) ≤ 1 - (y - θ) := by
        linarith

      calc
        δ ≤ 1 / (N : ℝ) := le_of_lt hδ_lt_invN
        _ ≤ 1 - (y - θ) := hinv_le
        _ = |1 - (|θ - y|)| := by
          rw [habs]
          exact (abs_of_nonneg houter_nonneg).symm

  simpa [
    qpeCircularTail,
    qpeCircularDistance,
    θ,
    y,
    δ
  ] using le_min hord hwrap

lemma qpe_ordinary_bad_mass_le_circular_tail
    (η : ℝ)
    (N D M r : ℕ)
    (hηhalf : η < (1 / 2 : ℝ))
    (hN : 0 < (N : ℝ))
    (hD : 0 < (D : ℝ))
    (hND : N ≤ D)
    (hrpos : 0 < r)
    (hr : r < N) :
    ∑ t ∈ Finset.univ.filter
        (fun t : Fin M =>
          ¬
            |((r : ℝ) / (N : ℝ)) -
                ((t.1 : ℝ) / (M : ℝ))|
              <
            η / (D : ℝ)),
      ‖qpeKernel M ((r : ℝ) / (N : ℝ)) t‖ ^ 2
      ≤
    ∑ t ∈ qpeCircularTail
        M
        ((r : ℝ) / (N : ℝ))
        (η / (D : ℝ)),
      ‖qpeKernel M ((r : ℝ) / (N : ℝ)) t‖ ^ 2 := by
  classical
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro t ht
    exact
      qpe_ordinary_bad_mem_circularTail
        η N D M r
        hηhalf hN hD hND hrpos hr t ht
  · intro t _htTail _htNotSmall
    exact sq_nonneg _

lemma qpe_grid_cutoff_ge_four
    (η : ℝ)
    (D M : ℕ)
    (hη : 0 < η)
    (hD : 0 < (D : ℝ))
    (hgrid :
      (2 + 1 / (2 * η)) ^ 2
        ≤
      (M : ℝ) / (D : ℝ)) :
    4 ≤ (M : ℝ) * (η / (D : ℝ)) := by
  let B : ℝ := (2 + 1 / (2 * η)) ^ 2

  have hbase : 4 ≤ η * B := by
    have hden : 0 < 4 * η := by positivity
    have hsq : 0 ≤ (4 * η - 1) ^ 2 :=
      sq_nonneg (4 * η - 1)

    have hid :
        η * B - 4
          =
        (4 * η - 1) ^ 2 / (4 * η) := by
      dsimp [B]
      field_simp [ne_of_gt hη]
      ring

    have hnonneg :
        0 ≤ (4 * η - 1) ^ 2 / (4 * η) :=
      div_nonneg hsq (le_of_lt hden)

    nlinarith [hid]

  have hgrid' :
      B ≤ (M : ℝ) / (D : ℝ) := by
    simpa [B] using hgrid

  have hMD :
      B * (D : ℝ) ≤ (M : ℝ) :=
    (le_div_iff₀ hD).mp hgrid'

  have hleft :
      4 * (D : ℝ) ≤ (η * B) * (D : ℝ) :=
    mul_le_mul_of_nonneg_right hbase (le_of_lt hD)

  have hright :
      (η * B) * (D : ℝ) ≤ (M : ℝ) * η := by
    calc
      (η * B) * (D : ℝ)
          =
        (B * (D : ℝ)) * η := by ring
      _ ≤ (M : ℝ) * η :=
        mul_le_mul_of_nonneg_right hMD (le_of_lt hη)

  have hmain :
      4 * (D : ℝ) ≤ (M : ℝ) * η :=
    hleft.trans hright

  calc
    4 ≤ ((M : ℝ) * η) / (D : ℝ) :=
      (le_div_iff₀ hD).2 hmain
    _ = (M : ℝ) * (η / (D : ℝ)) := by
      field_simp [ne_of_gt hD]

/--
The Algorithm-1 cutoff is below one half of the unit circle.
-/
lemma qpe_precision_cutoff_lt_half
    (η : ℝ)
    (D : ℕ)
    (hη : 0 < η)
    (hηhalf : η < (1 / 2 : ℝ))
    (hD : 0 < D) :
    η / (D : ℝ) < (1 / 2 : ℝ) := by
  have hDreal : 0 < (D : ℝ) := by
    exact_mod_cast hD

  have hDone : (1 : ℝ) ≤ (D : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hD)

  have hmul : η ≤ η * (D : ℝ) := by
    simpa using
      (mul_le_mul_of_nonneg_left hDone (le_of_lt hη))

  have hdiv : η / (D : ℝ) ≤ η :=
    (div_le_iff₀ hDreal).2 hmul

  exact lt_of_le_of_lt hdiv hηhalf

/--
Pure field normalization of the circular-tail denominator.
-/
lemma qpe_tail_scale_rewrite
    (η : ℝ)
    (D M : ℕ)
    (hη : 0 < η)
    (hD : 0 < (D : ℝ))
    (hM : 0 < (M : ℝ)) :
    128 / ((M : ℝ) * (η / (D : ℝ)))
      =
    128 * ((D : ℝ) / ((M : ℝ) * η)) := by
  field_simp [ne_of_gt hη, ne_of_gt hD, ne_of_gt hM]

/--
The actual analytic QPE estimate.
-/
lemma qpeKernel_bad_mass_le_grid_ratio
    (η : ℝ)
    (N D M r : ℕ)
    (hη : 0 < η)
    (hηhalf : η < (1 / 2 : ℝ))
    (hN : 0 < (N : ℝ))
    (hD : 0 < (D : ℝ))
    (hM : 0 < (M : ℝ))
    (hND : N ≤ D)
    (hr : r < N)
    (hgrid :
      (2 + 1 / (2 * η)) ^ 2
        ≤
      (M : ℝ) / (D : ℝ)) :
    ∑ t ∈ Finset.univ.filter
        (fun t : Fin M =>
          ¬
            |((r : ℝ) / (N : ℝ)) -
                ((t.1 : ℝ) / (M : ℝ))|
              <
            η / (D : ℝ)),
      ‖qpeKernel M ((r : ℝ) / (N : ℝ)) t‖ ^ 2
      ≤
    128 * ((D : ℝ) / ((M : ℝ) * η)) := by
  classical

  have hδ :
      0 < η / (D : ℝ) :=
    div_pos hη hD

  have hDnat : 0 < D := by
    exact_mod_cast hD

  have hδhalf :
      η / (D : ℝ) < (1 / 2 : ℝ) :=
    qpe_precision_cutoff_lt_half η D hη hηhalf hDnat

  have hcutoff :
      4 ≤ (M : ℝ) * (η / (D : ℝ)) :=
    qpe_grid_cutoff_ge_four η D M hη hD hgrid

  by_cases hrzero : r = 0
  · subst r

    have hzero :
        ∑ t ∈ Finset.univ.filter
            (fun t : Fin M =>
              ¬
                |(0 : ℝ) - ((t.1 : ℝ) / (M : ℝ))|
                  <
                η / (D : ℝ)),
          ‖qpeKernel M 0 t‖ ^ 2
          =
        0 :=
      qpeKernel_zero_phase_bad_mass_zero
        M
        (η / (D : ℝ))
        hM
        hδ

    norm_cast
    calc
      ∑ t ∈ Finset.univ.filter
          (fun t : Fin M =>
            ¬
              |((0 : ℝ) / (N : ℝ)) -
                  ((t.1 : ℝ) / (M : ℝ))|
                <
              η / (D : ℝ)),
        ‖qpeKernel M ((0 : ℝ) / (N : ℝ)) t‖ ^ 2
          =
        0 := by
          simpa using hzero
      _ ≤ 128 * ((D : ℝ) / ((M : ℝ) * η)) := by
          positivity

  ·
    have hrpos : 0 < r :=
      Nat.pos_of_ne_zero hrzero

    have hr_real :
        (r : ℝ) < (N : ℝ) := by
      exact_mod_cast hr

    have hθ0 :
        0 ≤ (r : ℝ) / (N : ℝ) :=
      div_nonneg (by positivity) (le_of_lt hN)

    have hθ1 :
        (r : ℝ) / (N : ℝ) < 1 :=
      (div_lt_one hN).2 hr_real

    calc
      ∑ t ∈ Finset.univ.filter
          (fun t : Fin M =>
            ¬
              |((r : ℝ) / (N : ℝ)) -
                  ((t.1 : ℝ) / (M : ℝ))|
                <
              η / (D : ℝ)),
        ‖qpeKernel M ((r : ℝ) / (N : ℝ)) t‖ ^ 2
          ≤
        ∑ t ∈ qpeCircularTail
            M
            ((r : ℝ) / (N : ℝ))
            (η / (D : ℝ)),
          ‖qpeKernel M ((r : ℝ) / (N : ℝ)) t‖ ^ 2 :=
        qpe_ordinary_bad_mass_le_circular_tail
          η N D M r hηhalf hN hD hND hrpos hr

      _ ≤
        128 / ((M : ℝ) * (η / (D : ℝ))) :=
        qpeKernel_circular_tail_le
          M
          ((r : ℝ) / (N : ℝ))
          (η / (D : ℝ))
          hM hθ0 hθ1 hδ hcutoff

      _ =
        128 * ((D : ℝ) / ((M : ℝ) * η)) :=
        qpe_tail_scale_rewrite η D M hη hD hM

lemma alg1FractionalLoadCoeff_eq_qpeKernel
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η)
    (b : qs.Basis)
    (t : Fin (ASize cfg.env.work)) :
    alg1FractionalLoadCoeff cfg b t
      =
    qpeKernel
      (ASize cfg.env.work)
      (alg1TargetFraction cfg b)
      t := by
  classical
  unfold alg1FractionalLoadCoeff qpeKernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  exact
    alg1FractionalLoadCoeff_summand_eq_qpeKernel_summand
      qs cfg b z t
/--
Uniform basis-input QPE-tail estimate.
-/
lemma alg1_qpe_tail_basis_uniform
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [Spec]
    [GateSemanticsFacts qs] :
    ∃ Ctail : ℝ, 0 ≤ Ctail ∧
      ∀ (η : ℝ) (cfg : ModMulConfig η) (b : qs.Basis),
        GoodModMulBasisInput
          qs cfg.env.N cfg.env.data cfg.env.work cfg.flag b →
        alg1QpeBadMass qs cfg b ≤ Ctail * η := by
  classical
  refine ⟨512, by norm_num, ?_⟩
  intro η cfg b hb

  rcases alg1_precision_grid_ratio cfg with
    ⟨hη, hηhalf, hD, hM, hgrid⟩

  have hNnat : 0 < cfg.env.N :=
    Nat.lt_trans Nat.zero_lt_one cfg.env.modulus_gt_one

  have hN : 0 < (cfg.env.N : ℝ) := by
    exact_mod_cast hNnat

  have hr : alg1TargetResidue cfg b < cfg.env.N :=
    alg1TargetResidue_lt_N cfg b

  have hkernel :
      ∑ t ∈ Finset.univ.filter
          (fun t : Fin (ASize cfg.env.work) =>
            ¬
              |((alg1TargetResidue cfg b : ℝ) / (cfg.env.N : ℝ)) -
                  ((t.1 : ℝ) / (ASize cfg.env.work : ℝ))|
                <
              η / (ASize cfg.env.data : ℝ)),
        ‖qpeKernel
            (ASize cfg.env.work)
            ((alg1TargetResidue cfg b : ℝ) / (cfg.env.N : ℝ))
            t‖ ^ 2
        ≤
      128 *
        ((ASize cfg.env.data : ℝ) /
          ((ASize cfg.env.work : ℝ) * η)) := by
    exact
      qpeKernel_bad_mass_le_grid_ratio
        η
        cfg.env.N
        (ASize cfg.env.data)
        (ASize cfg.env.work)
        (alg1TargetResidue cfg b)
        hη
        hηhalf
        hN
        hD
        hM
        cfg.env.data_capacity
        hr
        hgrid

  have hscale :
      (ASize cfg.env.data : ℝ) /
          ((ASize cfg.env.work : ℝ) * η)
        ≤
      4 * η :=
    qpe_precision_tail_scale hη hD hM hgrid

  unfold alg1QpeBadMass
  rw [alg1_bad_label_set_eq_qpe_bad_set qs cfg b]

  calc
    ∑ t ∈ Finset.univ.filter
        (fun t : Fin (ASize cfg.env.work) =>
          ¬
            |alg1TargetFraction cfg b -
                ((t.1 : ℝ) / (ASize cfg.env.work : ℝ))|
              <
            η / (ASize cfg.env.data : ℝ)),
      ‖alg1PhaseCoeff qs cfg b t‖ ^ 2
        =
    ∑ t ∈ Finset.univ.filter
        (fun t : Fin (ASize cfg.env.work) =>
          ¬
            |alg1TargetFraction cfg b -
                ((t.1 : ℝ) / (ASize cfg.env.work : ℝ))|
              <
            η / (ASize cfg.env.data : ℝ)),
      ‖qpeKernel
          (ASize cfg.env.work)
          (alg1TargetFraction cfg b)
          t‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [
        alg1PhaseCoeff_eq_fractionalLoadCoeff qs cfg b hb t,
        alg1FractionalLoadCoeff_eq_qpeKernel qs cfg b t
      ]

    _ ≤
      128 *
        ((ASize cfg.env.data : ℝ) /
          ((ASize cfg.env.work : ℝ) * η)) := by
      simpa [alg1TargetFraction] using hkernel

    _ ≤ 512 * η := by
      calc
        128 *
            ((ASize cfg.env.data : ℝ) /
              ((ASize cfg.env.work : ℝ) * η))
          ≤
        128 * (4 * η) :=
          mul_le_mul_of_nonneg_left hscale (by norm_num)
        _ = 512 * η := by ring
