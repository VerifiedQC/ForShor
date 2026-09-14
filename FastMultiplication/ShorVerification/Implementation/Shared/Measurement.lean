import FastMultiplication.ShorVerification.Framework.Quantum.Measurement
import FastMultiplication.ShorVerification.Framework.Semantics.GateSemantics

/-!
# Measurement and Success Probabilities

`MeasureClass` packages the Born-rule projectors used to talk about measuring
a register. The lemmas in this file turn those projector axioms into the
probability estimates needed by circuit-correctness proofs:

* orthogonal projector sums have the expected norm square;
* measurement mass outside a register range is zero;
* measurement distributions are Lipschitz in state distance.
-/

namespace Shor

/-! =========================================================
    Section 2: Measurement and success probabilities

    `MeasureClass` packages the Born-rule projectors used to talk about
    measuring a register.  The lemmas in this section turn those projector
    axioms into the probability estimates needed later:

    * orthogonal projector sums have the expected norm square;
    * measurement mass outside a register range is zero;
    * measurement distributions are Lipschitz in state distance.
========================================================= -/

variable {qs : QSemantics}
variable [RegEncoding qs.Basis]
variable [MeasureClass qs]

/-! ## Projector Hilbert-space estimates -/

omit [RegEncoding QSemantics.Basis] [MeasureClass qs] in
/-- Difference of squared norms, expressed in a form suitable for Cauchy-Schwarz. -/
lemma abs_norm_sq_sub_norm_sq_le
    (u v : qs.State) :
    |‖u‖ ^ 2 - ‖v‖ ^ 2|
      ≤ ‖u + v‖ * ‖u - v‖ := by
  have hre_symm :
    Complex.re (inner ℂ u v)
      = Complex.re (inner ℂ v u) := by
    calc
      Complex.re (inner ℂ u v)
          =
        Complex.re ((starRingEnd ℂ) (inner ℂ v u)) := by
            exact congrArg Complex.re
              (inner_conj_symm (𝕜 := ℂ) u v).symm
      _ = Complex.re (inner ℂ v u) := by
            simpa using RCLike.conj_re (inner ℂ v u)

  have hident :
      ‖u‖ ^ 2 - ‖v‖ ^ 2
        = Complex.re (inner ℂ (u + v) (u - v)) := by
    calc
      ‖u‖ ^ 2 - ‖v‖ ^ 2
          =
        Complex.re (inner ℂ u u)
          - Complex.re (inner ℂ v v) := by
            simp [norm_sq_eq_re_inner (𝕜 := ℂ) u]
            rw [norm_sq_eq_re_inner (𝕜 := ℂ) v]
            simp
      _ =
        Complex.re (inner ℂ (u + v) (u - v)) := by
            simp only [inner_add_left, inner_sub_right,
              Complex.add_re, Complex.sub_re]
            rw [← hre_symm]
            ring

  calc
    |‖u‖ ^ 2 - ‖v‖ ^ 2|
        = |Complex.re (inner ℂ (u + v) (u - v))| := by
            rw [hident]
    _ ≤ ‖inner ℂ (u + v) (u - v)‖ := by
          exact Complex.abs_re_le_norm _
    _ ≤ ‖u + v‖ * ‖u - v‖ := by
          exact norm_inner_le_norm _ _

/-- Applying the same measurement projector to two states makes their squared
norm difference controlled by the projected sum and difference. -/
lemma measProj_sqdiff_le
    (r : Reg) (o : ℕ) (ψ φ : qs.State) :
    |‖MeasureClass.measProj (qs := qs) r o ψ‖ ^ 2
      - ‖MeasureClass.measProj (qs := qs) r o φ‖ ^ 2|
      ≤
    ‖MeasureClass.measProj (qs := qs) r o (ψ + φ)‖
      * ‖MeasureClass.measProj (qs := qs) r o (ψ - φ)‖ := by
  simpa using
    (abs_norm_sq_sub_norm_sq_le
      (qs := qs)
      (MeasureClass.measProj (qs := qs) r o ψ)
      (MeasureClass.measProj (qs := qs) r o φ))

/-- Different measurement outcomes have orthogonal image vectors. -/
lemma measProj_inner_eq_zero_of_ne
    (r : Reg) (o o' : ℕ) (ψ : qs.State)
    (hneq : o ≠ o') :
    inner ℂ
      (MeasureClass.measProj (qs := qs) r o ψ)
      (MeasureClass.measProj (qs := qs) r o' ψ) = 0 := by
  calc
    inner ℂ
        (MeasureClass.measProj (qs := qs) r o ψ)
        (MeasureClass.measProj (qs := qs) r o' ψ)
      =
    inner ℂ ψ
      (MeasureClass.measProj (qs := qs) r o
        (MeasureClass.measProj (qs := qs) r o' ψ)) := by
          simpa using
            (MeasureClass.measProj_selfAdjoint
              (qs := qs) r o ψ
              (MeasureClass.measProj (qs := qs) r o' ψ))
    _ = 0 := by
          rw [MeasureClass.measProj_orthogonal
            (qs := qs) r o o' ψ hneq]
          simp

omit [RegEncoding QSemantics.Basis] [MeasureClass qs] in
/-- Pythagoras for a finite sum of pairwise orthogonal vectors. -/
lemma norm_sq_sum_eq_sum_norm_sq_of_orthogonal
    {ι : Type}
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
      intro horth
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
            simp_all only [ne_eq, Finset.mem_insert, or_true, not_false_eq_true, implies_true,
              forall_eq_or_imp, not_true_eq_false, inner_self_eq_norm_sq_to_K, Complex.coe_algebraMap,
              OfNat.ofNat_ne_zero, pow_eq_zero_iff, Complex.ofReal_eq_zero, norm_eq_zero, IsEmpty.forall_iff,
              true_and, and_true, Complex.zero_re, mul_zero, add_zero]
        _ =
          ‖f a‖ ^ 2 + ∑ i ∈ s, ‖f i‖ ^ 2 := by
            rw [hih]
        _ =
          ∑ i ∈ insert a s, ‖f i‖ ^ 2 := by
            rw [Finset.sum_insert ha]

/-- The measurement projectors decompose the state norm over all valid outcomes. -/
lemma measProj_full_norm_sq_sum
    (r : Reg) (ψ : qs.State) :
    (∑ o : Fin (2 ^ regSize r),
      ‖MeasureClass.measProj (qs := qs) r o.1 ψ‖ ^ 2)
      =
    ‖ψ‖ ^ 2 := by
  classical

  have horth :
      ∀ i ∈ (Finset.univ : Finset (Fin (2 ^ regSize r))),
      ∀ j ∈ (Finset.univ : Finset (Fin (2 ^ regSize r))),
      i ≠ j →
      inner ℂ
        (MeasureClass.measProj (qs := qs) r i.1 ψ)
        (MeasureClass.measProj (qs := qs) r j.1 ψ) = 0 := by
    intro i hi j hj hij
    have hij_nat : i.1 ≠ j.1 := by
      intro h
      apply hij
      exact Fin.ext h
    simpa using
      (measProj_inner_eq_zero_of_ne
        (qs := qs) r i.1 j.1 ψ hij_nat)

  have hsum :=
    norm_sq_sum_eq_sum_norm_sq_of_orthogonal
      (qs := qs)
      (s := (Finset.univ : Finset (Fin (2 ^ regSize r))))
      (f := fun o =>
        MeasureClass.measProj (qs := qs) r o.1 ψ)
      horth

  calc
    (∑ o : Fin (2 ^ regSize r),
      ‖MeasureClass.measProj (qs := qs) r o.1 ψ‖ ^ 2)
        =
      ‖∑ o : Fin (2 ^ regSize r),
        MeasureClass.measProj (qs := qs) r o.1 ψ‖ ^ 2 := by
          simpa using hsum.symm
    _ = ‖ψ‖ ^ 2 := by
          rw [MeasureClass.measProj_complete (qs := qs) r ψ]

/-- Any finite subset of measurement outcomes has total projected mass at most
the full state norm.  Outcomes outside the register range contribute zero. -/
lemma measProj_norm_sq_sum_le
    (r : Reg) (s : Finset ℕ) (ψ : qs.State) :
    (∑ o ∈ s,
      ‖MeasureClass.measProj (qs := qs) r o ψ‖ ^ 2)
      ≤ ‖ψ‖ ^ 2 := by
  classical

  let n : ℕ := 2 ^ regSize r

  have hcut :
      (∑ o ∈ s ∩ Finset.range n,
        ‖MeasureClass.measProj (qs := qs) r o ψ‖ ^ 2)
        =
      ∑ o ∈ s,
        ‖MeasureClass.measProj (qs := qs) r o ψ‖ ^ 2 := by
    refine Finset.sum_subset ?_ ?_
    · intro o ho
      exact (Finset.mem_inter.mp ho).1
    · intro o hos hnotinter
      have hnotrange : o ∉ Finset.range n := by
        intro horange
        exact hnotinter (Finset.mem_inter.mpr ⟨hos, horange⟩)

      have hge : n ≤ o := by
        apply Nat.le_of_not_gt
        intro hlt
        exact hnotrange (Finset.mem_range.mpr hlt)

      have hzero :
          MeasureClass.measProj (qs := qs) r o ψ = 0 := by
        exact MeasureClass.measProj_zero_outOfRange
          (qs := qs) r o ψ (by simpa [n] using hge)

      simp [hzero]

  have hsub : s ∩ Finset.range n ⊆ Finset.range n := by
    intro o ho
    exact (Finset.mem_inter.mp ho).2

  have hle :
      (∑ o ∈ s ∩ Finset.range n,
        ‖MeasureClass.measProj (qs := qs) r o ψ‖ ^ 2)
        ≤
      ∑ o ∈ Finset.range n,
        ‖MeasureClass.measProj (qs := qs) r o ψ‖ ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro o ho hnot
    exact sq_nonneg _

  have hfull :
      (∑ o ∈ Finset.range n,
        ‖MeasureClass.measProj (qs := qs) r o ψ‖ ^ 2)
        =
      ‖ψ‖ ^ 2 := by
    have hfull_fin := measProj_full_norm_sq_sum (qs := qs) r ψ
    rw [← hfull_fin]
    exact (Fin.sum_univ_eq_sum_range
      (fun o : ℕ =>
        ‖MeasureClass.measProj (qs := qs) r o ψ‖ ^ 2) n).symm

  calc
    (∑ o ∈ s,
      ‖MeasureClass.measProj (qs := qs) r o ψ‖ ^ 2)
        =
      (∑ o ∈ s ∩ Finset.range n,
        ‖MeasureClass.measProj (qs := qs) r o ψ‖ ^ 2) := by
          exact hcut.symm
    _ ≤
      ∑ o ∈ Finset.range n,
        ‖MeasureClass.measProj (qs := qs) r o ψ‖ ^ 2 := hle
    _ = ‖ψ‖ ^ 2 := hfull

/-- The same mass bound for a `Fin Q` prefix of outcomes. -/
lemma measProj_norm_sq_prefix_le
    (r : Reg) (Q : ℕ) (ψ : qs.State) :
    (∑ o : Fin Q,
      ‖MeasureClass.measProj (qs := qs) r o.1 ψ‖ ^ 2)
      ≤ ‖ψ‖ ^ 2 := by
  classical
  rw [Fin.sum_univ_eq_sum_range
    (fun o : ℕ =>
      ‖MeasureClass.measProj (qs := qs) r o ψ‖ ^ 2) Q]
  exact
    measProj_norm_sq_sum_le
      (qs := qs)
      r
      (Finset.range Q)
      ψ

/-- Cauchy-Schwarz for the sequence of projected norms over a finite prefix. -/
lemma measProj_cauchy_prefix
    (r : Reg) (Q : ℕ) (u v : qs.State) :
    (∑ o : Fin Q,
      ‖MeasureClass.measProj (qs := qs) r o.1 u‖
        * ‖MeasureClass.measProj (qs := qs) r o.1 v‖)
      ≤ ‖u‖ * ‖v‖ := by
  have hA :
      (∑ o : Fin Q,
        ‖MeasureClass.measProj (qs := qs) r o.1 u‖ ^ 2)
        ≤ ‖u‖ ^ 2 :=
    measProj_norm_sq_prefix_le (qs := qs) r Q u

  have hB :
      (∑ o : Fin Q,
        ‖MeasureClass.measProj (qs := qs) r o.1 v‖ ^ 2)
        ≤ ‖v‖ ^ 2 :=
    measProj_norm_sq_prefix_le (qs := qs) r Q v

  have hcs :
      (∑ o : Fin Q,
        ‖MeasureClass.measProj (qs := qs) r o.1 u‖
          * ‖MeasureClass.measProj (qs := qs) r o.1 v‖) ^ 2
        ≤
      (∑ o : Fin Q,
        ‖MeasureClass.measProj (qs := qs) r o.1 u‖ ^ 2)
        *
      (∑ o : Fin Q,
        ‖MeasureClass.measProj (qs := qs) r o.1 v‖ ^ 2) := by
    let fu : ℕ → ℝ := fun o =>
      ‖MeasureClass.measProj (qs := qs) r o u‖
    let fv : ℕ → ℝ := fun o =>
      ‖MeasureClass.measProj (qs := qs) r o v‖
    have hrange :
        (∑ o ∈ Finset.range Q, fu o * fv o) ^ 2
          ≤
        (∑ o ∈ Finset.range Q, fu o ^ 2)
          *
        (∑ o ∈ Finset.range Q, fv o ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq (Finset.range Q) fu fv
    rw [Fin.sum_univ_eq_sum_range
      (fun o : ℕ =>
        ‖MeasureClass.measProj (qs := qs) r o u‖
          * ‖MeasureClass.measProj (qs := qs) r o v‖) Q]
    rw [Fin.sum_univ_eq_sum_range
      (fun o : ℕ =>
        ‖MeasureClass.measProj (qs := qs) r o u‖ ^ 2) Q]
    rw [Fin.sum_univ_eq_sum_range
      (fun o : ℕ =>
        ‖MeasureClass.measProj (qs := qs) r o v‖ ^ 2) Q]
    simpa [fu, fv] using hrange

  have hB_nonneg :
      0 ≤
      ∑ o : Fin Q,
        ‖MeasureClass.measProj (qs := qs) r o.1 v‖ ^ 2 := by
    refine Finset.sum_nonneg ?_
    intro o ho
    exact sq_nonneg _

  have hprod :
      (∑ o : Fin Q,
        ‖MeasureClass.measProj (qs := qs) r o.1 u‖ ^ 2)
        *
      (∑ o : Fin Q,
        ‖MeasureClass.measProj (qs := qs) r o.1 v‖ ^ 2)
        ≤
      ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
    exact mul_le_mul hA hB hB_nonneg (sq_nonneg _)

  have hsq :
      (∑ o : Fin Q,
        ‖MeasureClass.measProj (qs := qs) r o.1 u‖
          * ‖MeasureClass.measProj (qs := qs) r o.1 v‖) ^ 2
        ≤
      (‖u‖ * ‖v‖) ^ 2 := by
    calc
      (∑ o : Fin Q,
        ‖MeasureClass.measProj (qs := qs) r o.1 u‖
          * ‖MeasureClass.measProj (qs := qs) r o.1 v‖) ^ 2
          ≤
        (∑ o : Fin Q,
          ‖MeasureClass.measProj (qs := qs) r o.1 u‖ ^ 2)
          *
        (∑ o : Fin Q,
          ‖MeasureClass.measProj (qs := qs) r o.1 v‖ ^ 2) := hcs
      _ ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 := hprod
      _ = (‖u‖ * ‖v‖) ^ 2 := by ring

  have hsum_nonneg :
      0 ≤
      ∑ o : Fin Q,
        ‖MeasureClass.measProj (qs := qs) r o.1 u‖
          * ‖MeasureClass.measProj (qs := qs) r o.1 v‖ := by
    refine Finset.sum_nonneg ?_
    intro o ho
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)

  have hnorm_nonneg : 0 ≤ ‖u‖ * ‖v‖ := by
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)

  nlinarith

/-! ## Measurement distribution distance bounds -/

/-- The total variation distance between two finite measurement distributions
is bounded by twice the Hilbert-space distance between unit states. -/
lemma MeasureClass.probMeas_l1_dist
    {qs : QSemantics} [RegEncoding qs.Basis] [MeasureClass qs]
    (r : Reg) (Q : ℕ) (ψ φ : qs.State)
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    (∑ o : Fin Q,
      |MeasureClass.probMeas (qs := qs) r o.1 ψ
        - MeasureClass.probMeas (qs := qs) r o.1 φ|)
      ≤ 2 * ‖ψ - φ‖ := by
  calc
    (∑ o : Fin Q,
      |MeasureClass.probMeas (qs := qs) r o.1 ψ
        - MeasureClass.probMeas (qs := qs) r o.1 φ|)
        =
      ∑ o : Fin Q,
        |‖MeasureClass.measProj (qs := qs) r o.1 ψ‖ ^ 2
          - ‖MeasureClass.measProj (qs := qs) r o.1 φ‖ ^ 2| := by
          refine Finset.sum_congr rfl ?_
          intro o ho
          rw [MeasureClass.probMeas_born (qs := qs) r o.1 ψ,
              MeasureClass.probMeas_born (qs := qs) r o.1 φ]
    _ ≤
      ∑ o : Fin Q,
        ‖MeasureClass.measProj (qs := qs) r o.1 (ψ + φ)‖
          * ‖MeasureClass.measProj (qs := qs) r o.1 (ψ - φ)‖ := by
          refine Finset.sum_le_sum ?_
          intro o ho
          exact measProj_sqdiff_le (qs := qs) r o.1 ψ φ
    _ ≤ ‖ψ + φ‖ * ‖ψ - φ‖ := by
          exact measProj_cauchy_prefix
            (qs := qs) r Q (ψ + φ) (ψ - φ)
    _ ≤ (‖ψ‖ + ‖φ‖) * ‖ψ - φ‖ := by
          exact mul_le_mul_of_nonneg_right
            (norm_add_le ψ φ) (norm_nonneg _)
    _ = 2 * ‖ψ - φ‖ := by
          rw [hψ, hφ]
          ring

omit [MeasureClass qs] in
/-- Weighted version of `MeasureClass.probMeas_l1_dist` for weights in `[0, 1]`.

This is the form used for postprocessing success probabilities, where the
weight is the indicator that continued-fraction postprocessing recovered the
right order. -/
lemma probMeas_weighted_dist [MeasureClass qs] :
    ∀ (r : Reg) (Q : ℕ) (w : Fin Q → ℝ) (ψ φ : qs.State),
      (∀ o, 0 ≤ w o ∧ w o ≤ 1) →
      ‖ψ‖ = 1 →
      ‖φ‖ = 1 →
      |(∑ o : Fin Q, w o * MeasureClass.probMeas (qs := qs) r o.1 ψ)
        -
        (∑ o : Fin Q, w o * MeasureClass.probMeas (qs := qs) r o.1 φ)|
      ≤ 2 * ‖ψ - φ‖ := by
  intro r Q w ψ φ hw hψ hφ
  have hpoint :
      ∀ o : Fin Q,
        |w o * MeasureClass.probMeas (qs := qs) r o.1 ψ
          - w o * MeasureClass.probMeas (qs := qs) r o.1 φ|
        ≤
        |MeasureClass.probMeas (qs := qs) r o.1 ψ
          - MeasureClass.probMeas (qs := qs) r o.1 φ| := by
    intro o
    have h0 : 0 ≤ w o := (hw o).1
    have h1 : w o ≤ 1 := (hw o).2
    calc
      |w o * MeasureClass.probMeas (qs := qs) r o.1 ψ
        - w o * MeasureClass.probMeas (qs := qs) r o.1 φ|
          =
        |w o| *
          |MeasureClass.probMeas (qs := qs) r o.1 ψ
            - MeasureClass.probMeas (qs := qs) r o.1 φ| := by
              rw [← abs_mul]
              congr 1
              ring
      _ = w o *
          |MeasureClass.probMeas (qs := qs) r o.1 ψ
            - MeasureClass.probMeas (qs := qs) r o.1 φ| := by
              rw [abs_of_nonneg h0]
      _ ≤ 1 *
          |MeasureClass.probMeas (qs := qs) r o.1 ψ
            - MeasureClass.probMeas (qs := qs) r o.1 φ| := by
              exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ =
          |MeasureClass.probMeas (qs := qs) r o.1 ψ
            - MeasureClass.probMeas (qs := qs) r o.1 φ| := by ring

  calc
    |(∑ o : Fin Q, w o * MeasureClass.probMeas (qs := qs) r o.1 ψ)
      - (∑ o : Fin Q, w o * MeasureClass.probMeas (qs := qs) r o.1 φ)|
        =
      |∑ o : Fin Q,
        (w o * MeasureClass.probMeas (qs := qs) r o.1 ψ
          - w o * MeasureClass.probMeas (qs := qs) r o.1 φ)| := by
          rw [← Finset.sum_sub_distrib]
    _ ≤ ∑ o : Fin Q,
        |w o * MeasureClass.probMeas (qs := qs) r o.1 ψ
          - w o * MeasureClass.probMeas (qs := qs) r o.1 φ| := by
          simpa using
            Finset.abs_sum_le_sum_abs
              (fun o : Fin Q =>
                w o * MeasureClass.probMeas (qs := qs) r o.1 ψ
                  - w o * MeasureClass.probMeas (qs := qs) r o.1 φ)
              Finset.univ
    _ ≤ ∑ o : Fin Q,
        |MeasureClass.probMeas (qs := qs) r o.1 ψ
          - MeasureClass.probMeas (qs := qs) r o.1 φ| := by
          exact Finset.sum_le_sum (fun o ho => hpoint o)
    _ ≤ 2 * ‖ψ - φ‖ := by
          exact MeasureClass.probMeas_l1_dist
            (qs := qs) r Q ψ φ hψ hφ

/-! ## Success probabilities and range facts -/

-- /-- Run the circuit G on input state ψ, then measure register r, and ask for probability of outcome o -/
-- noncomputable def measProbAfter (r : Reg) (o : ℕ) (G : Gate) (ψ : qs.State) : ℝ :=
--   MeasureClass.probMeas (qs := qs) r o (qs.eval G ψ)


/-- Given a finite set Good of outcomes that are “successful,” sum the measurement probability over those outcomes. -/
noncomputable def successProbAfterFinset
  [GateSemanticsCore qs]
  (r : Reg) (Good : Finset ℕ) (G : Gate) (ψ : qs.State) : ℝ :=
  ∑ o ∈ Good, MeasureClass.probMeas (qs := qs) r o (qs.eval G ψ)

/-- The Born-rule probability of an out-of-range outcome is zero. -/
lemma probMeas_outOfRange_of_born
    {qs : QSemantics} [RegEncoding qs.Basis] [MeasureClass qs]
    (r : Reg) (o : ℕ) (ψ : qs.State)
    (ho : 2 ^ regSize r ≤ o) :
    MeasureClass.probMeas (qs := qs) r o ψ = 0 := by
  rw [MeasureClass.probMeas_born (qs := qs) r o ψ]
  rw [MeasureClass.measProj_zero_outOfRange (qs := qs) r o ψ ho]
  simp

omit [MeasureClass qs] in
/-- Success probability is nonnegative. -/
lemma successProbAfterFinset_nonneg [MeasureClass qs]
  [GateSemanticsCore qs]
  (r : Reg) (Good : Finset ℕ) (G : Gate) (ψ : qs.State) :
  0 ≤ successProbAfterFinset (qs := qs) r Good G ψ := by
  unfold successProbAfterFinset MeasureClass.probMeas
  refine Finset.sum_nonneg ?_
  intro o ho
  exact sq_nonneg _

omit [MeasureClass qs] in
/-- If the good-outcome set is enlarged, success probability can only go up. -/
lemma successProbAfterFinset_mono [MeasureClass qs]
  [GateSemanticsCore qs]
  (r : Reg) {Good Good' : Finset ℕ} (hsub : Good ⊆ Good')
  (G : Gate) (ψ : qs.State) :
  successProbAfterFinset (qs := qs) r Good G ψ
    ≤
  successProbAfterFinset (qs := qs) r Good' G ψ := by
  unfold successProbAfterFinset MeasureClass.probMeas
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
  intro o ho hnot
  exact sq_nonneg _

omit [MeasureClass qs] in
/-- Intersecting the good-outcome set with the register range does not change
the success probability. -/
lemma successProbAfterFinset_inter_range_eq [MeasureClass qs]
  [GateSemanticsCore qs]
  (r : Reg) (Good : Finset ℕ) (G : Gate) (ψ : qs.State) :
  successProbAfterFinset (qs := qs)
      r (Good ∩ Finset.range (2 ^ regSize r)) G ψ
    =
  successProbAfterFinset (qs := qs) r Good G ψ := by
  classical
  unfold successProbAfterFinset MeasureClass.probMeas

  refine Finset.sum_subset ?_ ?_
  · intro o ho
    exact (Finset.mem_inter.mp ho).1

  · intro o hoGood hoNotInter
    have hoNotRange : o ∉ Finset.range (2 ^ regSize r) := by
      intro hoRange
      exact hoNotInter (Finset.mem_inter.mpr ⟨hoGood, hoRange⟩)

    have hoGe : 2 ^ regSize r ≤ o := by
      apply Nat.le_of_not_gt
      intro hoLt
      exact hoNotRange (Finset.mem_range.mpr hoLt)

    exact probMeas_outOfRange_of_born
      (qs := qs) r o (qs.eval G ψ) hoGe


end Shor
