import FastMultiplication.ShorVerification.AbstractMachine.WholeProgramCorrectness
import FastMultiplication.ShorVerification.AlgorithmCorrectness.ModExpBounds
import FastMultiplication.ShorVerification.MathBackbone.ShorDefinition
import FastMultiplication.ShorVerification.MathBackbone.Factoring_Reduction.Reduction
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Shor
open Gate
open Classical

/-!
# Shor/order-finding circuit statement

This file keeps the quantum-facing part of the Shor statement: the ideal and
approximate order-finding circuits, the measurement interface, and the final
success-probability theorem.  Classical order and continued-fraction material
lives in `MathBackbone/ShorAlgorithm.lean`.
-/

/-! =========================================================
    Section 1: Order-finding circuits

    These definitions assemble the high-level gates used by the ideal and
    approximate order-finding algorithms.
========================================================= -/

def initY1 (y : Reg) : Gate :=
  Gate.X y.lo

/-- Approximate (in-place) quantum order-finding circuit. -/
noncomputable def orderFindingApprox
  (qs : QSemantics) [RegEncoding qs.Basis] [Spec] [ExtRegEncoding qs.Basis] [ModMul qs]
  (a N : ℕ) (x y w_reg : Reg) (flag : ℕ) : Gate :=
  (H_reg x) ;;
  (initY1 y) ;;
  (modExpApprox' (qs := qs) a N x y w_reg flag) ;;
  (Gate.QFT x)

/-- Ideal order-finding circuit using exact modular exponentiation. -/
noncomputable def orderFindingIdeal
  (qs : QSemantics) [RegEncoding qs.Basis] [Spec]
  (a N : ℕ) (x y : Reg) : Gate :=
  (H_reg x) ;;
  (initY1 y) ;;
  (modExpIdeal' (qs := qs) a N x y) ;;
  (Gate.QFT x)


variable {qs : QSemantics}
variable [RegEncoding qs.Basis]

/-! =========================================================
    Section 2: Measurement and success probabilities

    `MeasureClass` packages the Born-rule projectors used to talk about
    measuring a register.  The lemmas in this section turn those projector
    axioms into the probability estimates needed later:

    * orthogonal projector sums have the expected norm square;
    * measurement mass outside a register range is zero;
    * measurement distributions are Lipschitz in state distance.
========================================================= -/

/-- Abstract interface for measuring a register.

Rather than committing to a concrete basis-level measurement construction,
the rest of this file assumes the usual finite family of orthogonal
self-adjoint projectors and the Born rule for probabilities. -/
class MeasureClass (qs : QSemantics) [RegEncoding qs.Basis] where
  /-- Probability of observing outcome `o` when measuring register `r`. -/
  probMeas : Reg → ℕ → qs.State → ℝ

  /-- Outcome projector for measuring register `r`. -/
  measProj : Reg → ℕ → qs.State →L[ℂ] qs.State

  /-- Born rule. -/
  probMeas_born :
    ∀ r o ψ,
      probMeas r o ψ = ‖measProj r o ψ‖ ^ 2

  /-- No outcomes beyond the register's computational-basis range. -/
  measProj_zero_outOfRange :
    ∀ r o ψ,
      2 ^ regSize r ≤ o →
      measProj r o ψ = 0

  /-- Each measurement effect is a self-adjoint projector. -/
  measProj_selfAdjoint :
    ∀ r o ψ φ,
      inner ℂ (measProj r o ψ) φ
        = inner ℂ ψ (measProj r o φ)

  /-- Projector idempotence for a single measurement outcome. -/
  measProj_idempotent :
    ∀ r o ψ,
      measProj r o (measProj r o ψ) = measProj r o ψ

  /-- Different outcomes are orthogonal projectors. -/
  measProj_orthogonal :
    ∀ r o o' ψ,
      o ≠ o' →
      measProj r o (measProj r o' ψ) = 0

  /-- The projectors sum to identity over valid outcomes. -/
  measProj_complete :
    ∀ r ψ,
      (∑ o : Fin (2 ^ regSize r), measProj r o.1 ψ) = ψ


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

/-- Run the circuit G on input state ψ, then measure register r, and ask for probability of outcome o -/
noncomputable def measProbAfter (r : Reg) (o : ℕ) (G : Gate) (ψ : qs.State) : ℝ :=
  MeasureClass.probMeas (qs := qs) r o (qs.eval G ψ)

/-- Given a finite set Good of outcomes that are “successful,” sum the measurement probability over those outcomes. -/
noncomputable def successProbAfterFinset
  (r : Reg) (Good : Finset ℕ) (G : Gate) (ψ : qs.State) : ℝ :=
  ∑ o ∈ Good, measProbAfter (qs := qs) r o G ψ

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
  (r : Reg) (Good : Finset ℕ) (G : Gate) (ψ : qs.State) :
  0 ≤ successProbAfterFinset (qs := qs) r Good G ψ := by
  unfold successProbAfterFinset measProbAfter
  refine Finset.sum_nonneg ?_
  intro o ho
  rw [MeasureClass.probMeas_born (qs := qs) r o (qs.eval G ψ)]
  exact sq_nonneg _

omit [MeasureClass qs] in
/-- If the good-outcome set is enlarged, success probability can only go up. -/
lemma successProbAfterFinset_mono [MeasureClass qs]
  (r : Reg) {Good Good' : Finset ℕ} (hsub : Good ⊆ Good')
  (G : Gate) (ψ : qs.State) :
  successProbAfterFinset (qs := qs) r Good G ψ
    ≤
  successProbAfterFinset (qs := qs) r Good' G ψ := by
  unfold successProbAfterFinset measProbAfter
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
  intro o ho hnot
  rw [MeasureClass.probMeas_born (qs := qs) r o (qs.eval G ψ)]
  exact sq_nonneg _

omit [MeasureClass qs] in
/-- Intersecting the good-outcome set with the register range does not change
the success probability. -/
lemma successProbAfterFinset_inter_range_eq [MeasureClass qs]
  (r : Reg) (Good : Finset ℕ) (G : Gate) (ψ : qs.State) :
  successProbAfterFinset (qs := qs)
      r (Good ∩ Finset.range (2 ^ regSize r)) G ψ
    =
  successProbAfterFinset (qs := qs) r Good G ψ := by
  classical
  unfold successProbAfterFinset measProbAfter

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

variable [ContinuedFractionPost] [Spec]
variable [ExtRegEncoding qs.Basis]
variable [ModMul qs]

/-- Success probability after running `G` and then applying classical
continued-fraction/order-verification postprocessing to the measured `x`
register outcome. -/
noncomputable def probability_of_success
  (T : ℕ → ℕ) (verify : OrderVerifier)
  (x : Reg) (r Q : ℕ) (G : Gate) (ψ : qs.State) : ℝ :=
  ∑ o : Fin Q,
    (r_found (T := T) verify o.1 Q r) *
      (measProbAfter (qs := qs) x o.1 G ψ)


/-! =========================================================
    Section 3: Probability-transfer lemmas

    These lemmas are the bridge from state-vector approximation to
    success-probability approximation.  The first group is pure real/probability
    bookkeeping; the second group uses gate isometry to move distance bounds
    through common circuit context.
========================================================= -/
omit [ContinuedFractionPost] [Spec] in
/-- If two probabilities differ by at most `ε`, then the first is at least
    the second minus `ε`.

    This is the Lean version of:

        |A - B| ≤ ε  ⇒  A ≥ B - ε.
-/
lemma lower_bound_of_abs_sub_le {A B ε : ℝ}
    (h : |A - B| ≤ ε) :
    A ≥ B - ε := by
  have hleft : -ε ≤ A - B := (abs_le.mp h).1
  linarith

omit [ContinuedFractionPost] [Spec] in
/-- If the approximate and ideal success probabilities differ by at most `ε`,
    and the ideal success probability is at least `L`, then the approximate
    success probability is at least `L - ε`. -/
lemma transfer_lower_bound_from_abs_prob
    {Papprox Pideal L ε : ℝ}
    (hprob : |Papprox - Pideal| ≤ ε)
    (hideal : Pideal ≥ L) :
    Papprox ≥ L - ε := by
  have hlow : Papprox ≥ Pideal - ε :=
    lower_bound_of_abs_sub_le hprob
  linarith

omit [ContinuedFractionPost] [Spec] in
/-- Applying a common suffix gate preserves a state-distance bound. -/
lemma dist_eval_common_suffix_le
    (qs : QSemantics)
    (W A I : Gate)
    (ψ : qs.State)
    {ε : ℝ}
    (h : ‖qs.eval A ψ - qs.eval I ψ‖ ≤ ε) :
    ‖qs.eval W (qs.eval A ψ) - qs.eval W (qs.eval I ψ)‖ ≤ ε := by
  calc
    ‖qs.eval W (qs.eval A ψ) - qs.eval W (qs.eval I ψ)‖
        = ‖qs.eval A ψ - qs.eval I ψ‖ := by
            simpa using
              (eval_isometry qs W
                (by
                  intro ψ φ
                  simpa using qs.inner_preserved W ψ φ)
                (qs.eval A ψ)
                (qs.eval I ψ))
    _ ≤ ε := h

omit [MeasureClass qs] [Spec] [ExtRegEncoding QSemantics.Basis] [ModMul qs] in
/-- Convert a state-distance bound between two complete circuits into a lower
bound on the approximate circuit's postprocessed success probability. -/
lemma probability_of_success_eval_dist [MeasureClass qs]
  (T : ℕ → ℕ)
  (verify : ℕ → Bool)
  (x : Reg)
  (r Q : ℕ)
  (Gapprox Gideal : Gate)
  (ψ : qs.State)
  (ε : ℝ)
  (hψ : ‖ψ‖ = 1)
  (hdist :
    ‖qs.eval Gapprox ψ - qs.eval Gideal ψ‖ ≤ ε) :
  probability_of_success (qs := qs) (T := T)
      (verify := verify)
      (x := x) (r := r) (Q := Q)
      (G := Gapprox)
      (ψ := ψ)
    ≥
  probability_of_success (qs := qs) (T := T)
      (verify := verify)
      (x := x) (r := r) (Q := Q)
      (G := Gideal)
      (ψ := ψ)
    - 2 * ε := by
  let ψA : qs.State := qs.eval Gapprox ψ
  let ψI : qs.State := qs.eval Gideal ψ

  have hψA : ‖ψA‖ = 1 := by
    dsimp [ψA]
    simpa [hψ] using
      (eval_norm_preserved (qs := qs) Gapprox ψ)

  have hψI : ‖ψI‖ = 1 := by
    dsimp [ψI]
    simpa [hψ] using
      (eval_norm_preserved (qs := qs) Gideal ψ)

  let w : Fin Q → ℝ :=
    fun o => r_found (T := T) verify o.1 Q r

  have hw : ∀ o, 0 ≤ w o ∧ w o ≤ 1 := by
    intro o
    dsimp [w, r_found]
    by_cases h : OF_post (T := T) verify o.1 Q = r
    · simp [h]
    · simp [h]

  have hprob_dist :
      |probability_of_success (qs := qs) (T := T)
          (verify := verify)
          (x := x) (r := r) (Q := Q)
          (G := Gapprox)
          (ψ := ψ)
        -
        probability_of_success (qs := qs) (T := T)
          (verify := verify)
          (x := x) (r := r) (Q := Q)
          (G := Gideal)
          (ψ := ψ)|
      ≤ 2 * ‖qs.eval Gapprox ψ - qs.eval Gideal ψ‖ := by
    have hmain :=
      probMeas_weighted_dist
        (qs := qs)
        x Q w ψA ψI hw hψA hψI

    simpa [probability_of_success, measProbAfter, ψA, ψI, w] using hmain

  have hprob :
      |probability_of_success (qs := qs) (T := T)
          (verify := verify)
          (x := x) (r := r) (Q := Q)
          (G := Gapprox)
          (ψ := ψ)
        -
        probability_of_success (qs := qs) (T := T)
          (verify := verify)
          (x := x) (r := r) (Q := Q)
          (G := Gideal)
          (ψ := ψ)|
      ≤ 2 * ε := by
    exact le_trans hprob_dist
      (mul_le_mul_of_nonneg_left hdist (by norm_num))

  exact lower_bound_of_abs_sub_le hprob

omit [RegEncoding qs.Basis] [MeasureClass qs] [ContinuedFractionPost] [Spec] [ExtRegEncoding qs.Basis] [ModMul qs] in
/-- Gate evaluation is an isometry for state distance. -/
lemma eval_common_gate_dist_eq
    (W : Gate) (ψ φ : qs.State) :
    ‖qs.eval W ψ - qs.eval W φ‖ = ‖ψ - φ‖ := by
  simpa using
    (eval_isometry qs W
      (by
        intro ψ φ
        simpa using qs.inner_preserved W ψ φ)
      ψ φ)

omit [RegEncoding qs.Basis] [MeasureClass qs] [ContinuedFractionPost] [Spec] [ExtRegEncoding qs.Basis] [ModMul qs] in
/-- Gate evaluation preserves the norm of a state. -/
lemma eval_norm_preserved_from_inner
    (W : Gate) (ψ : qs.State) :
    ‖qs.eval W ψ‖ = ‖ ψ‖ := by
  have h :=
    eval_common_gate_dist_eq (qs := qs) W ψ 0
  simpa [qs.eval_zero W] using h

omit [RegEncoding qs.Basis] [MeasureClass qs] [ContinuedFractionPost] [Spec] [ExtRegEncoding qs.Basis] [ModMul qs] in
/-- A distance bound in the middle of a circuit survives identical pre- and
post-contexts. -/
lemma eval_common_context_dist_bound
    (Upre A I Upost : Gate)
    (ψ : qs.State)
    (ε : ℝ)
    (hmid :
      ‖ qs.eval A (qs.eval Upre ψ)
        - qs.eval I (qs.eval Upre ψ)‖ ≤ ε) :
    ‖ qs.eval ((Upre ;; A) ;; Upost) ψ
      - qs.eval ((Upre ;; I) ;; Upost) ψ‖ ≤ ε := by
  calc
    ‖ qs.eval ((Upre ;; A) ;; Upost) ψ
      - qs.eval ((Upre ;; I) ;; Upost) ψ‖
        =
      ‖ qs.eval Upost (qs.eval A (qs.eval Upre ψ))
        - qs.eval Upost (qs.eval I (qs.eval Upre ψ))‖ := by
          simp [qs.eval_seq]
    _ =
      ‖ qs.eval A (qs.eval Upre ψ)
        - qs.eval I (qs.eval Upre ψ)‖ := by
          exact eval_common_gate_dist_eq
            (qs := qs)
            Upost
            (qs.eval A (qs.eval Upre ψ))
            (qs.eval I (qs.eval Upre ψ))
    _ ≤ ε := hmid

omit [RegEncoding qs.Basis] [MeasureClass qs] [ContinuedFractionPost] [Spec] [ExtRegEncoding qs.Basis] [ModMul qs] in
/-- Version of `eval_common_context_dist_bound` where the middle bound is only
known for unit inputs. -/
lemma eval_common_context_dist_bound_of_unit_input
    (Upre A I Upost : Gate)
    (ψ : qs.State)
    (ε : ℝ)
    (hψ : ‖ψ‖ = 1)
    (hmid :
      ∀ φ : qs.State,
        ‖φ‖ = 1 →
        ‖ qs.eval A φ - qs.eval I φ‖ ≤ ε) :
    ‖ qs.eval ((Upre ;; A) ;; Upost) ψ
      - qs.eval ((Upre ;; I) ;; Upost) ψ‖ ≤ ε := by
  apply eval_common_context_dist_bound (qs := qs)
  apply hmid
  simpa [hψ] using
    eval_norm_preserved_from_inner (qs := qs) Upre ψ

omit [MeasureClass qs] [ContinuedFractionPost] in
/-- Generic context lemma for order-finding circuits once the pre/post
decomposition is supplied explicitly. -/
lemma orderFindingApprox_eval_dist_bound_of_decomp
    (K : ℝ)
    (hmodExp :
      ∀ (a N : ℕ) (x y w_reg : Reg) (flag : ℕ) (ψ : qs.State),
        ‖ψ‖ = 1 →
        ‖ qs.eval (modExpApprox' (qs := qs) a N x y w_reg flag) ψ
          - qs.eval (modExpIdeal'  (qs := qs) a N x y) ψ‖
        ≤ (tbits x : ℝ) * stepErr K (ModMul.η (qs := qs)))
    (a N : ℕ)
    (x y w : Reg)
    (flag : ℕ)
    (ψ0 : qs.State)
    (hψ0 : ‖ψ0‖ = 1)
    (Upre Upost : Gate)
    (hApprox :
      orderFindingApprox (qs := qs) a N x y w flag
        =
      ((Upre ;; modExpApprox' (qs := qs) a N x y w flag) ;; Upost))
    (hIdeal :
      orderFindingIdeal (qs := qs) a N x y
        =
      ((Upre ;; modExpIdeal' (qs := qs) a N x y) ;; Upost)) :
    ‖ qs.eval (orderFindingApprox (qs := qs) a N x y w flag) ψ0
      - qs.eval (orderFindingIdeal  (qs := qs) a N x y) ψ0‖
      ≤ (tbits x : ℝ) * stepErr K (ModMul.η (qs := qs)) := by
  rw [hApprox, hIdeal]
  apply eval_common_context_dist_bound_of_unit_input (qs := qs)
  · exact hψ0
  · intro φ hφ
    exact hmodExp a N x y w flag φ hφ

omit [MeasureClass qs] [ContinuedFractionPost] in
/-- Distance between the approximate and ideal order-finding circuits follows
from the modular-exponentiation distance bound, since the surrounding gates are
common isometries. -/
lemma orderFindingApprox_eval_dist_bound
 (K : ℝ)
  (hmodExp :
    ∀ (a N : ℕ) (x y w_reg : Reg) (flag : ℕ) (ψ : qs.State),
      ‖ψ‖ = 1 →
      ‖ qs.eval (modExpApprox' (qs := qs) a N x y w_reg flag) ψ
        - qs.eval (modExpIdeal'  (qs := qs) a N x y) ψ‖
      ≤ (tbits x : ℝ) * stepErr K (ModMul.η (qs := qs)))
  (a N : ℕ)
  (x y w : Reg)
  (flag : ℕ)
  (ψ0 : qs.State)
  (hψ0 : ‖ψ0‖ = 1) :
  ‖ qs.eval (orderFindingApprox (qs := qs) a N x y w flag) ψ0
    - qs.eval (orderFindingIdeal  (qs := qs) a N x y) ψ0‖
    ≤ (tbits x : ℝ) * stepErr K (ModMul.η (qs := qs)) := by
  let ψpre : qs.State :=
    qs.eval (initY1 y) (qs.eval (H_reg x) ψ0)

  have hH_unit :
      ‖qs.eval (H_reg x) ψ0‖ = 1 := by
    simpa [hψ0] using
      (eval_norm_preserved_from_inner
        (qs := qs)
        (H_reg x)
        ψ0)

  have hpre_unit : ‖ψpre‖ = 1 := by
    dsimp [ψpre]
    simpa [hH_unit] using
      (eval_norm_preserved_from_inner
        (qs := qs)
        (initY1 y)
        (qs.eval (H_reg x) ψ0))

  have hmid :
      ‖ qs.eval (modExpApprox' (qs := qs) a N x y w flag) ψpre
        - qs.eval (modExpIdeal'  (qs := qs) a N x y) ψpre‖
      ≤ (tbits x : ℝ) * stepErr K (ModMul.η (qs := qs)) := by
    exact hmodExp a N x y w flag ψpre hpre_unit

  have hpost :
      ‖ qs.eval (Gate.QFT x)
            (qs.eval (modExpApprox' (qs := qs) a N x y w flag) ψpre)
        - qs.eval (Gate.QFT x)
            (qs.eval (modExpIdeal'  (qs := qs) a N x y) ψpre)‖
      ≤ (tbits x : ℝ) * stepErr K (ModMul.η (qs := qs)) := by
    exact dist_eval_common_suffix_le
      (qs := qs)
      (Gate.QFT x)
      (modExpApprox' (qs := qs) a N x y w flag)
      (modExpIdeal'  (qs := qs) a N x y)
      ψpre
      hmid

  simpa [orderFindingApprox, orderFindingIdeal, ψpre, qs.eval_seq] using hpost


/-! =========================================================
    Section 4: Final correctness statements

    The ideal theorem is the quantum order-finding lower bound used by the
    rest of the file.  The approximation theorem transfers that ideal bound
    across the modular-exponentiation implementation error, and the final
    factoring statement combines it with the classical reduction.
========================================================= -/

/-- Ideal order-finding success probability for Shor's algorithm.

This is the top-level quantum lower bound: starting from a unit input state,
the ideal order-finding circuit recovers the order with at least the standard
inverse-polylogarithmic probability. -/
theorem Shor_correct
  (T : ℕ → ℕ)
  (a N : ℕ)
  (ha : 0 < a ∧ a < N)
  (hgcd : Nat.gcd a N = 1)
  (x y w : Reg)
  (ψ0 : qs.State)
  (hψ0 : ‖ψ0‖ = 1)
  (hm : regSize x = Nat.log2 (2 * N^2))
  (hn : regSize y = Nat.log2 (2 * N))
  (hset : BasicSetting a (ord a N hgcd) N (regSize x) (regSize y)) :
  probability_of_success (qs := qs) (T := T)
    (verify := fun d => decide ((a ^ d) % N = 1))
    (x := x) (r := ord a N hgcd) (Q := 2^(regSize x))
    (G := orderFindingIdeal (qs := qs) a N x y)
    (ψ := ψ0)
  ≥ κ / (Nat.log2 N : ℝ)^4 := by
  sorry


omit [MeasureClass qs] in
/-- Approximate order-finding inherits the ideal lower bound, with a penalty
controlled by the modular-exponentiation distance estimate. -/
theorem Shor_correct_approx [MeasureClass qs]
  (T : ℕ → ℕ)
  (a N : ℕ)
  (ha : 0 < a ∧ a < N)
  (hgcd : Nat.gcd a N = 1)
  (x y w : Reg) (flag : ℕ)
  (ψ0 : qs.State)
  (hψ0 : ‖ψ0‖ = 1)
  (hm : regSize x = Nat.log2 (2 * N^2))
  (hn : regSize y = Nat.log2 (2 * N))
  (hset : BasicSetting a (ord a N hgcd) N (regSize x) (regSize y)) :
  ∃ K : ℝ, 0 ≤ K ∧
    probability_of_success (qs := qs) (T := T)
      (verify := fun d => decide ((a ^ d) % N = 1))
      (x := x) (r := ord a N hgcd) (Q := 2^(regSize x))
      (G := orderFindingApprox (qs := qs) a N x y w flag)
      (ψ := ψ0)
    ≥
      κ / (Nat.log2 N : ℝ)^4
      - 2 * (tbits x : ℝ) * (Real.sqrt (2 * (K * (ModMul.η (qs := qs))))) := by
  rcases modExp_dist_bound (qs := qs) with ⟨K, hK_nonneg, hmodExp⟩
  refine ⟨K, hK_nonneg, ?_⟩

  let verify : ℕ → Bool := fun d => decide ((a ^ d) % N = 1)
  let r : ℕ := ord a N hgcd
  let Q : ℕ := 2 ^ regSize x
  let ε : ℝ := (tbits x : ℝ) * stepErr K (ModMul.η (qs := qs))

  have hε_nonneg : 0 ≤ ε := by
    dsimp [ε]
    exact mul_nonneg (Nat.cast_nonneg _)
      (by
        unfold stepErr
        exact Real.sqrt_nonneg _)

  have hdist_full :
      ‖ qs.eval (orderFindingApprox (qs := qs) a N x y w flag) ψ0
        - qs.eval (orderFindingIdeal  (qs := qs) a N x y) ψ0‖
      ≤ ε := by
    dsimp [ε]
    exact orderFindingApprox_eval_dist_bound
      (qs := qs)
      K hmodExp
      a N x y w flag ψ0 hψ0

  have htransfer :
      probability_of_success (qs := qs) (T := T)
        (verify := verify)
        (x := x) (r := r) (Q := Q)
        (G := orderFindingApprox (qs := qs) a N x y w flag)
        (ψ := ψ0)
      ≥
      probability_of_success (qs := qs) (T := T)
        (verify := verify)
        (x := x) (r := r) (Q := Q)
        (G := orderFindingIdeal (qs := qs) a N x y)
        (ψ := ψ0)
      - 2 * ε := by
    exact probability_of_success_eval_dist
      (qs := qs)
      T verify x r Q
      (orderFindingApprox (qs := qs) a N x y w flag)
      (orderFindingIdeal  (qs := qs) a N x y)
      ψ0 ε hψ0 hdist_full

  have hideal :
      probability_of_success (qs := qs) (T := T)
        (verify := verify)
        (x := x) (r := r) (Q := Q)
        (G := orderFindingIdeal (qs := qs) a N x y)
        (ψ := ψ0)
      ≥ κ / (Nat.log2 N : ℝ)^4 := by
    simpa [verify, r, Q] using
      (Shor_correct
        (qs := qs)
        T a N ha hgcd x y w ψ0 hψ0 hm hn hset)

  calc
    probability_of_success (qs := qs) (T := T)
        (verify := fun d => decide ((a ^ d) % N = 1))
        (x := x) (r := ord a N hgcd) (Q := 2^(regSize x))
        (G := orderFindingApprox (qs := qs) a N x y w flag)
        (ψ := ψ0)
        ≥
      probability_of_success (qs := qs) (T := T)
        (verify := verify)
        (x := x) (r := r) (Q := Q)
        (G := orderFindingIdeal (qs := qs) a N x y)
        (ψ := ψ0)
        - 2 * ε := by
          simpa [verify, r, Q] using htransfer
    _ ≥ κ / (Nat.log2 N : ℝ)^4 - 2 * ε := by
          exact sub_le_sub_right hideal (2 * ε)
    _ = κ / (Nat.log2 N : ℝ)^4
        - 2 * (tbits x : ℝ) * stepErr K (ModMul.η (qs := qs)) := by
          simp [ε, mul_assoc]

omit [ContinuedFractionPost] [Spec] in
/-- At least half of the coprime classical choices are successful for the
classical reduction, assuming `N` is odd, composite in the required sense, and
not a prime power. -/
theorem shors_probability_bound (N : ℕ)
(h_odd : Odd N)
(h_gt_one : N > 1)
(h_not_prime_power : ∀ (p k : ℕ), Nat.Prime p → N ≠ p ^ k) :
2 * (successful_choices N).card ≥ (valid_choices N).card := by {
  -- Extract two distinct odd prime factors, then apply the counting bound for
  -- unsuccessful choices.
  obtain ⟨p, q, hp, hq, hpq, hpN, hqN⟩ := exists_two_distinct_prime_factors h_gt_one h_not_prime_power
  have hp2 : p ≠ 2 := by
    rintro rfl; obtain ⟨k, hk⟩ := h_odd; obtain ⟨m, hm⟩ := hpN; omega
  have hq2 : q ≠ 2 := by
    rintro rfl; obtain ⟨k, hk⟩ := h_odd; obtain ⟨m, hm⟩ := hqN; omega

  have hvc := valid_choices_card_general h_gt_one
  set S := (Finset.range N).filter (fun a => Nat.gcd a N = 1) with hS_def

  have hS_card : S.card = Nat.totient N := by
    unfold Nat.totient; congr 1
    apply Finset.filter_congr; intro a _
    show Nat.gcd a N = 1 ↔ Nat.Coprime N a; rw [Nat.gcd_comm]

  have h_unsucc_bound :
      2 * (S.filter (fun a => ¬is_successful_choice a N)).card ≤ Nat.totient N := by
    have : S.filter (fun a => ¬is_successful_choice a N) =
        (Finset.range N).filter (fun a => Nat.gcd a N = 1 ∧ ¬is_successful_choice a N) := by
      rw [hS_def, Finset.filter_filter]
    rw [this]; exact general_unsuccessful_bound hp hq hpq hp2 hq2 hpN hqN

  have h_partition := Finset.card_filter_add_card_filter_not
    (fun a => is_successful_choice a N) (s := S)

  have h_succ_eq : successful_choices N = S.filter (fun a => is_successful_choice a N) := by
    unfold successful_choices valid_choices
    rw [Finset.filter_filter, hS_def, Finset.filter_filter]
    apply Finset.filter_congr; intro a ha
    rw [Finset.mem_range] at ha
    constructor
    · rintro ⟨⟨-, hg⟩, hs⟩; exact ⟨hg, hs⟩
    · rintro ⟨hg, hs⟩
      refine ⟨⟨?_, hg⟩, hs⟩
      have ha0 : a ≠ 0 := by rintro rfl; simp at hg; omega
      have ha1 : a ≠ 1 := fun h => by subst h; exact one_not_successful_choice _ hs
      omega

  rw [hvc, h_succ_eq]
  omega
}

omit [MeasureClass qs] in
/-- End-to-end statement combining the classical choice probability, ideal
quantum order-finding, and the classical factor extraction theorem. -/
theorem Shor_end_to_end_factoring [MeasureClass qs]
(T : ℕ → ℕ) (N : ℕ)
(h_odd : Odd N)
(h_N : N > 2)
(h_not_prime_power : ∀ (p k : ℕ), Nat.Prime p → N ≠ p ^ k)
(x y w : Reg)
(ψ0 : qs.State)
(hψ0 : ‖ψ0‖ = 1)
(hm : regSize x = Nat.log2 (2 * N^2))
(hn : regSize y = Nat.log2 (2 * N))
(hset : ∀ a, a ∈ valid_choices N →
  ∃ hgcd, BasicSetting a (ord a N hgcd) N (regSize x) (regSize y)) :
  (2 * (successful_choices N).card ≥ (valid_choices N).card)
  ∧
  (∀ a ∈ successful_choices N,
    ∃ (hgcd : Nat.gcd a N = 1),
    (probability_of_success (qs := qs) (T := T)
      (verify := fun d => decide ((a ^ d) % N = 1))
      (x := x) (r := ord a N hgcd) (Q := 2^(regSize x))
      (G := orderFindingIdeal (qs := qs) a N x y)
      (ψ := ψ0)
    ≥ κ / (Nat.log2 N : ℝ)^4)
    ∧
    (is_nontrivial_factor (Nat.gcd ((a ^ (ord a N hgcd / 2)) - 1) N) N ∨
     is_nontrivial_factor (Nat.gcd ((a ^ (ord a N hgcd / 2)) + 1) N) N)) := by {
  constructor
  { exact shors_probability_bound N h_odd (by omega) h_not_prime_power }
  {
    intro a h_a_in_successful
    obtain ⟨⟨ha1, ha2⟩, hgcd⟩ := success_eq_conditions a N h_a_in_successful
    obtain ⟨hgcd_set, hset_a⟩ := hset a (by simp [valid_choices, ha1, ha2, hgcd])

    have h_succ : shor_success_conditions a (ord a N hgcd) N := by {
      have h_a_is_succ : is_successful_choice a N := by {
        unfold successful_choices at h_a_in_successful
        simp_all
      }
      unfold is_successful_choice is_period at h_a_is_succ
      obtain ⟨r, h_per, h_cond⟩ := h_a_is_succ
      have h_r_eq : r = ord a N hgcd := by {
        have h_bridge := is_period_ord a N hgcd
        subst h_per
        simpa
      }
      rwa [h_r_eq] at h_cond
    }

    exists hgcd
    exact ⟨
      Shor_correct T a N ⟨by omega, ha2⟩ hgcd x y w ψ0 hψ0 hm hn hset_a,
      shors_classical_reduction a (ord a N hgcd) N h_N ⟨ha1, ha2⟩ hgcd (is_period_ord a N hgcd) h_succ
    ⟩
  }
}
