import FastMultiplication.ShorVerification.AbstractMachine.WholeProgramCorrectness
import FastMultiplication.ShorVerification.AlgorithmCorrectness.ModMulBounds.ModExp
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

/-- Approximate order finding using the proved valid-input ModExp circuit. -/
noncomputable def orderFindingApprox
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    (a N : ℕ)
    (x y work : Reg)
    (flag : ℕ) : Gate :=
  (H_reg x) ;;
  (initY1 y) ;;
  (modExpApproxValid
    (Basis := qs.Basis)
    a N x y work flag) ;;
  (Gate.QFT x)

/-- The lowered implementation of approximate order finding. -/
noncomputable def orderFindingApproxLow
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [ExtRegSplitSemantics qs.Basis]
    (k : ℕ) (hk : 1 < k)
    (ops : Prog k)
    (a N : ℕ)
    (x y work : Reg)
    (flag : ℕ) :=
  lowerGate
    (Basis := qs.Basis)
    k hk ops
    (orderFindingApprox (qs := qs) a N x y work flag)

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


/--
Run an arbitrary circuit-like object `C` using `evalC`, then measure `r`.
-/
noncomputable def measProbAfter
    [MeasureClass qs]
    {Circuit : Type}
    (evalC : Circuit → qs.State → qs.State)
    (r : Reg)
    (o : ℕ)
    (C : Circuit)
    (ψ : qs.State) : ℝ :=
  MeasureClass.probMeas (qs := qs) r o (evalC C ψ)

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
  (r : Reg) (Good : Finset ℕ) (G : Gate) (ψ : qs.State) : ℝ :=
  ∑ o ∈ Good, measProbAfter (qs := qs) qs.eval r o G ψ

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

/--
Success probability after an arbitrary circuit-like object `C`.

`evalC` specifies how that circuit type acts on states.
-/
noncomputable def probability_of_success
    {Circuit : Type}
    (evalC : Circuit → qs.State → qs.State)
    (T : ℕ → ℕ)
    (verify : OrderVerifier)
    (x : Reg)
    (r Q : ℕ)
    (C : Circuit)
    (ψ : qs.State) : ℝ :=
  ∑ o : Fin Q,
    (r_found (T := T) verify o.1 Q r) *
      measProbAfter
        (qs := qs) evalC x o.1 C ψ


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

omit [MeasureClass qs] [Spec] [ExtRegEncoding QSemantics.Basis] in
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
      (evalC := qs.eval)
      (C := Gapprox)
      (ψ := ψ)
    ≥
  probability_of_success (qs := qs) (T := T)
      (verify := verify)
      (x := x) (r := r) (Q := Q)
      (evalC := qs.eval)
      (C := Gideal)
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
          (evalC := qs.eval)
          (C := Gapprox)
          (ψ := ψ)
        -
        probability_of_success (qs := qs) (T := T)
          (verify := verify)
          (x := x) (r := r) (Q := Q)
          (evalC := qs.eval)
          (C := Gideal)
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
          (evalC := qs.eval)
          (C := Gapprox)
          (ψ := ψ)
        -
        probability_of_success (qs := qs) (T := T)
          (verify := verify)
          (x := x) (r := r) (Q := Q)
          (evalC := qs.eval)
          (C := Gideal)
          (ψ := ψ)|
      ≤ 2 * ε := by
    exact le_trans hprob_dist
      (mul_le_mul_of_nonneg_left hdist (by norm_num))

  exact lower_bound_of_abs_sub_le hprob

/-- Arithmetic, width, and continued-fraction assumptions for one
order-finding instance. -/
structure ShorOrderFindingInstance where
  /-- The base whose order is being found. -/
  a : ℕ
  /-- The modulus to factor. -/
  N : ℕ
  /-- The exponent/control register. -/
  x : Reg
  /-- The modular-exponentiation data register. -/
  y : Reg
  /-- The sampled base is in the valid range. -/
  range : 0 < a ∧ a < N
  /-- The sampled base is coprime to the modulus. -/
  coprime : Nat.gcd a N = 1
  /-- The exponent register has the standard Shor width. -/
  x_width : regSize x = Nat.log2 (2 * N^2)
  /-- The data register has enough room for residues modulo `N`. -/
  y_width : regSize y = Nat.log2 (2 * N)
  /-- The continued-fraction/postprocessing assumptions for this instance. -/
  order_setting :
    BasicSetting a (ord a N coprime) N (regSize x) (regSize y)

/-- Low-level lowering assumptions shared by lowered Shor statements. -/
structure ShorLoweringSetup where
  /-- Number of synthesis registers used by the lowering program. -/
  k : ℕ
  /-- At least two synthesis registers are available. -/
  hk : 1 < k
  /-- Program that consumes the interpolation points used by lowering. -/
  ops : Prog k
  /-- The point-consuming program is safe. -/
  consumes :
    ProgConsumesPtsSafe
      (k := k) (by omega)
      State.start_state ops
      (genInterpolationPoints k)
  /-- The point-consuming program uncomputes back to the start state. -/
  returns : run? ops State.start_state = some State.start_state

/-- Classical assumptions on a modulus for the final factoring theorem. -/
structure ShorFactoringInstance where
  /-- The modulus to factor. -/
  N : ℕ
  /-- Shor's classical reduction is stated for odd composite moduli. -/
  odd : Odd N
  /-- The modulus is nontrivial. -/
  gt_two : N > 2
  /-- The modulus is not a prime power. -/
  not_prime_power : ∀ (p k : ℕ), Nat.Prime p → N ≠ p ^ k

/-- The input basis state is clean on every register used by Shor. -/
def ShorCleanInput
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (x y work : Reg) (flag : ℕ)
    (b0 : qs.Basis) : Prop :=
  RegEncoding.toNat x b0 = 0 ∧
  RegEncoding.toNat y b0 = 0 ∧
  RegEncoding.bit y.hi b0 = false ∧
  RegEncoding.toNat work b0 = 0 ∧
  RegEncoding.bit flag b0 = false

/--
Public assumptions for the approximate implementation of Shor.
-/
structure ShorApproxSetup
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (η : ℝ)
    (a N : ℕ)
    (x y work : Reg)
    (flag : ℕ)
    (b0 : qs.Basis) : Prop where
  /-- The exponent, data, work, carry, and flag qubits do not overlap. -/
  register_layout :
    ModExpLayout x y work flag

  /-- The work register has enough extra bits for precision `η`. -/
  work_precision :
    Algorithm1Precision η y work

  /-- Shor begins in `|0⋯0⟩` on all registers it uses. -/
  clean_input :
    ShorCleanInput qs x y work flag b0

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
  (inst : ShorOrderFindingInstance)
  (ψ0 : qs.State)
  (hψ0 : ‖ψ0‖ = 1) :
  probability_of_success (qs := qs) (T := T)
    (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
    (x := inst.x) (r := ord inst.a inst.N inst.coprime)
    (Q := 2^(regSize inst.x))
    (evalC := qs.eval)
    (C := orderFindingIdeal (qs := qs) inst.a inst.N inst.x inst.y)
    (ψ := ψ0)
  ≥ κ / (Nat.log2 inst.N : ℝ)^4 := by
  sorry

omit [MeasureClass qs] [ContinuedFractionPost] [Spec] [ExtRegEncoding qs.Basis] in
lemma qubit_toNat_eq_zero_of_bit_false
    {q : ℕ} {b : qs.Basis}
    (hbit : RegEncoding.bit q b = false) :
    RegEncoding.toNat (qubitReg q) b = 0 := by
  have hlt :
      RegEncoding.toNat (qubitReg q) b < 2 := by
    simpa [ASize, regSize, qubitReg] using
      RegEncoding.toNat_lt_ASize (qubitReg q) b
  have hbit_toNat :
      false = Nat.testBit (RegEncoding.toNat (qubitReg q) b) 0 := by
    calc
      false = RegEncoding.bit q b := hbit.symm
      _ = Nat.testBit (RegEncoding.toNat (qubitReg q) b) (q - (qubitReg q).lo) := by
        exact RegEncoding.bit_eq_testBit_toNat
          (r := qubitReg q) (b := b) (q := q)
          (by simp [qubitReg])
          (by simp [qubitReg, Reg.hi])
      _ = Nat.testBit (RegEncoding.toNat (qubitReg q) b) 0 := by
        simp [qubitReg]
  have hcases :
      RegEncoding.toNat (qubitReg q) b = 0 ∨
        RegEncoding.toNat (qubitReg q) b = 1 := by
    omega
  rcases hcases with hzero | hone
  · exact hzero
  · exfalso
    simp [hone] at hbit_toNat

omit [MeasureClass qs] [ContinuedFractionPost] [Spec] [ExtRegEncoding qs.Basis] in
lemma disjoint_of_forall_qubits_outside
    (x r : Reg)
    (hx : 0 < regSize x)
    (hr : 0 < regSize r)
    (hout :
      ∀ q : ℕ, x.lo ≤ q → q < x.hi → QubitOutside q r) :
    Disjoint x r := by
  by_contra hdisj
  simp [Disjoint] at hdisj
  by_cases hxr : x.lo ≤ r.lo
  · have hrlo_xhi : r.lo < x.hi := by
      simpa [Reg.hi] using hdisj.1
    have hrlo_rhi : r.lo < r.hi := by
      simp [Reg.hi, regSize] at hr ⊢
      omega
    rcases hout r.lo hxr hrlo_xhi with hleft | hright
    · exact (Nat.lt_irrefl r.lo hleft).elim
    · omega
  · have hrx : r.lo ≤ x.lo := by omega
    have hxlo_xhi : x.lo < x.hi := by
      simp [Reg.hi, regSize] at hx ⊢
      omega
    have hxlo_rhi : x.lo < r.hi := by
      simpa [Reg.hi] using hdisj.2
    rcases hout x.lo (le_rfl) hxlo_xhi with hleft | hright
    · omega
    · omega

omit [MeasureClass qs] [ContinuedFractionPost] [Spec] [ExtRegEncoding qs.Basis] in
lemma disjoint_of_forall_qubits_ne
    (x : Reg) (q₀ : ℕ)
    (hx : 0 < regSize x)
    (hne :
      ∀ q : ℕ, x.lo ≤ q → q < x.hi → q ≠ q₀) :
    Disjoint x (qubitReg q₀) := by
  apply disjoint_of_forall_qubits_outside
  · exact hx
  · simp [qubitReg, regSize]
  · intro q hqlo hqhi
    unfold QubitOutside
    have hne' := hne q hqlo hqhi
    simp [qubitReg, Reg.hi]
    omega

omit [ContinuedFractionPost] [Spec] in
/--
After Shor's Hadamards on `x` and initialization of `y` to `1`,
the state is a valid input for modular exponentiation.

This must be proved from `hsetup.clean_input`, `hsetup.register_layout`,
the `H_reg` expansion/locality theorem, and the semantics of `Gate.X`.
-/
lemma ShorApproxSetup.prepared_state_valid
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {η : ℝ}
    {a N : ℕ}
    {x y work : Reg}
    {flag : ℕ}
    {b0 : qs.Basis}
    (ha : 0 < a ∧ a < N)
    (hxpos : 0 < regSize x)
    (hn : regSize y = Nat.log2 (2 * N))
    (hsetup : ShorApproxSetup qs η a N x y work flag b0) :
    qs.eval (initY1 y) (qs.eval (H_reg x) (qs.ket b0))
      ∈ ValidModMulState qs N y work flag := by
  classical
  rcases hsetup.clean_input with
    ⟨hx0, hy0, hcarry_bit, hwork0, hflag_bit⟩

  have hN : 1 < N := by
    omega

  have hypos : 0 < regSize y := by
    have harg_ne : 2 * N ≠ 0 := by omega
    have hle_log : 1 ≤ Nat.log2 (2 * N) := by
      rw [Nat.le_log2 harg_ne]
      have hN_ge_two : 2 ≤ N := by omega
      omega
    rw [hn]
    omega

  have hy_one_lt : 1 < ASize y := by
    have : regSize y ≠ 0 := Nat.ne_of_gt hypos
    simpa [ASize] using this

  have hy_one_lt_cap : 1 < ASize y := hy_one_lt

  have hLayoutTail :
      ModExpTailLayout x y work flag x.lo (tbits x) := by
    simpa [ModExpLayout] using hsetup.register_layout
  rcases hLayoutTail with ⟨_hxlo, _hxhi, hcontrols⟩

  have hcore0 : ModMulCoreLayout y work flag x.lo := by
    simpa [tbits] using hcontrols 0 (by simpa [tbits] using hxpos)

  rcases hcore0 with
    ⟨hext_work, hflag_ext, _hflag_work, _hctrl_ext0, _hctrl_work0, _hctrl_ne0⟩

  have hwork_y : Disjoint work y := by
    rcases hext_work with h | h
    · right
      exact le_trans
        (show y.hi ≤ (extendHi y).hi by simp [extendHi, Reg.hi])
        h
    · left
      simpa [extendHi] using h

  have hcarry_y : Disjoint (qubitReg y.hi) y := by
    right
    simp [qubitReg]

  have hflag_y : Disjoint (qubitReg flag) y := by
    unfold QubitOutside at hflag_ext
    rcases hflag_ext with h | h
    · left
      change flag + 1 ≤ y.lo
      exact Nat.succ_le_of_lt h
    · right
      exact le_trans
        (show y.hi ≤ (extendHi y).hi by simp [extendHi, Reg.hi])
        h

  have hx_ext : Disjoint x (extendHi y) := by
    apply disjoint_of_forall_qubits_outside
    · exact hxpos
    · simp [extendHi, regSize]
    · intro q hqlo hqhi
      let j : ℕ := q - x.lo
      have hj : j < tbits x := by
        have hqhi' : q < x.lo + regSize x := by
          simpa [Reg.hi, regSize] using hqhi
        dsimp [j, tbits]
        omega
      have hq_eq : x.lo + j = q := by
        dsimp [j]
        omega
      have hcore := hcontrols j hj
      rcases hcore with ⟨_, _, _, hctrl_ext, _, _⟩
      simpa [hq_eq] using hctrl_ext

  have hy_x : Disjoint y x := by
    rcases hx_ext with h | h
    · right
      simpa [extendHi] using h
    · left
      exact le_trans
        (show y.hi ≤ (extendHi y).hi by simp [extendHi, Reg.hi])
        h

  have hcarry_x : Disjoint (qubitReg y.hi) x := by
    rcases hx_ext with h | h
    · right
      exact le_trans h (by simp [extendHi, qubitReg])
    · left
      simpa [extendHi, qubitReg, Reg.hi] using h

  have hwork_x_of_pos : 0 < regSize work → Disjoint work x := by
    intro hwork_pos
    have hx_work : Disjoint x work := by
      apply disjoint_of_forall_qubits_outside
      · exact hxpos
      · exact hwork_pos
      · intro q hqlo hqhi
        let j : ℕ := q - x.lo
        have hj : j < tbits x := by
          have hqhi' : q < x.lo + regSize x := by
            simpa [Reg.hi, regSize] using hqhi
          dsimp [j, tbits]
          omega
        have hq_eq : x.lo + j = q := by
          dsimp [j]
          omega
        have hcore := hcontrols j hj
        rcases hcore with ⟨_, _, _, _, hctrl_work, _⟩
        simpa [hq_eq] using hctrl_work
    rcases hx_work with h | h
    · right
      exact h
    · left
      exact h

  have hflag_x : Disjoint (qubitReg flag) x := by
    have hx_flag : Disjoint x (qubitReg flag) := by
      apply disjoint_of_forall_qubits_ne
      · exact hxpos
      · intro q hqlo hqhi
        let j : ℕ := q - x.lo
        have hj : j < tbits x := by
          have hqhi' : q < x.lo + regSize x := by
            simpa [Reg.hi, regSize] using hqhi
          dsimp [j, tbits]
          omega
        have hq_eq : x.lo + j = q := by
          dsimp [j]
          omega
        have hcore := hcontrols j hj
        rcases hcore with ⟨_, _, _, _, _, hctrl_ne⟩
        simpa [hq_eq] using hctrl_ne
    rcases hx_flag with h | h
    · right
      exact h
    · left
      exact h

  let validSet : Set qs.State :=
    { ψ : qs.State |
      ∃ b : qs.Basis,
        GoodModMulBasisInput qs N y work flag b ∧
        ψ = qs.ket b }

  have hH_expansion :
      ∃ β : Fin (ASize x) → ℂ,
        qs.eval (H_reg x) (qs.ket b0)
          =
        ∑ t : Fin (ASize x),
          β t • qs.ket (RegEncoding.writeNat x t.1 b0) := by
    rcases RegisterHadamardSemantics.eval_Hreg_ket
        (qs := qs) x b0 with ⟨β, hβ⟩
    refine ⟨β, ?_⟩
    simpa [H_reg] using hβ

  rcases hH_expansion with ⟨β, hβ⟩

  change
    qs.eval (initY1 y) (qs.eval (H_reg x) (qs.ket b0))
      ∈ Submodule.span ℂ validSet

  rw [hβ]
  have hsum_eval :
      qs.eval (initY1 y)
          (∑ t : Fin (ASize x),
            β t • qs.ket (RegEncoding.writeNat x t.1 b0))
        =
      ∑ t : Fin (ASize x),
        qs.eval (initY1 y)
          (β t • qs.ket (RegEncoding.writeNat x t.1 b0)) := by
    simpa using
      eval_finset_sum
        qs
        (initY1 y)
        Finset.univ
        (fun t : Fin (ASize x) =>
          β t • qs.ket (RegEncoding.writeNat x t.1 b0))
  rw [hsum_eval]

  apply Submodule.sum_mem
  intro t _ht
  rw [qs.eval_smul]
  apply (Submodule.span ℂ validSet).smul_mem

  let b : qs.Basis := RegEncoding.writeNat x t.1 b0

  have hy_b : RegEncoding.toNat y b = 0 := by
    calc
      RegEncoding.toNat y b
          = RegEncoding.toNat y b0 := by
            simpa [b] using
              RegEncoding.toNat_left_write_right y x hy_x b0 t.1
      _ = 0 := hy0

  have hwork_b : RegEncoding.toNat work b = 0 := by
    by_cases hwork_zero : regSize work = 0
    · have hlt := RegEncoding.toNat_lt_ASize work b
      simp [ASize, hwork_zero] at hlt
      omega
    · have hwork_pos : 0 < regSize work := Nat.pos_of_ne_zero hwork_zero
      calc
        RegEncoding.toNat work b
            = RegEncoding.toNat work b0 := by
              simpa [b] using
                RegEncoding.toNat_left_write_right
                  work x (hwork_x_of_pos hwork_pos) b0 t.1
        _ = 0 := hwork0

  have hcarry_b :
      RegEncoding.toNat (qubitReg y.hi) b = 0 := by
    calc
      RegEncoding.toNat (qubitReg y.hi) b
          = RegEncoding.toNat (qubitReg y.hi) b0 := by
            simpa [b] using
              RegEncoding.toNat_left_write_right
                (qubitReg y.hi) x hcarry_x b0 t.1
      _ = 0 := qubit_toNat_eq_zero_of_bit_false (qs := qs) hcarry_bit

  have hflag_b :
      RegEncoding.toNat (qubitReg flag) b = 0 := by
    calc
      RegEncoding.toNat (qubitReg flag) b
          = RegEncoding.toNat (qubitReg flag) b0 := by
            simpa [b] using
              RegEncoding.toNat_left_write_right
                (qubitReg flag) x hflag_x b0 t.1
      _ = 0 := qubit_toNat_eq_zero_of_bit_false (qs := qs) hflag_bit

  have hinit :
      qs.eval (initY1 y) (qs.ket b)
        =
      qs.ket (RegEncoding.writeNat y 1 b) := by
    simpa [initY1] using
      PauliXSemantics.eval_X_low_zero_reg_ket
        (qs := qs) y b hypos hy_b

  rw [hinit]
  apply Submodule.subset_span
  refine ⟨RegEncoding.writeNat y 1 b, ?_, rfl⟩

  have hdata_out :
      RegEncoding.toNat y (RegEncoding.writeNat y 1 b) = 1 := by
    exact RegEncoding.toNat_writeNat_of_lt y 1 b hy_one_lt_cap

  have hcarry_out :
      RegEncoding.toNat (qubitReg y.hi)
          (RegEncoding.writeNat y 1 b) = 0 := by
    calc
      RegEncoding.toNat (qubitReg y.hi)
          (RegEncoding.writeNat y 1 b)
          = RegEncoding.toNat (qubitReg y.hi) b := by
            exact
              RegEncoding.toNat_left_write_right
                (qubitReg y.hi) y hcarry_y b 1
      _ = 0 := hcarry_b

  have hwork_out :
      RegEncoding.toNat work (RegEncoding.writeNat y 1 b) = 0 := by
    calc
      RegEncoding.toNat work (RegEncoding.writeNat y 1 b)
          = RegEncoding.toNat work b := by
            exact RegEncoding.toNat_left_write_right work y hwork_y b 1
      _ = 0 := hwork_b

  have hflag_out :
      RegEncoding.toNat (qubitReg flag)
          (RegEncoding.writeNat y 1 b) = 0 := by
    calc
      RegEncoding.toNat (qubitReg flag)
          (RegEncoding.writeNat y 1 b)
          = RegEncoding.toNat (qubitReg flag) b := by
            exact
              RegEncoding.toNat_left_write_right
                (qubitReg flag) y hflag_y b 1
      _ = 0 := hflag_b

  refine ⟨?_, hcarry_out, hwork_out, hflag_out⟩
  calc
    RegEncoding.toNat y (RegEncoding.writeNat y 1 b) = 1 := hdata_out
    _ < N := hN

omit [ContinuedFractionPost] [Spec] in
lemma shor_data_capacity_from_log2
    (N : ℕ) :
    N ≤ 2 ^ Nat.log2 (2 * N) := by
  rcases N with _ | N
  · simp
  · have hlt :
        2 * (N + 1) < 2 ^ (Nat.log 2 (2 * (N + 1))).succ := by
      exact Nat.lt_pow_succ_log_self Nat.one_lt_two (2 * (N + 1))
    rw [← Nat.log2_eq_log_two] at hlt
    rw [Nat.pow_succ] at hlt
    have hdouble_le :
        (N + 1) * 2 ≤ 2 ^ Nat.log2 (2 * (N + 1)) * 2 := by
      simpa [Nat.mul_comm] using hlt.le
    exact Nat.le_of_mul_le_mul_right hdouble_le (by norm_num : 0 < 2)

def ShorApproxSetup.toModExpConfig
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    {a N : ℕ}
    {y : Reg}
    {η : ℝ}
    {x work : Reg}
    {flag : ℕ}
    {b0 : qs.Basis}
    (ha : 0 < a ∧ a < N)
    (hgcd : Nat.gcd a N = 1)
    (hn : regSize y = Nat.log2 (2 * N))
    (hsetup : ShorApproxSetup qs η a N x y work flag b0) :
    ModExpConfig η := by
  have hN : 1 < N := by
    omega
  have hcapacity : N ≤ ASize y := by
    simpa [ASize, hn] using shor_data_capacity_from_log2 N
  have hcoprime : Nat.Coprime a N := by
    rw [Nat.coprime_iff_gcd_eq_one]
    exact hgcd
  refine
    { env :=
        { N := N
          data := y
          work := work
          modulus_gt_one := hN
          data_capacity := hcapacity
          precision := hsetup.work_precision }
      a := a
      x := x
      flag := flag
      layout := hsetup.register_layout
      arithmetic := ?_ }
  intro j hj
  dsimp
  exact modExp_tail_coprime a N x x.lo (tbits x) hcoprime j hj

/--
Uniform approximate Shor order-finding bound.

`K` is chosen before `η`, so it is independent of the precision parameter.
It may depend on the fixed instance data `qs`, `T`, `a`, `N`, `x`, `y`,
`w`, `flag`, `b0`, and the fixed size/arithmetic hypotheses.
-/
theorem Shor_correct_approx_uniform
    [GateSemanticsFacts qs]
    [IdealCtrlModMulExactSemantics qs]
    [ModMulPrimitiveSemantics qs]
    (T : ℕ → ℕ)
    (inst : ShorOrderFindingInstance)
    (w : Reg)
    (flag : ℕ)
    (b0 : qs.Basis) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (η : ℝ)
        (_hS: ShorApproxSetup qs η inst.a inst.N inst.x inst.y w flag b0),
        probability_of_success (qs := qs) (T := T)
          (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
          (x := inst.x)
          (r := ord inst.a inst.N inst.coprime)
          (Q := 2 ^ regSize inst.x)
          (evalC := qs.eval)
          (C := orderFindingApprox (qs := qs) inst.a inst.N inst.x inst.y w flag)
          (ψ := qs.ket b0)
        ≥
          κ / (Nat.log2 inst.N : ℝ)^4
            - 2 * (tbits inst.x : ℝ) * Real.sqrt (2 * (K * η)) := by
  classical
  let a := inst.a
  let N := inst.N
  let x := inst.x
  let y := inst.y
  have ha : 0 < a ∧ a < N := inst.range
  have hgcd : Nat.gcd a N = 1 := inst.coprime
  have hm : regSize x = Nat.log2 (2 * N^2) := inst.x_width
  have hn : regSize y = Nat.log2 (2 * N) := inst.y_width

  rcases modExpApprox_valid_dist_uniform (qs := qs) with
    ⟨K, hK_nonneg, hmodExp⟩

  refine ⟨K, hK_nonneg, ?_⟩
  intro η hsetup

  let cfg : ModExpConfig η :=
    ShorApproxSetup.toModExpConfig ha hgcd hn hsetup

  let ψpre : qs.State :=
    qs.eval (initY1 y) (qs.eval (H_reg x) (qs.ket b0))

  have hxpos : 0 < regSize x := by
    have harg_ne : 2 * N ^ 2 ≠ 0 := by
      have hNpos : 0 < N := by
        omega
      positivity

    have hle_log : 1 ≤ Nat.log2 (2 * N ^ 2) := by
      rw [Nat.le_log2 harg_ne]
      have hNsq_pos : 0 < N ^ 2 := by
        have hNpos : 0 < N := by
          omega
        positivity
      exact Nat.mul_le_mul_left 2 hNsq_pos

    rw [hm]
    omega

  have hpreValid :
      ψpre ∈ ValidModMulState qs N y w flag := by
    simpa [ψpre] using
      (ShorApproxSetup.prepared_state_valid
        (qs := qs)
        ha
        hxpos
        hn
        hsetup)

  have hpreUnit : ‖ψpre‖ = 1 := by
    dsimp [ψpre]
    calc
      ‖qs.eval (initY1 y) (qs.eval (H_reg x) (qs.ket b0))‖
          =
          ‖qs.eval (H_reg x) (qs.ket b0)‖ := by
            simpa using
              (eval_norm_preserved qs
                (initY1 y)
                (qs.eval (H_reg x) (qs.ket b0)))
      _ = ‖qs.ket b0‖ := by
            simpa using
              (eval_norm_preserved qs (H_reg x) (qs.ket b0))
      _ = 1 := ket_norm_one qs b0

  have hpre :
      ModExpConfig.ValidUnitState qs cfg ψpre := by
    simpa [
      ModExpConfig.ValidUnitState,
      cfg,
      ShorApproxSetup.toModExpConfig
    ] using
      (And.intro hpreValid hpreUnit)

  let ε : ℝ := (tbits x : ℝ) * stepErr K η

  have hmid :
      ‖qs.eval
          (modExpApproxValid
            (Basis := qs.Basis)
            a N x y w flag)
          ψpre
        -
        qs.eval (modExpIdeal' (qs := qs) a N x y) ψpre‖
      ≤ ε := by
    simpa [
      ε,
      cfg,
      ShorApproxSetup.toModExpConfig,
      ModExpConfig.approxGate,
      ModExpConfig.idealGate
    ] using
      (hmodExp η cfg ψpre hpre)

  have hpost :
      ‖qs.eval (Gate.QFT x)
          (qs.eval
            (modExpApproxValid
              (Basis := qs.Basis)
              a N x y w flag)
            ψpre)
        -
        qs.eval (Gate.QFT x)
          (qs.eval (modExpIdeal' (qs := qs) a N x y) ψpre)‖
      ≤ ε := by
    exact dist_eval_common_suffix_le
      (qs := qs)
      (Gate.QFT x)
      (modExpApproxValid
        (Basis := qs.Basis)
        a N x y w flag)
      (modExpIdeal' (qs := qs) a N x y)
      ψpre
      hmid

  have hdist_full :
      ‖qs.eval
          (orderFindingApprox (qs := qs) a N x y w flag)
          (qs.ket b0)
        -
        qs.eval
          (orderFindingIdeal (qs := qs) a N x y)
          (qs.ket b0)‖
      ≤ ε := by
    simpa [
      orderFindingApprox,
      orderFindingIdeal,
      ψpre,
      qs.eval_seq
    ] using hpost

  let verify : ℕ → Bool :=
    fun d => decide ((a ^ d) % N = 1)

  let r : ℕ := ord a N hgcd
  let Q : ℕ := 2 ^ regSize x

  have htransfer :
      probability_of_success (qs := qs) (T := T)
        (verify := verify)
        (x := x) (r := r) (Q := Q)
        (evalC := qs.eval)
        (C := orderFindingApprox (qs := qs) a N x y w flag)
        (ψ := qs.ket b0)
      ≥
      probability_of_success (qs := qs) (T := T)
        (verify := verify)
        (x := x) (r := r) (Q := Q)
        (evalC := qs.eval)
        (C := orderFindingIdeal (qs := qs) a N x y)
        (ψ := qs.ket b0)
      - 2 * ε := by
    exact probability_of_success_eval_dist
      (qs := qs)
      T
      verify
      x
      r
      Q
      (orderFindingApprox (qs := qs) a N x y w flag)
      (orderFindingIdeal (qs := qs) a N x y)
      (qs.ket b0)
      ε
      (ket_norm_one qs b0)
      hdist_full

  have hideal :
      probability_of_success (qs := qs) (T := T)
        (verify := verify)
        (x := x) (r := r) (Q := Q)
        (evalC := qs.eval)
        (C := orderFindingIdeal (qs := qs) a N x y)
        (ψ := qs.ket b0)
      ≥ κ / (Nat.log2 N : ℝ)^4 := by
    simpa [verify, r, Q] using
      (Shor_correct
        (qs := qs)
        T
        inst
        (qs.ket b0)
        (ket_norm_one qs b0))

  calc
    probability_of_success (qs := qs) (T := T)
        (verify := fun d => decide ((a ^ d) % N = 1))
        (x := x)
        (r := ord a N hgcd)
        (Q := 2 ^ regSize x)
        (evalC := qs.eval)
        (C := orderFindingApprox (qs := qs) a N x y w flag)
        (ψ := qs.ket b0)
      ≥
        probability_of_success (qs := qs) (T := T)
          (verify := verify)
          (x := x)
          (r := r)
          (Q := Q)
          (evalC := qs.eval)
          (C := orderFindingIdeal (qs := qs) a N x y)
          (ψ := qs.ket b0)
        - 2 * ε := by
          simpa [verify, r, Q] using htransfer
    _ ≥
        κ / (Nat.log2 N : ℝ)^4 - 2 * ε := by
          exact sub_le_sub_right hideal (2 * ε)
    _ =
        κ / (Nat.log2 N : ℝ)^4
          - 2 * (tbits x : ℝ) *
              Real.sqrt (2 * (K * η)) := by
          simp [ε, stepErr, mul_assoc]

omit [Spec] in
/--
Lowering preserves the order-finding success probability exactly.
-/
lemma probability_of_success_lowerGate_eq
    [ExtRegSplitSemantics qs.Basis]
    [LowerGateClass qs]
    [GateSemanticsFacts qs]
    (k : ℕ) (hk : 1 < k)
    (ops : Prog k)
    (hC : ProgConsumesPtsSafe
      (k := k) (by omega)
      State.start_state ops
      (genInterpolationPoints k))
    (hRun : run? ops State.start_state = some State.start_state)
    (T : ℕ → ℕ)
    (verify : OrderVerifier)
    (x : Reg)
    (r Q : ℕ)
    (G : Gate)
    (hGeom : GateGeomOK G)
    (ψ : qs.State) :
    probability_of_success
        (qs := qs)
        (evalC := LowerGateClass.evalL (qs := qs))
        (T := T)
        (verify := verify)
        (x := x) (r := r) (Q := Q)
        (C := lowerGate (Basis := qs.Basis) k hk ops G)
        (ψ := ψ)
      =
    probability_of_success
        (qs := qs)
        (evalC := qs.eval)
        (T := T)
        (verify := verify)
        (x := x) (r := r) (Q := Q)
        (C := G)
        (ψ := ψ) := by
  have hEval :
      LowerGateClass.evalL
          (qs := qs)
          (lowerGate (Basis := qs.Basis) k hk ops G)
          ψ
        =
      qs.eval G ψ :=
    lowerGate_correctness
      (k := k)
      (hk := hk)
      G
      hGeom
      qs
      (inferInstance : RegEncoding qs.Basis)
      ops
      hC
      hRun
      ψ

  unfold probability_of_success measProbAfter
  apply Finset.sum_congr rfl
  intro o ho
  rw [hEval]

theorem Shor_correct_approx_uniform_low
    [GateSemanticsFacts qs] [IdealCtrlModMulExactSemantics qs] [ModMulPrimitiveSemantics qs]
    [ExtRegSplitSemantics qs.Basis] [LowerGateClass qs]
    (low : ShorLoweringSetup)
    (T : ℕ → ℕ)
    (inst : ShorOrderFindingInstance)
    (w : Reg)
    (flag : ℕ)
    (b0 : qs.Basis)
    (hGeom : GateGeomOK (orderFindingApprox (qs := qs) inst.a inst.N inst.x inst.y w flag)) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (η : ℝ),
        (hsetup : ShorApproxSetup qs η inst.a inst.N inst.x inst.y w flag b0) →
        probability_of_success
            (evalC := LowerGateClass.evalL (qs := qs)) (T := T)
            (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
            (x := inst.x) (r := ord inst.a inst.N inst.coprime) (Q := 2 ^ regSize inst.x)
            (C := orderFindingApproxLow qs low.k low.hk low.ops inst.a inst.N inst.x inst.y w flag) (ψ := qs.ket b0)
          ≥
        κ / (Nat.log2 inst.N : ℝ)^4 - 2 * (tbits inst.x : ℝ) * Real.sqrt (2 * (K * η)) := by
  let a := inst.a
  let N := inst.N
  let x := inst.x
  let y := inst.y
  have hgcd : Nat.gcd a N = 1 := inst.coprime
  rcases Shor_correct_approx_uniform
      (qs := qs)
      T inst w flag b0 with
    ⟨K, hK, hHigh⟩

  refine ⟨K, hK, ?_⟩
  intro η hsetup

  calc
    probability_of_success
        (qs := qs)
        (evalC := LowerGateClass.evalL (qs := qs))
        (T := T)
        (verify := fun d => decide ((a ^ d) % N = 1))
        (x := x)
        (r := ord a N hgcd)
        (Q := 2 ^ regSize x)
        (C :=
          orderFindingApproxLow
            (qs := qs)
            low.k low.hk low.ops a N x y w flag)
        (ψ := qs.ket b0)
      =
    probability_of_success
        (qs := qs)
        (evalC := qs.eval)
        (T := T)
        (verify := fun d => decide ((a ^ d) % N = 1))
        (x := x)
        (r := ord a N hgcd)
        (Q := 2 ^ regSize x)
        (C := orderFindingApprox (qs := qs) a N x y w flag)
        (ψ := qs.ket b0) := by
          simpa [orderFindingApproxLow] using
            (probability_of_success_lowerGate_eq
              (qs := qs)
              low.k low.hk low.ops low.consumes low.returns
              T
              (fun d => decide ((a ^ d) % N = 1))
              x
              (ord a N hgcd)
              (2 ^ regSize x)
              (orderFindingApprox (qs := qs) a N x y w flag)
              hGeom
              (qs.ket b0))
    _ ≥
      κ / (Nat.log2 N : ℝ)^4
        - 2 * (tbits x : ℝ) *
            Real.sqrt (2 * (K * η)) :=
      hHigh η hsetup


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
(T : ℕ → ℕ)
(fact : ShorFactoringInstance)
(x y : Reg)
(ψ0 : qs.State)
(hψ0 : ‖ψ0‖ = 1)
(hm : regSize x = Nat.log2 (2 * fact.N^2))
(hn : regSize y = Nat.log2 (2 * fact.N))
(hset : ∀ a, a ∈ valid_choices fact.N →
  ∃ hgcd, BasicSetting a (ord a fact.N hgcd) fact.N (regSize x) (regSize y)) :
  (2 * (successful_choices fact.N).card ≥ (valid_choices fact.N).card)
  ∧
  (∀ a ∈ successful_choices fact.N,
    ∃ (hgcd : Nat.gcd a fact.N = 1),
    (probability_of_success (qs := qs) (T := T)
      (verify := fun d => decide ((a ^ d) % fact.N = 1))
      (x := x) (r := ord a fact.N hgcd) (Q := 2^(regSize x))
      (evalC := qs.eval)
      (C := orderFindingIdeal (qs := qs) a fact.N x y)
      (ψ := ψ0)
    ≥ κ / (Nat.log2 fact.N : ℝ)^4)
    ∧
    (is_nontrivial_factor (Nat.gcd ((a ^ (ord a fact.N hgcd / 2)) - 1) fact.N) fact.N ∨
     is_nontrivial_factor (Nat.gcd ((a ^ (ord a fact.N hgcd / 2)) + 1) fact.N) fact.N)) := by {
  let N := fact.N
  have h_odd : Odd N := fact.odd
  have h_N : N > 2 := fact.gt_two
  have h_not_prime_power : ∀ (p k : ℕ), Nat.Prime p → N ≠ p ^ k :=
    fact.not_prime_power
  constructor
  { exact shors_probability_bound N h_odd (by omega) h_not_prime_power }
  {
    intro a h_a_in_successful
    obtain ⟨⟨ha1, ha2⟩, hgcd⟩ := success_eq_conditions a N h_a_in_successful
    have hvalid_N : a ∈ valid_choices N := by
      simp [valid_choices, ha1, ha2, hgcd]
    have hvalid_fact : a ∈ valid_choices fact.N := by
      simpa [N] using hvalid_N
    obtain ⟨hgcd_set, hset_a⟩ := hset a hvalid_fact

    have h_succ : shor_success_conditions a (ord a N hgcd) N := by {
      have h_a_in_successful_N : a ∈ successful_choices N := by
        simpa [N] using h_a_in_successful
      have h_a_is_succ : is_successful_choice a N := by {
        unfold successful_choices at h_a_in_successful_N
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
    let inst : ShorOrderFindingInstance :=
      { a := a
        N := N
        x := x
        y := y
        range := ⟨by omega, ha2⟩
        coprime := hgcd
        x_width := hm
        y_width := hn
        order_setting := by
          simpa using hset_a }
    exact ⟨
      Shor_correct T inst ψ0 hψ0,
      shors_classical_reduction a (ord a N hgcd) N h_N ⟨ha1, ha2⟩ hgcd (is_period_ord a N hgcd) h_succ
    ⟩
  }
}
