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
  (qs : QSemantics) [RegEncoding qs.Basis] [Spec] [ExtRegEncoding QSemantics.Basis] [ModMul qs]
  (a N : ℕ) (x y w_reg : Reg) (flag : ℕ) : Gate :=
  (H_reg x) ;;
  (initY1 y) ;;
  (modExpApprox' (qs := qs) a N x y w_reg flag) ;;
  (Gate.QFT x)

/-- Approximate (in-place) quantum order-finding circuit. -/
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

    `MeasureClass` abstracts measurement probabilities, while the lemmas below
    record the basic monotonicity and range facts used by the final statement.
========================================================= -/

/--Modelling “measurement”-/
class MeasureClass (qs : QSemantics) [RegEncoding qs.Basis] where
  probMeas : (r : Reg) → (o : ℕ) → qs.State → ℝ

  probMeas_nonneg : ∀ r o ψ, 0 ≤ probMeas r o ψ

  probMeas_outOfRange : ∀ r o ψ, (2^(regSize r) ≤ o) → probMeas r o ψ = 0

  probMeas_total :
    ∀ r (ψ : qs.State),
      ‖ψ‖ = 1 →
      (∑ o : Fin (2^(regSize r)), probMeas r o.1 ψ) = 1



variable [MeasureClass qs]

/-- Run the circuit G on input state ψ, then measure register r, and ask for probability of outcome o -/
noncomputable def measProbAfter (r : Reg) (o : ℕ) (G : Gate) (ψ : qs.State) : ℝ :=
  MeasureClass.probMeas (qs := qs) r o (qs.eval G ψ)

/-- Given a finite set Good of outcomes that are “successful,” sum the measurement probability over those outcomes. -/
noncomputable def successProbAfterFinset
  (r : Reg) (Good : Finset ℕ) (G : Gate) (ψ : qs.State) : ℝ :=
  ∑ o ∈ Good, measProbAfter (qs := qs) r o G ψ

/--Success probability is nonnegative.-/
lemma successProbAfterFinset_nonneg
  (r : Reg) (Good : Finset ℕ) (G : Gate) (ψ : qs.State) :
  0 ≤ successProbAfterFinset (qs := qs) r Good G ψ := by
  unfold successProbAfterFinset measProbAfter
  refine Finset.sum_nonneg ?_
  intro o ho
  have : 0 ≤ MeasureClass.probMeas (qs := qs) r o (qs.eval G ψ) := by
    simpa using (MeasureClass.probMeas_nonneg (qs := qs) r o (qs.eval G ψ))
  simpa using this

/-- If the “good outcomes” set is enlargened, success probability can only go up -/
lemma successProbAfterFinset_mono
  (r : Reg) {Good Good' : Finset ℕ} (hsub : Good ⊆ Good')
  (G : Gate) (ψ : qs.State) :
  successProbAfterFinset (qs := qs) r Good G ψ
    ≤
  successProbAfterFinset (qs := qs) r Good' G ψ := by
  unfold successProbAfterFinset
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
  intro o ho hnot
  unfold measProbAfter
  simpa using (MeasureClass.probMeas_nonneg (qs := qs) r o (qs.eval G ψ))

lemma successProbAfterFinset_inter_range_eq
  (r : Reg) (Good : Finset ℕ) (G : Gate) (ψ : qs.State) :
  successProbAfterFinset (qs := qs) r (Good ∩ Finset.range (2^(regSize r))) G ψ
    =
  successProbAfterFinset (qs := qs) r Good G ψ := by
  classical
  unfold successProbAfterFinset measProbAfter
  have :
      (∑ o ∈ Good ∩ Finset.range (2^(regSize r)),
          MeasureClass.probMeas (qs := qs) r o (qs.eval G ψ))
      =
      ∑ o ∈ Good,
        MeasureClass.probMeas (qs := qs) r o (qs.eval G ψ) := by
    have hdecomp :
        (∑ o ∈ Good,
            MeasureClass.probMeas (qs := qs) r o (qs.eval G ψ))
        =
        (∑ o ∈ (Good ∩ Finset.range (2^(regSize r))),
            MeasureClass.probMeas (qs := qs) r o (qs.eval G ψ))
        +
        (∑ o ∈ (Good \ Finset.range (2^(regSize r))),
            MeasureClass.probMeas (qs := qs) r o (qs.eval G ψ)) := by

      have:=(Finset.sum_inter_add_sum_diff (s := Good) (t := Finset.range (2^(regSize r)))
              (f := fun o => MeasureClass.probMeas (qs := qs) r o (qs.eval G ψ)))
      simp at *
      rw[← this]

    have hdiff0 :
        (∑ o ∈ (Good \ Finset.range (2^(regSize r))),
            MeasureClass.probMeas (qs := qs) r o (qs.eval G ψ)) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro o ho
      have ho_not_range : o ∉ Finset.range (2^(regSize r)) := by
        exact (Finset.mem_sdiff.mp ho).2
      have ho_ge : 2^(regSize r) ≤ o := by
        exact Nat.le_of_not_gt (by
          intro ho_lt
          exact ho_not_range (Finset.mem_range.mpr ho_lt))
      simpa using (MeasureClass.probMeas_outOfRange (qs := qs) r o (qs.eval G ψ) ho_ge)


    have := congrArg (fun t => t - (∑ o ∈ (Good \ Finset.range (2^(regSize r))),
        MeasureClass.probMeas (qs := qs) r o (qs.eval G ψ))) hdecomp
    calc
      (∑ o ∈ Good ∩ Finset.range (2^(regSize r)),
          MeasureClass.probMeas (qs := qs) r o (qs.eval G ψ))
          =
      (∑ o ∈ Good ∩ Finset.range (2^(regSize r)),
          MeasureClass.probMeas (qs := qs) r o (qs.eval G ψ)) + 0 := by simp
      _ =
      (∑ o ∈ Good ∩ Finset.range (2^(regSize r)),
          MeasureClass.probMeas (qs := qs) r o (qs.eval G ψ))
        +
      (∑ o ∈ (Good \ Finset.range (2^(regSize r))),
          MeasureClass.probMeas (qs := qs) r o (qs.eval G ψ)) := by simp [hdiff0]
      _ =
      (∑ o ∈ Good,
          MeasureClass.probMeas (qs := qs) r o (qs.eval G ψ)) := by
          symm
          exact hdecomp
  simp[this]

variable [ContinuedFractionPost] [Spec]
variable [ExtRegEncoding qs.Basis]
variable [ModMul qs]

noncomputable def probability_of_success
  (T : ℕ → ℕ) (verify : OrderVerifier)
  (x : Reg) (r Q : ℕ) (G : Gate) (ψ : qs.State) : ℝ :=
  ∑ o : Fin Q,
    (r_found (T := T) verify o.1 Q r) *
      (measProbAfter (qs := qs) x o.1 G ψ)
/-! =========================================================
    Section 3: Final correctness statement

    This is the top-level theorem shape: the ideal order-finding circuit has
    at least the standard inverse-polylogarithmic success probability.
========================================================= -/

/-- Shor/order-finding correctness statement -/
theorem Shor_correct
  (T : ℕ → ℕ)
  (a N : ℕ)
  (ha : 0 < a ∧ a < N)
  (hgcd : Nat.gcd a N = 1)
  (x y w : Reg) (flag : ℕ)
  (ψ0 : qs.State)
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

-- Theorem stating that there is a 1/2 chance of a randomly selected 'a' being a successful choice
omit [ContinuedFractionPost] [Spec] in
theorem shors_probability_bound (N : ℕ)
(h_odd : Odd N)
(h_gt_one : N > 1)
(h_not_prime_power : ∀ (p k : ℕ), Nat.Prime p → N ≠ p ^ k) :
2 * (successful_choices N).card ≥ (valid_choices N).card := by {
  -- Step 1: Extract two distinct prime factors
  obtain ⟨p, q, hp, hq, hpq, hpN, hqN⟩ := exists_two_distinct_prime_factors h_gt_one h_not_prime_power
  -- Step 2: Both primes are odd (since N is odd and p, q ∣ N)
  have hp2 : p ≠ 2 := by
    rintro rfl; obtain ⟨k, hk⟩ := h_odd; obtain ⟨m, hm⟩ := hpN; omega
  have hq2 : q ≠ 2 := by
    rintro rfl; obtain ⟨k, hk⟩ := h_odd; obtain ⟨m, hm⟩ := hqN; omega
  -- Step 3: Counting
  have hvc := valid_choices_card_general h_gt_one
  -- Partition coprime residues into successful and unsuccessful
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
  -- successful_choices = S.filter(successful) (a=0 not coprime, a=1 not successful)
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

/-- Shor/order-finding correctness statement -/
theorem Shor_end_to_end_factoring
(T : ℕ → ℕ) (N : ℕ)
(h_odd : Odd N)
(h_N : N > 2)
(h_not_prime_power : ∀ (p k : ℕ), Nat.Prime p → N ≠ p ^ k)
(x y w : Reg) (flag : ℕ)
(ψ0 : qs.State)
(hm : regSize x = Nat.log2 (2 * N^2))
(hn : regSize y = Nat.log2 (2 * N))
(hset : ∀ a, a ∈ valid_choices N →
  ∃ hgcd, BasicSetting a (ord a N hgcd) N (regSize x) (regSize y)) :
  -- Classical probability bound (probability of successful 'a' ≥ 1/2)
  (2 * (successful_choices N).card ≥ (valid_choices N).card)
  ∧
  -- For every successful 'a', the quantum order-finding and classical reduction are correct
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
    -- Extract successful conditions
    obtain ⟨⟨ha1, ha2⟩, hgcd⟩ := success_eq_conditions a N h_a_in_successful
    obtain ⟨hgcd_set, hset_a⟩ := hset a (by simp [valid_choices, ha1, ha2, hgcd])
    -- State that 'a' meets the success conditions
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
      Shor_correct T a N ⟨by omega, ha2⟩ hgcd x y w flag ψ0 hm hn hset_a,
      shors_classical_reduction a (ord a N hgcd) N h_N ⟨ha1, ha2⟩ hgcd (is_period_ord a N hgcd) h_succ
    ⟩
  }
}


/-! =========================================================
    Section 3: Probability-transfer lemmas
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
/-- Applying the same post-unitary/post-gate to both states does not increase
    their distance.

    This is the formal version of:

        ‖W A ψ - W I ψ‖ = ‖A ψ - I ψ‖.

    So any distance bound immediately after `ModExp` survives through the
    later common gates, such as inverse QFT.
-/
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

lemma probMeas_weighted_dist [MeasureClass qs]:
    ∀ (r : Reg) (Q : ℕ) (w : Fin Q → ℝ) (ψ φ : qs.State),
      (∀ o, 0 ≤ w o ∧ w o ≤ 1) →
      ‖ψ‖ = 1 →
      ‖φ‖ = 1 →
      |(∑ o : Fin Q, w o * MeasureClass.probMeas r o.1 ψ)
        -
        (∑ o : Fin Q, w o * MeasureClass.probMeas r o.1 φ)|
      ≤ 2 * ‖ψ - φ‖:= by sorry

lemma probability_of_success_eval_dist
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

omit [RegEncoding QSemantics.Basis] [MeasureClass qs] [ContinuedFractionPost] [Spec] [ExtRegEncoding QSemantics.Basis] [ModMul qs] in
lemma eval_common_gate_dist_eq
    (W : Gate) (ψ φ : qs.State) :
    ‖qs.eval W ψ - qs.eval W φ‖ = ‖ψ - φ‖ := by
  simpa using
    (eval_isometry qs W
      (by
        intro ψ φ
        simpa using qs.inner_preserved W ψ φ)
      ψ φ)

omit [RegEncoding QSemantics.Basis] [MeasureClass qs] [ContinuedFractionPost] [Spec] [ExtRegEncoding QSemantics.Basis] [ModMul qs] in
lemma eval_norm_preserved_from_inner
    (W : Gate) (ψ : qs.State) :
    ‖qs.eval W ψ‖ = ‖ ψ‖ := by
  have h :=
    eval_common_gate_dist_eq (qs := qs) W ψ 0
  simpa [qs.eval_zero W] using h

omit [RegEncoding QSemantics.Basis] [MeasureClass qs] [ContinuedFractionPost] [Spec] [ExtRegEncoding QSemantics.Basis] [ModMul qs] in
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

omit [RegEncoding QSemantics.Basis] [MeasureClass qs] [ContinuedFractionPost] [Spec] [ExtRegEncoding QSemantics.Basis] [ModMul qs] in
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

theorem Shor_correct_approx
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
      - 2 * (tbits x : ℝ) * stepErr K (ModMul.η (qs := qs)) := by
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
        T a N ha hgcd x y w flag ψ0 hm hn hset)

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
