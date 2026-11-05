import Mathlib.Data.List.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Weighted words and budget enumeration

Defines the branch count `q`, the weight `1 / q^10` of a branch label, and the enumeration `budgetWords` of words under a budget. Proves the weighted-sum estimate `quotaWeightSum_le`, length bounds on `budgetWords`, and that the enumeration is sound and complete (`budgetWords_sound`, `budgetWords_complete`).
-/

namespace Paper.CountStage.Decoration

def q (k : Nat) : Nat := 2 * k - 1
def B (k : Nat) : Nat := k ^ 2 * (27 * k ^ 3 + 1)

theorem q_ge_k_add_one {k : Nat} (hk : 2 ≤ k) : k + 1 ≤ q k := by
  simp [q]
  omega

theorem q_ge_three {k : Nat} (hk : 2 ≤ k) : 3 ≤ q k := by
  have h := q_ge_k_add_one hk
  omega

theorem B_le_28_pow5 {k : Nat} (hk : 2 ≤ k) : B k ≤ 28 * k ^ 5 := by
  have hk3 : 1 ≤ k ^ 3 := Nat.one_le_pow 3 k (by omega)
  dsimp [B]
  calc
    k ^ 2 * (27 * k ^ 3 + 1) ≤ k ^ 2 * (28 * k ^ 3) := by
      apply Nat.mul_le_mul_left
      omega
    _ = 28 * k ^ 5 := by ring

theorem B_le_28_qpow5 {k : Nat} (hk : 2 ≤ k) : B k ≤ 28 * q k ^ 5 := by
  have hB := B_le_28_pow5 hk
  have hq : k ≤ q k := by have := q_ge_k_add_one hk; omega
  have hp : k ^ 5 ≤ q k ^ 5 := Nat.pow_le_pow_left hq 5
  calc
    B k ≤ 28 * k ^ 5 := hB
    _ ≤ 28 * q k ^ 5 := Nat.mul_le_mul_left _ hp

theorem qpow5_ge_27_mul {k : Nat} (hk : 2 ≤ k) :
    27 * k * (k + 1) ≤ q k ^ 5 := by
  have hq := q_ge_k_add_one hk
  have hq3 : 27 ≤ q k ^ 3 := by
    simpa using Nat.pow_le_pow_left (q_ge_three hk) 3
  have hq2 : k * (k + 1) ≤ q k ^ 2 := by
    calc
      k * (k + 1) ≤ (k + 1) * (k + 1) := Nat.mul_le_mul_right _ (by omega)
      _ ≤ q k * q k := Nat.mul_le_mul hq hq
      _ = q k ^ 2 := by simp [pow_two]
  have hmul := Nat.mul_le_mul hq3 hq2
  simpa [Nat.mul_assoc, ← pow_add] using hmul

theorem B_weight_le_telescoping {k : Nat} (hk : 2 ≤ k) :
    (B k : ℚ) / (q k : ℚ) ^ 10 ≤
      (28 / 27 : ℚ) / ((k : ℚ) * (k + 1)) := by
  have hB : (B k : ℚ) ≤ 28 * (q k : ℚ) ^ 5 := by
    exact_mod_cast B_le_28_qpow5 hk
  have hqpos : 0 < (q k : ℚ) := by
    exact_mod_cast (by have := q_ge_three hk; omega : 0 < q k)
  have hq5 : (27 : ℚ) * k * (k + 1) ≤ (q k : ℚ) ^ 5 := by
    exact_mod_cast qpow5_ge_27_mul hk
  calc
    (B k : ℚ) / (q k : ℚ) ^ 10 ≤
        (28 * (q k : ℚ) ^ 5) / (q k : ℚ) ^ 10 :=
      div_le_div_of_nonneg_right hB (by positivity)
    _ = 28 / (q k : ℚ) ^ 5 := by
      field_simp [ne_of_gt hqpos]
    _ ≤ (28 / 27 : ℚ) / ((k : ℚ) * (k + 1)) := by
      have hkposR : 0 < (k : ℚ) * (k + 1) := by positivity
      have hq5pos : 0 < (q k : ℚ) ^ 5 := by positivity
      field_simp [ne_of_gt hkposR, ne_of_gt hq5pos]
      nlinarith [hq5]

theorem sum_inv_shift_mul_le_half (K : Nat) :
    (∑ i ∈ Finset.range K,
      (1 : ℚ) / ((i + 2 : Nat) : ℚ) / ((i + 3 : Nat) : ℚ)) ≤ 1 / 2 := by
  have htelescope1 :
      (∑ i ∈ Finset.range K,
        ((1 : ℚ) / ((i + 2 : Nat) : ℚ) - (1 : ℚ) / ((i + 3 : Nat) : ℚ))) =
        (1 : ℚ) / ((0 + 2 : Nat) : ℚ) - (1 : ℚ) / ((K + 2 : Nat) : ℚ) := by
    simpa only [show ∀ i : Nat, i + 1 + 2 = i + 3 by intro i; omega] using
      (Finset.sum_range_sub' (fun n => (1 : ℚ) / ((n + 2 : Nat) : ℚ)) K)
  have htelescope :
      (∑ i ∈ Finset.range K,
        ((1 : ℚ) / ((i + 2 : Nat) : ℚ) - (1 : ℚ) / ((i + 3 : Nat) : ℚ))) =
        (1 : ℚ) / 2 - (1 : ℚ) / (K + 2) := by
    simpa using htelescope1
  have hterm : ∀ i ∈ Finset.range K,
      (1 : ℚ) / ((i + 2 : Nat) : ℚ) / ((i + 3 : Nat) : ℚ) =
        (1 : ℚ) / ((i + 2 : Nat) : ℚ) - (1 : ℚ) / ((i + 3 : Nat) : ℚ) := by
    intro i hi
    have hi0 : 0 < (i + 2 : Nat) := by omega
    have hi1 : 0 < (i + 3 : Nat) := by omega
    field_simp
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, htelescope]
  change 1 / 2 - (1 : ℚ) / ((K : ℚ) + 2) ≤ 1 / 2
  have hden : (0 : ℚ) < (K : ℚ) + 2 := by
    exact_mod_cast (by omega : 0 < K + 2)
  have hnonneg : 0 ≤ (1 : ℚ) / ((K : ℚ) + 2) :=
    div_nonneg (by norm_num) (le_of_lt hden)
  linarith

theorem finite_decoration_weight_le {K : Nat} :
    (∑ i ∈ Finset.range K,
      (B (i + 2) : ℚ) / (q (i + 2) : ℚ) ^ 10) ≤ 14 / 27 := by
  calc
    (∑ i ∈ Finset.range K,
      (B (i + 2) : ℚ) / (q (i + 2) : ℚ) ^ 10) ≤
      ∑ i ∈ Finset.range K,
        (28 / 27 : ℚ) / (((i + 2 : Nat) : ℚ) * ((i + 3 : Nat) : ℚ)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi2 : 2 ≤ i + 2 := by omega
        have h := B_weight_le_telescoping (k := i + 2) hi2
        convert h using 1 <;> push_cast <;> ring
    _ = (28 / 27 : ℚ) *
        ∑ i ∈ Finset.range K,
          (1 : ℚ) / ((i + 2 : Nat) : ℚ) / ((i + 3 : Nat) : ℚ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
    _ ≤ (28 / 27 : ℚ) * (1 / 2) := by
        apply mul_le_mul_of_nonneg_left (sum_inv_shift_mul_le_half K)
        norm_num
    _ = 14 / 27 := by norm_num

end Paper.CountStage.Decoration

namespace Paper.CountStage.DecorationWords

abbrev BranchLabel := {q : Nat // 3 ≤ q}

def weight (q : BranchLabel) : ℚ := (1 : ℚ) / (q.val : ℚ) ^ 10
def weightSum (A : List BranchLabel) : ℚ := (A.map weight).sum

def budgetWords (A : List BranchLabel) : Nat → List (List Nat)
  | 0 => []
  | U + 1 => [[]] ++ A.flatMap (fun q =>
      (budgetWords A ((U + 1) / q.val)).map (q.val :: ·))
termination_by U => U
decreasing_by
  simp_wf
  exact Nat.div_lt_self (by omega) (by omega)

def quotaWeightSum (A : List BranchLabel) (U : Nat) : ℚ :=
  (A.map fun q => ((U / q.val : Nat) : ℚ) ^ 10).sum

lemma sum_map_le_rat {α : Type} (A : List α) (f g : α → ℚ)
    (h : ∀ a ∈ A, f a ≤ g a) :
    (A.map f).sum ≤ (A.map g).sum := by
  induction A with
  | nil => simp
  | cons a A ih =>
      simp only [List.map_cons, List.sum_cons]
      apply add_le_add
      · exact h a (by simp)
      · apply ih
        intro b hb
        exact h b (by simp [hb])

lemma sum_map_const_mul {α : Type} (A : List α) (f : α → ℚ) (c : ℚ) :
    (A.map fun a => c * f a).sum = c * (A.map f).sum := by
  induction A with
  | nil => simp
  | cons a A ih => simp [List.map_cons, List.sum_cons, ih, mul_add]

lemma sum_map_nat_cast {α : Type} (A : List α) (f : α → Nat) :
    ((A.map f).sum : ℚ) = (A.map fun a => (f a : ℚ)).sum := by
  induction A with
  | nil => simp
  | cons a A ih => simp [List.map_cons, List.sum_cons, ih]

theorem divPow_weight_le (U : Nat) (q : BranchLabel) :
    ((U / q.val : Nat) : ℚ) ^ 10 ≤ (U : ℚ) ^ 10 * weight q := by
  have hdiv : (U / q.val) * q.val ≤ U := Nat.div_mul_le_self U q.val
  have hpow : (U / q.val) ^ 10 * q.val ^ 10 ≤ U ^ 10 := by
    calc
      (U / q.val) ^ 10 * q.val ^ 10 = ((U / q.val) * q.val) ^ 10 := by ring
      _ ≤ U ^ 10 := Nat.pow_le_pow_left hdiv 10
  have hpowR :
      ((U / q.val : Nat) : ℚ) ^ 10 * (q.val : ℚ) ^ 10 ≤ (U : ℚ) ^ 10 := by
    exact_mod_cast hpow
  have hqpos : (0 : ℚ) < (q.val : ℚ) := by
    exact_mod_cast (by have := q.property; omega : 0 < q.val)
  change ((U / q.val : Nat) : ℚ) ^ 10 ≤
    (U : ℚ) ^ 10 * ((1 : ℚ) / (q.val : ℚ) ^ 10)
  field_simp [ne_of_gt hqpos]
  nlinarith [hpowR]

theorem quotaWeightSum_le (A : List BranchLabel) (U : Nat) :
    quotaWeightSum A U ≤ (U : ℚ) ^ 10 * weightSum A := by
  induction A with
  | nil => simp [quotaWeightSum, weightSum]
  | cons q A ih =>
      simp only [quotaWeightSum, weightSum, List.map_cons, List.sum_cons]
      calc
        ((U / q.val : Nat) : ℚ) ^ 10 +
            (A.map fun q => ((U / q.val : Nat) : ℚ) ^ 10).sum ≤
          (U : ℚ) ^ 10 * weight q + (U : ℚ) ^ 10 * weightSum A :=
            add_le_add (divPow_weight_le U q) ih
        _ = (U : ℚ) ^ 10 * (weight q + weightSum A) := by ring

theorem budgetWords_length_eq (A : List BranchLabel) : ∀ U,
    (budgetWords A U).length =
      if U = 0 then 0 else 1 +
        (A.map fun q => (budgetWords A (U / q.val)).length).sum := by
  intro U
  cases U with
  | zero => simp [budgetWords]
  | succ U =>
      simp [budgetWords, List.length_flatMap, Nat.add_comm]

theorem sum_recLengths_le (A : List BranchLabel) (U : Nat)
    (hrec : ∀ q ∈ A,
      ((budgetWords A (U / q.val)).length : ℚ) ≤
        3 * ((U / q.val : Nat) : ℚ) ^ 10) :
    ((A.map fun q => (budgetWords A (U / q.val)).length : List Nat).sum : ℚ) ≤
      3 * quotaWeightSum A U := by
  have hmap := sum_map_le_rat A
    (fun q => ((budgetWords A (U / q.val)).length : ℚ))
    (fun q => 3 * ((U / q.val : Nat) : ℚ) ^ 10) hrec
  have hcast := sum_map_nat_cast A (fun q => (budgetWords A (U / q.val)).length)
  have hmul := sum_map_const_mul A (fun q => ((U / q.val : Nat) : ℚ) ^ 10) 3
  calc
    ((A.map fun q => (budgetWords A (U / q.val)).length : List Nat).sum : ℚ) =
        (A.map fun q => ((budgetWords A (U / q.val)).length : ℚ)).sum := hcast
    _ ≤ (A.map fun q => 3 * ((U / q.val : Nat) : ℚ) ^ 10).sum := hmap
    _ = 3 * quotaWeightSum A U := by simpa [quotaWeightSum] using hmul

theorem budgetWords_length_bounds (A : List BranchLabel)
    (hweight : weightSum A ≤ 14 / 27) :
    ∀ U, ((budgetWords A U).length : ℚ) ≤ 3 * (U : ℚ) ^ 10 ∧
      ((budgetWords A U).length : ℚ) ≤
        1 + (14 / 9 : ℚ) * (U : ℚ) ^ 10 := by
  intro U
  induction U using Nat.strong_induction_on with
  | h U ih =>
      cases U with
      | zero => simp [budgetWords]
      | succ U =>
          let n := U + 1
          have hn : 0 < n := by dsimp [n]; omega
          have hsmall : ∀ q ∈ A, n / q.val < n := by
            intro q hq
            exact Nat.div_lt_self hn (by have := q.property; omega)
          have hrec : ∀ q ∈ A,
              ((budgetWords A (n / q.val)).length : ℚ) ≤
                3 * ((n / q.val : Nat) : ℚ) ^ 10 := by
            intro q hq
            exact (ih (n / q.val) (hsmall q hq)).1
          have hsum := sum_recLengths_le A n hrec
          have hlen := budgetWords_length_eq A n
          have hquota := quotaWeightSum_le A n
          have hword : (budgetWords A n).length =
              1 + (A.map fun q => (budgetWords A (n / q.val)).length).sum := by
            simpa [n] using hlen
          have hwordR : ((budgetWords A n).length : ℚ) =
              1 + ((A.map fun q => (budgetWords A (n / q.val)).length).sum : ℚ) := by
            exact_mod_cast hword
          have hbound :
              3 * quotaWeightSum A n ≤ 3 * (n : ℚ) ^ 10 * (14 / 27 : ℚ) := by
            calc
              3 * quotaWeightSum A n ≤ 3 * ((n : ℚ) ^ 10 * weightSum A) :=
                mul_le_mul_of_nonneg_left hquota (by norm_num)
              _ ≤ 3 * (n : ℚ) ^ 10 * (14 / 27 : ℚ) := by
                calc
                  3 * ((n : ℚ) ^ 10 * weightSum A) =
                      (3 * (n : ℚ) ^ 10) * weightSum A := by ring
                  _ ≤ (3 * (n : ℚ) ^ 10) * (14 / 27 : ℚ) :=
                    mul_le_mul_of_nonneg_left hweight (by positivity)
                  _ = 3 * (n : ℚ) ^ 10 * (14 / 27 : ℚ) := by ring
          have hn10 : (1 : ℚ) ≤ (n : ℚ) ^ 10 := by
            exact_mod_cast Nat.one_le_pow 10 n hn
          have hstrong : ((budgetWords A n).length : ℚ) ≤
              1 + (14 / 9 : ℚ) * (n : ℚ) ^ 10 := by
            calc
              ((budgetWords A n).length : ℚ) =
                  1 + ((A.map fun q => (budgetWords A (n / q.val)).length).sum : ℚ) := hwordR
              _ ≤ 1 + 3 * quotaWeightSum A n := by linarith [hsum]
              _ ≤ 1 + (14 / 9 : ℚ) * (n : ℚ) ^ 10 := by
                have hmul :
                    3 * (n : ℚ) ^ 10 * (14 / 27 : ℚ) =
                      (14 / 9 : ℚ) * (n : ℚ) ^ 10 := by ring
                linarith [hbound, hmul]
          constructor
          · have hweak : 1 + (14 / 9 : ℚ) * (n : ℚ) ^ 10 ≤
                3 * (n : ℚ) ^ 10 := by nlinarith [hn10]
            exact hstrong.trans hweak
          · exact hstrong

theorem budgetWords_length_lt_three_pow {A : List BranchLabel}
    (hweight : weightSum A ≤ 14 / 27) {U : Nat} (hU : 1 ≤ U) :
    ((budgetWords A U).length : ℚ) < 3 * (U : ℚ) ^ 10 := by
  have hstrong := (budgetWords_length_bounds A hweight U).2
  have hU10 : (1 : ℚ) ≤ (U : ℚ) ^ 10 := by
    exact_mod_cast Nat.one_le_pow 10 U (by omega)
  have hstrict : 1 + (14 / 9 : ℚ) * (U : ℚ) ^ 10 <
      3 * (U : ℚ) ^ 10 := by nlinarith [hU10]
  exact lt_of_le_of_lt hstrong hstrict

def wordProduct (w : List Nat) : Nat := w.prod

theorem wordProduct_ge_one {A : List BranchLabel} : ∀ w : List Nat,
    (∀ x ∈ w, x ∈ A.map Subtype.val) → 1 ≤ wordProduct w
  | [], _ => by simp [wordProduct]
  | x :: xs, hmem => by
      have hxmem : x ∈ A.map Subtype.val := hmem x (by simp)
      obtain ⟨q, hq, hqx⟩ := List.mem_map.mp hxmem
      have hx : 1 ≤ x := by rw [← hqx]; omega
      have htail : ∀ y ∈ xs, y ∈ A.map Subtype.val := by
        intro y hy
        exact hmem y (by simp [hy])
      have hprod := wordProduct_ge_one (A := A) xs htail
      simp [wordProduct] at hprod ⊢
      simpa using Nat.mul_le_mul hx hprod

theorem budgetWords_sound (A : List BranchLabel) : ∀ U w,
    w ∈ budgetWords A U →
      wordProduct w ≤ U ∧ ∀ x ∈ w, x ∈ A.map Subtype.val := by
  intro U
  induction U using Nat.strong_induction_on with
  | h U ih =>
      intro w hw
      cases U with
      | zero => simp [budgetWords] at hw
      | succ U =>
          simp only [budgetWords, List.mem_append, List.mem_singleton,
            List.mem_flatMap, List.mem_map] at hw
          rcases hw with hempty | ⟨q, hq, tail, htail, hEq⟩
          · subst w
            simp [wordProduct]
          · subst w
            have hlt : (U + 1) / q.val < U + 1 :=
              Nat.div_lt_self (by omega) (by have := q.property; omega)
            have htailSound := ih ((U + 1) / q.val) hlt tail htail
            have hprod : tail.prod * q.val ≤ U + 1 :=
              (Nat.le_div_iff_mul_le (by have := q.property; omega)).mp
                htailSound.1
            constructor
            · simpa [wordProduct, Nat.mul_comm] using hprod
            · intro x hx
              rcases List.mem_cons.mp hx with hx | hx
              · subst x
                exact List.mem_map.mpr ⟨q, hq, rfl⟩
              · exact htailSound.2 x hx

theorem budgetWords_complete (A : List BranchLabel) : ∀ U w,
    (∀ x ∈ w, x ∈ A.map Subtype.val) → wordProduct w ≤ U →
      w ∈ budgetWords A U := by
  intro U
  induction U using Nat.strong_induction_on with
  | h U ih =>
      intro w hmem hprod
      cases U with
      | zero =>
          have hpos := wordProduct_ge_one (A := A) w hmem
          have hz : wordProduct w = 0 := Nat.eq_zero_of_le_zero hprod
          rw [hz] at hpos
          omega
      | succ U =>
          cases w with
          | nil => simp [budgetWords]
          | cons x xs =>
              have hxmem : x ∈ A.map Subtype.val := hmem x (by simp)
              obtain ⟨q, hq, hqx⟩ := List.mem_map.mp hxmem
              have htailMem : ∀ y ∈ xs, y ∈ A.map Subtype.val := by
                intro y hy
                exact hmem y (by simp [hy])
              have hprod' : x * xs.prod ≤ U + 1 := by
                simpa [wordProduct] using hprod
              have hprodQ : q.val * xs.prod ≤ U + 1 := by
                rw [hqx]
                exact hprod'
              have htailprod : xs.prod ≤ (U + 1) / q.val := by
                apply (Nat.le_div_iff_mul_le (by have := q.property; omega)).2
                simpa [Nat.mul_comm] using hprodQ
              have hlt : (U + 1) / q.val < U + 1 :=
                Nat.div_lt_self (by omega) (by have := q.property; omega)
              have htail : xs ∈ budgetWords A ((U + 1) / q.val) :=
                ih ((U + 1) / q.val) hlt xs htailMem (by
                  simpa [wordProduct] using htailprod)
              have hbranch : x :: xs ∈ A.flatMap (fun r =>
                  (budgetWords A ((U + 1) / r.val)).map (r.val :: ·)) := by
                rw [List.mem_flatMap]
                refine ⟨q, hq, ?_⟩
                rw [List.mem_map]
                exact ⟨xs, htail, by rw [hqx]⟩
              have hmemAll : x :: xs ∈ [[]] ++
                  A.flatMap (fun r =>
                    (budgetWords A ((U + 1) / r.val)).map (r.val :: ·)) :=
                List.mem_append.mpr (Or.inr hbranch)
              simpa [budgetWords] using hmemAll

end Paper.CountStage.DecorationWords


namespace Paper.CountStage.DecorationWords

open Paper.CountStage.Decoration

def decorationAlphabet (K : Nat) : List BranchLabel :=
  (List.range (K - 1)).flatMap fun i =>
    List.replicate (B (i + 2)) ⟨q (i + 2), q_ge_three (by omega)⟩

lemma weightSum_replicate (n : Nat) (l : BranchLabel) :
    weightSum (List.replicate n l) = (n : ℚ) * weight l := by
  induction n with
  | zero => simp [weightSum]
  | succ n ih =>
      simp [weightSum, ih]

lemma weightSum_flatMap {α : Type} (xs : List α) (f : α → List BranchLabel) :
    weightSum (xs.flatMap f) = (xs.map fun x => weightSum (f x)).sum := by
  induction xs with
  | nil => simp [weightSum]
  | cons x xs ih =>
      simp only [weightSum] at ih
      simp only [weightSum, List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons]
      rw [ih]

lemma listRangeSum_eq_finset (f : Nat → ℚ) : ∀ K,
    ((List.range K).map f).sum = ∑ i ∈ Finset.range K, f i := by
  intro K
  induction K with
  | zero => simp
  | succ K ih =>
      rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]
      simp

theorem decorationAlphabet_weight_le (K : Nat) : weightSum (decorationAlphabet K) ≤ 14 / 27 := by
  rw [decorationAlphabet, weightSum_flatMap]
  have hsum : ((List.range (K - 1)).map fun i =>
      (B (i + 2) : ℚ) / (q (i + 2) : ℚ) ^ 10).sum ≤ 14 / 27 := by
    rw [listRangeSum_eq_finset]
    exact finite_decoration_weight_le
  calc
    ((List.range (K - 1)).map fun i =>
        weightSum (List.replicate (B (i + 2)) ⟨q (i + 2), q_ge_three (by omega)⟩)).sum =
      ((List.range (K - 1)).map fun i =>
        (B (i + 2) : ℚ) / (q (i + 2) : ℚ) ^ 10).sum := by
          apply congrArg List.sum
          apply List.map_congr_left
          intro i hi
          rw [weightSum_replicate]
          simp [weight, q]
          push_cast
          ring
    _ ≤ 14 / 27 := hsum

theorem decoratedWords_lt_three_U10 {K U : Nat} (hU : 1 ≤ U) :
    ((budgetWords (decorationAlphabet K) U).length : ℚ) < 3 * (U : ℚ) ^ 10 := by
  exact budgetWords_length_lt_three_pow (A := decorationAlphabet K)
    (decorationAlphabet_weight_le K) hU

end Paper.CountStage.DecorationWords