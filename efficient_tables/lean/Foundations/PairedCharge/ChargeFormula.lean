import Foundations.PairedCharge.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Algebra.Order.Field.Power

namespace PairedCharge

private lemma zp_neg (j : ℕ) : (2 : ℚ) ^ (-(j : ℤ)) = ((2 : ℚ) ^ j)⁻¹ := by
  rw [zpow_neg, zpow_natCast]

private lemma pow_two_ge (n : ℕ) (hn : 1 ≤ n) : (2 : ℚ) ≤ (2 : ℚ) ^ n := by
  calc (2 : ℚ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn

private lemma pointAt_four (j : ℕ) (hj : 1 ≤ j) :
    pointAt (4 * j) = Pt.fin (-(2 : ℚ) ^ (-(j : ℤ))) := by
  have h1 : (4 * j) % 4 = 0 := by omega
  have d1 : (4 * j) / 4 = j := by omega
  unfold pointAt
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  simp only [h1, d1]

private lemma negFrac_iff (i : ℕ) :
    IsNegFrac (pointAt i) ↔ ∃ j : ℕ, 1 ≤ j ∧ i = 4 * j := by
  constructor
  · rintro ⟨j, hj, h⟩
    have hjp : (2 : ℚ) ≤ (2 : ℚ) ^ j := pow_two_ge j hj
    have hjpos : (0 : ℚ) < (2 : ℚ) ^ j := by linarith
    have hinv : ((2 : ℚ) ^ j)⁻¹ ≤ 1 / 2 := by
      have := inv_anti₀ (by norm_num : (0:ℚ) < 2) hjp
      linarith
    have hinvpos : (0 : ℚ) < ((2 : ℚ) ^ j)⁻¹ := inv_pos.mpr hjpos
    by_cases hi : i < 4
    · exfalso
      interval_cases i <;> simp [pointAt, zp_neg] at h <;> linarith
    · replace hi : 4 ≤ i := by omega
      have hne : ¬ i = 0 := by omega
      have hne1 : ¬ i = 1 := by omega
      have hne2 : ¬ i = 2 := by omega
      have hne3 : ¬ i = 3 := by omega
      have hn : 1 ≤ i / 4 := by omega
      have hge := pow_two_ge (i / 4) hn
      unfold pointAt at h
      rw [if_neg hne, if_neg hne1, if_neg hne2, if_neg hne3] at h
      have hm : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
      rcases hm with hm | hm | hm | hm
      · simp only [hm, Pt.fin.injEq, zp_neg, zpow_natCast] at h
        have h' : (2 : ℚ) ^ (i / 4) = (2 : ℚ) ^ j := by
          have := neg_injective h
          exact inv_injective this
        have : i / 4 = j := Nat.pow_right_injective (le_refl 2) (by exact_mod_cast h')
        exact ⟨j, hj, by omega⟩
      · exfalso
        simp only [hm, Pt.fin.injEq, zp_neg, zpow_natCast] at h
        have : (0 : ℚ) < ((2 : ℚ) ^ (i / 4))⁻¹ := inv_pos.mpr (by linarith)
        linarith
      · exfalso
        simp only [hm, Pt.fin.injEq, zp_neg, zpow_natCast] at h
        have h' : (2 : ℚ) ^ (i / 4) = ((2 : ℚ) ^ j)⁻¹ := by linarith
        linarith
      · exfalso
        simp only [hm, Pt.fin.injEq, zp_neg, zpow_natCast] at h
        linarith
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, pointAt_four j hj⟩

private lemma fMinus_gen (k : ℕ) [DecidablePred fun i => IsNegFrac (pointAt i)] :
    ((Finset.range (2 * k - 1)).filter (fun i => IsNegFrac (pointAt i))).card = (k - 1) / 2 := by
  have : (Finset.range (2 * k - 1)).filter (fun i => IsNegFrac (pointAt i))
      = (Finset.Icc 1 ((2 * k - 2) / 4)).image (fun j => 4 * j) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, Finset.mem_Icc,
      negFrac_iff]
    constructor
    · rintro ⟨hi, j, hj, rfl⟩
      exact ⟨j, ⟨hj, by omega⟩, rfl⟩
    · rintro ⟨j, ⟨hj, hj2⟩, rfl⟩
      exact ⟨by omega, j, hj, rfl⟩
  rw [this, Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
  simp only [Nat.card_Icc]
  omega

private lemma fMinus_eq (k : ℕ) : fMinus k = (k - 1) / 2 := by
  unfold fMinus
  exact @fMinus_gen k (fun _ => Classical.propDecidable _)

private lemma skel_card (k : ℕ) [DecidablePred fun i => IsNegFrac (pointAt i)] :
    ((Finset.Ico 2 (2 * k - 1)).filter (fun i => IsNegFrac (pointAt i))).card
      = (k - 1) / 2 := by
  have : (Finset.Ico 2 (2 * k - 1)).filter (fun i => IsNegFrac (pointAt i))
      = (Finset.Icc 1 ((2 * k - 2) / 4)).image (fun j => 4 * j) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_image, Finset.mem_Icc,
      negFrac_iff]
    constructor
    · rintro ⟨hi, j, hj, rfl⟩
      exact ⟨j, ⟨hj, by omega⟩, rfl⟩
    · rintro ⟨j, ⟨hj, hj2⟩, rfl⟩
      exact ⟨⟨by omega, by omega⟩, j, hj, rfl⟩
  rw [this, Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
  simp only [Nat.card_Icc]
  omega

private lemma lc_append (a b : List Instr) :
    listCharge (a ++ b) = listCharge a + listCharge b := by
  simp [listCharge]

private lemma cPair_nat (k : ℕ) (hk : 2 ≤ k) :
    cPair k = (k - 2) * (4 * k - 3) + 4 * (k - 1) + nu k := by
  have hpb : listCharge (pairBlock k) = 4 * k - 3 := by
    unfold pairBlock listCharge
    simp [Instr.charge]
    omega
  have hsb : listCharge (singletonBlock k) = 4 * (k - 1) := by
    unfold singletonBlock listCharge
    simp [Instr.charge]
    omega
  have hrep : ∀ (n : ℕ), listCharge ((List.replicate n (pairBlock k)).flatten)
      = n * (4 * k - 3) := by
    intro n
    induction n with
    | zero => simp [listCharge]
    | succ n ih =>
      rw [List.replicate_succ, List.flatten_cons]
      rw [lc_append, ih, hpb, Nat.add_mul, Nat.one_mul]
      omega
  unfold cPair skeleton
  rw [@skel_card k (fun _ => Classical.propDecidable _)]
  unfold nu
  have h1 := hrep (k - 2)
  unfold listCharge at h1 hsb ⊢
  simp only [List.map_append, List.sum_append, List.map_replicate, List.sum_replicate]
  rw [h1, hsb]
  simp [Instr.charge, fMinus_eq]

private lemma nu_le (k : ℕ) : nu k ≤ k - 1 := by
  unfold nu
  rw [fMinus_eq]
  split_ifs <;> omega

theorem charge_formula (k : ℕ) (hk : 2 ≤ k) :
    ((cPair k : ℤ) = ((k : ℤ) - 2) * (4 * (k : ℤ) - 3) + 4 * ((k : ℤ) - 1) + (nu k : ℤ) ∧
      ((k : ℤ) - 2) * (4 * (k : ℤ) - 3) + 4 * ((k : ℤ) - 1) + (nu k : ℤ)
        = 4 * (k : ℤ) ^ 2 - 7 * (k : ℤ) + 2 + (nu k : ℤ)) ∧
    fMinus k = (k - 1) / 2 ∧ nu k ≤ k - 1 := by
  refine ⟨⟨?_, ?_⟩, fMinus_eq k, nu_le k⟩
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    have h := cPair_nat (m + 2) hk
    have e1 : m + 2 - 2 = m := by omega
    have e2 : m + 2 - 1 = m + 1 := by omega
    have e3 : 4 * (m + 2) - 3 = 4 * m + 5 := by omega
    rw [e1, e2, e3] at h
    rw [h]
    push_cast
    ring
  · ring

end PairedCharge
