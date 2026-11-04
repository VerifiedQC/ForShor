import Foundations.RuntimeComposition.Defs
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorial.Basic

namespace RuntimeComposition

theorem local_factor_bound (c : ℕ) (hc : 1 ≤ c) (k C Lambda m : ℕ) (hk : 2 ≤ k)
    (hC : C ≤ 27 * k ^ 3)
    (h1 : C ≤ 6 * k ^ 2 → Lambda + 1 ≤ RuntimeComposition.S k)
    (h2 : 6 * k ^ 2 ≤ C → Lambda ≤ 9 * k ^ 2) :
    (k ^ 2 * (Lambda + 1)) ^ (c * (C + 1)) * (k + Lambda + m + 1) ^ c
      ≤ 2 ^ (600 * c * k ^ 4 * RuntimeComposition.bl k) * (m + 1) ^ c := by
  obtain ⟨b, hb⟩ : ∃ b, b = RuntimeComposition.bl k := ⟨_, rfl⟩
  rw [← hb]
  have hb2 : 2 ≤ b := by
    have : 0 < Nat.log 2 k := Nat.log_pos Nat.one_lt_two hk
    rw [hb]; unfold RuntimeComposition.bl; omega
  have hkb : k < 2 ^ b := by
    rw [hb]; exact Nat.lt_pow_succ_log_self (by norm_num) k
  have hk2 : k ^ 2 ≤ 2 ^ (2 * b) := by
    calc k ^ 2 = k * k := sq k
      _ ≤ 2 ^ b * 2 ^ b := Nat.mul_le_mul hkb.le hkb.le
      _ = 2 ^ (2 * b) := by rw [← pow_add]; congr 1; omega
  set A := k ^ 2 * (Lambda + 1) with hA
  have hmain : A ^ (C + 2) ≤ 2 ^ (600 * k ^ 4 * b) := by
    have hq : 4 ≤ k ^ 2 := by nlinarith
    have hk3 : k ^ 2 ≤ k ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have hk4 : k ^ 3 ≤ k ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    rcases le_total C (6 * k ^ 2) with hl | hh
    · -- low regime
      have hS := h1 hl
      have hP : 8 * k ^ 2 ≤ 2 ^ (2 * b + 3) := by
        rw [pow_add]; nlinarith
      have hfac : (6 * k ^ 2).factorial ≤ (2 ^ (2 * b + 3)) ^ (6 * k ^ 2) :=
        (Nat.factorial_le_pow _).trans
          (Nat.pow_le_pow_left (by omega) _)
      have hS2 : RuntimeComposition.S k ≤ (2 ^ (2 * b + 3)) ^ (2 * (6 * k ^ 2) + 1) := by
        unfold RuntimeComposition.S
        have e1 : 6 * k ^ 2 + 1 ≤ 2 ^ (2 * b + 3) := by omega
        have e3 : (8 * k ^ 2) ^ (6 * k ^ 2) ≤ (2 ^ (2 * b + 3)) ^ (6 * k ^ 2) :=
          Nat.pow_le_pow_left hP _
        calc (6 * k ^ 2 + 1) * (6 * k ^ 2).factorial * (8 * k ^ 2) ^ (6 * k ^ 2)
            ≤ 2 ^ (2 * b + 3) * (2 ^ (2 * b + 3)) ^ (6 * k ^ 2) * (2 ^ (2 * b + 3)) ^ (6 * k ^ 2) :=
              Nat.mul_le_mul (Nat.mul_le_mul e1 hfac) e3
          _ = _ := by ring
      have hexp : (2 * b + 3) * (2 * (6 * k ^ 2) + 1) ≤ 46 * k ^ 2 * b := by
        generalize k ^ 2 = q at hq ⊢
        nlinarith
      have hS3 : RuntimeComposition.S k ≤ 2 ^ (46 * k ^ 2 * b) := by
        refine hS2.trans ?_
        rw [← pow_mul]
        exact Nat.pow_le_pow_right (by norm_num) hexp
      have hA1 : A ≤ 2 ^ (48 * k ^ 2 * b) := by
        have : A ≤ 2 ^ (2 * b) * 2 ^ (46 * k ^ 2 * b) :=
          Nat.mul_le_mul hk2 (hS.trans hS3)
        refine this.trans ?_
        rw [← pow_add]
        apply Nat.pow_le_pow_right (by norm_num)
        nlinarith
      calc A ^ (C + 2) ≤ (2 ^ (48 * k ^ 2 * b)) ^ (C + 2) := Nat.pow_le_pow_left hA1 _
        _ = 2 ^ (48 * k ^ 2 * b * (C + 2)) := by rw [← pow_mul]
        _ ≤ 2 ^ (600 * k ^ 4 * b) := by
          apply Nat.pow_le_pow_right (by norm_num)
          have : C + 2 ≤ 7 * k ^ 2 := by omega
          calc 48 * k ^ 2 * b * (C + 2) ≤ 48 * k ^ 2 * b * (7 * k ^ 2) :=
                Nat.mul_le_mul_left _ this
            _ ≤ 600 * k ^ 4 * b := by
                have : k ^ 4 = k ^ 2 * k ^ 2 := by ring
                rw [this]; nlinarith [Nat.zero_le (k ^ 2 * k ^ 2 * b)]
    · -- high regime
      have hL := h2 hh
      have hA1 : A ≤ 2 ^ (6 * b) := by
        have e : A ≤ 2 ^ (2 * b) * (10 * k ^ 2) :=
          Nat.mul_le_mul hk2 (by omega)
        refine e.trans ?_
        have : 10 * k ^ 2 ≤ 2 ^ (2 * b + 4) := by
          rw [pow_add]; nlinarith
        calc 2 ^ (2 * b) * (10 * k ^ 2) ≤ 2 ^ (2 * b) * 2 ^ (2 * b + 4) :=
              Nat.mul_le_mul_left _ this
          _ = 2 ^ (4 * b + 4) := by rw [← pow_add]; congr 1; omega
          _ ≤ 2 ^ (6 * b) := Nat.pow_le_pow_right (by norm_num) (by omega)
      calc A ^ (C + 2) ≤ (2 ^ (6 * b)) ^ (C + 2) := Nat.pow_le_pow_left hA1 _
        _ = 2 ^ (6 * b * (C + 2)) := by rw [← pow_mul]
        _ ≤ 2 ^ (600 * k ^ 4 * b) := by
          apply Nat.pow_le_pow_right (by norm_num)
          have : C + 2 ≤ 28 * k ^ 3 := by nlinarith
          calc 6 * b * (C + 2) ≤ 6 * b * (28 * k ^ 3) := Nat.mul_le_mul_left _ this
            _ ≤ 600 * k ^ 4 * b := by
                have : k ^ 4 = k * k ^ 3 := by ring
                rw [this]; nlinarith [Nat.zero_le (k ^ 3 * b)]
  have hkL : k + Lambda + 1 ≤ A := by
    rw [hA]
    have h4 : k + 2 ≤ k ^ 2 := by nlinarith
    nlinarith [Nat.zero_le Lambda, Nat.mul_le_mul_right Lambda (show 1 ≤ k ^ 2 by omega)]
  have hm : k + Lambda + m + 1 ≤ A * (m + 1) := by nlinarith
  calc A ^ (c * (C + 1)) * (k + Lambda + m + 1) ^ c
      ≤ (A ^ (C + 1)) ^ c * (A * (m + 1)) ^ c := by
        rw [pow_mul']
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm _)
    _ = (A ^ (C + 2)) ^ c * (m + 1) ^ c := by
        rw [← mul_pow, ← mul_pow]; ring
    _ ≤ (2 ^ (600 * k ^ 4 * b)) ^ c * (m + 1) ^ c :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hmain _)
    _ = _ := by rw [← pow_mul]; congr 2; ring

end RuntimeComposition
