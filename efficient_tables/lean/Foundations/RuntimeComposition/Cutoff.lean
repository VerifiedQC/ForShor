import Foundations.RuntimeComposition.Defs
import Mathlib.Tactic

namespace RuntimeComposition

theorem S_le_two_pow (k : ℕ) (hk : 2 ≤ k) :
    RuntimeComposition.S k ≤ 2 ^ (70 * k ^ 2 * RuntimeComposition.bl k) := by
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
  have hq : 4 ≤ k ^ 2 := by nlinarith
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
  have hexp : (2 * b + 3) * (2 * (6 * k ^ 2) + 1) ≤ 70 * k ^ 2 * b := by
    generalize k ^ 2 = q at hq ⊢
    nlinarith
  refine hS2.trans ?_
  rw [← pow_mul]
  exact Nat.pow_le_pow_right (by norm_num) hexp

end RuntimeComposition
