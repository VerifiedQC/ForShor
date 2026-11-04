import Foundations.RuntimeComposition.Defs
import Foundations.RuntimeComposition.Factorial
import Foundations.RuntimeComposition.TripleCount
import Foundations.RuntimeComposition.LocalFactor
import Mathlib.Tactic

namespace RuntimeComposition

private lemma bl_le_self (x : ℕ) (hx : 1 ≤ x) : RuntimeComposition.bl x ≤ x := by
  unfold RuntimeComposition.bl
  have : Nat.log 2 x < x :=
    Nat.log_lt_of_lt_pow (by omega) (Nat.lt_two_pow_self)
  omega

private lemma bl_succ_le (n : ℕ) (hn : 2 ≤ n) : RuntimeComposition.bl (n + 1) ≤ n := by
  unfold RuntimeComposition.bl
  have h : n + 1 < 2 ^ n := by
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ m hm ih => rw [pow_succ]; omega
  have : Nat.log 2 (n + 1) < n := Nat.log_lt_of_lt_pow (by omega) h
  omega

private lemma bl_mono (a b : ℕ) (h : a ≤ b) : RuntimeComposition.bl a ≤ RuntimeComposition.bl b := by
  unfold RuntimeComposition.bl
  have := Nat.log_mono_right (b := 2) h
  omega

theorem composition (c e K n U : ℕ) (hc : 1 ≤ c) (he : 1 ≤ e) (hK : 2 ≤ K) (hn : 2 ≤ n)
    (hU1 : 1 ≤ U) (hU2 : U ≤ (n + 1) ^ e)
    (Loc : ℕ → ℕ → ℕ → ℕ) (Lambda : ℕ → ℕ → ℕ)
    (H1 : ∀ k d C : ℕ, 2 ≤ k → k ≤ K → d < k → C ≤ 27 * k ^ 3 →
      Loc k d C ≤ (k ^ 2 * (Lambda k C + 1)) ^ (c * (C + 1)) *
        (k + Lambda k C + RuntimeComposition.bl (n + 1) + 1) ^ c)
    (H2 : ∀ k C : ℕ, 2 ≤ k → k ≤ K → C ≤ 27 * k ^ 3 →
      (C ≤ 6 * k ^ 2 → Lambda k C + 1 ≤ RuntimeComposition.S k) ∧
      (6 * k ^ 2 ≤ C → Lambda k C ≤ 9 * k ^ 2))
    (W t P Outer Total : ℕ) (ht : 1 ≤ t) (hW : W ≤ 3 * U ^ 10)
    (htU : Nat.factorial t ≤ U)
    (hP : P ≤ t ^ (c * t) * (RuntimeComposition.bl U + 2) ^ c)
    (hOuter : Outer ≤ W * n * (RuntimeComposition.bl U + 1) * P)
    (hTotal : Total = RuntimeComposition.localTotal Loc K + Outer) :
    Total ≤ 2 ^ (611 * c * K ^ 4 * RuntimeComposition.bl K) * (n + 1) ^ (e * (11 + 3 * c) + 2 * c + 4) := by
  obtain ⟨m, hm⟩ : ∃ m, m = RuntimeComposition.bl (n + 1) := ⟨_, rfl⟩
  have hmn : m + 1 ≤ n + 1 := by have := bl_succ_le n hn; omega
  have hN1 : 1 ≤ n + 1 := by omega
  set N := n + 1 with hN
  have hN3 : 3 ≤ N := by omega
  obtain ⟨b, hb⟩ : ∃ b, b = RuntimeComposition.bl K := ⟨_, rfl⟩
  have hb2 : 2 ≤ b := by
    have : 0 < Nat.log 2 K := Nat.log_pos Nat.one_lt_two hK
    rw [hb]; unfold RuntimeComposition.bl; omega
  have hK4 : 16 ≤ K ^ 4 := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ K ^ 4 := Nat.pow_le_pow_left hK 4
  -- local part
  have hLoc : RuntimeComposition.localTotal Loc K ≤ 2 ^ (610 * c * K ^ 4 * b) * N ^ c := by
    unfold RuntimeComposition.localTotal
    have hterm : ∀ t ∈ RuntimeComposition.tripleSet K,
        Loc t.1 t.2.1 t.2.2 ≤ 2 ^ (600 * c * K ^ 4 * b) * N ^ c := by
      intro t ht
      unfold RuntimeComposition.tripleSet at ht
      simp only [Finset.mem_image, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_product,
        Finset.mem_range] at ht
      obtain ⟨⟨k, d, C⟩, ⟨hk, hd, hC⟩, rfl⟩ := ht
      simp only at hk hd hC ⊢
      have hC' : C ≤ 27 * k ^ 3 := by omega
      have h1 := H1 k d C hk.1 hk.2 hd hC'
      obtain ⟨h2a, h2b⟩ := H2 k C hk.1 hk.2 hC'
      have h4 := local_factor_bound c hc k C (Lambda k C) m hk.1 hC' h2a h2b
      rw [hm] at h4
      have h5 := h1.trans h4
      refine h5.trans ?_
      have hbl : RuntimeComposition.bl k ≤ b := hb ▸ bl_mono k K hk.2
      have hk4 : k ^ 4 ≤ K ^ 4 := Nat.pow_le_pow_left hk.2 4
      have : 600 * c * k ^ 4 * RuntimeComposition.bl k ≤ 600 * c * K ^ 4 * b := by
        calc 600 * c * k ^ 4 * RuntimeComposition.bl k ≤ 600 * c * K ^ 4 * RuntimeComposition.bl k :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hk4)
          _ ≤ _ := Nat.mul_le_mul_left _ hbl
      have hpow : 2 ^ (600 * c * k ^ 4 * RuntimeComposition.bl k) ≤ 2 ^ (600 * c * K ^ 4 * b) :=
        Nat.pow_le_pow_right (by norm_num) this
      have hm' : (RuntimeComposition.bl (n + 1) + 1) ^ c ≤ N ^ c := by
        apply Nat.pow_le_pow_left; rw [← hm]; exact hmn
      exact Nat.mul_le_mul hpow hm'
    have hsum := Finset.sum_le_card_nsmul _ _ _ hterm
    refine hsum.trans ?_
    rw [smul_eq_mul]
    obtain ⟨hc3, hc4⟩ := triple_count_le K hK
    have hkb : (RuntimeComposition.tripleSet K).card ≤ 2 ^ (10 * K ^ 4 * b) := by
      refine hc4.trans ?_
      rw [← hb]
      apply Nat.pow_le_pow_right (by norm_num)
      nlinarith
    calc (RuntimeComposition.tripleSet K).card * (2 ^ (600 * c * K ^ 4 * b) * N ^ c)
        ≤ 2 ^ (10 * K ^ 4 * b) * (2 ^ (600 * c * K ^ 4 * b) * N ^ c) :=
          Nat.mul_le_mul_right _ hkb
      _ = 2 ^ (10 * K ^ 4 * b + 600 * c * K ^ 4 * b) * N ^ c := by rw [pow_add]; ring
      _ ≤ 2 ^ (610 * c * K ^ 4 * b) * N ^ c := by
          apply Nat.mul_le_mul_right
          apply Nat.pow_le_pow_right (by norm_num)
          have : 10 * K ^ 4 * b ≤ 10 * c * K ^ 4 * b := by
            have : 10 * K ^ 4 * b * 1 ≤ 10 * K ^ 4 * b * c := Nat.mul_le_mul_left _ hc
            nlinarith
          nlinarith
  -- outer part
  have hbU : RuntimeComposition.bl U ≤ U := bl_le_self U hU1
  have hP2 : P ≤ (U ^ (2 * c)) * (3 * U) ^ c := by
    refine hP.trans (Nat.mul_le_mul ((tt_le_factorial_sq t ht).2 c U hc htU) ?_)
    exact Nat.pow_le_pow_left (by omega) c
  have hOut : Outer ≤ N ^ (e * (11 + 3 * c) + c + 3) := by
    have hUe : U ^ (11 + 3 * c) ≤ N ^ (e * (11 + 3 * c)) := by
      calc U ^ (11 + 3 * c) ≤ (N ^ e) ^ (11 + 3 * c) := Nat.pow_le_pow_left hU2 _
        _ = N ^ (e * (11 + 3 * c)) := (pow_mul N e _).symm
    have hW' : W ≤ 3 * U ^ 10 := hW
    have h3c : 3 ^ c ≤ N ^ c := Nat.pow_le_pow_left hN3 c
    have hn' : n ≤ N := by omega
    have step : Outer ≤ (3 * U ^ 10) * n * (2 * U) * ((U ^ (2 * c)) * (3 * U) ^ c) := by
      refine hOuter.trans ?_
      refine Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hW' le_rfl) ?_) hP2
      omega
    have e1 : (3 * U ^ 10) * n * (2 * U) * ((U ^ (2 * c)) * (3 * U) ^ c)
        = 6 * 3 ^ c * n * U ^ (11 + 3 * c) := by
      rw [mul_pow]; ring
    rw [e1] at step
    have : 6 * 3 ^ c * n * U ^ (11 + 3 * c) ≤ (N ^ 2) * N ^ c * N * N ^ (e * (11 + 3 * c)) := by
      have h6 : 6 ≤ N ^ 2 :=
        calc 6 ≤ 3 ^ 2 := by norm_num
          _ ≤ N ^ 2 := Nat.pow_le_pow_left hN3 2
      exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h6 h3c) hn') hUe
    refine step.trans (this.trans ?_)
    apply le_of_eq
    rw [← pow_add, ← pow_succ, ← pow_add]
    congr 1
    ring
  have hT : 1 ≤ 2 ^ (610 * c * K ^ 4 * b) := Nat.one_le_two_pow
  rw [hTotal, ← hb]
  have hNp : N ^ (e * (11 + 3 * c) + c + 3) ≤ N ^ (e * (11 + 3 * c) + 2 * c + 4) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hNq : N ^ c ≤ N ^ (e * (11 + 3 * c) + 2 * c + 4) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have e2 : 2 * 2 ^ (610 * c * K ^ 4 * b) ≤ 2 ^ (611 * c * K ^ 4 * b) := by
    have hX : 1 ≤ c * K ^ 4 * b :=
      Nat.mul_pos (Nat.mul_pos hc (by omega)) (by omega)
    obtain ⟨X, hXd⟩ : ∃ X, X = c * K ^ 4 * b := ⟨_, rfl⟩
    have h6 : 610 * c * K ^ 4 * b = 610 * X := by rw [hXd]; ring
    have h7 : 611 * c * K ^ 4 * b = 611 * X := by rw [hXd]; ring
    rw [← hXd] at hX
    rw [h6, h7]
    calc 2 * 2 ^ (610 * X) = 2 ^ (610 * X + 1) := by rw [pow_succ]; ring
      _ ≤ 2 ^ (611 * X) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have a1 : 2 ^ (610 * c * K ^ 4 * b) * N ^ c ≤
      2 ^ (610 * c * K ^ 4 * b) * N ^ (e * (11 + 3 * c) + 2 * c + 4) :=
    Nat.mul_le_mul_left _ hNq
  have a2 : Outer ≤ 2 ^ (610 * c * K ^ 4 * b) * N ^ (e * (11 + 3 * c) + 2 * c + 4) := by
    refine hOut.trans (hNp.trans ?_)
    exact Nat.le_mul_of_pos_left _ hT
  have a3 : 2 * 2 ^ (610 * c * K ^ 4 * b) * N ^ (e * (11 + 3 * c) + 2 * c + 4) ≤
      2 ^ (611 * c * K ^ 4 * b) * N ^ (e * (11 + 3 * c) + 2 * c + 4) :=
    Nat.mul_le_mul_right _ e2
  generalize 2 ^ (610 * c * K ^ 4 * b) = T at *
  generalize 2 ^ (611 * c * K ^ 4 * b) = T' at *
  generalize N ^ (e * (11 + 3 * c) + 2 * c + 4) = M at *
  generalize N ^ c = M0 at *
  generalize RuntimeComposition.localTotal Loc K = L at *
  have : 2 * T * M = T * M + T * M := by ring
  omega

end RuntimeComposition
