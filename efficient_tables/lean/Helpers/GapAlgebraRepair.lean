import Mathlib.Data.Int.Basic

/- Integer implications only. No table DSL, determinant semantics,
   global induction, integer-programming algorithm or complexity model. -/
namespace Paper

theorem potential_shift_cancel (s d h : ℤ) :
    (s + h) - (d + h) = s - d := by omega

theorem potential_add_gain (v u h : ℤ) :
    1 ≤ (1 + max v (u + h)) - v := by omega

theorem potential_paid_step (t p p' : ℤ)
    (ht : t ≤ p) (hp : p + 1 ≤ p') : t + 1 ≤ p' := by omega

theorem potential_free_step (t p p' : ℤ)
    (ht : t ≤ p) (hp : p = p') : t ≤ p' := by omega

theorem closed_potential_charge_bound (t c s d s0 k a : ℤ)
    (ht : t ≤ s - d - s0) (hd : d = 0) (h0 : s0 = 0)
    (hs : s ≤ k * a) (hc : c ≤ 3 * t) :
    t ≤ k * a ∧ c ≤ 3 * (k * a) := by omega

theorem canonical_ray_rewrite (a b d r : ℤ) (hd : d = a - b) :
    max a (r + b) = a + max 0 (r - d) := by omega

theorem terminal_cut_divisibility (m terminal x tail : ℤ)
    (ht : m ∣ terminal) (hh : m ∣ tail)
    (heq : terminal = x + tail) : m ∣ x := by
  have h := Int.dvd_sub ht hh
  simpa [heq] using h

theorem scaled_residue_representation (p k x r : ℤ)
    (h : p * k ∣ x - p * r) : ∃ q : ℤ, x = p * (k * q + r) := by
  obtain ⟨q, hq⟩ := h
  refine ⟨q, ?_⟩
  rw [Int.mul_add, ← Int.mul_assoc]
  omega

theorem scaled_cut_residue (p k terminal x r tail : ℤ)
    (ht : p * k ∣ terminal) (hh : p * k ∣ tail)
    (heq : terminal = (x - p * r) + tail) :
    ∃ q : ℤ, x = p * (k * q + r) := by
  exact scaled_residue_representation p k x r
    (terminal_cut_divisibility (p * k) terminal (x - p * r) tail ht hh heq)

end Paper
