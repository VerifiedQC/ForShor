import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic

namespace Paper

theorem diagonal_cover_injection {A B : Type*}
    (L R : B → A → Prop)
    (cover : ∀ i, ∃ b, L b i ∧ R b i)
    (sound : ∀ b i j, L b i → R b j → i = j) :
    ∃ f : A → B, Function.Injective f := by
  classical
  let f : A → B := fun i => Classical.choose (cover i)
  have hf : ∀ i, L (f i) i ∧ R (f i) i := fun i => Classical.choose_spec (cover i)
  refine ⟨f, ?_⟩
  intro i j h
  apply sound (f i) i j (hf i).1
  rw [h]
  exact (hf j).2

theorem diagonal_cover_card {A B : Type*} [Fintype A] [Fintype B]
    (L R : B → A → Prop)
    (cover : ∀ i, ∃ b, L b i ∧ R b i)
    (sound : ∀ b i j, L b i → R b j → i = j) :
    Fintype.card A ≤ Fintype.card B := by
  obtain ⟨f, hf⟩ := diagonal_cover_injection L R cover sound
  exact Fintype.card_le_of_injective f hf

theorem separate_minima_can_fail (M : ℚ) (h : 0 < M) :
    min 0 M + min M 0 < min (0 + M) (M + 0) := by
  simp [min_eq_left (le_of_lt h), min_eq_right (le_of_lt h), h]

end Paper
