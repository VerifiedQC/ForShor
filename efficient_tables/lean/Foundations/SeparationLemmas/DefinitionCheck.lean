import Foundations.SeparationLemmas.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card

namespace SeparationLemmas

open Finset

theorem definitions_unfold {ι : Type*} [Fintype ι] [DecidableEq ι] (H : ℕ) (ε lam : ι → ℤ) (c : ι → ℕ) :
    (SeparationLemmas.GapSep H ε lam c ↔
      (Fintype.card ι < 2 ^ H ∧ (∀ i, ε i ∈ ({-1, 0, 1} : Set ℤ)) ∧
        ∀ i j, c i < c j → lam i + H ≤ lam j)) ∧
    (∀ q : ℕ, SeparationLemmas.clusterSum ε lam c q =
      ∑ i ∈ Finset.univ.filter (fun i => c i = q), (ε i : ℚ) * (2 : ℚ) ^ (lam i)) ∧
    SeparationLemmas.total ε lam = ∑ i, (ε i : ℚ) * (2 : ℚ) ^ (lam i) := by
  refine ⟨Iff.rfl, fun q => ?_, rfl⟩
  unfold SeparationLemmas.clusterSum
  congr 1

end SeparationLemmas
