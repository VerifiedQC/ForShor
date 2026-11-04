import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.Field.Basic

namespace SeparationLemmas

open Finset

/-- Gap-separated family. -/
def GapSep {ι : Type*} [Fintype ι] (H : ℕ) (ε lam : ι → ℤ) (c : ι → ℕ) : Prop :=
  (Fintype.card ι < 2 ^ H) ∧ (∀ i, ε i ∈ ({-1, 0, 1} : Set ℤ)) ∧
    (∀ i j, c i < c j → lam i + H ≤ lam j)

/-- Cluster sum `S_q`. -/
noncomputable def clusterSum {ι : Type*} [Fintype ι] (ε lam : ι → ℤ) (c : ι → ℕ) (q : ℕ) : ℚ :=
  by classical exact ∑ i ∈ Finset.univ.filter (fun i => c i = q), (ε i : ℚ) * (2 : ℚ) ^ (lam i)

/-- Total `S`. -/
noncomputable def total {ι : Type*} [Fintype ι] (ε lam : ι → ℤ) : ℚ :=
  ∑ i, (ε i : ℚ) * (2 : ℚ) ^ (lam i)

/-- A rational is an integer. -/
def IsIntQ (x : ℚ) : Prop := x ∈ Set.range (Int.cast : ℤ → ℚ)

end SeparationLemmas
