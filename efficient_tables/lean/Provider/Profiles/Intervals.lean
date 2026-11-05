import Provider.Ladders.CatalogTransfer

/-!
# Profile charge intervals

Defines the two-cap profile `rawProfile` of a raw F2 source table, fixed-kink
cap feasibility `feasible`, and the least charge budget `minCharge` realizing
some raw table under the caps. It proves that finite minima are attained by an
actual table (`minCharge_attained`), that feasibility is equivalent to the
minimum being within budget (`feasible_iff_minCharge_le_budget`), and that
`minCharge` is antitone in the first cap with level sets forming intervals
(`minCharge_level_interval`).
-/

namespace Paper.F4ChargeIntervals

open Paper.F2CatalogTransfer
open Paper.SourceBridge
open TableGeneration

/-- The actual two-cap profile of a raw F2 source table, read through the
accepted sourceProfile scanner bridge at the high register. -/
def rawProfile {K : Nat} (t : F2Source K) : Paper.Planner.Profile :=
  sourceProfile (TableGeneration.finLast
    (TableGeneration.positive_of_ge_two t.source.hk)) t.source.program

/-- Fixed-kink cap feasibility in the raw, legal F2 domain. We keep the
constraint `d ≤ a` explicit, so the second cap is the intended natural
number `a-d`, not a truncated surrogate. -/
def feasible {K : Nat} (k d a C : Nat) : Prop :=
  d ≤ a ∧ ∃ t : F2Source K,
    t.arity = k ∧
    (rawProfile t).peakA ≤ a ∧
    (rawProfile t).peakB ≤ a - d ∧
    t.charge ≤ C

theorem feasible_cap_mono {K : Nat} {k d a b C : Nat}
    (hab : a ≤ b) (h : feasible (K := K) k d a C) :
    feasible (K := K) k d b C := by
  rcases h with ⟨hda, t, hk, hA, hB, hC⟩
  refine ⟨hda.trans hab, t, hk, hA.trans hab, ?_, hC⟩
  exact hB.trans (Nat.sub_le_sub_right hab d)

theorem feasible_budget_mono {K : Nat} {k d a C D : Nat}
    (hCD : C ≤ D) (h : feasible (K := K) k d a C) :
    feasible (K := K) k d a D := by
  rcases h with ⟨hda, t, hk, hA, hB, hC⟩
  exact ⟨hda, t, hk, hA, hB, hC.trans hCD⟩

/-- Classical least element helper, isolated so public theorem types do not
expose a noncomputable decidability instance. -/
noncomputable def leastBudget {p : Nat → Prop} (h : ∃ C, p C) : Nat := by
  classical
  exact Nat.find h

theorem leastBudget_spec {p : Nat → Prop} (h : ∃ C, p C) :
    p (leastBudget h) := by
  classical
  unfold leastBudget
  exact Nat.find_spec h

theorem leastBudget_min {p : Nat → Prop} (h : ∃ C, p C) {C : Nat}
    (hC : p C) : leastBudget h ≤ C := by
  classical
  unfold leastBudget
  exact Nat.find_min' h hC

/-- Least charge budget realizing some raw legal table under the two caps;
`⊤` records infeasibility. -/
noncomputable def minCharge {K : Nat} (k d a : Nat) : WithTop Nat := by
  classical
  exact if h : ∃ C, feasible (K := K) k d a C then
    (leastBudget h : WithTop Nat)
  else ⊤

theorem minCharge_eq_leastBudget {K : Nat} {k d a : Nat}
    (h : ∃ C, feasible (K := K) k d a C) :
    minCharge (K := K) k d a = (leastBudget h : WithTop Nat) := by
  classical
  unfold minCharge
  rw [dif_pos h]

theorem minCharge_witness {K : Nat} {k d a : Nat}
    (h : ∃ C, feasible (K := K) k d a C) :
    feasible (K := K) k d a (leastBudget h) :=
  leastBudget_spec h

theorem minCharge_le_budget {K : Nat} {k d a C : Nat}
    (h : feasible (K := K) k d a C) :
    minCharge (K := K) k d a ≤ (C : WithTop Nat) := by
  classical
  by_cases hex : ∃ D, feasible (K := K) k d a D
  · rw [minCharge, dif_pos hex]
    exact_mod_cast leastBudget_min hex h
  · exact False.elim (hex ⟨C, h⟩)

/-- Every finite minimum charge is attained by an actual raw F2 source
whose arity and two canonical caps witness feasibility, and whose actual
charged instruction count equals the minimum. -/
theorem minCharge_attained {K : Nat} {k d a : Nat}
    (h : ∃ C, feasible (K := K) k d a C) :
    ∃ t : F2Source K,
      d ≤ a ∧ t.arity = k ∧
      (rawProfile t).peakA ≤ a ∧
      (rawProfile t).peakB ≤ a - d ∧
      t.charge = leastBudget h ∧
      minCharge (K := K) k d a = (t.charge : WithTop Nat) := by
  rcases minCharge_witness h with ⟨hda, t, hk, hA, hB, hbudget⟩
  have hown : feasible (K := K) k d a t.charge :=
    ⟨hda, t, hk, hA, hB, Nat.le_refl _⟩
  have hleast : leastBudget h ≤ t.charge := leastBudget_min h hown
  have heq : t.charge = leastBudget h := Nat.le_antisymm hbudget hleast
  refine ⟨t, hda, hk, hA, hB, heq, ?_⟩
  rw [minCharge_eq_leastBudget h, ← heq]
/-- A bounded charge budget is feasible exactly when the least charge is
below that budget; this is the minimum-charge form of the bounded threshold
predicate. -/
theorem feasible_iff_minCharge_le_budget {K : Nat} {k d a C : Nat} :
    feasible (K := K) k d a C ↔
      minCharge (K := K) k d a ≤ (C : WithTop Nat) := by
  constructor
  · exact minCharge_le_budget
  · classical
    intro hm
    by_cases hex : ∃ D, feasible (K := K) k d a D
    · rw [minCharge_eq_leastBudget hex] at hm
      have hmin : leastBudget hex ≤ C := by exact_mod_cast hm
      exact feasible_budget_mono hmin (leastBudget_spec hex)
    · simp [minCharge, hex] at hm
/-- Minimum charge is antitone as the first cap grows at fixed kink. -/
theorem minCharge_antitone {K : Nat} {k d a b : Nat} (hab : a ≤ b) :
    minCharge (K := K) k d b ≤ minCharge (K := K) k d a := by
  classical
  by_cases ha : ∃ C, feasible (K := K) k d a C
  · let m := leastBudget ha
    have hfa : feasible (K := K) k d a m := leastBudget_spec ha
    have hfb : feasible (K := K) k d b m := feasible_cap_mono hab hfa
    have hb : ∃ C, feasible (K := K) k d b C := ⟨m, hfb⟩
    have hle : leastBudget hb ≤ m := leastBudget_min hb hfb
    rw [minCharge, dif_pos hb, minCharge, dif_pos ha]
    exact_mod_cast hle
  · simp [minCharge, ha]
/-- On a fixed-kink ray, every finite exact minimum-charge level set is an
integer interval. -/
theorem minCharge_level_interval {K : Nat} {k d a b c v : Nat}
    (hab : a ≤ b) (hbc : b ≤ c)
    (ha : minCharge (K := K) k d a = (v : WithTop Nat))
    (hc : minCharge (K := K) k d c = (v : WithTop Nat)) :
    minCharge (K := K) k d b = (v : WithTop Nat) := by
  have h1 := minCharge_antitone (K := K) (k := k) (d := d) hbc
  have h2 := minCharge_antitone (K := K) (k := k) (d := d) hab
  rw [hc] at h1
  rw [ha] at h2
  exact le_antisymm h2 h1

end Paper.F4ChargeIntervals






#print axioms Paper.F4ChargeIntervals.feasible_cap_mono
#print axioms Paper.F4ChargeIntervals.feasible_budget_mono
#print axioms Paper.F4ChargeIntervals.leastBudget_spec
#print axioms Paper.F4ChargeIntervals.leastBudget_min
#print axioms Paper.F4ChargeIntervals.minCharge_eq_leastBudget
#print axioms Paper.F4ChargeIntervals.minCharge_witness
#print axioms Paper.F4ChargeIntervals.minCharge_le_budget
#print axioms Paper.F4ChargeIntervals.minCharge_antitone
#print axioms Paper.F4ChargeIntervals.minCharge_level_interval

#print axioms Paper.F4ChargeIntervals.feasible_iff_minCharge_le_budget


#print axioms Paper.F4ChargeIntervals.minCharge_attained

