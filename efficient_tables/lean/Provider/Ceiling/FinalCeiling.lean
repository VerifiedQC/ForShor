import Provider.Ceiling.GroupedPeak

/-! # Final Charge Ceiling
Defines `BoundedF2Baseline` and shows the grouped literal baseline satisfies it (`grouped_bounded_baseline`). Discharges the baseline premise of the earlier conditional ceiling, yielding `feasible_has_ceiling_grouped` and `minCharge_le_27_cube`.
-/

namespace Paper.F3ChargeCeiling

open Paper.F2CatalogTransfer Paper.F4ChargeIntervals

def BoundedF2Baseline {K : Nat} (k : Nat) (t : F2Source K) : Prop :=
  t.arity = k ∧ (rawProfile t).peakA ≤ 8*k*k ∧
    (rawProfile t).peakB ≤ 8*k*k

theorem grouped_bounded_baseline {K k : Nat} (hk : 2 ≤ k) (hK : k ≤ K) :
    BoundedF2Baseline k (groupedLiteralBaseline k hk hK) := by
  exact ⟨rfl, (groupedLiteralBaseline_peaks hk hK).1,
    (groupedLiteralBaseline_peaks hk hK).2⟩

theorem feasible_has_ceiling_of_bounded_baseline {K : Nat} {k d a C : Nat}
    (hk : 2 ≤ k) (hfeasible : feasible (K := K) k d a C)
    (baseline : F2Source K) (hbase : BoundedF2Baseline k baseline) :
    feasible (K := K) k d a (27*k^3) := by
  rcases hfeasible with ⟨hda, t, htarity, hA, hB, hC⟩
  rcases hbase with ⟨hbarity, hbA, hbB⟩
  by_cases ha : 8*k*k ≤ a
  · by_cases hb : 8*k*k ≤ a-d
    · refine ⟨hda, baseline, hbarity, hbA.trans ha, hbB.trans hb, ?_⟩
      have hcap := (source_charge_cap_bound baseline).1
      have hbc : baseline.charge ≤ 3*(k*(8*k*k)) := by
        rw [hbarity] at hcap
        exact hcap.trans (Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left k hbA))
      calc
        baseline.charge ≤ 3*(k*(8*k*k)) := hbc
        _ = 24*k^3 := by ring
        _ ≤ 27*k^3 := by nlinarith [Nat.zero_le (k^3)]
    · have hsmall : a-d ≤ 8*k*k := by omega
      have hcap := (source_charge_cap_bound t).2
      have hcb : t.charge ≤ 3*(k*(a-d)+(k-1)^2) := by
        rw [htarity] at hcap
        exact hcap.trans (Nat.mul_le_mul_left 3
          (Nat.add_le_add_right (Nat.mul_le_mul_left k hB) _))
      refine ⟨hda, t, htarity, hA, hB, ?_⟩
      have hsq : (k-1)^2 ≤ k^2 := by nlinarith [Nat.sub_le k 1]
      have hcube : k^2 ≤ k^3 := by nlinarith [Nat.zero_le (k^2)]
      nlinarith [Nat.mul_le_mul_left k hsmall]
  · have hsmall : a ≤ 8*k*k := by omega
    have hcap := (source_charge_cap_bound t).1
    have hca : t.charge ≤ 3*(k*a) := by
      rw [htarity] at hcap
      exact hcap.trans (Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left k hA))
    refine ⟨hda, t, htarity, hA, hB, ?_⟩
    nlinarith [Nat.mul_le_mul_left k hsmall, Nat.zero_le (k^3)]

theorem feasible_has_ceiling_grouped {K : Nat} {k d a C : Nat}
    (hk : 2 ≤ k) (hfeasible : feasible (K := K) k d a C) :
    feasible (K := K) k d a (27*k^3) := by
  have hK : k ≤ K := by
    obtain ⟨_, t, htarity, _, _, _⟩ := hfeasible
    rw [← htarity]
    exact t.cap
  exact feasible_has_ceiling_of_bounded_baseline hk hfeasible
    (groupedLiteralBaseline k hk hK) (grouped_bounded_baseline hk hK)

theorem minCharge_le_27_cube {K : Nat} {k d a C : Nat}
    (hk : 2 ≤ k) (hfeasible : feasible (K := K) k d a C) :
    minCharge (K := K) k d a ≤ (27*k^3 : WithTop Nat) :=
  minCharge_le_budget (feasible_has_ceiling_grouped hk hfeasible)

end Paper.F3ChargeCeiling
