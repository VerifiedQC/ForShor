import Provider.Compression.Potential
import Provider.Profiles.Intervals

/-! # Paired Baseline and Charge Ceiling
Defines `PairedBaseline`, an actual legal literal-F2 source table with arity `k`, charge at most `6 * k^2` and both raw peaks at most `8 * k^2`. Proves `feasible_has_ceiling` and the conditional uniform ceiling `minCharge_le_27_cube_of_baseline` for the minimum raw F2 charge. The ceiling is conditional on a paired baseline existing; it does not assert that the baseline constructor exists or compute the minimum.
-/

namespace Paper.F3ChargeCeiling

open Paper.F2CatalogTransfer Paper.F4ChargeIntervals
open TableGeneration Paper.SourceBridge

/-- A paired baseline is an actual legal literal-F2 source table. Its
existence uniformly in the arity is a separate construction obligation. -/
def PairedBaseline {K : Nat} (k : Nat) (t : F2Source K) : Prop :=
  t.arity = k ∧ t.charge ≤ 6 * k^2 ∧
    (rawProfile t).peakA ≤ 8 * k^2 ∧
    (rawProfile t).peakB ≤ 8 * k^2

theorem source_closed {K : Nat} (t : F2Source K) :
    Paper.FullDSL.runRows (mapToFull t.source.program)
      (Paper.FullDSL.identity t.arity) =
        some (Paper.FullDSL.identity t.arity) := by
  have h := (returnsToStartCheck_eq_true_iff_model
    t.source.program TableGeneration.State.start_state t.safe.safe_add).mp
    t.safe.returns_start
  simpa only [F2Source.arity, source_start_eq_identity] using h

theorem source_charge_cap_bound {K : Nat} (t : F2Source K) :
    let p := rawProfile t
    t.charge ≤ 3 * (t.arity * p.peakA) ∧
      t.charge ≤ 3 * (t.arity * p.peakB + (t.arity - 1)^2) := by
  have h := Paper.ScannerPotential.source_charged_bound
    (finLast (positive_of_ge_two t.source.hk)) t.source.program
    (source_closed t)
  rcases h with ⟨hpaid, hcharge⟩
  dsimp [rawProfile, F2Source.arity, F2Source.charge]
  constructor
  · exact hcharge.trans (Nat.mul_le_mul_left 3 (hpaid.trans (Nat.min_le_left ..)))
  · exact hcharge.trans (Nat.mul_le_mul_left 3 (hpaid.trans (Nat.min_le_right ..)))

theorem feasible_has_ceiling {K : Nat} {k d a C : Nat}
    (hk : 2 ≤ k) (hfeasible : feasible (K := K) k d a C)
    (baseline : F2Source K) (hbase : PairedBaseline k baseline) :
    feasible (K := K) k d a (27 * k^3) := by
  rcases hfeasible with ⟨hda, t, htarity, hA, hB, hC⟩
  rcases hbase with ⟨hbarity, hbc, hbA, hbB⟩
  by_cases ha : 8 * k^2 ≤ a
  · by_cases hb : 8 * k^2 ≤ a - d
    · refine ⟨hda, baseline, hbarity, hbA.trans ha, hbB.trans hb, ?_⟩
      calc
        baseline.charge ≤ 6 * k^2 := hbc
        _ ≤ 27 * k^3 := by nlinarith [Nat.zero_le (k^2), Nat.zero_le (k^3)]
    · have hsmall : a - d ≤ 8 * k^2 := by omega
      have hcap := (source_charge_cap_bound t).2
      have hcb : t.charge ≤ 3 * (k * (a - d) + (k - 1)^2) := by
        rw [htarity] at hcap
        exact hcap.trans (Nat.mul_le_mul_left 3
          (Nat.add_le_add_right (Nat.mul_le_mul_left k hB) _))
      refine ⟨hda, t, htarity, hA, hB, ?_⟩
      have hsq : (k - 1)^2 ≤ k^2 := by nlinarith [Nat.sub_le k 1]
      have hcube : k^2 ≤ k^3 := by nlinarith [Nat.zero_le (k^2)]
      nlinarith [Nat.mul_le_mul_left k hsmall]
  · have hsmall : a ≤ 8 * k^2 := by omega
    have hcap := (source_charge_cap_bound t).1
    have hca : t.charge ≤ 3 * (k * a) := by
      rw [htarity] at hcap
      exact hcap.trans (Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left k hA))
    refine ⟨hda, t, htarity, hA, hB, ?_⟩
    nlinarith [Nat.mul_le_mul_left k hsmall, Nat.zero_le (k^3)]

/-- Conditional uniform ceiling for the *minimum* raw F2 charge. It does
not assert the paired baseline constructor exists or compute the minimum. -/
theorem minCharge_le_27_cube_of_baseline {K : Nat} {k d a C : Nat}
    (hk : 2 ≤ k) (hfeasible : feasible (K := K) k d a C)
    (baseline : F2Source K) (hbase : PairedBaseline k baseline) :
    minCharge (K := K) k d a ≤ (27 * k^3 : WithTop Nat) :=
  minCharge_le_budget (feasible_has_ceiling hk hfeasible baseline hbase)

end Paper.F3ChargeCeiling
