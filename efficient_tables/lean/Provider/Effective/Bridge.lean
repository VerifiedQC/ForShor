import Provider.Ladders.CertificateExists
import Model.Interpreter.SourceConnection

/-! # Source Peak Bridge
Defines `sourcePeaks`, the pair of profile peaks of an F2 source. Proves that a source has a run (`source_run_exists`), that its child width equals the profile child width (`source_childWidth_eq_profile`), and that relevant sources have bounded peaks (`relevant_peaks_bounded`).
-/

namespace Paper.F2CatalogTransfer

open TableGeneration Paper.SourceBridge

def sourcePeaks {K : Nat} (t : F2Source K) : Nat × Nat :=
  let p := sourceProfile (finLast (positive_of_ge_two t.source.hk)) t.source.program
  (p.peakA, p.peakB)

theorem source_run_exists {K : Nat} (t : F2Source K) :
    ∃ final, run? t.source.program State.start_state = some final := by
  have hr := t.safe.returns_start
  cases h : run? t.source.program State.start_state with
  | none => simp [returnsToStartCheck, h] at hr
  | some final => exact ⟨final, rfl⟩

theorem source_childWidth_eq_profile {K : Nat} (t : F2Source K) (w : Nat) :
    t.childWidth w =
      Planner.childWidth t.arity
        (sourceProfile (finLast (positive_of_ge_two t.source.hk)) t.source.program) w := by
  obtain ⟨final, hrun⟩ := source_run_exists t
  exact SourceBridge.original_legal_program_childWidth
    (finLast (positive_of_ge_two t.source.hk))
    (by simp [finLast]; have hk := t.source.hk; omega)
    t.source.program final t.safe.safe_add hrun w

theorem relevant_peaks_bounded {K : Nat} {root : Nat} (t : F2Source K)
    (hrel : Relevant root t) :
    (sourcePeaks t).1 ≤ root ∧ (sourcePeaks t).2 ≤ root := by
  obtain ⟨w, hw, hcontract⟩ := hrel
  rw [source_childWidth_eq_profile] at hcontract
  let p := sourceProfile (finLast (positive_of_ge_two t.source.hk)) t.source.program
  have hleft : p.peakA ≤ max p.peakA (p.peakB + w % t.arity) :=
    Nat.le_max_left _ _
  have hright : p.peakB ≤ max p.peakA (p.peakB + w % t.arity) := by
    have h := Nat.le_max_right p.peakA (p.peakB + w % t.arity)
    omega
  change w / t.arity + 1 + max p.peakA (p.peakB + w % t.arity) < w at hcontract
  let m := max p.peakA (p.peakB + w % t.arity)
  change w / t.arity + 1 + m < w at hcontract
  have hmaxlt : m < w := by
    have hle : m ≤ w / t.arity + 1 + m := Nat.le_add_left m _
    exact lt_of_le_of_lt hle hcontract
  change p.peakA ≤ root ∧ p.peakB ≤ root
  exact ⟨(hleft.trans_lt hmaxlt).le.trans hw, (hright.trans_lt hmaxlt).le.trans hw⟩

theorem sourcePeaks_width_eq {K : Nat} (t u : F2Source K)
    (hk : t.arity = u.arity) (hp : sourcePeaks t = sourcePeaks u) :
    ∀ w, t.childWidth w = u.childWidth w := by
  intro w
  rw [source_childWidth_eq_profile, source_childWidth_eq_profile]
  rcases Prod.mk.inj hp with ⟨ha, hb⟩
  exact Planner.childWidth_eq_of_peaks (k := t.arity) (w := w)
    (by simpa only [sourcePeaks] using ha)
    (by simpa only [sourcePeaks] using hb) |>.trans (by rw [hk])

end Paper.F2CatalogTransfer
