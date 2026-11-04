import Provider.Compression.Padding
import Provider.Profiles.Intervals

/-!
# Exact-profile reconstruction

A finite least-charge witness can be realized at the exact profile
(`minCharge_exactProfile`), and the exact padded profile gives the same closed
formula for the actual child width (`minCharge_exactProfile_childWidth`).
-/

namespace Paper.F4PaddingReconstruction

open Paper.F2CatalogTransfer
open Paper.F4ChargeIntervals
open Paper.PrefixPaddingStage
open Paper.SourceBridge
open TableGeneration

/-- A finite least-charge witness can be realized at the exact profile
(a,a-d) by prepending legal, reversible excursions. The side condition d<k
is the scanner's canonical profile condition; F4 feasibility alone permits
larger d and does not imply this theorem's hypothesis. -/
theorem minCharge_exactProfile {K k d a : Nat}
    (hfeas : ∃ C, feasible (K := K) k d a C) (hdk : d < k) :
    ∃ t : F2Source K,
      t.arity = k ∧ t.charge = leastBudget hfeas ∧
      (rawProfile t).peakA = a ∧ (rawProfile t).peakB = a - d ∧
      minCharge (K := K) k d a = (t.charge : WithTop Nat) := by
  obtain ⟨t, hda, hk, hA, hB, hcharge, hmin⟩ := minCharge_attained hfeas
  let b := a - d
  have hsourcearity : t.source.k = k := by
    simpa [F2Source.arity] using hk
  have hba : b ≤ a := Nat.sub_le _ _
  have hcanon : a ≤ b + (t.source.k - 1) := by
    dsimp [b]
    omega
  let t' := paddedF2Source t a b
  have hpeaks := paddedF2Source_exactPeaks t a b hba hcanon hA hB
  have hcharge' : t'.charge = leastBudget hfeas := by
    have heq : t'.charge = t.charge := by
      simp [t', F2Source.charge, paddedF2Source, paddingPrefix,
        Paper.PPEndToEnd.chargedCount, Paper.PPEndToEnd.chargedOp]
    exact heq.trans hcharge
  have hmin' : minCharge (K := K) k d a = (t'.charge : WithTop Nat) := by
    calc
      minCharge (K := K) k d a = (t.charge : WithTop Nat) := hmin
      _ = (t'.charge : WithTop Nat) := by
        exact_mod_cast hcharge.trans hcharge'.symm
  refine ⟨t', ?_, hcharge', ?_, ?_, hmin'⟩
  · simpa [t', F2Source.arity] using hk
  · simpa [t', F4ChargeIntervals.rawProfile, sourceProfileRaw] using hpeaks.1
  · simpa [t', b, F4ChargeIntervals.rawProfile, sourceProfileRaw] using hpeaks.2

/-- The exact padded profile gives the same closed formula for the actual
source interpreter's next balanced signed width at every input width. -/
theorem minCharge_exactProfile_childWidth {K k d a w : Nat}
    (hfeas : ∃ C, feasible (K := K) k d a C) (hdk : d < k) :
    ∃ t : F2Source K,
      t.arity = k ∧
      F2Source.childWidth t w =
        w / k + 1 + max a ((a - d) + w % k) := by
  obtain ⟨t, harity, hcharge, hA, hB, hmin⟩ := minCharge_exactProfile hfeas hdk
  refine ⟨t, harity, ?_⟩
  have hwscan :
      F2Source.childWidth t w =
        Paper.Planner.childWidth t.source.k
          (sourceProfileRaw t) w := by
    let hkpos := TableGeneration.positive_of_ge_two t.source.hk
    let top := TableGeneration.finLast hkpos
    have htop : top.val + 1 = t.source.k := by
      have hhk := t.source.hk
      dsimp [top, TableGeneration.finLast]
      omega
    have hsafe : TableGeneration.safeProg? t.source.program = true := t.safe.safe_add
    have hrows0 :
        FullDSL.runRows (SourceBridge.mapToFull t.source.program)
          TableGeneration.State.start_state = some TableGeneration.State.start_state := by
      exact (returnsToStartCheck_eq_true_iff_model t.source.program
        TableGeneration.State.start_state hsafe).mp t.safe.returns_start
    have hrows : FullDSL.runRows (SourceBridge.mapToFull t.source.program)
        (FullDSL.identity t.source.k) = some TableGeneration.State.start_state := by
      calc
        FullDSL.runRows (SourceBridge.mapToFull t.source.program)
            (FullDSL.identity t.source.k) =
          FullDSL.runRows (SourceBridge.mapToFull t.source.program)
            TableGeneration.State.start_state := by rw [← source_start_eq_identity]
        _ = some TableGeneration.State.start_state := hrows0
    have hsuccess :
        TableGeneration.run? t.source.program TableGeneration.State.start_state =
          some TableGeneration.State.start_state := by
      rw [← runRows_from_start_of_safe t.source.program hsafe]
      exact hrows
    exact original_legal_program_childWidth top htop t.source.program
      TableGeneration.State.start_state hsafe hsuccess w
  rw [hwscan]
  have hpeaks : (sourceProfileRaw t).peakA = a ∧
      (sourceProfileRaw t).peakB = a - d := by
    simpa [F4ChargeIntervals.rawProfile] using ⟨hA, hB⟩
  have hk' : t.source.k = k := by simpa [F2Source.arity] using harity
  simp [Paper.Planner.childWidth, hpeaks.1, hpeaks.2, hk']

end Paper.F4PaddingReconstruction
