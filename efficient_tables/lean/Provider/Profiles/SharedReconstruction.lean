import Provider.Profiles.Reconstruction

/-!
# Exact-profile reconstruction with shared child width

The shared-child-width version of exact-profile reconstruction. The single
theorem `minCharge_exactProfile_sharedChildWidth` says one actual
minimum-charge source realizes the exact profile and therefore its child-width
formula.
-/

namespace Paper.F4PaddingReconstructionShared

open Paper.F2CatalogTransfer
open Paper.F4ChargeIntervals
open Paper.F4PaddingReconstruction
open Paper.PrefixPaddingStage
open Paper.SourceBridge
open TableGeneration

/-- One actual minimum-charge source realizes the exact profile and therefore
has the canonical child-width formula simultaneously at every input width. -/
theorem minCharge_exactProfile_sharedChildWidth {K k d a : Nat}
    (hfeas : ∃ C, feasible (K := K) k d a C) (hdk : d < k) :
    ∃ t : F2Source K,
      t.arity = k ∧ t.charge = leastBudget hfeas ∧
      (rawProfile t).peakA = a ∧ (rawProfile t).peakB = a - d ∧
      minCharge (K := K) k d a = (t.charge : WithTop Nat) ∧
      ∀ w, F2Source.childWidth t w =
        w / k + 1 + max a ((a - d) + w % k) := by
  obtain ⟨t, harity, hcharge, hA, hB, hmin⟩ :=
    minCharge_exactProfile hfeas hdk
  refine ⟨t, harity, hcharge, hA, hB, hmin, ?_⟩
  intro w
  have hwscan :
      F2Source.childWidth t w =
        Paper.Planner.childWidth t.source.k (sourceProfileRaw t) w := by
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

end Paper.F4PaddingReconstructionShared
