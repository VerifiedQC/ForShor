import Provider.Effective.Enumeration
import Provider.Effective.Keys
import Provider.Weights.Projective

/-! # Minimum-Profile Provider
Defines the computable provider over profile keys: `catalog`, `fallback`, `rawEntry`, `entry`, `pick` and `provider`. Proves `pick_relevant`, `rawEntry_pick_spec`, `catalog_mem`, `entry_literal` and `catalog_length`.
-/

namespace Paper.ComputableProfileProvider

open Paper.F2CatalogTransfer Paper.F4ChargeIntervals
open Paper.BoundedThreshold Paper.PrefixPaddingStage
open Paper.CompressionComplete

abbrev Index (K root : Nat) := ProfileKey K root

def catalog (K root : Nat) : List (Index K root) :=
  (List.finRange (K+1)).flatMap fun k =>
    (List.finRange (root+1)).flatMap fun a =>
      (List.finRange (root+1)).map fun b => (k, (a, b))

def fallback {K : Nat} (hK : 2 ≤ K) : F2Source K :=
  Paper.F3ChargeCeiling.groupedLiteralBaseline 2 (by omega) hK

def rawEntry {K root : Nat} (hK : 2 ≤ K) (key : Index K root) :
    F2Source K :=
  let k := key.1.val
  let a := key.2.1.val
  let b := key.2.2.val
  if hk : 2 ≤ k then
    if hba : b ≤ a then
      if hcanon : a ≤ b + (k - 1) then
        match firstBudget hk (Nat.le_of_lt_succ key.1.isLt)
            a b (27*k^3) with
        | some (_, t) => paddedF2Source t a b
        | none => fallback hK
      else fallback hK
    else fallback hK
  else fallback hK

def entry {K root : Nat} (hK : 2 ≤ K) (key : Index K root) :
    Paper.PPEndToEnd.VerifiedPPCandidate K :=
  Paper.A4Certificate.verifiedSource (rawEntry hK key)

def pick {K root : Nat} (t : F2Source K) : Index K root :=
  (⟨t.arity, Nat.lt_succ_of_le t.cap⟩,
    ⟨⟨min (sourcePeaks t).1 root, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩,
     ⟨min (sourcePeaks t).2 root, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩⟩)

theorem pick_relevant {K root : Nat} (t : F2Source K)
    (hrel : Relevant root t) : pick (root := root) t = relevantKey t hrel := by
  obtain ⟨hA, hB⟩ := relevant_peaks_bounded t hrel
  simp [pick, relevantKey, Nat.min_eq_left hA, Nat.min_eq_left hB]

theorem firstBudget_for_source {K root : Nat} (t : F2Source K)
    (hrel : Relevant root t) :
    ∃ C u, firstBudget t.source.hk t.cap
        (sourcePeaks t).1 (sourcePeaks t).2 (27*t.arity^3) = some (C,u) ∧
      u.arity = t.arity ∧ u.charge = C ∧
      (rawProfile u).peakA ≤ (sourcePeaks t).1 ∧
      (rawProfile u).peakB ≤ (sourcePeaks t).2 ∧
      C ≤ t.charge := by
  let a := (sourcePeaks t).1
  let b := (sourcePeaks t).2
  have hcanon := original_profile_canonical t
  have hba : b ≤ a := by
    simpa [a, b, sourcePeaks, originalA, originalB,
      sourceProfileRaw, rawProfile] using hcanon.1
  have hsub : a - (a-b) = b := by omega
  have hA : (rawProfile t).peakA = a := rfl
  have hB : (rawProfile t).peakB = b := rfl
  have hfeas : feasible (K := K) t.arity (a-b) a t.charge := by
    refine ⟨by omega, t, rfl, ?_, ?_, le_rfl⟩
    · omega
    · omega
  obtain ⟨C,u,hfound,huarity,hcharge,huA,huB,hminimal⟩ :=
    firstBudget_exists_of_feasible t.source.hk t.cap
      (by omega : a-b ≤ a) hfeas
  refine ⟨C,u,?_,huarity,hcharge,huA,?_,?_⟩
  · simpa [a, b, F2Source.arity, hsub] using hfound
  · simpa [a, b, hsub] using huB
  · apply hminimal t rfl
    · omega
    · omega

theorem rawEntry_pick_spec {K root : Nat} (hK : 2 ≤ K)
    (t : F2Source K) (hrel : Relevant root t) :
    let v := rawEntry hK (pick (root := root) t)
    v.arity = t.arity ∧ sourcePeaks v = sourcePeaks t ∧
      v.charge ≤ t.charge := by
  obtain ⟨C,u,hfound,huarity,hcharge,huA,huB,hminimal⟩ :=
    firstBudget_for_source t hrel
  have hcanonical := original_profile_canonical t
  have hBA : (sourcePeaks t).2 ≤ (sourcePeaks t).1 := by
    simpa [sourcePeaks, originalA, originalB, sourceProfileRaw, rawProfile]
      using hcanonical.1
  have hCanon : (sourcePeaks t).1 ≤ (sourcePeaks t).2 + (t.arity - 1) := by
    simpa [sourcePeaks, originalA, originalB, sourceProfileRaw, rawProfile,
      F2Source.arity] using hcanonical.2
  have hCanonU : (sourcePeaks t).1 ≤ (sourcePeaks t).2 + (u.source.k - 1) := by
    change (sourcePeaks t).1 ≤ (sourcePeaks t).2 + (u.arity - 1)
    rw [huarity]
    exact hCanon
  let v := paddedF2Source u (sourcePeaks t).1 (sourcePeaks t).2
  have hp := paddedF2Source_exactPeaks u (sourcePeaks t).1
    (sourcePeaks t).2 hBA hCanonU huA huB
  have hpeaks : sourcePeaks v = sourcePeaks t := by
    apply Prod.ext
    · simpa [v, sourcePeaks, rawProfile, sourceProfileRaw] using hp.1
    · simpa [v, sourcePeaks, rawProfile, sourceProfileRaw] using hp.2
  have hcharge : v.charge = u.charge := by
    simp [v, F2Source.charge, paddedF2Source, paddingPrefix,
      Paper.PPEndToEnd.chargedCount, Paper.PPEndToEnd.chargedOp]
  have hraw : rawEntry hK (pick (root := root) t) = v := by
    rw [pick_relevant t hrel]
    simp only [rawEntry, relevantKey]
    have hk : 2 ≤ t.arity := t.source.hk
    simp only [dif_pos hk, dif_pos hBA, dif_pos hCanon, hfound, v]
  rw [hraw]
  exact ⟨by simpa [v, F2Source.arity] using huarity,
    hpeaks, by omega⟩

theorem catalog_mem {K root : Nat} (key : Index K root) :
    key ∈ catalog K root := by
  rcases key with ⟨k, ⟨a, b⟩⟩
  simp [catalog]

theorem entry_literal {K root : Nat} (hK : 2 ≤ K) (key : Index K root) :
    VerifiedLiteralF2 (entry hK key) :=
  (Paper.A4Certificate.verifiedSource_literal (rawEntry hK key)).2

def provider {K root : Nat} (hK : 2 ≤ K) :
    CompleteProvider root (entry (root := root) hK) (catalog K root) := by
  refine {
    pick := pick,
    catalog_literal := ?_, member := ?_, arity := ?_, width := ?_, charge := ?_
  }
  · intro c hc
    exact entry_literal hK c
  · intro t hrel
    exact catalog_mem (pick (root := root) t)
  · intro t hrel
    exact (rawEntry_pick_spec hK t hrel).1
  · intro t hrel w
    have hs := rawEntry_pick_spec hK t hrel
    exact sourcePeaks_width_eq _ t hs.1 hs.2.1 w
  · intro t hrel
    exact (rawEntry_pick_spec hK t hrel).2.2

theorem catalog_length (K root : Nat) :
    (catalog K root).length = (K+1) * (root+1)^2 := by
  simp [catalog, List.length_flatMap, pow_two]

end Paper.ComputableProfileProvider
