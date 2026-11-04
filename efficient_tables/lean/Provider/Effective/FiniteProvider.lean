import Provider.Effective.Keys

/-! # Finite Provider from Representatives
Defines the noncomputable `representative` of a profile key and assembles `providerRaw`, `providerEntry`, `providerCatalog`, `providerPick` and `finiteCompleteProvider`. Proves `representative_realizes` and `representative_le`. The definitions are noncomputable, so this file gives existence rather than an executable provider.
-/

namespace Paper.F2CatalogTransfer

noncomputable def representative {K root : Nat} (fallback : F2Source K)
    (key : ProfileKey K root) : F2Source K := by
  classical
  exact if h : ∃ t : F2Source K, Realizes key t then minSource key h else fallback

theorem representative_realizes {K root : Nat} (fallback : F2Source K)
    (key : ProfileKey K root) (h : ∃ t : F2Source K, Realizes key t) :
    Realizes key (representative fallback key) := by
  classical
  simp only [representative, dif_pos h]
  exact minSource_realizes key h

theorem representative_le {K root : Nat} (fallback : F2Source K)
    (key : ProfileKey K root) (t : F2Source K) (ht : Realizes key t) :
    (representative fallback key).charge ≤ t.charge := by
  classical
  let h : ∃ u : F2Source K, Realizes key u := ⟨t, ht⟩
  simp only [representative, dif_pos h]
  exact minSource_le key h t ht

noncomputable def providerRaw {K root : Nat} (fallback : F2Source K) :
    Option (ProfileKey K root) → F2Source K
  | none => fallback
  | some key => representative fallback key

noncomputable def providerEntry {K root : Nat} (fallback : F2Source K) :
    Option (ProfileKey K root) → Paper.PPEndToEnd.VerifiedPPCandidate K :=
  fun c => (providerRaw fallback c).toVerified
    (Classical.choice (f2Source_certificate_exists (providerRaw fallback c)))

noncomputable def providerCatalog (K root : Nat) :
    List (Option (ProfileKey K root)) := by
  classical
  exact (Finset.univ : Finset (Option (ProfileKey K root))).toList

noncomputable def providerPick {K root : Nat} (t : F2Source K) :
    Option (ProfileKey K root) := by
  classical
  exact if h : Relevant root t then some (relevantKey t h) else none

noncomputable def finiteCompleteProvider {K root : Nat} (fallback : F2Source K) :
    CompleteProvider root (providerEntry fallback) (providerCatalog K root) := by
  classical
  refine {
    pick := providerPick,
    catalog_literal := ?_, member := ?_, arity := ?_, width := ?_, charge := ?_
  }
  . intro c hc
    exact toVerified_literal (providerRaw fallback c)
      (Classical.choice (f2Source_certificate_exists (providerRaw fallback c)))
  . intro t hrel
    simp only [providerCatalog, Finset.mem_toList]
    exact Finset.mem_univ _
  . intro t hrel
    have ht := relevantKey_realizes t hrel
    have hr := representative_realizes fallback (relevantKey t hrel) ⟨t, ht⟩
    change (providerRaw fallback (providerPick t)).arity = t.arity
    simpa only [providerPick, dif_pos hrel, providerRaw] using hr.1.trans ht.1.symm
  . intro t hrel w
    have ht := relevantKey_realizes t hrel
    have hr := representative_realizes fallback (relevantKey t hrel) ⟨t, ht⟩
    have he := realizes_width_eq hr ht w
    change (providerRaw fallback (providerPick t)).childWidth w = t.childWidth w
    simpa only [providerPick, dif_pos hrel, providerRaw] using he
  . intro t hrel
    have ht := relevantKey_realizes t hrel
    have hle := representative_le fallback (relevantKey t hrel) t ht
    change (providerRaw fallback (providerPick t)).charge ≤ t.charge
    simpa only [providerPick, dif_pos hrel, providerRaw] using hle

end Paper.F2CatalogTransfer
