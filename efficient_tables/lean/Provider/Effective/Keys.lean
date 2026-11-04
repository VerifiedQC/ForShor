import Provider.Effective.Bridge

/-! # Profile Keys
Defines `ProfileKey K root` (an arity together with two bounded peaks), `relevantKey` and the predicate `Realizes`. Proves `relevantKey_realizes` and `realizes_width_eq`, and defines the noncomputable `minSource` with `minSource_realizes` and `minSource_le`.
-/

namespace Paper.F2CatalogTransfer

abbrev ProfileKey (K root : Nat) :=
  Fin (K + 1) × (Fin (root + 1) × Fin (root + 1))

def relevantKey {K root : Nat} (t : F2Source K) (h : Relevant root t) :
    ProfileKey K root :=
  (⟨t.arity, by change t.source.k < K + 1; exact Nat.lt_succ_of_le t.cap⟩,
    ⟨⟨(sourcePeaks t).1, by exact Nat.lt_succ_of_le (relevant_peaks_bounded t h).1⟩,
     ⟨(sourcePeaks t).2, by exact Nat.lt_succ_of_le (relevant_peaks_bounded t h).2⟩⟩)

def Realizes {K root : Nat} (key : ProfileKey K root) (t : F2Source K) : Prop :=
  t.arity = key.1.val ∧
  sourcePeaks t = (key.2.1.val, key.2.2.val) ∧
  Relevant root t

theorem relevantKey_realizes {K root : Nat} (t : F2Source K)
    (h : Relevant root t) : Realizes (relevantKey t h) t := by
  exact ⟨rfl, rfl, h⟩

theorem realizes_width_eq {K root : Nat} {key : ProfileKey K root}
    {t u : F2Source K} (ht : Realizes key t) (hu : Realizes key u) :
    ∀ w, t.childWidth w = u.childWidth w := by
  apply sourcePeaks_width_eq t u
  . exact ht.1.trans hu.1.symm
  . exact ht.2.1.trans hu.2.1.symm

private def chargeWitness {K root : Nat} (key : ProfileKey K root)
    (h : ∃ t : F2Source K, Realizes key t) :
    ∃ n : Nat, ∃ t : F2Source K, Realizes key t ∧ t.charge = n := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t.charge, t, ht, rfl⟩

noncomputable def minSource {K root : Nat} (key : ProfileKey K root)
    (h : ∃ t : F2Source K, Realizes key t) : F2Source K := by
  classical
  exact Classical.choose (Nat.find_spec (chargeWitness key h))

theorem minSource_realizes {K root : Nat} (key : ProfileKey K root)
    (h : ∃ t : F2Source K, Realizes key t) : Realizes key (minSource key h) := by
  classical
  exact (Classical.choose_spec (Nat.find_spec (chargeWitness key h))).1

theorem minSource_le {K root : Nat} (key : ProfileKey K root)
    (h : ∃ t : F2Source K, Realizes key t)
    (t : F2Source K) (ht : Realizes key t) :
    (minSource key h).charge ≤ t.charge := by
  classical
  have hs := Classical.choose_spec (Nat.find_spec (chargeWitness key h))
  have hm : Nat.find (chargeWitness key h) ≤ t.charge :=
    Nat.find_min' (chargeWitness key h) ⟨t, ht, rfl⟩
  exact hs.2 ▸ hm

end Paper.F2CatalogTransfer
