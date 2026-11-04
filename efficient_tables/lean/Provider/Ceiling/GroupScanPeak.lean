import Provider.Ceiling.GroupWords

/-! # Group Scan Peaks
Proves peak bounds for scans over fixed words: `balanced_fresh_bound`, `retarget_bound` for moving to a new target register, and `scan_two_fixed_peak` for scanning with two fixed registers.
-/

namespace Paper.F3ChargeCeiling

open Paper.Scanner Paper.SourceBridge Paper.FullDSL

theorem balanced_fresh_bound {k : Nat} (top d : Fin k) (r E : Nat) :
    BoundState d r E 0 (fresh (balanced top 0 r)) := by
  have hrow : ∀ i, balanced top 0 r i ≤ r := by
    intro i
    simp only [balanced, Nat.zero_add]
    split <;> omega
  have hpeak : (fresh (balanced top 0 r)).peak ≤ r := by
    exact maximum_le_of_rows _ _ hrow
  refine ⟨by simpa using hpeak.trans (by omega), ?_, ?_⟩
  · exact (hrow d).trans (by omega)
  · intro i _
    exact hrow i

theorem retarget_bound {k : Nat} {d d' : Fin k} {B E n : Nat}
    {s : Scanner.State k} (h : BoundState d B E n s) :
    BoundState d' (B + E + n) E 0 s := by
  rcases h with ⟨hp, hd, ho⟩
  refine ⟨by omega, ?_, ?_⟩
  · by_cases heq : d' = d
    · subst d'
      omega
    · have := ho d' heq
      omega
  · intro i _
    by_cases heq : i = d
    · subst i
      omega
    · have := ho i heq
      omega

theorem scan_two_fixed_peak {k : Nat} (top d d' : Fin k)
    (r E : Nat) (wi wf : List (Op k))
    (hi : FixedWord d E wi) (hf : FixedWord d' E wf) :
    (scan (wi ++ wf) (fresh (balanced top 0 r))).peak ≤
      r + 2*E + wi.length + wf.length := by
  have h0 := balanced_fresh_bound top d r E
  have h1 := fixed_scan wi (fresh (balanced top 0 r)) hi h0
  have h1' := retarget_bound (d' := d') h1
  have h2 := fixed_scan wf (scan wi (fresh (balanced top 0 r))) hf h1'
  rw [scan_append]
  exact h2.1.trans (by omega)

end Paper.F3ChargeCeiling
