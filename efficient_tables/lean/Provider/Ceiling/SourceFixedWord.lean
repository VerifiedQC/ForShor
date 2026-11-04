import Provider.Ceiling.FixedScanner

/-! # Source Fixed Words
Defines `SourceFixed`, the fixed-word property for source programs. Proves it is closed under append (`sourceFixed_append`) and inverse (`sourceFixed_inverse`) and holds for width words (`sourceFixed_widthWord`).
-/

namespace Paper.F3ChargeCeiling

open TableGeneration Paper.SourceBridge Paper.FullDSL

def SourceFixed {k : Nat} (d : Fin k) (E : Nat) (word : Prog k) : Prop :=
  ∀ op ∈ word, (∃ i, op = .phaseProduct i) ∨
    ∃ src neg sh, src ≠ d ∧ sh ≤ E ∧ op = .addScaled d src neg sh

theorem sourceFixed_append {k : Nat} {d : Fin k} {E : Nat}
    {first second : Prog k} (hfirst : SourceFixed d E first)
    (hsecond : SourceFixed d E second) :
    SourceFixed d E (first ++ second) := by
  intro op hop
  rcases List.mem_append.mp hop with h | h
  · exact hfirst op h
  · exact hsecond op h

theorem sourceFixed_inverse {k : Nat} {d : Fin k} {E : Nat}
    {word : Prog k} (h : SourceFixed d E word) :
    SourceFixed d E (apply_Op_inverse word) := by
  intro op hop
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hop
  have hw : old ∈ word := List.mem_reverse.mp hold
  rcases h old hw with ⟨i, rfl⟩ | ⟨src, neg, sh, hsrc, hsh, rfl⟩
  · exact Or.inl ⟨i, rfl⟩
  · exact Or.inr ⟨src, !neg, sh, hsrc, hsh, rfl⟩

theorem sourceFixed_widthWord {k : Nat} {d : Fin k} {E : Nat}
    {word : Prog k} (h : SourceFixed d E word) :
    FixedWord d E (widthWord (mapToFull word)) := by
  intro op hop
  simp only [widthWord, mapToFull, List.map_map] at hop
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hop
  rcases h old hold with ⟨i, rfl⟩ | ⟨src, neg, sh, hsrc, hsh, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨src, sh, hsrc, hsh, rfl⟩

end Paper.F3ChargeCeiling
