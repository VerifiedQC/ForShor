import Provider.Ceiling.DyadicPower

/-! # Fixed-Word Scanner
Defines `FixedWord` and `BoundState` for operation words acting on a fixed register with exponent `E`. Proves the one-step bound `fixed_advance` and its iteration `fixed_scan`, together with the helper `maximum_le_of_rows`.
-/

namespace Paper.F3ChargeCeiling

open Paper.Scanner

def FixedWord {k : Nat} (d : Fin k) (E : Nat) (word : List (Op k)) : Prop :=
  ∀ op ∈ word, op = .marker ∨
    ∃ s sh, s ≠ d ∧ sh ≤ E ∧ op = .addScaled d s sh

def BoundState {k : Nat} (d : Fin k) (B E n : Nat) (s : State k) : Prop :=
  s.peak ≤ B + E + n ∧
  s.widths d ≤ B + E + n ∧
  ∀ i, i ≠ d → s.widths i ≤ B

theorem maximum_le_of_rows {k : Nat} (w : Widths k) (B : Nat)
    (h : ∀ i, w i ≤ B) : maximum w ≤ B := by
  unfold maximum
  exact Finset.sup_le (fun i _ => h i)

theorem fixed_advance {k : Nat} {d : Fin k} {B E n : Nat}
    {s : State k} {op : Op k}
    (hs : BoundState d B E n s)
    (hop : op = .marker ∨ ∃ src sh, src ≠ d ∧ sh ≤ E ∧ op = .addScaled d src sh) :
    BoundState d B E (n + 1) (advance op s) := by
  rcases hs with ⟨hpeak, hd, hother⟩
  rcases hop with rfl | ⟨src, sh, hsrc, hsh, rfl⟩
  · refine ⟨?_, ?_, ?_⟩
    · have hall : ∀ i, s.widths i ≤ B + E + (n+1) := by
        intro i
        by_cases hi : i = d
        · subst i; omega
        · exact (hother i hi).trans (by omega)
      have hm := maximum_le_of_rows s.widths (B + E + (n+1)) hall
      change max s.peak (maximum s.widths) ≤ B + E + (n+1)
      exact max_le (by omega) hm
    · simpa [advance, step] using (show s.widths d ≤ B + E + (n+1) by omega)
    · simpa [advance, step] using hother
  · have hnewd : (step (.addScaled d src sh) s.widths) d ≤ B + E + (n+1) := by
      simp only [step, Function.update_self]
      have hsrcB := hother src hsrc
      omega
    have hnewother : ∀ i, i ≠ d → (step (.addScaled d src sh) s.widths) i ≤ B := by
      intro i hi
      simpa [step, Function.update_of_ne hi] using hother i hi
    have hnewall : ∀ i, (step (.addScaled d src sh) s.widths) i ≤ B + E + (n+1) := by
      intro i
      by_cases hi : i = d
      · subst i; exact hnewd
      · exact (hnewother i hi).trans (by omega)
    have hmax := maximum_le_of_rows _ _ hnewall
    refine ⟨?_, ?_, ?_⟩
    · simp only [advance]
      exact max_le (by omega) hmax
    · simpa only [advance] using hnewd
    · simpa only [advance] using hnewother

theorem fixed_scan {k : Nat} {d : Fin k} {B E n : Nat}
    (word : List (Op k)) (s : State k)
    (hw : FixedWord d E word) (hs : BoundState d B E n s) :
    BoundState d B E (n + word.length) (scan word s) := by
  induction word generalizing s n with
  | nil => simpa [scan] using hs
  | cons op rest ih =>
    have hop := hw op List.mem_cons_self
    have hrest : FixedWord d E rest := by
      intro op' hop'
      exact hw op' (List.mem_cons_of_mem _ hop')
    have hstep := fixed_advance hs hop
    have hfinal := ih (advance op s) hrest hstep
    simpa [scan, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hfinal

end Paper.F3ChargeCeiling
