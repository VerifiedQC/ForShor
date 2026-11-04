import Model.Scanner.Scanner
import Mathlib.Algebra.Order.Group.Finset

/-!
# Profile algebra of the scanner

Algebra of clipped joins and translations of width vectors. Proves how the maximum and scan commute with `combineWidths` and `combineState` (`maximum_combineWidths`, `scan_combineState`), the balanced clipping identities, and translation behaviour (`maximum_translate`, `advance_translateState`).
-/

namespace Paper.Profile

open Paper.Scanner

theorem finset_sup_sub {ι : Type} [DecidableEq ι] (s : Finset ι)
    (v : ι → Nat) (c : Nat) :
    s.sup (fun i => v i - c) = s.sup v - c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sup_insert] at *
      omega

theorem maximum_sub {k : Nat} (v : Widths k) (c : Nat) :
    maximum (fun i => v i - c) = maximum v - c := by
  classical
  unfold maximum
  exact finset_sup_sub Finset.univ v c

theorem maximum_combineWidths {k : Nat} (c : Nat) (u v : Widths k) :
    maximum (combineWidths c u v) = max (maximum u) (maximum v - c) := by
  classical
  unfold maximum combineWidths
  change Finset.univ.sup (u ⊔ fun i => v i - c) = _
  rw [Finset.sup_sup, finset_sup_sub]

theorem step_combineWidths {k : Nat} (c : Nat) (op : Op k)
    (u v : Widths k) :
    step op (combineWidths c u v) =
      combineWidths c (step op u) (step op v) := by
  funext i
  cases op with
  | shiftL row n =>
      by_cases hi : i = row
      · subst i
        simp [step, combineWidths, max_def] <;> split_ifs <;> omega
      · simp [step, combineWidths, hi, max_def] <;> split_ifs <;> omega
  | shiftR row n =>
      by_cases hi : i = row
      · subst i
        simp [step, combineWidths, max_def] <;> split_ifs <;> omega
      · simp [step, combineWidths, hi, max_def] <;> split_ifs <;> omega
  | negate row =>
      by_cases hi : i = row
      · subst i
        simp [step, combineWidths, max_def] <;> split_ifs <;> omega
      · simp [step, combineWidths, hi, max_def] <;> split_ifs <;> omega
  | addScaled d s n =>
      by_cases hi : i = d
      · subst i
        simp [step, combineWidths, max_def] <;> split_ifs <;> omega
      · simp [step, combineWidths, hi, max_def] <;> split_ifs <;> omega
  | marker => rfl

theorem advance_combineState {k : Nat} (c : Nat) (op : Op k)
    (s t : State k) :
    advance op (combineState c s t) =
      combineState c (advance op s) (advance op t) := by
  cases s with
  | mk sw sp =>
    cases t with
    | mk tw tp =>
      simp [advance, combineState, step_combineWidths,
        maximum_combineWidths, max_assoc, max_left_comm, max_comm]
      omega

theorem scan_combineState {k : Nat} (c : Nat) (word : List (Op k))
    (s t : State k) :
    scan word (combineState c s t) =
      combineState c (scan word s) (scan word t) := by
  induction word generalizing s t with
  | nil => rfl
  | cons op rest ih =>
      simp [scan, advance_combineState, ih]

theorem balanced_clipped {k : Nat} (top : Fin k) (R r : Nat) (hr : r ≤ R) :
    combineWidths (R - r) (balanced top 0 0) (balanced top 0 R) =
      balanced top 0 r := by
  funext i
  by_cases hi : i = top <;> simp [combineWidths, balanced, hi] <;> omega

theorem maximum_balanced {k : Nat} (top : Fin k) (L r : Nat) :
    maximum (balanced top L r) = L + r := by
  classical
  unfold maximum
  apply le_antisymm
  · apply Finset.sup_le
    intro i hi
    by_cases hitop : i = top
    · subst i
      simp [balanced]
    · simp [balanced, hitop]
  · have hmem : top ∈ (Finset.univ : Finset (Fin k)) := Finset.mem_univ _
    simpa [balanced] using (Finset.le_sup hmem : balanced top L r top ≤ Finset.univ.sup (balanced top L r))

/-- A common translation raises the finite maximum by exactly its offset. -/
theorem finset_sup_add {ι : Type} [DecidableEq ι] (s : Finset ι)
    (v : ι → Nat) (L : Nat) (hne : s.Nonempty) :
    s.sup (fun i => v i + L) = s.sup v + L := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hne
  | @insert a s ha ih =>
      simp only [Finset.sup_insert]
      by_cases hs : s.Nonempty
      · rw [ih hs]
        omega
      · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
        simp [hs0]

theorem maximum_translate {k : Nat} (top : Fin k) (w : Widths k) (L : Nat) :
    maximum (translate w L) = maximum w + L := by
  classical
  unfold maximum translate
  exact finset_sup_add Finset.univ w L ⟨top, Finset.mem_univ _⟩

theorem advance_translateState {k : Nat} (top : Fin k) (op : Op k) (s : State k)
    (L : Nat) (h : stepNoUnderflow op s.widths) :
    advance op (translateState s L) = translateState (advance op s) L := by
  apply congrArg₂ (fun w p => (⟨w, p⟩ : State k))
    (step_translate op s.widths L h)
  simp only [advance, translateState]
  rw [step_translate op s.widths L h, maximum_translate top]
  simp [max_add_add_right]

theorem scan_translateState {k : Nat} (top : Fin k) (word : List (Op k)) (s : State k)
    (L : Nat) (h : noUnderflow word s.widths) :
    scan word (translateState s L) = translateState (scan word s) L := by
  induction word generalizing s with
  | nil => rfl
  | cons op rest ih =>
      obtain ⟨hop, hrest⟩ := h
      rw [scan, scan, advance_translateState top op s L hop]
      exact ih (advance op s) hrest

theorem fresh_translateState {k : Nat} (top : Fin k) (L r : Nat) :
    fresh (balanced top L r) = translateState (fresh (balanced top 0 r)) L := by
  apply congrArg₂ (fun w p => (⟨w, p⟩ : State k))
  · change balanced top L r = translate (balanced top 0 r) L
    funext i
    by_cases hi : i = top <;> simp [translate, balanced, hi] <;> omega
  · simp [fresh, translateState, maximum_balanced]
    omega

/-- Exact translation law for the complete fresh peak, with the full saved
history translated alongside the current row widths. -/
theorem fresh_peak_translate {k : Nat} (top : Fin k) (word : List (Op k))
    (L r : Nat) (h : noUnderflow word (balanced top 0 r)) :
    (scan word (fresh (balanced top L r))).peak =
      L + (scan word (fresh (balanced top 0 r))).peak := by
  rw [fresh_translateState, scan_translateState top word _ L h]
  simp [translateState]
  omega

/-- Whole-word endpoint/profile law for fresh scans. -/
theorem fresh_peak_profile {k : Nat} (top : Fin k) (word : List (Op k))
    (R r : Nat) (hr : r ≤ R) :
    (scan word (fresh (balanced top 0 r))).peak =
      max ((scan word (fresh (balanced top 0 0))).peak)
        ((scan word (fresh (balanced top 0 R))).peak - (R - r)) := by
  have hwidth := balanced_clipped top R r hr
  have hstate : fresh (balanced top 0 r) =
      combineState (R-r) (fresh (balanced top 0 0))
        (fresh (balanced top 0 R)) := by
    apply congrArg₂ (fun w p => (⟨w, p⟩ : State k)) (Eq.symm hwidth)
    simp [fresh, combineState, maximum_balanced]
    omega
  rw [hstate, scan_combineState]
  rfl

/-- Affine-in-remainder endpoint form, with its intercept made explicit. -/
theorem fresh_peak_profile_affine {k : Nat} (top : Fin k)
    (word : List (Op k)) (R r : Nat) (hr : r ≤ R) :
    (scan word (fresh (balanced top 0 r))).peak =
      max ((scan word (fresh (balanced top 0 0))).peak)
        (((scan word (fresh (balanced top 0 R))).peak - R) + r) := by
  have hR : R ≤ (scan word (fresh (balanced top 0 R))).peak := by
    have h := incoming_peak_le_scan word (fresh (balanced top 0 R))
    simpa [fresh, maximum_balanced] using h
  rw [fresh_peak_profile top word R r hr]
  congr 1
  omega

/-- A remainder cap holds exactly when both endpoint scans satisfy their
corresponding caps. -/
theorem fresh_peak_profile_cap_iff {k : Nat} (top : Fin k)
    (word : List (Op k)) (R r C : Nat) (hr : r ≤ R) :
    (scan word (fresh (balanced top 0 r))).peak ≤ C ↔
      (scan word (fresh (balanced top 0 0))).peak ≤ C ∧
        (scan word (fresh (balanced top 0 R))).peak ≤ C + (R-r) := by
  rw [fresh_peak_profile top word R r hr]
  constructor
  · intro h
    constructor
    · exact le_trans (le_max_left _ _) h
    · have hsub := le_trans (le_max_right _ _) h
      omega
  · rintro ⟨h0, hR⟩
    apply max_le h0
    omega

/-- The canonical affine intercept lies between `max (0, a-R)` and `a`. -/
theorem fresh_peak_profile_intercept_bounds {k : Nat} (top : Fin k)
    (word : List (Op k)) (R : Nat) :
    max 0 ((scan word (fresh (balanced top 0 0))).peak - R) ≤
      (scan word (fresh (balanced top 0 R))).peak - R ∧
    (scan word (fresh (balanced top 0 R))).peak - R ≤
      (scan word (fresh (balanced top 0 0))).peak := by
  have hR : R ≤ (scan word (fresh (balanced top 0 R))).peak := by
    have h := incoming_peak_le_scan word (fresh (balanced top 0 R))
    simpa [fresh, maximum_balanced] using h
  have h0 := fresh_peak_profile top word R 0 (Nat.zero_le R)
  have hmono :
      (scan word (fresh (balanced top 0 0))).peak ≤
        (scan word (fresh (balanced top 0 R))).peak := by
    have hle : LE (fresh (balanced top 0 0)) (fresh (balanced top 0 R)) := by
      constructor
      · simp [fresh, maximum_balanced]
      · intro i
        change balanced top 0 0 i ≤ balanced top 0 R i
        by_cases hi : i = top <;> simp [balanced, hi]
    exact (scan_mono word hle).1
  constructor <;> omega

/-- Combining two signed child width caps factors out their common quotient
and the signed-child unit overhead. -/
theorem signed_child_two_caps (q a b : Nat) :
    max (q + 1 + a) (q + 1 + b) = q + 1 + max a b := by
  omega

end Paper.Profile
