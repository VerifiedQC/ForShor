import Model.Defs

/-!
# Width scanner monotonicity and joins

Order-theoretic facts about the width scanner. Proves monotonicity of a step and a scan (`step_mono`, `scan_mono`), compatibility with joins (`step_join`, `scan_join`), concatenation (`scan_append`), and that an incoming peak is never forgotten (`incoming_peak_le_scan`).
-/

namespace Paper.Scanner

theorem step_mono {k : Nat} (op : Op k) {u v : Widths k}
    (h : ∀ i, u i ≤ v i) : ∀ i, step op u i ≤ step op v i := by
  cases op with
  | shiftL row n =>
      intro i
      by_cases hi : i = row
      · subst i; simp [step, h row]
      · simp [step, hi, h i]
  | shiftR row n =>
      intro i
      by_cases hi : i = row
      · subst i; simp [step, Nat.sub_le_sub_right (h row) n]
      · simp [step, hi, h i]
  | negate row =>
      intro i
      by_cases hi : i = row
      · subst i; simp [step, h row]
      · simp [step, hi, h i]
  | addScaled d s n =>
      intro i
      by_cases hi : i = d
      · subst i
        have hd := h d
        have hs := h s
        simp [step]
        omega
      · simp [step, hi, h i]
  | marker => exact h

theorem maximum_mono {k : Nat} {u v : Widths k}
    (h : ∀ i, u i ≤ v i) : maximum u ≤ maximum v := by
  unfold maximum
  exact Finset.sup_mono_fun (fun i _ => h i)

theorem advance_mono {k : Nat} (op : Op k) {s t : State k}
    (h : LE s t) : LE (advance op s) (advance op t) := by
  constructor
  · exact max_le_max h.1 (maximum_mono (step_mono op h.2))
  · exact step_mono op h.2

theorem scan_mono {k : Nat} (word : List (Op k)) {s t : State k}
    (h : LE s t) : LE (scan word s) (scan word t) := by
  induction word generalizing s t with
  | nil => exact h
  | cons op rest ih => exact ih (advance_mono op h)

/-- An upper bound on both the current widths and prior peak propagates to
any common continuation. -/
theorem continuation_upper_bound {k : Nat} (word : List (Op k))
    {s t : State k} (hpeak : s.peak ≤ t.peak)
    (hwidth : ∀ i, s.widths i ≤ t.widths i) :
    (scan word s).peak ≤ (scan word t).peak :=
  (scan_mono word ⟨hpeak, hwidth⟩).1

theorem step_join {k : Nat} (op : Op k) (u v : Widths k) :
    step op (joinWidths u v) = joinWidths (step op u) (step op v) := by
  funext i
  cases op with
  | shiftL row n =>
      by_cases hi : i = row
      · subst i; simp [step, joinWidths]
      · simp [step, joinWidths, hi]
  | shiftR row n =>
      by_cases hi : i = row
      · subst i; simp [step, joinWidths]; omega
      · simp [step, joinWidths, hi]
  | negate row =>
      by_cases hi : i = row
      · subst i; simp [step, joinWidths]
      · simp [step, joinWidths, hi]
  | addScaled d s n =>
      by_cases hi : i = d
      · subst i; simp [step, joinWidths]; omega
      · simp [step, joinWidths, hi]
  | marker => rfl

theorem maximum_join {k : Nat} (u v : Widths k) :
    maximum (joinWidths u v) = max (maximum u) (maximum v) := by
  change Finset.univ.sup (u ⊔ v) = Finset.univ.sup u ⊔ Finset.univ.sup v
  exact Finset.sup_sup

theorem advance_join {k : Nat} (op : Op k) (s t : State k) :
    advance op (joinState s t) = joinState (advance op s) (advance op t) := by
  cases s with
  | mk sw sp =>
    cases t with
    | mk tw tp =>
      simp [advance, joinState, step_join, maximum_join,
        max_assoc, max_left_comm]

theorem scan_join {k : Nat} (word : List (Op k)) (s t : State k) :
    scan word (joinState s t) = joinState (scan word s) (scan word t) := by
  induction word generalizing s t with
  | nil => rfl
  | cons op rest ih =>
      simp [scan, advance_join, ih]

theorem scan_append {k : Nat} (first second : List (Op k)) (s : State k) :
    scan (first ++ second) s = scan second (scan first s) := by
  induction first generalizing s with
  | nil => rfl
  | cons op rest ih => simpa [scan] using ih (advance op s)

/-- The peak supplied by an incoming history is never forgotten. -/
theorem incoming_peak_le_scan {k : Nat} (word : List (Op k)) (s : State k) :
    s.peak ≤ (scan word s).peak := by
  induction word generalizing s with
  | nil => exact le_rfl
  | cons op rest ih =>
      exact le_trans (le_max_left s.peak (maximum (step op s.widths)))
        (ih (advance op s))

theorem scan_widths_eq_runWidths {k : Nat} (word : List (Op k)) (s : State k) :
    (scan word s).widths = runWidths word s.widths := by
  induction word generalizing s with
  | nil => rfl
  | cons op rest ih => exact ih (advance op s)

theorem step_translate {k : Nat} (op : Op k) (w : Widths k) (L : Nat)
    (h : stepNoUnderflow op w) :
    step op (translate w L) = translate (step op w) L := by
  funext i
  cases op with
  | shiftL row n =>
      by_cases hi : i = row
      · subst i; simp [step, translate]; omega
      · simp [step, translate, hi]
  | shiftR row n =>
      by_cases hi : i = row
      · subst i; simp [stepNoUnderflow] at h; simp [step, translate] at *; omega
      · simp [step, translate, hi]
  | negate row =>
      by_cases hi : i = row
      · subst i; simp [step, translate]; omega
      · simp [step, translate, hi]
  | addScaled d s n =>
      by_cases hi : i = d
      · subst i; simp [step, translate]; omega
      · simp [step, translate, hi]
  | marker => rfl

/-- Common translation is valid for whole-word *current widths* when the
baseline run never truncates a right shift. This does not assert a translated
historical peak (which also needs a nonempty row set). -/
theorem runWidths_translate {k : Nat} (word : List (Op k))
    (w : Widths k) (L : Nat) (h : noUnderflow word w) :
    runWidths word (translate w L) = translate (runWidths word w) L := by
  induction word generalizing w with
  | nil => rfl
  | cons op rest ih =>
      obtain ⟨hop, hrest⟩ := h
      simpa [runWidths, step_translate op w L hop] using ih (step op w) hrest

end Paper.Scanner
