import Model.Defs

/-!
# Array-based width scanner bridge

Relates the array-based width scanner to the model scanner. Proves size and view lemmas for array initialization and update (`init_size`, `view_set`, `view_update`), `toScanner_eq_widthOp_toFull`, and maximum-fold facts such as `foldl_max_le`.
-/

namespace Paper.ArrayBridge

open TableGeneration.RecursiveCost

theorem literalSourceSplit_eq_explicit (width k : Nat) :
    literalSourceSplit width k =
      (fun i => phaseSplitLogicalWidth width (width / k) k i) := by
  funext i
  simp [literalSourceSplit, phaseLimbWidth, phaseLimbWidthOfWidth]

theorem toScanner_eq_widthOp_toFull {k : Nat}
    (op : TableGeneration.Operations.valid_ops k) :
    toScanner op = FullDSL.widthOp (SourceBridge.toFull op) := by
  cases op <;> rfl

theorem mappedWord_eq_widthWord {k : Nat} (ops : TableGeneration.Prog k) :
    ops.map toScanner = FullDSL.widthWord (SourceBridge.mapToFull ops) := by
  induction ops with
  | nil => rfl
  | cons op rest ih =>
      simp [SourceBridge.mapToFull, FullDSL.widthWord,
        toScanner_eq_widthOp_toFull, ih]

theorem init_size (width k : Nat) :
    (TableGeneration.RecursiveCost.initBalancedWidths width k).size = k := by
  simp [TableGeneration.RecursiveCost.initBalancedWidths]

theorem update_size {k : Nat} (a : Array Nat)
    (op : TableGeneration.Operations.valid_ops k) :
    (TableGeneration.RecursiveCost.updateBalancedWidths a op).size = a.size := by
  cases op <;> simp [TableGeneration.RecursiveCost.updateBalancedWidths]

theorem view_set {k : Nat} (a : Array Nat) (ha : a.size = k)
    (d : Fin k) (v : Nat) :
    widthView (a.setIfInBounds d.val v) =
      Function.update (widthView a) d v := by
  funext i
  by_cases h : i = d
  · subst i
    simp [widthView, TableGeneration.RecursiveCost.balancedWidthAt, ha]
  · have hv : d.val ≠ i.val := by
      intro heq
      exact h (Fin.ext heq.symm)
    simp [widthView, TableGeneration.RecursiveCost.balancedWidthAt, Function.update, h, hv]

theorem view_init (width k : Nat) :
    widthView (TableGeneration.RecursiveCost.initBalancedWidths width k) =
      literalSourceSplit width k := by
  funext i
  simp [widthView, TableGeneration.RecursiveCost.balancedWidthAt, TableGeneration.RecursiveCost.initBalancedWidths,
    literalSourceSplit]

theorem view_update {k : Nat} (a : Array Nat) (ha : a.size = k)
    (op : TableGeneration.Operations.valid_ops k) :
    widthView (TableGeneration.RecursiveCost.updateBalancedWidths a op) =
      Scanner.step (toScanner op) (widthView a) := by
  cases op with
  | shiftL i n =>
      simpa [TableGeneration.RecursiveCost.updateBalancedWidths, Scanner.step, toScanner] using
        view_set a ha i (TableGeneration.RecursiveCost.balancedWidthAt a i + n)
  | shiftR i n =>
      simpa [TableGeneration.RecursiveCost.updateBalancedWidths, Scanner.step, toScanner] using
        view_set a ha i (TableGeneration.RecursiveCost.balancedWidthAt a i - n)
  | negate i =>
      simpa [TableGeneration.RecursiveCost.updateBalancedWidths, Scanner.step, toScanner] using
        view_set a ha i (TableGeneration.RecursiveCost.balancedWidthAt a i + 1)
  | addScaled d s negative shift =>
      simpa [TableGeneration.RecursiveCost.updateBalancedWidths, Scanner.step, toScanner] using
        view_set a ha d (1 + max (TableGeneration.RecursiveCost.balancedWidthAt a d)
          (TableGeneration.RecursiveCost.balancedWidthAt a s + shift))
  | phaseProduct i => rfl

theorem foldl_max_le_aux : ∀ (l : List Nat) (b acc : Nat),
    (∀ x ∈ l, x ≤ b) → acc ≤ b → l.foldl max acc ≤ b := by
  intro l
  induction l with
  | nil => intro b acc _ hacc; exact hacc
  | cons x xs ih =>
      intro b acc h hacc
      apply ih b (max acc x)
      · intro y hy
        exact h y (List.mem_cons_of_mem _ hy)
      · exact max_le hacc (h x (by simp))

theorem foldl_max_le (l : List Nat) (b : Nat)
    (h : ∀ x ∈ l, x ≤ b) : l.foldl max 0 ≤ b :=
  foldl_max_le_aux l b 0 h (Nat.zero_le b)

theorem acc_le_foldl_max : ∀ (l : List Nat) (acc : Nat),
    acc ≤ l.foldl max acc := by
  intro l
  induction l with
  | nil => intro acc; exact le_refl _
  | cons x xs ih =>
      intro acc
      exact le_trans (le_max_left acc x) (ih (max acc x))

theorem le_foldl_max_of_mem_aux : ∀ (l : List Nat) (x acc : Nat),
    x ∈ l → x ≤ l.foldl max acc := by
  intro l
  induction l with
  | nil => intro x acc h; simp at h
  | cons y ys ih =>
      intro x acc h
      rcases List.mem_cons.mp h with hxy | hrest
      · subst x
        exact le_trans (le_max_right acc y) (acc_le_foldl_max ys (max acc y))
      · exact ih x (max acc y) hrest

theorem le_foldl_max_of_mem (l : List Nat) (x : Nat)
    (h : x ∈ l) : x ≤ l.foldl max 0 :=
  le_foldl_max_of_mem_aux l x 0 h

theorem maximum_eq {k : Nat} (a : Array Nat) (ha : a.size = k) :
    TableGeneration.RecursiveCost.maximumBalancedWidth a =
      Scanner.maximum (widthView (k := k) a) := by
  apply le_antisymm
  · unfold TableGeneration.RecursiveCost.maximumBalancedWidth
    rw [← Array.foldl_toList]
    apply foldl_max_le
    intro x hx
    obtain ⟨i, hi, heq⟩ := Array.mem_iff_getElem.mp
      (Array.mem_toList_iff.mp hx)
    let j : Fin k := ⟨i, by simpa [ha] using hi⟩
    have hxj : widthView a j = x := by
      simp [widthView, TableGeneration.RecursiveCost.balancedWidthAt, j, hi, heq]
    rw [← hxj]
    exact Finset.le_sup (Finset.mem_univ j)
  · unfold Scanner.maximum
    apply Finset.sup_le
    intro i _
    have hi : i.val < a.size := by simpa [ha] using i.isLt
    have hmem : a[i.val] ∈ a.toList := Array.getElem_mem_toList hi
    have hle := le_foldl_max_of_mem a.toList (a[i.val]) hmem
    simpa [TableGeneration.RecursiveCost.maximumBalancedWidth, widthView, TableGeneration.RecursiveCost.balancedWidthAt, hi,
      ← Array.foldl_toList] using hle

theorem scan_aux_eq {k : Nat} (a : Array Nat) (ha : a.size = k)
    (peak : Nat) (ops : TableGeneration.Prog k) :
    (Scanner.scan (ops.map toScanner) ⟨widthView a, peak⟩).peak =
      TableGeneration.RecursiveCost.scanBalancedMaximumAux a peak ops := by
  induction ops generalizing a peak with
  | nil => rfl
  | cons op rest ih =>
      have hs : (TableGeneration.RecursiveCost.updateBalancedWidths a op).size = k := by
        rw [update_size, ha]
      simpa [Scanner.scan, Scanner.advance, TableGeneration.RecursiveCost.scanBalancedMaximumAux,
        view_update a ha op, maximum_eq _ hs] using
        ih (TableGeneration.RecursiveCost.updateBalancedWidths a op) hs
          (max peak (TableGeneration.RecursiveCost.maximumBalancedWidth (TableGeneration.RecursiveCost.updateBalancedWidths a op)))

theorem nextBalancedSignedWidth_eq_scanner {k : Nat}
    (width : Nat) (ops : TableGeneration.Prog k) :
    TableGeneration.RecursiveCost.nextBalancedSignedWidth width ops =
      1 + (Scanner.scan (ops.map toScanner)
        (Scanner.fresh (literalSourceSplit width k))).peak := by
  have hs := init_size width k
  have hscan := scan_aux_eq (TableGeneration.RecursiveCost.initBalancedWidths width k) hs
    (TableGeneration.RecursiveCost.maximumBalancedWidth (TableGeneration.RecursiveCost.initBalancedWidths width k)) ops
  simpa [TableGeneration.RecursiveCost.nextBalancedSignedWidth, Scanner.fresh, view_init,
    maximum_eq _ hs] using congrArg (Nat.add 1) hscan.symm

theorem nextBalancedSignedWidth_eq_full_widthWord {k : Nat}
    (width : Nat) (ops : TableGeneration.Prog k) :
    nextBalancedSignedWidth width ops =
      1 + (Scanner.scan (FullDSL.widthWord (SourceBridge.mapToFull ops))
        (Scanner.fresh (literalSourceSplit width k))).peak := by
  rw [nextBalancedSignedWidth_eq_scanner, mappedWord_eq_widthWord]

end Paper.ArrayBridge
