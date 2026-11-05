import Model.Scanner.ArrayScanner

/-!
# Array scan prefix trajectory

Shows that folding array updates tracks the scanner state. Proves the size and view lemmas `fold_update_size` and `fold_update_view`, the trajectory statement `scan_state_eq_array_trajectory`, and the initial-prefix case `initial_prefix_trajectory`.
-/

namespace Paper.ArrayBridge

open TableGeneration.RecursiveCost

theorem fold_update_size {k : Nat} (a : Array Nat) (ha : a.size = k)
    (ops : TableGeneration.Prog k) :
    (ops.foldl updateBalancedWidths a).size = k := by
  induction ops generalizing a with
  | nil => simpa using ha
  | cons op rest ih =>
      have hs : (updateBalancedWidths a op).size = k := by
        simpa [update_size] using ha
      simpa [List.foldl] using ih (updateBalancedWidths a op) hs

theorem fold_update_view {k : Nat} (a : Array Nat) (ha : a.size = k)
    (peak : Nat) (ops : TableGeneration.Prog k) :
    widthView (ops.foldl updateBalancedWidths a) =
      (Scanner.scan (ops.map toScanner) ⟨widthView a, peak⟩).widths := by
  induction ops generalizing a peak with
  | nil => rfl
  | cons op rest ih =>
      have hs : (updateBalancedWidths a op).size = k := by
        simpa [update_size] using ha
      simpa [List.foldl, Scanner.scan, Scanner.advance, view_update a ha op] using
        ih (updateBalancedWidths a op) hs
          (max peak (Scanner.maximum (Scanner.step (toScanner op) (widthView a))))

theorem scan_state_eq_array_trajectory {k : Nat} (a : Array Nat)
    (ha : a.size = k) (peak : Nat) (ops : TableGeneration.Prog k) :
    Scanner.scan (ops.map toScanner) ⟨widthView a, peak⟩ =
      ⟨widthView (ops.foldl updateBalancedWidths a),
        scanBalancedMaximumAux a peak ops⟩ := by
  cases hscan : Scanner.scan (ops.map toScanner) ⟨widthView a, peak⟩ with
  | mk w p =>
      have hw : w = widthView (ops.foldl updateBalancedWidths a) := by
        simpa [hscan] using (fold_update_view a ha peak ops).symm
      have hp : p = scanBalancedMaximumAux a peak ops := by
        simpa [hscan] using scan_aux_eq a ha peak ops
      cases hw
      cases hp
      rfl

theorem initial_prefix_trajectory (width k : Nat)
    (ops : TableGeneration.Prog k) (n : Nat) :
    Scanner.scan ((ops.take n).map toScanner)
        (Scanner.fresh (literalSourceSplit width k)) =
      ⟨widthView ((ops.take n).foldl updateBalancedWidths
          (initBalancedWidths width k)),
        scanBalancedMaximumAux (initBalancedWidths width k)
          (maximumBalancedWidth (initBalancedWidths width k)) (ops.take n)⟩ := by
  have hs := init_size width k
  simpa [Scanner.fresh, view_init, maximum_eq _ hs] using
    scan_state_eq_array_trajectory (initBalancedWidths width k) hs
      (maximumBalancedWidth (initBalancedWidths width k)) (ops.take n)

end Paper.ArrayBridge
