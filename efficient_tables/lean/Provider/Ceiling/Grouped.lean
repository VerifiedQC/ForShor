import Provider.Ceiling.Witness

/-! # Grouped Literal Baseline
Defines `groupedF2Points`, a list of grouped points of arity `k`, and `groupedLiteralBaseline`, a literal F2 source built from it. Proves `groupedF2Points_perm` and `groupedF2Points_length` for the point list and `groupedLiteralBaseline_exists` for the source.
-/

namespace Paper.F3ChargeCeiling

open Paper.F2CatalogTransfer TableGeneration

def isIntegerPoint : TableGeneration.Operations.Point → Bool
  | .int _ => true
  | .frac _ => false

def groupedF2Points (k : Nat) : List TableGeneration.Operations.Point :=
  (f2Points k).filter isIntegerPoint ++
    (f2Points k).filter (fun p => !isIntegerPoint p)

theorem groupedF2Points_perm (k : Nat) :
    (groupedF2Points k).Perm (f2Points k) := by
  exact List.filter_append_perm isIntegerPoint (f2Points k)

theorem groupedF2Points_length (k : Nat) (hk : 2 ≤ k) :
    (groupedF2Points k).length = 2 * (k - 1) + 1 := by
  have hp := (groupedF2Points_perm k).length_eq
  simp only [f2Points, List.length_map, List.length_range] at hp
  omega

theorem ofFn_get_cast {α : Type*} (l : List α) {n : Nat}
    (h : l.length = n) :
    List.ofFn (fun i : Fin n => l.get (Fin.cast h.symm i)) = l := by
  subst n
  exact List.ofFn_get l

def groupedLiteralBaseline {K : Nat} (k : Nat) (hk : 2 ≤ k) (hK : k ≤ K) :
    F2Source K :=
  {
    source := {
      policyId := "grouped literal F2 source baseline"
      k := k
      hk := hk
      program := genOpsWithProduct (positive_of_ge_two hk) (groupedF2Points k)
    }
    cap := hK
    points := fun i => (groupedF2Points k).get
      (Fin.cast (groupedF2Points_length k hk).symm i)
    safe := by
      simpa only [ofFn_get_cast (groupedF2Points k) (groupedF2Points_length k hk)] using
        Paper.BaselineContract.genOpsWithProduct_contract
          (positive_of_ge_two hk) (groupedF2Points k)
    literalF2 := by
      simpa only [ofFn_get_cast (groupedF2Points k) (groupedF2Points_length k hk)] using
        groupedF2Points_perm k
  }

theorem groupedLiteralBaseline_exists {K : Nat} {k : Nat}
    (hk : 2 ≤ k) (hK : k ≤ K) :
    ∃ t : F2Source K, t.arity = k := by
  exact ⟨groupedLiteralBaseline k hk hK, rfl⟩

end Paper.F3ChargeCeiling
