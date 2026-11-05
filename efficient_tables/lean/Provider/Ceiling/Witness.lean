import Provider.Ceiling.Ceiling
import PhaseProduct.Baseline.BaselineContract

/-! # Literal Baseline Witness
Defines `literalBaseline`, a literal F2 source for arity `k` at least two within the cap `K`. Proves `f2Points_ofFn` about its point list and `literalBaseline_exists`.
-/

namespace Paper.F3ChargeCeiling

open Paper.F2CatalogTransfer TableGeneration

theorem f2Points_ofFn (k : Nat) (hk : 2 ≤ k) :
    (List.ofFn (fun i : Fin (2 * (k - 1) + 1) => f2Point i.val)) = f2Points k := by
  have hcount : 2 * (k - 1) + 1 = 2 * k - 1 := by omega
  simp only [List.ofFn_eq_map, f2Points]
  rw [hcount]
  calc
    List.map (fun i => f2Point i.val) (List.finRange (2 * k - 1))
      = List.map f2Point (List.map Fin.val (List.finRange (2 * k - 1))) := by
        simp only [List.map_map, Function.comp_def]
    _ = List.map f2Point (List.range (2 * k - 1)) := by
      rw [List.map_coe_finRange_eq_range]

def literalBaseline {K : Nat} (k : Nat) (hk : 2 ≤ k) (hK : k ≤ K) : F2Source K :=
  {
    source := {
      policyId := "literal F2 source baseline"
      k := k
      hk := hk
      program := genOpsWithProduct (positive_of_ge_two hk) (f2Points k)
    }
    cap := hK
    points := fun i => f2Point i.val
    safe := by
      simpa only [f2Points_ofFn k hk] using
        Paper.BaselineContract.genOpsWithProduct_contract
          (positive_of_ge_two hk) (f2Points k)
    literalF2 := by
      rw [f2Points_ofFn k hk]
  }

theorem literalBaseline_exists {K : Nat} {k : Nat} (hk : 2 ≤ k) (hK : k ≤ K) :
    ∃ t : F2Source K, t.arity = k := by
  exact ⟨literalBaseline k hk hK, rfl⟩

end Paper.F3ChargeCeiling
