import Points.SplitBack

/-!
# Directed Hamiltonian cycle (out-degree ≤ 2) ⟺ the points-as-input table problem

Composition of `dhc_iff_ehc` (split-and-pendant line graph) and `cycle_reduction` (labels translated
so that one edge's label is `0`).
-/

namespace Pts

/-- The table instance of a digraph. -/
def tableOf (D : Dig) : List TableGeneration.Operations.Point := pointsC (HE D)

theorem dhc_iff_table {D : Dig} (hD : D.ok) (ho : D.out2) (hn : 2 ≤ D.n) :
    DHC D ↔ GenTableOpt 2 (tableOf D) (7 * (3 * D.n + D.arcs.length)) := by
  rw [dhc_iff_ehc hD ho hn, ← length_HE, tableOf]
  exact cycle_reduction (HE_nodup D hD) (fun f hf => card_HE D hf)

end Pts
