import ILPEncoding.Bounds.Matrix
import Mathlib.Data.List.Dedup

/-! # Computable System Rows
Defines `usedKeys`, a deduplicated list of the variables used by a label list, and `systemRowsC`, a computable list of system rows. Proves `usedKeys_length`, `usedKeys_card` and `systemRowsC_length`.
-/

namespace Paper.F7Computable

open Paper.F6ILP Paper.F6ILPRows Paper.F6ILPCost Paper.F6ILPSystem
open Paper.F7Encoding Paper.AffineNat

def usedKeys (labels : List Label) : List (Variable labels) :=
  ((labels.map Label.k).dedup).attach.map fun key =>
    ⟨key.val, by
      have h : key.val ∈ labels.map Label.k := by
        simpa only [List.mem_dedup] using key.property
      simpa only [usedArities, List.mem_toFinset] using h⟩

theorem usedKeys_length (labels : List Label) :
    (usedKeys labels).length = (labels.map Label.k).dedup.length := by
  simp only [usedKeys, List.length_map, List.length_attach]

theorem usedKeys_card (labels : List Label) :
    (usedKeys labels).length = Fintype.card (Variable labels) := by
  rw [usedKeys_length, variable_count]
  have hset : ((labels.map Label.k).dedup).toFinset =
      (labels.map Label.k).toFinset := by
    ext k
    simp only [List.mem_toFinset, List.mem_dedup]
  have hcard := List.toFinset_card_of_nodup
    (List.nodup_dedup (labels.map Label.k))
  rw [hset] at hcard
  simpa only [usedArities] using hcard.symm

def systemRowsC (labels : List Label) (x z : ℤ)
    (c lo hi : Nat → Nat) (price : Nat → Nat) (N T : Nat) :
    List (AffineExpr (usedArities labels)) :=
  let terminal := terminalRow labels x z
  [terminal, scaleExpr (-1) terminal] ++
    contractionRoot labels x ++
    [budgetRow labels x z c price N T] ++
    boundRows lo hi (usedKeys labels)

theorem systemRowsC_length (labels : List Label) (x z : ℤ)
    (c lo hi : Nat → Nat) (price : Nat → Nat) (N T : Nat) :
    (systemRowsC labels x z c lo hi price N T).length =
      2 * (usedKeys labels).length + labels.length + 3 := by
  have hcon := Paper.F7Size.contractionRoot_length labels x
  simp only [systemRowsC, List.length_append, List.length_cons,
    List.length_nil, hcon, boundRows_length]
  omega

end Paper.F7Computable

