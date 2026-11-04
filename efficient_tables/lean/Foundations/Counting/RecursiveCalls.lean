import Foundations.Counting.TypedWords

/-!
# Recursive call counts of the word generator

Defines `recursiveCalls`, `positiveNodes` and `zeroLeaves` for a generic alphabet with branch counts `q`. Proves that the call count splits as nodes plus zero leaves (`recursiveCalls_eq_nodes_add_zeroLeaves`) and bounds it by an enumerated-size bound (`recursiveCalls_le_enumeratedSize_bound`).
-/

namespace Paper.CountStage.TypedWordRuntime

open Paper.CountStage.TypedDecorationWords

def recursiveCalls {α : Type} (A : List α) (q : α → Nat)
    (hq : ∀ a, 3 ≤ q a) : Nat → Nat
  | 0 => 1
  | U + 1 => 1 + (A.map fun a => recursiveCalls A q hq ((U + 1) / q a)).sum
termination_by U => U
decreasing_by
  simp_wf
  exact Nat.div_lt_self (by omega) (by have := hq a; omega)

def positiveNodes {α : Type} (A : List α) (q : α → Nat)
    (hq : ∀ a, 3 ≤ q a) : Nat → Nat
  | 0 => 0
  | U + 1 => 1 + (A.map fun a => positiveNodes A q hq ((U + 1) / q a)).sum
termination_by U => U
decreasing_by
  simp_wf
  exact Nat.div_lt_self (by omega) (by have := hq a; omega)

def zeroLeaves {α : Type} (A : List α) (q : α → Nat)
    (hq : ∀ a, 3 ≤ q a) : Nat → Nat
  | 0 => 1
  | U + 1 => (A.map fun a => zeroLeaves A q hq ((U + 1) / q a)).sum
termination_by U => U
decreasing_by
  simp_wf
  exact Nat.div_lt_self (by omega) (by have := hq a; omega)

private theorem sum_map_add {α : Type} (A : List α) (f g : α → Nat) :
    (A.map fun a => f a + g a).sum = (A.map f).sum + (A.map g).sum := by
  induction A with
  | nil => simp
  | cons a A ih => simp [ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem sum_map_mul_left {α : Type} (A : List α) (c : Nat) (f : α → Nat) :
    (A.map fun a => c * f a).sum = c * (A.map f).sum := by
  induction A with
  | nil => simp
  | cons a A ih => simp [ih, Nat.mul_add]

private theorem sum_map_const {α : Type} (A : List α) (c : Nat) :
    (A.map fun _ : α => c).sum = A.length * c := by
  induction A with
  | nil => simp
  | cons a A ih => simp [ih]; ring

theorem positiveNodes_eq_outputLength {α : Type} (A : List α) (q : α → Nat)
    (hq : ∀ a, 3 ≤ q a) : ∀ U,
    positiveNodes A q hq U = (typedBudgetWords A q hq U).length := by
  intro U
  induction U using Nat.strong_induction_on with
  | h U ih =>
      cases U with
      | zero => simp [positiveNodes, typedBudgetWords]
      | succ U =>
          have hbranch : ∀ a ∈ A,
              positiveNodes A q hq ((U + 1) / q a) =
                (typedBudgetWords A q hq ((U + 1) / q a)).length := by
            intro a ha
            apply ih
            exact Nat.div_lt_self (by omega) (by have := hq a; omega)
          simp only [positiveNodes, typedBudgetWords, List.length_append,
            List.length_singleton, List.length_flatMap, List.length_map]
          congr 1
          apply congrArg List.sum
          apply List.map_congr_left
          intro a ha
          exact hbranch a ha

theorem recursiveCalls_eq_nodes_add_zeroLeaves {α : Type} (A : List α)
    (q : α → Nat) (hq : ∀ a, 3 ≤ q a) : ∀ U,
    recursiveCalls A q hq U = positiveNodes A q hq U + zeroLeaves A q hq U := by
  intro U
  induction U using Nat.strong_induction_on with
  | h U ih =>
      cases U with
      | zero => simp [recursiveCalls, positiveNodes, zeroLeaves]
      | succ U =>
          have hbranch : ∀ a ∈ A,
              recursiveCalls A q hq ((U + 1) / q a) =
                positiveNodes A q hq ((U + 1) / q a) +
                  zeroLeaves A q hq ((U + 1) / q a) := by
            intro a ha
            apply ih
            exact Nat.div_lt_self (by omega) (by have := hq a; omega)
          simp only [recursiveCalls, positiveNodes, zeroLeaves]
          have hm : A.map (fun a => recursiveCalls A q hq ((U + 1) / q a)) =
              A.map (fun a => positiveNodes A q hq ((U + 1) / q a) +
                zeroLeaves A q hq ((U + 1) / q a)) := by
            apply List.map_congr_left
            intro a ha
            exact hbranch a ha
          rw [hm, sum_map_add]
          omega

theorem zeroLeaves_le_size_mul_nodes_add_one {α : Type} (A : List α)
    (q : α → Nat) (hq : ∀ a, 3 ≤ q a) : ∀ U,
    zeroLeaves A q hq U ≤ A.length * positiveNodes A q hq U + 1 := by
  intro U
  induction U using Nat.strong_induction_on with
  | h U ih =>
      cases U with
      | zero => simp [zeroLeaves, positiveNodes]
      | succ U =>
          have hbranch : ∀ a ∈ A,
              zeroLeaves A q hq ((U + 1) / q a) ≤
                A.length * positiveNodes A q hq ((U + 1) / q a) + 1 := by
            intro a ha
            apply ih
            exact Nat.div_lt_self (by omega) (by have := hq a; omega)
          simp only [zeroLeaves, positiveNodes]
          calc
            (A.map fun a => zeroLeaves A q hq ((U + 1) / q a)).sum ≤
                (A.map fun a => A.length * positiveNodes A q hq ((U + 1) / q a) + 1).sum := by
              apply List.sum_le_sum
              intro a ha
              exact hbranch a ha
            _ = A.length * (A.map fun a => positiveNodes A q hq ((U + 1) / q a)).sum +
                A.length := by
              rw [sum_map_add, sum_map_mul_left, sum_map_const]
              simp
            _ ≤ A.length * (1 + (A.map fun a => positiveNodes A q hq ((U + 1) / q a)).sum) + 1 := by
              calc
                _ = A.length * (1 + (A.map fun a => positiveNodes A q hq ((U + 1) / q a)).sum) := by ring
                _ ≤ _ := Nat.le_add_right _ _

theorem recursiveCalls_le_enumeratedSize_bound {α : Type} (A : List α)
    (q : α → Nat) (hq : ∀ a, 3 ≤ q a) (U : Nat) :
    recursiveCalls A q hq U ≤
      (A.length + 1) * (typedBudgetWords A q hq U).length + 1 := by
  rw [recursiveCalls_eq_nodes_add_zeroLeaves, positiveNodes_eq_outputLength]
  have hz := zeroLeaves_le_size_mul_nodes_add_one A q hq U
  calc
    (typedBudgetWords A q hq U).length + zeroLeaves A q hq U ≤
        (typedBudgetWords A q hq U).length +
          (A.length * (typedBudgetWords A q hq U).length + 1) := by
      apply Nat.add_le_add_left
      simpa [positiveNodes_eq_outputLength A q hq U] using hz
    _ = (A.length + 1) * (typedBudgetWords A q hq U).length + 1 := by ring

end Paper.CountStage.TypedWordRuntime
