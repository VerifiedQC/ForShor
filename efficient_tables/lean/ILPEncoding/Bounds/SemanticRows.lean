import ILPEncoding.Bounds.ComputableRows

/-! # Semantics of the Computable Rows
Proves `usedKeys_complete`, evaluation lemmas `evalInt_lowerRow` and `evalInt_upperRow`, `boundRows_iff`, and `systemRowsC_iff_feasible`: the computable system rows are all nonnegative exactly when the `Feasible` predicate holds.
-/

namespace Paper.F7Semantics

open Paper.F6ILP Paper.F6ILPRows Paper.F6ILPCost Paper.F6ILPSystem
open Paper.F6ILPFeasible Paper.F7Encoding Paper.F7Computable
open Paper.AffineNat

theorem usedKeys_complete (labels : List Label) (key : Variable labels) :
    key ∈ usedKeys labels := by
  unfold usedKeys
  simp only [List.mem_map, List.mem_attach, true_and]
  have hm : key.val ∈ (labels.map Label.k).dedup := by
    simpa only [List.mem_dedup, usedArities, List.mem_toFinset] using key.property
  refine ⟨⟨key.val, hm⟩, ?_⟩
  apply Subtype.ext
  rfl

theorem evalInt_lowerRow {keys : Finset Nat}
    (key : { k : Nat // k ∈ keys }) (lo : Nat → Nat)
    (values : { k : Nat // k ∈ keys } → ℤ) :
    evalInt (lowerRow key lo) values = values key - lo key.val := by
  simp [evalInt, lowerRow, Finset.sum_ite_eq']; ring

theorem evalInt_upperRow {keys : Finset Nat}
    (key : { k : Nat // k ∈ keys }) (hi : Nat → Nat)
    (values : { k : Nat // k ∈ keys } → ℤ) :
    evalInt (upperRow key hi) values = hi key.val - values key := by
  simp [evalInt, upperRow, Finset.sum_ite_eq']; ring

theorem boundRows_iff {keys : Finset Nat}
    (lo hi : Nat → Nat) (ks : List { k : Nat // k ∈ keys })
    (values : { k : Nat // k ∈ keys } → ℤ) :
    (boundRows lo hi ks).Forall (fun row => 0 ≤ evalInt row values) ↔
      ∀ key ∈ ks, (lo key.val : ℤ) ≤ values key ∧
        values key ≤ (hi key.val : ℤ) := by
  induction ks with
  | nil => simp [boundRows]
  | cons key rest ih =>
      simp only [boundRows, List.forall_cons, List.mem_cons]
      rw [evalInt_lowerRow, evalInt_upperRow, ih]
      constructor
      · rintro ⟨hl, hu, hrest⟩ q (hq | hq)
        · subst q
          constructor <;> omega
        · exact hrest q hq
      · intro h
        have hk := h key (Or.inl rfl)
        refine ⟨by omega, by omega, ?_⟩
        intro q hq
        exact h q (Or.inr hq)

theorem systemRowsC_iff_feasible (labels : List Label) (x z : ℤ)
    (c lo hi : Nat → Nat) (price : Nat → Nat) (N T : Nat)
    (values : Variable labels → ℤ) :
    (systemRowsC labels x z c lo hi price N T).Forall
      (fun row => 0 ≤ evalInt row values) ↔
        Feasible labels x z c lo hi price N T values := by
  have hscale : evalInt (scaleExpr (-1) (terminalRow labels x z)) values =
      -evalInt (terminalRow labels x z) values := by
    simp [evalInt, scaleExpr, Finset.mul_sum]
    ring
  have hb : (∀ key ∈ usedKeys labels,
      (lo key.val : ℤ) ≤ values key ∧ values key ≤ (hi key.val : ℤ)) ↔
      ∀ key : Variable labels,
        (lo key.val : ℤ) ≤ values key ∧ values key ≤ (hi key.val : ℤ) := by
    constructor
    · intro h key
      exact h key (usedKeys_complete labels key)
    · intro h key _
      exact h key
  have heq : (0 ≤ evalInt (terminalRow labels x z) values ∧
      0 ≤ -evalInt (terminalRow labels x z) values) ↔
      evalInt (terminalRow labels x z) values = 0 := by omega
  simp only [systemRowsC, List.forall_append, List.forall_cons,
    and_true, boundRows_iff, hscale, Feasible]
  simp only [← and_assoc]
  rw [heq, hb]
  simp
end Paper.F7Semantics





