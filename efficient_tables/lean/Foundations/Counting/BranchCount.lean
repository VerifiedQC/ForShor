import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Fintype.BigOperators

/-!
# Branch counts of arity words

Defines the per-arity branch count `q k = 2 * k - 1` and the product `qProduct` of branch counts over a word of arities. Proves that every arity of at least two contributes at least three branches, giving `three_pow_length_le_qProduct`, and bounds the product over distinct entries by the product over the whole list (`prod_toFinset_q_le_list`).
-/

namespace Paper.CountStage.Bounds

/-- The per-arity branch count. -/
def q (k : Nat) : Nat := 2 * k - 1

/-- Product of branch counts over a word, retaining repetitions. -/
def qProduct (ks : List Nat) : Nat := (ks.map q).prod

/-- The set of distinct arities represented by a word. -/
def distinctArities (ks : List Nat) : Finset Nat := ks.toFinset

theorem q_ge_three {k : Nat} (hk : 2 ≤ k) : 3 ≤ q k := by
  simp [q]
  omega

/-- Every valid arity contributes at least three branches, so arbitrary
repeated-arity words satisfy the exponential lower bound. -/
theorem three_pow_length_le_qProduct : ∀ ks : List Nat,
    (∀ k ∈ ks, 2 ≤ k) → 3 ^ ks.length ≤ qProduct ks
  | [], _ => by simp [qProduct]
  | k :: ks, hall => by
      have hk : 2 ≤ k := hall k (by simp)
      have ht : ∀ x ∈ ks, 2 ≤ x := by
        intro x hx
        exact hall x (by simp [hx])
      have hq := q_ge_three hk
      have htail := three_pow_length_le_qProduct ks ht
      simp only [qProduct, List.map_cons, List.prod_cons, List.length_cons, pow_succ]
      calc
        3 ^ ks.length * 3 = 3 * 3 ^ ks.length := Nat.mul_comm _ _
        _ ≤ q k * 3 ^ ks.length := Nat.mul_le_mul_right _ hq
        _ ≤ q k * qProduct ks := Nat.mul_le_mul_left _ htail

/-- The product over distinct list entries is bounded by the product over all
entries; repetitions can only increase the latter. -/
theorem prod_toFinset_q_le_list {ks : List Nat}
    (hall : ∀ k ∈ ks, 2 ≤ k) :
    (∏ k ∈ ks.toFinset, q k) ≤ qProduct ks := by
  induction ks with
  | nil => simp [qProduct]
  | cons k ks ih =>
      have hk : 2 ≤ k := hall k (by simp)
      have ht : ∀ x ∈ ks, 2 ≤ x := by
        intro x hx
        exact hall x (by simp [hx])
      have ih' := ih ht
      by_cases hm : k ∈ ks.toFinset
      · simp only [List.toFinset_cons, Finset.insert_eq_of_mem hm,
          qProduct] at *
        have hq : 1 ≤ q k := by have := q_ge_three hk; omega
        exact ih'.trans (Nat.le_mul_of_pos_left _ (by omega))
      · simp only [List.toFinset_cons, Finset.prod_insert hm, qProduct]
        exact Nat.mul_le_mul_left (q k) ih'

/-- A set of `m` distinct arities, each at least two, has branch-count
product at least `m!`. The increasing enumeration of the set has its `i`th
entry at least `i+2`, and hence branch count at least `i+3`. -/
theorem factorial_card_le_prod_q (s : Finset Nat)
    (hs : ∀ k ∈ s, 2 ≤ k) : s.card.factorial ≤ ∏ k ∈ s, q k := by
  classical
  let m := s.card
  have hcard : s.card = m := rfl
  let e : Fin m ↪o Nat := s.orderEmbOfFin hcard
  have rank_bound (i : Fin m) : i.val + 2 ≤ e i := by
    have haux : ∀ n (hn : n < m), n + 2 ≤ e ⟨n, hn⟩ := by
      intro n
      induction n with
      | zero =>
          intro hn
          let i0 : Fin m := ⟨0, hn⟩
          have hi : e i0 ∈ s := Finset.orderEmbOfFin_mem s hcard i0
          have hh := hs (e i0) hi
          change 2 ≤ e i0
          exact hh
      | succ n ih =>
          intro hn
          have hn' : n < m := by omega
          have hi : (⟨n, hn'⟩ : Fin m) < ⟨n + 1, hn⟩ := by
            exact Fin.mk_lt_mk.mpr (by omega)
          have hlt := e.strictMono hi
          have hprev := ih hn'
          omega
    exact haux i.val i.isLt
  have hterm : ∀ i : Fin m, i.val + 1 ≤ q (e i) := by
    intro i
    have hr := rank_bound i
    simp [q]
    omega
  have hprod : (∏ i : Fin m, (i.val + 1)) ≤ ∏ i : Fin m, q (e i) := by
    apply Finset.prod_le_prod (s := Finset.univ)
    · intro i hi
      omega
    · intro i hi
      exact hterm i
  have hfact : (∏ i : Fin m, (i.val + 1)) = m.factorial := by
    rw [Fin.prod_univ_eq_prod_range (fun j => j + 1) m]
    exact (Nat.factorial_eq_prod_range_add_one m).symm
  have heq : (∏ i : Fin m, q (e i)) = ∏ k ∈ s, q k := by
    calc
      (∏ i : Fin m, q (e i)) = ∏ k ∈ (Finset.univ.image e), q k := by
        symm
        exact Finset.prod_image e.injective.injOn
      _ = ∏ k ∈ s, q k := by rw [Finset.image_orderEmbOfFin_univ]
  calc
    s.card.factorial = m.factorial := by rw [hcard]
    _ = ∏ i : Fin m, (i.val + 1) := hfact.symm
    _ ≤ ∏ i : Fin m, q (e i) := hprod
    _ = ∏ k ∈ s, q k := heq

/-- Factorial growth in the number of distinct arities is controlled by the
word's full branch-count product, including when arities repeat. -/
theorem factorial_distinct_le_qProduct {ks : List Nat}
    (hall : ∀ k ∈ ks, 2 ≤ k) :
    (distinctArities ks).card.factorial ≤ qProduct ks := by
  have hs : ∀ k ∈ distinctArities ks, 2 ≤ k := by
    intro k hk
    exact hall k (List.mem_toFinset.mp hk)
  exact (factorial_card_le_prod_q (distinctArities ks) hs).trans
    (prod_toFinset_q_le_list hall)

end Paper.CountStage.Bounds
