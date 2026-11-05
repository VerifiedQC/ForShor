import ILPEncoding.Bounds.BudgetStep
import ILPEncoding.Bounds.QControl
import ILPEncoding.Bounds.Products

/-! # Budget Bounds for Actual Words
Proves bounds on the cleared budget terms of actual label words: `quotient_budget_bound`, `termBounded_of_budget_aux` and `clearedRoot_bound`. Also proves `shared_charge_cap`, a cap on the shared charge.
-/

namespace Paper.F7Budget

open Paper.F6ILP Paper.F6ILPRows Paper.F6ILPCost Paper.AffineNat
open Paper.F6ILPSystem Paper.AffineILP
open Paper.F7Size Paper.F7QControl
open Paper.F7Products

theorem quotient_budget_bound (D P : ℤ) (k U : Nat)
    (hD : 0 ≤ D ∧ D ≤ U) (hP : 0 < P) (hk : 1 ≤ k) :
    0 ≤ D / (P * k) ∧ D / (P * k) ≤ U := by
  have hden : 0 ≤ P * (k : ℤ) := by positivity
  exact ⟨Int.ediv_nonneg hD.1 hden,
    le_trans (Int.ediv_le_self _ hD.1) hD.2⟩

theorem n_le_of_qBudget (U N : Nat) (labels : List Label)
    (hbudget : N * qWord labels ≤ U) : N ≤ U := by
  have h := Nat.mul_le_mul_left N (qWord_pos labels)
  have hh : N ≤ N * qWord labels := by
    simpa only [mul_one] using h
  exact le_trans hh hbudget

theorem termBounded_of_budget_aux {keys : Finset Nat}
    (D : ℤ) (c : Nat → Nat) (N : Nat) (P : ℤ)
    (e : AffineExpr keys) (labels : List Label)
    (hkeys : ∀ label ∈ labels, label.k ∈ keys)
    (U K H B0 C0 : Nat)
    (hD : 0 ≤ D ∧ D ≤ U) (hP : 0 < P)
    (hcontrol : Controlled U K P labels)
    (hbudget : N * qWord labels ≤ U)
    (hcap : ∀ label ∈ labels, c label.k ≤ H)
    (he : -(B0 : ℤ) ≤ e.intercept ∧ e.intercept ≤ B0)
    (hc : ∀ key, 0 ≤ e.coeff key ∧ e.coeff key ≤ C0) :
    TermBounded D c
      (8 * (U : ℤ) * H * U * (B0 + 2 * U * K * labels.length + 1))
      (8 * (U : ℤ) * H * U * (C0 + U * labels.length))
      N P e labels hkeys := by
  induction labels generalizing N P e B0 C0 with
  | nil =>
      simp [TermBounded]
  | cons label rest ih =>
      let hk := hkeys label (by simp)
      let next := stepExpr e P label hk
      let hrest : ∀ q ∈ rest, q.k ∈ keys := by
        intro q hq
        exact hkeys q (by simp [hq])
      have hnext := step_constant_bounds e P U K B0 label hk
        (le_of_lt hP) hcontrol.2.1 hcontrol.2.2.1 he
      have hnextCoeff := step_coeff_nonneg_le e P U C0 label hk
        (le_of_lt hP) hcontrol.2.1 hc
      have hBrow : (B0 : ℤ) + 2 * U * K ≤
          B0 + 2 * U * K * (label :: rest).length := by
        simp only [List.length_cons, Nat.cast_succ]
        nlinarith [mul_nonneg (by positivity : 0 ≤ (2 : ℤ) * U * K)
          (Int.natCast_nonneg rest.length)]
      have hCrow : (C0 : ℤ) + U ≤
          C0 + U * (label :: rest).length := by
        simp only [List.length_cons, Nat.cast_succ]
        nlinarith [mul_nonneg (Int.natCast_nonneg U)
          (Int.natCast_nonneg rest.length)]
      have hnextB :
          -((B0 + 2 * U * K * (label :: rest).length : Nat) : ℤ) ≤
              next.intercept ∧
          next.intercept ≤
              ((B0 + 2 * U * K * (label :: rest).length : Nat) : ℤ) := by
        have hbig : ((B0 + 2 * U * K : Nat) : ℤ) ≤
            ((B0 + 2 * U * K * (label :: rest).length : Nat) : ℤ) := by
          simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
            using hBrow
        have hsmall : -((B0 + 2 * U * K : Nat) : ℤ) ≤
            next.intercept ∧
            next.intercept ≤ ((B0 + 2 * U * K : Nat) : ℤ) := by
          simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
            using hnext
        exact ⟨le_trans (neg_le_neg hbig) hsmall.1,
          le_trans hsmall.2 hbig⟩
      have hnextC : ∀ key, 0 ≤ next.coeff key ∧
          next.coeff key ≤
            ((C0 + U * (label :: rest).length : Nat) : ℤ) := by
        intro key
        have hbig : ((C0 + U : Nat) : ℤ) ≤
            ((C0 + U * (label :: rest).length : Nat) : ℤ) := by
          simpa only [Nat.cast_add, Nat.cast_mul] using hCrow
        have hsmall : 0 ≤ next.coeff key ∧
            next.coeff key ≤ ((C0 + U : Nat) : ℤ) := by
          simpa only [Nat.cast_add] using hnextCoeff key
        exact ⟨hsmall.1, le_trans hsmall.2 hbig⟩
      have hQ := quotient_budget_bound D P label.k U hD hP
        (Nat.le_trans (by decide : 1 ≤ 2) label.hk)
      have hN : N ≤ U := n_le_of_qBudget U N _ hbudget
      have hhead := clearedTerm_bound next D (D / (P * label.k))
        N (c label.k) U H
        (B0 + 2 * U * K * (label :: rest).length)
        (C0 + U * (label :: rest).length)
        hD hQ hN (hcap label (by simp)) hnextB hnextC
      have hq : 2 * (label.k - 1) + 1 = 2 * label.k - 1 := by
        have hk2 := label.hk
        omega
      have htailBudget :
          (N * (2 * (label.k - 1) + 1)) * qWord rest ≤ U := by
        simpa only [qWord, hq, mul_assoc] using hbudget
      have htailCap : ∀ q ∈ rest, c q.k ≤ H := by
        intro q hqmem
        exact hcap q (by simp [hqmem])
      have hkpos : (0 : ℤ) < label.k := by
        exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) label.hk)
      have hPnext : 0 < P * label.k := mul_pos hP hkpos
      have htail := ih (N * (2 * (label.k - 1) + 1))
        (P * label.k) next hrest (B0 + 2 * U * K) (C0 + U)
        hPnext hcontrol.2.2.2 htailBudget htailCap
        (by simpa only [Nat.cast_add, Nat.cast_mul] using hnext)
        (by intro key; simpa only [Nat.cast_add] using hnextCoeff key)
      have htail' : TermBounded D c
          (8 * (U : ℤ) * H * U *
            (B0 + 2 * U * K * (label :: rest).length + 1))
          (8 * (U : ℤ) * H * U *
            (C0 + U * (label :: rest).length))
          (N * (2 * (label.k - 1) + 1)) (P * label.k)
          next rest hrest := by
        convert htail using 1 <;>
          simp only [List.length_cons, Nat.cast_succ, Nat.cast_add,
            Nat.cast_mul] <;> ring
      exact ⟨hhead, htail'⟩

theorem clearedRoot_bound (labels : List Label) (x : ℤ)
    (c : Nat → Nat) (U K H n : Nat)
    (hbudget : qWord labels ≤ U)
    (hK : ∀ label ∈ labels, label.k ≤ K)
    (hcap : ∀ label ∈ labels, c label.k ≤ H)
    (hx : -((n : Nat) : ℤ) ≤ x ∧ x ≤ n) :
    AbsBound
      (clearedExpr
        (terminalProduct 1
          (labels.map (instantiate (fun _ => 0))))
        c 1 1 (rootExpr labels x) labels (keyProof labels))
      (labels.length *
        (8 * (U : ℤ) * H * U *
          (n + 2 * U * K * labels.length + 1)))
      (labels.length *
        (8 * (U : ℤ) * H * U *
          (U * labels.length))) := by
  let D := terminalProduct 1
    (labels.map (instantiate (fun _ => 0)))
  have hD : 0 ≤ D ∧ D ≤ U := by
    constructor
    · exact le_of_lt (Paper.F6Cleared.terminalProduct_pos
        1 _ (by decide))
    · exact terminalProduct_le_typed_budget U (fun _ => 0)
        labels hbudget
  have hcontrol : Controlled U K 1 labels :=
    controlled_of_qWord U K 1 labels
      (by simpa using hbudget) hK
  have hroot : -(n : ℤ) ≤ (rootExpr labels x).intercept ∧
      (rootExpr labels x).intercept ≤ n := by
    simpa only [rootExpr, startExpr] using hx
  have hc : ∀ key, 0 ≤ (rootExpr labels x).coeff key ∧
      (rootExpr labels x).coeff key ≤ (0 : ℤ) := by
    intro key
    simp [rootExpr, startExpr]
  have hterms := termBounded_of_budget_aux D c 1 1
    (rootExpr labels x) labels (keyProof labels)
    U K H n 0 hD (by decide) hcontrol
    (by simpa using hbudget) hcap hroot hc
  have hA : 0 ≤ 8 * (U : ℤ) * H * U *
      (n + 2 * U * K * labels.length + 1) := by positivity
  have hC : 0 ≤ 8 * (U : ℤ) * H * U *
      (0 + U * labels.length) := by positivity
  have hsum := clearedExpr_sum_bound D c
    (8 * (U : ℤ) * H * U *
      (n + 2 * U * K * labels.length + 1))
    (8 * (U : ℤ) * H * U *
      (0 + U * labels.length))
    1 1 (rootExpr labels x) labels (keyProof labels)
    hA hC hterms
  simpa only [D, zero_add] using hsum

theorem shared_charge_cap (labels : List Label)
    (c : Nat → Nat) (K : Nat)
    (hK : ∀ label ∈ labels, label.k ≤ K)
    (hlabelCap : ∀ label ∈ labels, label.c ≤ 27 * label.k ^ 3)
    (hshared : ∀ label ∈ labels, label.c = c label.k) :
    ∀ label ∈ labels, c label.k ≤ 27 * K ^ 3 := by
  intro label hmem
  have hpower := Nat.pow_le_pow_left (hK label hmem) 3
  have hbound := hlabelCap label hmem
  rw [hshared label hmem] at hbound
  exact le_trans hbound (Nat.mul_le_mul_left 27 hpower)

end Paper.F7Budget
