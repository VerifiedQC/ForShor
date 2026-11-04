import ILPEncoding.Bounds.ComputableRows
import ILPEncoding.Bounds.Terminal
import ILPEncoding.Bounds.ContractionRoot
import ILPEncoding.Bounds.Matrix

/-! # Common Row Bounds for the System
Defines `RowAbsBound` and proves `systemRowsC_row_bounds`, a common absolute-value bound on every system row, assembled from the terminal, contraction, box and budget envelopes. Concludes `systemRowsC_matrixBits_le`, a bit-size bound for the system matrix.
-/

namespace Paper.F7System

open Paper.F6ILP Paper.F6ILPRows Paper.F6ILPCost Paper.F6ILPSystem
open Paper.F7Encoding Paper.F7Computable Paper.F7Terminal Paper.F7Contraction
open Paper.F7Size Paper.F7QControl Paper.AffineNat

private theorem natAbs_le_of_signed_bounds (z : ℤ) (M : Nat)
    (hlo : -((M : Nat) : ℤ) ≤ z) (hhi : z ≤ M) :
    z.natAbs ≤ M := by
  by_cases hz : 0 ≤ z
  · have hnat : (z.natAbs : ℤ) = z := Int.natAbs_of_nonneg hz
    have hle : (z.natAbs : ℤ) ≤ M := by rw [hnat]; omega
    exact_mod_cast hle
  · have hzn : z ≤ 0 := le_of_not_ge hz
    have hnat : (z.natAbs : ℤ) = -z := Int.ofNat_natAbs_of_nonpos hzn
    have hle : (z.natAbs : ℤ) ≤ M := by rw [hnat]; omega
    exact_mod_cast hle

def RowAbsBound {keys : Finset Nat} (M : Nat) (row : AffineExpr keys) : Prop :=
  row.intercept.natAbs ≤ M ∧ ∀ key, (row.coeff key).natAbs ≤ M

private theorem forall_append_rowAbsBound {keys : Finset Nat} (M : Nat)
    (xs ys : List (AffineExpr keys))
    (hxs : xs.Forall (RowAbsBound M)) (hys : ys.Forall (RowAbsBound M)) :
    (xs ++ ys).Forall (RowAbsBound M) := by
  apply (List.forall_iff_forall_mem).2
  intro row hmem
  rcases List.mem_append.mp hmem with hleft | hright
  · exact (List.forall_iff_forall_mem).1 hxs row hleft
  · exact (List.forall_iff_forall_mem).1 hys row hright

private theorem boundRows_rowAbsBound {keys : Finset Nat}
    (lo hi : Nat → Nat) (ks : List { k : Nat // k ∈ keys })
    (n M : Nat) (hM1 : 1 ≤ M) (hbound : n ≤ M)
    (hlohi : ∀ key ∈ ks, lo key.val ≤ n ∧ hi key.val ≤ n) :
    (boundRows lo hi ks).Forall (RowAbsBound M) := by
  induction ks with
  | nil => simp [boundRows]
  | cons key rest ih =>
      have hkey := hlohi key (by simp)
      have htail : ∀ q ∈ rest, lo q.val ≤ n ∧ hi q.val ≤ n := by
        intro q hq
        exact hlohi q (by simp [hq])
      have htailRows := ih htail
      have hnM : (n : ℤ) ≤ M := by exact_mod_cast hbound
      have hloM : (lo key.val : ℤ) ≤ M := by
        exact_mod_cast (le_trans hkey.1 hbound)
      have hhiM : (hi key.val : ℤ) ≤ M := by
        exact_mod_cast (le_trans hkey.2 hbound)
      have hloNonneg : 0 ≤ (lo key.val : ℤ) := by positivity
      have hhiNonneg : 0 ≤ (hi key.val : ℤ) := by positivity
      have hrowLo : RowAbsBound M (lowerRow key lo) := by
        constructor
        · have hval := natAbs_le_of_signed_bounds
            (-(lo key.val : ℤ)) M (by omega) (by omega)
          simpa [lowerRow] using hval
        · intro j
          by_cases hj : j = key
          · simpa [lowerRow, hj] using hM1
          · simp [lowerRow, hj]
      have hrowHi : RowAbsBound M (upperRow key hi) := by
        constructor
        · have hval := natAbs_le_of_signed_bounds
            (hi key.val : ℤ) M (by omega) hhiM
          simpa [upperRow] using hval
        · intro j
          by_cases hj : j = key
          · simpa [upperRow, hj] using hM1
          · simp [upperRow, hj]
      simp only [boundRows, List.forall_cons]
      exact ⟨hrowLo, hrowHi, htailRows⟩

theorem systemRowsC_row_bounds
    (labels : List Label) (x z : ℤ)
    (c lo hi : Nat → Nat) (price : Nat → Nat) (T U K n M : Nat)
    (hbudget : qWord labels ≤ U)
    (hK : ∀ label ∈ labels, label.k ≤ K)
    (hx : -((n : Nat) : ℤ) ≤ x ∧ x ≤ n)
    (hz : 0 ≤ z ∧ z ≤ U)
    (hM1 : 1 ≤ M)
    (hterm : (n : ℤ) + 2 * (U : ℤ) * K * labels.length +
      (U : ℤ) * U ≤ M)
    (htermCoeff : (U : ℤ) * labels.length ≤ M)
    (hcontract : ((K : ℤ) + 1) *
      ((n : ℤ) + 2 * (U : ℤ) * K * labels.length) + U ≤ M)
    (hcontractCoeff : ((K : ℤ) + 1) * (U : ℤ) * labels.length ≤ M)
    (hbound : n ≤ M)
    (hlohi : ∀ key ∈ usedKeys labels,
      lo key.val ≤ n ∧ hi key.val ≤ n)
    (hbudgetRow : RowAbsBound M
      (budgetRow labels x z c price 1 T)) :
    ∀ row ∈ systemRowsC labels x z c lo hi price 1 T,
      RowAbsBound M row := by
  let nZ : ℤ := n
  have hnZ : 0 ≤ nZ := by positivity
  have hxZ : -nZ ≤ x ∧ x ≤ nZ := by simpa [nZ] using hx
  have htermRow := terminalRow_bounds labels x z (fun _ => 0) U K nZ
    hbudget hK hxZ hz
  have htermZ : nZ + 2 * (U : ℤ) * K * labels.length +
      (U : ℤ) * U ≤ M := by
    simpa [nZ] using hterm
  have htermCoeffZ : (U : ℤ) * labels.length ≤ M := by
    simpa using htermCoeff
  have hterminal : RowAbsBound M (terminalRow labels x z) := by
    constructor
    · exact natAbs_le_of_signed_bounds _ M
        (by have h := htermRow.1; omega)
        (by have h := htermRow.2.1; omega)
    · intro key
      have hpos := (htermRow.2.2 key).1
      have hupper := (htermRow.2.2 key).2
      have hupperM : (terminalRow labels x z).coeff key ≤ M :=
        le_trans hupper htermCoeffZ
      have hlowerM : -M ≤ (terminalRow labels x z).coeff key := by omega
      exact natAbs_le_of_signed_bounds _ M hlowerM hupperM
  have hterminalNeg : RowAbsBound M (scaleExpr (-1)
      (terminalRow labels x z)) := by
    constructor
    · simpa [scaleExpr] using hterminal.1
    · intro key
      simpa [scaleExpr] using hterminal.2 key
  have hconRows := contractionRoot_bounds labels x nZ U K hbudget hK
    hnZ hxZ
  have hcontractCoeffZ : ((K : ℤ) + 1) * (U : ℤ) * labels.length ≤ M := by
    simpa using hcontractCoeff
  have hcontraction : (contractionRoot labels x).Forall (RowAbsBound M) := by
    apply List.Forall.imp (p := fun row =>
      -( ((K : ℤ) + 1) * ((n : ℤ) + 2 * (U : ℤ) * K * labels.length) + U) ≤
        row.intercept ∧
      row.intercept ≤ ((K : ℤ) + 1) *
        ((n : ℤ) + 2 * (U : ℤ) * K * labels.length) + U ∧
      (∀ key, -(((K : ℤ) + 1) * (U : ℤ) * labels.length) ≤
        row.coeff key ∧ row.coeff key ≤ ((K : ℤ) + 1) *
          (U : ℤ) * labels.length))
    · intro row hrow
      constructor
      · apply natAbs_le_of_signed_bounds
        · omega
        · omega
      · intro key
        apply natAbs_le_of_signed_bounds
        · have hlow := (hrow.2.2 key).1
          omega
        · have hup := (hrow.2.2 key).2
          exact le_trans hup hcontractCoeffZ
    · simpa [nZ] using hconRows
  have hbudgetList : ([budgetRow labels x z c price 1 T] :
      List (AffineExpr (usedArities labels))).Forall (RowAbsBound M) := by
    simpa [hbudgetRow]
  have hboundRows := boundRows_rowAbsBound lo hi (usedKeys labels) n M
    hM1 hbound hlohi
  intro row hrow
  have hall : (systemRowsC labels x z c lo hi price 1 T).Forall
      (RowAbsBound M) := by
    have hfirst : ([terminalRow labels x z,
        scaleExpr (-1) (terminalRow labels x z)] :
        List (AffineExpr (usedArities labels))).Forall (RowAbsBound M) := by
      simp [hterminal, hterminalNeg]
    have hconTail := forall_append_rowAbsBound M
      ((contractionRoot labels x) ++ [budgetRow labels x z c price 1 T])
      (boundRows lo hi (usedKeys labels))
      (forall_append_rowAbsBound M (contractionRoot labels x)
        [budgetRow labels x z c price 1 T] hcontraction hbudgetList)
      hboundRows
    have hwhole := forall_append_rowAbsBound M
      ([terminalRow labels x z, scaleExpr (-1) (terminalRow labels x z)])
      (contractionRoot labels x ++ [budgetRow labels x z c price 1 T] ++
        boundRows lo hi (usedKeys labels)) hfirst hconTail
    simpa [systemRowsC] using hwhole
  exact (List.forall_iff_forall_mem).1 hall row hrow

theorem systemRowsC_matrixBits_le
    (labels : List Label) (x z : ℤ)
    (c lo hi : Nat → Nat) (price : Nat → Nat) (T U K n M : Nat)
    (hbudget : qWord labels ≤ U)
    (hK : ∀ label ∈ labels, label.k ≤ K)
    (hx : -((n : Nat) : ℤ) ≤ x ∧ x ≤ n)
    (hz : 0 ≤ z ∧ z ≤ U)
    (hM1 : 1 ≤ M)
    (hterm : (n : ℤ) + 2 * (U : ℤ) * K * labels.length +
      (U : ℤ) * U ≤ M)
    (htermCoeff : (U : ℤ) * labels.length ≤ M)
    (hcontract : ((K : ℤ) + 1) *
      ((n : ℤ) + 2 * (U : ℤ) * K * labels.length) + U ≤ M)
    (hcontractCoeff : ((K : ℤ) + 1) * (U : ℤ) * labels.length ≤ M)
    (hbound : n ≤ M)
    (hlohi : ∀ key ∈ usedKeys labels,
      lo key.val ≤ n ∧ hi key.val ≤ n)
    (hbudgetRow : RowAbsBound M
      (budgetRow labels x z c price 1 T)) :
    matrixBits (systemRowsC labels x z c lo hi price 1 T) ≤
      (2 * Fintype.card (Variable labels) + labels.length + 3) *
        (Fintype.card (Variable labels) + 1) * (M + 2) := by
  have hrows := systemRowsC_row_bounds labels x z c lo hi price T U K n M
    hbudget hK hx hz hM1 hterm htermCoeff hcontract hcontractCoeff
    hbound hlohi hbudgetRow
  have hmatrix := matrixBits_le
    (systemRowsC labels x z c lo hi price 1 T) M hrows
  rw [systemRowsC_length, usedKeys_card] at hmatrix
  exact hmatrix

end Paper.F7System

