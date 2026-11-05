import ILPEncoding.Bounds.SystemCommon
import ILPEncoding.Bounds.WordSize

/-! # Numeric Matrix-Size Closure
Defines the numeric envelopes `budgetS`, `budgetR`, `budgetA`, `numericMagnitude` and `numericMagnitudeUniform`. Proves `systemRowsC_numericBits_le`, a numeric matrix-size closure that takes the budget row as an explicit signed-envelope premise, and `systemRowsC_numericBits_uniform`, which depends on `U`, `K` and `n` alone.
-/

namespace Paper.F7System

open Paper.AffineNat Paper.F6ILP Paper.F6ILPCost Paper.F6ILPSystem
open Paper.F7Computable Paper.F7Encoding Paper.F7QControl Paper.F7Size Paper.F7WordSize
open Paper.AffineILP

def budgetS (U K n ell : Nat) : Nat :=
  ell * (8 * U * (27 * K ^ 3) * U * (n + 2 * U * K * ell + 1))

def budgetR (U K ell : Nat) : Nat :=
  ell * (8 * U * (27 * K ^ 3) * U * (U * ell))

def budgetA (U K n ell : Nat) : Nat :=
  U * (U + 2004 * (U + 1) ^ 6) + budgetS U K n ell

/-- One common coefficient envelope for all rows, from the separate terminal,
contraction, box, and budget-row envelopes. -/
def numericMagnitude (U K n ell : Nat) : Nat :=
  1 + n + (n + 2 * U * K * ell + U ^ 2) + (U * ell) +
    ((K + 1) * (n + 2 * U * K * ell) + U) +
    ((K + 1) * U * ell) + budgetA U K n ell + budgetR U K ell

def numericMagnitudeUniform (U K n : Nat) : Nat :=
  numericMagnitude U K n U

private theorem natAbs_le_of_signed_envelope (z : ℤ) (B M : Nat)
    (hB : -((B : Nat) : ℤ) ≤ z ∧ z ≤ B)
    (hBM : B ≤ M) : z.natAbs ≤ M := by
  by_cases hz : 0 ≤ z
  · have hn : (z.natAbs : ℤ) = z := Int.natAbs_of_nonneg hz
    have hM : (z.natAbs : ℤ) ≤ M := by
      rw [hn]
      exact le_trans hB.2 (by exact_mod_cast hBM)
    exact_mod_cast hM
  · have hzn : z ≤ 0 := le_of_not_ge hz
    have hn : (z.natAbs : ℤ) = -z := Int.ofNat_natAbs_of_nonpos hzn
    have hM : (z.natAbs : ℤ) ≤ M := by
      rw [hn]
      have hBMZ : (B : ℤ) ≤ M := by exact_mod_cast hBM
      omega
    exact_mod_cast hM

/-- Numeric matrix-size closure. The budget row is an explicit signed-envelope
premise; callers discharge it from the canonical leaf/budget theorem. -/
theorem systemRowsC_numericBits_le
    (labels : List Label) (x z : ℤ) (c lo hi price : Nat → Nat)
    (T U K n : Nat)
    (hbudget : qWord labels ≤ U)
    (hK : ∀ label ∈ labels, label.k ≤ K)
    (hx : -((n : Nat) : ℤ) ≤ x ∧ x ≤ n)
    (hz : 0 ≤ z ∧ z ≤ U)
    (hlohi : ∀ key ∈ usedKeys labels,
      lo key.val ≤ n ∧ hi key.val ≤ n)
    (hbudgetIntercept :
      -((budgetA U K n labels.length : Nat) : ℤ) ≤
        (budgetRow labels x z c price 1 T).intercept ∧
      (budgetRow labels x z c price 1 T).intercept ≤ budgetA U K n labels.length)
    (hbudgetCoeff : ∀ key,
      -((budgetR U K labels.length : Nat) : ℤ) ≤
        (budgetRow labels x z c price 1 T).coeff key ∧
      (budgetRow labels x z c price 1 T).coeff key ≤ budgetR U K labels.length) :
    matrixBits (systemRowsC labels x z c lo hi price 1 T) ≤
      (3 * U + 3) * (U + 1) * (numericMagnitude U K n labels.length + 2) := by
  let ell := labels.length
  let M := numericMagnitude U K n ell
  have hM1 : 1 ≤ M := by
    dsimp [M, numericMagnitude]
    omega
  have htermNat : n + 2 * U * K * ell + U ^ 2 ≤ M := by
    dsimp [M, numericMagnitude, budgetA, budgetS, budgetR]
    omega
  have hterm : (n : ℤ) + 2 * (U : ℤ) * K * labels.length +
      (U : ℤ) * U ≤ M := by
    have hcast : ((n + 2 * U * K * ell + U ^ 2 : Nat) : ℤ) ≤ M := by
      exact_mod_cast htermNat
    simpa [ell, pow_two] using hcast
  have htermCoeffNat : U * ell ≤ M := by
    dsimp [M, numericMagnitude, budgetA, budgetS, budgetR]
    omega
  have htermCoeff : (U : ℤ) * labels.length ≤ M := by
    have hcast : ((U * ell : Nat) : ℤ) ≤ M := by exact_mod_cast htermCoeffNat
    simpa [ell] using hcast
  have hcontractNat : (K + 1) * (n + 2 * U * K * ell) + U ≤ M := by
    dsimp [M, numericMagnitude, budgetA, budgetS, budgetR]
    omega
  have hcontract : ((K : ℤ) + 1) *
      ((n : ℤ) + 2 * (U : ℤ) * K * labels.length) + U ≤ M := by
    have hcast : (((K + 1) * (n + 2 * U * K * ell) + U : Nat) : ℤ) ≤ M := by
      exact_mod_cast hcontractNat
    simpa [ell] using hcast
  have hcontractCoeffNat : (K + 1) * U * ell ≤ M := by
    dsimp [M, numericMagnitude, budgetA, budgetS, budgetR]
    omega
  have hcontractCoeff : ((K : ℤ) + 1) * (U : ℤ) * labels.length ≤ M := by
    have hcast : (((K + 1) * U * ell : Nat) : ℤ) ≤ M := by
      exact_mod_cast hcontractCoeffNat
    simpa [ell] using hcast
  have hbound : n ≤ M := by
    dsimp [M, numericMagnitude, budgetA, budgetS, budgetR]
    omega
  have hbudgetA : budgetA U K n ell ≤ M := by
    dsimp [M, numericMagnitude]
    omega
  have hbudgetR : budgetR U K ell ≤ M := by
    dsimp [M, numericMagnitude]
    omega
  have hbudgetRow : RowAbsBound M (budgetRow labels x z c price 1 T) := by
    constructor
    · exact natAbs_le_of_signed_envelope _ (budgetA U K n ell) M
        hbudgetIntercept hbudgetA
    · intro key
      exact natAbs_le_of_signed_envelope _ (budgetR U K ell) M
        (hbudgetCoeff key) hbudgetR
  have hrows := systemRowsC_matrixBits_le labels x z c lo hi price T U K n M
    hbudget hK hx hz hM1 hterm htermCoeff hcontract hcontractCoeff
    hbound hlohi hbudgetRow
  have hsize := length_and_variable_card_le_of_qWord_bound labels U hbudget
  have hfirst : 2 * Fintype.card (Variable labels) + labels.length + 3 ≤
      3 * U + 3 := by omega
  have hsecond : Fintype.card (Variable labels) + 1 ≤ U + 1 := by omega
  have hproduct := Nat.mul_le_mul hfirst hsecond
  have hscaled := Nat.mul_le_mul_right (M + 2) hproduct
  simpa [M, ell] using hrows.trans hscaled

/-- Replacing the label count by U yields a fixed polynomial envelope in
numeric U,K,n alone. -/
theorem numericMagnitude_le_uniform (U K n ell : Nat) (hell : ell ≤ U) :
    numericMagnitude U K n ell ≤ numericMagnitudeUniform U K n := by
  unfold numericMagnitudeUniform numericMagnitude budgetA budgetS budgetR
  gcongr <;> omega

/-- A system-row bound from `systemRowsC_numericBits_le` becomes a numeric
polynomial bound in U,K,n alone, using qWord to absorb both list and variable
counts. -/
theorem systemRowsC_numericBits_uniform
    (labels : List Label) (x z : ℤ) (c lo hi price : Nat → Nat)
    (T U K n : Nat)
    (hbudget : qWord labels ≤ U)
    (hbits : matrixBits (systemRowsC labels x z c lo hi price 1 T) ≤
      (3 * U + 3) * (U + 1) *
        (numericMagnitude U K n labels.length + 2)) :
    matrixBits (systemRowsC labels x z c lo hi price 1 T) ≤
      (3 * U + 3) * (U + 1) *
        (numericMagnitudeUniform U K n + 2) := by
  have hsize := length_and_variable_card_le_of_qWord_bound labels U hbudget
  have hmag := numericMagnitude_le_uniform U K n labels.length hsize.1
  calc
    matrixBits (systemRowsC labels x z c lo hi price 1 T) ≤
        (3 * U + 3) * (U + 1) *
          (numericMagnitude U K n labels.length + 2) := hbits
    _ ≤ (3 * U + 3) * (U + 1) *
          (numericMagnitudeUniform U K n + 2) := by
      exact Nat.mul_le_mul_left ((3 * U + 3) * (U + 1))
        (Nat.add_le_add_right hmag 2)

end Paper.F7System
