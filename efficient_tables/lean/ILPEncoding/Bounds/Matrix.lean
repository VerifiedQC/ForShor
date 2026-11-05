import ILPEncoding.Bounds.QControl

/-! # Matrix Bit Size
Defines `binaryBits`, `rowBits` and `matrixBits`, the box rows `lowerRow`, `upperRow` and `boundRows`, and the noncomputable `systemRows`. Proves `binaryBits_le`, `rowBits_le` and `matrixBits_le`, which bound bit sizes by magnitude bounds, and `boundRows_length` and `systemRows_length`.
-/

namespace Paper.F7Encoding

open Paper.F6ILP Paper.F6ILPRows Paper.F6ILPCost Paper.F6ILPSystem
open Paper.F6Objective Paper.F6Cleared Paper.AffineNat

def binaryBits (z : ℤ) : Nat := Nat.log2 z.natAbs + 2

theorem binaryBits_le (z : ℤ) (M : Nat) (h : z.natAbs ≤ M) :
    binaryBits z ≤ M + 2 := by
  unfold binaryBits
  exact Nat.add_le_add_right ((Nat.log2_le_self _).trans h) 2

def rowBits {keys : Finset Nat} (row : AffineExpr keys) : Nat :=
  binaryBits row.intercept +
    ∑ key : { k : Nat // k ∈ keys }, binaryBits (row.coeff key)

def matrixBits {keys : Finset Nat} (rows : List (AffineExpr keys)) : Nat :=
  (rows.map rowBits).sum

theorem rowBits_le {keys : Finset Nat} (row : AffineExpr keys)
    (M : Nat) (hintercept : row.intercept.natAbs ≤ M)
    (hcoeff : ∀ key, (row.coeff key).natAbs ≤ M) :
    rowBits row ≤ (Fintype.card { k : Nat // k ∈ keys } + 1) * (M + 2) := by
  have hsum : (∑ key : { k : Nat // k ∈ keys }, binaryBits (row.coeff key)) ≤
      ∑ _key : { k : Nat // k ∈ keys }, (M + 2) := by
    apply Finset.sum_le_sum
    intro key _
    exact binaryBits_le _ M (hcoeff key)
  calc
    rowBits row ≤ (M + 2) +
        ∑ _key : { k : Nat // k ∈ keys }, (M + 2) :=
      Nat.add_le_add (binaryBits_le _ M hintercept) hsum
    _ = (Fintype.card { k : Nat // k ∈ keys } + 1) * (M + 2) := by
      simp [add_mul, Nat.add_comm]

theorem matrixBits_le {keys : Finset Nat}
    (rows : List (AffineExpr keys)) (M : Nat)
    (hrows : ∀ row ∈ rows,
      row.intercept.natAbs ≤ M ∧
      ∀ key, (row.coeff key).natAbs ≤ M) :
    matrixBits rows ≤ rows.length *
      (Fintype.card { k : Nat // k ∈ keys } + 1) * (M + 2) := by
  induction rows with
  | nil => simp [matrixBits]
  | cons row rest ih =>
      have hfirst := hrows row (by simp)
      have htail : ∀ q ∈ rest,
          q.intercept.natAbs ≤ M ∧
          ∀ key, (q.coeff key).natAbs ≤ M := by
        intro q hq
        exact hrows q (by simp [hq])
      have hrest := ih htail
      have hrow := rowBits_le row M hfirst.1 hfirst.2
      calc
        matrixBits (row :: rest) = rowBits row + matrixBits rest := rfl
        _ ≤ (Fintype.card { k : Nat // k ∈ keys } + 1) * (M + 2) +
            rest.length * (Fintype.card { k : Nat // k ∈ keys } + 1) *
              (M + 2) := Nat.add_le_add hrow hrest
        _ = (row :: rest).length *
            (Fintype.card { k : Nat // k ∈ keys } + 1) * (M + 2) := by
          simp only [List.length_cons]
          ring

def lowerRow {keys : Finset Nat} (key : { k : Nat // k ∈ keys })
    (lo : Nat → Nat) : AffineExpr keys where
  intercept := -(lo key.val : ℤ)
  coeff := fun j => if j = key then 1 else 0

def upperRow {keys : Finset Nat} (key : { k : Nat // k ∈ keys })
    (hi : Nat → Nat) : AffineExpr keys where
  intercept := hi key.val
  coeff := fun j => if j = key then -1 else 0

def boundRows {keys : Finset Nat} (lo hi : Nat → Nat) :
    List { k : Nat // k ∈ keys } → List (AffineExpr keys)
  | [] => []
  | key :: rest => lowerRow key lo :: upperRow key hi :: boundRows lo hi rest

theorem boundRows_length {keys : Finset Nat} (lo hi : Nat → Nat)
    (ks : List { k : Nat // k ∈ keys }) :
    (boundRows lo hi ks).length = 2 * ks.length := by
  induction ks with
  | nil => rfl
  | cons key rest ih =>
      simp only [boundRows, List.length_cons, ih]
      omega

noncomputable def systemRows (labels : List Label) (x z : ℤ)
    (c lo hi : Nat → Nat) (price : Nat → Nat) (N T : Nat) :
    List (AffineExpr (usedArities labels)) :=
  let terminal := terminalRow labels x z
  [terminal, scaleExpr (-1) terminal] ++
    contractionRoot labels x ++
    [budgetRow labels x z c price N T] ++
    boundRows lo hi (Finset.univ.toList : List (Variable labels))

theorem systemRows_length (labels : List Label) (x z : ℤ)
    (c lo hi : Nat → Nat) (price : Nat → Nat) (N T : Nat) :
    (systemRows labels x z c lo hi price N T).length =
      2 * Fintype.card (Variable labels) + labels.length + 3 := by
  have hcon := Paper.F7Size.contractionRoot_length labels x
  simp only [systemRows, List.length_append, List.length_cons,
    List.length_nil, Nat.add_zero, hcon, boundRows_length]
  simp
  omega

end Paper.F7Encoding
