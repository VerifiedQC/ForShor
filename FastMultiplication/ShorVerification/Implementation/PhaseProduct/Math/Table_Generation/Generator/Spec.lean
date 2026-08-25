import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Builders.Fragments

open Operations

namespace Table_Generation

inductive ProductMode where
  | PhaseProduct
  | PhaseTripleProduct
deriving DecidableEq, Repr

def ProductMode.pointCount : ProductMode → ℕ → ℕ
  | .PhaseProduct, k => 2 * k - 1
  | .PhaseTripleProduct, k => 3 * k - 2

def canonicalPoint : ℕ -> Point
  | 0 => .int 0
  | 1 => .frac 0
  | 2 => .int 1
  | 3 => .int (-1)
  | n + 4 =>
    let e := 1 + (n / 4)
    match n % 4 with
    | 0 => .int (2 ^ e)
    | 1 => .int (- (2 ^ e))
    | 2 => .frac (2 ^ e)
    | _ => .frac (-(2 ^ e))

def canonicalPoints (mode : ProductMode) (k : ℕ) : List Point :=
  (List.range (mode.pointCount k)).map canonicalPoint

def IsSignedPowerOfTwo (z : ℤ) : Prop :=
  ∃ n : ℕ, z = (2 : ℤ) ^ n ∨ z = -((2 : ℤ) ^ n)

def AllowedPoint : Point → Prop
  | .int z => z = 0 ∨ IsSignedPowerOfTwo z
  | .frac z => z = 0 ∨ IsSignedPowerOfTwo z

def ValidPointList (mode : ProductMode) (k : ℕ) (pts : List Point) : Prop :=
  pts = canonicalPoints mode k

def ValidPointOrder (mode : ProductMode) (k : ℕ) (pts : List Point) : Prop :=
  pts.Perm (canonicalPoints mode k)

end Table_Generation
