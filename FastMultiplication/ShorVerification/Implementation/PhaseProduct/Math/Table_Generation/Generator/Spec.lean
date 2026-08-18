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

def IsSignedPowerOfTwo (z : ℤ) : Prop :=
  ∃ n : ℕ, z = (2 : ℤ) ^ n ∨ z = -((2 : ℤ) ^ n)

def AllowedPoint : Point → Prop
  | .int z => z = 0 ∨ IsSignedPowerOfTwo z
  | .frac z => z = 0 ∨ IsSignedPowerOfTwo z

def ValidPointList (mode : ProductMode) (k : ℕ) (pts : List Point) : Prop :=
  pts.length = ProductMode.pointCount mode k ∧
    ∀ p, p ∈ pts → AllowedPoint p

end Table_Generation
