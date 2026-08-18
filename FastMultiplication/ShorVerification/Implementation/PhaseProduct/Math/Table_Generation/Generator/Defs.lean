import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Generator.Spec

open Operations

namespace Table_Generation

def streamPoint : ℕ -> Point
  | 0 => .int 0
  | 1 => .frac 0
  | 2 => .int 1
  | 3 => .int (-1)
  | n + 4 =>
      let e := 1 + n / 4
      match n % 4 with
      | 0 => .int (2 ^ e)
      | 1 => .int (-(2 ^ e))
      | 2 => .frac (2 ^ e)
      | _ => .frac (-(2 ^ e))

def generatedPoints (mode : ProductMode) (k : ℕ) : List Point :=
  (List.range (mode.pointCount k)).map streamPoint

def generatePointsInOrder (mode : ProductMode) (k : ℕ) (_ : k ≥ 2) : List Point :=
  generatedPoints mode k

def generate (mode : ProductMode) (k : ℕ) (hk : k ≥ 2) : Prog k :=
  genOpsWithProduct (k := k) (by omega) (generatePointsInOrder mode k hk)

end Table_Generation
