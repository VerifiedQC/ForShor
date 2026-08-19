import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Generator.Spec

open Operations

namespace Table_Generation

def generatedPoints (mode : ProductMode) (k : ℕ) : List Point :=
  List.replicate (ProductMode.pointCount mode k) (.int 0)

def generatePointsInOrder (mode : ProductMode) (k : ℕ) (_hk : k ≥ 2) : List Point :=
  generatedPoints mode k

def generate (mode : ProductMode) (k : ℕ) (hk : k ≥ 2) : Prog k :=
  List.replicate (ProductMode.pointCount mode k)
    (valid_ops.phaseProduct (finZero (by omega)))

end Table_Generation
