import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Generator.Spec

open Operations

namespace Table_Generation

def generatedPoints (mode : ProductMode) (k : ℕ) : List Point :=
  canonicalPoints mode k

def generatePointsInOrder (mode : ProductMode) (k : ℕ) (_hk : k ≥ 2) : List Point :=
  generatedPoints mode k

def generate (mode : ProductMode) (k : ℕ) (hk : k ≥ 2) : Prog k :=
  genOpsWithProduct (k := k) (by omega) (generatePointsInOrder mode k hk)

end Table_Generation
