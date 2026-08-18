import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Generator.Spec

open Operations

namespace Table_Generation

def generatedPoints (mode : ProductMode) (k : ℕ) : List Point :=
  match mode, k with
  | .PhaseProduct, _ => []
  | .PhaseTripleProduct, _ => []

def generatePointsInOrder (mode : ProductMode) (k : ℕ) (hk : k ≥ 2) : List Point :=
  match hk with
  | _ => generatedPoints mode k

def generate (mode : ProductMode) (k : ℕ) (hk : k ≥ 2) : Prog k :=
  match mode, hk with
  | .PhaseProduct, _ => []
  | .PhaseTripleProduct, _ => []

end Table_Generation
