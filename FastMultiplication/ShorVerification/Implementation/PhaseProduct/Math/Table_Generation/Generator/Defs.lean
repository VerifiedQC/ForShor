import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Generator.Spec

open Operations

namespace Table_Generation

def generatedPoints (mode : ProductMode) (k : ℕ) : List Point :=
  canonicalPoints mode k

def generatePointsInOrder (mode : ProductMode) (k : ℕ) (hk : k ≥ 2) : List Point :=
  match hk with
  | _ => generatedPoints mode k

def targetFirst : Prog 4 :=
  (1 +:= 3 << 0) ;;
  (2 +:= 0 << 0) ;;
  (1 +:= 2 << 0) ;;
  (2 <<s= 1) ;;
  (2 -:= 1 << 0)

def targetAtTwo : Prog 4 :=
  (2 <<s= 2) ;;
  (2 +:= 0 << 0) ;;
  (1 +:= 3 << 2) ;;
  (2 -:= 1 << 1) ;;
  (1 <<s= 2) ;;
  (1 +:= 2 << 0)

def targetAtHalf : Prog 4 :=
  (1 <<s= 2) ;;
  (1 +:= 3 << 0) ;;
  (2 +:= 0 << 2) ;;
  (1 -:= 2 << 1) ;;
  (2 <<s= 2) ;;
  (2 +:= 1 << 0)

def targetAtFour : Prog 4 :=
  (2 <<s= 4) ;;
  (2 +:= 0 << 0) ;;
  (1 +:= 3 << 4) ;;
  (2 -:= 1 << 2) ;;
  (1 <<s= 3) ;;
  (1 +:= 2 << 0)

def targetGenerate : Prog 4 :=
  targetFirst ;;
  [valid_ops.phaseProduct 0, valid_ops.phaseProduct 3,
    valid_ops.phaseProduct 1, valid_ops.phaseProduct 2] ;;
  apply_Op_inverse targetFirst ;;
  targetAtTwo ;;
  [valid_ops.phaseProduct 1, valid_ops.phaseProduct 2] ;;
  apply_Op_inverse targetAtTwo ;;
  targetAtHalf ;;
  [valid_ops.phaseProduct 2, valid_ops.phaseProduct 1] ;;
  apply_Op_inverse targetAtHalf ;;
  targetAtFour ;;
  [valid_ops.phaseProduct 1, valid_ops.phaseProduct 2]

def generate : (mode : ProductMode) → (k : ℕ) → (hk : k ≥ 2) → Prog k
  | .PhaseTripleProduct, 4, _ => targetGenerate
  | mode, k, hk =>
      genOpsWithProduct (by omega) (generatePointsInOrder mode k hk)

end Table_Generation
