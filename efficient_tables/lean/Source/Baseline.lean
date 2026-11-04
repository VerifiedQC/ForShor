import Source.Spec

/-!
# Baseline table generator

Defines the baseline program generator for a list of points. Builds per-point programs from constant-addition helpers (`addConstFrom`, `computeLocal`, `computeFracLocal`) and assembles them with `opsForPointWithProduct` and `genOpsWithProduct`; `baselineGeneratedPoints` gives the points it handles.
-/

namespace TableGeneration

open Operations

def addConstAuxFuel {k : Nat} (dst src : Fin k) (negSrc : Bool) :
    Nat -> Nat -> Nat -> Prog k
  | 0, _, _ => []
  | fuel + 1, n, shift =>
      match n with
      | 0 => []
      | n' + 1 =>
          let rest := addConstAuxFuel dst src negSrc fuel ((n' + 1) / 2) (shift + 1)
          if (n' + 1) % 2 = 1 then
            valid_ops.addScaled dst src negSrc shift :: rest
          else
            rest

def addConstFrom {k : Nat} (dst src : Fin k) (c : Int) : Prog k :=
  if c = 0 then
    []
  else
    let negSrc := decide (c < 0)
    let n := Int.natAbs c
    addConstAuxFuel dst src negSrc (n + 1) n 0

def nonzeroFins {k : Nat} (hk : 0 < k) : List (Fin k) :=
  (List.finRange k).filter (fun j => decide (j != finZero hk))

def computeLocalAux {k : Nat} (hk : 0 < k) (z : Int) :
    List (Fin k) -> Prog k
  | [] => []
  | j :: js =>
      addConstFrom (finZero hk) j (z ^ j.val) ++ computeLocalAux hk z js

def computeLocal {k : Nat} (hk : 0 < k) (z : Int) : Prog k :=
  computeLocalAux hk z (nonzeroFins hk)

def nonlastFins {k : Nat} (hk : 0 < k) : List (Fin k) :=
  (List.finRange k).filter (fun j => decide (j != finLast hk))

def fracCoeff {k : Nat} (c : Int) (j : Fin k) : Int :=
  c ^ (k - 1 - j.val)

def computeFracLocalAux {k : Nat} (hk : 0 < k) (c : Int) :
    List (Fin k) -> Prog k
  | [] => []
  | j :: js =>
      addConstFrom (finLast hk) j (fracCoeff (k := k) c j) ++
        computeFracLocalAux hk c js

def computeFracLocal {k : Nat} (hk : 0 < k) (c : Int) : Prog k :=
  computeFracLocalAux hk c (nonlastFins hk)

def opsForPointWithProduct {k : Nat} (hk : 0 < k) : Point -> Prog k
  | .int z =>
      let build := computeLocal hk z
      build ++ [valid_ops.phaseProduct (finZero hk)] ++ apply_Op_inverse build
  | .frac c =>
      if c = 0 then
        [valid_ops.phaseProduct (finLast hk)]
      else
        let build := computeFracLocal hk c
        build ++ [valid_ops.phaseProduct (finLast hk)] ++ apply_Op_inverse build

def genOpsWithProduct {k : Nat} (hk : 0 < k) : List Point -> Prog k
  | [] => []
  | pt :: pts => opsForPointWithProduct hk pt ++ genOpsWithProduct hk pts

def baselineGeneratedPoints (mode : ProductMode) (k : Nat) : List Point :=
  canonicalPoints mode k

def baselineGeneratePointsInOrder
    (mode : ProductMode) (k : Nat) (_hk : k >= 2) : List Point :=
  baselineGeneratedPoints mode k

def baselineGenerate : (mode : ProductMode) -> (k : Nat) -> (hk : k >= 2) -> Prog k
  | mode, k, hk =>
      genOpsWithProduct (positive_of_ge_two hk) (baselineGeneratePointsInOrder mode k hk)

end TableGeneration
