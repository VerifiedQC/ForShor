import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Generator.Defs
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Generator.Metrics

open Operations

namespace Table_Generation

/- Utility functions for inspecting generated point streams and programs -/

def ProductMode.toString : ProductMode → String
  | .PhaseProduct => "phaseProduct"
  | .PhaseTripleProduct => "phaseTripleProduct"

instance : ToString ProductMode :=
  ⟨ProductMode.toString⟩

def pointsToString (pts : List Point) : String :=
  joinComma (pts.map pointToString)

def joinNewline : List String → String
  | [] => ""
  | x :: xs => xs.foldl (fun acc s => acc ++ "\n" ++ s) x

def progToLinesString {k} (p : Prog k) : String :=
  joinNewline (p.map opToString)

def generatedPointsString (mode : ProductMode) (k : ℕ) : String :=
  pointsToString (generatedPoints mode k)

def generatePointsInOrderString (mode : ProductMode) (k : ℕ) (hk : k ≥ 2) : String :=
  pointsToString (generatePointsInOrder mode k hk)

def generateString (mode : ProductMode) (k : ℕ) (hk : k ≥ 2) : String :=
  progToLinesString (generate mode k hk)

def generateMetricsString (mode : ProductMode) (k : ℕ) (hk : k ≥ 2) : String :=
  let p := generate mode k hk
  joinNewline [
    "total operations: " ++ toString p.length,
    "arithmetic operations: " ++ toString (arithmeticOperationCount p),
    "phase product operations: " ++ toString (phaseProductCount p),
    "parallel phase product layers: " ++ toString (parallelPhaseProductLayerCount p)
  ]


def ExampleK := 4
def ExampleProductMode : ProductMode := .PhaseTripleProduct

#eval IO.println (generatePointsInOrderString ExampleProductMode ExampleK (by decide))
#eval IO.println (generateMetricsString ExampleProductMode ExampleK (by decide))
#eval IO.println (generateString ExampleProductMode ExampleK (by decide))

end Table_Generation
