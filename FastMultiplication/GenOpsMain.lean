import FastMultiplication.Synthesis_programs

open Operations

def k : Nat := 3

theorem hk : 0 < k := by decide


def samplePoints : List Point :=
  [Point.int 1,
   Point.int 2,
   Point.int 3,
   Point.inf]

def main : IO Unit := do
  let prog := genOpsWithProduct (k := k) hk samplePoints
  let lines : List String := prog.map (fun op => opToString op)
  let content := String.intercalate "\n" lines
  IO.FS.writeFile "generated_ops.txt" (content ++ "\n")
  IO.println "Wrote generated_ops.txt"
