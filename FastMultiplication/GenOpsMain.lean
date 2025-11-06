import FastMultiplication.Synthesis_programs

open Operations
/-- Choose k and a proof `0 < k`. Adjust as needed. -/
def k : Nat := 3
theorem hk : 0 < k := by decide

/-- Example list of interpolation points. Adjust as needed. -/
def samplePoints : List Point :=
  [Point.int 1,
   Point.int 2,
   Point.int 3,
   Point.inf]

/-- Main: generate ops and write one operation per line to generated_ops.txt. -/
def main : IO Unit := do
  -- Use your verified generator
  let prog := genOpsWithProduct (k := k) hk samplePoints

  -- Pretty-print each op using the existing opToString
  let lines : List String := prog.map (fun op => opToString op)

  -- Join with newlines
  let content := String.intercalate "\n" lines

  -- Write to txt file
  IO.FS.writeFile "generated_ops.txt" (content ++ "\n")

  -- Optional: small confirmation
  IO.println "Wrote generated_ops.txt"
