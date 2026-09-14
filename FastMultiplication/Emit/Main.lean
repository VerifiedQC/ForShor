import FastMultiplication.ShorVerification.Implementation.Reference.StandardLoweringSetup
import FastMultiplication.ShorVerification.Implementation.Reference.ReferenceShorImplementation
import FastMultiplication.Emit.LowGateJson

/-!
# `forshor_emit` executable

Prints the reference lowered Shor circuit for `(k, a, N, m)` as JSON on
stdout (`Shor.emitProgram`'s `forshor.lowgate/v2` schema). Use the compiled
binary (`lake exe forshor_emit ...`) for anything beyond tiny instances:
`#eval` in the editor runs interpreted and can hit stack limits on deep
`seq` chains.
-/

def usageText : String :=
  "usage: forshor_emit <k> <a> <N> <m>\n" ++
  "  k : number of PhaseProduct synthesis registers (k > 1)\n" ++
  "  a : base, with 0 < a < N and gcd a N = 1\n" ++
  "  N : modulus\n" ++
  "  m : approximation level (a natural number)\n"

def runEmit (k a N m : ℕ) : IO UInt32 := do
  if hk : 1 < k then
    if hrange : 0 < a ∧ a < N then
      if hcop : Nat.gcd a N = 1 then
        let lowering := Shor.standardLoweringSetup k hk
        let inst : Shor.ShorOrderFindingInstance := ⟨a, N, hrange, hcop⟩
        let prog := Shor.Reference.referenceProgramAt lowering m inst
        let metaJson : Lean.Json :=
          Lean.Json.mkObj [
            ("k", (k : Lean.Json)),
            ("a", (a : Lean.Json)),
            ("N", (N : Lean.Json)),
            ("m", (m : Lean.Json)),
            ("source", Lean.Json.str "Shor.Reference.referenceProgramAt")
          ]
        IO.println (Shor.emitProgram prog metaJson).compress
        return 0
      else
        IO.eprintln s!"error: need gcd a N = 1 (a = {a}, N = {N})"
        return 2
    else
      IO.eprintln s!"error: need 0 < a < N (a = {a}, N = {N})"
      return 2
  else
    IO.eprintln s!"error: need k > 1 (k = {k})"
    return 2

def main (args : List String) : IO UInt32 := do
  match args with
  | [kStr, aStr, NStr, mStr] =>
      match kStr.toNat?, aStr.toNat?, NStr.toNat?, mStr.toNat? with
      | some k, some a, some N, some m => runEmit k a N m
      | _, _, _, _ =>
          IO.eprintln "error: k, a, N, m must all be natural numbers"
          IO.eprint usageText
          return 2
  | _ =>
      IO.eprint usageText
      return 2
