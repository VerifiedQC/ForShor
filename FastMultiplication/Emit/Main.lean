import FastMultiplication.Emit.Lower.Shor
import FastMultiplication.Emit.Symbolic.Bundle
import FastMultiplication.Emit.Json.PlanJson
import FastMultiplication.Emit.Lower.Decide
import FastMultiplication.Emit.Lower.PhaseProduct
import FastMultiplication.Emit.Lower.Qft
import FastMultiplication.Emit.Lower.Instantiate

/-!
# `forshor_emit` executable

Dispatch only (per `Emit/README.md`'s Phase 0): `shor` prints the reference
lowered Shor circuit (`Lower/Shor.lean`); `bundle` prints the n-free
`forshor.emit/v1` symbolic document (`Symbolic/Bundle.lean`). The bare
`<k> <a> <N> <m>` form (no subcommand) is kept as an alias of `shor`, for
compatibility with earlier use of this executable.
-/

def usageText : String :=
  "usage: forshor_emit shor <k> <a> <N> <m>\n" ++
  "       forshor_emit <k> <a> <N> <m>   (alias of shor)\n" ++
  "       forshor_emit bundle <k> [--table standard|generate] [--m-max M] " ++
  "[--w-max W] [--check-cramer]\n" ++
  "       forshor_emit <schedule|coeff_poly|width|qft_plan|shor_plan|" ++
  "recursion|template> <k> [--table standard|generate] [--m-max M] " ++
  "[--w-max W] [--check-cramer]\n" ++
  "       forshor_emit phases <k> <m> <phiNum/phiDen>\n" ++
  "       forshor_emit pp <k> <n> <phiNum/phiDen> [--flat]\n" ++
  "       forshor_emit cpp <k> <n> <phiNum/phiDen> [--flat]\n" ++
  "       forshor_emit qft <k> <w> [--flat]\n" ++
  "  k : number of PhaseProduct synthesis registers (k > 1)\n" ++
  "  a : base, with 0 < a < N and gcd a N = 1\n" ++
  "  N : modulus\n" ++
  "  m : approximation level (a natural number; also the E2 chunk width for " ++
  "phases)\n" ++
  "  n, w : operand/register width (a natural number)\n" ++
  "  phiNum/phiDen : the phase product's angle, as an integer ratio (den " ++
  "defaults to 1 if omitted)\n" ++
  "  --flat : print the flat forshor.lowgate/v2 circuit instead of the " ++
  "default annotated forshor.plan/v1 view\n"

/-- `"n"`, `"n/d"` → `(num, den)`; `d` defaults to `1`. -/
def parsePhi (s : String) : Option (ℤ × ℤ) :=
  match s.splitOn "/" with
  | [numStr] => numStr.toInt?.map (·, 1)
  | [numStr, denStr] =>
      match numStr.toInt?, denStr.toInt? with
      | some n, some d => some (n, d)
      | _, _ => none
  | _ => none

structure BundleArgs where
  k : ℕ
  src : Shor.TableSource := .standard
  mMax : ℕ := 16
  wMax : ℕ := 32
  checkCramer : Bool := false

def parseFlags : List String → BundleArgs → Option BundleArgs
  | [], acc => some acc
  | "--table" :: "standard" :: rest, acc => parseFlags rest { acc with src := .standard }
  | "--table" :: "generate" :: rest, acc => parseFlags rest { acc with src := .generate }
  | "--m-max" :: mStr :: rest, acc =>
      match mStr.toNat? with
      | some m => parseFlags rest { acc with mMax := m }
      | none => none
  | "--w-max" :: wStr :: rest, acc =>
      match wStr.toNat? with
      | some w => parseFlags rest { acc with wMax := w }
      | none => none
  | "--check-cramer" :: rest, acc => parseFlags rest { acc with checkCramer := true }
  | _, _ => none

def parseBundleArgs : List String → Option BundleArgs
  | [] => none
  | kStr :: rest =>
      match kStr.toNat? with
      | none => none
      | some k => parseFlags rest { k := k }

def runBundle (a : BundleArgs) : IO UInt32 := do
  if hk : 1 < a.k then
    match Shor.buildBundle a.src a.k hk a.mMax a.wMax a.checkCramer with
    | .ok json =>
        IO.println json.compress
        return 0
    | .error e =>
        IO.eprintln s!"error: {e}"
        return 3
  else
    IO.eprintln s!"error: need k > 1 (k = {a.k})"
    return 2

def parseSectionArgs : List String → Option BundleArgs
  | [] => none
  | kStr :: rest =>
      match kStr.toNat? with
      | none => none
      | some k => parseFlags rest { k := k }

def runSection (sectionName : String) (args : List String) : IO UInt32 :=
  match parseSectionArgs args with
  | none => do
      IO.eprintln "error: bad arguments"
      IO.eprint usageText
      return 2
  | some ba =>
      if hk : 1 < ba.k then do
        match Shor.buildSection sectionName ba.src ba.k hk ba.mMax ba.wMax ba.checkCramer with
        | .ok json =>
            IO.println json.compress
            return 0
        | .error e =>
            IO.eprintln s!"error: {e}"
            return 3
      else do
        IO.eprintln s!"error: need k > 1 (k = {ba.k})"
        return 2

def runPhases (kStr mStr phiStr : String) : IO UInt32 :=
  match kStr.toNat?, mStr.toNat?, parsePhi phiStr with
  | some k, some m, some (num, den) =>
      match Shor.buildPhases k m num den with
      | .ok lines => do
          for line in lines do
            IO.println line
          return 0
      | .error e => do
          IO.eprintln s!"error: {e}"
          return 3
  | _, _, _ => do
      IO.eprintln "error: k, m must be natural numbers and phi must be an integer ratio num/den"
      IO.eprint usageText
      return 2

def runShorArgs (kStr aStr NStr mStr : String) : IO UInt32 :=
  match kStr.toNat?, aStr.toNat?, NStr.toNat?, mStr.toNat? with
  | some k, some a, some N, some m => Emit.Lower.Shor.runEmit k a N m
  | _, _, _, _ => do
      IO.eprintln "error: k, a, N, m must all be natural numbers"
      IO.eprint usageText
      return 2

/-- Shared driver for `pp`/`cpp`/`qft`: parse `<k> <n-or-w> [<phi>] [--flat]`,
run the builder, print or report the `Except`. `buildFn`'s `annotated` flag
is `!flat`. -/
def runPPQFT (build : ℕ → ℕ → Bool → Except String Lean.Json) (kStr wStr : String)
    (flat : Bool) : IO UInt32 :=
  match kStr.toNat?, wStr.toNat? with
  | some k, some w =>
      if k ≤ 1 then do
        IO.eprintln s!"error: need k > 1 (k = {k})"
        return 2
      else
      match build k w (!flat) with
      | .ok json => do
          IO.println json.compress
          return 0
      | .error e => do
          IO.eprintln s!"error: {e}"
          return 3
  | _, _ => do
      IO.eprintln "error: k, n/w must be natural numbers"
      IO.eprint usageText
      return 2

def runPP (isCtrl : Bool) (kStr nStr phiStr : String) (flat : Bool) : IO UInt32 :=
  match parsePhi phiStr with
  | none => do
      IO.eprintln "error: phi must be an integer ratio num/den"
      IO.eprint usageText
      return 2
  | some (num, den) =>
      runPPQFT (fun k n annotated =>
        if isCtrl then Shor.buildCPP k n num den annotated else Shor.buildPP k n num den annotated)
        kStr nStr flat

def main (args : List String) : IO UInt32 := do
  match args with
  | "shor" :: kStr :: aStr :: NStr :: mStr :: [] => runShorArgs kStr aStr NStr mStr
  | "bundle" :: rest =>
      match parseBundleArgs rest with
      | some ba => runBundle ba
      | none =>
          IO.eprintln "error: bad bundle arguments"
          IO.eprint usageText
          return 2
  | "pp" :: kStr :: nStr :: phiStr :: rest => runPP false kStr nStr phiStr (rest.contains "--flat")
  | "cpp" :: kStr :: nStr :: phiStr :: rest => runPP true kStr nStr phiStr (rest.contains "--flat")
  | "qft" :: kStr :: wStr :: rest =>
      runPPQFT Shor.buildQFT kStr wStr (rest.contains "--flat")
  | "phases" :: kStr :: mStr :: phiStr :: [] => runPhases kStr mStr phiStr
  | sectionName :: rest =>
      if Shor.sectionNames.contains sectionName then
        runSection sectionName rest
      else
        match args with
        | [kStr, aStr, NStr, mStr] => runShorArgs kStr aStr NStr mStr
        | _ => do
            IO.eprint usageText
            return 2
  | [] =>
      IO.eprint usageText
      return 2
