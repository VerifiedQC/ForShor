import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Statement

/-!
# Statement closure check

The ForShor layout rule: a folder's `Statement.lean` states its claims using only `Mathlib`/core,
`Framework/` and other `Statement.lean` files; every lemma lives in `Proofs/`, and `Main.lean`
proves the claims. This script checks the rule semantically rather than by reading imports:
it computes every constant reachable from the claims (unfolding definitions, entering the types
of theorems) and fails if any of them lives in a module outside the allowlist, so a definition
that quietly depends on a `Proofs/` lemma cannot pass.

Run from the project root:

    lake env lean scripts/StatementClosure.lean

It exits non-zero and names the offending constants on a violation. To check another folder,
edit `claimRoots` and `statementModule`.
-/

open Lean Meta Elab Command

/-- The claims of the folder being checked. -/
def claimRoots : List Name := [
  `Shor.PTP.PTPLowerExactCorrect, `Shor.PTP.PTPExactCensus,
  `Shor.PTP.PTPCtlLowerExactCorrect, `Shor.PTP.PTPCtlExactCensus,
  `Shor.PTP.PTPPadLowerExactCorrect, `Shor.PTP.PTPPadExactCensus,
  `Shor.PTP.PTPGateTotalBound, `Shor.PTP.PTPCircuitGateCountBound,
  `Shor.PTP.PTPQubitsTight, `Shor.PTP.PTPQubitsTightExact, `Shor.PTP.PTPQubitsLePtpQubits,
  `Shor.PTP.PTPPeakQubits, `Shor.PTP.PTPPeakQubitsExact, `Shor.PTP.PTPPeakQubitsScan,
  `Shor.PTP.PTPPeakLePtpQubitsAdd,
  `Shor.PTP.PTPChainContractsTightIffReach]

/-- The `Statement` module whose claims these are. -/
def statementModule : String :=
  "ForShor.ShorVerification.Implementation.PhaseTripleProduct.Statement"

/-- Module prefixes a claim may depend on: core, Mathlib and its dependencies, and `Framework/`. -/
def allowedPrefixes : List String :=
  ["Init", "Std", "Lean", "Mathlib", "Batteries", "Aesop", "Qq", "Plausible", "ImportGraph",
   "LeanSearchClient", "ProofWidgets", "Cli",
   "ForShor.ShorVerification.Framework"]

/-- Another folder's `Statement.lean` is allowed; nothing else under `Implementation/` is. -/
def moduleAllowed (m : String) : Bool :=
  m == statementModule ||
  allowedPrefixes.any (fun p => m == p || m.startsWith (p ++ ".")) ||
  (m.startsWith "ForShor.ShorVerification.Implementation." && m.endsWith ".Statement")

/-- Constants reachable from `roots`: a definition is unfolded (type and value), an inductive
contributes its constructors, a theorem contributes only its type. -/
def reachable (roots : List Name) : CoreM (Std.HashMap Name String) := do
  let env ← getEnv
  let mut seen : Std.HashMap Name String := {}
  let mut todo := roots
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail
    if seen.contains n then continue
    match env.find? n with
    | none => continue
    | some ci =>
      let kind := match ci with
        | .defnInfo _ => "def" | .thmInfo _ => "thm" | .inductInfo _ => "ind" | .ctorInfo _ => "ctor"
        | .recInfo _ => "rec" | .axiomInfo _ => "axiom" | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot"
      seen := seen.insert n kind
      let mut used := ci.type.getUsedConstants
      match ci with
      | .defnInfo d => used := used ++ d.value.getUsedConstants
      | .inductInfo i => used := used ++ i.ctors.toArray
      | .ctorInfo c => used := used.push c.induct
      | _ => pure ()
      todo := todo ++ used.toList
  return seen

run_cmd do
  let env ← getEnv
  for r in claimRoots do
    unless env.contains r do throwError "claim {r} does not exist in {statementModule}"
  let seen ← liftCoreM (reachable claimRoots)
  let mut byMod : Std.HashMap String (Array (Name × String)) := {}
  for (n, k) in seen.toList do
    let some idx := env.getModuleIdxFor? n | throwError "constant {n} has no module"
    let m := (env.header.moduleNames[idx.toNat]!).toString
    byMod := byMod.insert m ((byMod.getD m #[]).push (n, k))
  let mods := byMod.toList.toArray.qsort (fun a b => a.1 < b.1)
  logInfo m!"claims checked: {claimRoots.length}; constants reached: {seen.size}; modules: {mods.size}"
  let mut bad : Array (String × Name × String) := #[]
  -- Mathlib and core are summarised; every ForShor module (and any violation) is listed.
  let mut libMods : Nat := 0
  let mut libConsts : Nat := 0
  for (m, xs) in mods do
    let ok := moduleAllowed m
    let isLib := !(m.startsWith "ForShor")
    if ok && isLib then
      libMods := libMods + 1
      libConsts := libConsts + xs.size
    else
      let thms := (xs.filter (fun (_, k) => k == "thm")).size
      logInfo m!"  {if ok then "ok " else "BAD"} {m}: {xs.size} constants ({thms} theorems)"
    unless ok do
      for (n, k) in xs do bad := bad.push (m, n, k)
  logInfo m!"  ok  Mathlib and core (Init, Std, Batteries, Mathlib, ...): {libConsts} constants in {libMods} modules"
  unless bad.isEmpty do
    let lines := bad.toList.map (fun (m, n, k) => m!"  {n} ({k}) in {m}")
    throwError "Statement closure violates the layout rule: {bad.size} constant(s) outside Framework/Statement/Mathlib:\n{MessageData.joinSep lines "\n"}"
  logInfo m!"statement closure OK: every constant the claims reach lives in Mathlib/core, Framework/, or a Statement.lean"
