import Lean

namespace Shor

/-- A standalone-board choice; it does not select the full order-finding circuit. -/
inductive PrimitiveSynthesis where
  | rossSelinger
  | catalyticB2
  | adaptiveB3
  deriving BEq, DecidableEq

open Lean Elab Term in
/-- Read an optional submitted declaration by its exact environment name, not by namespace
resolution. Only an absent declaration chooses `default`; a private one, or one of another type,
is an error. The one resolver behind every optional opt-in (`submittedDesign`,
`submittedPrimitive`, `submittedFullRunDesign`). -/
def resolveOptional (ty default name : Name) (sourceModule : Option Name := none) : TermElabM Expr := do
  let env ← getEnv
  if (env.setExporting false).contains (mkPrivateNameCore (sourceModule.getD env.mainModule) name) then
    throwError "optional declaration '{name}' must be public; remove 'private' to opt in"
  let some info := env.find? name | return mkConst default
  unless info.levelParams.isEmpty && (← Meta.isDefEq info.type (mkConst ty)) do
    throwError "optional declaration '{name}' must have type {ty}"
  return mkConst name

open Lean Elab Command in
/-- Fail with `why` if the submission declares `name`, public or private. -/
def refuseOptional (name sourceModule : Name) (why : String) : CommandElabM Unit := do
  let env ← getEnv
  if env.contains name || (env.setExporting false).contains (mkPrivateNameCore sourceModule name) then
    throwError "{why}"

/-- Which board a primitive selection is attested on. -/
inductive AttestScope where
  | pp | ptp

def AttestScope.label : AttestScope → String
  | .pp => "pp"
  | .ptp => "ptp"

namespace PrimitiveSynthesis

/-- The document, with the selection attested unless it is the default. -/
def attest (choice : PrimitiveSynthesis) (scope : AttestScope) (out : Lean.Json) : Lean.Json :=
  let label := match choice with
    | .rossSelinger => none
    | .catalyticB2 => some "catalytic-b2"
    | .adaptiveB3 => some "adaptive-b3"
  match label with
  | none => out
  | some backend => out.mergeObj (Lean.Json.mkObj [("submitted_primitive", Lean.Json.mkObj [
      ("schema", Lean.Json.str "forshor.primitive-selection/v1"),
      ("scope", Lean.Json.str scope.label), ("backend", Lean.Json.str backend)])])

end PrimitiveSynthesis
end Shor
