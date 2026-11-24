import Lean

namespace Shor

/-- A standalone-board choice; it does not select the full order-finding circuit. -/
inductive PrimitiveSynthesis where
  | rossSelinger
  | catalyticB2
  | adaptiveB3
  deriving BEq, DecidableEq

namespace PrimitiveSynthesis

open Lean Elab Term in
def resolve (name sourceModule : Name) : TermElabM Expr := do
  let env ← getEnv
  if (env.setExporting false).contains (mkPrivateNameCore sourceModule name) then
    throwError "optional declaration '{name}' must be public"
  let some info := env.find? name | return mkConst ``PrimitiveSynthesis.rossSelinger
  unless info.levelParams.isEmpty && (← Meta.isDefEq info.type (mkConst ``PrimitiveSynthesis)) do
    throwError "optional declaration '{name}' must have type Shor.PrimitiveSynthesis"
  return mkConst name

def attest (choice : PrimitiveSynthesis) (scope : String) (out : Lean.Json) : Lean.Json :=
  let label := match choice with
    | .rossSelinger => none
    | .catalyticB2 => some "catalytic-b2"
    | .adaptiveB3 => some "adaptive-b3"
  match label with
  | none => out
  | some backend => out.mergeObj (Lean.Json.mkObj [("submitted_primitive", Lean.Json.mkObj [
      ("schema", Lean.Json.str "forshor.primitive-selection/v1"),
      ("scope", Lean.Json.str scope), ("backend", Lean.Json.str backend)])])

end PrimitiveSynthesis
end Shor
