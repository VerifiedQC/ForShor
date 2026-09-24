import FastMultiplication.Emit.Json.PlanJson
import FastMultiplication.Emit.Lower.Decide
import FastMultiplication.Emit.Lower.Registers
import FastMultiplication.Emit.Reflect.Verify
import FastMultiplication.Emit.Table.Source
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Lowering.PlanBuilders
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Lowering.Lower

/-!
# `pp`/`cpp`: concrete-width signed (and controlled) phase product

Registers `x = [0, n)`, `z = [n, 2n)`, reserves placed immediately after each
sized by `RecursivePhaseWorkspace.reserveNeed ops n n` plus one bit each.
`SignedRecursiveWorkspaceOK`/`CSignedRecursiveWorkspaceOK`, and the plain
`Disjoint active reserve` needed to build the `ExtReg`s at all, are all
`Decidable` (`Lower/Decide.lean`) at this *concrete* `n`, so every
precondition is discharged with `if h : … then … else refuse` — there is no
abstract proof for general `n` anywhere in this file. The table is always
`standardLoweringSetup k hk` (matching README: the table the lowering
theorems are about); a table of one's own is a build-time path
(`extract_ir_doc`, `Reflect/Driver.lean`), never a CLI flag.

`Emit/PLAN.md` R3/R4: the annotated view's `template_match`/`ladder` checks
(`Symbolic/Template.lean`/`Symbolic/Recursion.lean`, both removed) are
replaced by `instantiate_eq_real` — the extracted `phase_product`/
`cphase_product` template (`Reflect.Verify`), instantiated at *this* `n`,
agreeing with the real compiled term directly. That needs `Reflect.
runExtractAndVerify`'s environment reload, so `buildPP`/`buildCPP` are now
`unsafe`/`IO`. -/

namespace Shor

open Lean (Json)

/-- `{"annotated_eq_flat", "instantiate_eq_real"}` as a JSON object, plus
whether both checks passed. -/
def checksJson (check1 instantiateEqReal : Bool) : Json × Bool :=
  (Json.mkObj [
    ("annotated_eq_flat", Json.bool check1),
    ("instantiate_eq_real", Json.bool instantiateEqReal)
  ], check1 && instantiateEqReal)

/-- Build the `pp` document (uncontrolled) at concrete `k, n, phi = phiNum /
phiDen`. `annotated` selects the `PlanJson` view (with instantiation checks
embedded, refusing on failure) over the flat `LowGate` view. -/
unsafe def buildPP (k n : ℕ) (phiNum phiDen : ℤ) (annotated : Bool) : IO (Except String Json) := do
  if hk : 1 < k then
    let setup := standardLoweringSetup k hk
    let ops := setup.ops
    match ppRegisters ops n with
    | .error e => return .error e
    | .ok (x, z, _ctrl) =>
        if hws : SignedRecursiveWorkspaceOK ops x z then
          let phi : Angle := (phiNum : ℚ) / (phiDen : ℚ)
          if annotated then
            match ← Reflect.runExtractAndVerify k with
            | .error e => return .error e
            | .ok doc =>
                let plan :=
                  standardSignedPhaseLoweringPlan k hk phi x z ops setup.pts setup.hpts hws
                let check1 := check1_annotatedEqFlat (planJson plan) (lowerGateRec plan)
                let instantiateEqReal :=
                  Reflect.phaseProductAgrees hk ops setup.pts setup.hpts doc x z phi hws
                let (checksJ, allOk) := checksJson check1 instantiateEqReal
                let metaJ :=
                  Json.mkObj [
                    ("k", (k : Json)), ("n", (n : Json)), ("phi", angleJson phi), ("checks", checksJ)
                  ]
                if allOk then
                  return .ok (emitPlanDoc (planJson plan) metaJ)
                else
                  return .error "instantiation check failed"
          else
            let metaJ := Json.mkObj [("k", (k : Json)), ("n", (n : Json)), ("phi", angleJson phi)]
            return .ok
              (emitLowGateDoc
                (lowerSignedPhaseProdWithWorkspace k hk phi x z ops setup.pts setup.hpts hws)
                metaJ)
        else
          return .error s!"insufficient workspace for n={n}"
  else
    return .error s!"need k > 1 (k={k})"

/-- Build the `cpp` document (controlled) at concrete `k, n, phi = phiNum /
phiDen`, with the control qubit placed deterministically by `ppRegisters`. -/
unsafe def buildCPP (k n : ℕ) (phiNum phiDen : ℤ) (annotated : Bool) : IO (Except String Json) := do
  if hk : 1 < k then
    let setup := standardLoweringSetup k hk
    let ops := setup.ops
    match ppRegisters ops n with
    | .error e => return .error e
    | .ok (x, z, ctrl) =>
        if hws : CSignedRecursiveWorkspaceOK ops ctrl x z then
          let phi : Angle := (phiNum : ℚ) / (phiDen : ℚ)
          if annotated then
            match ← Reflect.runExtractAndVerify k with
            | .error e => return .error e
            | .ok doc =>
                let plan :=
                  standardCSignedPhaseLoweringPlan k hk ctrl phi x z ops setup.pts setup.hpts hws
                let check1 := check1_annotatedEqFlat (planJson plan) (lowerGateRec plan)
                let instantiateEqReal :=
                  Reflect.cPhaseProductAgrees hk ops setup.pts setup.hpts doc ctrl x z phi hws
                let (checksJ, allOk) := checksJson check1 instantiateEqReal
                let metaJ :=
                  Json.mkObj [
                    ("k", (k : Json)), ("n", (n : Json)), ("ctrl", (ctrl : Json)),
                    ("phi", angleJson phi), ("checks", checksJ)
                  ]
                if allOk then
                  return .ok (emitPlanDoc (planJson plan) metaJ)
                else
                  return .error "instantiation check failed"
          else
            let metaJ :=
              Json.mkObj [
                ("k", (k : Json)), ("n", (n : Json)), ("ctrl", (ctrl : Json)), ("phi", angleJson phi)
              ]
            return .ok
              (emitLowGateDoc
                (lowerCSignedPhaseProdWithWorkspace k hk ctrl phi x z ops setup.pts setup.hpts hws)
                metaJ)
        else
          return .error s!"insufficient workspace for n={n}"
  else
    return .error s!"need k > 1 (k={k})"

end Shor
