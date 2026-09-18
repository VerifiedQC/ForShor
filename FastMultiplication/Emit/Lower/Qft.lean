import FastMultiplication.Emit.Json.PlanJson
import FastMultiplication.Emit.Lower.Decide
import FastMultiplication.Emit.Lower.Registers
import FastMultiplication.Emit.Reflect.Verify
import FastMultiplication.Emit.Table.Source
import FastMultiplication.ShorVerification.Implementation.QFT.Lowering.PlanBuilders

/-!
# `qft`: concrete-width QFT

One register of width `w`, reserve sized by `qftWorkspaceNeed ops w`.
`QFTReserveOK` (and the plain `Disjoint active reserve` needed to build the
`ExtReg` at all) are `Decidable` at this concrete `w` (`Lower/Decide.lean`),
discharged with `if h : … then … else refuse`.

`Emit/PLAN.md` R3/R4: the `split` check (`Symbolic/Recursion.lean`-adjacent,
now-deleted `Lower/Instantiate.lean`) is replaced by `instantiate_eq_real` —
the extracted `qft` template (`Reflect.Verify`), instantiated at this `w`,
agreeing with the real compiled term directly. -/

namespace Shor

open Lean (Json)

/-- Build the `qft` document at concrete `k, w`. `annotated` selects the
`PlanJson` view (with instantiation checks embedded, refusing on failure)
over the flat `LowGate` view. -/
unsafe def buildQFT (k w : ℕ) (annotated : Bool) : IO (Except String Json) := do
  if hk : 1 < k then
    let ops := (tableInstance .standard k hk).ops
    match qftRegister ops w with
    | .error e => return .error e
    | .ok r =>
        if hws : QFTReserveOK ops r then
          if annotated then
            match ← Reflect.runExtractAndVerify k with
            | .error e => return .error e
            | .ok doc =>
                let plan := reserveQFTLoweringPlan k hk ops r hws
                let check1 := lowGateJson (lowerQFTPlan plan) == lowGateJson (lowerQFT k hk ops r hws)
                let instantiateEqReal := Reflect.qftAgrees hk ops doc r hws
                let checksJ :=
                  Json.mkObj [
                    ("annotated_eq_flat", Json.bool check1),
                    ("instantiate_eq_real", Json.bool instantiateEqReal)
                  ]
                let metaJ := Json.mkObj [("k", (k : Json)), ("w", (w : Json)), ("checks", checksJ)]
                if check1 && instantiateEqReal then
                  return .ok (emitPlanDoc (qftPlanJsonOf plan) metaJ)
                else
                  return .error "instantiation check failed"
          else
            let metaJ := Json.mkObj [("k", (k : Json)), ("w", (w : Json))]
            return .ok (emitLowGateDoc (lowerQFT k hk ops r hws) metaJ)
        else
          return .error s!"insufficient workspace for w={w}"
  else
    return .error s!"need k > 1 (k={k})"

end Shor
