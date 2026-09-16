import FastMultiplication.Emit.Json.PlanJson
import FastMultiplication.Emit.Lower.Decide
import FastMultiplication.Emit.Lower.Instantiate
import FastMultiplication.Emit.Table.Source
import FastMultiplication.ShorVerification.Implementation.QFT.Lowering.PlanBuilders

/-!
# `qft`: concrete-width QFT

One register of width `w`, reserve sized by `qftWorkspaceNeed ops w`.
`QFTReserveOK` (and the plain `Disjoint active reserve` needed to build the
`ExtReg` at all) are `Decidable` at this concrete `w` (`Lower/Decide.lean`),
discharged with `if h : … then … else refuse`.
-/

namespace Shor

open Lean (Json)

/-- One register of width `w` with reserve sized by `qftWorkspaceNeed`. -/
def qftRegister {k : ℕ} (ops : Prog k) (w : ℕ) : Except String ExtReg :=
  let need := qftWorkspaceNeed ops w
  let active := Reg.interval 0 w
  let reserve := Reg.interval w (need.1 + need.2)
  if h : Disjoint active reserve then
    .ok (ExtReg.withReserve active reserve h)
  else
    .error "internal: active/reserve overlap"

/-- Build the `qft` document at concrete `k, w`. `annotated` selects the
`PlanJson` view (with instantiation checks embedded, refusing on failure)
over the flat `LowGate` view. -/
def buildQFT (k w : ℕ) (annotated : Bool) : Except String Json :=
  if hk : 1 < k then
    let ops := (tableInstance .standard k hk).ops
    match qftRegister ops w with
    | .error e => .error e
    | .ok r =>
        if hws : QFTReserveOK ops r then
          if annotated then
            let plan := reserveQFTLoweringPlan k hk ops r hws
            let check1 := lowGateJson (lowerQFTPlan plan) == lowGateJson (lowerQFT k hk ops r hws)
            let check3 := check3_qftSplit plan
            let checksJ :=
              Json.mkObj [("annotated_eq_flat", Json.bool check1), ("split", Json.bool check3)]
            let metaJ := Json.mkObj [("k", (k : Json)), ("w", (w : Json)), ("checks", checksJ)]
            if check1 && check3 then
              .ok (emitPlanDoc (qftPlanJsonOf plan) metaJ)
            else
              .error "instantiation check failed"
          else
            let metaJ := Json.mkObj [("k", (k : Json)), ("w", (w : Json))]
            .ok (emitLowGateDoc (lowerQFT k hk ops r hws) metaJ)
        else
          .error s!"insufficient workspace for w={w}"
  else
    .error s!"need k > 1 (k={k})"

end Shor
