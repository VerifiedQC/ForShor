import FastMultiplication.Emit.Json.PlanJson
import FastMultiplication.Emit.Lower.Decide
import FastMultiplication.Emit.Lower.Instantiate
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
abstract proof for general `n` anywhere in this file. `standard` is always
the table source here (matching README: the table the lowering theorems are
about).
-/

namespace Shor

open Lean (Json)

/-- Concrete registers for a (controlled) signed phase product at width `n`.
The controlled variant additionally allocates a control qubit past both
registers' full extent (so it is disjoint from both by construction, still
checked decidably below since that's what `CSignedRecursiveWorkspaceOK`
itself demands). -/
def ppRegisters {k : ℕ} (ops : Prog k) (n : ℕ) : Except String (ExtReg × ExtReg × ℕ) :=
  let need := RecursivePhaseWorkspace.reserveNeed ops n n
  let xActive := Reg.interval 0 n
  let xReserve := Reg.interval n (need.1 + 1)
  if hx : Disjoint xActive xReserve then
    let zStart := n + (need.1 + 1)
    let zActive := Reg.interval zStart n
    let zReserve := Reg.interval (zStart + n) (need.2 + 1)
    if hz : Disjoint zActive zReserve then
      let ctrl := zStart + n + (need.2 + 1)
      .ok (ExtReg.withReserve xActive xReserve hx, ExtReg.withReserve zActive zReserve hz, ctrl)
    else
      .error "internal: z active/reserve overlap"
  else
    .error "internal: x active/reserve overlap"

/-- `{"annotated_eq_flat", "template_match", "ladder"}` as a JSON object,
plus whether all present checks passed. `template_match` is `"n/a (base
case)"` when the plan is already at a base case (nothing for check 2 to
compare). -/
def checksJson (check1 : Bool) (check2 : Option Bool) (check3 : Bool) : Json × Bool :=
  let check2Json := match check2 with
    | none => Json.str "n/a (base case)"
    | some b => Json.bool b
  let allOk := check1 && check3 && check2.getD true
  (Json.mkObj [
    ("annotated_eq_flat", Json.bool check1),
    ("template_match", check2Json),
    ("ladder", Json.bool check3)
  ], allOk)

/-- Build the `pp` document (uncontrolled) at concrete `k, n, phi = phiNum /
phiDen`. `annotated` selects the `PlanJson` view (with instantiation checks
embedded, refusing on failure) over the flat `LowGate` view. -/
def buildPP (k n : ℕ) (phiNum phiDen : ℤ) (annotated : Bool) : Except String Json :=
  if hk : 1 < k then
    let ops := (tableInstance .standard k hk).ops
    match ppRegisters ops n with
    | .error e => .error e
    | .ok (x, z, _ctrl) =>
        if hws : SignedRecursiveWorkspaceOK ops x z then
          let phi : Angle := (phiNum : ℚ) / (phiDen : ℚ)
          if annotated then
            let plan := standardSignedPhaseLoweringPlan k hk phi x z ops hws
            let check1 := check1_annotatedEqFlat (planJson plan) (lowerGateRec plan)
            let check3 := check3_ladder plan
            let check2 := check2_signed hk ops phi x z plan
            let (checksJ, allOk) := checksJson check1 check2 check3
            let metaJ :=
              Json.mkObj [
                ("k", (k : Json)), ("n", (n : Json)), ("phi", angleJson phi), ("checks", checksJ)
              ]
            if allOk then
              .ok (emitPlanDoc (planJson plan) metaJ)
            else
              .error "instantiation check failed"
          else
            let metaJ := Json.mkObj [("k", (k : Json)), ("n", (n : Json)), ("phi", angleJson phi)]
            .ok (emitLowGateDoc (lowerSignedPhaseProdWithWorkspace k hk phi x z ops hws) metaJ)
        else
          .error s!"insufficient workspace for n={n}"
  else
    .error s!"need k > 1 (k={k})"

/-- Build the `cpp` document (controlled) at concrete `k, n, phi = phiNum /
phiDen`, with the control qubit placed deterministically by `ppRegisters`. -/
def buildCPP (k n : ℕ) (phiNum phiDen : ℤ) (annotated : Bool) : Except String Json :=
  if hk : 1 < k then
    let ops := (tableInstance .standard k hk).ops
    match ppRegisters ops n with
    | .error e => .error e
    | .ok (x, z, ctrl) =>
        if hws : CSignedRecursiveWorkspaceOK ops ctrl x z then
          let phi : Angle := (phiNum : ℚ) / (phiDen : ℚ)
          if annotated then
            let plan := standardCSignedPhaseLoweringPlan k hk ctrl phi x z ops hws
            let check1 := check1_annotatedEqFlat (planJson plan) (lowerGateRec plan)
            let check3 := check3_ladder plan
            let check2 := check2_csigned hk ops ctrl phi x z plan
            let (checksJ, allOk) := checksJson check1 check2 check3
            let metaJ :=
              Json.mkObj [
                ("k", (k : Json)), ("n", (n : Json)), ("ctrl", (ctrl : Json)),
                ("phi", angleJson phi), ("checks", checksJ)
              ]
            if allOk then
              .ok (emitPlanDoc (planJson plan) metaJ)
            else
              .error "instantiation check failed"
          else
            let metaJ :=
              Json.mkObj [
                ("k", (k : Json)), ("n", (n : Json)), ("ctrl", (ctrl : Json)), ("phi", angleJson phi)
              ]
            .ok
              (emitLowGateDoc (lowerCSignedPhaseProdWithWorkspace k hk ctrl phi x z ops hws) metaJ)
        else
          .error s!"insufficient workspace for n={n}"
  else
    .error s!"need k > 1 (k={k})"

end Shor
