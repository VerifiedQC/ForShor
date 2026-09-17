import FastMultiplication.ShorVerification.Implementation.Reference.StandardLoweringSetup
import FastMultiplication.ShorVerification.Implementation.Reference.ReferenceShorImplementation
import FastMultiplication.Emit.Json.LowGateJson
import FastMultiplication.Emit.Symbolic.Bundle
import FastMultiplication.Emit.Lower.PhaseProduct
import FastMultiplication.Emit.Lower.Qft
import FastMultiplication.Emit.Reflect.Driver
import FastMultiplication.Emit.IR.Instantiate
import FastMultiplication.Emit.IR.WellFormed

/-!
# Emitter acceptance tests

Small-`N` sanity checks for the JSON printer. These are acceptance tests, not
part of the verified core: nothing here is imported by
`Shor.Shor_correct`/`Shor.exists_shorGateCountBound`.
-/

namespace Shor.Emit.Tests

open Lean (Json)

/-- A tiny concrete instance: `a = 2`, `N = 3` (`gcd 2 3 = 1`, `0 < 2 < 3`). -/
def smallLowering : ShorLoweringSetup := standardLoweringSetup 2 (by decide)

def smallInst : ShorOrderFindingInstance := ⟨2, 15, by decide, by decide⟩

def smallProgram : ShorOrderFindingProgram :=
  Reference.referenceProgramAt smallLowering 0 smallInst

def smallJson : Json := emitProgram smallProgram (Json.mkObj [])

-- 1. The emitted document round-trips: the `gate_count` field extracted back
-- out of the JSON agrees with the value computed directly on the circuit.
example :
    ((smallJson.getObjVal? "gate_count").bind Json.getNat?).toOption
      =
    some (LowGate.gateCount shorGateCostModel smallProgram.circuit) := by
  native_decide

-- 1b. The document declares the expected schema.
example :
    ((smallJson.getObjVal? "schema").bind Json.getStr?).toOption = some "forshor.lowgate/v2" := by
  native_decide

/-- 2. Every `Angle` has a positive denominator (structural: `ℚ`'s invariant). -/
example (a : Angle) : 0 < a.den := a.pos

/-- 2b. Every register's physical qubit list is duplicate-free (structural:
`Reg`'s own `nodup` field, carried by construction). -/
example (r : Reg) : r.qubits.Nodup := r.nodup

/-- 3. The final submitted program is the reference program at the chosen
precision — documents that `standardLoweringSetup`/`referenceProgramAt` (what
the emitter calls) matches what `referenceShorImplementation` actually
submits. -/
example (lowering : ShorLoweringSetup) (inst : ShorOrderFindingInstance) :
    Reference.referenceSubmittedProgram lowering inst
      =
    Reference.referenceProgramAt lowering (Reference.referenceChosenPrecision inst.N) inst :=
  rfl

/-- 4. Exercise the `k = 3` (`q k = 5`) interpolation-coefficient path. -/
def k3Lowering : ShorLoweringSetup := standardLoweringSetup 3 (by decide)

def k3Program : ShorOrderFindingProgram :=
  Reference.referenceProgramAt k3Lowering 0 smallInst

example : 0 < LowGate.gateCount shorGateCostModel k3Program.circuit := by native_decide

#eval LowGate.gateCount shorGateCostModel k3Program.circuit

-- 5. `emitProgram`'s new `resources`/`max_qubit_index` fields round-trip.
example :
    ((smallJson.getObjVal? "max_qubit_index").bind Json.getNat?).toOption
      = some (((LowGate.usedQubits smallProgram.circuit).sup id : ℕ)) := by
  native_decide

example : (smallJson.getObjVal? "resources").toOption.isSome := by native_decide

-- 6. `checkTable .generate` succeeds for `k = 2, 3` (the precomputed tables),
-- using `generatePointsInOrder`'s own consumption order.
example :
    (match checkTable .generate 2 (by decide) (tableInstance .generate 2 (by decide)) with
      | .ok _ => true
      | .error _ => false) = true := by
  native_decide

example :
    (match checkTable .generate 3 (by decide) (tableInstance .generate 3 (by decide)) with
      | .ok _ => true
      | .error _ => false) = true := by
  native_decide

-- 7. `check1_inverseOf`/`check2_agreesWithCramer` succeed for `k = 2, 3` at a
-- small `mMax`, on the standard table (Gauss-Jordan `M⁻¹` agrees with the
-- compiler's own `cramerCoeffFromPtsWidth`).
def k2StdInst : TableInstance 2 := tableInstance .standard 2 (by decide)
def k3StdInst : TableInstance 3 := tableInstance .standard 3 (by decide)

example :
    (match coeffInverse 2 k2StdInst.points k2StdInst.hlen with
      | some inv => check1_inverseOf (coeffMatrix 2 k2StdInst.points k2StdInst.hlen) inv
      | none => false) = true := by
  native_decide

example :
    (match coeffInverse 3 k3StdInst.points k3StdInst.hlen with
      | some inv => check1_inverseOf (coeffMatrix 3 k3StdInst.points k3StdInst.hlen) inv
      | none => false) = true := by
  native_decide

example :
    (match coeffInverse 2 k2StdInst.points k2StdInst.hlen with
      | some inv => check2_agreesWithCramer inv 2 k2StdInst.points k2StdInst.hlen 6
      | none => false) = true := by
  native_decide

-- 8. The `bundle` document has `schema = "forshor.emit/v1"` and `n_free = true`.
example :
    (match buildBundle .standard 2 (by decide) 6 10 false with
      | .ok json =>
          decide (((json.getObjVal? "schema").bind Json.getStr?).toOption = some "forshor.emit/v1") &&
          decide (((json.getObjVal? "n_free").bind Json.getBool?).toOption = some true)
      | .error _ => false) = true := by
  native_decide

-- 9. The E7 phase-product template has one `PhaseProduct` leaf per
-- interpolation point (`q k` of them), for `k = 2, 3` on the standard table.
def countPhaseProductLeaves (bodyJson : Json) : ℕ :=
  match bodyJson.getArr? with
  | .error _ => 0
  | .ok a =>
      (a.toList.filter fun o =>
        decide (((o.getObjVal? "op").bind Json.getStr?).toOption = some "PhaseProduct") ||
        decide (((o.getObjVal? "op").bind Json.getStr?).toOption = some "CPhaseProduct")).length

example :
    countPhaseProductLeaves ((phaseProductTemplateJson k2StdInst.ops false).getObjValD "body")
      = q 2 := by
  native_decide

example :
    countPhaseProductLeaves ((phaseProductTemplateJson k3StdInst.ops false).getObjValD "body")
      = q 3 := by
  native_decide

-- 10. The bundle document carries a `template` section with all four parts.
example :
    (match buildBundle .standard 2 (by decide) 6 10 false with
      | .ok json =>
          let t := json.getObjValD "template"
          (t.getObjVal? "phase_product").toOption.isSome &&
          (t.getObjVal? "controlled_phase_product").toOption.isSome &&
          (t.getObjVal? "qft").toOption.isSome &&
          (t.getObjVal? "shor").toOption.isSome
      | .error _ => false) = true := by
  native_decide

-- 11. Phase 2's instantiation checks (annotated = flat, template ≈
-- annotated one level, ladder) all pass for `pp`/`cpp`/`qft` at a width that
-- triggers recursion (`k = 2, n = 16` recurses once; `k = 2, w = 16` splits
-- twice).
def checkField (json : Json) (field : String) : Bool :=
  ((json.getObjValD "meta").getObjValD "checks").getObjValD field == Json.bool true

example :
    (match buildPP 2 16 1 8 true with
      | .ok json =>
          checkField json "annotated_eq_flat" && checkField json "ladder" &&
            checkField json "template_match"
      | .error _ => false) = true := by
  native_decide

example :
    (match buildCPP 2 16 1 8 true with
      | .ok json => checkField json "annotated_eq_flat" && checkField json "template_match"
      | .error _ => false) = true := by
  native_decide

example :
    (match buildQFT 2 16 true with
      | .ok json => checkField json "annotated_eq_flat" && checkField json "split"
      | .error _ => false) = true := by
  native_decide

-- 12. `#guard` anchors for the `k = 2, 3` width ladders and leaf counts
-- (E6, `Symbolic/Recursion.lean`), read off the built binary once and pinned.
#guard widthLadder k2StdInst.ops 16 = [16, 13, 12, 11]
#guard widthLadder k2StdInst.ops 32 = [32, 21, 16, 13, 12, 11]
#guard widthLadder k3StdInst.ops 24 = [24]
#guard (recursionLevels k2StdInst.ops 16).map (·.leafMultiplicity) = [1, 3, 9, 27]
#guard (recursionLevels k3StdInst.ops 24).map (·.leafMultiplicity) = [1]

-- 13. Every named section (`sectionNames`) is buildable standalone and
-- carries its own name as a top-level key, for `k = 2`.
example :
    sectionNames.all (fun s =>
      match buildSection s .standard 2 (by decide) 6 10 false with
      | .ok json => (json.getObjVal? s).toOption.isSome
      | .error _ => false) = true := by
  native_decide

-- 14. `phases` prints exactly `q k` lines for `k = 2, 3`.
example : (buildPhases 2 8 1 8).toOption.map List.length = some (q 2) := by native_decide
example : (buildPhases 3 8 1 8).toOption.map List.length = some (q 3) := by native_decide

-- 15. R2.1's exit criterion (`Emit/PLAN.md` §6, §6.1): `pp_body`, extracted
-- by reflection (`extract_ir_doc`, pinning a `Doc` at build time) and
-- `instantiateGate`'d at a concrete `k = 2`, standard table, `x`/`z` both
-- width 4 with enough reserve that `targetSignedLayoutState`'s growth to
-- `commonNeededWidth (scanNeededWidths x z ops) = 7` is not truncated,
-- agrees with `compileOpsToSignedGate` itself — flattened first (raw `Gate`
-- `BEq` compares tree shape, and `Gate.seq` bracketing differs harmlessly
-- between the two sides; same convention as `check1_annotatedEqFlat`).
section R2_1

deriving instance BEq for Shor.Gate

extract_ir_doc pp_body_doc_k2 2

abbrev r2_1_k : Nat := 2
def r2_1_hk : 1 < r2_1_k := by decide
def r2_1_ops := (tableInstance .standard r2_1_k r2_1_hk).ops

def r2_1_x : ExtReg := ExtReg.withReserve (Reg.interval 0 4) (Reg.interval 4 12) (by decide)
def r2_1_z : ExtReg := ExtReg.withReserve (Reg.interval 16 4) (Reg.interval 20 12) (by decide)

def r2_1_xBudget : ReserveBudget r2_1_x r2_1_k :=
  ReserveBudget.ofRequirements (by decide) (fun _ => 5) (by decide)

def r2_1_zBudget : ReserveBudget r2_1_z r2_1_k :=
  ReserveBudget.ofRequirements (by decide) (fun _ => 5) (by decide)

def r2_1_xSplit : PhaseSplitLayout r2_1_x r2_1_k (phaseLimbWidth r2_1_x r2_1_z r2_1_k) :=
  PhaseSplitLayout.ofBudget r2_1_x r2_1_k (phaseLimbWidth r2_1_x r2_1_z r2_1_k)
    (phaseLimbWidth_valid_left r2_1_x r2_1_z (by decide)) r2_1_xBudget

def r2_1_zSplit : PhaseSplitLayout r2_1_z r2_1_k (phaseLimbWidth r2_1_x r2_1_z r2_1_k) :=
  PhaseSplitLayout.ofBudget r2_1_z r2_1_k (phaseLimbWidth r2_1_x r2_1_z r2_1_k)
    (phaseLimbWidth_valid_right r2_1_x r2_1_z (by decide)) r2_1_zBudget

def r2_1_layout : Gate.PhaseProductLayout r2_1_x r2_1_z r2_1_k :=
  { xSplit := r2_1_xSplit, zSplit := r2_1_zSplit, cross_owned_disjoint := by decide }

def r2_1_m : Nat := phaseLimbWidth r2_1_x r2_1_z r2_1_k

def r2_1_coeffFn : Fin (q r2_1_k) → ℚ :=
  cramerCoeffFromPtsWidth r2_1_k r2_1_m (tableInstance .standard r2_1_k r2_1_hk).points
    (tableInstance .standard r2_1_k r2_1_hk).hlen

def r2_1_phi : Angle := (1 : ℚ) / 4

def r2_1_real : Gate :=
  compileOpsToSignedGate r2_1_k r2_1_hk r2_1_phi r2_1_x r2_1_z r2_1_layout r2_1_coeffFn r2_1_ops

def r2_1_env : IR.Env :=
  { w := fun n =>
      if n == "xw" then some r2_1_x.width
      else if n == "zw" then some r2_1_z.width
      else none
    a := fun n => if n == "phi" then some r2_1_phi else none
    r := fun n =>
      if n == "x" then some r2_1_x
      else if n == "z" then some r2_1_z
      else if n == "x0R" then some (ExtReg.ofReg (r2_1_xBudget.childReserve 0))
      else if n == "x1R" then some (ExtReg.ofReg (r2_1_xBudget.childReserve 1))
      else if n == "z0R" then some (ExtReg.ofReg (r2_1_zBudget.childReserve 0))
      else if n == "z1R" then some (ExtReg.ofReg (r2_1_zBudget.childReserve 1))
      else none
    opaqueW := fun name args =>
      if name == "nextWidth" then
        match args with
        | [xw, zw] => some (RecursivePhaseWorkspace.nextWidth r2_1_ops xw zw)
        | _ => none
      else none
    coeff := fun l m =>
      if m == r2_1_m then
        if h : l < q r2_1_k then some (r2_1_coeffFn ⟨l, h⟩) else none
      else none }

/-- Flatten nested `Gate.seq`, dropping `Gate.id` — the `Gate` analogue of
`LowGate.flattenSeq`. -/
partial def r2_1_flatten : Gate → List Gate
  | .id => []
  | .seq a b => r2_1_flatten a ++ r2_1_flatten b
  | g => [g]

example :
    ((match IR.instantiateGate pp_body_doc_k2 "pp_body" r2_1_env 10 with
      | .ok g => r2_1_flatten g
      | .error _ => [])
      == r2_1_flatten r2_1_real) = true := by
  native_decide

end R2_1

-- 16. R2.3's exit criterion (`Emit/PLAN.md` §6, §6.2): `naive_leaf`
-- (`LowGate.Naive_SignedPhaseProd`) needs no `k`/`TableSource` and so no
-- `extract_ir_doc` pinning either — `Reflect/Targets.lean`'s
-- `naiveLeafTemplate` is already a plain `def`, hand-specified rather than
-- reflected (`naiveSignedPhaseGates`'s double loop is recursion over a
-- symbolic-length list, which no equation lemma turns into a visible loop
-- the way `.eq_1` does `WellFounded.fix`); what makes it trustworthy is
-- this check, not the hand-transcription. `instantiate` agrees with the
-- real term at six different `(xw, zw)` pairs covering widths 1..6 on both
-- sides.
section R2_3

open Shor.Reflect in
def r2_3_doc : IR.Doc :=
  { templates := [naiveLeafTemplate], opaqueFns := [], entry := "naive_leaf" }

def r2_3_check (xw zw : Nat) : Bool :=
  let x := ExtReg.ofReg (Reg.interval 0 xw)
  let z := ExtReg.ofReg (Reg.interval xw zw)
  let phi : Angle := (3 : ℚ) / 7
  let real := LowGate.Naive_SignedPhaseProd phi x z
  let env : IR.Env :=
    { w := fun n => if n == "xw" then some xw else if n == "zw" then some zw else none
      a := fun n => if n == "phi" then some phi else none
      r := fun n => if n == "x" then some x else if n == "z" then some z else none
      opaqueW := fun _ _ => none, coeff := fun _ _ => none }
  match IR.instantiate r2_3_doc "naive_leaf" env 10 with
  | .ok g => lowGateJson g == lowGateJson real
  | .error _ => false

example : IR.Doc.wellFormed r2_3_doc = true := by native_decide

example :
    [r2_3_check 1 4, r2_3_check 2 3, r2_3_check 3 2, r2_3_check 4 1, r2_3_check 5 6,
      r2_3_check 6 5] = [true, true, true, true, true, true] := by
  native_decide

end R2_3

end Shor.Emit.Tests
