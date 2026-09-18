import FastMultiplication.ShorVerification.Implementation.Reference.StandardLoweringSetup
import FastMultiplication.ShorVerification.Implementation.Reference.ReferenceShorImplementation
import FastMultiplication.Emit.Json.LowGateJson
import FastMultiplication.Emit.Symbolic.Bundle
import FastMultiplication.Emit.Table.Decide
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
-- `buildBundleCore` (the pure sections only — `template` needs `IO`, see
-- `Emit/PLAN.md` §7/R3, and is checked at run time via the deliverable
-- checklist's `forshor_emit bundle`/`template` invocations instead).
example :
    (match buildBundleCore .standard 2 (by decide) 6 10 false with
      | .ok json =>
          decide (((json.getObjVal? "schema").bind Json.getStr?).toOption = some "forshor.emit/v1") &&
          decide (((json.getObjVal? "n_free").bind Json.getBool?).toOption = some true)
      | .error _ => false) = true := by
  native_decide

-- 9/10/11 (the old hand-written E7 template's leaf count, the bundle's
-- `template` section shape, and `pp`/`cpp`/`qft`'s `template_match`/`ladder`/
-- `split` checks) are superseded by R2.1-R2.7's own exit criteria below,
-- which check the *extracted* `Doc` directly against the real term, and by
-- `Reflect.Verify`'s run-time `instantiate_eq_real` check that replaced
-- `template_match`/`ladder`/`split` in `pp`/`cpp`/`qft` themselves
-- (`Emit/PLAN.md` R3/R4) — `buildPP`/`buildCPP`/`buildQFT`/`buildBundle`/
-- `buildTemplateDoc` all need `IO` now (the extractor's environment
-- reload), so they are no longer `native_decide`-testable; they are
-- exercised by the deliverable checklist's `lake exe forshor_emit`
-- invocations instead.

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

-- `BEq Shor.Gate`/`BEq Shor.LowGate` are derived once in `Reflect/Verify.lean`
-- (imported transitively via `Symbolic.Bundle`), reused here and throughout.

set_option maxHeartbeats 1000000 in
extract_ir_doc pp_body_doc_k2 smallLowering

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

-- 17. R2.2's exit criterion (`Emit/PLAN.md` §6.4): `phase_product`
-- (`Shor.standardSignedPhaseLoweringPlan` + `Shor.lowerGateRec`), checked
-- against `IR.instantiate` at `n = 8` (base — `nextWidth ops 8 8 = 9 ≥ 8`,
-- so the guard is false and the real term is
-- `LowGate.Naive_SignedPhaseProd`) and `n = 16` (recurses once —
-- `nextWidth ops 16 16 = 13 < 16`, `reserveNeed ops 16 16 = (72, 72)`, so
-- 100 qubits of reserve on each side is enough). `buildDoc` (`Driver.lean`)
-- now bundles `phase_product` and `naive_leaf` together with `pp_body` —
-- `phase_product`'s base case is a `Node.call` to `naive_leaf`, so a `Doc`
-- with one but not the other is never `wellFormed`.
section R2_2

abbrev r2_2_k : Nat := 2
def r2_2_hk : 1 < r2_2_k := by decide
def r2_2_ops := (tableInstance .standard r2_2_k r2_2_hk).ops
def r2_2_phi : Angle := (1 : ℚ) / 4

set_option maxHeartbeats 1000000 in
extract_ir_doc r2_2_doc smallLowering

example : IR.Doc.wellFormed r2_2_doc = true := by native_decide

-- `coeff` is *not* keyed to one fixed `m`: `Env.call` (`IR/Instantiate.lean`)
-- carries `opaqueW`/`coeff` unchanged into a recursive `call`'s own
-- environment, and the child level's own `m` (`phaseLimbWidth` at the
-- child's, smaller, widths) genuinely differs from the top level's — so
-- `coeff` recomputes `cramerCoeffFromPtsWidth` at whatever `m` it is asked
-- for, exactly like `loweringPhaseCoeff` itself does for any `x`/`z`,
-- rather than checking a single fixed `m` (which would only ever match the
-- outermost call and silently error every recursive one).
def r2_2_env (ops : Prog r2_2_k) (x z : ExtReg) : IR.Env :=
  { w := fun n =>
      if n == "xw" then some x.width
      else if n == "zw" then some z.width
      else if n == "xCap" then some x.capacity
      else if n == "zCap" then some z.capacity
      else none
    a := fun n => if n == "phi" then some r2_2_phi else none
    r := fun n => if n == "x" then some x else if n == "z" then some z else none
    opaqueW := fun name args =>
      match name, args with
      | "nextWidth", [xw, zw] => some (RecursivePhaseWorkspace.nextWidth ops xw zw)
      | "reserveNeed_x", [xw, zw] => some (RecursivePhaseWorkspace.reserveNeed ops xw zw).1
      | "reserveNeed_z", [xw, zw] => some (RecursivePhaseWorkspace.reserveNeed ops xw zw).2
      | _, _ => none
    coeff := fun l mv =>
      if h : l < q r2_2_k then
        some (cramerCoeffFromPtsWidth r2_2_k mv (tableInstance .standard r2_2_k r2_2_hk).points
          (tableInstance .standard r2_2_k r2_2_hk).hlen ⟨l, h⟩)
      else none }

partial def r2_2_flatten : LowGate → List LowGate
  | .id => []
  | .seq a b => r2_2_flatten a ++ r2_2_flatten b
  | g => [g]

section R2_2_Base

def r2_2b_x : ExtReg := ExtReg.ofReg (Reg.interval 0 8)
def r2_2b_z : ExtReg := ExtReg.ofReg (Reg.interval 100 8)

def r2_2b_hworkspace : SignedRecursiveWorkspaceOK r2_2_ops r2_2b_x r2_2b_z :=
  ⟨by decide, by native_decide, by native_decide⟩

def r2_2b_real : LowGate :=
  lowerGateRec (standardSignedPhaseLoweringPlan r2_2_k r2_2_hk r2_2_phi r2_2b_x r2_2b_z r2_2_ops
    r2_2b_hworkspace)

set_option maxHeartbeats 1000000 in
example :
    ((match IR.instantiate r2_2_doc "phase_product" (r2_2_env r2_2_ops r2_2b_x r2_2b_z) 50 with
      | .ok g => r2_2_flatten g
      | .error _ => [])
      == r2_2_flatten r2_2b_real) = true := by
  native_decide

end R2_2_Base

section R2_2_Rec

def r2_2r_x : ExtReg := ExtReg.withReserve (Reg.interval 0 16) (Reg.interval 16 100) (by decide)
def r2_2r_z : ExtReg := ExtReg.withReserve (Reg.interval 200 16) (Reg.interval 216 100) (by decide)

def r2_2r_hworkspace : SignedRecursiveWorkspaceOK r2_2_ops r2_2r_x r2_2r_z :=
  ⟨by native_decide, by native_decide, by native_decide⟩

def r2_2r_real : LowGate :=
  lowerGateRec (standardSignedPhaseLoweringPlan r2_2_k r2_2_hk r2_2_phi r2_2r_x r2_2r_z r2_2_ops
    r2_2r_hworkspace)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
example :
    ((match IR.instantiate r2_2_doc "phase_product" (r2_2_env r2_2_ops r2_2r_x r2_2r_z) 50 with
      | .ok g => r2_2_flatten g
      | .error _ => [])
      == r2_2_flatten r2_2r_real) = true := by
  native_decide

end R2_2_Rec

end R2_2

-- 18. R2.4's `naive_cleaf` exit criterion (`Emit/PLAN.md` §6, controlled
-- counterpart of R2.3's `naive_leaf`): `LowGate.Naive_CSignedPhaseProd`'s
-- own double loop, `CCPhase` instead of `CPhase`, `ctrl` a single-qubit
-- register parameter per `IR/Instantiate.lean`'s `buildLowGate` convention.
-- `instantiate` agrees with the real term at the same six `(xw, zw)` pairs
-- R2.3 used, plus a fixed `ctrl` qubit disjoint from both `x`/`z`.
section R2_4_NaiveCLeaf

open Shor.Reflect in
def r2_4nc_doc : IR.Doc :=
  { templates := [naiveCLeafTemplate], opaqueFns := [], entry := "naive_cleaf" }

def r2_4nc_check (xw zw : Nat) : Bool :=
  let ctrl := ExtReg.ofReg (Reg.interval 1000 1)
  let x := ExtReg.ofReg (Reg.interval 0 xw)
  let z := ExtReg.ofReg (Reg.interval xw zw)
  let phi : Angle := (3 : ℚ) / 7
  let real := LowGate.Naive_CSignedPhaseProd 1000 phi x z
  let env : IR.Env :=
    { w := fun n => if n == "xw" then some xw else if n == "zw" then some zw else none
      a := fun n => if n == "phi" then some phi else none
      r := fun n =>
        if n == "ctrl" then some ctrl
        else if n == "x" then some x
        else if n == "z" then some z
        else none
      opaqueW := fun _ _ => none, coeff := fun _ _ => none }
  match IR.instantiate r2_4nc_doc "naive_cleaf" env 10 with
  | .ok g => lowGateJson g == lowGateJson real
  | .error _ => false

example : IR.Doc.wellFormed r2_4nc_doc = true := by native_decide

example :
    [r2_4nc_check 1 4, r2_4nc_check 2 3, r2_4nc_check 3 2, r2_4nc_check 4 1, r2_4nc_check 5 6,
      r2_4nc_check 6 5] = [true, true, true, true, true, true] := by
  native_decide

end R2_4_NaiveCLeaf

-- 19. R2.4's `cphase_product` exit criterion (`Emit/PLAN.md` §6, controlled
-- counterpart of R2.2's `phase_product`): `standardCSignedPhaseLoweringPlan`
-- + `lowerGateRec`, checked at `n = 8` (base) and `n = 16` (recurses) —
-- same widths, same `reserveNeed`/`nextWidth` values as R2.2, since `ctrl`
-- plays no part in the layout/reserve bookkeeping, only in which qubit the
-- phase leaves are controlled by. `ctrl` is a fixed qubit disjoint from
-- both `x`/`z`'s complete ranges (`CtrlDisjoint`).
section R2_4_CPhaseProduct

abbrev r2_4_k : Nat := 2
def r2_4_hk : 1 < r2_4_k := by decide
def r2_4_ops := (tableInstance .standard r2_4_k r2_4_hk).ops
def r2_4_phi : Angle := (1 : ℚ) / 4
def r2_4_ctrlIdx : Nat := 1000

set_option maxHeartbeats 1000000 in
extract_ir_doc r2_4_doc smallLowering

def r2_4_env (ops : Prog r2_4_k) (ctrl x z : ExtReg) : IR.Env :=
  { w := fun n =>
      if n == "xw" then some x.width
      else if n == "zw" then some z.width
      else if n == "xCap" then some x.capacity
      else if n == "zCap" then some z.capacity
      else none
    a := fun n => if n == "phi" then some r2_4_phi else none
    r := fun n =>
      if n == "ctrl" then some ctrl
      else if n == "x" then some x
      else if n == "z" then some z
      else none
    opaqueW := fun name args =>
      match name, args with
      | "nextWidth", [xw, zw] => some (RecursivePhaseWorkspace.nextWidth ops xw zw)
      | "reserveNeed_x", [xw, zw] => some (RecursivePhaseWorkspace.reserveNeed ops xw zw).1
      | "reserveNeed_z", [xw, zw] => some (RecursivePhaseWorkspace.reserveNeed ops xw zw).2
      | _, _ => none
    coeff := fun l mv =>
      if h : l < q r2_4_k then
        some (cramerCoeffFromPtsWidth r2_4_k mv (tableInstance .standard r2_4_k r2_4_hk).points
          (tableInstance .standard r2_4_k r2_4_hk).hlen ⟨l, h⟩)
      else none }

partial def r2_4_flatten : LowGate → List LowGate
  | .id => []
  | .seq a b => r2_4_flatten a ++ r2_4_flatten b
  | g => [g]

def r2_4_ctrl : ExtReg := ExtReg.ofReg (Reg.interval r2_4_ctrlIdx 1)

section R2_4_Base

def r2_4b_x : ExtReg := ExtReg.ofReg (Reg.interval 0 8)
def r2_4b_z : ExtReg := ExtReg.ofReg (Reg.interval 100 8)

def r2_4b_hworkspace : CSignedRecursiveWorkspaceOK r2_4_ops r2_4_ctrlIdx r2_4b_x r2_4b_z :=
  { owned_disjoint := by decide
    x_reserve_sufficient := by native_decide
    z_reserve_sufficient := by native_decide
    control_disjoint := by decide }

def r2_4b_real : LowGate :=
  lowerGateRec (standardCSignedPhaseLoweringPlan r2_4_k r2_4_hk r2_4_ctrlIdx r2_4_phi r2_4b_x
    r2_4b_z r2_4_ops r2_4b_hworkspace)

set_option maxHeartbeats 1000000 in
example :
    ((match IR.instantiate r2_4_doc "cphase_product" (r2_4_env r2_4_ops r2_4_ctrl r2_4b_x r2_4b_z)
        50 with
      | .ok g => r2_4_flatten g
      | .error _ => [])
      == r2_4_flatten r2_4b_real) = true := by
  native_decide

end R2_4_Base

section R2_4_Rec

def r2_4r_x : ExtReg := ExtReg.withReserve (Reg.interval 0 16) (Reg.interval 16 100) (by decide)
def r2_4r_z : ExtReg := ExtReg.withReserve (Reg.interval 200 16) (Reg.interval 216 100) (by decide)

def r2_4r_hworkspace : CSignedRecursiveWorkspaceOK r2_4_ops r2_4_ctrlIdx r2_4r_x r2_4r_z :=
  { owned_disjoint := by native_decide
    x_reserve_sufficient := by native_decide
    z_reserve_sufficient := by native_decide
    control_disjoint := by native_decide }

def r2_4r_real : LowGate :=
  lowerGateRec (standardCSignedPhaseLoweringPlan r2_4_k r2_4_hk r2_4_ctrlIdx r2_4_phi r2_4r_x
    r2_4r_z r2_4_ops r2_4r_hworkspace)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
example :
    ((match IR.instantiate r2_4_doc "cphase_product" (r2_4_env r2_4_ops r2_4_ctrl r2_4r_x r2_4r_z)
        50 with
      | .ok g => r2_4_flatten g
      | .error _ => [])
      == r2_4_flatten r2_4r_real) = true := by
  native_decide

end R2_4_Rec

end R2_4_CPhaseProduct

-- 20. R2.5's exit criterion (`Emit/PLAN.md` §6): `qft`
-- (`Shor.standardQFTLoweringPlan` + `Shor.lowerQFTPlan`), checked against
-- `IR.instantiate` at `w = 4` (two levels of `qft`'s own recursion: 4
-- splits into two width-2 halves, each of which splits again into two
-- width-1 singletons) and `w = 8` (three levels). `qftWorkspaceNeed ops _ =
-- (1, 1)` for every width in this table, so 2 qubits of reserve is always
-- enough. `qft`'s own `Node.call`s to `phase_product` at each split are
-- exactly why `buildDoc` bundles `phase_product`/`naive_leaf` into the same
-- `Doc` as `qft`.
section R2_5

abbrev r2_5_k : Nat := 2
def r2_5_hk : 1 < r2_5_k := by decide
def r2_5_ops := (tableInstance .standard r2_5_k r2_5_hk).ops

set_option maxHeartbeats 1000000 in
extract_ir_doc r2_5_doc smallLowering

def r2_5_env (ops : Prog r2_5_k) (r xWork zWork : ExtReg) : IR.Env :=
  { w := fun n =>
      if n == "w" then some r.width
      else if n == "xWorkW" then some xWork.width
      else if n == "zWorkW" then some zWork.width
      else none
    a := fun _ => none
    r := fun n =>
      if n == "r" then some r
      else if n == "xWork" then some xWork
      else if n == "zWork" then some zWork
      else none
    opaqueW := fun name args =>
      match name, args with
      | "nextWidth", [xw, zw] => some (RecursivePhaseWorkspace.nextWidth ops xw zw)
      | "reserveNeed_x", [xw, zw] => some (RecursivePhaseWorkspace.reserveNeed ops xw zw).1
      | "reserveNeed_z", [xw, zw] => some (RecursivePhaseWorkspace.reserveNeed ops xw zw).2
      | "qftXWork", [w] => some (qftWorkspaceNeed ops w).1
      | "qftZWork", [w] => some (qftWorkspaceNeed ops w).2
      | _, _ => none
    coeff := fun l mv =>
      if h : l < q r2_5_k then
        some (cramerCoeffFromPtsWidth r2_5_k mv (tableInstance .standard r2_5_k r2_5_hk).points
          (tableInstance .standard r2_5_k r2_5_hk).hlen ⟨l, h⟩)
      else none }

partial def r2_5_flatten : LowGate → List LowGate
  | .id => []
  | .seq a b => r2_5_flatten a ++ r2_5_flatten b
  | g => [g]

section R2_5_W4

def r2_5w4_r : ExtReg := ExtReg.withReserve (Reg.interval 0 4) (Reg.interval 4 2) (by decide)
def r2_5w4_hworkspace : QFTReserveOK r2_5_ops r2_5w4_r := ⟨by native_decide⟩
def r2_5w4_xWork : ExtReg := ExtReg.ofReg (qftXWork r2_5_ops r2_5w4_r)
def r2_5w4_zWork : ExtReg := ExtReg.ofReg (qftZWork r2_5_ops r2_5w4_r)
def r2_5w4_real : LowGate := lowerQFT r2_5_k r2_5_hk r2_5_ops r2_5w4_r r2_5w4_hworkspace

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
example :
    ((match IR.instantiate r2_5_doc "qft" (r2_5_env r2_5_ops r2_5w4_r r2_5w4_xWork r2_5w4_zWork)
        100 with
      | .ok g => r2_5_flatten g
      | .error _ => [])
      == r2_5_flatten r2_5w4_real) = true := by
  native_decide

end R2_5_W4

section R2_5_W8

def r2_5w8_r : ExtReg := ExtReg.withReserve (Reg.interval 0 8) (Reg.interval 8 2) (by decide)
def r2_5w8_hworkspace : QFTReserveOK r2_5_ops r2_5w8_r := ⟨by native_decide⟩
def r2_5w8_xWork : ExtReg := ExtReg.ofReg (qftXWork r2_5_ops r2_5w8_r)
def r2_5w8_zWork : ExtReg := ExtReg.ofReg (qftZWork r2_5_ops r2_5w8_r)
def r2_5w8_real : LowGate := lowerQFT r2_5_k r2_5_hk r2_5_ops r2_5w8_r r2_5w8_hworkspace

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
example :
    ((match IR.instantiate r2_5_doc "qft" (r2_5_env r2_5_ops r2_5w8_r r2_5w8_xWork r2_5w8_zWork)
        200 with
      | .ok g => r2_5_flatten g
      | .error _ => [])
      == r2_5_flatten r2_5w8_real) = true := by
  native_decide

end R2_5_W8

end R2_5

section R2_6_ShorGate

set_option maxHeartbeats 4000000 in
extract_ir_doc r2_6g_doc smallLowering

def r2_6g_env (a N : ℕ) (x y work scratch : ExtReg) (flag : ℕ) : IR.Env :=
  { w := fun n =>
      if n == "a" then some a
      else if n == "N" then some N
      else if n == "xW" then some x.width
      else if n == "xCap" then some x.capacity
      else if n == "yW" then some y.width
      else if n == "yCap" then some y.capacity
      else if n == "workW" then some work.width
      else if n == "workCap" then some work.capacity
      else if n == "scratchW" then some scratch.width
      else if n == "scratchCap" then some scratch.capacity
      else none
    a := fun _ => none
    r := fun n =>
      if n == "x" then some x
      else if n == "y" then some y
      else if n == "work" then some work
      else if n == "scratch" then some scratch
      else if n == "flag" then some (ExtReg.ofReg (Reg.interval flag 1))
      else none
    opaqueW := fun name args =>
      match name, args with
      | "mod", [m, n] => some (m % n)
      | "pow", [b, e] => some (b ^ e)
      | "modpow", [b, e, n] => some ((b ^ (2 ^ e)) % n)
      | "step5Const", [c, n] => some (step5Constant c n)
      | "log2", [n] => some (Nat.log2 n)
      | _, _ => none
    coeff := fun _ _ => none }

-- Unlike every earlier `_flatten` (which only ever needs to flatten one
-- top-level `;;` chain), `orderFindingApprox`'s adjoints (`step5`'s
-- `†(H_reg ;; CPhaseProdUsing ;; IQFT)`, `cmpLtNW`'s `†diff ;; †mul`) wrap
-- *multi-gate* sub-sequences whose own `Node.seq`↦`foldGateSeq` folding
-- introduces a trailing `.id` the real term's direct `;;` chain never has —
-- `translateNode`'s `.seq`/`.adj` cases are still exactly right (§6.7's
-- `flatten` idiom already handles it at the top level); it is only *this
-- test's own comparison* that must recurse into `.adj` bodies too, or a
-- mismatch hidden under an `adj` never surfaces (confirmed empirically).
partial def r2_6g_flatten : Gate → List Gate
  | .id => []
  | .seq a b => r2_6g_flatten a ++ r2_6g_flatten b
  | .adj g => [Gate.adj ((r2_6g_flatten g).foldr Gate.seq .id)]
  | g => [g]

def r2_6g_ops := smallLowering.ops

def r2_6g_layout : Reference.ReferenceShorLayout :=
  Reference.allocateReferenceLayout r2_6g_ops smallInst 0

def r2_6g_hworkspace : ModMulCircuitWorkspaceOK r2_6g_layout.data r2_6g_layout.work :=
  Reference.reference_modMulCircuitWorkspaceOK r2_6g_ops smallInst 0

def r2_6g_hstep4 :
    CmpLtNWWorkspace smallInst.N (r2_6g_layout.data.grow 1) r2_6g_layout.work r2_6g_layout.scratch
      r2_6g_layout.flag :=
  Reference.reference_step4Workspace r2_6g_ops smallInst 0

def r2_6g_real : Gate :=
  orderFindingApprox smallInst.a smallInst.N r2_6g_layout.x r2_6g_layout.data r2_6g_layout.work
    r2_6g_layout.scratch r2_6g_layout.flag r2_6g_hworkspace r2_6g_hstep4

example : IR.Doc.wellFormed r2_6g_doc = true := by native_decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
example :
    ((match IR.instantiateGate r2_6g_doc "shor_gate"
        (r2_6g_env smallInst.a smallInst.N r2_6g_layout.x r2_6g_layout.data r2_6g_layout.work
          r2_6g_layout.scratch r2_6g_layout.flag)
        300 with
      | .ok g => r2_6g_flatten g
      | .error _ => [])
      == r2_6g_flatten r2_6g_real) = true := by
  native_decide

end R2_6_ShorGate

section R2_6_Shor

set_option maxHeartbeats 4000000 in
extract_ir_doc r2_6_doc smallLowering

-- `shor`'s `Node.call`s reach into `qft`/`phase_product`/`cphase_product`'s
-- own bodies, so this env needs every opaque name/`coeff` those templates
-- need too (`r2_2_env`/`r2_5_env`'s formulas), on top of R2.6's own
-- `mod`/`pow`/`modpow`/`step5Const`/`log2` (`r2_6g_env`'s).
def r2_6_env (a N : ℕ) (x y work scratch : ExtReg) (flag : ℕ) : IR.Env :=
  { w := fun n =>
      if n == "a" then some a
      else if n == "N" then some N
      else if n == "xW" then some x.width
      else if n == "xCap" then some x.capacity
      else if n == "yW" then some y.width
      else if n == "yCap" then some y.capacity
      else if n == "workW" then some work.width
      else if n == "workCap" then some work.capacity
      else if n == "scratchW" then some scratch.width
      else if n == "scratchCap" then some scratch.capacity
      else none
    a := fun _ => none
    r := fun n =>
      if n == "x" then some x
      else if n == "y" then some y
      else if n == "work" then some work
      else if n == "scratch" then some scratch
      else if n == "flag" then some (ExtReg.ofReg (Reg.interval flag 1))
      else none
    opaqueW := fun name args =>
      match name, args with
      | "mod", [m, n] => some (m % n)
      | "pow", [b, e] => some (b ^ e)
      | "modpow", [b, e, n] => some ((b ^ (2 ^ e)) % n)
      | "step5Const", [c, n] => some (step5Constant c n)
      | "log2", [n] => some (Nat.log2 n)
      | "nextWidth", [xw, zw] => some (RecursivePhaseWorkspace.nextWidth r2_6g_ops xw zw)
      | "reserveNeed_x", [xw, zw] => some (RecursivePhaseWorkspace.reserveNeed r2_6g_ops xw zw).1
      | "reserveNeed_z", [xw, zw] => some (RecursivePhaseWorkspace.reserveNeed r2_6g_ops xw zw).2
      | "qftXWork", [w] => some (qftWorkspaceNeed r2_6g_ops w).1
      | "qftZWork", [w] => some (qftWorkspaceNeed r2_6g_ops w).2
      | _, _ => none
    coeff := fun l mv =>
      if h : l < q 2 then
        some (cramerCoeffFromPtsWidth 2 mv (tableInstance .standard 2 (by decide)).points
          (tableInstance .standard 2 (by decide)).hlen ⟨l, h⟩)
      else none }

-- Same recursive-through-`adj` discipline as `r2_6g_flatten` — `cmpLtNW`'s
-- `†diff ;; †mul` and `CmodMulInPlaceCore`'s per-step adjoints are still
-- present after lowering.
partial def r2_6_flatten : LowGate → List LowGate
  | .id => []
  | .seq a b => r2_6_flatten a ++ r2_6_flatten b
  | .adj g => [LowGate.adj ((r2_6_flatten g).foldr LowGate.seq .id)]
  | g => [g]

def r2_6_real : LowGate :=
  Reference.referenceShorCircuit smallLowering smallInst 0

example : IR.Doc.wellFormed r2_6_doc = true := by native_decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
example :
    ((match IR.instantiate r2_6_doc "shor"
        (r2_6_env smallInst.a smallInst.N r2_6g_layout.x r2_6g_layout.data r2_6g_layout.work
          r2_6g_layout.scratch r2_6g_layout.flag)
        300 with
      | .ok g => r2_6_flatten g
      | .error _ => [])
      == r2_6_flatten r2_6_real) = true := by
  native_decide

end R2_6_Shor

-- R2.7 (`Emit/PLAN.md` §6, the genericity checkpoint): `Extract.lean`/
-- `Targets.lean` are keyed by Lean construct name only (D2), never by `k` or
-- table source — so R2.2's and R2.5's own exit criteria should carry over to
-- `k = 3` (standard) and to `k = 2` with the `generate` table source with
-- **no code change** to either file. This section is exactly that recheck:
-- same `extractPhaseProductBody`/`extractQFTBody`, same `r2_2_env`/`r2_5_env`
-- shape, same `_flatten` idiom, just called at different `(k, src)` pairs.
section R2_7

section R2_7_PhaseProduct_K3Standard

abbrev r2_7pp3_k : Nat := 3
def r2_7pp3_hk : 1 < r2_7pp3_k := by decide
def r2_7pp3_ops := (tableInstance .standard r2_7pp3_k r2_7pp3_hk).ops
def r2_7pp3_phi : Angle := (1 : ℚ) / 4

set_option maxHeartbeats 4000000 in
extract_ir_doc r2_7pp3_doc k3Lowering

example : IR.Doc.wellFormed r2_7pp3_doc = true := by native_decide

def r2_7pp3_env (ops : Prog r2_7pp3_k) (x z : ExtReg) : IR.Env :=
  { w := fun n =>
      if n == "xw" then some x.width
      else if n == "zw" then some z.width
      else if n == "xCap" then some x.capacity
      else if n == "zCap" then some z.capacity
      else none
    a := fun n => if n == "phi" then some r2_7pp3_phi else none
    r := fun n => if n == "x" then some x else if n == "z" then some z else none
    opaqueW := fun name args =>
      match name, args with
      | "nextWidth", [xw, zw] => some (RecursivePhaseWorkspace.nextWidth ops xw zw)
      | "reserveNeed_x", [xw, zw] => some (RecursivePhaseWorkspace.reserveNeed ops xw zw).1
      | "reserveNeed_z", [xw, zw] => some (RecursivePhaseWorkspace.reserveNeed ops xw zw).2
      | _, _ => none
    coeff := fun l mv =>
      if h : l < q r2_7pp3_k then
        some (cramerCoeffFromPtsWidth r2_7pp3_k mv (tableInstance .standard r2_7pp3_k r2_7pp3_hk).points
          (tableInstance .standard r2_7pp3_k r2_7pp3_hk).hlen ⟨l, h⟩)
      else none }

partial def r2_7pp3_flatten : LowGate → List LowGate
  | .id => []
  | .seq a b => r2_7pp3_flatten a ++ r2_7pp3_flatten b
  | g => [g]

def r2_7pp3_x : ExtReg := ExtReg.ofReg (Reg.interval 0 8)
def r2_7pp3_z : ExtReg := ExtReg.ofReg (Reg.interval 100 8)

def r2_7pp3_hworkspace : SignedRecursiveWorkspaceOK r2_7pp3_ops r2_7pp3_x r2_7pp3_z :=
  ⟨by decide, by native_decide, by native_decide⟩

def r2_7pp3_real : LowGate :=
  lowerGateRec (standardSignedPhaseLoweringPlan r2_7pp3_k r2_7pp3_hk r2_7pp3_phi r2_7pp3_x r2_7pp3_z
    r2_7pp3_ops r2_7pp3_hworkspace)

set_option maxHeartbeats 1000000 in
example :
    ((match IR.instantiate r2_7pp3_doc "phase_product" (r2_7pp3_env r2_7pp3_ops r2_7pp3_x r2_7pp3_z)
        50 with
      | .ok g => r2_7pp3_flatten g
      | .error _ => [])
      == r2_7pp3_flatten r2_7pp3_real) = true := by
  native_decide

end R2_7_PhaseProduct_K3Standard

-- R5 (`Emit/PLAN.md` §11): D5's amendment means "any table" is now "any
-- `ShorLoweringSetup`", not "any `TableSource`" — `.generate` (no
-- `ShorLoweringSetup`, since `StandardPhaseLoweringPlan`'s coefficients are
-- fixed to `genInterpolationPoints k` regardless of `ops`, so a `.generate`
-- table's own points would be the *wrong* ones) is no longer a legitimate
-- input anywhere in the symbolic path. This section replaces the old
-- `.generate` genericity demonstration with §11.3's exit criterion: a
-- hand-built `ShorLoweringSetup` whose `ops` genuinely differ from
-- `standardLoweringSetup 2`'s (a redundant, semantically-inert
-- `shiftL`/`shiftR 0` pair appended) but still consume
-- `genInterpolationPoints 2` in order and return to the start state —
-- discharged by `native_decide` using `Table/Decide.lean`'s new `Decidable`
-- instances, not assumed.
section R2_7_PhaseProduct_CustomTable

abbrev r2_7c_k : Nat := 2
def r2_7c_hk : 1 < r2_7c_k := by decide

/-- The standard `k = 2` ops, plus one semantically-inert `shiftL i 0 ;;
shiftR i 0` pair (shifting by `0` is the identity on `State.shiftLReg`/
`.shiftRReg?`, and `shiftRReg?` never fails at `n = 0`, so this changes
`ops`'s *list structure* — hence what the extractor actually walks — without
changing what point sequence it consumes or what state it returns to). -/
def r2_7c_ops : Prog r2_7c_k :=
  (standardLoweringSetup r2_7c_k r2_7c_hk).ops ++
    [Operations.valid_ops.shiftL ⟨0, by decide⟩ 0, Operations.valid_ops.shiftR ⟨0, by decide⟩ 0]

def r2_7c_setup : ShorLoweringSetup :=
  { k := r2_7c_k
    hk := r2_7c_hk
    ops := r2_7c_ops
    consumes := by native_decide
    returns := by native_decide }

def r2_7c_phi : Angle := (1 : ℚ) / 4

set_option maxHeartbeats 4000000 in
extract_ir_doc r2_7c_doc r2_7c_setup

example : IR.Doc.wellFormed r2_7c_doc = true := by native_decide

def r2_7c_env (ops : Prog r2_7c_k) (x z : ExtReg) : IR.Env :=
  { w := fun n =>
      if n == "xw" then some x.width
      else if n == "zw" then some z.width
      else if n == "xCap" then some x.capacity
      else if n == "zCap" then some z.capacity
      else none
    a := fun n => if n == "phi" then some r2_7c_phi else none
    r := fun n => if n == "x" then some x else if n == "z" then some z else none
    opaqueW := fun name args =>
      match name, args with
      | "nextWidth", [xw, zw] => some (RecursivePhaseWorkspace.nextWidth ops xw zw)
      | "reserveNeed_x", [xw, zw] => some (RecursivePhaseWorkspace.reserveNeed ops xw zw).1
      | "reserveNeed_z", [xw, zw] => some (RecursivePhaseWorkspace.reserveNeed ops xw zw).2
      | _, _ => none
    coeff := fun l mv =>
      if h : l < q r2_7c_k then
        some (cramerCoeffFromPtsWidth r2_7c_k mv (genInterpolationPoints r2_7c_k)
          (generatedInterpolationPoints_length r2_7c_k) ⟨l, h⟩)
      else none }

partial def r2_7c_flatten : LowGate → List LowGate
  | .id => []
  | .seq a b => r2_7c_flatten a ++ r2_7c_flatten b
  | g => [g]

-- `n = 16` recurses (R2.2's own recursive case, `nextWidth ops 16 16 < 16`)
-- — the two extra trailing ops don't change that, since `nextWidth`/
-- `reserveNeed` are computed from the same `addScaled`/adder-class ops
-- either way; the generous reserve margin absorbs whatever small change the
-- two extra ops make.
def r2_7c_x : ExtReg := ExtReg.withReserve (Reg.interval 0 16) (Reg.interval 16 100) (by decide)
def r2_7c_z : ExtReg := ExtReg.withReserve (Reg.interval 200 16) (Reg.interval 216 100) (by decide)

def r2_7c_hworkspace : SignedRecursiveWorkspaceOK r2_7c_ops r2_7c_x r2_7c_z :=
  ⟨by native_decide, by native_decide, by native_decide⟩

def r2_7c_real : LowGate :=
  lowerSignedPhaseProdWithWorkspace r2_7c_k r2_7c_hk r2_7c_phi r2_7c_x r2_7c_z r2_7c_ops
    r2_7c_hworkspace

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
example :
    ((match IR.instantiate r2_7c_doc "phase_product" (r2_7c_env r2_7c_ops r2_7c_x r2_7c_z) 50 with
      | .ok g => r2_7c_flatten g
      | .error _ => [])
      == r2_7c_flatten r2_7c_real) = true := by
  native_decide

end R2_7_PhaseProduct_CustomTable

section R2_7_Qft_K3Standard

abbrev r2_7q3_k : Nat := 3
def r2_7q3_hk : 1 < r2_7q3_k := by decide
def r2_7q3_ops := (tableInstance .standard r2_7q3_k r2_7q3_hk).ops

set_option maxHeartbeats 4000000 in
extract_ir_doc r2_7q3_doc k3Lowering

example : IR.Doc.wellFormed r2_7q3_doc = true := by native_decide

def r2_7q3_env (ops : Prog r2_7q3_k) (r xWork zWork : ExtReg) : IR.Env :=
  { w := fun n =>
      if n == "w" then some r.width
      else if n == "xWorkW" then some xWork.width
      else if n == "zWorkW" then some zWork.width
      else none
    a := fun _ => none
    r := fun n =>
      if n == "r" then some r
      else if n == "xWork" then some xWork
      else if n == "zWork" then some zWork
      else none
    opaqueW := fun name args =>
      match name, args with
      | "nextWidth", [xw, zw] => some (RecursivePhaseWorkspace.nextWidth ops xw zw)
      | "reserveNeed_x", [xw, zw] => some (RecursivePhaseWorkspace.reserveNeed ops xw zw).1
      | "reserveNeed_z", [xw, zw] => some (RecursivePhaseWorkspace.reserveNeed ops xw zw).2
      | "qftXWork", [w] => some (qftWorkspaceNeed ops w).1
      | "qftZWork", [w] => some (qftWorkspaceNeed ops w).2
      | _, _ => none
    coeff := fun l mv =>
      if h : l < q r2_7q3_k then
        some (cramerCoeffFromPtsWidth r2_7q3_k mv (tableInstance .standard r2_7q3_k r2_7q3_hk).points
          (tableInstance .standard r2_7q3_k r2_7q3_hk).hlen ⟨l, h⟩)
      else none }

partial def r2_7q3_flatten : LowGate → List LowGate
  | .id => []
  | .seq a b => r2_7q3_flatten a ++ r2_7q3_flatten b
  | g => [g]

def r2_7q3_r : ExtReg := ExtReg.withReserve (Reg.interval 0 4) (Reg.interval 4 2) (by decide)
def r2_7q3_hworkspace : QFTReserveOK r2_7q3_ops r2_7q3_r := ⟨by native_decide⟩
def r2_7q3_xWork : ExtReg := ExtReg.ofReg (qftXWork r2_7q3_ops r2_7q3_r)
def r2_7q3_zWork : ExtReg := ExtReg.ofReg (qftZWork r2_7q3_ops r2_7q3_r)
def r2_7q3_real : LowGate := lowerQFT r2_7q3_k r2_7q3_hk r2_7q3_ops r2_7q3_r r2_7q3_hworkspace

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
example :
    ((match IR.instantiate r2_7q3_doc "qft" (r2_7q3_env r2_7q3_ops r2_7q3_r r2_7q3_xWork r2_7q3_zWork)
        100 with
      | .ok g => r2_7q3_flatten g
      | .error _ => [])
      == r2_7q3_flatten r2_7q3_real) = true := by
  native_decide

end R2_7_Qft_K3Standard

-- Reuses `r2_7c_doc`/`r2_7c_setup` (`R2_7_PhaseProduct_CustomTable` above):
-- `buildDoc` extracts every template from one `setup` at once, so `qft`'s
-- own genericity is already checked by the same extraction — no second
-- `extract_ir_doc` needed.
section R2_7_Qft_CustomTable

def r2_7cq_env (ops : Prog r2_7c_k) (r xWork zWork : ExtReg) : IR.Env :=
  { w := fun n =>
      if n == "w" then some r.width
      else if n == "xWorkW" then some xWork.width
      else if n == "zWorkW" then some zWork.width
      else none
    a := fun _ => none
    r := fun n =>
      if n == "r" then some r
      else if n == "xWork" then some xWork
      else if n == "zWork" then some zWork
      else none
    opaqueW := fun name args =>
      match name, args with
      | "nextWidth", [xw, zw] => some (RecursivePhaseWorkspace.nextWidth ops xw zw)
      | "reserveNeed_x", [xw, zw] => some (RecursivePhaseWorkspace.reserveNeed ops xw zw).1
      | "reserveNeed_z", [xw, zw] => some (RecursivePhaseWorkspace.reserveNeed ops xw zw).2
      | "qftXWork", [w] => some (qftWorkspaceNeed ops w).1
      | "qftZWork", [w] => some (qftWorkspaceNeed ops w).2
      | _, _ => none
    coeff := fun l mv =>
      if h : l < q r2_7c_k then
        some (cramerCoeffFromPtsWidth r2_7c_k mv (genInterpolationPoints r2_7c_k)
          (generatedInterpolationPoints_length r2_7c_k) ⟨l, h⟩)
      else none }

partial def r2_7cq_flatten : LowGate → List LowGate
  | .id => []
  | .seq a b => r2_7cq_flatten a ++ r2_7cq_flatten b
  | g => [g]

def r2_7cq_r : ExtReg := ExtReg.withReserve (Reg.interval 0 4) (Reg.interval 4 2) (by decide)
def r2_7cq_hworkspace : QFTReserveOK r2_7c_ops r2_7cq_r := ⟨by native_decide⟩
def r2_7cq_xWork : ExtReg := ExtReg.ofReg (qftXWork r2_7c_ops r2_7cq_r)
def r2_7cq_zWork : ExtReg := ExtReg.ofReg (qftZWork r2_7c_ops r2_7cq_r)
def r2_7cq_real : LowGate := lowerQFT r2_7c_k r2_7c_hk r2_7c_ops r2_7cq_r r2_7cq_hworkspace

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
example :
    ((match IR.instantiate r2_7c_doc "qft" (r2_7cq_env r2_7c_ops r2_7cq_r r2_7cq_xWork r2_7cq_zWork)
        100 with
      | .ok g => r2_7cq_flatten g
      | .error _ => [])
      == r2_7cq_flatten r2_7cq_real) = true := by
  native_decide

end R2_7_Qft_CustomTable

end R2_7

end Shor.Emit.Tests
