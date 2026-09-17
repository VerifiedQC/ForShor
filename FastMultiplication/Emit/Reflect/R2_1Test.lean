import FastMultiplication.Emit.Reflect.Targets
import FastMultiplication.Emit.IR.Instantiate
import FastMultiplication.Emit.IR.WellFormed
import FastMultiplication.Emit.Lower.Decide

/-!
# R2.1 exit criterion

`instantiateGate` of the extracted `pp_body` template, at a concrete `x`,
`z`, equals `compileOpsToSignedGate` itself: `k = 2`, standard table,
`x`/`z` both width 4 (chunk width 2 each — `4` divides evenly by `k = 2`),
enough reserve that `targetSignedLayoutState`'s growth to
`commonNeededWidth (scanNeededWidths x z ops) = 7` is not truncated (an
*insufficient* reserve makes `ExtReg.grow` silently truncate — a real
precondition failure `SignedRecursiveWorkspaceOK` rules out in the actual
pipeline, not something this comparison is answerable for).

Raw `Gate` `BEq` compares tree shape, not just leaf sequence — nested
`Gate.seq`s bracketed differently but with the same flattened leaves are
`BEq`-unequal even though semantically identical (the same reason
`Lower/Instantiate.lean`'s `check1_annotatedEqFlat` flattens before
comparing). So the actual check flattens both sides first, matching that
existing convention.
-/

open Lean Lean.Meta Shor Shor.Reflect

deriving instance BEq for Shor.Gate

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
partial def flattenGate : Gate → List Gate
  | .id => []
  | .seq a b => flattenGate a ++ flattenGate b
  | g => [g]

-- Run the extractor, `instantiateGate` the result, and report whether its
-- flattened leaf sequence matches the real term's — this is `#eval`, not yet
-- `native_decide`, since the extractor runs in `MetaM` (it needs the
-- environment) and only its *result* (an ordinary `IR.Doc`/`Gate`) is
-- something `native_decide` can later be pointed at once `Driver.lean` pins
-- one via the build-time `extract_ir_doc` command (`PLAN.md` §5.4).
#eval show MetaM Unit from do
  let t ← extractPPBody r2_1_k r2_1_hk .standard
  let doc : IR.Doc := { templates := [t], opaqueFns := [("nextWidth", 2)], entry := t.name }
  logInfo m!"wellFormed = {IR.Doc.wellFormed doc}"
  match IR.instantiateGate doc "pp_body" r2_1_env 10 with
  | .error e => logInfo m!"instantiate error: {e}"
  | .ok g =>
      let same := flattenGate g == flattenGate r2_1_real
      logInfo m!"R2.1 exit criterion (flattened leaves match) = {same}"
