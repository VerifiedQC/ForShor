import FastMultiplication.Emit.Json.PlanJson
import FastMultiplication.Emit.Symbolic.Template
import FastMultiplication.Emit.Symbolic.Recursion
import FastMultiplication.Emit.Lower.Decide

/-!
# Instantiation checks

Three checks tying the annotated plan view, the flat `LowGate` view, and the
E7 symbolic template together at a concrete checked width. Re-scoped from the
README's literal "byte for byte" / multi-level wording (see `Emit/README.md`,
Phase 2): full fidelity would mean recursively unrolling the template and
replaying `PhaseSplitLayout.ofBudget`'s exact physical-qubit assignment
algorithm, which is a new sub-system, not a check. What is implemented
instead, at one level of a checked concrete width:

1. **Annotated = flat.** The annotated `PhaseLoweringPlan`'s JSON, with every
   `SignedPhaseProd`/`CSignedPhaseProd` annotation substituted away (its
   `expansion` at a base case, its `body` recursively at a step case) and
   `seq` nodes fully spliced — matching `LowGate.flattenSeq`'s own n-ary
   flattening — equals `lowGateJson` of the independently-computed flat term,
   as `Json` values (`BEq Json`). Scoped to `pp`/`cpp`/`qft` (their terms
   contain no `Gate.adj`, which this flattener does not descend into).
2. **Template ≈ annotated, one level.** The E7 template's width formulas
   (`limb_width`, each slot's width), evaluated at the checked width with
   `nextWidth` realized as `RecursivePhaseWorkspace.nextWidth`, equal the real
   compiler's own numbers (`phaseLimbWidth`, `PhaseSplitLayout.child`'s
   width) read directly off the annotated plan's `layout`; and the template's
   one-level op-*kind* sequence (op tag, plus `negSrc`/`shift` for
   `AddScaled`; a phase-product node normalizes to one canonical tag on both
   sides, dropping the template's `child` index — the real plan's node has
   no comparable field, carrying all `q k` coefficients rather than one
   selected index. Widths, slot names, and physical registers are
   deliberately not compared either, since they live in different
   representations on the two sides) equals the real
   plan's one-level body, shallow-flattened (not descending into a nested
   `SignedPhaseProd`/`CSignedPhaseProd`, unlike check 1's deep flatten).
3. **Ladder.** The annotated plan's recursion depth and total base-case leaf
   count equal E6's `widthLadder`'s length and `q k ^ depth`
   (`Symbolic/Recursion.lean`).
-/

namespace Shor

open Lean (Json)
open Operations

/-- Evaluate a `WExpr` at a concrete `W`, realizing the opaque `nextWidth`
function as the caller supplies it (`RecursivePhaseWorkspace.nextWidth ops`
at the call sites below). -/
partial def WExpr.eval (nextWidthFn : ℕ → ℕ) (wVal : ℕ) : WExpr → ℕ
  | .var _ => wVal
  | .const n => n
  | .add a b => a.eval nextWidthFn wVal + b.eval nextWidthFn wVal
  | .sub a b => a.eval nextWidthFn wVal - b.eval nextWidthFn wVal
  | .mul a b => a.eval nextWidthFn wVal * b.eval nextWidthFn wVal
  | .div a b => a.eval nextWidthFn wVal / b.eval nextWidthFn wVal
  | .max a b => Nat.max (a.eval nextWidthFn wVal) (b.eval nextWidthFn wVal)
  | .nextWidth a => nextWidthFn (a.eval nextWidthFn wVal)

/-- Check 1's deep flattener: splice `seq` nodes fully (matching
`LowGate.flattenSeq`), substitute `SignedPhaseProd`/`CSignedPhaseProd`
annotations with their `expansion`/`body`, drop `id`. -/
partial def deepFlattenPlanJsonList (j : Json) : List Json :=
  match (j.getObjValD "op").getStr?.toOption with
  | some "id" => []
  | some "seq" =>
      match (j.getObjValD "body").getArr?.toOption with
      | some arr => arr.toList.flatMap deepFlattenPlanJsonList
      | none => [j]
  | some "SignedPhaseProd" | some "CSignedPhaseProd" =>
      deepFlattenPlanJsonList (j.getObjValD "body")
  | some "NaiveSignedPhaseProd" | some "NaiveCSignedPhaseProd" =>
      -- `expansion` is itself `lowGateJson`'s output for a `LowGate.seq` term
      -- (or a single leaf) — splice it the same way, don't embed it opaquely.
      deepFlattenPlanJsonList (j.getObjValD "expansion")
  | _ => [j]

/-- Canonicalize a flattened list the same way `lowGateJson` would present a
top-level term: a single item as itself, `id` (an empty list) as `{"op":
"id"}`, otherwise as one `seq` node wrapping the whole n-ary list. -/
def wrapFlattened (items : List Json) : Json :=
  match items with
  | [] => Json.mkObj [("op", Json.str "id")]
  | [single] => single
  | _ => Json.mkObj [("op", Json.str "seq"), ("body", Json.arr items.toArray)]

/-- Check 1: deep-flattening the annotated plan's JSON equals `lowGateJson`
of the independently-computed flat term. -/
def check1_annotatedEqFlat (planJ : Json) (flat : LowGate) : Bool :=
  wrapFlattened (deepFlattenPlanJsonList planJ) == lowGateJson flat

/-- Check 2's shallow flattener: splice `seq` nodes, but stop at a nested
`SignedPhaseProd`/`CSignedPhaseProd` (treat it as one opaque leaf) — this is
what makes the comparison "one level". -/
partial def shallowFlattenPlanJsonList (j : Json) : List Json :=
  match (j.getObjValD "op").getStr?.toOption with
  | some "id" => []
  | some "seq" =>
      match (j.getObjValD "body").getArr?.toOption with
      | some arr => arr.toList.flatMap shallowFlattenPlanJsonList
      | none => [j]
  | _ => [j]

/-- The shape-relevant fields of one op, discarding widths/slots/registers
(which live in different representations on the template and the real
plan): the op tag, plus `negSrc`/`shift` for `AddScaled`. A phase-product
node — `PhaseProduct`/`CPhaseProduct` on the template side,
`SignedPhaseProd`/`CSignedPhaseProd` on the real plan side — normalizes to
one canonical tag with no further fields: the template's `child` index (an
interpolation-point index) has no counterpart on the real plan's node (which
carries all `q k` coefficients, not a single selected index), so it is not a
meaningfully comparable field and is dropped rather than forced to match. -/
def opSignature (j : Json) : Json :=
  let op := (j.getObjValD "op").getStr?.toOption.getD ""
  match op with
  | "AddScaled" =>
      Json.mkObj [("op", Json.str op), ("negSrc", j.getObjValD "negSrc"), ("shift", j.getObjValD "shift")]
  | "PhaseProduct" | "CPhaseProduct" | "SignedPhaseProd" | "CSignedPhaseProd" =>
      Json.mkObj [("op", Json.str "PhaseProductNode")]
  | _ => Json.mkObj [("op", Json.str op)]

/-- Check 2's shape half: the template's one-level op-kind sequence equals
the real annotated plan's one-level body, shallow-flattened, up to the
`opSignature` projection. -/
def check2_shapeMatch (templateBodyArr : Array Json) (realStepBodyJ : Json) : Bool :=
  (templateBodyArr.toList.map opSignature)
    == ((shallowFlattenPlanJsonList realStepBodyJ).map opSignature)

/-- Check 2, both halves, for one signed phase product at concrete width `n`
(`n = max x.width z.width`, i.e. `phaseInputSize x z`). `none` if the plan is
already at a base case (nothing to check — the template's own `recursion`
field already says the naive primitive applies there). -/
def check2_signed
    {k : ℕ} (hk : 1 < k) (ops : Prog k) (phi : Angle) (x z : ExtReg)
    (plan : StandardPhaseLoweringPlan k hk ops (phaseInputSize x z) (Gate.SignedPhaseProd phi x z)) :
    Option Bool :=
  match plan with
  | .signedBase .. => none
  | .signedStep _ _ _ layout _ _ _ =>
      let n := phaseInputSize x z
      let nextWidthFn := fun w => RecursivePhaseWorkspace.nextWidth ops w w
      let widthsOk :=
        decide ((limbWidthExpr k).eval nextWidthFn n = phaseLimbWidth x z k) &&
        (List.finRange k).all fun i =>
          decide ((slotWidthExpr k i.val).eval nextWidthFn n = (layout.xSplit.child i).width) &&
          decide ((slotWidthExpr k i.val).eval nextWidthFn n = (layout.zSplit.child i).width)
      let templateBody := (phaseProductTemplateJson ops false).getObjValD "body"
      let shapeOk :=
        match templateBody.getArr? with
        | .error _ => false
        | .ok arr => check2_shapeMatch arr (planJson plan |>.getObjValD "body")
      some (widthsOk && shapeOk)

/-- Controlled analogue of `check2_signed`. -/
def check2_csigned
    {k : ℕ} (hk : 1 < k) (ops : Prog k) (ctrl : ℕ) (phi : Angle) (x z : ExtReg)
    (plan :
      StandardPhaseLoweringPlan k hk ops (phaseInputSize x z) (Gate.CSignedPhaseProd ctrl phi x z)) :
    Option Bool :=
  match plan with
  | .cSignedBase .. => none
  | .cSignedStep _ _ _ _ layout _ _ _ _ =>
      let n := phaseInputSize x z
      let nextWidthFn := fun w => RecursivePhaseWorkspace.nextWidth ops w w
      let widthsOk :=
        decide ((limbWidthExpr k).eval nextWidthFn n = phaseLimbWidth x z k) &&
        (List.finRange k).all fun i =>
          decide ((slotWidthExpr k i.val).eval nextWidthFn n = (layout.xSplit.child i).width) &&
          decide ((slotWidthExpr k i.val).eval nextWidthFn n = (layout.zSplit.child i).width)
      let templateBody := (phaseProductTemplateJson ops true).getObjValD "body"
      let shapeOk :=
        match templateBody.getArr? with
        | .error _ => false
        | .ok arr => check2_shapeMatch arr (planJson plan |>.getObjValD "body")
      some (widthsOk && shapeOk)

/-- Check 3: recursion depth and total base-case leaf count, compared
against E6's `widthLadder` and `q k ^ depth`. -/
partial def planDepth {k : ℕ} {hk : 1 < k} {pts : List Point} {hpts : pts.length = q k}
    {ops : Prog k} {initSize : ℕ} {U : Gate} :
    PhaseLoweringPlan k hk pts hpts ops initSize U → ℕ
  | .signedStep _ _ _ _ _ _ child => 1 + planDepth child
  | .cSignedStep _ _ _ _ _ _ _ _ child => 1 + planDepth child
  | .seq left right => max (planDepth left) (planDepth right)
  | _ => 0

partial def planLeafCount {k : ℕ} {hk : 1 < k} {pts : List Point} {hpts : pts.length = q k}
    {ops : Prog k} {initSize : ℕ} {U : Gate} :
    PhaseLoweringPlan k hk pts hpts ops initSize U → ℕ
  | .signedBase .. => 1
  | .cSignedBase .. => 1
  | .signedStep _ _ _ _ _ _ child => planLeafCount child
  | .cSignedStep _ _ _ _ _ _ _ _ child => planLeafCount child
  | .seq left right => planLeafCount left + planLeafCount right
  | _ => 0

def check3_ladder {k : ℕ} {hk : 1 < k} {pts : List Point} {hpts : pts.length = q k}
    {ops : Prog k} {n : ℕ} {U : Gate} (plan : PhaseLoweringPlan k hk pts hpts ops n U) : Bool :=
  let depth := planDepth plan
  let leaves := planLeafCount plan
  let ladderLen := (widthLadder ops n).length
  decide (depth = ladderLen - 1) && decide (leaves = q k ^ depth)

/-- Check 3, QFT variant: every `.split` node's left/right widths match E4's
own `splitM`-based formula (`left = w/2`, `right = w − w/2`). -/
partial def qftPlanSplits {k : ℕ} {hk : 1 < k} {ops : Prog k} {r : Reg} :
    QFTLoweringPlan k hk ops r → List (ℕ × ℕ × ℕ)
  | .empty _ _ => []
  | .singleton _ _ => []
  | .split r _ _ _ _ rightPlan leftPlan =>
      (regSize r, regSize (leftReg r), regSize (rightReg r)) ::
        (qftPlanSplits rightPlan ++ qftPlanSplits leftPlan)

def check3_qftSplit {k : ℕ} {hk : 1 < k} {ops : Prog k} {r : Reg} (plan : QFTLoweringPlan k hk ops r) :
    Bool :=
  (qftPlanSplits plan).all fun (w, l, rr) => decide (l = w / 2) && decide (rr = w - w / 2)

end Shor
