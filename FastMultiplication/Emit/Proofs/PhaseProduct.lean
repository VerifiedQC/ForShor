import FastMultiplication.Emit.Proofs.Correct
import FastMultiplication.Emit.Tests

/-!
# R6.2: `phase_product` correctness

`Emit/PLAN.md` §12.2–§12.3, for `r2_2_doc` (k = 2, `standard` table — the
`Doc` `Emit/Tests.lean`'s R2.2 section already pins and native_decide-checks
at two sample workspaces). Unlike `naive_leaf` (R6.1), this template
recurses (`Node.call "phase_product"` to itself) and its body depends on
register-slicing (`Node.cond`-guarded `zeroExtend`/`signExtend`/
`zeroDealloc`/`signDealloc` allocation/deallocation, plus `activeSlice`/
`reserveSlice`/`ext`/`grow` register expressions for each of the `k = 2`
chunks) — `§12.6`'s own risk assessment names this the most expensive part
of R6.

**Ground truth, established by direct inspection (not just reading the
extractor's meta-code) of `r2_2_doc`'s `"phase_product"` template body**
(57 `Node`s total): `body = .cond guard thenNode (.call "naive_leaf" …)`.
The `else` branch (base case) is a single `call` to `naive_leaf` — matching
`standardSignedPhaseLoweringPlan`'s `by_cases hrec : nextSignedWidth x z ops
< phaseInputSize x z`, where the *positive* branch (`hrec` true) is the
`PhaseLoweringPlan.signedStep` (recursive) case and the *negative* branch is
`signedBase` (`lowerGateRec (.signedBase …) = LowGate.Naive_SignedPhaseProd
phi x z`, exactly `evalNode_naive_leaf`'s target). The `then` branch's
leaf sequence (allocations; annotated-ops body; deallocations) was read off
directly and confirmed, op for op, against `r2_2_ops`'s 7 operations
(`[phaseProduct 0, addScaled 0 1 true 0, phaseProduct 0, addScaled 0 1
false 0, addScaled 0 1 false 0, phaseProduct 0, addScaled 0 1 true 0]`) and
`compileSignedAllocationsAux`/`compileAnnotatedOpsToSignedGateAux`/
`compileSignedDeallocationsAux`'s own recursion: 5 allocation leaves (`id,
cond(0=0,zeroExtend) × 2, cond(0=0,signExtend) × 2` for `x0,z0` non-top and
`x1,z1` top), 12 body leaves (`call, AddScaled × 2, call, AddScaled × 2,
AddScaled × 2, call, AddScaled × 2, id` — one `call(phase_product)` per
`phaseProduct` op, two `AddScaled` per `addScaled` op), 5 deallocation
leaves (`signDealloc × 2, zeroDealloc × 2, id`, top-first per
`compileSignedDeallocationsAux`'s decreasing order).
-/

namespace Shor.IR

open Shor.Emit.Tests (r2_2_k r2_2_hk r2_2_ops r2_2_doc)

/-- `phase_product`'s environment, parametrized over `phi` (unlike
`Tests.lean`'s `r2_2_env`, which hardcodes `r2_2_phi` — R2.2's smoke test
only needs one `phi`, but R6.2's theorem is for every `phi`). Otherwise
identical: `opaqueW`/`coeff` are the real `RecursivePhaseWorkspace`/
`cramerCoeffFromPtsWidth` functions against `r2_2_ops`/`r2_2_k`'s table,
exactly what `Tests.lean`'s `native_decide` checks already validate at
sample widths. -/
def ppEnv (x z : ExtReg) (phi : Angle) : Env :=
  { w := fun n =>
      if n == "xw" then some x.width
      else if n == "zw" then some z.width
      else if n == "xCap" then some x.capacity
      else if n == "zCap" then some z.capacity
      else none
    a := fun n => if n == "phi" then some phi else none
    r := fun n => if n == "x" then some x else if n == "z" then some z else none
    opaqueW := fun name args =>
      match name, args with
      | "nextWidth", [xw, zw] => some (RecursivePhaseWorkspace.nextWidth r2_2_ops xw zw)
      | "reserveNeed_x", [xw, zw] => some (RecursivePhaseWorkspace.reserveNeed r2_2_ops xw zw).1
      | "reserveNeed_z", [xw, zw] => some (RecursivePhaseWorkspace.reserveNeed r2_2_ops xw zw).2
      | _, _ => none
    coeff := fun l mv =>
      if h : l < q r2_2_k then
        some (cramerCoeffFromPtsWidth r2_2_k mv (tableInstance .standard r2_2_k r2_2_hk).points
          (tableInstance .standard r2_2_k r2_2_hk).hlen ⟨l, h⟩)
      else none }

/-- `RecursivePhaseWorkspace.nextWidth`, evaluated at a real register pair's
own widths, agrees with `nextSignedWidth` at those same registers — both
are width-only functions of `x.width`/`z.width` (`RecursivePhaseWorkspace`'s
own doc comment: "canonical extendable register used only for width
calculations"), so the specific registers don't matter, only their widths.
General (not tied to `r2_2_ops`/`k = 2`); lifted verbatim from
`canonicalSignedStep`'s own local proof of the same fact
(`Compiler/Workspace.lean`), which has no standalone name. -/
theorem nextWidth_eq_nextSignedWidth {k : ℕ} (ops : Prog k) (x z : ExtReg) :
    RecursivePhaseWorkspace.nextWidth ops x.width z.width = nextSignedWidth x z ops := by
  have hwmX : (RecursivePhaseWorkspace.widthModelX x.width).width = x.width := by
    simp [RecursivePhaseWorkspace.widthModelX, ExtReg.width, ExtReg.ofReg, regSize, Reg.width,
      Reg.interval]
  have hwmZ : (RecursivePhaseWorkspace.widthModelZ x.width z.width).width = z.width := by
    simp [RecursivePhaseWorkspace.widthModelZ, ExtReg.width, ExtReg.ofReg, regSize, Reg.width,
      Reg.interval]
  have hlimb :
      phaseLimbWidth (RecursivePhaseWorkspace.widthModelX x.width)
        (RecursivePhaseWorkspace.widthModelZ x.width z.width) k = phaseLimbWidth x z k := by
    simp only [phaseLimbWidth, hwmX, hwmZ]
  have hinit :
      initWidthState (RecursivePhaseWorkspace.widthModelX x.width)
        (RecursivePhaseWorkspace.widthModelZ x.width z.width) k = initWidthState x z k := by
    simp only [initWidthState, hwmX, hwmZ, hlimb]
  simp only [RecursivePhaseWorkspace.nextWidth, nextSignedWidth, scanNeededWidths, hinit]

/-- The extracted guard (`nextWidth < max xw zw`, D2's translation of
`nextSignedWidth x z ops < phaseInputSize x z`) evaluates to exactly the
real recursion condition, for every `x, z`. This is `evalNode_phase_product`
step 2 of `Emit/PLAN.md` §12.3. -/
theorem evalProp_phase_product_guard (x z : ExtReg) (phi : Angle) :
    evalProp (ppEnv x z phi) (.lt (.opaque "nextWidth" [.var "xw", .var "zw"])
      (.max (.var "xw") (.var "zw"))) =
      .ok (decide (nextSignedWidth x z r2_2_ops < phaseInputSize x z)) := by
  unfold ppEnv
  simp only [evalProp, evalW, evalWList, Except.instMonad, Monad.toBind, Except.bind, Except.pure]
  simp [phaseInputSize, nextWidth_eq_nextSignedWidth]

/-- The `phase_product` template's body, read directly off `r2_2_doc`
(confirmed by direct inspection, see the file docstring): `.cond guard
thenNode (.call "naive_leaf" [xw, zw] [phi] [x, z])`. Exposed as a `def` so
the base/recursive-case theorems don't each re-pay the cost of finding it in
`r2_2_doc.templates`. -/
def r2_2_ppBody : Node :=
  ((r2_2_doc.templates.find? (fun t => t.name == "phase_product")).getD
    { name := "?", wParams := [], aParams := [], rParams := [], body := .op "" [] [] none [],
      provenance := "" }).body

theorem instantiate_phase_product_eq_evalNode (x z : ExtReg) (phi : Angle) (fuel : ℕ) :
    IR.instantiate r2_2_doc "phase_product" (ppEnv x z phi) fuel =
      evalNode r2_2_doc fuel (ppEnv x z phi) r2_2_ppBody := by
  rfl

-- `r2_2_ppBody`'s three top-level pieces, extracted by projection so
-- `rfl` only has to check the outer `.cond` shape, never `r2_2_ppBody`'s
-- (large) `thenNode` subterm.
def r2_2_ppGuard : Prop' := match r2_2_ppBody with | .cond g _ _ => g | _ => .lt (.lit 0) (.lit 0)
def r2_2_ppThen : Node := match r2_2_ppBody with | .cond _ t _ => t | n => n
def r2_2_ppElse : Node := match r2_2_ppBody with | .cond _ _ e => e | n => n

theorem r2_2_ppBody_eq_cond : r2_2_ppBody = .cond r2_2_ppGuard r2_2_ppThen r2_2_ppElse := by
  rfl

theorem r2_2_ppGuard_eq :
    r2_2_ppGuard = .lt (.opaque "nextWidth" [.var "xw", .var "zw"]) (.max (.var "xw") (.var "zw")) := by
  rfl

-- `evalW`/`evalA`/`evalReg` at `ppEnv`'s registered variables, proven by
-- `unfold` + `rfl` rather than `simp [ppEnv, ...]`: a full `simp` call that
-- unfolds `ppEnv` loops (`ppEnv.eq_1` against `RecursivePhaseWorkspace.
-- reserveNeed_fst`/`lt_sup_iff`/`max_self` from the default simp set, none
-- of which are needed here) — isolating each projection into its own tiny
-- goal, with nothing else in scope, avoids ever exposing `opaqueW`'s
-- `RecursivePhaseWorkspace` references to a simp call at all.
theorem evalW_ppEnv_xw (x z : ExtReg) (phi : Angle) : evalW (ppEnv x z phi) (.var "xw") = .ok x.width := by
  unfold ppEnv evalW; rfl
theorem evalW_ppEnv_zw (x z : ExtReg) (phi : Angle) : evalW (ppEnv x z phi) (.var "zw") = .ok z.width := by
  unfold ppEnv evalW; rfl
theorem evalA_ppEnv_phi (x z : ExtReg) (phi : Angle) : evalA (ppEnv x z phi) (.var "phi") = .ok phi := by
  unfold ppEnv evalA; rfl
theorem evalReg_ppEnv_x (x z : ExtReg) (phi : Angle) : evalReg (ppEnv x z phi) (.var "x") = .ok x := by
  unfold ppEnv evalReg; rfl
theorem evalReg_ppEnv_z (x z : ExtReg) (phi : Angle) : evalReg (ppEnv x z phi) (.var "z") = .ok z := by
  unfold ppEnv evalReg; rfl

/-- `Env.call`'s result at `naive_leaf`'s parameter lists/values (`ppEnv
x z phi`'s `w`/`a`/`r` evaluated at `naive_leaf`'s `wArgs`/`aArgs`/`rArgs`,
literally `[x.width, z.width]`/`[phi]`/`[x, z]`) has the same `w`/`a`/`r`
fields as `naiveLeafEnv x z phi`, carrying `ppEnv`'s `opaqueW`/`coeff`
through unchanged (`Env.call`'s doc comment) rather than resetting them —
see `naiveLeafEnv`'s doc comment in `Correct.lean` for why that's fine. -/
theorem envCall_naive_leaf_eq (x z : ExtReg) (phi : Angle) :
    Env.call (ppEnv x z phi) ["xw", "zw"] [x.width, z.width] ["phi"] [phi] ["x", "z"] [x, z] =
      naiveLeafEnv x z phi (ppEnv x z phi).opaqueW (ppEnv x z phi).coeff := by
  unfold Env.call naiveLeafEnv
  congr 1
  · funext n
    by_cases hxw : n = "xw"
    · subst hxw; simp [List.lookup_cons]
    · have hxw' : (n == "xw") = false := by simpa using hxw
      by_cases hzw : n = "zw"
      · subst hzw; simp [List.lookup_cons, hxw']
      · have hzw' : (n == "zw") = false := by simpa using hzw
        simp [List.lookup_cons, hxw, hzw, hxw', hzw']
  · funext n
    by_cases hphi : n = "phi"
    · subst hphi; simp [List.lookup_cons]
    · have hphi' : (n == "phi") = false := by simpa using hphi
      simp [List.lookup_cons, hphi, hphi']
  · funext n
    by_cases hx : n = "x"
    · subst hx; simp [List.lookup_cons]
    · have hx' : (n == "x") = false := by simpa using hx
      by_cases hz : n = "z"
      · subst hz; simp [List.lookup_cons, hx']
      · have hz' : (n == "z") = false := by simpa using hz
        simp [List.lookup_cons, hx, hz, hx', hz']

theorem r2_2_ppElse_eq :
    r2_2_ppElse = .call "naive_leaf" [.var "xw", .var "zw"] [.var "phi"] [.var "x", .var "z"] := by
  rfl

/-- R6.2's base-case step (`Emit/PLAN.md` §12.3, step 3): when the guard is
false, `phase_product`'s extracted body evaluates its `.call "naive_leaf"`
branch. The callee environment (`Env.call`) has the same `w`/`a`/`r` fields
as `naiveLeafEnv x z phi`, differing only in `opaqueW`/`coeff` (carried over
from `ppEnv`, per `Env.call`'s own doc comment) — irrelevant, since
`naive_leaf`'s body has no `.opaque`/`.coeff` subexpression
(`naiveLeafEnv`'s doc comment in `Correct.lean`). So this reduces directly
to `evalNode_naive_leaf`. -/
theorem evalNode_phase_product_base (x z : ExtReg) (phi : Angle) (fuel : ℕ) (hfuel : fuel ≠ 0)
    (hnotrec : ¬ nextSignedWidth x z r2_2_ops < phaseInputSize x z) :
    ∃ g, evalNode r2_2_doc fuel (ppEnv x z phi) r2_2_ppBody = .ok g ∧
      g.flattenSeq = (LowGate.Naive_SignedPhaseProd phi x z).flattenSeq := by
  have hlookup :
      r2_2_doc.templates.find? (fun t => t.name == "naive_leaf") =
        some Reflect.naiveLeafTemplate := by
    rfl
  have hcall : evalNode r2_2_doc fuel (ppEnv x z phi) r2_2_ppBody =
      evalNode r2_2_doc (fuel - 1)
        (naiveLeafEnv x z phi (ppEnv x z phi).opaqueW (ppEnv x z phi).coeff)
        Reflect.naiveLeafTemplate.body := by
    simp only [r2_2_ppBody_eq_cond, evalNode, r2_2_ppGuard_eq, evalProp_phase_product_guard,
      decide_eq_false hnotrec, r2_2_ppElse_eq, hfuel, hlookup, Reflect.naiveLeafTemplate,
      Bool.false_eq_true, if_false,
      evalW_ppEnv_xw, evalW_ppEnv_zw, evalA_ppEnv_phi, evalReg_ppEnv_x, evalReg_ppEnv_z,
      List.mapM_cons, List.mapM_nil, Except.instMonad, Monad.toBind, Except.bind, Except.pure]
    rw [envCall_naive_leaf_eq]
  rw [hcall]
  exact evalNode_naive_leaf x z phi r2_2_doc (fuel - 1) (ppEnv x z phi).opaqueW (ppEnv x z phi).coeff

/-! ## The `hrec` (recursive) branch: register-slicing

`Emit/PLAN.md` §12.6's own risk assessment names this the most expensive
part of R6: showing the `k = 2` chunks the extractor sliced out of `x`/`z`
(`.ext (.activeSlice …) (.reserveSlice …)`, `precomputePhaseProductSlots` in
`Reflect/Targets.lean`) are the *same registers* `canonicalSignedStep`'s
concrete layout (`Compiler/Workspace.lean`) actually builds
(`PhaseSplitLayout.ofBudget` over a `ReserveBudget.ofRequirements`). This
turned out to be provable by `rfl`/`simp` rather than needing the general
`fillSlack`/prefix-sum induction lemmas `Compiler/Workspace.lean` proves for
*symbolic* `k`: `r2_2_k = 2` is concrete, so `List.ofFn`/`Fin.cases` over it
compute directly once `canonicalSignedStep` itself is unfolded — confirmed
empirically (`(canonicalSignedStep …).layout.xSplit.reserve i` for a literal
`i` closes via a bare `rfl` in ~2s, no induction needed at all). -/

-- Ground truth (direct inspection, same method as the guard/base case
-- above): `r2_2_ppThen`'s allocation/body/deallocation leaves all reference
-- exactly four register subexpressions (`ext0x, ext1x, ext0z, ext1z`, one
-- per `(side, chunk)` pair) and their four `grow` counterparts
-- (`grow(extNy, nextWidth - widthAt(extNy))`, used in the recursive `call`s'
-- `rArgs` and every `AddScaled`). `opRegsByName` extracts them by walking
-- the tree for a named op's `regs`/first arg, so the extraction is
-- `rfl`-checked against the real `r2_2_ppThen`, never hand-transcribed.
mutual
def Node.opRegsByName (name : String) : Node → List (List RegExpr)
  | .op n regs _ _ _ => if n == name then [regs] else []
  | .seq ns => Node.opRegsByNameList name ns
  | .cond _ t e => Node.opRegsByName name t ++ Node.opRegsByName name e
  | .call _ _ _ _ => []
  | .adj n => Node.opRegsByName name n
  | .loop _ _ _ n => Node.opRegsByName name n
def Node.opRegsByNameList (name : String) : List Node → List (List RegExpr)
  | [] => []
  | n :: ns => Node.opRegsByName name n ++ Node.opRegsByNameList name ns
end

/-- The `k = 2` limb width, exactly `Reflect/Targets.lean`'s `translateW`
output for `phaseLimbWidth x z 2`. -/
def limbW : WExpr := .min (.div (.var "xw") (.lit 2)) (.div (.var "zw") (.lit 2))
def nextWidthW : WExpr := .opaque "nextWidth" [.var "xw", .var "zw"]
def reserveNeedXW : WExpr := .opaque "reserveNeed_x" [nextWidthW, nextWidthW]
def reserveNeedZW : WExpr := .opaque "reserveNeed_z" [nextWidthW, nextWidthW]

def r2_2_ext0x : RegExpr := ((Node.opRegsByName "zeroExtend" r2_2_ppThen).getD 0 []).getD 0 (.var "?")
def r2_2_ext0z : RegExpr := ((Node.opRegsByName "zeroExtend" r2_2_ppThen).getD 1 []).getD 0 (.var "?")
def r2_2_ext1x : RegExpr := ((Node.opRegsByName "signExtend" r2_2_ppThen).getD 0 []).getD 0 (.var "?")
def r2_2_ext1z : RegExpr := ((Node.opRegsByName "signExtend" r2_2_ppThen).getD 1 []).getD 0 (.var "?")

theorem r2_2_ext0x_eq : r2_2_ext0x =
    .ext (.activeSlice (.var "x") (.mul (.lit 0) limbW) (.add (.mul (.lit 0) limbW) limbW))
      (.reserveSlice (.var "x") (.lit 0) (.add (.lit 0) (.add (.sub nextWidthW limbW) reserveNeedXW))) := by
  rfl

theorem r2_2_ext0z_eq : r2_2_ext0z =
    .ext (.activeSlice (.var "z") (.mul (.lit 0) limbW) (.add (.mul (.lit 0) limbW) limbW))
      (.reserveSlice (.var "z") (.lit 0) (.add (.lit 0) (.add (.sub nextWidthW limbW) reserveNeedZW))) := by
  rfl

def r2_2_offsetX1W : WExpr := .add (.lit 0) (.add (.sub nextWidthW limbW) reserveNeedXW)
def r2_2_sizeX1W : WExpr :=
  .add (.add (.sub nextWidthW (.sub (.var "xw") (.mul (.lit 1) limbW))) reserveNeedXW)
    (.sub (.var "xCap")
      (.add r2_2_offsetX1W (.add (.sub nextWidthW (.sub (.var "xw") (.mul (.lit 1) limbW))) reserveNeedXW)))

theorem r2_2_ext1x_eq : r2_2_ext1x =
    .ext (.activeSlice (.var "x") (.mul (.lit 1) limbW)
        (.add (.mul (.lit 1) limbW) (.sub (.var "xw") (.mul (.lit 1) limbW))))
      (.reserveSlice (.var "x") r2_2_offsetX1W (.add r2_2_offsetX1W r2_2_sizeX1W)) := by
  rfl

def r2_2_offsetZ1W : WExpr := .add (.lit 0) (.add (.sub nextWidthW limbW) reserveNeedZW)
def r2_2_sizeZ1W : WExpr :=
  .add (.add (.sub nextWidthW (.sub (.var "zw") (.mul (.lit 1) limbW))) reserveNeedZW)
    (.sub (.var "zCap")
      (.add r2_2_offsetZ1W (.add (.sub nextWidthW (.sub (.var "zw") (.mul (.lit 1) limbW))) reserveNeedZW)))

theorem r2_2_ext1z_eq : r2_2_ext1z =
    .ext (.activeSlice (.var "z") (.mul (.lit 1) limbW)
        (.add (.mul (.lit 1) limbW) (.sub (.var "zw") (.mul (.lit 1) limbW))))
      (.reserveSlice (.var "z") r2_2_offsetZ1W (.add r2_2_offsetZ1W r2_2_sizeZ1W)) := by
  rfl

/-- The extracted `ext0x` register expression, instantiated, is exactly the
real layout's chunk-0 `x` child — for *every* `x, z`, not just the sampled
widths R2.2's `native_decide` check covers. The disjointness side-condition
(`.ext`'s `if h : Disjoint … then …`) is supplied by
`PhaseSplitLayout.active_reserve_disjoint`, `canonicalSignedStep`'s own
layout field, normalized (via the same `simp` set used on the goal) to the
identical concrete shape so it applies directly — no separate case split on
whether the registers are disjoint is needed. -/
theorem evalReg_pp_ext0x (x z : ExtReg) (phi : Angle)
    (hrec : nextSignedWidth x z r2_2_ops < phaseInputSize x z)
    (hworkspace : SignedRecursiveWorkspaceOK r2_2_ops x z) :
    evalReg (ppEnv x z phi) r2_2_ext0x =
      .ok ((canonicalSignedStep r2_2_hk r2_2_ops x z hrec hworkspace).layout.xSplit.child 0) := by
  have hdisj := (canonicalSignedStep r2_2_hk r2_2_ops x z hrec hworkspace).layout.xSplit.active_reserve_disjoint 0
  simp [-RecursivePhaseWorkspace.reserveNeed_fst, -RecursivePhaseWorkspace.reserveNeed_snd,
    phaseChunkActive, phaseChunkStart, phaseSplitLogicalWidth, isTopChunk, r2_2_k, phaseLimbWidth,
    phaseLimbWidthOfWidth, canonicalSignedStep, PhaseSplitLayout.ofBudget, ReserveBudget.topIndex,
    ReserveBudget.ofRequirements, ReserveBudget.childReserve, ReserveBudget.offset, ReserveBudget.fillSlack,
    RecursivePhaseWorkspace.requiredXChildReserve, RecursivePhaseWorkspace.requiredChildReserve,
    RecursivePhaseWorkspace.PhaseSide.width, RecursivePhaseWorkspace.PhaseSide.reserveComponent,
    RecursivePhaseWorkspace.limbWidth, RecursivePhaseWorkspace.widthModelX, RecursivePhaseWorkspace.widthModelZ,
    Reg.interval, ExtReg.width, ExtReg.ofReg, regSize, Reg.width, List.length_range, List.length_map] at hdisj
  rw [r2_2_ext0x_eq]
  unfold ppEnv
  simp [-RecursivePhaseWorkspace.reserveNeed_fst, -RecursivePhaseWorkspace.reserveNeed_snd,
    evalReg, evalW, evalWList, limbW, nextWidthW, reserveNeedXW, ExtReg.ofReg, phaseChunkActive, phaseChunkStart,
    phaseSplitLogicalWidth, isTopChunk, PhaseSplitLayout.child, r2_2_k, phaseLimbWidth,
    phaseLimbWidthOfWidth, canonicalSignedStep, PhaseSplitLayout.ofBudget, ReserveBudget.topIndex,
    ReserveBudget.ofRequirements, ReserveBudget.childReserve, ReserveBudget.offset, ReserveBudget.fillSlack,
    RecursivePhaseWorkspace.requiredXChildReserve, RecursivePhaseWorkspace.requiredChildReserve,
    RecursivePhaseWorkspace.PhaseSide.width, RecursivePhaseWorkspace.PhaseSide.reserveComponent,
    RecursivePhaseWorkspace.limbWidth, RecursivePhaseWorkspace.widthModelX, RecursivePhaseWorkspace.widthModelZ,
    Reg.interval, ExtReg.width, regSize, Reg.width, List.length_range, List.length_map,
    Except.instMonad, Monad.toBind, Except.bind, Except.pure, Except.map, hdisj]

/-- Same as `evalReg_pp_ext0x`, `z`'s chunk 0. -/
theorem evalReg_pp_ext0z (x z : ExtReg) (phi : Angle)
    (hrec : nextSignedWidth x z r2_2_ops < phaseInputSize x z)
    (hworkspace : SignedRecursiveWorkspaceOK r2_2_ops x z) :
    evalReg (ppEnv x z phi) r2_2_ext0z =
      .ok ((canonicalSignedStep r2_2_hk r2_2_ops x z hrec hworkspace).layout.zSplit.child 0) := by
  have hdisj := (canonicalSignedStep r2_2_hk r2_2_ops x z hrec hworkspace).layout.zSplit.active_reserve_disjoint 0
  simp [-RecursivePhaseWorkspace.reserveNeed_fst, -RecursivePhaseWorkspace.reserveNeed_snd,
    phaseChunkActive, phaseChunkStart, phaseSplitLogicalWidth, isTopChunk, r2_2_k, phaseLimbWidth,
    phaseLimbWidthOfWidth, canonicalSignedStep, PhaseSplitLayout.ofBudget, ReserveBudget.topIndex,
    ReserveBudget.ofRequirements, ReserveBudget.childReserve, ReserveBudget.offset, ReserveBudget.fillSlack,
    RecursivePhaseWorkspace.requiredZChildReserve, RecursivePhaseWorkspace.requiredChildReserve,
    RecursivePhaseWorkspace.PhaseSide.width, RecursivePhaseWorkspace.PhaseSide.reserveComponent,
    RecursivePhaseWorkspace.limbWidth, RecursivePhaseWorkspace.widthModelX, RecursivePhaseWorkspace.widthModelZ,
    Reg.interval, ExtReg.width, ExtReg.ofReg, regSize, Reg.width, List.length_range, List.length_map] at hdisj
  rw [r2_2_ext0z_eq]
  unfold ppEnv
  simp [-RecursivePhaseWorkspace.reserveNeed_fst, -RecursivePhaseWorkspace.reserveNeed_snd,
    evalReg, evalW, evalWList, limbW, nextWidthW, reserveNeedZW, ExtReg.ofReg, phaseChunkActive, phaseChunkStart,
    phaseSplitLogicalWidth, isTopChunk, PhaseSplitLayout.child, r2_2_k, phaseLimbWidth,
    phaseLimbWidthOfWidth, canonicalSignedStep, PhaseSplitLayout.ofBudget, ReserveBudget.topIndex,
    ReserveBudget.ofRequirements, ReserveBudget.childReserve, ReserveBudget.offset, ReserveBudget.fillSlack,
    RecursivePhaseWorkspace.requiredZChildReserve, RecursivePhaseWorkspace.requiredChildReserve,
    RecursivePhaseWorkspace.PhaseSide.width, RecursivePhaseWorkspace.PhaseSide.reserveComponent,
    RecursivePhaseWorkspace.limbWidth, RecursivePhaseWorkspace.widthModelX, RecursivePhaseWorkspace.widthModelZ,
    Reg.interval, ExtReg.width, regSize, Reg.width, List.length_range, List.length_map,
    Except.instMonad, Monad.toBind, Except.bind, Except.pure, Except.map, hdisj]

/-- Same as `evalReg_pp_ext0x`, `x`'s chunk 1 — the *top* chunk (`fillSlack`'s
`Function.update` case), which absorbs both the width remainder
(`phaseSplitLogicalWidth`'s `isTopChunk` branch) and the reserve slack
(`ReserveBudget.ofRequirements`'s `capacity - used`); the same `simp` set
that handled chunk 0's plain case discharges both automatically. -/
theorem evalReg_pp_ext1x (x z : ExtReg) (phi : Angle)
    (hrec : nextSignedWidth x z r2_2_ops < phaseInputSize x z)
    (hworkspace : SignedRecursiveWorkspaceOK r2_2_ops x z) :
    evalReg (ppEnv x z phi) r2_2_ext1x =
      .ok ((canonicalSignedStep r2_2_hk r2_2_ops x z hrec hworkspace).layout.xSplit.child 1) := by
  have hdisj := (canonicalSignedStep r2_2_hk r2_2_ops x z hrec hworkspace).layout.xSplit.active_reserve_disjoint 1
  simp [-RecursivePhaseWorkspace.reserveNeed_fst, -RecursivePhaseWorkspace.reserveNeed_snd,
    phaseChunkActive, phaseChunkStart, phaseSplitLogicalWidth, isTopChunk, r2_2_k, phaseLimbWidth,
    phaseLimbWidthOfWidth, canonicalSignedStep, PhaseSplitLayout.ofBudget, ReserveBudget.topIndex,
    ReserveBudget.ofRequirements, ReserveBudget.childReserve, ReserveBudget.offset, ReserveBudget.fillSlack,
    RecursivePhaseWorkspace.requiredXChildReserve, RecursivePhaseWorkspace.requiredChildReserve,
    RecursivePhaseWorkspace.PhaseSide.width, RecursivePhaseWorkspace.PhaseSide.reserveComponent,
    RecursivePhaseWorkspace.limbWidth, RecursivePhaseWorkspace.widthModelX, RecursivePhaseWorkspace.widthModelZ,
    Reg.interval, ExtReg.width, ExtReg.ofReg, regSize, Reg.width, List.length_range, List.length_map] at hdisj
  rw [r2_2_ext1x_eq]
  unfold ppEnv
  simp [-RecursivePhaseWorkspace.reserveNeed_fst, -RecursivePhaseWorkspace.reserveNeed_snd,
    evalReg, evalW, evalWList, limbW, nextWidthW, reserveNeedXW, r2_2_offsetX1W, r2_2_sizeX1W, ExtReg.ofReg,
    phaseChunkActive, phaseChunkStart, phaseSplitLogicalWidth, isTopChunk, PhaseSplitLayout.child, r2_2_k,
    phaseLimbWidth, phaseLimbWidthOfWidth, canonicalSignedStep, PhaseSplitLayout.ofBudget, ReserveBudget.topIndex,
    ReserveBudget.ofRequirements, ReserveBudget.childReserve, ReserveBudget.offset, ReserveBudget.fillSlack,
    RecursivePhaseWorkspace.requiredXChildReserve, RecursivePhaseWorkspace.requiredChildReserve,
    RecursivePhaseWorkspace.PhaseSide.width, RecursivePhaseWorkspace.PhaseSide.reserveComponent,
    RecursivePhaseWorkspace.limbWidth, RecursivePhaseWorkspace.widthModelX, RecursivePhaseWorkspace.widthModelZ,
    Reg.interval, ExtReg.width, regSize, Reg.width, List.length_range, List.length_map,
    Except.instMonad, Monad.toBind, Except.bind, Except.pure, Except.map, hdisj]

/-- Same as `evalReg_pp_ext1x`, `z`'s chunk 1. -/
theorem evalReg_pp_ext1z (x z : ExtReg) (phi : Angle)
    (hrec : nextSignedWidth x z r2_2_ops < phaseInputSize x z)
    (hworkspace : SignedRecursiveWorkspaceOK r2_2_ops x z) :
    evalReg (ppEnv x z phi) r2_2_ext1z =
      .ok ((canonicalSignedStep r2_2_hk r2_2_ops x z hrec hworkspace).layout.zSplit.child 1) := by
  have hdisj := (canonicalSignedStep r2_2_hk r2_2_ops x z hrec hworkspace).layout.zSplit.active_reserve_disjoint 1
  simp [-RecursivePhaseWorkspace.reserveNeed_fst, -RecursivePhaseWorkspace.reserveNeed_snd,
    phaseChunkActive, phaseChunkStart, phaseSplitLogicalWidth, isTopChunk, r2_2_k, phaseLimbWidth,
    phaseLimbWidthOfWidth, canonicalSignedStep, PhaseSplitLayout.ofBudget, ReserveBudget.topIndex,
    ReserveBudget.ofRequirements, ReserveBudget.childReserve, ReserveBudget.offset, ReserveBudget.fillSlack,
    RecursivePhaseWorkspace.requiredZChildReserve, RecursivePhaseWorkspace.requiredChildReserve,
    RecursivePhaseWorkspace.PhaseSide.width, RecursivePhaseWorkspace.PhaseSide.reserveComponent,
    RecursivePhaseWorkspace.limbWidth, RecursivePhaseWorkspace.widthModelX, RecursivePhaseWorkspace.widthModelZ,
    Reg.interval, ExtReg.width, ExtReg.ofReg, regSize, Reg.width, List.length_range, List.length_map] at hdisj
  rw [r2_2_ext1z_eq]
  unfold ppEnv
  simp [-RecursivePhaseWorkspace.reserveNeed_fst, -RecursivePhaseWorkspace.reserveNeed_snd,
    evalReg, evalW, evalWList, limbW, nextWidthW, reserveNeedZW, r2_2_offsetZ1W, r2_2_sizeZ1W, ExtReg.ofReg,
    phaseChunkActive, phaseChunkStart, phaseSplitLogicalWidth, isTopChunk, PhaseSplitLayout.child, r2_2_k,
    phaseLimbWidth, phaseLimbWidthOfWidth, canonicalSignedStep, PhaseSplitLayout.ofBudget, ReserveBudget.topIndex,
    ReserveBudget.ofRequirements, ReserveBudget.childReserve, ReserveBudget.offset, ReserveBudget.fillSlack,
    RecursivePhaseWorkspace.requiredZChildReserve, RecursivePhaseWorkspace.requiredChildReserve,
    RecursivePhaseWorkspace.PhaseSide.width, RecursivePhaseWorkspace.PhaseSide.reserveComponent,
    RecursivePhaseWorkspace.limbWidth, RecursivePhaseWorkspace.widthModelX, RecursivePhaseWorkspace.widthModelZ,
    Reg.interval, ExtReg.width, regSize, Reg.width, List.length_range, List.length_map,
    Except.instMonad, Monad.toBind, Except.bind, Except.pure, Except.map, hdisj]

/-! ## The `hrec` branch: `.grow` lemmas

The compiled body (`compileAnnotatedOpsToSignedGateAux`) and the recursive
`call` leaves operate on the *grown* slots (`targetSignedLayoutState`'s
`growExtRegTo (child i) Wwork`), not the bare split children `ext0x`
etc. above. The extractor represents this as `.grow (extNy) (nextWidth −
widthAt extNy)` (`precomputePhaseProductSlots`). The width target,
`Wwork = commonNeededWidth need`, turns out to be *definitionally*
`nextSignedWidth x z ops` (`Compiler/Widths.lean`:
`nextSignedWidth x z ops := commonNeededWidth (scanNeededWidths x z ops)`),
which is exactly what the extracted delta's `nextWidth` opaque call
evaluates to (`nextWidth_eq_nextSignedWidth`) — so no new arithmetic fact
about `commonNeededWidth`/`scanNeededWidths` is needed at all, only
`growExtRegTo`'s own definition (`e.grow (W - e.width)`) matching
`evalReg`'s `.grow` case verbatim once the width delta is known. -/

theorem evalW_pp_nextWidth (x z : ExtReg) (phi : Angle) :
    evalW (ppEnv x z phi) nextWidthW = .ok (nextSignedWidth x z r2_2_ops) := by
  have h : evalW (ppEnv x z phi) nextWidthW =
      .ok (RecursivePhaseWorkspace.nextWidth r2_2_ops x.width z.width) := by
    show evalW (ppEnv x z phi) (.opaque "nextWidth" [.var "xw", .var "zw"]) = _
    unfold ppEnv evalW evalWList
    rfl
  rw [h, nextWidth_eq_nextSignedWidth]

theorem evalW_pp_limbW (x z : ExtReg) (phi : Angle) :
    evalW (ppEnv x z phi) limbW = .ok (phaseLimbWidth x z r2_2_k) := by
  show evalW (ppEnv x z phi) (.min (.div (.var "xw") (.lit 2)) (.div (.var "zw") (.lit 2))) = _
  unfold ppEnv evalW
  rfl

/-- Chunk 0's width, for either side, is exactly `phaseLimbWidth x z 2`
(the non-top case of `phaseSplitLogicalWidth`). -/
theorem child_width_0 {parent : ExtReg} {W : ℕ} (layout : PhaseSplitLayout parent 2 W) :
    (layout.child 0).width = W := by
  rw [PhaseSplitLayout.child_width]
  simp [phaseSplitLogicalWidth, isTopChunk]

/-- Chunk 1's width, for either side, is `parent.width - phaseLimbWidth x z 2`
(the top case of `phaseSplitLogicalWidth`, `k = 2` so chunk 1 is `isTopChunk`). -/
theorem child_width_1 {parent : ExtReg} {W : ℕ} (layout : PhaseSplitLayout parent 2 W) :
    (layout.child 1).width = parent.width - W := by
  rw [PhaseSplitLayout.child_width]
  simp [phaseSplitLogicalWidth, isTopChunk]

def r2_2_growDeltaX0W : WExpr := .sub nextWidthW limbW
def r2_2_growDeltaZ0W : WExpr := .sub nextWidthW limbW
def r2_2_growDeltaX1W : WExpr := .sub nextWidthW (.sub (.var "xw") limbW)
def r2_2_growDeltaZ1W : WExpr := .sub nextWidthW (.sub (.var "zw") limbW)

-- Ground truth (same method as above): every `.grow` occurrence in
-- `r2_2_ppThen` pairs one of the four `extNy` register expressions with
-- exactly one of these four delta expressions (confirmed by direct
-- inspection of `r2_2_ppThen`'s three `call` leaves and eight `AddScaled`
-- leaves — every `.grow` there is syntactically one of `grow(ext0x,
-- growDeltaX0W)`, `grow(ext0z, growDeltaZ0W)`, `grow(ext1x, growDeltaX1W)`,
-- `grow(ext1z, growDeltaZ1W)`, never a fifth shape).
theorem evalReg_pp_grow0x (x z : ExtReg) (phi : Angle)
    (hrec : nextSignedWidth x z r2_2_ops < phaseInputSize x z)
    (hworkspace : SignedRecursiveWorkspaceOK r2_2_ops x z) :
    evalReg (ppEnv x z phi) (.grow r2_2_ext0x r2_2_growDeltaX0W) =
      .ok (growExtRegTo ((canonicalSignedStep r2_2_hk r2_2_ops x z hrec hworkspace).layout.xSplit.child 0)
        (nextSignedWidth x z r2_2_ops)) := by
  unfold r2_2_growDeltaX0W growExtRegTo
  simp only [evalReg, evalW, evalReg_pp_ext0x x z phi hrec hworkspace, evalW_pp_nextWidth,
    evalW_pp_limbW, child_width_0, Except.instMonad, Monad.toBind, Except.bind, Except.pure]

theorem evalReg_pp_grow0z (x z : ExtReg) (phi : Angle)
    (hrec : nextSignedWidth x z r2_2_ops < phaseInputSize x z)
    (hworkspace : SignedRecursiveWorkspaceOK r2_2_ops x z) :
    evalReg (ppEnv x z phi) (.grow r2_2_ext0z r2_2_growDeltaZ0W) =
      .ok (growExtRegTo ((canonicalSignedStep r2_2_hk r2_2_ops x z hrec hworkspace).layout.zSplit.child 0)
        (nextSignedWidth x z r2_2_ops)) := by
  unfold r2_2_growDeltaZ0W growExtRegTo
  simp only [evalReg, evalW, evalReg_pp_ext0z x z phi hrec hworkspace, evalW_pp_nextWidth,
    evalW_pp_limbW, child_width_0, Except.instMonad, Monad.toBind, Except.bind, Except.pure]

theorem evalReg_pp_grow1x (x z : ExtReg) (phi : Angle)
    (hrec : nextSignedWidth x z r2_2_ops < phaseInputSize x z)
    (hworkspace : SignedRecursiveWorkspaceOK r2_2_ops x z) :
    evalReg (ppEnv x z phi) (.grow r2_2_ext1x r2_2_growDeltaX1W) =
      .ok (growExtRegTo ((canonicalSignedStep r2_2_hk r2_2_ops x z hrec hworkspace).layout.xSplit.child 1)
        (nextSignedWidth x z r2_2_ops)) := by
  unfold r2_2_growDeltaX1W growExtRegTo
  simp only [evalReg, evalReg_pp_ext1x x z phi hrec hworkspace, evalW_pp_nextWidth,
    evalW_pp_limbW, evalW, child_width_1,
    Except.instMonad, Monad.toBind, Except.bind, Except.pure]
  rfl

theorem evalReg_pp_grow1z (x z : ExtReg) (phi : Angle)
    (hrec : nextSignedWidth x z r2_2_ops < phaseInputSize x z)
    (hworkspace : SignedRecursiveWorkspaceOK r2_2_ops x z) :
    evalReg (ppEnv x z phi) (.grow r2_2_ext1z r2_2_growDeltaZ1W) =
      .ok (growExtRegTo ((canonicalSignedStep r2_2_hk r2_2_ops x z hrec hworkspace).layout.zSplit.child 1)
        (nextSignedWidth x z r2_2_ops)) := by
  unfold r2_2_growDeltaZ1W growExtRegTo
  simp only [evalReg, evalReg_pp_ext1z x z phi hrec hworkspace, evalW_pp_nextWidth,
    evalW_pp_limbW, evalW, child_width_1,
    Except.instMonad, Monad.toBind, Except.bind, Except.pure]
  rfl

/-! ## The `hrec` branch: the annotated-ops body's angle coefficients

`compileAnnotatedOpsToSignedGateAux`'s `.phaseProduct` case scales `phi` by
`phaseCoeff l = loweringPhaseCoeff r2_2_k x z pts hpts l`, one per
interpolation-term index `l` assigned by `annotatePhaseTermsAux`
(`Emit/PLAN.md` §12.3 step 4's "`evalA (coeff phi l m) = phi *
loweringPhaseCoeff …`" lemma). The extractor represents this as
`.coeff (.var "phi") l limbW` (`Reflect/Extract.lean`'s `Registry.coeffMExpr`
convention: the width argument is always the limb width). -/
theorem evalA_pp_coeff (x z : ExtReg) (phi : Angle) (l : ℕ) (hl : l < q r2_2_k) :
    evalA (ppEnv x z phi) (.coeff (.var "phi") l limbW) =
      .ok (phi * loweringPhaseCoeff r2_2_k x z (genInterpolationPoints r2_2_k)
        (generatedInterpolationPoints_length r2_2_k) ⟨l, hl⟩) := by
  have hpts : (tableInstance .standard r2_2_k r2_2_hk).points = genInterpolationPoints r2_2_k := rfl
  have hhlen : (tableInstance .standard r2_2_k r2_2_hk).hlen =
      hpts ▸ generatedInterpolationPoints_length r2_2_k := rfl
  show evalA (ppEnv x z phi) (AExpr.coeff (.var "phi") l limbW) = _
  simp only [evalA, evalA_ppEnv_phi, evalW_pp_limbW, ppEnv, hl, dite_true,
    Except.instMonad, Monad.toBind, Except.bind, Except.pure, loweringPhaseCoeff]
  congr 2

theorem lowerGateRec_standardSignedPhaseLoweringPlan_base
    (x z : ExtReg) (phi : Angle) (hworkspace : SignedRecursiveWorkspaceOK r2_2_ops x z)
    (hnotrec : ¬ nextSignedWidth x z r2_2_ops < phaseInputSize x z) :
    lowerGateRec (standardSignedPhaseLoweringPlan r2_2_k r2_2_hk phi x z r2_2_ops hworkspace) =
      LowGate.Naive_SignedPhaseProd phi x z := by
  rw [standardSignedPhaseLoweringPlan.eq_1, dif_neg hnotrec, PhaseLoweringPlan.lowerGateRec_signedBase]

/-- `evalNode_phase_product_base`, restated against `lowerGateRec
(standardSignedPhaseLoweringPlan ...)` directly — the shape
`evalNode_phase_product_correct`'s base case needs, matching §12.2's stated
RHS rather than the intermediate `Naive_SignedPhaseProd` `evalNode_naive_leaf`
itself produces. -/
theorem evalNode_phase_product_base' (x z : ExtReg) (phi : Angle) (fuel : ℕ) (hfuel : fuel ≠ 0)
    (hworkspace : SignedRecursiveWorkspaceOK r2_2_ops x z)
    (hnotrec : ¬ nextSignedWidth x z r2_2_ops < phaseInputSize x z) :
    ∃ g, evalNode r2_2_doc fuel (ppEnv x z phi) r2_2_ppBody = .ok g ∧
      g.flattenSeq =
        (lowerGateRec
          (standardSignedPhaseLoweringPlan r2_2_k r2_2_hk phi x z r2_2_ops hworkspace)).flattenSeq := by
  obtain ⟨g, hg, hflat⟩ := evalNode_phase_product_base x z phi fuel hfuel hnotrec
  refine ⟨g, hg, ?_⟩
  rw [hflat, lowerGateRec_standardSignedPhaseLoweringPlan_base x z phi hworkspace hnotrec]

/-! ## The `hrec` branch: the `.capacity` gap

`ppEnv`'s `w` field maps `"xCap"`/`"zCap"` to `x.capacity`/`z.capacity`, and
the recursive `.call "phase_product"` leaves' `wArgs` include
`reserveNeedXW`/`reserveNeedZW` in those slots — so connecting `Env.call` at
those leaves to the real child environment needs a fact about how
`ExtReg.grow`/`growExtRegTo` changes `.capacity`, not just `.width`
(`width_growExtRegTo` in `Compiler/Layout.lean` only covers the width side).
-/

/-- `PhaseSplitLayout.child`'s `.capacity` is exactly `regSize (layout.reserve
i)` — `ExtReg.withReserve`'s second field is `layout.reserve i` verbatim, no
further slicing. General, not tied to `k = 2`. -/
theorem PhaseSplitLayout.child_capacity {parent : ExtReg} {k W : ℕ}
    (layout : PhaseSplitLayout parent k W) (i : Fin k) :
    (layout.child i).capacity = regSize (layout.reserve i) := by
  rfl

-- Chunk 0's concrete reserve capacity, for either side, is exactly
-- `requiredXChildReserve`/`requiredZChildReserve` with no slack adjustment
-- (chunk 0 is never the `fillSlack` top chunk for `r2_2_k = 2`) — the same
-- `simp` set `evalReg_pp_ext0x`/`evalReg_pp_ext0z` already use to unfold
-- `canonicalSignedStep`'s layout, applied to `.capacity` instead of the
-- active slice, plus the fit bound below to avoid `List.take` truncation.

/-- `canonicalSignedStep`'s own local proof that the `x`-side requirements fit
the parent's capacity (`Compiler/Workspace.lean` `hxfit`, not exposed as a
standalone lemma) — re-derived here from the exposed pieces
(`requiredXChildReserve_sum`, `hworkspace.x_reserve_sufficient`,
`reserveNeed_fst`), the same way `canonicalSignedStep` itself does it. Needed
because `List.take`'s length only collapses to the requested size (rather
than clamping at the parent's actual capacity) once this bound is in hand. -/
theorem requiredXChildReserve_fits (x z : ExtReg)
    (hrec : nextSignedWidth x z r2_2_ops < phaseInputSize x z)
    (hworkspace : SignedRecursiveWorkspaceOK r2_2_ops x z) :
    (List.ofFn (RecursivePhaseWorkspace.requiredXChildReserve r2_2_ops x.width z.width)).sum ≤
      x.capacity := by
  have hrec' : RecursivePhaseWorkspace.nextWidth r2_2_ops x.width z.width < max x.width z.width := by
    rw [nextWidth_eq_nextSignedWidth]; exact hrec
  rw [RecursivePhaseWorkspace.requiredXChildReserve_sum]
  have hres := hworkspace.x_reserve_sufficient
  rw [RecursivePhaseWorkspace.reserveNeed_fst, dif_pos hrec'] at hres
  exact hres

theorem requiredZChildReserve_fits (x z : ExtReg)
    (hrec : nextSignedWidth x z r2_2_ops < phaseInputSize x z)
    (hworkspace : SignedRecursiveWorkspaceOK r2_2_ops x z) :
    (List.ofFn (RecursivePhaseWorkspace.requiredZChildReserve r2_2_ops x.width z.width)).sum ≤
      z.capacity := by
  have hrec' : RecursivePhaseWorkspace.nextWidth r2_2_ops x.width z.width < max x.width z.width := by
    rw [nextWidth_eq_nextSignedWidth]; exact hrec
  rw [RecursivePhaseWorkspace.requiredZChildReserve_sum]
  have hres := hworkspace.z_reserve_sufficient
  rw [RecursivePhaseWorkspace.reserveNeed_snd, dif_pos hrec'] at hres
  exact hres

theorem child_capacity_0x (x z : ExtReg)
    (hrec : nextSignedWidth x z r2_2_ops < phaseInputSize x z)
    (hworkspace : SignedRecursiveWorkspaceOK r2_2_ops x z) :
    ((canonicalSignedStep r2_2_hk r2_2_ops x z hrec hworkspace).layout.xSplit.child 0).capacity =
      RecursivePhaseWorkspace.requiredXChildReserve r2_2_ops x.width z.width 0 := by
  rw [PhaseSplitLayout.child_capacity]
  have hfit := requiredXChildReserve_fits x z hrec hworkspace
  simp only [List.ofFn_succ, List.ofFn_zero, List.sum_cons, List.sum_nil, Fin.isValue,
    Fin.succ_zero_eq_one] at hfit
  simp [-RecursivePhaseWorkspace.reserveNeed_fst, -RecursivePhaseWorkspace.reserveNeed_snd,
    canonicalSignedStep, PhaseSplitLayout.ofBudget, ReserveBudget.topIndex,
    ReserveBudget.ofRequirements, ReserveBudget.childReserve, ReserveBudget.offset, ReserveBudget.fillSlack,
    RecursivePhaseWorkspace.requiredXChildReserve, RecursivePhaseWorkspace.requiredChildReserve,
    RecursivePhaseWorkspace.PhaseSide.width, RecursivePhaseWorkspace.PhaseSide.reserveComponent,
    RecursivePhaseWorkspace.limbWidth, RecursivePhaseWorkspace.widthModelX, RecursivePhaseWorkspace.widthModelZ,
    phaseChunkActive, phaseChunkStart, phaseSplitLogicalWidth, isTopChunk, r2_2_k, phaseLimbWidth,
    phaseLimbWidthOfWidth, Reg.interval, ExtReg.width, ExtReg.ofReg, ExtReg.capacity, regSize, Reg.width,
    List.length_range, List.length_map, List.length_take, List.length_drop, List.drop_zero, Reg.take,
    Reg.drop] at hfit ⊢
  omega

theorem child_capacity_0z (x z : ExtReg)
    (hrec : nextSignedWidth x z r2_2_ops < phaseInputSize x z)
    (hworkspace : SignedRecursiveWorkspaceOK r2_2_ops x z) :
    ((canonicalSignedStep r2_2_hk r2_2_ops x z hrec hworkspace).layout.zSplit.child 0).capacity =
      RecursivePhaseWorkspace.requiredZChildReserve r2_2_ops x.width z.width 0 := by
  rw [PhaseSplitLayout.child_capacity]
  have hfit := requiredZChildReserve_fits x z hrec hworkspace
  simp only [List.ofFn_succ, List.ofFn_zero, List.sum_cons, List.sum_nil, Fin.isValue,
    Fin.succ_zero_eq_one] at hfit
  simp [-RecursivePhaseWorkspace.reserveNeed_fst, -RecursivePhaseWorkspace.reserveNeed_snd,
    canonicalSignedStep, PhaseSplitLayout.ofBudget, ReserveBudget.topIndex,
    ReserveBudget.ofRequirements, ReserveBudget.childReserve, ReserveBudget.offset, ReserveBudget.fillSlack,
    RecursivePhaseWorkspace.requiredZChildReserve, RecursivePhaseWorkspace.requiredChildReserve,
    RecursivePhaseWorkspace.PhaseSide.width, RecursivePhaseWorkspace.PhaseSide.reserveComponent,
    RecursivePhaseWorkspace.limbWidth, RecursivePhaseWorkspace.widthModelX, RecursivePhaseWorkspace.widthModelZ,
    phaseChunkActive, phaseChunkStart, phaseSplitLogicalWidth, isTopChunk, r2_2_k, phaseLimbWidth,
    phaseLimbWidthOfWidth, Reg.interval, ExtReg.width, ExtReg.ofReg, ExtReg.capacity, regSize, Reg.width,
    List.length_range, List.length_map, List.length_take, List.length_drop, List.drop_zero, Reg.take,
    Reg.drop] at hfit ⊢
  omega

/-- `ExtReg.grow`'s effect on `.capacity`: growing by `n` consumes exactly
`n` reserve bits (`List.length_drop` is unconditional — no bound needed,
unlike the `.width`/`.active` side which needs `CanGrowTo`). General, not
tied to `phase_product` at all. -/
theorem ExtReg.capacity_grow (e : ExtReg) (n : ℕ) : (e.grow n).capacity = e.capacity - n := by
  unfold ExtReg.grow ExtReg.capacity ExtReg.remainingReserve
  simp [Reg.drop, regSize, Reg.width]

/-- The `.capacity` gap (`Emit/PLAN.md`'s R6.2 row), resolved: the extracted
`grow(ext0x, growDeltaX0W)`'s real value's `.capacity` is exactly what
`ppEnv`'s `"xCap"` slot is expected to carry at the recursive `.call`
(`RecursivePhaseWorkspace.reserveNeed`'s `x`-component at the *next* width,
twice — matching `reserveNeedXW`'s `[nextWidthW, nextWidthW]` args). Chains
`ExtReg.capacity_grow` with `child_capacity_0x`/`child_width_0` and
`requiredXChildReserve`'s arithmetic definition (`(Wnext - childWidth) +
reserveComponent`, `Compiler/Workspace.lean`) — the `Wnext - childWidth`
summand cancels exactly against `capacity_grow`'s `- n`, leaving the
`reserveComponent` alone. -/
theorem capacity_grow0x (x z : ExtReg)
    (hrec : nextSignedWidth x z r2_2_ops < phaseInputSize x z)
    (hworkspace : SignedRecursiveWorkspaceOK r2_2_ops x z) :
    (growExtRegTo ((canonicalSignedStep r2_2_hk r2_2_ops x z hrec hworkspace).layout.xSplit.child 0)
      (nextSignedWidth x z r2_2_ops)).capacity =
      (RecursivePhaseWorkspace.reserveNeed r2_2_ops (nextSignedWidth x z r2_2_ops)
        (nextSignedWidth x z r2_2_ops)).1 := by
  unfold growExtRegTo
  rw [ExtReg.capacity_grow, child_capacity_0x x z hrec hworkspace, child_width_0]
  have hk2 : r2_2_k = 2 := rfl
  have hwmX : (RecursivePhaseWorkspace.widthModelX x.width).width = x.width := by
    simp [RecursivePhaseWorkspace.widthModelX, ExtReg.width, ExtReg.ofReg, regSize, Reg.width,
      Reg.interval]
  have hwmZ : (RecursivePhaseWorkspace.widthModelZ x.width z.width).width = z.width := by
    simp [RecursivePhaseWorkspace.widthModelZ, ExtReg.width, ExtReg.ofReg, regSize, Reg.width,
      Reg.interval]
  have hlimbeq : phaseLimbWidth (RecursivePhaseWorkspace.widthModelX x.width)
      (RecursivePhaseWorkspace.widthModelZ x.width z.width) 2 = phaseLimbWidth x z 2 := by
    simp only [phaseLimbWidth, hwmX, hwmZ]
  simp only [RecursivePhaseWorkspace.requiredXChildReserve, RecursivePhaseWorkspace.requiredChildReserve,
    RecursivePhaseWorkspace.PhaseSide.width, RecursivePhaseWorkspace.PhaseSide.reserveComponent,
    RecursivePhaseWorkspace.limbWidth, phaseSplitLogicalWidth, isTopChunk, hk2, Fin.isValue,
    Fin.val_zero, show ¬ (0 + 1 = 2) from by decide, if_false, hlimbeq]
  rw [nextWidth_eq_nextSignedWidth]
  omega

theorem capacity_grow0z (x z : ExtReg)
    (hrec : nextSignedWidth x z r2_2_ops < phaseInputSize x z)
    (hworkspace : SignedRecursiveWorkspaceOK r2_2_ops x z) :
    (growExtRegTo ((canonicalSignedStep r2_2_hk r2_2_ops x z hrec hworkspace).layout.zSplit.child 0)
      (nextSignedWidth x z r2_2_ops)).capacity =
      (RecursivePhaseWorkspace.reserveNeed r2_2_ops (nextSignedWidth x z r2_2_ops)
        (nextSignedWidth x z r2_2_ops)).2 := by
  unfold growExtRegTo
  rw [ExtReg.capacity_grow, child_capacity_0z x z hrec hworkspace, child_width_0]
  have hk2 : r2_2_k = 2 := rfl
  have hwmX : (RecursivePhaseWorkspace.widthModelX x.width).width = x.width := by
    simp [RecursivePhaseWorkspace.widthModelX, ExtReg.width, ExtReg.ofReg, regSize, Reg.width,
      Reg.interval]
  have hwmZ : (RecursivePhaseWorkspace.widthModelZ x.width z.width).width = z.width := by
    simp [RecursivePhaseWorkspace.widthModelZ, ExtReg.width, ExtReg.ofReg, regSize, Reg.width,
      Reg.interval]
  have hlimbeq : phaseLimbWidth (RecursivePhaseWorkspace.widthModelX x.width)
      (RecursivePhaseWorkspace.widthModelZ x.width z.width) 2 = phaseLimbWidth x z 2 := by
    simp only [phaseLimbWidth, hwmX, hwmZ]
  simp only [RecursivePhaseWorkspace.requiredZChildReserve, RecursivePhaseWorkspace.requiredChildReserve,
    RecursivePhaseWorkspace.PhaseSide.width, RecursivePhaseWorkspace.PhaseSide.reserveComponent,
    RecursivePhaseWorkspace.limbWidth, phaseSplitLogicalWidth, isTopChunk, hk2, Fin.isValue,
    Fin.val_zero, show ¬ (0 + 1 = 2) from by decide, if_false, hlimbeq]
  rw [nextWidth_eq_nextSignedWidth]
  omega

/-- `evalW` of `reserveNeedXW := .opaque "reserveNeed_x" [nextWidthW, nextWidthW]`
against `ppEnv` — the width of reserve `Env.call` substitutes for the
recursive `.call` leaves' `"xCap"` slot. -/
theorem evalW_pp_reserveNeedX (x z : ExtReg) (phi : Angle) :
    evalW (ppEnv x z phi) reserveNeedXW =
      .ok (RecursivePhaseWorkspace.reserveNeed r2_2_ops (nextSignedWidth x z r2_2_ops)
        (nextSignedWidth x z r2_2_ops)).1 := by
  have h : evalW (ppEnv x z phi) reserveNeedXW =
      .ok (RecursivePhaseWorkspace.reserveNeed r2_2_ops
        (RecursivePhaseWorkspace.nextWidth r2_2_ops x.width z.width)
        (RecursivePhaseWorkspace.nextWidth r2_2_ops x.width z.width)).1 := by
    show evalW (ppEnv x z phi) (.opaque "reserveNeed_x"
      [.opaque "nextWidth" [.var "xw", .var "zw"], .opaque "nextWidth" [.var "xw", .var "zw"]]) = _
    unfold ppEnv evalW evalWList
    rfl
  rw [h, nextWidth_eq_nextSignedWidth]

theorem evalW_pp_reserveNeedZ (x z : ExtReg) (phi : Angle) :
    evalW (ppEnv x z phi) reserveNeedZW =
      .ok (RecursivePhaseWorkspace.reserveNeed r2_2_ops (nextSignedWidth x z r2_2_ops)
        (nextSignedWidth x z r2_2_ops)).2 := by
  have h : evalW (ppEnv x z phi) reserveNeedZW =
      .ok (RecursivePhaseWorkspace.reserveNeed r2_2_ops
        (RecursivePhaseWorkspace.nextWidth r2_2_ops x.width z.width)
        (RecursivePhaseWorkspace.nextWidth r2_2_ops x.width z.width)).2 := by
    show evalW (ppEnv x z phi) (.opaque "reserveNeed_z"
      [.opaque "nextWidth" [.var "xw", .var "zw"], .opaque "nextWidth" [.var "xw", .var "zw"]]) = _
    unfold ppEnv evalW evalWList
    rfl
  rw [h, nextWidth_eq_nextSignedWidth]

/-- The grown chunk-0 slot has *exactly* the recursive width, for both sides
-- reusing `Compiler/Widths.lean`'s already-proven
`targetSignedLayoutState_xslot_width_scan`/`_zslot_width_scan` (general, for
any `i`) at `i = 0` and `hcap := (canonicalSignedStep ...).capacity` (the
`CanonicalSignedStep` structure's own field, exactly the
`CanGrowToNeeds`/`CanGrowTo` hypothesis those lemmas need) — no new
width-dominance fact needed, it was already established for the real
compiler's own correctness proofs. -/
theorem width_grow0x (x z : ExtReg)
    (hrec : nextSignedWidth x z r2_2_ops < phaseInputSize x z)
    (hworkspace : SignedRecursiveWorkspaceOK r2_2_ops x z) :
    (growExtRegTo ((canonicalSignedStep r2_2_hk r2_2_ops x z hrec hworkspace).layout.xSplit.child 0)
      (nextSignedWidth x z r2_2_ops)).width = nextSignedWidth x z r2_2_ops := by
  have h := targetSignedLayoutState_xslot_width_scan
    (canonicalSignedStep r2_2_hk r2_2_ops x z hrec hworkspace).layout r2_2_ops 0
    (canonicalSignedStep r2_2_hk r2_2_ops x z hrec hworkspace).capacity
  simpa [targetSignedLayoutState, initSignedLayoutState, nextSignedWidth] using h

theorem width_grow0z (x z : ExtReg)
    (hrec : nextSignedWidth x z r2_2_ops < phaseInputSize x z)
    (hworkspace : SignedRecursiveWorkspaceOK r2_2_ops x z) :
    (growExtRegTo ((canonicalSignedStep r2_2_hk r2_2_ops x z hrec hworkspace).layout.zSplit.child 0)
      (nextSignedWidth x z r2_2_ops)).width = nextSignedWidth x z r2_2_ops := by
  have h := targetSignedLayoutState_zslot_width_scan
    (canonicalSignedStep r2_2_hk r2_2_ops x z hrec hworkspace).layout r2_2_ops 0
    (canonicalSignedStep r2_2_hk r2_2_ops x z hrec hworkspace).capacity
  simpa [targetSignedLayoutState, initSignedLayoutState, nextSignedWidth] using h

/-- `Env.call`'s result at each recursive `.call "phase_product"` leaf's
evaluated args (`wArgs = [nextWidth, nextWidth, reserveNeed_x, reserveNeed_z]`,
`aArgs = [phi * coeff(l, limbW)]`, `rArgs = [grow(ext0x, growDeltaX0W),
grow(ext0z, growDeltaZ0W)]` — the "Second round of research findings" ground
truth, `Emit/PLAN.md`'s R6.2 row) equals `ppEnv` at the grown chunk-0
children and the scaled angle — the induction hypothesis's exact target
environment. `opaqueW`/`coeff` need no case analysis at all: `ppEnv`'s fields
for those don't reference `x, z, phi` (only the fixed `r2_2_ops`/`r2_2_k`), so
`Env.call`'s `{env with ...}` carry-over is *syntactically* the same closed
term `ppEnv` would build fresh for any other `x, z, phi` — `rfl` after
`congr 1` closes those two components directly, same as `envCall_naive_leaf_eq`. -/
theorem envCall_phase_product_eq (x z : ExtReg) (phi : Angle) (l : ℕ) (hl : l < q r2_2_k)
    (hrec : nextSignedWidth x z r2_2_ops < phaseInputSize x z)
    (hworkspace : SignedRecursiveWorkspaceOK r2_2_ops x z) :
    Env.call (ppEnv x z phi) ["xw", "zw", "xCap", "zCap"]
      [nextSignedWidth x z r2_2_ops, nextSignedWidth x z r2_2_ops,
        (RecursivePhaseWorkspace.reserveNeed r2_2_ops (nextSignedWidth x z r2_2_ops)
          (nextSignedWidth x z r2_2_ops)).1,
        (RecursivePhaseWorkspace.reserveNeed r2_2_ops (nextSignedWidth x z r2_2_ops)
          (nextSignedWidth x z r2_2_ops)).2]
      ["phi"]
      [phi * loweringPhaseCoeff r2_2_k x z (genInterpolationPoints r2_2_k)
        (generatedInterpolationPoints_length r2_2_k) ⟨l, hl⟩]
      ["x", "z"]
      [growExtRegTo ((canonicalSignedStep r2_2_hk r2_2_ops x z hrec hworkspace).layout.xSplit.child 0)
          (nextSignedWidth x z r2_2_ops),
        growExtRegTo ((canonicalSignedStep r2_2_hk r2_2_ops x z hrec hworkspace).layout.zSplit.child 0)
          (nextSignedWidth x z r2_2_ops)] =
      ppEnv
        (growExtRegTo ((canonicalSignedStep r2_2_hk r2_2_ops x z hrec hworkspace).layout.xSplit.child 0)
          (nextSignedWidth x z r2_2_ops))
        (growExtRegTo ((canonicalSignedStep r2_2_hk r2_2_ops x z hrec hworkspace).layout.zSplit.child 0)
          (nextSignedWidth x z r2_2_ops))
        (phi * loweringPhaseCoeff r2_2_k x z (genInterpolationPoints r2_2_k)
          (generatedInterpolationPoints_length r2_2_k) ⟨l, hl⟩) := by
  set childX := growExtRegTo ((canonicalSignedStep r2_2_hk r2_2_ops x z hrec hworkspace).layout.xSplit.child 0)
    (nextSignedWidth x z r2_2_ops) with hchildX
  set childZ := growExtRegTo ((canonicalSignedStep r2_2_hk r2_2_ops x z hrec hworkspace).layout.zSplit.child 0)
    (nextSignedWidth x z r2_2_ops) with hchildZ
  have hcw := width_grow0x x z hrec hworkspace
  have hcz := width_grow0z x z hrec hworkspace
  have hcwCap := capacity_grow0x x z hrec hworkspace
  have hczCap := capacity_grow0z x z hrec hworkspace
  rw [← hchildX] at hcw hcwCap
  rw [← hchildZ] at hcz hczCap
  unfold Env.call ppEnv
  congr 1
  · funext n
    by_cases hxw : n = "xw"
    · subst hxw
      simp only [List.zip_cons_cons, List.lookup_cons, List.cons.injEq, and_true, reduceCtorEq,
        beq_self_eq_true, ↓reduceIte]
      exact congrArg some hcw.symm
    · have hxw' : (n == "xw") = false := by simpa using hxw
      by_cases hzw : n = "zw"
      · subst hzw
        simp only [List.zip_cons_cons, List.lookup_cons, hxw', Bool.false_eq_true, ↓reduceIte,
          beq_self_eq_true]
        exact congrArg some hcz.symm
      · have hzw' : (n == "zw") = false := by simpa using hzw
        by_cases hxc : n = "xCap"
        · subst hxc
          simp only [List.zip_cons_cons, List.lookup_cons, hxw, hzw, hxw', hzw', Bool.false_eq_true,
            ↓reduceIte, beq_self_eq_true]
          exact congrArg some hcwCap.symm
        · have hxc' : (n == "xCap") = false := by simpa using hxc
          by_cases hzc : n = "zCap"
          · subst hzc
            simp only [List.zip_cons_cons, List.lookup_cons, hxw, hzw, hxc, hxw', hzw', hxc',
              Bool.false_eq_true, ↓reduceIte, beq_self_eq_true]
            exact congrArg some hczCap.symm
          · have hzc' : (n == "zCap") = false := by simpa using hzc
            simp [-RecursivePhaseWorkspace.reserveNeed_fst, -RecursivePhaseWorkspace.reserveNeed_snd,
              List.lookup_cons, hxw, hzw, hxc, hzc, hxw', hzw', hxc', hzc']
  · funext n
    by_cases hphi : n = "phi"
    · subst hphi; simp [List.lookup_cons]
    · have hphi' : (n == "phi") = false := by simpa using hphi
      simp [List.lookup_cons, hphi, hphi']
  · funext n
    by_cases hx : n = "x"
    · subst hx; simp [List.lookup_cons]
    · have hx' : (n == "x") = false := by simpa using hx
      by_cases hz : n = "z"
      · subst hz; simp [List.lookup_cons, hx']
      · have hz' : (n == "z") = false := by simpa using hz
        simp [List.lookup_cons, hx, hz, hx', hz']

/-! ## The `hrec` branch: `lowerGateRec`'s real structure

The final assembly step: `lowerGateRec (standardSignedPhaseLoweringPlan ...)`,
in the `hrec` (recursive) branch, against `r2_2_ppThen`'s 21-leaf extracted
body. Confirmed by direct experimentation (not yet a closed theorem — see
`Emit/PLAN.md`'s R6.2 row for the precise state and what blocks it): -/

/-- `lowerGateRec` doesn't depend on a `PhaseLoweringPlan`'s `initSize` index
(`LowGate`, the output type, has no such index at all), so casting a plan
along a proof that its index equals some other value doesn't change what it
lowers to — regardless of *which* proof of that equality the cast uses. This
is the tool needed to bridge `standardSignedPhaseLoweringPlan`'s recursive
`recurse` field (built via `simpa [hsize] using childPlan` in
`PlanBuilders.lean`, i.e. literally a cast of the *same* recursive call an
induction hypothesis would supply) against a cast-free statement of that
same recursive call: `lowerGateRec (h ▸ p) = lowerGateRec p` holds by `rfl`
once `h` is substituted away, since `▸`'s underlying `Eq.rec` reduces on a
literal `Eq.refl`. -/
theorem lowerGateRec_cast {k : ℕ} {hk : 1 < k} {pts : List Operations.Point}
    {hpts : pts.length = q k} {ops : Prog k} {n1 n2 : ℕ} {U : Gate} (h : n1 = n2)
    (p : PhaseLoweringPlan k hk pts hpts ops n1 U) :
    lowerGateRec (h ▸ p) = lowerGateRec p := by
  subst h
  rfl

/-! ## The `hrec` branch: `r2_2_ops` reduces (a second, independent obstacle,
now resolved)

Assembling the 21-leaf `hrec` branch needs `r2_2_ops`'s own value concrete —
`annotatePhaseTermsAux`/`compileAnnotatedOpsToSignedGateAux` genuinely
pattern-match on it (unlike the *extracted* side, where `r2_2_doc` is already
a baked-in literal `IR.Node` AST computed once by the extractor — the *real*
compiler side has no such precomputation and must reduce `r2_2_ops` itself).
`r2_2_ops := (tableInstance .standard r2_2_k r2_2_hk).ops`, built through
`genOpsWithProduct`/`opsForPointWithProduct`/`computeLocal2`/`addConstFrom`.
Plain `rfl`/`unfold` gets stuck partway through — not slow, genuinely stuck —
traced to `Table_Generation/Builders/Fragments.lean`'s `addConstAux`, which
(unlike everything else in this chain) is declared with `termination_by`/
`decreasing_by omega` rather than plain structural recursion. This is the
*same* class of issue `Emit/PLAN.md` §12.0 already documents for `evalW`/
`evalNode` (`partial def`, there): a `termination_by`-compiled definition
produces real `.eq_n` equation lemmas, but compiles via `WellFounded.fix`,
whose underlying `Acc.rec` does not reduce through plain `rfl`/`unfold` — it
needs `simp [addConstAux]` (or any tactic that rewrites via the equation
lemmas) instead. Once that's supplied, alongside the standard `List.range`/
`List.map`/`List.filter`/`Fin.finRange` unfolding lemmas everything else in
the chain needs, `r2_2_ops` reduces cleanly and quickly (a few seconds, not
the "possibly minutes of kernel computation" its `Matrix.det`-adjacent
neighbours in this file might suggest — `addConstAux` was the only genuinely
stuck step, not a performance problem). -/
theorem r2_2_ops_eq :
    r2_2_ops =
      [Operations.valid_ops.phaseProduct (0 : Fin 2),
       Operations.valid_ops.addScaled (0 : Fin 2) (1 : Fin 2) true 0,
       Operations.valid_ops.phaseProduct (0 : Fin 2),
       Operations.valid_ops.addScaled (0 : Fin 2) (1 : Fin 2) false 0,
       Operations.valid_ops.addScaled (0 : Fin 2) (1 : Fin 2) false 0,
       Operations.valid_ops.phaseProduct (0 : Fin 2),
       Operations.valid_ops.addScaled (0 : Fin 2) (1 : Fin 2) true 0] := by
  simp [r2_2_ops, Shor.tableInstance, genOpsWithProduct, genInterpolationPoints,
    opsForPointWithProduct, computeLocal2, computeLocalAux, computeFracLocal2,
    computeFracLocalAux, addConstFrom, addConstAux, apply_Op_inverse,
    List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.length_append,
    alternatingPoint, Shor.Emit.Tests.r2_2_k, nonzeroFins, finZero, finLast, nonlastFins,
    List.finRange_succ, List.finRange_zero, List.filter_cons, List.filter_nil,
    List.length_reverse, List.length_map, Operations.inv]

/-- `annotatePhaseTermsAux`'s output on `r2_2_ops`, concretely: the three
`phaseProduct` leaves get interpolation terms `l = 0, 1, 2` in source order
(`annotatePhaseTermsAux`'s own counter), every other op gets `none`. This is
what `planCompileAnnotatedOpsToSignedGateAux`'s `.phaseProduct` case
actually recurses on — needed as its own lemma (via `rw`, not repeating
`r2_2_ops_eq`'s whole reduction inside every subsequent `simp` call) because
unfolding `planCompileAnnotatedOpsToSignedGateAux` against a still-symbolic
`annotatePhaseTermsAux 2 0 r2_2_ops` scrutinee is expensive enough to exhaust
`simp`'s default step budget partway through the 21-leaf goal (observed:
`unfold` first, `rw [r2_2_ops_eq]` after, times out at 4M heartbeats; `rw
[r2_2_ops_eq]` before reducing `annotatePhaseTermsAux` on its own, as this
lemma does, takes 10s). -/
theorem r2_2_annotatedOps_eq :
    annotatePhaseTermsAux 2 0 r2_2_ops =
      [⟨Operations.valid_ops.phaseProduct (0 : Fin 2), some ⟨0, by decide⟩⟩,
       ⟨Operations.valid_ops.addScaled (0 : Fin 2) (1 : Fin 2) true 0, none⟩,
       ⟨Operations.valid_ops.phaseProduct (0 : Fin 2), some ⟨1, by decide⟩⟩,
       ⟨Operations.valid_ops.addScaled (0 : Fin 2) (1 : Fin 2) false 0, none⟩,
       ⟨Operations.valid_ops.addScaled (0 : Fin 2) (1 : Fin 2) false 0, none⟩,
       ⟨Operations.valid_ops.phaseProduct (0 : Fin 2), some ⟨2, by decide⟩⟩,
       ⟨Operations.valid_ops.addScaled (0 : Fin 2) (1 : Fin 2) true 0, none⟩] := by
  rw [r2_2_ops_eq]
  simp [annotatePhaseTermsAux, q]

/-! ## The `hrec` branch: the universe-cast obstacle, resolved

`Emit/PLAN.md`'s R6.2 row ("Third round of research findings") documents the
obstacle: `standardSignedPhaseLoweringPlan`'s recursive `recurse` field casts
a genuine recursive call (`standardSignedPhaseLoweringPlan k hk theta childX
childZ ops hchild`) along an `initSize`-index equality, built by nested
`simpa` calls — and the *specific* cast term this produces is not
syntactically `h ▸ p` for any `h` a hand-written lemma can predict (the
`congrArg`-shaped guess `lowerGateRec_cast` above needed did not match:
`simp` reported it unused against the real goal). The fix does not try to
know the cast's exact shape at all: any two casts along *any* proof of the
same type-level equality are `HEq` to the value being cast (`eqmp_heq`,
general over any `Type`, not specific to `PhaseLoweringPlan` — proof
irrelevance for the `Prop`-valued equality `α = β` makes this true
regardless of which specific proof built the cast), and `lowerGateRec`
respects `HEq` once the `initSize` indices are known equal
(`lowerGateRec_heq`, using the *separately supplied* index equality rather
than trying to extract it from the cast). Composed: `lowerGateRec_eqmp_final`
rewrites `lowerGateRec (Eq.mp h p)` to `lowerGateRec p` for *any* `h`,
needing only the `initSize` equality as an explicit argument (from
`(canonicalSignedStep ...).childInputSize i`, already available, per the
"Third round" notes) — not the cast term itself. Confirmed empirically: `simp
only [lowerGateRec_eqmp_final hn0]` (with `hn0` instantiated once, since all
three recursive `.phaseProduct` leaves recurse into the same chunk-0
children) collapses all three casts and, combined with `simp only
[planCompileAnnotatedOpsToSignedGateAux]` (not `unfold`, which only unfolds
one list position at a time — `simp only` repeats until the whole concrete
12-element list from `r2_2_annotatedOps_eq` is consumed), produces the full
12-leaf body with every recursive call already in clean, cast-free
`lowerGateRec (standardSignedPhaseLoweringPlan ...)` form. -/

/-- `Eq.mp` along *any* proof of a type equality produces a value `HEq` to
the original — true by proof irrelevance for the `Prop`-valued equality
`α = β`, regardless of how that particular proof was built. This is the
general tool that sidesteps ever needing to know a cast's exact syntactic
shape. -/
theorem eqmp_heq {α β : Type} (h : α = β) (p : α) : HEq (Eq.mp h p) p := by
  cases h
  rfl

/-- `lowerGateRec` respects `HEq` across an `initSize` index change, given
the index equality supplied directly (not extracted from whatever term
proves the two `PhaseLoweringPlan` types equal). -/
theorem lowerGateRec_heq {k : ℕ} {hk : 1 < k} {pts : List Operations.Point}
    {hpts : pts.length = q k} {ops : Prog k} {n1 n2 : ℕ} {U : Gate} (hn : n1 = n2)
    (p1 : PhaseLoweringPlan k hk pts hpts ops n1 U)
    (p2 : PhaseLoweringPlan k hk pts hpts ops n2 U)
    (h : HEq p1 p2) :
    lowerGateRec p1 = lowerGateRec p2 := by
  subst hn
  rw [eq_of_heq h]

/-- The composed tool: `lowerGateRec` of *any* `Eq.mp`-cast plan equals
`lowerGateRec` of the plan being cast, given only the underlying `initSize`
equality (not the cast's specific proof term). This is what makes each
recursive `.phaseProduct` leaf collapse to a clean, cast-free recursive call
matching the induction hypothesis's exact target shape. -/
theorem lowerGateRec_eqmp_final {k : ℕ} {hk : 1 < k} {pts : List Operations.Point}
    {hpts : pts.length = q k} {ops : Prog k} {n1 n2 : ℕ} {U : Gate} (hn : n1 = n2)
    (h : PhaseLoweringPlan k hk pts hpts ops n1 U = PhaseLoweringPlan k hk pts hpts ops n2 U)
    (p : PhaseLoweringPlan k hk pts hpts ops n1 U) :
    lowerGateRec (Eq.mp h p) = lowerGateRec p := by
  have heq1 : HEq (Eq.mp h p) p := eqmp_heq h p
  exact (lowerGateRec_heq hn p (Eq.mp h p) heq1.symm).symm

/-! ## The `hrec` branch: allocation/deallocation, resolved

The `Gate`-index analogue of the universe-cast obstacle above: `allocChunkGate`/
`deallocChunkGate`'s tactic-mode `dsimp; split; ·⋯; · split; ⋯` proofs
(`planAllocChunkGate`/`planDeallocChunkGate`, `PlanBuilders.lean`) generalize
the *return type's* `Gate` index over the `dite`, producing `Decidable.rec`/
`cast` terms `simp`/`split_ifs`/`split` cannot push a bare `lowerGateRec`
application through (confirmed empirically: every combination left a stuck
`Decidable.rec (⋯) (⋯) (instDecidableEqNat ⋯)` no rewrite touched). Same fix
as before, extended to this index: `lowerGateRec_heq_gate` (respects `HEq`
across a `Gate`-index change, exactly like `lowerGateRec_heq` does for
`initSize`), combined with `eqRec_heq` (Lean core: `HEq (h ▸ a) a`, the
`▸`-flavored counterpart of `eqmp_heq`) to cast `planAllocChunkGate`'s opaque
value along a *proven* `Gate`-level equality (`allocChunkGate i src dst =
Gate.id`, by `unfold allocChunkGate; simp [h0]` once `h0`/`htop` are known)
rather than trying to reduce through the cast already baked into the term.
Once the cast value's `Gate` index is a literal constructor application,
`cases`/`rfl` closes it directly — no motive/index mismatch left, since
`lowerGateRec`'s own pattern match only has one viable case for that index. -/

/-- `lowerGateRec` respects `HEq` across a *`Gate`-index* change too (not just
`initSize`, `lowerGateRec_heq`'s index) — its output doesn't depend on either
index of `PhaseLoweringPlan`. -/
theorem lowerGateRec_heq_gate {k : ℕ} {hk : 1 < k} {pts : List Operations.Point}
    {hpts : pts.length = q k} {ops : Prog k} {initSize : ℕ} {U1 U2 : Gate} (hU : U1 = U2)
    (p1 : PhaseLoweringPlan k hk pts hpts ops initSize U1)
    (p2 : PhaseLoweringPlan k hk pts hpts ops initSize U2)
    (h : HEq p1 p2) :
    lowerGateRec p1 = lowerGateRec p2 := by
  subst hU
  rw [eq_of_heq h]

theorem lowerGateRec_planAllocChunkGate {k : ℕ} {hk : 1 < k} {pts : List Operations.Point}
    {hpts : pts.length = q k} {ops : Prog k} (initSize : ℕ) (i : Fin k) (src dst : ExtReg) :
    lowerGateRec (planAllocChunkGate (k := k) (hk := hk) (pts := pts) (hpts := hpts) (ops := ops)
      initSize i src dst) =
      if extraDelta src dst = 0 then LowGate.id
      else if isTopChunk i then LowGate.signExtend src (extraDelta src dst)
      else LowGate.zeroExtend src (extraDelta src dst) := by
  set p := planAllocChunkGate (k := k) (hk := hk) (pts := pts) (hpts := hpts) (ops := ops)
    initSize i src dst with hp
  by_cases h0 : extraDelta src dst = 0
  · have hU : allocChunkGate i src dst = Gate.id := by unfold allocChunkGate; simp [h0]
    have hheq : HEq p (hU ▸ p) := (eqRec_heq hU p).symm
    rw [if_pos h0, lowerGateRec_heq_gate hU p (hU ▸ p) hheq]
    cases (hU ▸ p : PhaseLoweringPlan k hk pts hpts ops initSize Gate.id) with
    | id _ => rfl
  · by_cases htop : isTopChunk i
    · have hU : allocChunkGate i src dst = Gate.signExtend src (extraDelta src dst) := by
        unfold allocChunkGate; simp [h0, htop]
      have hheq : HEq p (hU ▸ p) := (eqRec_heq hU p).symm
      rw [if_neg h0, if_pos htop, lowerGateRec_heq_gate hU p (hU ▸ p) hheq]
      cases (hU ▸ p : PhaseLoweringPlan k hk pts hpts ops initSize (Gate.signExtend src (extraDelta src dst)))
        with
      | signExtend _ _ _ => rfl
    · have hU : allocChunkGate i src dst = Gate.zeroExtend src (extraDelta src dst) := by
        unfold allocChunkGate; simp [h0, htop]
      have hheq : HEq p (hU ▸ p) := (eqRec_heq hU p).symm
      rw [if_neg h0, if_neg htop, lowerGateRec_heq_gate hU p (hU ▸ p) hheq]
      cases (hU ▸ p : PhaseLoweringPlan k hk pts hpts ops initSize (Gate.zeroExtend src (extraDelta src dst)))
        with
      | zeroExtend _ _ _ => rfl

/-- Same as `lowerGateRec_planAllocChunkGate`, deallocation side
(`Gate.zeroDealloc`/`Gate.signDealloc` instead of `Gate.zeroExtend`/
`Gate.signExtend`, `planDeallocChunkGate` instead of `planAllocChunkGate` —
otherwise an identical `dite`/`dite` shape, so the same `lowerGateRec_heq_gate`
+ concrete-index `cases` fix applies verbatim). -/
theorem lowerGateRec_planDeallocChunkGate {k : ℕ} {hk : 1 < k} {pts : List Operations.Point}
    {hpts : pts.length = q k} {ops : Prog k} (initSize : ℕ) (i : Fin k) (src dst : ExtReg) :
    lowerGateRec (planDeallocChunkGate (k := k) (hk := hk) (pts := pts) (hpts := hpts) (ops := ops)
      initSize i src dst) =
      if extraDelta src dst = 0 then LowGate.id
      else if isTopChunk i then LowGate.signDealloc src (extraDelta src dst)
      else LowGate.zeroDealloc src (extraDelta src dst) := by
  set p := planDeallocChunkGate (k := k) (hk := hk) (pts := pts) (hpts := hpts) (ops := ops)
    initSize i src dst with hp
  by_cases h0 : extraDelta src dst = 0
  · have hU : deallocChunkGate i src dst = Gate.id := by unfold deallocChunkGate; simp [h0]
    have hheq : HEq p (hU ▸ p) := (eqRec_heq hU p).symm
    rw [if_pos h0, lowerGateRec_heq_gate hU p (hU ▸ p) hheq]
    cases (hU ▸ p : PhaseLoweringPlan k hk pts hpts ops initSize Gate.id) with
    | id _ => rfl
  · by_cases htop : isTopChunk i
    · have hU : deallocChunkGate i src dst = Gate.signDealloc src (extraDelta src dst) := by
        unfold deallocChunkGate; simp [h0, htop]
      have hheq : HEq p (hU ▸ p) := (eqRec_heq hU p).symm
      rw [if_neg h0, if_pos htop, lowerGateRec_heq_gate hU p (hU ▸ p) hheq]
      cases (hU ▸ p : PhaseLoweringPlan k hk pts hpts ops initSize (Gate.signDealloc src (extraDelta src dst)))
        with
      | signDealloc _ _ _ => rfl
    · have hU : deallocChunkGate i src dst = Gate.zeroDealloc src (extraDelta src dst) := by
        unfold deallocChunkGate; simp [h0, htop]
      have hheq : HEq p (hU ▸ p) := (eqRec_heq hU p).symm
      rw [if_neg h0, if_neg htop, lowerGateRec_heq_gate hU p (hU ▸ p) hheq]
      cases (hU ▸ p : PhaseLoweringPlan k hk pts hpts ops initSize (Gate.zeroDealloc src (extraDelta src dst)))
        with
      | zeroDealloc _ _ _ => rfl

end Shor.IR
