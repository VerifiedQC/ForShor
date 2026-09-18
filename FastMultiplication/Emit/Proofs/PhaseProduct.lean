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

end Shor.IR
