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

end Shor.IR
