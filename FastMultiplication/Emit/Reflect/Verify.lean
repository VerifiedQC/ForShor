import FastMultiplication.Emit.Reflect.Driver
import FastMultiplication.Emit.IR.WellFormed
import FastMultiplication.Emit.IR.Instantiate
import FastMultiplication.Emit.Lower.Registers
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Lowering.PlanBuilders
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Lowering.Lower
import FastMultiplication.ShorVerification.Implementation.QFT.Lowering.PlanBuilders
import FastMultiplication.ShorVerification.Implementation.Reference.StandardLoweringSetup
import FastMultiplication.ShorVerification.Implementation.Reference.ReferenceLayout
import FastMultiplication.ShorVerification.Implementation.Reference.ReferenceShorImplementation

/-!
# R3: runtime instance verification of an extracted `Doc`

D7's trust statement ("checked: instantiate = real term at the listed
widths") is established once, at build time, by `Tests.lean`'s R2.1-R2.7
`native_decide` suite — but those checks are pinned to fixed small `k`
(2, 3) and to one fixed table apiece. `bundle`/`template` extract a `Doc`
for whatever `k` the caller actually asks for at run time
(`Reflect.runExtract`), so this file re-runs the *same kind* of check —
`Doc.wellFormed`, then `instantiate`/`instantiateGate` agreeing with the
real compiled/reference term — generically over the whole
`ShorLoweringSetup`, as the safety net `PLAN.md` §7 asks for: "preceded by
`Doc.wellFormed` and by the R2 instance checks at a ladder of small widths;
any failure refuses the whole bundle with exit 3."

This is deliberately a representative canary, not exhaustive: one width per
template (`4 * k`, comfortably past `k` so slot splitting/allocation is
exercised, whether or not it happens to trigger `phase_product`'s own
recursive case), not a scan over every base/recursive combination — that
exhaustive coverage is what R2's own compile-time suite already
established, and D2 (the extractor is keyed by Lean construct name, never
by `k`) is exactly why agreement at one representative width generalizes.

`Emit/PLAN.md` §11 (R5): `verifyDoc` takes the `Shor.ShorLoweringSetup` the
`Doc` was extracted from, so `shor_gate`/`shor`'s canary — which §7.1 could
only run for `.standard`, since only the standard table had a
`ShorLoweringSetup` to build a reference Shor instance from — now runs for
*every* input table: `setup.ops`/`setup.k`/`setup.hk` are exactly what
`Reference.allocateReferenceLayout`/`referenceShorCircuit` need, and D5's
amendment means any `setup` reaching this file is, by construction, a table
those functions are proven to work over. -/

namespace Shor.Reflect

open Shor.IR

deriving instance BEq for Shor.LowGate
deriving instance BEq for Shor.Gate

/-- Flatten one top-level `;;` chain, recursing into `.adj` bodies too (an
adjoint's own body is a `Node.seq`/`foldLowGateSeq`-folded sub-sequence that
can hide a mismatch if left unflattened — see `Tests.lean`'s R2.6 comment
for why this matters once a target's adjoints wrap multi-gate bodies). -/
partial def flattenLowGate : LowGate → List LowGate
  | .id => []
  | .seq a b => flattenLowGate a ++ flattenLowGate b
  | .adj g => [LowGate.adj ((flattenLowGate g).foldr LowGate.seq .id)]
  | g => [g]

/-- `flattenLowGate`'s `Gate`-valued counterpart. -/
partial def flattenGate : Gate → List Gate
  | .id => []
  | .seq a b => flattenGate a ++ flattenGate b
  | .adj g => [Gate.adj ((flattenGate g).foldr Gate.seq .id)]
  | g => [g]

/-- The opaque-width dispatch every template's `Env` needs (D4's opaque
list), generalized over `ops : Prog k` — mirrors `Tests.lean`'s
`r2_2_env`/`r2_5_env`/`r2_6_env` exactly, just not pinned to one fixed
`ops`. -/
def opaqueDispatch {k : ℕ} (ops : Prog k) : String → List ℕ → Option ℕ :=
  fun name args =>
    match name, args with
    | "nextWidth", [xw, zw] => some (RecursivePhaseWorkspace.nextWidth ops xw zw)
    | "reserveNeed_x", [xw, zw] => some (RecursivePhaseWorkspace.reserveNeed ops xw zw).1
    | "reserveNeed_z", [xw, zw] => some (RecursivePhaseWorkspace.reserveNeed ops xw zw).2
    | "qftXWork", [w] => some (qftWorkspaceNeed ops w).1
    | "qftZWork", [w] => some (qftWorkspaceNeed ops w).2
    | "log2", [n] => some (Nat.log2 n)
    | "mod", [m, n] => some (m % n)
    | "pow", [b, e] => some (b ^ e)
    | "modpow", [b, e, n] => some ((b ^ (2 ^ e)) % n)
    | "step5Const", [c, n] => some (step5Constant c n)
    | _, _ => none

/-- The `coeff` oracle every template's `Env` needs, generalized over the
points a setup actually carries — mirrors `Tests.lean`'s own `coeff` fields.

`SUBMISSION_PLAN.md` S1.6: this used to read the `.standard` table's points
unconditionally, whatever table it was handed, and the docstring explained
at length why that was not a bug — `standardSignedPhaseLoweringPlan`/
`standardCSignedPhaseLoweringPlan`/`standardQFTLoweringPlan` hard-wired
`genInterpolationPoints k` into their own `recurse` obligation's stated
type, so the *real* term this canary compares against used the canonical
coefficients regardless of the `ops` it was given (`Emit/PLAN.md` §6.9's
genericity finding). S1.2/S1.3 removed that hard-wiring: the plan builders
now take `pts hpts`, the real term's coefficients follow the points it was
built with, and so does this oracle. The quirk is gone rather than
documented. -/
def coeffDispatch (k : ℕ) (pts : List Operations.Point) (hpts : pts.length = q k) :
    ℕ → ℕ → Option ℚ :=
  fun l mv =>
    if h : l < q k then some (cramerCoeffFromPtsWidth k mv pts hpts ⟨l, h⟩) else none

/-- The `phase_product` template, instantiated against `doc` with concrete
`x, z, phi`, agrees with the real compiled term (`false` on any
`instantiate` error too). Exposed (not just the canary below) so `pp`'s own
CLI command (`Lower/PhaseProduct.lean`) can run the *same* check at
whatever width the caller actually asked for. -/
def phaseProductAgrees {k : ℕ} (hk : 1 < k) (ops : Prog k) (pts : List Operations.Point)
    (hpts : pts.length = q k) (doc : Doc) (x z : ExtReg) (phi : Angle)
    (hws : SignedRecursiveWorkspaceOK ops x z) : Bool :=
  let real := lowerGateRec (standardSignedPhaseLoweringPlan k hk phi x z ops pts hpts hws)
  let env : Env :=
    { w := fun name =>
        if name == "xw" then some x.width
        else if name == "zw" then some z.width
        else if name == "xCap" then some x.capacity
        else if name == "zCap" then some z.capacity
        else none
      a := fun name => if name == "phi" then some phi else none
      r := fun name => if name == "x" then some x else if name == "z" then some z else none
      opaqueW := opaqueDispatch ops
      coeff := coeffDispatch k pts hpts }
  match instantiate doc "phase_product" env 200 with
  | .error _ => false
  | .ok g => flattenLowGate g == flattenLowGate real

/-- `phase_product` canary: one representative width `n = 4k`. -/
def checkPhaseProduct (setup : Shor.ShorLoweringSetup) (doc : Doc) : Except String Unit :=
  let ops := setup.ops
  let n := 4 * setup.k
  match ppRegisters ops n with
  | .error e => .error s!"template check (phase_product): {e}"
  | .ok (x, z, _ctrl) =>
      if hws : SignedRecursiveWorkspaceOK ops x z then
        if phaseProductAgrees setup.hk ops setup.pts setup.hpts doc x z ((1 : ℚ) / 4) hws then
          .ok ()
        else .error "template check (phase_product): instantiate disagrees with the real term"
      else .error s!"template check (phase_product): insufficient workspace at n={n}"

/-- `cphase_product`, instantiated against `doc` with concrete `ctrl, x, z,
phi`, agrees with the real compiled term. Controlled analogue of
`phaseProductAgrees`, exposed for `cpp`'s own CLI command the same way. -/
def cPhaseProductAgrees {k : ℕ} (hk : 1 < k) (ops : Prog k) (pts : List Operations.Point)
    (hpts : pts.length = q k) (doc : Doc) (ctrlIdx : ℕ) (x z : ExtReg) (phi : Angle)
    (hws : CSignedRecursiveWorkspaceOK ops ctrlIdx x z) : Bool :=
  let real := lowerGateRec (standardCSignedPhaseLoweringPlan k hk ctrlIdx phi x z ops pts hpts hws)
  let ctrl := ExtReg.ofReg (Reg.interval ctrlIdx 1)
  let env : Env :=
    { w := fun name =>
        if name == "xw" then some x.width
        else if name == "zw" then some z.width
        else if name == "xCap" then some x.capacity
        else if name == "zCap" then some z.capacity
        else none
      a := fun name => if name == "phi" then some phi else none
      r := fun name =>
        if name == "ctrl" then some ctrl
        else if name == "x" then some x
        else if name == "z" then some z
        else none
      opaqueW := opaqueDispatch ops
      coeff := coeffDispatch k pts hpts }
  match instantiate doc "cphase_product" env 200 with
  | .error _ => false
  | .ok g => flattenLowGate g == flattenLowGate real

/-- `cphase_product` canary, controlled analogue of `checkPhaseProduct`. -/
def checkCPhaseProduct (setup : Shor.ShorLoweringSetup) (doc : Doc) : Except String Unit :=
  let ops := setup.ops
  let n := 4 * setup.k
  match ppRegisters ops n with
  | .error e => .error s!"template check (cphase_product): {e}"
  | .ok (x, z, ctrlIdx) =>
      if hws : CSignedRecursiveWorkspaceOK ops ctrlIdx x z then
        if cPhaseProductAgrees setup.hk ops setup.pts setup.hpts doc ctrlIdx x z ((1 : ℚ) / 4) hws
        then .ok ()
        else .error "template check (cphase_product): instantiate disagrees with the real term"
      else .error s!"template check (cphase_product): insufficient workspace at n={n}"

/-- `qft`, instantiated against `doc` with concrete register `r`, agrees
with the real compiled term. Exposed for `qft`'s own CLI command the same
way. -/
def qftAgrees {k : ℕ} (hk : 1 < k) (ops : Prog k) (pts : List Operations.Point)
    (hpts : pts.length = q k) (doc : Doc) (r : ExtReg) (hws : QFTReserveOK ops r) : Bool :=
  let xWork := ExtReg.ofReg (qftXWork ops r)
  let zWork := ExtReg.ofReg (qftZWork ops r)
  let real := lowerQFT k hk ops pts hpts r hws
  let env : Env :=
    { w := fun name =>
        if name == "w" then some r.width
        else if name == "xWorkW" then some xWork.width
        else if name == "zWorkW" then some zWork.width
        else none
      a := fun _ => none
      r := fun name =>
        if name == "r" then some r
        else if name == "xWork" then some xWork
        else if name == "zWork" then some zWork
        else none
      opaqueW := opaqueDispatch ops
      coeff := coeffDispatch k pts hpts }
  match instantiate doc "qft" env 200 with
  | .error _ => false
  | .ok g => flattenLowGate g == flattenLowGate real

/-- `qft` canary: one representative width `w = 4k`. -/
def checkQft (setup : Shor.ShorLoweringSetup) (doc : Doc) : Except String Unit :=
  let ops := setup.ops
  let w := 4 * setup.k
  match qftRegister ops w with
  | .error e => .error s!"template check (qft): {e}"
  | .ok r =>
      if hws : QFTReserveOK ops r then
        if qftAgrees setup.hk ops setup.pts setup.hpts doc r hws then .ok ()
        else .error "template check (qft): instantiate disagrees with the real term"
      else .error s!"template check (qft): insufficient workspace at w={w}"

/-- The fixed small reference instance `shor_gate`/`shor`'s canary checks
against (`a = 2, N = 15`, precision `0`) — independent of `k`, matching
`Tests.lean`'s `smallInst`. -/
def canaryInst : ShorOrderFindingInstance := ⟨2, 15, by decide, by decide⟩

/-- `shor_gate`/`shor` env, shared by both checks below (mirrors
`Tests.lean`'s `r2_6g_env`/`r2_6_env`, generalized over `setup`). -/
def shorEnv (setup : Shor.ShorLoweringSetup) (layout : Reference.ReferenceShorLayout) : Env :=
  { w := fun name =>
      if name == "a" then some canaryInst.a
      else if name == "N" then some canaryInst.N
      else if name == "xW" then some layout.x.width
      else if name == "xCap" then some layout.x.capacity
      else if name == "yW" then some layout.data.width
      else if name == "yCap" then some layout.data.capacity
      else if name == "workW" then some layout.work.width
      else if name == "workCap" then some layout.work.capacity
      else if name == "scratchW" then some layout.scratch.width
      else if name == "scratchCap" then some layout.scratch.capacity
      else none
    a := fun _ => none
    r := fun name =>
      if name == "x" then some layout.x
      else if name == "y" then some layout.data
      else if name == "work" then some layout.work
      else if name == "scratch" then some layout.scratch
      else if name == "flag" then some (ExtReg.ofReg (Reg.interval layout.flag 1))
      else none
    opaqueW := opaqueDispatch setup.ops
    coeff := coeffDispatch setup.k setup.pts setup.hpts }

/-- `shor_gate` canary (`orderFindingApprox`, the `Gate`-level target). -/
def checkShorGate (setup : Shor.ShorLoweringSetup) (doc : Doc) : Except String Unit :=
  let ops := setup.ops
  let layout := Reference.allocateReferenceLayout ops canaryInst 0
  let hworkspace := Reference.reference_modMulCircuitWorkspaceOK ops canaryInst 0
  let hstep4 := Reference.reference_step4Workspace ops canaryInst 0
  let real :=
    orderFindingApprox canaryInst.a canaryInst.N layout.x layout.data layout.work layout.scratch
      layout.flag hworkspace hstep4
  match instantiateGate doc "shor_gate" (shorEnv setup layout) 400 with
  | .error e => .error s!"template check (shor_gate): instantiate: {e}"
  | .ok g =>
      if flattenGate g == flattenGate real then .ok ()
      else .error "template check (shor_gate): instantiate disagrees with the real term"

/-- `shor` canary (`Reference.referenceShorCircuit`, the flat `LowGate`
target). -/
def checkShor (setup : Shor.ShorLoweringSetup) (doc : Doc) : Except String Unit :=
  let layout := Reference.allocateReferenceLayout setup.ops canaryInst 0
  let real := Reference.referenceShorCircuit setup canaryInst 0
  match instantiate doc "shor" (shorEnv setup layout) 400 with
  | .error e => .error s!"template check (shor): instantiate: {e}"
  | .ok g =>
      if flattenLowGate g == flattenLowGate real then .ok ()
      else .error "template check (shor): instantiate disagrees with the real term"

/-- The full canary suite (`Emit/PLAN.md` §7, generalized to any table by
§11/R5): `Doc.wellFormed`, then instance agreement for every template this
`setup` extracted, at one representative width apiece. Every check now
always runs — `setup : ShorLoweringSetup` is, by construction, a table the
reference-instance machinery is proven to work over (D5), and since
`SUBMISSION_PLAN.md` S1.6 retired `TableSource` there is no longer any other
kind of table for this file to skip `shor_gate`/`shor` for. -/
def verifyDoc (setup : Shor.ShorLoweringSetup) (doc : Doc) : Except String Unit := do
  if doc.wellFormed then pure () else .error "extracted doc is not well-formed"
  checkPhaseProduct setup doc
  checkCPhaseProduct setup doc
  checkQft setup doc
  checkShorGate setup doc
  checkShor setup doc

/-- Run-time entry point: extract, then verify. `PLAN.md` §7's blocking
check — a failure here refuses the whole `bundle`/`template` output with
exit 3 (`Main.lean`). Standard-table only at run time (`Emit/PLAN.md` §11.2
point 4) — `runExtract` already fixes this. -/
unsafe def runExtractAndVerify (k : Nat) : IO (Except String Doc) := do
  match ← runExtract k with
  | .error e => return .error e
  | .ok doc =>
      if h : 1 < k then
        match verifyDoc (standardLoweringSetup k h) doc with
        | .error e => return .error e
        | .ok () => return .ok doc
      else return .error s!"runExtractAndVerify: k = {k} must be > 1"

end Shor.Reflect
