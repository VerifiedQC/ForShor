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
`ShorLoweringSetup`, as R3's run-time safety net asks for: "preceded by
`Doc.wellFormed` and by the R2 instance checks at a ladder of small widths;
any failure refuses the whole bundle with exit 3."

This is a canary, not an exhaustive scan — but it is a canary over a
*ladder* of widths per template, derived from the table under test, not one
representative width. `ppWidthLadder`/`qftWidthLadder` (below) return the
largest base-case width plus the smallest widths reaching one, two and three
levels of recursion, and each phase-product width is checked in two reserve
regimes. One width per template (the old `4 * k`) is what let the top-chunk
capacity bug through: it is visible only at a grandchild of the top-level
call, so the ladder has to reach three levels, and only when the parent has
slack to split, so both regimes have to run (`Emit/PLAN.md` §1.1, §2 T2.1).
R2's compile-time suite still supplies the exhaustive small-width coverage,
and D2 (the extractor is keyed by Lean construct name, never by `k`) is why
agreement on the ladder generalizes; the ladder is what makes "agreement"
mean something at the recursive arm.

R5: `verifyDoc` takes the `Shor.ShorLoweringSetup` the
`Doc` was extracted from, so `shor_gate`/`shor`'s canary — which before R5
could only run for `.standard`, since only the standard table had a
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
for why this matters once a target's adjoints wrap multi-gate bodies).

Kept for callers that want the list itself. The *comparison* below does not
use it — see `tokenize`. -/
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

/-! ### Comparing two circuits without recursing once per gate

`flattenLowGate a == flattenLowGate b` is the obvious comparison and it is
not stack-safe. `flattenLowGate` leaves an `.adj` element holding the whole
re-folded body, so the derived `BEq LowGate` walks *that* tree one stack
frame per nested gate; and the flattening itself recurses once per `;;`.
Both overflow on a circuit of a few thousand gates — observed as
`libc++abi: terminating due to uncaught exception of type lean::throwable:
deep recursion was detected at 'interpreter'`, a hard abort that takes the
whole `lake build` with it rather than reporting a failed check.

That matters because this is the comparison `Submission/Check.lean` runs: a
submitted table whose circuit is merely *large* would crash the acceptance
build with a C++ abort instead of passing or failing it.

So the comparison goes through a flat stream of **leaf** tokens, with
adjoint boundaries marked, built with an explicit work stack. Every
recursion here is a tail call, and `BEq LowGate` is only ever applied to a
leaf. The relation is the same one `flattenLowGate`'s comparison induced:
two trees agree iff their leaves agree in order and their adjoint
boundaries fall in the same places, which is exactly "equal up to `;;`
associativity and `.id`". -/
inductive GateTok (α : Type) where
  | leaf (g : α)
  | adjOpen
  | adjClose
deriving BEq

/-- One item of `tokenize`'s work stack: a subtree still to expand, or a
token already determined (the closing marker of an adjoint whose body has
not been emitted yet). -/
private inductive Work (α : Type) where
  | expand (g : α)
  | emit (t : GateTok α)

/-- `tokenize` for `LowGate`. Tail-recursive in every branch. -/
private partial def tokenizeLowGateAux :
    List (Work LowGate) → List (GateTok LowGate) → List (GateTok LowGate)
  | [], acc => acc.reverse
  | .emit t :: rest, acc => tokenizeLowGateAux rest (t :: acc)
  | .expand g :: rest, acc =>
      match g with
      | .id => tokenizeLowGateAux rest acc
      | .seq a b => tokenizeLowGateAux (.expand a :: .expand b :: rest) acc
      | .adj h => tokenizeLowGateAux (.emit .adjOpen :: .expand h :: .emit .adjClose :: rest) acc
      | leaf => tokenizeLowGateAux rest (.leaf leaf :: acc)

/-- The leaf-token stream of a `LowGate` tree. -/
def tokenizeLowGate (g : LowGate) : List (GateTok LowGate) :=
  tokenizeLowGateAux [.expand g] []

/-- `tokenizeLowGate`'s `Gate`-valued counterpart. -/
private partial def tokenizeGateAux :
    List (Work Gate) → List (GateTok Gate) → List (GateTok Gate)
  | [], acc => acc.reverse
  | .emit t :: rest, acc => tokenizeGateAux rest (t :: acc)
  | .expand g :: rest, acc =>
      match g with
      | .id => tokenizeGateAux rest acc
      | .seq a b => tokenizeGateAux (.expand a :: .expand b :: rest) acc
      | .adj h => tokenizeGateAux (.emit .adjOpen :: .expand h :: .emit .adjClose :: rest) acc
      | leaf => tokenizeGateAux rest (.leaf leaf :: acc)

def tokenizeGate (g : Gate) : List (GateTok Gate) :=
  tokenizeGateAux [.expand g] []

/-- Two `LowGate` trees agree up to `;;` associativity and `.id`. -/
def lowGateAgrees (a b : LowGate) : Bool := tokenizeLowGate a == tokenizeLowGate b

/-- `lowGateAgrees`'s `Gate`-valued counterpart. -/
def gateAgrees (a b : Gate) : Bool := tokenizeGate a == tokenizeGate b

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

/-- The `coeff` oracle every template's `Env` needs, over the points a setup
actually carries — mirrors `Tests.lean`'s own `coeff` fields.

`pts`/`hpts` are the caller's, not the canonical ladder's: the plan builders
take the points as parameters, so the real term this canary compares against
uses whatever points it was built with, and this oracle has to match. -/
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
  | .ok g => lowGateAgrees g real

/-- `phase_product` agreement at one concrete width and one reserve regime
(`slack` qubits beyond `reserveNeed` — see `ppRegisters`). -/
def checkPhaseProductAt (setup : Shor.ShorLoweringSetup) (n : ℕ) (doc : Doc) (slack : ℕ := 1) :
    Except String Unit :=
  let ops := setup.ops
  match ppRegisters ops n slack with
  | .error e => .error s!"template check (phase_product): {e}"
  | .ok (x, z, _ctrl) =>
      if hws : SignedRecursiveWorkspaceOK ops x z then
        if phaseProductAgrees setup.hk ops setup.pts setup.hpts doc x z ((1 : ℚ) / 4) hws then
          .ok ()
        else .error
          s!"template check (phase_product): instantiate disagrees with the real term \
            at n={n}, slack={slack}"
      else .error s!"template check (phase_product): insufficient workspace at n={n}, slack={slack}"

/-- `phase_product` canary: one representative width `n = 4k`. -/
def checkPhaseProduct (setup : Shor.ShorLoweringSetup) (doc : Doc) : Except String Unit :=
  checkPhaseProductAt setup (4 * setup.k) doc

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
  | .ok g => lowGateAgrees g real

/-- `cphase_product` agreement at one concrete width and reserve regime. -/
def checkCPhaseProductAt (setup : Shor.ShorLoweringSetup) (n : ℕ) (doc : Doc) (slack : ℕ := 1) :
    Except String Unit :=
  let ops := setup.ops
  match ppRegisters ops n slack with
  | .error e => .error s!"template check (cphase_product): {e}"
  | .ok (x, z, ctrlIdx) =>
      if hws : CSignedRecursiveWorkspaceOK ops ctrlIdx x z then
        if cPhaseProductAgrees setup.hk ops setup.pts setup.hpts doc ctrlIdx x z ((1 : ℚ) / 4) hws
        then .ok ()
        else .error
          s!"template check (cphase_product): instantiate disagrees with the real term \
            at n={n}, slack={slack}"
      else .error
        s!"template check (cphase_product): insufficient workspace at n={n}, slack={slack}"

/-- `cphase_product` canary, controlled analogue of `checkPhaseProduct`. -/
def checkCPhaseProduct (setup : Shor.ShorLoweringSetup) (doc : Doc) : Except String Unit :=
  checkCPhaseProductAt setup (4 * setup.k) doc

/-- `qft`, instantiated against `doc` with concrete register `r`, agrees
with the real compiled term. Exposed for `qft`'s own CLI command the same
way. -/
def qftAgrees {k : ℕ} (hk : 1 < k) (ops : Prog k) (pts : List Operations.Point)
    (hpts : pts.length = q k) (doc : Doc) (r : ExtReg) (hws : QFTReserveOK ops r)
    (wOracle : String → List ℕ → Option ℕ := opaqueDispatch ops) : Bool :=
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
      opaqueW := wOracle
      coeff := coeffDispatch k pts hpts }
  match instantiate doc "qft" env 200 with
  | .error _ => false
  | .ok g => lowGateAgrees g real

/-- `qft` agreement at one concrete width, resolving the opaque widths with
`wOracle` (by default, by calling the real functions). -/
def checkQftAt (setup : Shor.ShorLoweringSetup) (w : ℕ) (doc : Doc)
    (wOracle : String → List ℕ → Option ℕ := opaqueDispatch (ShorLoweringSetup.ops setup)) :
    Except String Unit :=
  let ops := setup.ops
  match qftRegister ops w with
  | .error e => .error s!"template check (qft): {e}"
  | .ok r =>
      if hws : QFTReserveOK ops r then
        if qftAgrees setup.hk ops setup.pts setup.hpts doc r hws wOracle then .ok ()
        else .error s!"template check (qft): instantiate disagrees with the real term at w={w}"
      else .error s!"template check (qft): insufficient workspace at w={w}"

/-- `qft` canary: one representative width `w = 4k`. -/
def checkQft (setup : Shor.ShorLoweringSetup) (doc : Doc) : Except String Unit :=
  checkQftAt setup (4 * setup.k) doc

/-- The small reference instance `shor_gate`/`shor`'s canary checks against
(`a = 2, N = 15`, precision `0`) — independent of `k`, matching `Tests.lean`'s
`smallInst`. -/
def canaryInst : ShorOrderFindingInstance := ⟨2, 15, by decide, by decide⟩

/-- A second, larger reference instance: `a = 2, N = 143 = 11 × 13`, eight bits
of modulus against `canaryInst`'s four. Paired with a precision `m > 0` in
`submissionShorInstances`, it is what makes the exponent loop, the Hadamard
loop and the `m`-dependent register widths more than a two-iteration walk —
every one of those is a hand-stated template body (T3.4), so the only thing
standing behind it is a comparison at a size where it could go wrong. -/
def largeInst : ShorOrderFindingInstance := ⟨2, 143, by decide, by decide⟩

/-- `shor_gate`/`shor` env, shared by both checks below (mirrors
`Tests.lean`'s `r2_6g_env`/`r2_6_env`, generalized over `setup`). -/
def shorEnv (setup : Shor.ShorLoweringSetup) (inst : ShorOrderFindingInstance)
    (layout : Reference.ReferenceShorLayout) : Env :=
  { w := fun name =>
      if name == "a" then some inst.a
      else if name == "N" then some inst.N
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

/-- `shor_gate` agreement at one reference instance and precision
(`orderFindingApprox`, the `Gate`-level target). -/
def checkShorGateAt (setup : Shor.ShorLoweringSetup) (inst : ShorOrderFindingInstance) (m : ℕ)
    (doc : Doc) : Except String Unit :=
  let ops := setup.ops
  let layout := Reference.allocateReferenceLayout ops inst m
  let hworkspace := Reference.reference_modMulCircuitWorkspaceOK ops inst m
  let hstep4 := Reference.reference_step4Workspace ops inst m
  let real :=
    orderFindingApprox inst.a inst.N layout.x layout.data layout.work layout.scratch
      layout.flag hworkspace hstep4
  match instantiateGate doc "shor_gate" (shorEnv setup inst layout) 400 with
  | .error e => .error s!"template check (shor_gate): instantiate: {e}"
  | .ok g =>
      if gateAgrees g real then .ok ()
      else .error
        s!"template check (shor_gate): instantiate disagrees with the real term \
          at N={inst.N}, m={m}"

/-- `shor_gate` canary at the small instance. -/
def checkShorGate (setup : Shor.ShorLoweringSetup) (doc : Doc) : Except String Unit :=
  checkShorGateAt setup canaryInst 0 doc

/-- `shor` agreement at one reference instance and precision
(`Reference.referenceShorCircuit`, the flat `LowGate` target). -/
def checkShorAt (setup : Shor.ShorLoweringSetup) (inst : ShorOrderFindingInstance) (m : ℕ)
    (doc : Doc) : Except String Unit :=
  let layout := Reference.allocateReferenceLayout setup.ops inst m
  let real := Reference.referenceShorCircuit setup inst m
  match instantiate doc "shor" (shorEnv setup inst layout) 400 with
  | .error e => .error s!"template check (shor): instantiate: {e}"
  | .ok g =>
      if lowGateAgrees g real then .ok ()
      else .error
        s!"template check (shor): instantiate disagrees with the real term at N={inst.N}, m={m}"

/-- `shor` canary at the small instance. -/
def checkShor (setup : Shor.ShorLoweringSetup) (doc : Doc) : Except String Unit :=
  checkShorAt setup canaryInst 0 doc

/-! =========================================================
    The hand-stated leaf templates
========================================================= -/

/-- `naive_leaf` agreement at one `(xw, zw)` pair.

`naiveLeafTemplate` is written out by hand, not reflected: its source
(`naiveSignedPhaseGates`) is a double fold over a *symbolic-length* list,
which no equation lemma turns into a visible loop the way `.eq_1` does for
`WellFounded.fix`. What stands behind it is this comparison and nothing
else, which is why the evaluation tier runs it at widths well past the 1..6
pairs `Tests.lean`'s R2.3 covers — and at unequal ones, since the loop
bounds are the one place `xw` and `zw` could be transposed without any equal
pair noticing. -/
def checkNaiveLeafAt (doc : Doc) (xw zw : ℕ) : Except String Unit :=
  let x := ExtReg.ofReg (Reg.interval 0 xw)
  let z := ExtReg.ofReg (Reg.interval xw zw)
  let phi : Angle := (3 : ℚ) / 7
  let real := LowGate.Naive_SignedPhaseProd phi x z
  let env : Env :=
    { w := fun n => if n == "xw" then some xw else if n == "zw" then some zw else none
      a := fun n => if n == "phi" then some phi else none
      r := fun n => if n == "x" then some x else if n == "z" then some z else none
      opaqueW := fun _ _ => none
      coeff := fun _ _ => none }
  match instantiate doc "naive_leaf" env 10 with
  | .error e => .error s!"template check (naive_leaf): instantiate: {e}"
  | .ok g =>
      if lowGateAgrees g real then .ok ()
      else .error s!"template check (naive_leaf): instantiate disagrees at (xw, zw) = ({xw}, {zw})"

/-- `naive_cleaf` agreement at one `(xw, zw)` pair, controlled counterpart of
`checkNaiveLeafAt`. The control qubit sits past both registers. -/
def checkNaiveCLeafAt (doc : Doc) (xw zw : ℕ) : Except String Unit :=
  let ctrlIdx := xw + zw + 1
  let ctrl := ExtReg.ofReg (Reg.interval ctrlIdx 1)
  let x := ExtReg.ofReg (Reg.interval 0 xw)
  let z := ExtReg.ofReg (Reg.interval xw zw)
  let phi : Angle := (3 : ℚ) / 7
  let real := LowGate.Naive_CSignedPhaseProd ctrlIdx phi x z
  let env : Env :=
    { w := fun n => if n == "xw" then some xw else if n == "zw" then some zw else none
      a := fun n => if n == "phi" then some phi else none
      r := fun n =>
        if n == "ctrl" then some ctrl
        else if n == "x" then some x
        else if n == "z" then some z
        else none
      opaqueW := fun _ _ => none
      coeff := fun _ _ => none }
  match instantiate doc "naive_cleaf" env 10 with
  | .error e => .error s!"template check (naive_cleaf): instantiate: {e}"
  | .ok g =>
      if lowGateAgrees g real then .ok ()
      else .error
        s!"template check (naive_cleaf): instantiate disagrees at (xw, zw) = ({xw}, {zw})"

/-! =========================================================
    Which widths to check, derived from the table itself
========================================================= -/

/-- How many levels of recursion `phase_product` takes starting from
symmetric operand widths `n`.

The guard is `nextSignedWidth x z ops < phaseInputSize x z`, and
`scanNeededWidths`/`phaseLimbWidth` look only at active widths, so it is
`nextWidth ops wx wz < max wx wz`; a recursive call grows *both* children to
`nextWidth`, so the chain from a symmetric start stays symmetric and is just
`n ↦ nextWidth ops n n`. The chain strictly decreases while it runs, so any
`fuel ≥ n` is non-binding. -/
def ppRecursionDepth {k : ℕ} (ops : Prog k) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n =>
      let n' := RecursivePhaseWorkspace.nextWidth ops n n
      if n' < n then ppRecursionDepth ops fuel n' + 1 else 0

/-- How many levels the phase product *embedded in* `qft` at register width
`w` takes. `qft` splits its register at `splitM r = regSize r / 2` and calls
`phase_product` on the pair `(w / 2, w - w / 2)` — unequal at every odd `w`,
which is the one shape `ppRecursionDepth`'s symmetric chain never reaches. -/
def qftPPRecursionDepth {k : ℕ} (ops : Prog k) (w : ℕ) : ℕ :=
  let xw := w / 2
  let zw := w - xw
  let w' := RecursivePhaseWorkspace.nextWidth ops xw zw
  if w' < max xw zw then ppRecursionDepth ops w w' + 1 else 0

/-- How far up the width search for a recursion ladder goes. Generous: the
standard table's three-level width is 15 at `k = 2` and 275 at `k = 6`, and
a table with wider limbs pushes it further still. -/
def widthSearchBound : ℕ := 1024

/-- The phase-product widths a table is checked at: the largest width that
still takes the *base* case, then the smallest width reaching one, two and
three levels of recursion.

Derived from the table's own `nextWidth` chain rather than fixed, because a
fixed pair cannot do this job. The retired `[8, 16]` was chosen against the
`k = 2` standard ladder; a table with one more adder in it moves every
width in the chain, and at `k = 6` the standard table does not recurse at
all below `n = 261`. Three levels, not one, is what makes the *grandchild*
of a recursive call exist — which is where the reserve-split bug of
`PLAN.md` §1.1 lived, invisible at every width `[8, 16]` sampled.

A table that never recurses below `widthSearchBound` (none is known) falls
back to the single representative `4k` the run-time canary always used. -/
def ppWidthLadder {k : ℕ} (ops : Prog k) : List ℕ :=
  let depths := [1, 2, 3].filterMap fun d =>
    (List.range widthSearchBound).find? fun n => d ≤ ppRecursionDepth ops widthSearchBound n
  match depths with
  | [] => [4 * k]
  | n₁ :: _ => ((if 1 < n₁ then [n₁ - 1] else []) ++ depths).eraseDups

/-- The `qft` widths a table is checked at: `4` and `8` as before, `9` for an
odd `regSize` (the `splitM` split is unequal exactly then, and `qft` is the
only caller that ever hands `phase_product` an unequal pair), and the
smallest *odd* width whose embedded phase product recurses — so one checked
width exercises both at once. -/
def qftWidthLadder {k : ℕ} (ops : Prog k) : List ℕ :=
  let deepOdd := (List.range widthSearchBound).find? fun w =>
    w % 2 = 1 && 0 < qftPPRecursionDepth ops w
  ([4, 8, 9] ++ deepOdd.toList).eraseDups

/-! =========================================================
    The same checks, as one `Bool` a submission can pin
========================================================= -/

/-- `Except.isOk`, spelled out so the `Bool` checks below reduce cleanly
under `native_decide` (the error strings are `String`s built by `s!`, which
there is no reason to evaluate just to discard). -/
def okB {ε α : Type} : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

/-- The widths a submission's `phase_product`/`cphase_product` templates are
checked at: `ppWidthLadder` on the submission's own table.

What the ladder buys over a fixed pair, in the terms the two historical
measurements were recorded in. Both were at `k = 2`, both passed at `n = 8`
and failed at `n = 16`:

* the canonical ladder plus a semantically-inert `shiftL 0 0 ;; shiftR 0 0`
  pair, checked against a `Doc` extracted from the canonical ladder
  *without* it. The compiled circuits really do coincide at `n = 8`, the
  extra ops being inert; at the recursive width the recursion's
  `nextWidth`/`reserveNeed` are computed from the op list and the two
  tables' lists differ. A ladder derived from the table's own chain sees
  this sooner, since the two tables' ladders are themselves different.
* a table whose `phaseProduct` checkpoints do not all sit on register 0,
  checked against its *own* `Doc`. That one was a real bug in the extractor
  — the top chunk's reserve capacity, `PLAN.md` §1.1 — fixed, and anchored
  by `Emit/Tests.lean`'s `T1_1_TopChunkReserve` section. It needed a
  *grandchild* of the top-level call to exist, which is why the ladder goes
  three levels deep and not one. -/
def submissionPPWidths (setup : Shor.ShorLoweringSetup) : List ℕ := ppWidthLadder setup.ops

/-- The `(xw, zw)` pairs the hand-stated leaf templates are checked at.

Unequal and well past `Tests.lean`'s R2.3/R2.4 range (1..6 on both sides),
in both orders, because the leaves' two loop bounds are independent and a
square check cannot tell them apart. The pairs are small enough to cost
nothing: `(13, 7)` is 91 `CPhase`s. -/
def submissionLeafWidths : List (ℕ × ℕ) := [(13, 7), (7, 13), (6, 5)]

/-- The reserve regimes each phase-product width is checked in.

Not a detail of the harness: `ReserveBudget.ofRequirements`/`fillSlack` pay
each child its `requiredChildReserve` and give the *whole* remainder to the
top chunk, so a register carrying exactly `reserveNeed` and one carrying
`reserveNeed + 64` drive genuinely different reserve arithmetic below the
first recursive call. Checking only one of them is what let §1.1's bug sit
unseen: `ppRegisters` used to hand out exactly one spare qubit, always. -/
def submissionPPSlacks : List ℕ := [0, 64]

/-- The widths a submission's `qft` template is checked at: `qftWidthLadder`
on the submission's own table. -/
def submissionQFTWidths (setup : Shor.ShorLoweringSetup) : List ℕ := qftWidthLadder setup.ops

/-- The reference Shor instances `shor_gate` is checked at, as
`(instance, precision)` pairs.

Two, and the second is the one that earns its place. `canaryInst` at `m = 0`
is four bits of modulus and a short exponent loop — enough to reach every
construct, not enough to tell a correct loop template from one that is right
for its first two steps. `largeInst` at `m = 1` is eight bits and a longer
loop, and the `m`-dependent register widths differ from the `m = 0` ones.
Both the Hadamard loop and the exponent loop are hand-stated template bodies
(`PLAN.md` T3.4), so a second instance is the only thing separating them
from their first two iterations.

`shor_gate` keeps the modular arithmetic as opaque `Gate`s, so its
comparison is 66 ms at `largeInst`; `submissionShorInstances` runs the fully
lowered `shor` at the same pair. -/
def submissionShorGateInstances : List (ShorOrderFindingInstance × ℕ) :=
  [(canaryInst, 0), (largeInst, 1)]

/-- The reference Shor instances the *fully lowered* `shor` is checked at.

The same two, which was not always affordable. With the old comparison
(`flattenLowGate a == flattenLowGate b`) `largeInst` at `m = 1` did not
finish: `LowGate`'s derived `BEq` walks an `.adj` element one stack frame
per nested gate, and the interpreter aborted the process outright rather
than returning a verdict. `lowGateAgrees` compares a flat leaf-token stream
instead, and the same circuit — 247 428 tokens — now compares in about
1.5 s. -/
def submissionShorInstances : List (ShorOrderFindingInstance × ℕ) :=
  [(canaryInst, 0), (largeInst, 1)]

/-- **The evaluation tier.** `verifyDoc`'s checks, with two differences:
ladders of widths, reserve regimes and reference instances instead of a
single representative apiece, and a `Bool` instead of an `Except` so a
submission can pin the result with `native_decide` at build time rather than
running it at print time.

This is evaluation, not a theorem: it does not establish that the extracted
IR is correct at *every* width. What a submission is held to is the four
kernel-checked side conditions on its table (proved in
`Submission/Template.lean`, decided by `Submission/Decide.lean`, audited by
`Submission/Audit.lean`), plus `instantiate = real` verified here at these
sampled widths, reserve regimes and reference instances, against the
submitter's own points. -/
def evaluationChecks (setup : Shor.ShorLoweringSetup) (doc : Doc)
    (ppWidths ppSlacks qftWidths : List ℕ) (leafWidths : List (ℕ × ℕ))
    (gateInsts flatInsts : List (ShorOrderFindingInstance × ℕ)) : Bool :=
  doc.wellFormed
    && ppWidths.all (fun n => ppSlacks.all fun s => okB (checkPhaseProductAt setup n doc s))
    && ppWidths.all (fun n => ppSlacks.all fun s => okB (checkCPhaseProductAt setup n doc s))
    && qftWidths.all (fun w => okB (checkQftAt setup w doc))
    && leafWidths.all (fun p => okB (checkNaiveLeafAt doc p.1 p.2))
    && leafWidths.all (fun p => okB (checkNaiveCLeafAt doc p.1 p.2))
    && gateInsts.all (fun im => okB (checkShorGateAt setup im.1 im.2 doc))
    && flatInsts.all (fun im => okB (checkShorAt setup im.1 im.2 doc))

/-- `evaluationChecks` at the sampled widths this table derives. This is the
single `Bool` `Submission/Check.lean` pins, so the acceptance build carries
one `native_decide` line and none of the machinery behind it — and no
submitter writes it. -/
def submissionChecks (setup : Shor.ShorLoweringSetup) (doc : Doc) : Bool :=
  evaluationChecks setup doc (submissionPPWidths setup) submissionPPSlacks
    (submissionQFTWidths setup) submissionLeafWidths
    submissionShorGateInstances submissionShorInstances

/-- The full canary suite, as an `Except` whose error names the first check
that failed: exactly `submissionChecks`' sampling, run at print time instead
of pinned at build time.

The same lists, deliberately (`PLAN.md` T2.5). The run-time canary used to
sample one representative width per template, `4k`, which at `k = 2` is `8`
— the base case, so `forshor_emit template 2` never once exercised
`phase_product`'s recursion. Two tiers that sample differently are two
tiers, and the weaker one is the one a reader meets first.

Every check runs for every setup. A `ShorLoweringSetup` is, by construction,
a table the reference-instance machinery is proven to work over (D5), so
`shor_gate`/`shor` are never skipped. -/
def verifyDoc (setup : Shor.ShorLoweringSetup) (doc : Doc) : Except String Unit := do
  if doc.wellFormed then pure () else .error "extracted doc is not well-formed"
  for n in submissionPPWidths setup do
    for s in submissionPPSlacks do
      checkPhaseProductAt setup n doc s
      checkCPhaseProductAt setup n doc s
  for w in submissionQFTWidths setup do
    checkQftAt setup w doc
  for (xw, zw) in submissionLeafWidths do
    checkNaiveLeafAt doc xw zw
    checkNaiveCLeafAt doc xw zw
  for (inst, m) in submissionShorGateInstances do
    checkShorGateAt setup inst m doc
  for (inst, m) in submissionShorInstances do
    checkShorAt setup inst m doc

/-- Run-time entry point: extract, then verify. R3's blocking run-time
check — a failure here refuses the whole `bundle`/`template` output with
exit 3 (`Main.lean`). Standard-table only at run time — `runExtract`
already fixes this. -/
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
