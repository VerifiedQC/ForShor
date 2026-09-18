import Lean
import FastMultiplication.Emit.IR.Syntax
import FastMultiplication.Emit.Reflect.Quote
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Compile
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Lowering.Lower
import FastMultiplication.ShorVerification.Implementation.QFT.Lowering.PlanBuilders
import FastMultiplication.ShorVerification.Implementation.Shor.Circuit.OrderFinding

/-!
# The extractor: shared machinery

Generic pieces used by every `Reflect/Targets.lean` extraction, factored out
of the R2.1 spike (`PLAN.md` §5.5) once it had de-risked the approach:
building a structure literal with fine-grained fresh leaves (Finding 1), and
a `Registry`-driven translator rather than a fully general one (Finding 2)
— `translateW`/`translateA`/`translateReg` first check whether the *exact*
`Expr` they were handed is one the Specialise step already built and named
(a slot, a width parameter, an angle parameter, …), and only fall back to
structural recognition (arithmetic, register-slicing constructors, the
opaque-function escape hatch) for the handful of shapes a given target
actually produces. An unrecognised shape is a hard error naming the
constant (D2), never a silent guess.
-/

namespace Shor.Reflect

open Lean Lean.Meta

/-- `fun (i : Fin k) => if i.val = 0 then vals[0] else if i.val = 1 then
vals[1] else … else vals[last]`, for concrete `k = vals.size`. Used to give
a dependent record's data field (e.g. `PhaseSplitLayout.reserve : Fin k →
Reg`) a real value built from `k` fresh leaves instead of one opaque
function variable (Finding 1). -/
partial def buildFinFnGo (elemTy ival : Expr) (vals : Array Expr) (n : Nat) : MetaM Expr := do
  if n + 1 = vals.size then
    pure vals[n]!
  else
    let cond ← mkAppM ``Eq #[ival, mkNatLit n]
    let elseE ← buildFinFnGo elemTy ival vals (n + 1)
    mkAppOptM ``ite #[some elemTy, some cond, none, some vals[n]!, some elseE]

def buildFinFn (finKTy elemTy : Expr) (vals : Array Expr) : MetaM Expr :=
  withLocalDecl `i .default finKTy fun i => do
    let ival ← mkAppM ``Fin.val #[i]
    let body ← buildFinFnGo elemTy ival vals 0
    mkLambdaFVars #[i] body

/-- Apply `declName` to `givenArgs` positionally against its own Pi-type
telescope, filling any `none` position with `sorry` at that position's
type. Every `none` position here is always a `Prop` field that translation
erases anyway (they're never inspected by `translateNode`/`translateW`/…);
`mkAppOptM` itself refuses to return a result containing unresolved
metavariables, hence this hand-rolled walk instead of `mkAppOptM` throughout. -/
partial def appFillingSorry (declName : Name) (givenArgs : Array (Option Expr)) : MetaM Expr := do
  let mut ty ← inferType (mkConst declName)
  let mut args : Array Expr := #[]
  for given in givenArgs do
    match ty with
    | .forallE _ dom body _ =>
        let argVal ← match given with
          | some v => pure v
          | none => mkSorry dom false
        args := args.push argVal
        ty := body.instantiate1 argVal
    | _ => throwError "appFillingSorry: too many arguments for {declName}"
  return mkAppN (mkConst declName) args

/-- Everything a target's `translate*` functions consult instead of
reflecting generically: named `Expr`s the Specialise step already built,
matched by `isDefEq` (not just syntactic equality — respects `whnf`-visible
defeq, e.g. a slot `Expr` built one way and encountered another). -/
structure Registry where
  /-- Register-valued `Expr`s known by construction, most-specific first
  (`lookupReg` returns the first match, so slices should precede the
  registers they slice). -/
  regs : Array (Expr × IR.RegExpr) := #[]
  /-- Nat-valued `Expr`s known by construction (register widths, table `k`,
  interpolation-term indices, …). -/
  widths : Array (Expr × IR.WExpr) := #[]
  /-- Angle-valued `Expr`s known by construction (an `AExpr.var` parameter). -/
  angles : Array (Expr × IR.AExpr) := #[]
  /-- The target's `phaseCoeff : Fin (q k) → ℚ` parameter, if it has one:
  recognising `phaseCoeffFVar l` for a literal `l` is how `AExpr.coeff`
  gets produced (D4: the interpolation weight is opaque). -/
  phaseCoeffFVar : Option FVarId := none
  /-- The `m` (limb-width) `WExpr` `AExpr.coeff`'s second argument is built
  from, when `phaseCoeffFVar` is set. -/
  coeffMExpr : IR.WExpr := .lit 0
  /-- Arguments to emit for a recognised `commonNeededWidth` ("nextWidth")
  call — fixed per target (e.g. `[xw, zw]`), never read off the actual
  `Expr` (D4: opaque by name, the argument is never inspected). -/
  nextWidthArgs : List IR.WExpr := []

def Registry.lookupReg (reg : Registry) (e : Expr) : MetaM (Option IR.RegExpr) := do
  for (cand, r) in reg.regs do
    if ← isDefEq e cand then return some r
  return none

def Registry.lookupWidth (reg : Registry) (e : Expr) : MetaM (Option IR.WExpr) := do
  for (cand, w) in reg.widths do
    if ← isDefEq e cand then return some w
  return none

def Registry.lookupAngle (reg : Registry) (e : Expr) : MetaM (Option IR.AExpr) := do
  for (cand, a) in reg.angles do
    if ← isDefEq e cand then return some a
  return none

/-- Read a natural-number literal off a `Expr`, reducing only via `whnfR`
(never a full `whnf`) to expose it. Originally used full `whnf`: harmless
for `pp_body` (nothing there both (a) needed `natLit?` to reduce through a
non-reducible `def` and (b) was expensive to reduce), but calling `natLit?`
on `Shor.nextSignedWidth x z ops` — checked *before* any pattern match gets
a chance, same as `Min.min`'s failure mode — sends a full `whnf` chasing
`commonNeededWidth`'s `Finset.univ.sup` over a symbolic-valued function,
which is not just "the wrong shape" the way `Decidable.rec` was, it is
*expensive enough to time out*. `whnfR` still performs the reduction this
function actually needs elsewhere (e.g. `Fin.val ⟨n, _⟩ → n` is iota
reduction on an already-concrete constructor, not unfolding a non-reducible
`def`), just never that. -/
def natLit? (e : Expr) : MetaM (Option Nat) := do
  match ← getNatValue? e with
  | some n => return some n
  | none =>
      let e' ← whnfR e
      match e' with
      | .lit (.natVal n) => return some n
      | _ =>
          -- `whnfR` on a projection like `Fin.val ⟨0, _⟩` can land on an
          -- `OfNat.ofNat`-wrapped literal rather than a raw `Expr.lit`
          -- (confirmed empirically) — `getNatValue?` recognises that shape
          -- but was only ever tried on the *pre*-reduction `e` above.
          match ← getNatValue? e' with
          | some n => return some n
          | none => return e'.rawNatLit?

/-- `natLit?`'s counterpart for `Fin.val` on an interpolation/phase-term
index (`Fin (q k)`, `k` concrete): unlike a *width* expression, this value
can never be `nextWidth`/`reserveNeed`-opaque or otherwise symbolic — it is
always ground arithmetic over the concrete `k`/list-position data a
specialised extraction already fixed (e.g. `Fin.val ⟨0 + 1, _⟩`, `whnfR`
alone doesn't compute `0 + 1` since `HAdd.hAdd`'s instance chain isn't all
`@[reducible]`). A full `whnf` is therefore safe here specifically — the
`Min`/`Max`/`nextWidth` cascade risk that rules it out for `natLit?` never
applies to a `Fin (q k)` index. -/
def finValLit? (e : Expr) : MetaM (Option Nat) := do
  match ← getNatValue? e with
  | some n => return some n
  | none =>
      let e' ← whnf e
      match ← getNatValue? e' with
      | some n => return some n
      | none => return e'.rawNatLit?

/-- `unfoldDefinition?` on a *named* structure-projector constant applied to
an argument (e.g. `Shor.Gate.PhaseProdWorkspace.xReserve rhs`) reduces it in
one step — but, once the projected field is itself another structure
projection, the result is Lean's *low-level* `Expr.proj structName idx
scrutinee` form, not the named-constant application `translateReg`/
`translateW`'s `getAppFnArgs`-based dispatch expects (confirmed empirically:
`ws.xReserve` on `ofExtRegs`'s `.eq_1` literal reduces to a bare `.proj`
node for `ExtReg.reserve`, invisible to every named case below). This
rebuilds the named form (`structName.fieldName scrutinee`) from a `.proj`
node so the ordinary dispatch gets another look, looping since the rebuilt
application can itself unfold to another `.proj` one level down. Returns `e`
unchanged once it is no longer `.proj`-headed. -/
partial def unfoldProj (e : Expr) : MetaM Expr := do
  match e with
  | .proj structName idx scrutinee => do
      let scrutinee' ← whnfR scrutinee
      let env ← getEnv
      let ctorName := (getStructureCtor env structName).name
      if scrutinee'.isAppOf ctorName then
        -- The scrutinee is *already* a literal constructor application
        -- (e.g. `ofExtRegs`'s `.eq_1` RHS): the field access is a genuine
        -- iota reduction, so index straight into its args (the structure's
        -- own parameters first, then fields in declaration order) — this is
        -- the step neither `unfoldDefinition?` nor a rebuilt named-projector
        -- application ever performs on their own (confirmed empirically: a
        -- projector applied to an already-literal struct is not itself
        -- further reducible by either, so rebuilding the named form just
        -- reproduces the same stuck shape — an `unfoldProj` ↔
        -- `resolvePhaseReserve`/`translateW` loop).
        let numParams := (getStructureCtor env structName).numParams
        return scrutinee'.getAppArgs[numParams + idx]!
      else
        -- Not yet a literal: rebuild the named `StructName.fieldName`
        -- application (reading the structure's own parameters off
        -- `scrutinee`'s inferred type, since a bare `mkConst` can't supply
        -- them) so `translateReg`/`translateW`'s ordinary named-constant
        -- dispatch gets a chance to recognise *this* layer by name (e.g.
        -- `ExtReg.withReserve`) instead.
        let fields := getStructureFields env structName
        let some fieldName := fields[idx]?
          | throwError "unfoldProj: field index {idx} out of range for {structName}"
        let scrutineeTy ← inferType scrutinee
        let projConst := mkConst (structName ++ fieldName)
        return mkAppN projConst (scrutineeTy.getAppArgs ++ #[scrutinee])
  | _ => return e

/-- `QFTWorkspaceOK.phaseWorkspace hworkspace hsize`'s `.eq_1` (a tactic-mode
`:= by ...; exact {xReserve := xWork, zReserve := zWork, ...}` def, same
shape as `planCompiledSignedPhaseGate`), applied to whatever it's currently
applied to. Returns the argument unchanged if it isn't `phaseWorkspace`-
headed, so callers can test `rhs == wsE` to detect "no progress possible"
without a separate `Option`. Needed because `ws.xReserve`/`.zReserve`
(`qft`'s embedded `PhaseProdWorkspace`, reused verbatim as `xWork`/`zWork`
at every recursion level) sits behind a raw structure-field accessor:
`unfoldDefinition?` on the accessor alone can't make progress until the
*argument* (`hworkspace.phaseWorkspace hlarge`) is itself exposed as a
concrete constructor, and a blind `whnf` of the whole projection gets stuck
partway through the tactic proof's `have`/cast machinery (confirmed
empirically) the same way `planCompiledSignedPhaseGate` did before its own
`.eq_1` fix. -/
partial def unfoldPhaseWorkspace (wsE : Expr) : MetaM Expr := do
  let ws' ← whnfR wsE
  if ws'.isAppOf ``Shor.QFTWorkspaceOK.phaseWorkspace || ws'.isAppOf ``Shor.Gate.PhaseProdWorkspace.ofExtRegs then
    let some eqns ← Lean.Meta.getEqnsFor? ws'.getAppFn.constName! | return wsE
    let some eqnName := eqns[0]? | return wsE
    let eqApp := mkAppN (mkConst eqnName) ws'.getAppArgs
    return (← inferType eqApp).getAppArgs[2]!
  else
    -- R2.6: `ModMulCircuitWorkspaceOK.step1Workspace`/`.step2Workspace`/
    -- `.step5Workspace` are plain (non-reducible) `def`s that merely apply
    -- `Gate.PhaseProdWorkspace.ofExtRegs` to already-known registers —
    -- `whnfR` alone (reducible-only) never unfolds them, so a bounded
    -- `unfoldDefinition?` loop first exposes the `ofExtRegs` application
    -- (its enclosing `let`s zeta-reduce under the next `whnfR`), then the
    -- branch above fires exactly as it does for `QFTWorkspaceOK.phaseWorkspace`.
    match ← unfoldDefinition? ws' with
    | some ws'' => unfoldPhaseWorkspace ws''
    | none => return wsE

mutual
/-- `Min ℕ`/`Max ℕ`'s instances unfold, under `whnf`, straight through
`Min.min`/`Max.max` into a raw `Decidable.rec` case split on a stuck
`Nat.decLe` witness once the operands are symbolic — `whnf` doesn't stop at
intermediate stages, it cascades until nothing is left to unfold. So
recognising `Min.min`/`Max.max` (and every other "nice" pattern below) must
happen *before any reduction at all*, and the fallback when a head like
`Shor.phaseLimbWidth` (a plain, not-yet-unfolded `def`) doesn't match
anything must unfold *one delta step* (`unfoldDefinition?`, replacing the
head with its literal body — no further reduction), not a full `whnf`,
precisely so the next recogniser gets a chance before the cascade would
carry it past `Min.min`/`Max.max` too. Confirmed empirically: an
unconditional `whnf`-first ordering produces the stuck `Decidable.rec` term
instead of `Min.min`, even one `whnf` call deep into the fallback. -/
partial def translateW (reg : Registry) (e : Expr) : MetaM IR.WExpr := do
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => return .add (← translateW reg a) (← translateW reg b)
  | (``HSub.hSub, #[_, _, _, _, a, b]) => return .sub (← translateW reg a) (← translateW reg b)
  | (``HMul.hMul, #[_, _, _, _, a, b]) => return .mul (← translateW reg a) (← translateW reg b)
  | (``HDiv.hDiv, #[_, _, _, _, a, b]) => return .div (← translateW reg a) (← translateW reg b)
  | (``HMod.hMod, #[_, _, _, _, a, b]) =>
      -- D4: opaque outright, by constant name — R2.6's Step 1/5 phase-load
      -- constants (`(c + N - 1) % N`, `step5Constant c N % N`) are `Nat.mod`
      -- on genuinely symbolic operands. Recognised *before* any reduction,
      -- same discipline as `Min.min`/`Max.max` above: `Nat.mod` is defined by
      -- well-founded recursion, so an unrecognised `%` falling through to
      -- `translateWFallback`'s last-resort `whnf` cascades into `Acc.rec`
      -- machinery instead of stopping (confirmed empirically — this is what
      -- actually caused the R2.6 `isDefEq` timeout, not anything about `%`
      -- itself being hard to name).
      return .opaque "mod" [← translateW reg a, ← translateW reg b]
  | (``HPow.hPow, #[_, _, _, _, a, b]) =>
      -- D4: opaque outright, by constant name — same discipline and
      -- justification as `HMod.hMod` above. `ASize r := 2 ^ regSize r`
      -- (R2.6's `fastConstMulInto`) is the one case seen so far; `Nat.pow`
      -- on a symbolic exponent has the same well-founded-recursion cascade
      -- risk `Nat.mod` does.
      return .opaque "pow" [← translateW reg a, ← translateW reg b]
  | (``Nat.pow, #[a, b]) =>
      -- The `HPow.hPow` instance for `Nat` unfolds straight to a bare
      -- `Nat.pow` application (no further typeclass indirection) once
      -- something upstream (`qNatW`'s `Nat.cast` recursion, here) has
      -- already peeled the instance away — same opaque treatment.
      return .opaque "pow" [← translateW reg a, ← translateW reg b]
  | (``Shor.step5Constant, #[cE, nE]) =>
      -- D4: opaque outright, by constant name — `step5Constant`'s `dite`
      -- guard is `∃ cinv, cinv < N ∧ (c * cinv) % N = 1`, decided via
      -- `Nat.find` on a symbolic `N`: not just non-reducible but genuinely
      -- undecidable-looking to `whnf`, which strands a raw `Decidable.rec`
      -- case split (confirmed empirically) rather than the clean `dite`
      -- `translateNode`'s own `dite` case expects.
      return .opaque "step5Const" [← translateW reg cE, ← translateW reg nE]
  | (``Max.max, #[_, _, a, b]) => return .max (← translateW reg a) (← translateW reg b)
  | (``Min.min, #[_, _, a, b]) => return .min (← translateW reg a) (← translateW reg b)
  | (``Nat.log2, #[nE]) =>
      -- D4: opaque outright, by constant name — `referenceXWidth`/
      -- `referenceWorkWidth`/`cmpLtNWWidth` (R2.6) all size registers off
      -- `Nat.log2` of a symbolic `N`, which has no closed form in `WExpr`.
      return .opaque "log2" [← translateW reg nE]
  | (``Shor.commonNeededWidth, _) =>
      -- D4: opaque outright, by constant name — never inspect the argument
      -- (which genuinely depends on the table; PLAN.md §5.5 Finding 2).
      return .opaque "nextWidth" reg.nextWidthArgs
  | (``Shor.nextSignedWidth, #[_, _, _, _]) =>
      -- `nextSignedWidth a b ops := commonNeededWidth (scanNeededWidths a b
      -- ops)` — recognised directly by name (D4), same as
      -- `commonNeededWidth` itself, rather than relying on
      -- `unfoldDefinition?` to expose it: cheap and, more importantly,
      -- avoids ever asking anything to reduce into `Finset.univ.sup`.
      return .opaque "nextWidth" reg.nextWidthArgs
  | (``Shor.RecursivePhaseWorkspace.nextWidth, #[_, _, wxE, wzE]) =>
      return .opaque "nextWidth" [← translateW reg wxE, ← translateW reg wzE]
  | (``Prod.fst, #[_, _, pairE]) =>
      match pairE.getAppFnArgs with
      | (``Shor.RecursivePhaseWorkspace.reserveNeed, #[_, _, wxE, wzE]) =>
          return .opaque "reserveNeed_x" [← translateW reg wxE, ← translateW reg wzE]
      | (``Shor.qftWorkspaceNeed, #[_, _, wE]) =>
          return .opaque "qftXWork" [← translateW reg wE]
      | _ => translateWFallback reg e
  | (``Prod.snd, #[_, _, pairE]) =>
      match pairE.getAppFnArgs with
      | (``Shor.RecursivePhaseWorkspace.reserveNeed, #[_, _, wxE, wzE]) =>
          return .opaque "reserveNeed_z" [← translateW reg wxE, ← translateW reg wzE]
      | (``Shor.qftWorkspaceNeed, #[_, _, wE]) =>
          return .opaque "qftZWork" [← translateW reg wE]
      | _ => translateWFallback reg e
  | (``Shor.regSize, #[rE]) =>
      -- `regSize`/`Reg.width` is an ordinary computable `List.length`, not
      -- D4-opaque — but on a symbolic-length register it can't reduce, so
      -- `leftReg`/`rightReg`'s effect on it (`w/2`, `w - w/2`) is named
      -- directly rather than left for `unfoldDefinition?` to get stuck on.
      match rE.getAppFnArgs with
      | (``Shor.leftReg, #[srcE]) =>
          return .div (← translateW reg (← mkAppM ``Shor.regSize #[srcE])) (.lit 2)
      | (``Shor.rightReg, #[srcE]) => do
          let srcW ← translateW reg (← mkAppM ``Shor.regSize #[srcE])
          return .sub srcW (.div srcW (.lit 2))
      -- A *bare* `Reg.drop` (R2.6: `ofExtRegs`'s `dataNoCarry.reserve =
      -- y.reserve.drop 1`, once `unfoldProj` resolves the field access down
      -- to it): `regSize (r.drop n) = regSize r - n`.
      | (``Shor.Reg.drop, #[srcE, loE]) =>
          return .sub (← translateW reg (← mkAppM ``Shor.regSize #[srcE])) (← translateW reg loE)
      -- `regSize r.active = r.width` by definition (R2.6:
      -- `CmodMulInPlaceCore`'s `regSize (data.grow 1).active`) — routes
      -- through `ExtReg.width`'s own `.grow`/`.withReserve` cases below
      -- instead of falling to the generic `unfoldDefinition?` chain, which
      -- gets stuck on `ExtReg.active`'s low-level `.proj` form the same way
      -- `resolvePhaseReserve`'s callers did.
      | (``Shor.ExtReg.active, #[parentE]) =>
          translateW reg (← mkAppM ``Shor.ExtReg.width #[parentE])
      -- `regSize r.reserve = r.capacity` by definition, same as `.active`
      -- above — needed once `unfoldProj` rebuilds `ExtReg.reserve
      -- (ExtReg.withReserve _ reserveE _)` (R2.6's `capacity`-of-`.xExt`
      -- chain): without this case that shape only unwraps one layer per
      -- `unfoldDefinition?`/`unfoldProj` round trip, effectively never
      -- reaching `reserveE` itself (confirmed empirically — this is what
      -- looked like `unfoldPhaseWorkspace` "losing" its progress on a
      -- second call).
      | (``Shor.ExtReg.reserve, #[parentE]) =>
          translateW reg (← mkAppM ``Shor.ExtReg.capacity #[parentE])
      | (``Shor.qftXWork, #[_, _, parentE]) =>
          return .opaque "qftXWork" [← translateW reg (← mkAppM ``Shor.ExtReg.width #[parentE])]
      | (``Shor.qftZWork, #[_, _, parentE]) =>
          return .opaque "qftZWork" [← translateW reg (← mkAppM ``Shor.ExtReg.width #[parentE])]
      -- `qft`'s `ws.xReserve`/`.zReserve` (`PhaseProdWorkspace.phaseWorkspace`
      -- reuses `xWork`/`zWork` verbatim as each level's own reserve pool):
      -- `unfoldPhaseWorkspace` exposes the struct literal (once `ws` is
      -- `phaseWorkspace`-headed), then the projection on that literal is a
      -- plain iota reduction the generic fallback below handles fine.
      -- (R2.6: `CmpLtNWWorkspace.mulWorkspace hstep4` needs the same named
      -- shortcut here `resolvePhaseReserve`'s doc comment explains — bare
      -- projection on a genuinely opaque `hstep4`, no amount of unfolding
      -- exposes an `ofExtRegs` application.)
      | (``Shor.Gate.PhaseProdWorkspace.xReserve, #[_, _, wsE]) =>
          match wsE.getAppFnArgs with
          | (``Shor.CmpLtNWWorkspace.mulWorkspace, #[_, _, workE, _, _, _]) =>
              translateW reg (← mkAppM ``Shor.ExtReg.capacity #[workE])
          | _ => do
            let rhs ← unfoldPhaseWorkspace wsE
            if rhs == wsE then translateWFallback reg e
            else
              -- Same `unfoldDefinition?` (one step) + `unfoldProj` discipline
              -- as `resolvePhaseReserve` (not `translateWFallback`'s `whnf`,
              -- which over-reduces past the field access the same way it did
              -- in `translateReg` — confirmed empirically here too).
              match ← unfoldDefinition? (← mkAppM ``Shor.Gate.PhaseProdWorkspace.xReserve #[rhs]) with
              | some e' => translateW reg (← mkAppM ``Shor.regSize #[← unfoldProj e'])
              | none => translateWFallback reg e
      | (``Shor.Gate.PhaseProdWorkspace.zReserve, #[_, _, wsE]) =>
          match wsE.getAppFnArgs with
          | (``Shor.CmpLtNWWorkspace.mulWorkspace, #[_, _, _, scratchE, _, _]) =>
              translateW reg (← mkAppM ``Shor.ExtReg.capacity #[scratchE])
          | _ => do
            let rhs ← unfoldPhaseWorkspace wsE
            if rhs == wsE then translateWFallback reg e
            else
              match ← unfoldDefinition? (← mkAppM ``Shor.Gate.PhaseProdWorkspace.zReserve #[rhs]) with
              | some e' => translateW reg (← mkAppM ``Shor.regSize #[← unfoldProj e'])
              | none => translateWFallback reg e
      | _ =>
          -- Same one-layer-at-a-time discipline as `ExtReg.width`/
          -- `.capacity` below: a blind `unfoldDefinition?` on the whole
          -- `regSize rE` gets stuck on the same non-unfoldable
          -- `List.length` head `ExtReg.width`'s doc comment describes.
          match ← reg.lookupWidth e with
          | some w => return w
          | none =>
          match ← unfoldDefinition? rE with
          | some rE' => translateW reg (← mkAppM ``Shor.regSize #[← unfoldProj rE'])
          | none => translateWFallback reg e
  | (``Shor.ExtReg.width, #[parentE]) =>
      -- Registered top-level registers (`x`, `z`, `qft`'s `r`, …) already
      -- have their own width registered directly (`.var "xw"`, …), caught
      -- by the registry-lookup fallback below — the two named cases here
      -- intercept a *computed* `ExtReg` (`qft`'s `ws.xExt`/`ws.xExt.grow 1`,
      -- from `PhaseProdWorkspace.xExt`/`ExtReg.grow`/`ExtReg.withReserve`)
      -- one *structural* layer at a time. A blind `unfoldDefinition?` on
      -- the whole `ExtReg.width parentE` only unfolds the outermost head
      -- (`ExtReg.width` itself), never descending into `parentE`, so once
      -- the head becomes a non-unfoldable projection like `List.length` it
      -- gets stuck holding a raw `(⋯).active.qubits.length` with `parentE`
      -- still buried, unreduced, inside — confirmed empirically. Unfolding
      -- *`parentE`* one step at a time instead, re-wrapped in `ExtReg.width`
      -- so this same dispatch gets another look each time, lets each
      -- exposed layer (`ExtReg.withReserve`, `ExtReg.grow`, `leftReg`, …)
      -- be recognised by name as it appears.
      match parentE.getAppFnArgs with
      | (``Shor.ExtReg.grow, #[grandparentE, nE]) =>
          return .add (← translateW reg (← mkAppM ``Shor.ExtReg.width #[grandparentE]))
            (← translateW reg nE)
      | (``Shor.ExtReg.withReserve, #[activeE, _, _]) =>
          translateW reg (← mkAppM ``Shor.regSize #[activeE])
      | _ =>
          match ← reg.lookupWidth e with
          | some w => return w
          | none =>
          match ← unfoldDefinition? parentE with
          | some parentE' => translateW reg (← mkAppM ``Shor.ExtReg.width #[← unfoldProj parentE'])
          | none => translateWFallback reg e
  -- `ExtReg.capacity`'s counterpart, same one-layer-at-a-time discipline:
  -- `(e.grow n).reserve = e.remainingReserve n = e.reserve.drop n`, so
  -- `(e.grow n).capacity = e.capacity - n` (`Registers.lean`'s `grow`).
  | (``Shor.ExtReg.capacity, #[parentE]) =>
      match parentE.getAppFnArgs with
      | (``Shor.ExtReg.grow, #[grandparentE, nE]) =>
          return .sub (← translateW reg (← mkAppM ``Shor.ExtReg.capacity #[grandparentE]))
            (← translateW reg nE)
      | (``Shor.ExtReg.withReserve, #[_, reserveE, _]) =>
          translateW reg (← mkAppM ``Shor.regSize #[reserveE])
      | _ =>
          match ← reg.lookupWidth e with
          | some w => return w
          | none =>
          match ← unfoldDefinition? parentE with
          | some parentE' => translateW reg (← mkAppM ``Shor.ExtReg.capacity #[← unfoldProj parentE'])
          | none => translateWFallback reg e
  | (``ite, #[_, cond, inst, thenE, elseE]) =>
      -- A width formula's own `ite` (e.g. `phaseSplitLogicalWidth`'s
      -- `isTopChunk i` branch) is always fully decidable on its own — `i`,
      -- `k` are concrete at extraction time — even though the *branches*
      -- may mention symbolic registers; decide it and recurse into the
      -- chosen branch, rather than modelling a guard `WExpr` has no
      -- constructor for.
      match ← whnf (← mkAppOptM ``Decidable.decide #[some cond, some inst]) with
      | .const ``Bool.true _ => translateW reg thenE
      | .const ``Bool.false _ => translateW reg elseE
      | d => throwError "translateW: ite condition not decidable to a literal Bool: {cond} ({d})"
  | _ => translateWFallback reg e

/-- The expensive path: everything above is a direct, `O(1)` name check on
`e`'s current head, tried first *precisely* because `reg.lookupWidth`'s
`isDefEq` against every registered slot is not cheap, and — confirmed
empirically, this file's second real performance bug after `Min.min` — a
term like `Shor.nextSignedWidth x z ops`, tried against ten-odd registered
candidates (`pp_body` never had enough of them to notice), turned "not
found" into a real timeout, not just wasted work. Registry lookup, then
`natLit?`, then one `unfoldDefinition?` step and retry, only after every
cheap recogniser above has already had its chance. -/
partial def translateWFallback (reg : Registry) (e : Expr) : MetaM IR.WExpr := do
  match ← reg.lookupWidth e with
  | some w => return w
  | none =>
  match ← natLit? e with
  | some n => return .lit n
  | none =>
  match ← unfoldDefinition? e with
  | some e' => translateW reg (← unfoldProj e')
  | none =>
      -- Last resort, same discipline (and justification) as `translateNode`'s
      -- own final fallback: every genuinely dangerous, D4-opaque-headed shape
      -- (`nextWidth`, `reserveNeed`, `qftWorkspaceNeed`, …) is caught by name
      -- earlier in `translateW`, before ever reaching here — reaching this
      -- point at all means whatever remains is ordinary, ground Nat/`Reg`
      -- arithmetic a stuck non-unfoldable head (a bare structure projection,
      -- e.g. `qft`'s `ws.xReserve` needing `phaseWorkspace` reduced through
      -- an intervening `let`) is blocking, not a cascade risk.
      let e' ← whnf e
      if e' == e then throwError "translateW: unrecognised width expr {e}"
      else translateW reg e'
end

/-- Recognise `b` as (an unfolds-to) `Shor.cramerCoeffFromPtsWidth k m pts
hpts l` for a literal `l`, returning `(l, m)` — `pp_body`'s `phaseCoeff` is
a free-variable *parameter*, but `phase_product`'s own angle
(`planCompiledSignedPhaseGate`'s `coeff := loweringPhaseCoeff k x z pts
hpts`) calls the real interpolation function directly, no parameter to
recognise by `FVarId`. `whnfR`-then-`unfoldDefinition?`, same discipline as
everywhere else: `loweringPhaseCoeff` is an ordinary (non-reducible,
non-recursive) `def` that unfolds in one step to the
`cramerCoeffFromPtsWidth` application this looks for. -/
partial def tryCramerCoeffApp (b : Expr) : MetaM (Option (Nat × Expr)) := do
  let b ← whnfR b
  match b.getAppFnArgs with
  | (``Shor.cramerCoeffFromPtsWidth, #[_, m, _, _, l]) => do
      match ← finValLit? (← mkAppM ``Fin.val #[l]) with
      | some lv => return some (lv, m)
      | none => return none
  | _ =>
      match ← unfoldDefinition? b with
      | some b' => tryCramerCoeffApp b'
      | none => return none

/-- Recognise a `ℚ`-valued `e` that is really just a `ℕ` value cast up,
possibly scaled by a literal factor (`Nat.cast n`, `2 * Nat.cast n`, …) —
`Algorithm 1`'s Step 1/2/5 phase-load angles (R2.6) are built as ordinary
`ℚ` arithmetic on `ℕ`-cast operands (`(2 * ((c + N - 1) % N : ℕ) : ℚ)`),
never through `AExpr`'s `mul`/`coeff`/`qftPhi` vocabulary, so recovering the
underlying `WExpr` this way lets `translateA`'s `HDiv.hDiv` case build an
`AExpr.ratio` (or, for a power-of-two denominator, reuse `qftPhi`) without
walking every possible `ℚ` arithmetic shape as its own `AExpr` case. -/
partial def qNatW (reg : Registry) (e : Expr) : MetaM (Option IR.WExpr) := do
  match e.getAppFnArgs with
  | (``Nat.cast, #[_, _, nE]) => return some (← translateW reg nE)
  | (``HMul.hMul, #[_, _, _, _, a, b]) => do
      -- `a` is `ℚ`-typed here (`2 * (↑X : ℚ)`), so its literal-`n` argument
      -- sits inside `@OfNat.ofNat ℚ n inst`, not as a bare `Nat` `Expr.lit` —
      -- `natLit?`'s `getNatValue?`/`whnfR` chain is built for a `ℕ`-typed
      -- argument and does not recognise this shape (confirmed empirically:
      -- `natLit?` on `(2 : ℚ)` returns `none`), so this reads the `OfNat`
      -- literal argument directly instead.
      match a.getAppFnArgs with
      | (``OfNat.ofNat, #[_, nLitE, _]) =>
          match nLitE.rawNatLit? with
          | some lit =>
              match ← qNatW reg b with
              | some bw => return some (.mul (.lit lit) bw)
              | none => return none
          | none => return none
      | _ => return none
  | _ => return none

partial def translateA (reg : Registry) (e : Expr) : MetaM IR.AExpr := do
  match ← reg.lookupAngle e with
  | some a => return a
  | none =>
  match e.getAppFnArgs with
  | (``Shor.qftPhi, #[mE]) => return .qftPhi (← translateW reg mE)
  | (``HMul.hMul, #[_, _, _, _, a, b]) => do
      -- `phi * phaseCoeff l` / `phi * loweringPhaseCoeff … l` → `AExpr.coeff`;
      -- anything else is a plain product.
      match reg.phaseCoeffFVar, b.getAppArgs with
      | some cfv, #[lE] =>
          if b.getAppFn.isFVarOf cfv then
            match ← finValLit? (← mkAppM ``Fin.val #[lE]) with
            | some l => return .coeff (← translateA reg a) l reg.coeffMExpr
            | none => throwError "translateA: phaseCoeff applied to non-literal index {lE}"
          else
            return .mul (← translateA reg a) (← translateW reg b)
      | _, _ =>
          match ← tryCramerCoeffApp b with
          | some (l, m) => return .coeff (← translateA reg a) l (← translateW reg m)
          | none => return .mul (← translateA reg a) (← translateW reg b)
  | (``Neg.neg, #[_, _, a]) => return .neg (← translateA reg a)
  | (``HDiv.hDiv, #[_, _, _, _, a, b]) => do
      -- R2.6: Algorithm 1's Step 1/2/5 phase-load angles are raw `ℚ`
      -- arithmetic on `ℕ`-cast operands, not calls through `AExpr`'s
      -- existing vocabulary. A power-of-two denominator (Step 2's
      -- `(2 * N) / 2 ^ e`) is `N * qftPhi(e)` (`qftPhi m := 2 / 2 ^ m`);
      -- any other denominator (Step 1/5's `(2 * X) / N`) is a genuine
      -- `AExpr.ratio`. Tried before the plain `div2`/error fallback, which
      -- still handles `CPhase`'s `θ / 2` (its `a` is a real tracked angle,
      -- never a bare `ℕ` cast, so `qNatW` never fires on it).
      let divFallback : MetaM IR.AExpr := do
        match ← qNatW reg a, ← qNatW reg b with
        | some numW, some denomW => return .ratio numW denomW
        | _, _ =>
            match ← natLit? b with
            | some 2 => return .div2 (← translateA reg a)
            | _ => throwError "translateA: unrecognised angle division {e}"
      match b.getAppFnArgs with
      | (``HPow.hPow, #[_, _, _, _, baseE, expE]) =>
          -- `baseE` is `ℚ`-typed (`(2 : ℚ) ^ e`) — same `OfNat`-literal shape
          -- `qNatW`'s `HMul` case handles, `natLit?` doesn't (see its doc
          -- comment there).
          match baseE.getAppFnArgs with
          | (``OfNat.ofNat, #[_, nLitE, _]) =>
              match nLitE.rawNatLit?, ← qNatW reg a with
              | some 2, some (.mul (.lit 2) numW) =>
                  return .mul (.qftPhi (← translateW reg expE)) numW
              | _, _ => divFallback
          | _ => divFallback
      | _ => divFallback
  | _ =>
      match ← unfoldDefinition? e with
      | some e' => translateA reg e'
      | none => throwError "translateA: unrecognised angle expr {e}"

mutual

/-- The `.xReserve`/`.zReserve` (`isX` picks which) resolution shared by
`translateReg`'s own named case and `.xExt`/`.zExt` below. Factored out so
`.xExt`/`.zExt` can call it *directly*, skipping `translateReg`'s top-level
`reg.lookupReg` — routing the freshly-built `wsE.xReserve` query back through
`translateReg`'s public entry forces `reg.lookupReg`'s `isDefEq` to compare it
against every registered (often atomic-`FVar`) candidate, which — for a query
still headed by a plain, non-reducible `def` like `ModMulCircuitWorkspaceOK.
step1Workspace` (as opposed to `QFTWorkspaceOK.phaseWorkspace`, R2.5's only
prior caller, which apparently never triggers this) — forces Lean's *own*
unbounded-transparency reduction machinery to try to unfold straight through
the `ofExtRegs` tactic proof looking for a match, independently of and far
more expensively than `unfoldPhaseWorkspace`'s targeted `.eq_1` shortcut
(confirmed empirically: this alone was the R2.6 `isDefEq` "hang", easily
mistaken for non-termination at 1..4 million heartbeats). -/
partial def resolvePhaseReserve
    (reg : Registry) (isX : Bool) (wsE origWhole : Expr) : MetaM IR.RegExpr := do
  match wsE.getAppFnArgs with
  | (``Shor.CmpLtNWWorkspace.mulWorkspace, #[_, _, workE, scratchE, _, _]) =>
      translateReg reg (← mkAppM ``Shor.ExtReg.reserve #[if isX then workE else scratchE])
  | _ =>
  let rhs ← unfoldPhaseWorkspace wsE
  if rhs == wsE then
    match ← unfoldDefinition? origWhole with
    | some e' => translateReg reg e'
    | none => throwError "translateReg: unrecognised register expr {origWhole}"
  else
    let projName :=
      if isX then ``Shor.Gate.PhaseProdWorkspace.xReserve else ``Shor.Gate.PhaseProdWorkspace.zReserve
    -- `unfoldDefinition?` (a single delta step) only converts the *outer*
    -- `xReserve`/`zReserve` projector into its low-level `.proj` form; since
    -- that `.proj`'s own scrutinee (`rhs`, a fresh literal) is *already* a
    -- constructor, the field access itself iota-reduces immediately too —
    -- but only `whnfR` (full reduction, not a single step) actually carries
    -- that second reduction through, landing on the *field's own* value
    -- (e.g. `dataNoCarry.reserve`, itself possibly another `.proj` layer)
    -- rather than reproducing the exact same `xReserve {rhs}` shape
    -- `unfoldProj` would just rebuild unchanged — confirmed empirically:
    -- that unchanged-rebuild was an infinite `resolvePhaseReserve` loop.
    let e' ← whnfR (← mkAppM projName #[rhs])
    translateReg reg (← unfoldProj e')

partial def translateReg (reg : Registry) (e : Expr) : MetaM IR.RegExpr := do
  match ← reg.lookupReg e with
  | some r => return r
  | none =>
  -- R2.6: normalise a low-level `.proj` node (e.g. `whnfR`/`unfoldDefinition?`
  -- collapsing a chain of structure-field accessors on an `ofExtRegs`-style
  -- literal) back to its named-constant form *first* — `.proj` never matches
  -- any `getAppFnArgs`-keyed case below, so left unnormalised it always falls
  -- straight through to the final generic fallback and errors, even when the
  -- named form underneath is perfectly recognisable.
  let e ← unfoldProj e
  match e.getAppFnArgs with
  | (``Shor.ExtReg.withReserve, #[activeE, reserveE, _]) =>
      return .ext (← translateReg reg activeE) (← translateReg reg reserveE)
  | (``Shor.growExtRegTo, #[parentE, wE]) => do
      -- `growExtRegTo e W := e.grow (W - e.width)`: named directly (D2) —
      -- the grown register's active part is an append of two different
      -- sources, not a slice of anything nameable (`IR/Syntax.lean`'s
      -- `RegExpr.grow` doc comment).
      let parent ← translateReg reg parentE
      let parentWidthE ← mkAppM ``Shor.ExtReg.width #[parentE]
      return .grow parent (.sub (← translateW reg wE) (← translateW reg parentWidthE))
  -- A direct `ExtReg.grow parent n` (e.g. `qft`'s `xExt.grow 1`), `n`
  -- already given rather than computed as `growExtRegTo`'s `W - width`.
  | (``Shor.ExtReg.grow, #[parentE, nE]) =>
      return .grow (← translateReg reg parentE) (← translateW reg nE)
  | (``Shor.Reg.take, #[dropE, widthE]) =>
      match dropE.getAppFnArgs with
      | (``Shor.Reg.drop, #[srcE, loE]) => do
          let lo ← translateW reg loE
          let width ← translateW reg widthE
          let hi := IR.WExpr.add lo width
          match srcE.getAppFnArgs with
          | (``Shor.ExtReg.active, #[parentE]) =>
              return .activeSlice (← translateReg reg parentE) lo hi
          | (``Shor.ExtReg.reserve, #[parentE]) =>
              return .reserveSlice (← translateReg reg parentE) lo hi
          | _ =>
              match ← unfoldDefinition? e with
              | some e' => translateReg reg e'
              | none => throwError "translateReg: unrecognised slice source {srcE}"
      -- A *bare* `Reg.take` (no outer `.drop`, i.e. "from the start" — e.g.
      -- `ExtReg.newBits n := e.reserve.take n`, R2.6's `constArithmeticUnitQubit`).
      | (``Shor.ExtReg.active, #[parentE]) => do
          let hi ← translateW reg widthE
          return .activeSlice (← translateReg reg parentE) (.lit 0) hi
      | (``Shor.ExtReg.reserve, #[parentE]) => do
          let hi ← translateW reg widthE
          return .reserveSlice (← translateReg reg parentE) (.lit 0) hi
      | _ =>
          match ← unfoldDefinition? e with
          | some e' => translateReg reg e'
          | none => throwError "translateReg: unrecognised take source {dropE}"
  -- A *bare* `Reg.drop` (not wrapped in an outer `.take`, e.g. `ofExtRegs`'s
  -- `dataNoCarry := ExtReg.withReserve data.active (data.reserve.drop 1) _`,
  -- R2.6): "drop `lo`, keep everything else" — the slice runs to the
  -- source's own full width, not a separately-given one.
  | (``Shor.Reg.drop, #[srcE, loE]) =>
      match srcE.getAppFnArgs with
      | (``Shor.ExtReg.active, #[parentE]) => do
          let lo ← translateW reg loE
          let hi ← translateW reg (← mkAppM ``Shor.ExtReg.width #[parentE])
          return .activeSlice (← translateReg reg parentE) lo hi
      | (``Shor.ExtReg.reserve, #[parentE]) => do
          let lo ← translateW reg loE
          let hi ← translateW reg (← mkAppM ``Shor.ExtReg.capacity #[parentE])
          return .reserveSlice (← translateReg reg parentE) lo hi
      | _ =>
          match ← unfoldDefinition? e with
          | some e' => translateReg reg e'
          | none => throwError "translateReg: unrecognised drop source {srcE}"
  -- `ExtReg.active` standing alone (not inside the `take (drop …) …` combo
  -- above): the register's *whole* active range, e.g. `qft`'s `r.active`
  -- itself, before `leftReg`/`rightReg` ever slice it further.
  | (``Shor.ExtReg.active, #[parentE]) => do
      let parent ← translateReg reg parentE
      let width ← translateW reg (← mkAppM ``Shor.ExtReg.width #[parentE])
      return .activeSlice parent (.lit 0) width
  -- `qft`'s register split (`Split.lean`): `leftReg r := r.take (regSize r
  -- / 2)`, `rightReg r := r.drop (regSize r / 2)` — named directly rather
  -- than via the `Reg.take`/`Reg.drop` shapes above, since `r` here is
  -- itself a `Reg` (no `ExtReg.active`/`.reserve` wrapper to key off of).
  -- `RegExpr.activeSlice` composes correctly under arbitrary nesting
  -- (`leftReg`/`rightReg` applied to an already-sliced result): each level
  -- slices *relative* to its immediate parent, exactly matching
  -- `Reg.take`/`.drop`'s own relative-indexing semantics.
  | (``Shor.leftReg, #[srcE]) => do
      let src ← translateReg reg srcE
      let srcW ← translateW reg (← mkAppM ``Shor.regSize #[srcE])
      return .activeSlice src (.lit 0) (.div srcW (.lit 2))
  | (``Shor.rightReg, #[srcE]) => do
      let src ← translateReg reg srcE
      let srcW ← translateW reg (← mkAppM ``Shor.regSize #[srcE])
      return .activeSlice src (.div srcW (.lit 2)) srcW
  -- `ws.xReserve`/`.zReserve` as *register* values (e.g. inside
  -- `ExtReg.withReserve x ws.xReserve h`, `ws.xExt`'s own unfolding) —
  -- `resolvePhaseReserve` above has the full rationale (including why
  -- `CmpLtNWWorkspace.mulWorkspace` is special-cased by name).
  | (``Shor.Gate.PhaseProdWorkspace.xReserve, #[_, _, wsE]) => resolvePhaseReserve reg true wsE e
  | (``Shor.Gate.PhaseProdWorkspace.zReserve, #[_, _, wsE]) => resolvePhaseReserve reg false wsE e
  -- `PhaseProdWorkspace.xExt`/`.zExt` (`Gates/Macros.lean`): plain
  -- projections of the already-known operand plus its reserve — calls
  -- `resolvePhaseReserve` *directly* (not `translateReg`'s public entry) for
  -- the same reason `resolvePhaseReserve`'s own doc comment explains.
  | (``Shor.Gate.PhaseProdWorkspace.xExt, #[xE, _, wsE]) =>
      return .ext (← translateReg reg xE)
        (← resolvePhaseReserve reg true wsE (← mkAppM ``Shor.Gate.PhaseProdWorkspace.xReserve #[wsE]))
  | (``Shor.Gate.PhaseProdWorkspace.zExt, #[_, zE, wsE]) =>
      return .ext (← translateReg reg zE)
        (← resolvePhaseReserve reg false wsE (← mkAppM ``Shor.Gate.PhaseProdWorkspace.zReserve #[wsE]))
  -- `(ExtReg.withReserve active reserve _).reserve` (`ofExtRegs`'s `.eq_1`
  -- literal projects straight to its own `reserve` field, e.g.
  -- `dataNoCarry.reserve`): the field *is* `reserve` by construction, no
  -- slicing involved — mirrors `ExtReg.width`'s `.withReserve` case above.
  | (``Shor.ExtReg.reserve, #[parentE]) =>
      match parentE.getAppFnArgs with
      | (``Shor.ExtReg.withReserve, #[_, reserveE, _]) => translateReg reg reserveE
      -- A registered `ExtReg`'s own whole `.reserve` field standing alone
      -- (e.g. `CmpLtNWWorkspace`'s `work`/`scratch`, above) — not sliced
      -- from any other structure, so it is the reserve's full width
      -- (`.capacity`).
      | _ => do
          let cap ← translateW reg (← mkAppM ``Shor.ExtReg.capacity #[parentE])
          return .reserveSlice (← translateReg reg parentE) (.lit 0) cap
  -- `qftXWork ops r := r.reserve.take (qftWorkspaceNeed ops r.width).1`,
  -- `qftZWork ops r := (r.reserve.drop xNeed).take zNeed` (`Lowering/
  -- Workspace.lean`): named directly (D2), like `growExtRegTo` — both the
  -- *offset* and *size* are D4-opaque (`qftWorkspaceNeed`), so there is no
  -- concrete slice bound to decompose into the `Reg.take`/`.drop` shapes
  -- above even in principle.
  | (``Shor.qftXWork, #[_, _, rE]) => do
      let rw ← translateW reg (← mkAppM ``Shor.ExtReg.width #[rE])
      let xWorkW := IR.WExpr.opaque "qftXWork" [rw]
      return .reserveSlice (← translateReg reg rE) (.lit 0) xWorkW
  | (``Shor.qftZWork, #[_, _, rE]) => do
      let rw ← translateW reg (← mkAppM ``Shor.ExtReg.width #[rE])
      let xWorkW := IR.WExpr.opaque "qftXWork" [rw]
      let zWorkW := IR.WExpr.opaque "qftZWork" [rw]
      return .reserveSlice (← translateReg reg rE) xWorkW (.add xWorkW zWorkW)
  | _ =>
      match ← unfoldDefinition? e with
      | some e' => translateReg reg (← unfoldProj e')
      | none => throwError "translateReg: unrecognised register expr {e}"

end

/-- A `dite`/`ite` guard: `Eq`/`LT.lt`/`LE.le` between two `WExpr`s (the only
shapes a concrete-`k` extractor's `n = 0`/`isTopChunk`-style conditions
produce — a matcher-generated guard would need its own case, not yet
needed by any target this file handles). -/
def translateProp (reg : Registry) (e : Expr) : MetaM IR.Prop' := do
  match e.getAppFnArgs with
  | (``Eq, #[_, a, b]) => return .eq (← translateW reg a) (← translateW reg b)
  | (``LT.lt, #[_, _, a, b]) => return .lt (← translateW reg a) (← translateW reg b)
  | (``LE.le, #[_, _, a, b]) => return .le (← translateW reg a) (← translateW reg b)
  | _ => throwError "translateProp: unrecognised guard {e}"

/-- A bare-`ℕ` qubit index (`Gate.H`/`.X`/`.CNOT`/`.Toffoli`'s arguments,
`cmpLtNWSignQubit`'s `flag`, …): per `IR/Instantiate.lean`'s `buildLowGate`
convention (already used for `ctrl`/`Reg.lowQubit`), every qubit-shaped
operand goes through `RegExpr.qubit`, never a raw `WExpr`, regardless of
whether the real value is sliced from a register or is a standalone index.
`Reg.get r i` (`Registers.lean`'s general "physical qubit for logical bit
`i`" accessor — `Reg.lowQubit` is the `i = 0` special case) is the one new
shape here; anything else falls back to `translateReg`, which already
finds a directly-registered free variable (`ctrl`, `flag`, …) via the
registry regardless of its Lean type. -/
partial def translateQubitIndex (reg : Registry) (qE : Expr) : MetaM IR.RegExpr := do
  match qE.getAppFnArgs with
  | (``Shor.Reg.lowQubit, #[rE, _]) => return .qubit (← translateReg reg rE) (.lit 0)
  | (``Shor.Reg.get, #[rE, iE]) =>
      return .qubit (← translateReg reg rE) (← translateW reg (← mkAppM ``Fin.val #[iE]))
  -- `cmpLtNWSignQubit scratch _ := scratch.active.get ⟨regSize scratch.active - 1, _⟩`
  -- (R2.6): named directly (D2) rather than left for `unfoldDefinition?` to
  -- expose — its own internal `Fin` proof is unrelated to (and doesn't use)
  -- the `h` parameter matched away below, but a *symbolic* `scratch` still
  -- leaves `Reg.get`'s underlying `List.get` stuck on a symbolic-length
  -- list, and this qubit index otherwise falls through to `translateReg`
  -- (the wrong category — this is a `ℕ`, not a register) trying to unfold
  -- through it regardless, which never terminates cleanly.
  | (``Shor.cmpLtNWSignQubit, #[scratchE, _]) => do
      let scratchActiveE ← mkAppM ``Shor.ExtReg.active #[scratchE]
      let sw ← translateW reg (← mkAppM ``Shor.regSize #[scratchActiveE])
      return .qubit (← translateReg reg scratchActiveE) (.sub sw (.lit 1))
  | _ =>
      match ← unfoldDefinition? qE with
      | some qE' => translateQubitIndex reg qE'
      | none => translateReg reg qE

/-- Flatten nested `Gate.seq`/drop `Gate.id`, matching `Node.seq`'s
right-fold semantics (`IR/Instantiate.lean`'s `foldGateSeq`) and this
emitter's existing `LowGate.flattenSeq` convention. Only `whnfR`s (never a
full `whnf` — same reasoning as `translateW`'s doc comment): a piece that
is not itself headed by `Gate.seq`/`Gate.id` is handed to `translateNode` as
one leaf unexamined, which will unfold it (by ordinary, non-reducible delta
steps) as needed and — if *that* turns out to itself be a `Gate.seq` (e.g.
`compileSignedAllocations`'s own internal chunk-pair sequencing) — flatten
it again one level down. The result may nest `Node.seq`s that a single
top-level call would have flattened fully, but `IR/Instantiate.lean`'s
`foldGateSeq` doesn't care about nesting depth, only leaf order. -/
partial def flattenGateSeq (e : Expr) : MetaM (List Expr) := do
  let e ← whnfR e
  match e.getAppFnArgs with
  | (``Shor.Gate.seq, #[a, b]) => return (← flattenGateSeq a) ++ (← flattenGateSeq b)
  | (``Shor.Gate.id, #[]) => return []
  | _ => return [e]

/-- `flattenGateSeq`'s `LowGate` counterpart — `phase_product` (R2.2) is
`LowGate`-valued (via `lowerGateRec`), not `Gate`-valued like `pp_body`, so
its `;;`/`id` are a *different* pair of constructors sharing the same
names. -/
partial def flattenLowGateSeq (e : Expr) : MetaM (List Expr) := do
  let e ← whnfR e
  match e.getAppFnArgs with
  | (``Shor.LowGate.seq, #[a, b]) => return (← flattenLowGateSeq a) ++ (← flattenLowGateSeq b)
  | (``Shor.LowGate.id, #[]) => return []
  | _ => return [e]

mutual

/-- Named-construct translation (D2, the same escape hatch `naive_leaf`
uses) of `planCompileAnnotatedOpsToSignedGateAux`'s body. Its `.phaseProduct`
leaf case's dependent match has `st.xslot i`/`st.zslot i` in its *motive*, so
no amount of narrowing a `whnf`/`unfoldDefinition?` attempt avoids forcing
`LayoutState`/`RecursivePhaseWorkspace`/`ReserveBudget` reduction while
type-checking the exposed match (confirmed empirically, repeatedly).
Instead: `annotatedOps`'s own argument list already holds `n` (the running
interpolation-index counter) and the underlying `ops` list *syntactically*
(`annotatePhaseTermsAux k n ops`, never reduced) — both readable with no
reduction at all — so this walks `ops` one `List.cons` at a time (safe: a
specialised extraction's `ops` is built via `Lean.toExpr`, already a literal
constructor tree) and replicates `annotatePhaseTermsAux`+
`planCompileAnnotatedOpsToSignedGateAux`'s combined logic by hand, exactly
mirroring what `lowerGateRec`'s translation does for `PhaseLoweringPlan`'s
other constructors. `st.xslot i`/`st.zslot i` are rebuilt as `Expr`s and
handed to `translateReg`/`translateW`'s existing registry lookup — the same
isDefEq-based technique that already resolves them for the
allocation/deallocation plans and the base case — never reduced directly. -/
partial def translateAnnotatedOps (reg : Registry) (st phi annotatedOpsE : Expr)
    (ctrl : Option Expr) : MetaM IR.Node := do
  let annArgs := annotatedOpsE.getAppArgs
  if annArgs.size != 3 then
    throwError "translateAnnotatedOps: unexpected annotatePhaseTermsAux arity {annotatedOpsE}"
  let some k ← natLit? annArgs[0]!
    | throwError "translateAnnotatedOps: non-literal k {annArgs[0]!}"
  let some n ← finValLit? annArgs[1]!
    | throwError "translateAnnotatedOps: non-literal annotation counter {annArgs[1]!}"
  let qk := Shor.q k
  translateAnnotatedOpsGo reg st phi ctrl qk n (← whnfR annArgs[2]!)

partial def translateAnnotatedOpsGo (reg : Registry) (st phi : Expr) (ctrl : Option Expr)
    (qk n : Nat) (opsE : Expr) : MetaM IR.Node := do
  let xreg (iE : Expr) : MetaM IR.RegExpr := do
    translateReg reg (← mkAppM ``Shor.LayoutState.xslot #[st, iE])
  let zreg (iE : Expr) : MetaM IR.RegExpr := do
    translateReg reg (← mkAppM ``Shor.LayoutState.zslot #[st, iE])
  match opsE.getAppFnArgs with
  | (``List.nil, _) => return .op "id" [] [] none []
  | (``List.cons, #[_, opE, restE]) => do
      let restE ← whnfR restE
      match opE.getAppFnArgs with
      | (``Operations.valid_ops.shiftL, #[_, iE, mE]) => do
          let some m ← natLit? mE
            | throwError "translateAnnotatedOps: non-literal shiftL amount {mE}"
          let tail ← translateAnnotatedOpsGo reg st phi ctrl qk n restE
          return .seq [.op "ShiftL" [← xreg iE] [.lit m] none [],
            .op "ShiftL" [← zreg iE] [.lit m] none [], tail]
      | (``Operations.valid_ops.shiftR, #[_, iE, mE]) => do
          let some m ← natLit? mE
            | throwError "translateAnnotatedOps: non-literal shiftR amount {mE}"
          let tail ← translateAnnotatedOpsGo reg st phi ctrl qk n restE
          return .seq [.op "ShiftR" [← xreg iE] [.lit m] none [],
            .op "ShiftR" [← zreg iE] [.lit m] none [], tail]
      | (``Operations.valid_ops.negate, #[_, iE]) => do
          let tail ← translateAnnotatedOpsGo reg st phi ctrl qk n restE
          return .seq [.op "Negate" [← xreg iE] [] none [], .op "Negate" [← zreg iE] [] none [], tail]
      | (``Operations.valid_ops.addScaled, #[_, dstE, srcE, negSrcE, shE]) => do
          let some sh ← natLit? shE
            | throwError "translateAnnotatedOps: non-literal addScaled shift {shE}"
          let negSrcB ←
            if negSrcE.isConstOf ``Bool.true then pure true
            else if negSrcE.isConstOf ``Bool.false then pure false
            else throwError "translateAnnotatedOps: addScaled negSrc not a literal Bool: {negSrcE}"
          let tail ← translateAnnotatedOpsGo reg st phi ctrl qk n restE
          return .seq [.op "AddScaled" [← xreg dstE, ← xreg srcE] [.lit sh] none [negSrcB],
            .op "AddScaled" [← zreg dstE, ← zreg srcE] [.lit sh] none [negSrcB], tail]
      | (``Operations.valid_ops.phaseProduct, #[_, iE]) => do
          let tail ← translateAnnotatedOpsGo reg st phi ctrl qk (n + 1) restE
          if n < qk then
            let xwE ← mkAppM ``Shor.ExtReg.width #[← mkAppM ``Shor.LayoutState.xslot #[st, iE]]
            let zwE ← mkAppM ``Shor.ExtReg.width #[← mkAppM ``Shor.LayoutState.zslot #[st, iE]]
            let xw ← translateW reg xwE
            let zw ← translateW reg zwE
            -- `x'`/`z'` (`st.xslot i`/`st.zslot i`) are grown to exactly
            -- `nextWidth`, and `canonicalSignedStep`'s whole purpose is
            -- guaranteeing each carries the child level's own reserve —
            -- i.e. `x'.capacity`/`z'.capacity` *are*
            -- `reserveNeed_x`/`reserveNeed_z` at the child's own width
            -- (matching `precomputePhaseProductSlots`'s own
            -- `reserveNeedWExpr`, computed there but not exposed). Built
            -- directly as opaque `WExpr`s, not via `translateW`: unlike
            -- `width`, `ExtReg.capacity` was never registered against these
            -- slots, so a registry miss would fall through to reduction —
            -- exactly the D4-opaque quantity this file never computes.
            let nextWidthW : IR.WExpr := .opaque "nextWidth" [.var "xw", .var "zw"]
            let xCap : IR.WExpr := .opaque "reserveNeed_x" [nextWidthW, nextWidthW]
            let zCap : IR.WExpr := .opaque "reserveNeed_z" [nextWidthW, nextWidthW]
            let phiAExpr ← translateA reg phi
            let callNode : IR.Node ←
              match ctrl with
              | none =>
                  pure <| .call "phase_product" [xw, zw, xCap, zCap]
                    [.coeff phiAExpr n reg.coeffMExpr] [← xreg iE, ← zreg iE]
              | some ctrlE =>
                  pure <| .call "cphase_product" [xw, zw, xCap, zCap]
                    [.coeff phiAExpr n reg.coeffMExpr]
                    [← translateReg reg ctrlE, ← xreg iE, ← zreg iE]
            return .seq [callNode, tail]
          else
            return tail
      | _ => throwError "translateAnnotatedOps: unrecognised op {opE}"
  | _ => throwError "translateAnnotatedOps: unrecognised annotated-ops list {opsE}"

end

mutual

/-- Translate one (already- or not-yet-reduced) `Gate`-valued `Expr` into a
`Node`. Op names are exactly the `Gate` constructor names (D2). Only
`whnfR`s at each step — see `translateW`'s doc comment: a plain `whnf` would
blow straight past `dite`'s own head into a raw `Decidable.rec` case split
(confirmed empirically, the same failure mode `Min.min` hit), destroying the
one thing this function needs to recognise. The fallback for a stuck,
*ordinary* (ergo non-reducible, ergo `whnfR`-invisible) definition head like
`compileOpsToSignedGate`/`allocChunkGate`/`compileSignedAllocationsAux` is
one `unfoldDefinition?` delta step, then retry — exactly `translateW`'s
discipline. Only the constructs `pp_body` (`compileOpsToSignedGate`,
uncontrolled) actually produces are handled; an unrecognised head is a hard
error naming the constant, never a silent drop (D2), including constructs a
*future* target will need (`Gate.CSignedPhaseProd`, `WellFounded.fix`'s
`.eq_def` rewrite, `Nat.casesOn`, …) — those are R2.2+'s job, not stubbed
here. -/
partial def translateNode (reg : Registry) (e : Expr) : MetaM IR.Node := do
  let e ← whnfR e
  match e.getAppFnArgs with
  | (``Shor.Gate.seq, #[a, b]) =>
      return .seq (← (← flattenGateSeq (mkApp2 (mkConst ``Shor.Gate.seq) a b)).mapM (translateNode reg))
  | (``Shor.Gate.id, #[]) => return .op "id" [] [] none []
  | (``Shor.Gate.adj, #[a]) => return .adj (← translateNode reg a)
  | (``dite, #[_, cond, inst, thenFn, elseFn]) => do
      -- Some `dite`s are fully decidable on their own even though the
      -- *branches* are symbolic (`allocChunkGate`'s `isTopChunk i` — `i`,
      -- `k` are concrete at extraction time): decide first, same as
      -- `translateW`'s `ite` case; only a genuinely symbolic condition
      -- becomes `Node.cond` (`allocChunkGate`'s outer `n = 0`, `n` a width
      -- difference against the opaque `nextWidth`).
      match ← whnf (← mkAppOptM ``Decidable.decide #[some cond, some inst]) with
      | .const ``Bool.true _ =>
          translateNode reg (← whnfR (mkApp thenFn (← mkSorry cond false)))
      | .const ``Bool.false _ =>
          let notCond ← mkAppM ``Not #[cond]
          translateNode reg (← whnfR (mkApp elseFn (← mkSorry notCond false)))
      | _ =>
          let guard ← translateProp reg cond
          let thenBody ← whnfR (mkApp thenFn (← mkSorry cond false))
          let notCond ← mkAppM ``Not #[cond]
          let elseBody ← whnfR (mkApp elseFn (← mkSorry notCond false))
          return .cond guard (← translateNode reg thenBody) (← translateNode reg elseBody)
  | (``ite, #[_, cond, inst, thenE, elseE]) => do
      match ← whnf (← mkAppOptM ``Decidable.decide #[some cond, some inst]) with
      | .const ``Bool.true _ => translateNode reg thenE
      | .const ``Bool.false _ => translateNode reg elseE
      | _ =>
          let guard ← translateProp reg cond
          return .cond guard (← translateNode reg thenE) (← translateNode reg elseE)
  | (``Shor.Gate.H, #[q]) => return .op "H" [← translateQubitIndex reg q] [] none []
  | (``Shor.Gate.X, #[q]) => return .op "X" [← translateQubitIndex reg q] [] none []
  | (``Shor.Gate.CNOT, #[c, t]) =>
      return .op "CNOT" [← translateQubitIndex reg c, ← translateQubitIndex reg t] [] none []
  | (``Shor.Gate.Toffoli, #[c1, c2, t]) =>
      return .op "Toffoli"
        [← translateQubitIndex reg c1, ← translateQubitIndex reg c2, ← translateQubitIndex reg t]
        [] none []
  | (``Shor.Gate.QFT, #[r]) => return .op "QFT" [← translateReg reg r] [] none []
  | (``Shor.Gate.RadixReverse, #[r, m]) =>
      return .op "RadixReverse" [← translateReg reg r] [← translateW reg m] none []
  | (``Shor.Gate.CmpGeConst, #[nE, data, scratch, flag]) =>
      return .op "CmpGeConst" [← translateReg reg data, ← translateReg reg scratch,
        ← translateQubitIndex reg flag] [← translateW reg nE] none []
  | (``Shor.Gate.CSubConst, #[nE, data, scratch, flag]) =>
      return .op "CSubConst" [← translateReg reg data, ← translateReg reg scratch,
        ← translateQubitIndex reg flag] [← translateW reg nE] none []
  -- `H_reg r := (regQubits r).foldl (fun acc q => Gate.H q ;; acc) Gate.id`
  -- (R2.6): recursion over a symbolic-length list (`regQubits r = r.qubits`,
  -- `r`'s width symbolic) — the same shape `naive_leaf` (R2.3) hit, same
  -- resolution (D2: name the whole function, state its known loop shape
  -- directly). The `foldl` builds gates in *descending* physical order
  -- (`H (r[w-1]) ;; H (r[w-2]) ;; … ;; H (r[0]) ;; id`, since each new `H q`
  -- is prepended in front of the accumulator) — `w - 1 - i` for an
  -- ascending loop variable `i` reproduces that order exactly.
  | (``Shor.H_reg, #[rE]) => do
      let rw ← translateW reg (← mkAppM ``Shor.regSize #[rE])
      let rReg ← translateReg reg rE
      return .loop "i" (.lit 0) rw
        (.op "H" [.qubit rReg (.sub (.sub rw (.lit 1)) (.var "i"))] [] none [])
  -- `initY1 y := match y.qubits with | [] => id | q :: _ => X q` (R2.6):
  -- named directly rather than reduced — `y.qubits`'s length is symbolic,
  -- so the match can't fire on its own, but "is it empty" is exactly
  -- `regSize y = 0`, and the `X` target is `y`'s own 0th qubit
  -- (`Reg.lowQubit`'s definition) when it isn't.
  | (``Shor.initY1, #[yE]) => do
      let yw ← translateW reg (← mkAppM ``Shor.regSize #[yE])
      let yReg ← translateReg reg yE
      return .cond (.eq yw (.lit 0)) (.op "id" [] [] none [])
        (.op "X" [.qubit yReg (.lit 0)] [] none [])
  -- `modExpApproxValid a N x data work scratch flag hworkspace hstep4 :=
  -- modExpApproxStepsValid ... 0 x.qubits` (R2.6): recursion over a
  -- symbolic-length list, same shape as `H_reg`/`initY1` above. Each step
  -- consumes one qubit of `x` (in ascending order, `e = 0, 1, …`) and runs
  -- `CmodMulInPlaceCore` with the loop-indexed multiplier
  -- `c := (a ^ (2 ^ e)) % N`. Rather than reduce that recursion, this names
  -- the whole function (D2) and re-runs `translateNode`/`translateW` on one
  -- generic step body — with `e` and `c` as fresh free variables registered
  -- directly against `.var "e"`/an `.opaque "modpow"` term — so the *loop
  -- body*'s own translation (five real algorithm steps: `CPhaseProdUsing`,
  -- `PhaseProdUsing`, `CmpGeConst`/`CSubConst`, `cmpLtNW`, adjoints) still
  -- goes through the ordinary `unfoldDefinition?` machinery below, exactly
  -- once, generically in `e`/`c`, instead of once per unrolled iteration. -/
  | (``Shor.modExpApproxValid,
      #[aE, nE, xE, dataE, workE, scratchE, flagE, hworkspaceE, hstep4E]) => do
      let xw ← translateW reg (← mkAppM ``Shor.regSize #[xE])
      withLocalDecl `e .default (mkConst ``Nat) fun eVar => do
      withLocalDecl `c .default (mkConst ``Nat) fun cVar => do
      withLocalDecl `ctrl .default (mkConst ``Nat) fun ctrlVar => do
        let aW ← translateW reg aE
        let nW ← translateW reg nE
        let cW := IR.WExpr.opaque "modpow" [aW, .var "e", nW]
        let ctrlReg := IR.RegExpr.qubit (← translateReg reg xE) (.var "e")
        let reg' := { reg with
          widths := reg.widths ++ #[(eVar, IR.WExpr.var "e"), (cVar, cW)]
          regs := reg.regs ++ #[(ctrlVar, ctrlReg)] }
        let bodyE ← mkAppM ``Shor.CmodMulInPlaceCore
          #[cVar, nE, ctrlVar, dataE, workE, scratchE, flagE, hworkspaceE, hstep4E]
        let bodyNode ← translateNode reg' bodyE
        return .loop "e" (.lit 0) xw bodyNode
  | (``Shor.Gate.ShiftL, #[r, n]) =>
      return .op "ShiftL" [← translateReg reg r] [← translateW reg n] none []
  | (``Shor.Gate.ShiftR, #[r, n]) =>
      return .op "ShiftR" [← translateReg reg r] [← translateW reg n] none []
  | (``Shor.Gate.Negate, #[r]) =>
      return .op "Negate" [← translateReg reg r] [] none []
  | (``Shor.Gate.AddScaled, #[dst, src, negSrc, sh]) => do
      let negSrcB ←
        if negSrc.isConstOf ``Bool.true then pure true
        else if negSrc.isConstOf ``Bool.false then pure false
        else throwError "translateNode: AddScaled negSrc not a literal Bool: {negSrc}"
      return .op "AddScaled" [← translateReg reg dst, ← translateReg reg src]
        [← translateW reg sh] none [negSrcB]
  | (``Shor.Gate.zeroExtend, #[r, n]) =>
      return .op "zeroExtend" [← translateReg reg r] [← translateW reg n] none []
  | (``Shor.Gate.signExtend, #[r, n]) =>
      return .op "signExtend" [← translateReg reg r] [← translateW reg n] none []
  | (``Shor.Gate.zeroDealloc, #[r, n]) =>
      return .op "zeroDealloc" [← translateReg reg r] [← translateW reg n] none []
  | (``Shor.Gate.signDealloc, #[r, n]) =>
      return .op "signDealloc" [← translateReg reg r] [← translateW reg n] none []
  | (``Shor.Gate.SignedPhaseProd, #[phi, x, z]) =>
      return .op "SignedPhaseProd" [← translateReg reg x, ← translateReg reg z]
        [] (some (← translateA reg phi)) []
  | (``Shor.Gate.CSignedPhaseProd, #[ctrl, phi, x, z]) =>
      return .op "CSignedPhaseProd"
        [← translateQubitIndex reg ctrl, ← translateReg reg x, ← translateReg reg z]
        [] (some (← translateA reg phi)) []
  -- `LowGate`'s counterparts (R2.2, `phase_product` — `Gate`/`LowGate` share
  -- op-name vocabulary by D2 but are different inductives).
  | (``Shor.LowGate.seq, #[a, b]) =>
      return .seq
        (← (← flattenLowGateSeq (mkApp2 (mkConst ``Shor.LowGate.seq) a b)).mapM (translateNode reg))
  | (``Shor.LowGate.id, #[]) => return .op "id" [] [] none []
  -- R2.6: `lowerCmpGeConst`/`lowerCSubConst` are the first target whose own
  -- adjoints stay unresolved past `flattenLowGateSeq` (`†diff ;; †prep`, both
  -- multi-gate) — `Shor.Gate.adj`'s counterpart.
  | (``Shor.LowGate.adj, #[a]) => return .adj (← translateNode reg a)
  -- `qft`'s `.singleton` case: `LowGate.H (r.lowQubit h)` — `Reg.lowQubit`
  -- is a raw-`ℕ` projection (the register's own 0th qubit, not sliced from
  -- anywhere else), named directly rather than reduced: it needs `r` to be
  -- concrete to compute, exactly the kind of ground-only reduction this
  -- file avoids forcing.
  | (``Shor.LowGate.H, #[qE]) =>
      match qE.getAppFnArgs with
      | (``Shor.Reg.lowQubit, #[rE, _]) =>
          return .op "H" [.qubit (← translateReg reg rE) (.lit 0)] [] none []
      | _ => throwError "translateNode: unrecognised H qubit expr {qE}"
  -- `LowGate.X`/`.CNOT`/`.Toffoli` (R2.6: `lowerCmpGeConst`/`lowerCSubConst`'s
  -- `lowerPrepareNegConst`/sign-copy steps produce these directly, unlike
  -- every earlier target) — same `translateQubitIndex` treatment as their
  -- `Gate` counterparts, general enough for any qubit-shaped argument
  -- (`constArithmeticUnitQubit`, `cmpLtNWSignQubit`, a registered free `flag`).
  | (``Shor.LowGate.X, #[qE]) => return .op "X" [← translateQubitIndex reg qE] [] none []
  | (``Shor.LowGate.CNOT, #[cE, tE]) =>
      return .op "CNOT" [← translateQubitIndex reg cE, ← translateQubitIndex reg tE] [] none []
  | (``Shor.LowGate.Toffoli, #[c1E, c2E, tE]) =>
      return .op "Toffoli"
        [← translateQubitIndex reg c1E, ← translateQubitIndex reg c2E,
          ← translateQubitIndex reg tE] [] none []
  -- `qft`'s `.split` case's final step: `LowGate.RadixReverse r (splitM
  -- r)`. `r : Reg` here (not `ExtReg`) — `translateReg` already treats a
  -- bare `Reg` value as an `ExtReg` with that `.active`, matching
  -- `buildLowGate`'s own `RadixReverse` case (`r.active`).
  | (``Shor.LowGate.RadixReverse, #[r, m]) =>
      return .op "RadixReverse" [← translateReg reg r] [← translateW reg m] none []
  | (``Shor.LowGate.ShiftL, #[r, n]) =>
      return .op "ShiftL" [← translateReg reg r] [← translateW reg n] none []
  | (``Shor.LowGate.ShiftR, #[r, n]) =>
      return .op "ShiftR" [← translateReg reg r] [← translateW reg n] none []
  | (``Shor.LowGate.Negate, #[r]) =>
      return .op "Negate" [← translateReg reg r] [] none []
  | (``Shor.LowGate.AddScaled, #[dst, src, negSrc, sh]) => do
      let negSrcB ←
        if negSrc.isConstOf ``Bool.true then pure true
        else if negSrc.isConstOf ``Bool.false then pure false
        else throwError "translateNode: AddScaled negSrc not a literal Bool: {negSrc}"
      return .op "AddScaled" [← translateReg reg dst, ← translateReg reg src]
        [← translateW reg sh] none [negSrcB]
  | (``Shor.LowGate.zeroExtend, #[r, n]) =>
      return .op "zeroExtend" [← translateReg reg r] [← translateW reg n] none []
  | (``Shor.LowGate.signExtend, #[r, n]) =>
      return .op "signExtend" [← translateReg reg r] [← translateW reg n] none []
  | (``Shor.LowGate.zeroDealloc, #[r, n]) =>
      return .op "zeroDealloc" [← translateReg reg r] [← translateW reg n] none []
  | (``Shor.LowGate.signDealloc, #[r, n]) =>
      return .op "signDealloc" [← translateReg reg r] [← translateW reg n] none []
  -- The base case of `standardSignedPhaseLoweringPlan`'s recursion
  -- (`lowerGateRec`'s `.signedBase phi x z _ => LowGate.Naive_SignedPhaseProd
  -- phi x z`): a call to the `naive_leaf` template (R2.3), never inlined.
  | (``Shor.LowGate.Naive_SignedPhaseProd, #[phi, x, z]) => do
      let xw ← translateW reg (← mkAppM ``Shor.ExtReg.width #[x])
      let zw ← translateW reg (← mkAppM ``Shor.ExtReg.width #[z])
      return .call "naive_leaf" [xw, zw] [← translateA reg phi]
        [← translateReg reg x, ← translateReg reg z]
  -- `cSignedBase`'s controlled counterpart: a call to `naive_cleaf` (R2.4).
  -- `ctrl : ℕ` here is a bare qubit index (not sliced from any register),
  -- but per `IR/Instantiate.lean`'s `buildLowGate` convention it is still a
  -- register parameter, not a width one — `translateReg` finds it via the
  -- registry (`extractCPhaseProductBody` registers the free `ctrl` variable
  -- against `RegExpr.var "ctrl"` directly; `translateReg` never inspects an
  -- `Expr`'s Lean *type*, only its shape, so a `ℕ`-typed term matching a
  -- registered `RegExpr` is exactly as findable as an `ExtReg`-typed one).
  | (``Shor.LowGate.Naive_CSignedPhaseProd, #[ctrl, phi, x, z]) => do
      let xw ← translateW reg (← mkAppM ``Shor.ExtReg.width #[x])
      let zw ← translateW reg (← mkAppM ``Shor.ExtReg.width #[z])
      return .call "naive_cleaf" [xw, zw] [← translateA reg phi]
        [← translateReg reg ctrl, ← translateReg reg x, ← translateReg reg z]
  -- The step case's self-call: `lowerGateRec (standardSignedPhaseLoweringPlan
  -- k hk theta x' z' ops hchild)`, D3's recursive `Node.call`. This is *only*
  -- ever a nested occurrence — `Targets.lean`'s `extractPhaseProductBody`
  -- unfolds the entry occurrence via `.eq_1` itself, once, before ever
  -- calling `translateNode`; anything found afterwards that still looks
  -- like this is, by construction, always the recursive call, never
  -- something to unfold further. `translatePlan` (below) handles every
  -- other `PhaseLoweringPlan` shape.
  | (``Shor.lowerGateRec, #[_, _, _, _, _, _, _, plan]) => translatePlan reg plan
  -- R2.6's `shor` target: `referenceShorCircuit`'s whole body is
  -- `lowerGate k hk ops (orderFindingApprox …) hLowerWorkspace` — routes to
  -- `translateLowerGate`'s own dedicated structural walk (`lowerGate` needs
  -- `ops`, which nothing else here threads through).
  | (``Shor.lowerGate, #[_, _, opsE, gE, _]) => translateLowerGate reg opsE gE
  -- `lowerCopyConstFromUnit N dst ctrl := lowerCopyBitPowers dst ctrl
  -- N.bitIndices` (R2.6): recursion over a symbolic-length list again (D2),
  -- reformulated as "loop over every bit position of `dst`, guarded on
  -- whether `N` has that bit set" — the two coincide by `Nat.bitIndices`'s
  -- own definition (its values are exactly `{i | N.testBit i}`, sorted
  -- ascending, matching `Node.loop`'s own ascending fold order).
  | (``Shor.lowerCopyConstFromUnit, #[nE, dstE, ctrlE]) => do
      let dstActiveE ← mkAppM ``Shor.ExtReg.active #[dstE]
      let dstW ← translateW reg (← mkAppM ``Shor.ExtReg.width #[dstE])
      let nW ← translateW reg nE
      let ctrlReg ← translateQubitIndex reg ctrlE
      let dstReg ← translateReg reg dstActiveE
      return .loop "i" (.lit 0) dstW
        (.cond (.testBit nW (.var "i"))
          (.op "CNOT" [ctrlReg, .qubit dstReg (.var "i")] [] none [])
          (.op "id" [] [] none []))
  | _ =>
      match ← unfoldDefinition? e with
      | some e' => translateNode reg e'
      | none =>
          -- Last resort: a matcher/`casesOn` application (e.g.
          -- `annotatePhaseTermsAux`'s `phaseTerm?` match) whose *scrutinee*
          -- is ground/decidable (concrete `n`, `k`) even though its branches
          -- are symbolic. `unfoldDefinition?` can't make progress on a
          -- matcher head; a full `whnf` safely can — it only performs the
          -- iota reduction the ground scrutinee licenses and stops at the
          -- next constructor, it does not "lose" anything the way an
          -- unconditional `whnf`-first policy did for `Min.min`/`dite`
          -- earlier, since by this point every recognisable pattern has
          -- already had its chance.
          let e' ← whnf e
          if e' == e then throwError "translateNode: unrecognised construct {e}"
          else translateNode reg e'

/-- Translate a `PhaseLoweringPlan` value directly (D2: named-construct
translation, mirroring `lowerGateRec`'s own match table by hand). This is
needed because `lowerGateRec` isn't `@[reducible]`, so `whnfR` never exposes
its match, while a blind full `whnf` overshoots: it doesn't stop at
`LowGate.Naive_SignedPhaseProd` (itself a plain, further-unfoldable `def`)
the way `translateNode`'s dedicated case needs it to, and instead runs on
into `LowGate.sequence (naiveSignedPhaseGates phi x z)`, a term nothing
recognises. Each recognised shape is instead reconstructed as the exact
`LowGate`/`PhaseLoweringPlan` term `lowerGateRec`'s own equation would
produce and hand back to `translateNode`, so its own (already-correct)
recognisers — not a second reduction — decide what happens next. -/
partial def translatePlan (reg : Registry) (plan : Expr) : MetaM IR.Node := do
  let plan ← whnfR plan
  match plan.getAppFnArgs with
  | (``Shor.standardSignedPhaseLoweringPlan, #[_, _, theta, x, z, _, _]) => do
      let xw ← translateW reg (← mkAppM ``Shor.ExtReg.width #[x])
      let zw ← translateW reg (← mkAppM ``Shor.ExtReg.width #[z])
      let xCap ← translateW reg (← mkAppM ``Shor.ExtReg.capacity #[x])
      let zCap ← translateW reg (← mkAppM ``Shor.ExtReg.capacity #[z])
      return .call "phase_product" [xw, zw, xCap, zCap] [← translateA reg theta]
        [← translateReg reg x, ← translateReg reg z]
  | (``Shor.standardCSignedPhaseLoweringPlan, #[_, _, ctrl, theta, x, z, _, _]) => do
      let xw ← translateW reg (← mkAppM ``Shor.ExtReg.width #[x])
      let zw ← translateW reg (← mkAppM ``Shor.ExtReg.width #[z])
      let xCap ← translateW reg (← mkAppM ``Shor.ExtReg.capacity #[x])
      let zCap ← translateW reg (← mkAppM ``Shor.ExtReg.capacity #[z])
      return .call "cphase_product" [xw, zw, xCap, zCap] [← translateA reg theta]
        [← translateReg reg ctrl, ← translateReg reg x, ← translateReg reg z]
  | (``Shor.PhaseLoweringPlan.id, _) =>
      translateNode reg (← mkAppM ``Shor.LowGate.id #[])
  | (``Shor.PhaseLoweringPlan.seq, #[_, _, _, _, _, _, _, _, left, right]) =>
      return .seq [← translatePlan reg left, ← translatePlan reg right]
  | (``Shor.PhaseLoweringPlan.ShiftL, #[_, _, _, _, _, _, r, n]) =>
      translateNode reg (← mkAppM ``Shor.LowGate.ShiftL #[r, n])
  | (``Shor.PhaseLoweringPlan.ShiftR, #[_, _, _, _, _, _, r, n]) =>
      translateNode reg (← mkAppM ``Shor.LowGate.ShiftR #[r, n])
  | (``Shor.PhaseLoweringPlan.Negate, #[_, _, _, _, _, _, r]) =>
      translateNode reg (← mkAppM ``Shor.LowGate.Negate #[r])
  | (``Shor.PhaseLoweringPlan.AddScaled, #[_, _, _, _, _, _, dst, src, negSrc, shift]) =>
      translateNode reg (← mkAppM ``Shor.LowGate.AddScaled #[dst, src, negSrc, shift])
  | (``Shor.PhaseLoweringPlan.zeroExtend, #[_, _, _, _, _, _, r, n]) =>
      translateNode reg (← mkAppM ``Shor.LowGate.zeroExtend #[r, n])
  | (``Shor.PhaseLoweringPlan.signExtend, #[_, _, _, _, _, _, r, n]) =>
      translateNode reg (← mkAppM ``Shor.LowGate.signExtend #[r, n])
  | (``Shor.PhaseLoweringPlan.zeroDealloc, #[_, _, _, _, _, _, r, n]) =>
      translateNode reg (← mkAppM ``Shor.LowGate.zeroDealloc #[r, n])
  | (``Shor.PhaseLoweringPlan.signDealloc, #[_, _, _, _, _, _, r, n]) =>
      translateNode reg (← mkAppM ``Shor.LowGate.signDealloc #[r, n])
  | (``Shor.PhaseLoweringPlan.signedBase, #[_, _, _, _, _, _, phi, x, z, _]) =>
      translateNode reg (← mkAppM ``Shor.LowGate.Naive_SignedPhaseProd #[phi, x, z])
  | (``Shor.PhaseLoweringPlan.signedStep, #[_, _, _, _, _, _, _, _, _, _, _, _, child]) =>
      translatePlan reg child
  | (``Shor.PhaseLoweringPlan.cSignedBase, #[_, _, _, _, _, _, ctrl, phi, x, z, _]) =>
      translateNode reg (← mkAppM ``Shor.LowGate.Naive_CSignedPhaseProd #[ctrl, phi, x, z])
  | (``Shor.PhaseLoweringPlan.cSignedStep,
      #[_, _, _, _, _, _, _, _, _, _, _, _, _, _, child]) =>
      translatePlan reg child
  | _ =>
      -- Not yet a recognised shape: `plan` is an application of a named
      -- plan-*builder* helper (`planCompiledSignedPhaseGate`,
      -- `planCompileSignedAllocations`, one of its structurally-recursive
      -- `...Aux` helpers, …) rather than a `PhaseLoweringPlan` constructor
      -- itself. Every one of these ultimately produces a value built from
      -- the constructors above, over already-concrete `ops`/`k`/list
      -- arguments (a specialised extraction's whole point) — no symbolic
      -- scrutinee is ever involved, so pushing the definition forward is
      -- safe; only *how* differs by how each is proved:
      -- A `split`-tactic-produced case split (e.g. `planAllocChunkGate`'s
      -- allocated-width comparison against the *symbolic* `xw`/`zw`): decide
      -- first — same discipline as `translateNode`'s own `dite`/`ite` cases
      -- — and only fall back to a genuine `Node.cond` when the guard truly
      -- depends on the still-parametric register widths. Builders compiled
      -- via the `split` tactic sometimes surface as a bare `Decidable.rec`
      -- rather than a named `dite`/`ite` (the matcher-generation path
      -- doesn't always re-materialise the `dite` head), so that shape needs
      -- its own case alongside the other two.
      if plan.isAppOf ``dite then
      match plan.getAppArgs with
      | #[_, cond, inst, thenFn, elseFn] => do
          match ← whnf (← mkAppOptM ``Decidable.decide #[some cond, some inst]) with
          | .const ``Bool.true _ =>
              translatePlan reg (← whnfR (mkApp thenFn (← mkSorry cond false)))
          | .const ``Bool.false _ =>
              let notCond ← mkAppM ``Not #[cond]
              translatePlan reg (← whnfR (mkApp elseFn (← mkSorry notCond false)))
          | _ =>
              let guard ← translateProp reg cond
              let thenNode ← translatePlan reg (← whnfR (mkApp thenFn (← mkSorry cond false)))
              let notCond ← mkAppM ``Not #[cond]
              let elseNode ← translatePlan reg (← whnfR (mkApp elseFn (← mkSorry notCond false)))
              return .cond guard thenNode elseNode
      | _ => throwError "translatePlan: unexpected dite arity {plan}"
      else if plan.isAppOf ``ite then
      match plan.getAppArgs with
      | #[_, cond, inst, thenE, elseE] => do
          match ← whnf (← mkAppOptM ``Decidable.decide #[some cond, some inst]) with
          | .const ``Bool.true _ => translatePlan reg thenE
          | .const ``Bool.false _ => translatePlan reg elseE
          | _ =>
              let guard ← translateProp reg cond
              return .cond guard (← translatePlan reg thenE) (← translatePlan reg elseE)
      | _ => throwError "translatePlan: unexpected ite arity {plan}"
      else if plan.getAppFn.isConstOf ``Decidable.rec then
      match plan.getAppArgs with
      | #[p, _motive, elseBranch, thenBranch, t] => do
          match (← whnf t).getAppFnArgs with
          | (``Decidable.isTrue, #[_, h]) => translatePlan reg (← whnfR (mkApp thenBranch h))
          | (``Decidable.isFalse, #[_, h]) => translatePlan reg (← whnfR (mkApp elseBranch h))
          | _ =>
              let guard ← translateProp reg p
              let notP ← mkAppM ``Not #[p]
              let thenNode ← translatePlan reg (← whnfR (mkApp thenBranch (← mkSorry p false)))
              let elseNode ← translatePlan reg (← whnfR (mkApp elseBranch (← mkSorry notP false)))
              return .cond guard thenNode elseNode
      | _ => throwError "translatePlan: unexpected Decidable.rec arity {plan}"
      else if plan.getAppFn.isConstOf ``Eq.rec || plan.getAppFn.isConstOf ``Eq.ndrec ||
          plan.getAppFn.isConstOf ``Eq.recOn then
      -- A `hsize ▸ childPlan`-style cast (from a builder's `simpa [hsize]
      -- using childPlan`, transporting along a proof that two width
      -- formulas agree): the cast only repackages the *type*, never the
      -- underlying value — `@Eq.rec {α}{a}{motive}(minor)( {b}(h:a=b) :
      -- motive b h`, so the value being transported is always the minor
      -- premise, the *fourth* argument, regardless of `h`'s shape (D7:
      -- trust is the translation table, not any particular proof term).
      match plan.getAppArgs with
      | #[_, _, _, minor, _, _] => translatePlan reg minor
      | _ => throwError "translatePlan: unexpected Eq.rec arity {plan}"
      else
      match plan.getAppFn.constName? with
      | some declName =>
          if declName == ``Shor.planCompiledSignedPhaseGate ||
              declName == ``Shor.planCompiledCSignedPhaseGate ||
              declName == ``Shor.standardPhaseProdUsingPlan then
            -- `:= by ... simpa [...] using completePlan`: like
            -- `standardSignedPhaseLoweringPlan`, a plain delta-unfold would
            -- expose the `simpa` proof's own unreduced cast machinery: the
            -- `.eq_1` equation lemma instead gives the already-normalised
            -- RHS directly (the same technique `extractPhaseProductBody`
            -- uses for `standardSignedPhaseLoweringPlan.eq_1`).
            let some eqns ← Lean.Meta.getEqnsFor? declName
              | throwError "translatePlan: no equation lemma for {plan}"
            let some eqnName := eqns[0]?
              | throwError "translatePlan: no equation lemma for {plan}"
            let eqApp := mkAppN (mkConst eqnName) plan.getAppArgs
            let rhs := (← inferType eqApp).getAppArgs[2]!
            translatePlan reg rhs
          else if declName == ``Shor.planCompileAnnotatedOpsToSignedGateAux then
            -- The `.phaseProduct` leaf case's dependent match has `st.xslot
            -- i`/`st.zslot i` in its *motive* (the `Gate.SignedPhaseProd`
            -- index type), so *any* attempt to exposed it via `whnf` —
            -- however narrowly the reduction is scoped — forces Lean to
            -- type-check the result against that motive, cascading through
            -- `LayoutState`/`RecursivePhaseWorkspace`/`ReserveBudget`
            -- exactly like the `Min`/`Max`/`nextWidth` cases this file
            -- already avoids (confirmed empirically, repeatedly). The named-
            -- construct escape hatch (D2, `naive_leaf`'s technique) is the
            -- only way through: walk the *already syntactically concrete*
            -- `ops` list embedded in `annotatedOps`'s own argument list by
            -- hand — see `translateAnnotatedOps`.
            let args := plan.getAppArgs
            translateAnnotatedOps reg args[8]! args[6]! args.back! none
          else if declName == ``Shor.planCompileAnnotatedOpsToCSignedGateAux then
            -- Controlled counterpart of the case above, same reasoning:
            -- `st`/`phi`/`ctrl` come from the arg list unreduced, `ctrl`
            -- threaded through so `.phaseProduct` leaves call
            -- `cphase_product` instead of `phase_product`.
            let args := plan.getAppArgs
            translateAnnotatedOps reg args[9]! args[7]! args.back! (some args[6]!)
          else
            -- `planCompileSignedAllocations`/`planCompileSignedDeallocations`
            -- (`:= by unfold X; exact Y`, no casting at all) and their
            -- structurally-recursive `...Aux` helpers (direct pattern match
            -- on the concrete `n`/list): ordinary delta+iota unfolding is
            -- always safe here, so keep pushing one step at a time.
            match ← unfoldDefinition? plan with
            | some plan' => translatePlan reg plan'
            | none => translatePlanWhnfFallback reg plan
      | none => translatePlanWhnfFallback reg plan

/-- Last resort for `translatePlan`. Reaching here means a shape the
translation table hasn't accounted for yet — every genuine cascade risk
this file has hit (`planCompileAnnotatedOpsToSignedGateAux`'s dependent
`.phaseProduct` match, chief among them) now has its own named-construct
case above instead of a generic reduction attempt, so a blind `whnf` here
would only be guessing. A hard, immediate error naming the constant (D2),
never a silent hang. -/
partial def translatePlanWhnfFallback (_reg : Registry) (plan : Expr) : MetaM IR.Node :=
  throwError "translatePlan: unsupported PhaseLoweringPlan constructor {plan}"

/-- `QFTLoweringPlan`'s named-construct translation (R2.5), mirroring
`lowerQFTPlan`'s own 3-arm match by hand exactly as `translatePlan` mirrors
`lowerGateRec`'s — a *different* plan type (indexed by `Reg`, not `ExtReg`
`x`/`z`), so its own function, not a `PhaseLoweringPlan` case. The `.split`
arm's `phasePlan : StandardPhaseLoweringPlan …` is `phase_product`'s own
plan type — `lowerGateRec phasePlan` routes it through the *existing*
`translateNode`/`translatePlan` machinery (which now also recognises
`standardPhaseProdUsingPlan` by name for its own `.eq_1`), not duplicated
here. -/
partial def translateQFTPlan (reg : Registry) (plan : Expr) : MetaM IR.Node := do
  let plan ← whnfR plan
  match plan.getAppFnArgs with
  | (``Shor.standardQFTLoweringPlan, #[_, _, _, r, xWork, zWork, _]) => do
      let w ← translateW reg (← mkAppM ``Shor.regSize #[r])
      let xWorkW ← translateW reg (← mkAppM ``Shor.regSize #[xWork])
      let zWorkW ← translateW reg (← mkAppM ``Shor.regSize #[zWork])
      return .call "qft" [w, xWorkW, zWorkW] []
        [← translateReg reg r, ← translateReg reg xWork, ← translateReg reg zWork]
  | (``Shor.QFTLoweringPlan.empty, _) =>
      translateNode reg (← mkAppM ``Shor.LowGate.id #[])
  | (``Shor.QFTLoweringPlan.singleton, #[_, _, _, r, _]) => do
      let hproof ← mkSorry (← mkAppM ``LT.lt #[mkNatLit 0, ← mkAppM ``Shor.regSize #[r]]) false
      translateNode reg (← mkAppM ``Shor.LowGate.H #[← mkAppM ``Shor.Reg.lowQubit #[r, hproof]])
  | (``Shor.QFTLoweringPlan.split,
      #[_, _, _, r, _, _ws, _phaseInitSize, phasePlan, rightPlan, leftPlan]) => do
      let rightNode ← translateQFTPlan reg rightPlan
      let phaseNode ← translateNode reg (← mkAppM ``Shor.lowerGateRec #[phasePlan])
      let leftNode ← translateQFTPlan reg leftPlan
      let radixNode ← translateNode reg
        (← mkAppM ``Shor.LowGate.RadixReverse #[r, ← mkAppM ``Shor.splitM #[r]])
      return .seq [rightNode, phaseNode, leftNode, radixNode]
  | _ =>
      match ← unfoldDefinition? plan with
      | some plan' => translateQFTPlan reg plan'
      | none => throwError "translateQFTPlan: unsupported QFTLoweringPlan constructor {plan}"

/-- R2.6's `shor` target: `Shor.lowerGate`'s own structural walk over a
`Gate`, mirroring its match table by hand (same D2 discipline as
`translatePlan`/`translateQFTPlan` above — `lowerGate` isn't `@[reducible]`,
so `whnfR` never exposes it). `opsE` is `lowerGate`'s own `ops` argument,
needed only to rebuild `Gate.QFT`'s `qftXWork`/`qftZWork` calls; the
workspace proof argument `lowerGate` itself takes is never threaded through
at all — `GateWorkspaceOK` is a `Prop`, and every case below reads its
registers/widths straight off `G`'s own constructor arguments, never off the
workspace (confirmed by inspection of `lowerGate`, `lowerQFT`,
`lowerSignedPhaseProdWithWorkspace`, … themselves: the workspace argument only
ever supplies further proof obligations passed on downward, never a register
or width value). -/
partial def translateLowerGate (reg : Registry) (opsE : Expr) (gE : Expr) : MetaM IR.Node := do
  let gE ← whnfR gE
  match gE.getAppFnArgs with
  | (``Shor.Gate.id, #[]) => return .op "id" [] [] none []
  | (``Shor.Gate.seq, #[a, b]) =>
      return .seq [← translateLowerGate reg opsE a, ← translateLowerGate reg opsE b]
  | (``Shor.Gate.adj, #[a]) => return .adj (← translateLowerGate reg opsE a)
  | (``Shor.Gate.H, #[q]) => return .op "H" [← translateQubitIndex reg q] [] none []
  | (``Shor.Gate.X, #[q]) => return .op "X" [← translateQubitIndex reg q] [] none []
  | (``Shor.Gate.CNOT, #[c, t]) =>
      return .op "CNOT" [← translateQubitIndex reg c, ← translateQubitIndex reg t] [] none []
  | (``Shor.Gate.Toffoli, #[c1, c2, t]) =>
      return .op "Toffoli"
        [← translateQubitIndex reg c1, ← translateQubitIndex reg c2, ← translateQubitIndex reg t]
        [] none []
  | (``Shor.Gate.ShiftL, #[r, n]) =>
      return .op "ShiftL" [← translateReg reg r] [← translateW reg n] none []
  | (``Shor.Gate.ShiftR, #[r, n]) =>
      return .op "ShiftR" [← translateReg reg r] [← translateW reg n] none []
  | (``Shor.Gate.Negate, #[r]) => return .op "Negate" [← translateReg reg r] [] none []
  | (``Shor.Gate.AddScaled, #[dst, src, negSrc, sh]) => do
      let negSrcB ←
        if negSrc.isConstOf ``Bool.true then pure true
        else if negSrc.isConstOf ``Bool.false then pure false
        else throwError "translateLowerGate: AddScaled negSrc not a literal Bool: {negSrc}"
      return .op "AddScaled" [← translateReg reg dst, ← translateReg reg src]
        [← translateW reg sh] none [negSrcB]
  | (``Shor.Gate.zeroExtend, #[r, n]) =>
      return .op "zeroExtend" [← translateReg reg r] [← translateW reg n] none []
  | (``Shor.Gate.signExtend, #[r, n]) =>
      return .op "signExtend" [← translateReg reg r] [← translateW reg n] none []
  | (``Shor.Gate.zeroDealloc, #[r, n]) =>
      return .op "zeroDealloc" [← translateReg reg r] [← translateW reg n] none []
  | (``Shor.Gate.signDealloc, #[r, n]) =>
      return .op "signDealloc" [← translateReg reg r] [← translateW reg n] none []
  | (``Shor.Gate.RadixReverse, #[r, m]) =>
      return .op "RadixReverse" [← translateReg reg r] [← translateW reg m] none []
  -- `lowerQFT k hk ops r hw := lowerQFTPlan (standardQFTLoweringPlan k hk ops
  -- r.active (qftXWork ops r) (qftZWork ops r) hw.explicitWorkspace)` —
  -- exactly `translateQFTPlan`'s own `standardQFTLoweringPlan` case, applied
  -- to `r.active`/`qftXWork ops r`/`qftZWork ops r` instead of free
  -- variables, so this reconstructs that same call rather than duplicating
  -- its body.
  | (``Shor.Gate.QFT, #[r]) => do
      let rActiveE ← mkAppM ``Shor.ExtReg.active #[r]
      let xWorkE ← mkAppM ``Shor.qftXWork #[opsE, r]
      let zWorkE ← mkAppM ``Shor.qftZWork #[opsE, r]
      let w ← translateW reg (← mkAppM ``Shor.regSize #[rActiveE])
      let xWorkW ← translateW reg (← mkAppM ``Shor.regSize #[xWorkE])
      let zWorkW ← translateW reg (← mkAppM ``Shor.regSize #[zWorkE])
      return .call "qft" [w, xWorkW, zWorkW] []
        [← translateReg reg rActiveE, ← translateReg reg xWorkE, ← translateReg reg zWorkE]
  -- `lowerSignedPhaseProdWithWorkspace k hk phi x z ops hw := lowerSignedPhaseProd
  -- k hk phi x z ops (standardSignedPhaseLoweringPlan k hk phi x z ops hw)` —
  -- exactly `translatePlan`'s own `standardSignedPhaseLoweringPlan` case.
  | (``Shor.Gate.SignedPhaseProd, #[phi, x, z]) => do
      let xw ← translateW reg (← mkAppM ``Shor.ExtReg.width #[x])
      let zw ← translateW reg (← mkAppM ``Shor.ExtReg.width #[z])
      let xCap ← translateW reg (← mkAppM ``Shor.ExtReg.capacity #[x])
      let zCap ← translateW reg (← mkAppM ``Shor.ExtReg.capacity #[z])
      return .call "phase_product" [xw, zw, xCap, zCap] [← translateA reg phi]
        [← translateReg reg x, ← translateReg reg z]
  | (``Shor.Gate.CSignedPhaseProd, #[ctrl, phi, x, z]) => do
      let xw ← translateW reg (← mkAppM ``Shor.ExtReg.width #[x])
      let zw ← translateW reg (← mkAppM ``Shor.ExtReg.width #[z])
      let xCap ← translateW reg (← mkAppM ``Shor.ExtReg.capacity #[x])
      let zCap ← translateW reg (← mkAppM ``Shor.ExtReg.capacity #[z])
      return .call "cphase_product" [xw, zw, xCap, zCap] [← translateA reg phi]
        [← translateQubitIndex reg ctrl, ← translateReg reg x, ← translateReg reg z]
  -- `lowerCmpGeConst`/`lowerCSubConst` are plain (non-tactic-mode) `def`s —
  -- unlike every case above, `lowerGate`'s own match doesn't need
  -- reconstructing here at all, `translateNode`'s ordinary `unfoldDefinition?`
  -- fallback already unfolds them into `Gate`-vocabulary primitives directly
  -- (`zeroExtend`/`AddScaled`/`CNOT`/`X`/`Negate`/adjoints), the one exception
  -- being `lowerCopyConstFromUnit`'s per-bit constant write, which
  -- `translateNode` recognises by name (below) the same way `H_reg`/
  -- `modExpApproxValid` are.
  | (``Shor.Gate.CmpGeConst, #[nE, data, scratch, flag]) => do
      let hE ← mkSorry (← mkAppM ``Shor.ConstArithmeticWorkspace #[nE, data, scratch, flag]) false
      translateNode reg (← mkAppM ``Shor.lowerCmpGeConst #[nE, data, scratch, flag, hE])
  | (``Shor.Gate.CSubConst, #[nE, data, scratch, flag]) => do
      let hE ← mkSorry (← mkAppM ``Shor.ConstArithmeticWorkspace #[nE, data, scratch, flag]) false
      translateNode reg (← mkAppM ``Shor.lowerCSubConst #[nE, data, scratch, flag, hE])
  -- `H_reg`/`initY1` need no lowering (already `H`/`X`, primitives in both
  -- `Gate` and `LowGate`) — same shapes as `translateNode`'s own cases.
  | (``Shor.H_reg, #[rE]) => do
      let rw ← translateW reg (← mkAppM ``Shor.regSize #[rE])
      let rReg ← translateReg reg rE
      return .loop "i" (.lit 0) rw
        (.op "H" [.qubit rReg (.sub (.sub rw (.lit 1)) (.var "i"))] [] none [])
  | (``Shor.initY1, #[yE]) => do
      let yw ← translateW reg (← mkAppM ``Shor.regSize #[yE])
      let yReg ← translateReg reg yE
      return .cond (.eq yw (.lit 0)) (.op "id" [] [] none [])
        (.op "X" [.qubit yReg (.lit 0)] [] none [])
  -- `modExpApproxValid`'s loop body (`CmodMulInPlaceCore`) *does* contain
  -- `Gate.QFT`/`.SignedPhaseProd`/`.CSignedPhaseProd` needing lowering — the
  -- one case here that must recurse via `translateLowerGate`, not
  -- `translateNode`, or the calls inside it would wrongly stay Gate-level
  -- `.op` nodes instead of `.call "qft"/"phase_product"/"cphase_product"`.
  | (``Shor.modExpApproxValid,
      #[aE, nE, xE, dataE, workE, scratchE, flagE, hworkspaceE, hstep4E]) => do
      let xw ← translateW reg (← mkAppM ``Shor.regSize #[xE])
      withLocalDecl `e .default (mkConst ``Nat) fun eVar => do
      withLocalDecl `c .default (mkConst ``Nat) fun cVar => do
      withLocalDecl `ctrl .default (mkConst ``Nat) fun ctrlVar => do
        let aW ← translateW reg aE
        let nW ← translateW reg nE
        let cW := IR.WExpr.opaque "modpow" [aW, .var "e", nW]
        let ctrlReg := IR.RegExpr.qubit (← translateReg reg xE) (.var "e")
        let reg' := { reg with
          widths := reg.widths ++ #[(eVar, IR.WExpr.var "e"), (cVar, cW)]
          regs := reg.regs ++ #[(ctrlVar, ctrlReg)] }
        let bodyE ← mkAppM ``Shor.CmodMulInPlaceCore
          #[cVar, nE, ctrlVar, dataE, workE, scratchE, flagE, hworkspaceE, hstep4E]
        let bodyNode ← translateLowerGate reg' opsE bodyE
        return .loop "e" (.lit 0) xw bodyNode
  | _ =>
      match ← unfoldDefinition? gE with
      | some gE' => translateLowerGate reg opsE gE'
      | none => throwError "translateLowerGate: unrecognised Gate constructor {gE}"

end

end Shor.Reflect
