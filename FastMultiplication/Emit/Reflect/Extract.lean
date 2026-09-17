import Lean
import FastMultiplication.Emit.IR.Syntax
import FastMultiplication.Emit.Reflect.Quote
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Compile

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

/-- Read a natural-number literal off a (already `whnf`'d) `Expr`, if it is
one. -/
def natLit? (e : Expr) : MetaM (Option Nat) := do
  match ← whnf e with
  | .lit (.natVal n) => return some n
  | e => return e.rawNatLit?

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
  match ← reg.lookupWidth e with
  | some w => return w
  | none =>
  match ← natLit? e with
  | some n => return .lit n
  | none =>
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => return .add (← translateW reg a) (← translateW reg b)
  | (``HSub.hSub, #[_, _, _, _, a, b]) => return .sub (← translateW reg a) (← translateW reg b)
  | (``HMul.hMul, #[_, _, _, _, a, b]) => return .mul (← translateW reg a) (← translateW reg b)
  | (``HDiv.hDiv, #[_, _, _, _, a, b]) => return .div (← translateW reg a) (← translateW reg b)
  | (``Max.max, #[_, _, a, b]) => return .max (← translateW reg a) (← translateW reg b)
  | (``Min.min, #[_, _, a, b]) => return .min (← translateW reg a) (← translateW reg b)
  | (``Shor.commonNeededWidth, _) =>
      -- D4: opaque outright, by constant name — never inspect the argument
      -- (which genuinely depends on the table; PLAN.md §5.5 Finding 2).
      return .opaque "nextWidth" reg.nextWidthArgs
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
  | _ =>
      match ← unfoldDefinition? e with
      | some e' => translateW reg e'
      | none => throwError "translateW: unrecognised width expr {e}"

partial def translateA (reg : Registry) (e : Expr) : MetaM IR.AExpr := do
  match ← reg.lookupAngle e with
  | some a => return a
  | none =>
  match e.getAppFnArgs with
  | (``HMul.hMul, #[_, _, _, _, a, b]) =>
      -- `phi * phaseCoeff l` → `AExpr.coeff`; anything else is a plain product.
      match reg.phaseCoeffFVar, b.getAppArgs with
      | some cfv, #[lE] =>
          if b.getAppFn.isFVarOf cfv then
            match ← natLit? (← mkAppM ``Fin.val #[lE]) with
            | some l => return .coeff (← translateA reg a) l reg.coeffMExpr
            | none => throwError "translateA: phaseCoeff applied to non-literal index {lE}"
          else
            return .mul (← translateA reg a) (← translateW reg b)
      | _, _ => return .mul (← translateA reg a) (← translateW reg b)
  | (``Neg.neg, #[_, _, a]) => return .neg (← translateA reg a)
  | (``HDiv.hDiv, #[_, _, _, _, a, b]) =>
      match ← natLit? b with
      | some 2 => return .div2 (← translateA reg a)
      | _ => throwError "translateA: unrecognised angle division {e}"
  | _ =>
      match ← unfoldDefinition? e with
      | some e' => translateA reg e'
      | none => throwError "translateA: unrecognised angle expr {e}"

partial def translateReg (reg : Registry) (e : Expr) : MetaM IR.RegExpr := do
  match ← reg.lookupReg e with
  | some r => return r
  | none =>
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
      | _ =>
          match ← unfoldDefinition? e with
          | some e' => translateReg reg e'
          | none => throwError "translateReg: unrecognised take source {dropE}"
  | _ =>
      match ← unfoldDefinition? e with
      | some e' => translateReg reg e'
      | none => throwError "translateReg: unrecognised register expr {e}"

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

end Shor.Reflect
