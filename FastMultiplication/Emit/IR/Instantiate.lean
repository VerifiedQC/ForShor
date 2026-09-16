import FastMultiplication.Emit.IR.Syntax
import FastMultiplication.Emit.Lower.Decide
import FastMultiplication.ShorVerification.Framework.AbstractMachine.Gates
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Gates.NaiveLeaf

/-!
# The extracted symbolic IR: instantiation

The interpreter D3 relies on: a recursive template is one activation plus a
`Node.call` to itself, and *this* file is what unrolls that call at a
concrete width. It is also D7's safety net — the only thing checked against
the extracted IR is that `instantiate`, run here with `Env` built from the
real opaque functions (`RecursivePhaseWorkspace.nextWidth`,
`cramerCoeffFromPtsWidth`, …), agrees with the real compiled term; this file
can only agree with the real term at every checked width if the extracted
structure is actually right.

`instantiate` targets `LowGate` (the flat compiled circuits: `pp`, `cpp`,
`qft`); `instantiateGate` targets `Gate` (the high-level tree
`orderFindingApprox`/`shor` is stated over, for R2.6). Both share the same
`WExpr`/`AExpr`/`RegExpr`/`Prop'` evaluator and the same `Doc`/`call`/`loop`
machinery; only the leaf `op` dispatcher differs, since the two gate
languages are different (though overlapping) sets of constructors.
-/

namespace Shor

/-- An `ExtReg` built by `IR.RegExpr.qubit` (`IR.evalReg`'s last case) is a
single-qubit active register; this recovers the bare index for the
`LowGate`/`Gate` constructors that take one (`H`, `X`, `CNOT`, …). -/
def ExtReg.singleQubit? (e : ExtReg) : Option ℕ :=
  match e.active.qubits with
  | [q] => some q
  | _ => none

namespace IR

/-- The oracle side of instantiation: everything the extracted `Doc` cannot
compute for itself because D4 keeps it opaque, or that a caller supplies as
the concrete instance data (the initial width/angle/register parameters of
the `entry` template). `opaqueW`/`coeff` are meant to be instantiated with
the real functions (`RecursivePhaseWorkspace.nextWidth ops`,
`RecursivePhaseWorkspace.reserveNeed ops`, `qftWorkspaceNeed ops`,
`Nat.log2`, `Nat.clog 2`, `cramerCoeffFromPtsWidth k m pts hpts`) at the call
sites that check `instantiate` against a real term. -/
structure Env where
  w : String → Option ℕ
  a : String → Option Angle
  r : String → Option ExtReg
  opaqueW : String → List ℕ → Option ℕ
  coeff : ℕ → ℕ → Option ℚ

/-- Bind one width variable, shadowing any previous binding of the same
name (`loop`'s induction variable). -/
def Env.bindW (env : Env) (name : String) (v : ℕ) : Env :=
  { env with w := fun n => if n == name then some v else env.w n }

/-- The environment a `call` executes its callee's body in: fresh
`w`/`a`/`r` maps built purely from the callee template's own parameter
lists and the evaluated argument lists (a template's body only ever
references its own parameters, never its caller's), with the oracle
(`opaqueW`/`coeff`) carried over unchanged. -/
def Env.call (env : Env) (wParams : List String) (wVals : List ℕ) (aParams : List String)
    (aVals : List Angle) (rParams : List String) (rVals : List ExtReg) : Env :=
  { env with
    w := fun n => (wParams.zip wVals).lookup n
    a := fun n => (aParams.zip aVals).lookup n
    r := fun n => (rParams.zip rVals).lookup n }

/-- Evaluate a `WExpr` against `env`, threading opaque-function lookups
through `Except`. `partial`: nested recursion through `List WExpr`
(`opaque`'s arguments), as in `IR/WellFormed.lean`. -/
partial def evalW (env : Env) : WExpr → Except String ℕ
  | .var name =>
      match env.w name with
      | some v => .ok v
      | none => .error s!"instantiate: unbound width var {name}"
  | .lit n => .ok n
  | .add a b => return (← evalW env a) + (← evalW env b)
  | .sub a b => return (← evalW env a) - (← evalW env b)
  | .mul a b => return (← evalW env a) * (← evalW env b)
  | .div a b => return (← evalW env a) / (← evalW env b)
  | .max a b => return Nat.max (← evalW env a) (← evalW env b)
  | .opaque fn args => do
      let vs ← args.mapM (evalW env)
      match env.opaqueW fn vs with
      | some v => .ok v
      | none => .error s!"instantiate: opaque {fn} undefined at {vs}"

/-- Evaluate an `AExpr`. -/
partial def evalA (env : Env) : AExpr → Except String Angle
  | .var name =>
      match env.a name with
      | some v => .ok v
      | none => .error s!"instantiate: unbound angle var {name}"
  | .lit a => .ok a
  | .mul a w => return (← evalA env a) * ((← evalW env w : ℕ) : ℚ)
  | .coeff phi l m => do
      let mv ← evalW env m
      match env.coeff l mv with
      | some c => return (← evalA env phi) * c
      | none => .error s!"instantiate: coeff undefined at l={l} m={mv}"
  | .div2 a => return (← evalA env a) / 2
  | .neg a => return (-(← evalA env a))

/-- Evaluate a `Prop'` guard. -/
def evalProp (env : Env) : Prop' → Except String Bool
  | .lt a b => return decide ((← evalW env a) < (← evalW env b))
  | .le a b => return decide ((← evalW env a) ≤ (← evalW env b))
  | .eq a b => return decide ((← evalW env a) = (← evalW env b))

/-- Evaluate a `RegExpr` to an `ExtReg`. A bare `Reg` (`RadixReverse`'s
argument) is that `ExtReg`'s `active` part, matching `ExtReg.ofReg`'s
treatment of an ordinary register as an extendable one with empty reserve.
`ext`'s `Disjoint` side condition is decided against the concrete evaluated
registers (`Emit/Lower/Decide.lean`'s `decidableRegDisjoint`) and refused,
never assumed, if it fails — matching this file's other `if h : …` register
constructions. `partial`: no nested `List RegExpr` occurs, but this mutually
threads through `evalW`, which is. -/
partial def evalReg (env : Env) : RegExpr → Except String ExtReg
  | .var name =>
      match env.r name with
      | some v => .ok v
      | none => .error s!"instantiate: unbound register var {name}"
  | .activeSlice r lo hi => do
      let rv ← evalReg env r
      let loV ← evalW env lo
      let hiV ← evalW env hi
      pure (ExtReg.ofReg ((rv.active.drop loV).take (hiV - loV)))
  | .reserveSlice r lo hi => do
      let rv ← evalReg env r
      let loV ← evalW env lo
      let hiV ← evalW env hi
      pure (ExtReg.ofReg ((rv.reserve.drop loV).take (hiV - loV)))
  | .ext active reserve => do
      let a ← evalReg env active
      let b ← evalReg env reserve
      if h : Disjoint a.active b.active then
        pure (ExtReg.withReserve a.active b.active h)
      else
        .error "instantiate: ext active/reserve not disjoint"
  | .qubit r i => do
      let rv ← evalReg env r
      let iv ← evalW env i
      if h : iv < rv.active.width then
        pure (ExtReg.ofReg (Reg.singleton (rv.active.get ⟨iv, h⟩)))
      else
        .error s!"instantiate: qubit index {iv} out of range"

/-- Build one `LowGate` leaf from an `op` node's already-evaluated
arguments. Op names are exactly the `LowGate` constructor names (D2); regs
land in declaration order, nats in declaration order, dropped into whichever
of the two lists they belong to. -/
def buildLowGate (name : String) (regs : List ExtReg) (nats : List ℕ) (angle : Option Angle)
    (flags : List Bool) : Except String LowGate :=
  let qb (r : ExtReg) : Except String ℕ :=
    match r.singleQubit? with
    | some q => .ok q
    | none => .error s!"instantiate: {name} expected a single-qubit register"
  match name, regs, nats, angle, flags with
  | "id", [], [], none, [] => .ok .id
  | "H", [r], [], none, [] => return .H (← qb r)
  | "X", [r], [], none, [] => return .X (← qb r)
  | "Phase", [r], [], some a, [] => return .Phase (← qb r) a
  | "CNOT", [c, t], [], none, [] => return .CNOT (← qb c) (← qb t)
  | "Toffoli", [c1, c2, t], [], none, [] => return .Toffoli (← qb c1) (← qb c2) (← qb t)
  | "ShiftL", [r], [n], none, [] => .ok (.ShiftL r n)
  | "ShiftR", [r], [n], none, [] => .ok (.ShiftR r n)
  | "Negate", [r], [], none, [] => .ok (.Negate r)
  | "AddScaled", [dst, src], [shift], none, [negSrc] => .ok (.AddScaled dst src negSrc shift)
  | "zeroExtend", [r], [n], none, [] => .ok (.zeroExtend r n)
  | "signExtend", [r], [n], none, [] => .ok (.signExtend r n)
  | "zeroDealloc", [r], [n], none, [] => .ok (.zeroDealloc r n)
  | "signDealloc", [r], [n], none, [] => .ok (.signDealloc r n)
  | "RadixReverse", [r], [m], none, [] => .ok (.RadixReverse r.active m)
  | _, _, _, _, _ => .error s!"instantiate: unrecognised/malformed LowGate op {name}"

/-- Build one `Gate` leaf from an `op` node's already-evaluated arguments.
Constructors shared with `LowGate` (`id, H, X, CNOT, Toffoli, ShiftL, ShiftR,
Negate, AddScaled, zeroExtend, signExtend, zeroDealloc, signDealloc,
RadixReverse`) use the same shapes as `buildLowGate`; `Phase` has no `Gate`
counterpart (`Gate` has no single-qubit phase primitive; `Phase` only
appears in a lowered `LowGate` tree). Qubit-valued arguments that are not
themselves a register operand of the gate (`CSignedPhaseProd`'s `ctrl`,
`CmpGeConst`/`CSubConst`'s `flag`, `idealCtrlModMul`'s `ctrl`) are still
carried as single-qubit `regs`, exactly as `H`/`X`/`CNOT` are, so that every
qubit-shaped operand goes through the same `RegExpr.qubit` path; genuine
width/count constants (`CmpGeConst`/`CSubConst`'s `N`, `idealCtrlModMul`'s
`c, N`) are `nats`. -/
def buildGate (name : String) (regs : List ExtReg) (nats : List ℕ) (angle : Option Angle)
    (flags : List Bool) : Except String Gate :=
  let qb (r : ExtReg) : Except String ℕ :=
    match r.singleQubit? with
    | some q => .ok q
    | none => .error s!"instantiate: {name} expected a single-qubit register"
  match name, regs, nats, angle, flags with
  | "id", [], [], none, [] => .ok .id
  | "H", [r], [], none, [] => return .H (← qb r)
  | "X", [r], [], none, [] => return .X (← qb r)
  | "CNOT", [c, t], [], none, [] => return .CNOT (← qb c) (← qb t)
  | "Toffoli", [c1, c2, t], [], none, [] => return .Toffoli (← qb c1) (← qb c2) (← qb t)
  | "QFT", [r], [], none, [] => .ok (.QFT r)
  | "RadixReverse", [r], [m], none, [] => .ok (.RadixReverse r.active m)
  | "SignedPhaseProd", [x, z], [], some phi, [] => .ok (.SignedPhaseProd phi x z)
  | "CSignedPhaseProd", [ctrl, x, z], [], some phi, [] =>
      return .CSignedPhaseProd (← qb ctrl) phi x z
  | "CmpGeConst", [data, scratch, flag], [n], none, [] =>
      return .CmpGeConst n data scratch (← qb flag)
  | "CSubConst", [data, scratch, flag], [n], none, [] =>
      return .CSubConst n data scratch (← qb flag)
  | "ShiftL", [r], [n], none, [] => .ok (.ShiftL r n)
  | "ShiftR", [r], [n], none, [] => .ok (.ShiftR r n)
  | "Negate", [r], [], none, [] => .ok (.Negate r)
  | "AddScaled", [dst, src], [shift], none, [negSrc] => .ok (.AddScaled dst src negSrc shift)
  | "zeroExtend", [r], [n], none, [] => .ok (.zeroExtend r n)
  | "signExtend", [r], [n], none, [] => .ok (.signExtend r n)
  | "zeroDealloc", [r], [n], none, [] => .ok (.zeroDealloc r n)
  | "signDealloc", [r], [n], none, [] => .ok (.signDealloc r n)
  | "idealCtrlModMul", [data, ctrl], [c, n], none, [] =>
      return .idealCtrlModMul c n data.active (← qb ctrl)
  | _, _, _, _, _ => .error s!"instantiate: unrecognised/malformed Gate op {name}"

/-- `LowGate.sequence`-style fold: `seq`'s `body`, right-nested with `id` for
`[]`, matching `LowGate.sequence`'s own recursion. -/
def foldLowGateSeq : List LowGate → LowGate
  | [] => .id
  | g :: gs => g ;; foldLowGateSeq gs

/-- `Gate.seq`-style fold, the `Gate` analogue of `foldLowGateSeq`. -/
def foldGateSeq : List Gate → Gate
  | [] => .id
  | g :: gs => g ;; foldGateSeq gs

/-- Instantiate one template's body against `d`/`env`, unrolling `call`
nodes (D3) until `fuel` runs out. `loop var lo hi body` iterates `body` with
`var` bound to each of `lo, lo+1, …, hi-1` and right-folds the results
(`foldLowGateSeq`), matching how the naive leaf's `signedTerms` sum and
Shor's per-exponent-bit loop are actually laid out as one flat sequence. -/
partial def evalNode (d : Doc) (fuel : ℕ) (env : Env) : Node → Except String LowGate
  | .op name regs nats angle flags => do
      let regs' ← regs.mapM (evalReg env)
      let nats' ← nats.mapM (evalW env)
      let angle' ← angle.mapM (evalA env)
      buildLowGate name regs' nats' angle' flags
  | .seq body => return foldLowGateSeq (← body.mapM (evalNode d fuel env))
  | .adj body => return .adj (← evalNode d fuel env body)
  | .cond guard ifTrue ifFalse => do
      if (← evalProp env guard) then evalNode d fuel env ifTrue else evalNode d fuel env ifFalse
  | .call template wArgs aArgs rArgs => do
      if fuel = 0 then .error s!"instantiate: fuel exhausted at call {template}" else
      match d.templates.find? (fun t => t.name == template) with
      | none => .error s!"instantiate: unknown template {template}"
      | some t => do
          let wVals ← wArgs.mapM (evalW env)
          let aVals ← aArgs.mapM (evalA env)
          let rVals ← rArgs.mapM (evalReg env)
          evalNode d (fuel - 1) (env.call t.wParams wVals t.aParams aVals t.rParams rVals) t.body
  | .loop var lo hi body => do
      let loV ← evalW env lo
      let hiV ← evalW env hi
      let gs ← (List.range (hiV - loV)).mapM
        (fun i => evalNode d fuel (env.bindW var (loV + i)) body)
      pure (foldLowGateSeq gs)

/-- `evalNode`'s `Gate`-valued counterpart, for R2.6's `orderFindingApprox`
criterion. Shares `Env`/`WExpr`/`AExpr`/`RegExpr`/`Prop'` evaluation; only
the `op` leaf dispatcher (`buildGate`) and the fold target differ. -/
partial def evalNodeGate (d : Doc) (fuel : ℕ) (env : Env) : Node → Except String Gate
  | .op name regs nats angle flags => do
      let regs' ← regs.mapM (evalReg env)
      let nats' ← nats.mapM (evalW env)
      let angle' ← angle.mapM (evalA env)
      buildGate name regs' nats' angle' flags
  | .seq body => return foldGateSeq (← body.mapM (evalNodeGate d fuel env))
  | .adj body => return .adj (← evalNodeGate d fuel env body)
  | .cond guard ifTrue ifFalse => do
      if (← evalProp env guard) then evalNodeGate d fuel env ifTrue
      else evalNodeGate d fuel env ifFalse
  | .call template wArgs aArgs rArgs => do
      if fuel = 0 then .error s!"instantiate: fuel exhausted at call {template}" else
      match d.templates.find? (fun t => t.name == template) with
      | none => .error s!"instantiate: unknown template {template}"
      | some t => do
          let wVals ← wArgs.mapM (evalW env)
          let aVals ← aArgs.mapM (evalA env)
          let rVals ← rArgs.mapM (evalReg env)
          evalNodeGate d (fuel - 1) (env.call t.wParams wVals t.aParams aVals t.rParams rVals)
            t.body
  | .loop var lo hi body => do
      let loV ← evalW env lo
      let hiV ← evalW env hi
      let gs ← (List.range (hiV - loV)).mapM
        (fun i => evalNodeGate d fuel (env.bindW var (loV + i)) body)
      pure (foldGateSeq gs)

/-- Instantiate template `t` of `d` at `env`, targeting `LowGate`. `fuel`
bounds the number of `call` unrollings (a concrete run always terminates
well before fuel runs out, since D3's recursion is guarded by a strictly
decreasing width — see `IR/WellFormed.lean`'s check 3 — but nothing here
depends on that guard holding; running out of fuel is a plain `Except`
error, never a proof obligation). -/
def instantiate (d : Doc) (t : String) (env : Env) (fuel : ℕ) : Except String LowGate :=
  match d.templates.find? (fun tpl => tpl.name == t) with
  | none => .error s!"instantiate: unknown template {t}"
  | some tpl => evalNode d fuel env tpl.body

/-- `instantiate`'s `Gate`-valued counterpart. -/
def instantiateGate (d : Doc) (t : String) (env : Env) (fuel : ℕ) : Except String Gate :=
  match d.templates.find? (fun tpl => tpl.name == t) with
  | none => .error s!"instantiate: unknown template {t}"
  | some tpl => evalNodeGate d fuel env tpl.body

end IR
end Shor
