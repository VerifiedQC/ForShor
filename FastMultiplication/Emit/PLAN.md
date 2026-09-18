# PLAN: extract the symbolic IR from the verified definitions by reflection

## 0. What this plan changes and why

`Emit/` currently prints two kinds of thing: the verified circuits evaluated at
concrete parameters (`pp`, `cpp`, `qft`, `shor`), and an n-free "symbolic"
bundle (E1–E7). The concrete side is sound: it evaluates `referenceProgramAt`
and its components and prints the result. The symbolic side is not acceptable
as it stands: `Symbolic/Template.lean` was written by a human reading the
ForShor definitions, so the templates are transcriptions, checked one level
deep at a few widths. The owner's requirement is:

> The symbolic IR must be *extracted* from the verified `referenceProgramAt`
> by an automated process, for any table (any `k`, any `TableSource`), with
> no per-table or per-`k` code. Recursion is not unrolled in Lean; the IR
> carries an encoding of the recursion that a consumer performs once a
> concrete `n` is given.

The mechanism is **reflection**: a `MetaM` program reads the *definitions* on
the `referenceProgramAt` call chain, specialises them to the given table
(which is a closed value, so every `match ops with …` collapses), leaves the
width-determining inputs as free variables, normalises, and translates the
resulting `Expr` into a small first-order IR of parameterised templates. The
recursive definitions become templates whose body contains a `call` to
themselves with translated arguments. Nothing about the circuit's shape is
written by hand.

This plan (a) builds the IR language and its interpreter, (b) builds the
extractor and runs it on the call chain, (c) integrates the output into the
bundle, and (d) deletes the mechanisms this makes redundant. It touches only
`Emit/` and `lakefile.lean`. Nothing in `ShorVerification/` changes.

## 1. Decisions (confirmed with the owner)

| # | decision |
|---|---|
| D1 | **Run-time extraction.** The `forshor_emit template <k> [--table …]` subcommand loads the environment with `importModules` and runs the extractor on `k` and the table given on the command line. No `extract_ir` line per `k` or table anywhere. A build-time elaborator command exists only for pinning `native_decide` tests. |
| D2 | **Genericity boundary.** The translation table is keyed by Lean *construct* (`Gate.seq`, `dite`, `Reg.interval`, `WellFounded.fix`, …), never by `k`, table, or width. A new `k` or table needs no code. An unknown construct is a hard error naming the constant, never a silent drop. |
| D3 | **Recursion is not unrolled in Lean.** A recursive definition yields one template whose body is one activation; the recursive call is a `call` node with its argument expressions. The consumer (and the Lean-side `instantiate`) unrolls at concrete `n`. |
| D4 | **Opaque set.** Left unevaluated and tabulated: `RecursivePhaseWorkspace.nextWidth`, `reserveNeed`, `qftWorkspaceNeed`, the interpolation weight `coeff(l, m)` (= `cramerCoeffFromPtsWidth`), `Nat.log2`, `Nat.clog`. Step R2.1 tests whether `nextWidth` unfolds to a closed expression on a fixed table; if so it leaves the set. |
| D5 | **Concrete table required, supplied through Lean as a `ShorLoweringSetup`.** (Amended by R5, §11.) The input to the symbolic emitter is a `Shor.ShorLoweringSetup` value — `k`, `hk`, `ops`, and the two proofs `consumes`/`returns` the theorems need — defined in a Lean file by the user; `TableSource.standard` is one such value (`standardLoweringSetup k`), not the interface. No table is parsed from JSON or the command line. Symbolic: `n, m, a, N` (Shor), `W, phi, x, z` (phase product), `w, r` (QFT). |
| D6 | **Reference instances stay.** `pp`, `cpp`, `qft`, `shor` and their annotated views remain; they are what the extracted IR is checked against. |
| D7 | **Not a theorem about the extractor; a theorem about each `Doc` (R6, §12).** Trusted: the translation table and Lean's normaliser. Evidence at instances: `instantiate` unrolls the IR at concrete widths and compares byte for byte with the real term (R2/§7.1). Proof for all widths, per `(k, table)`: the R6 theorems `instantiate <doc> … = .ok <verified term>`, generated with the `Doc`. The provenance says which of the two a given `Doc` carries. |

## 2. Ground rules

1. Work on a branch. Build after every step with `lake build forshor_emit EmitTests`. No `sorry`. No edits under `ShorVerification/`.
2. Every extraction target has an exit criterion of the form "`instantiate` of the extracted template equals the real term at these concrete widths"; a step is not done until that is a `native_decide` example in `Tests.lean` and a run-time check in the executable.
3. Delete old code in the same step that makes it redundant, not at the end. The tree must not carry two mechanisms for the same thing.
4. Time-box R2.1. If the normalised `Expr` cannot be translated cleanly there, stop and reconsider before building anything downstream.

## 3. Target layout

```
Emit/
  README.md                rewritten in R4
  PLAN.md                  this file
  Json/
    Common.lean            unchanged
    LowGateJson.lean       unchanged
    PlanJson.lean          unchanged (annotated instances)
  Table/
    Source.lean            unchanged (TableSource, TableInstance, checkTable)
  IR/
    Syntax.lean            WExpr, RegExpr, Node, Template, Doc
    Json.lean              printers for the IR
    WellFormed.lean        decidable well-formedness checks on a Doc
    Instantiate.lean       interpreter: Doc → template name → Env → Except String LowGate
  Proofs/
    Correct.lean           R6 lemma library: evalW / evalReg / evalA / Env.call / evalNode facts
    PhaseProduct.lean      R6 theorems for the phase-product and controlled phase-product Docs
    Qft.lean               R6 theorem for the qft Doc
    Shor.lean              R6 theorems for shor_gate / shor and the referenceShorCircuit corollary
    Generated.lean         theorems emitted by extract_ir_doc! (R6.5); regenerated, not hand-edited
  Reflect/
    Quote.lean             ToExpr instances for Point, valid_ops k, Prog k
    Extract.lean           the MetaM extractor: specialise, normalise, translate
    Targets.lean           the call-chain targets and their symbolic/fixed argument roles
    Driver.lean            run-time entry (importModules) and the build-time `extract_ir` command
  Symbolic/
    CoeffPoly.lean         E2, unchanged
    Width.lean             E3, trimmed: nextWidth / reserveNeed tables only
    QftPlan.lean           E4, trimmed: qftWorkspaceNeed only
    ShorPlan.lean          E5, trimmed: widths and reserves only
    Bundle.lean            trimmed; `template` section = extracted Doc
  Lower/
    Decide.lean            unchanged
    PhaseProduct.lean      unchanged except: checks come from IR/Instantiate
    Qft.lean               same
    Shor.lean              same
  Main.lean                adds `template`; removes nothing user-facing
  Tests.lean               extraction exit criteria as native_decide
```

Deleted: `Symbolic/Template.lean`, `Symbolic/Recursion.lean`,
`Table/Census.lean`, `Lower/Instantiate.lean`.

## 4. R0 — the IR language (`Emit/IR/`)

### 4.1 `Syntax.lean`

```lean
inductive WExpr            -- widths and indices
  | var (name : String)
  | lit (n : ℕ)
  | add | sub | mul | div | max : WExpr → WExpr → WExpr
  | opaque (fn : String) (args : List WExpr)      -- nextWidth, reserveNeed_x, log2, …

inductive AExpr            -- angles (units of π)
  | var (name : String)
  | lit (a : Angle)
  | mul (a : AExpr) (w : WExpr)                   -- phi * integer weight
  | coeff (phi : AExpr) (l : ℕ) (m : WExpr)       -- phi * coeff(l, m), opaque
  | div2 (a : AExpr) | neg (a : AExpr)            -- CPhase's θ/2, −θ/2

inductive RegExpr          -- registers as slice paths back to a parameter
  | var (name : String)                           -- an ExtReg parameter
  | activeSlice (r : RegExpr) (lo hi : WExpr)     -- r.active[lo:hi]
  | reserveSlice (r : RegExpr) (lo hi : WExpr)    -- r.reserve[lo:hi]
  | ext (active reserve : RegExpr)                -- ExtReg.withReserve
  | qubit (r : RegExpr) (i : WExpr)               -- r.active[i], a single qubit

inductive Prop'            -- decidable guards
  | lt | le | eq : WExpr → WExpr → Prop'

inductive Node
  | op (name : String) (regs : List RegExpr) (nats : List WExpr) (angle : Option AExpr) (flags : List Bool)
  | seq (body : List Node)
  | adj (body : Node)
  | cond (guard : Prop') (ifTrue ifFalse : Node)
  | call (template : String) (wArgs : List WExpr) (aArgs : List AExpr) (rArgs : List RegExpr)
  | loop (var : String) (lo hi : WExpr) (body : Node)

structure Template where
  name : String
  wParams : List String
  aParams : List String
  rParams : List String
  body : Node
  provenance : String          -- the Lean constant this was extracted from

structure Doc where
  templates : List Template
  opaqueFns : List (String × ℕ)  -- name, arity
  entry : String
deriving Repr, DecidableEq, ToExpr (all of the above)
```

`op` names are exactly the `LowGate`/`Gate` constructor names so the flat
and symbolic documents share a vocabulary. `ToExpr` is needed so the
build-time command can splice an extracted `Doc` into a `def`.

### 4.2 `Json.lean`

One printer per inductive. `WExpr` renders fully parenthesised; `opaque`
renders as `fn(args)`. `AExpr.coeff` renders as `phi * coeff(l, m)`. Reuse
`angleJson` for literals. The `Doc` prints as
`{"schema": "forshor.ir/v1", "entry": …, "opaque": [...], "templates": [...]}`.

### 4.3 `WellFormed.lean`

Decidable `Doc.wellFormed`:
- every `var` is a parameter of the enclosing template or a `loop` variable;
- every `call` names a template in the `Doc` and matches its arity in all
  three parameter lists;
- every `call` to the enclosing template (direct recursion) is under a
  `cond` whose guard is `lt` or `le` between a `wParam` and an expression;
- every `opaque` name is declared with the right arity.

### 4.4 `Instantiate.lean`

```lean
structure Env where
  w : String → Option ℕ
  a : String → Option Angle
  r : String → Option ExtReg
  opaqueW : String → List ℕ → Option ℕ          -- the real nextWidth, reserveNeed, …
  coeff : ℕ → ℕ → Option ℚ                       -- cramerCoeffFromPtsWidth k m pts l

def instantiate (d : Doc) (t : String) (env : Env) (fuel : ℕ) : Except String LowGate
```

Semantics: `op` evaluates its arguments and builds the constructor; `seq`
folds `LowGate.seq` right-nested with `id` for the empty list (matching
`LowGate.sequence`); `cond` decides the guard; `call` evaluates arguments,
binds them, and recurses with `fuel − 1`; `loop` iterates. `RegExpr`
evaluation uses `Reg.take`/`Reg.drop`/`Reg.append`; the `Disjoint` proof
`Reg.append` needs is decided with `if h : …` and refused otherwise. The
`Gate`-level variant `instantiateGate` is the same interpreter targeting
`Gate` (for R2.6's `orderFindingApprox` criterion).

`Env` is populated from the real functions:
`opaqueW "nextWidth" [w] = RecursivePhaseWorkspace.nextWidth ops w w`,
`"reserveNeed_x"`, `"reserveNeed_z"`, `"qftWorkspaceNeed_x"`, `"_z"`,
`"log2"`, `"clog"`; `coeff l m = cramerCoeffFromPtsWidth k m pts hpts l`.
This is the safety net: it can only agree with the real term if the
extracted structure is right.

### 4.5 R0 status: done, with one deriving adaptation

`Emit/IR/{Syntax,Json,WellFormed,Instantiate}.lean` are built (`lake build
forshor_emit EmitTests` green, no `sorry`). Sanity-checked by hand (not
committed — a scratch, `native_decide`-verified check, since real
`native_decide` exit criteria are R2's job on extracted `Doc`s, not R0's on
hand-built ones): `op`/`seq` folding, `cond`/`call` recursion with `fuel`
decrement and fresh per-call `Env`, and `Doc.wellFormed` all behave as
specified, against a hand-built countdown `Doc` (a `cond`-guarded self-`call`
emitting one `H` per level) and a flat two-op `Doc`.

One deviation from §4.1's "`deriving Repr, DecidableEq, ToExpr` (all of the
above)": `WExpr.opaque (args : List WExpr)` and `Node.seq (body : List
Node)` are nested-inductive occurrences (a type recursing through `List`
itself), and this toolchain's `DecidableEq`/`ToExpr`/`LawfulBEq` deriving
handlers reject that shape outright (`None of the deriving handlers for
class DecidableEq applied to …`), while `Repr` and `BEq` derive correctly
through it (verified structurally, not just that they compile). So every
type in `IR/Syntax.lean` derives `Repr, BEq` only; every equality check in
`IR/WellFormed.lean` is `Bool`/`==`-valued rather than `Decidable`/`decide`
— exactly the convention `Json` already used in this emitter
(`Lower/Instantiate.lean`'s `check1_annotatedEqFlat`) — and R2's
`native_decide` exit criteria (§6) will compare `instantiate`'s `LowGate`
output (which already has ordinary `DecidableEq`/no nested lists) rather
than IR `Doc`s directly. `ToExpr` is untouched by this — it was never
exercised in R0; it is needed only by R1's `Reflect/Driver.lean` build-time
command, and will have to be written by hand there against the same nested
shape (`ToExpr`'s deriving handler has the identical limitation) rather than
derived.

## 5. R1 — the extractor (`Emit/Reflect/`)

### 5.1 `Quote.lean`

`ToExpr Operations.Point`, `ToExpr (Operations.valid_ops k)`, and hence
`ToExpr (Prog k)`. The extractor computes `(tableInstance src k hk).ops`
with compiled code and quotes it as a literal list. This is what makes the
compiler's `match ops with …` reduce under `whnf`.

### 5.2 `Extract.lean`

```lean
structure Target where
  const : Name                          -- e.g. ``compileOpsToSignedGate
  fixed : List (Name × Expr)            -- k, hk, ops, hpts, …
  symbolicW : List Name                 -- parameters that become WExpr.var
  symbolicA : List Name
  symbolicR : List Name
  templateName : String

def extract (tgt : Target) : MetaM Template
def extractDoc (tgts : List Target) (entry : String) : MetaM Doc
```

Pipeline for one target:

1. **Specialise.** `mkAppN (mkConst tgt.const) args` with fixed arguments
   substituted and `mkFreshFVar` for each symbolic one (inside a
   `withLocalDecl` telescope). Proof arguments whose statement is about fixed
   values are discharged by `decide`/`by omega` at this point; proof arguments
   about symbolic values (e.g. `SignedRecursiveWorkspaceOK ops x z`) become
   free variables too, since they are erased by the translation.
2. **Normalise.** Loop: `whnfR` at the head; if the head is in the
   translation table, opaque set, or is a stop construct, translate it and
   recurse into its data arguments; otherwise `unfoldDefinition?` or apply
   the constant's equation lemmas via `simp only`, plus a fixed simp set
   (`Fin.val_mk`, `Nat` literal arithmetic, `List.length_cons`, matcher
   splitting through `Split.simpMatch`). Stop constructs:
   - `dite`/`ite` on a proposition containing a symbolic variable →
     `Node.cond`; the `Decidable` instance argument is ignored.
   - `Nat.casesOn`/`Nat.rec` on a symbolic scrutinee → nested `cond` on
     `eq lit 0`, `eq lit 1`, else (as `lowerQFTPlan`'s `0 / 1 / n+2`).
   - `WellFounded.fix` → do **not** unfold `fix`; instead rewrite with the
     definition's `.eq_def`/`.eq_1` equation lemma, which presents the body
     with the recursive call by name; that occurrence becomes `Node.call` to
     the enclosing template with its argument expressions translated.
   - Any call to another target's constant → `Node.call` to that template.
   - Any opaque constant (D4) → `WExpr.opaque` / `AExpr.coeff`.
   - Register constructors `Reg.interval`, `Reg.take`, `Reg.drop`,
     `Reg.append`, `ExtReg.withReserve`, `ExtReg.grow`, `phaseChunkActive`,
     `PhaseSplitLayout.child`, `ReserveBudget.offset` → `RegExpr` after
     unfolding to slices; `Nodup`/`Disjoint` proofs dropped.
3. **Translate.** `translate : Expr → ExtractM Node` keyed on
   `Expr.getAppFn` constant name. Arguments whose type is a `Prop` or a class
   instance are dropped by checking `inferType`/`isProp`. Unknown head:
   `throwError "extract: unrecognised construct {c} in {tgt.const}"`.

### 5.3 `Targets.lean`

The call-chain targets, in extraction order:

| template | constant | fixed | symbolic |
|---|---|---|---|
| `naive_leaf` | `LowGate.Naive_SignedPhaseProd` | — | `phi : A`, `x z : R` |
| `naive_cleaf` | `LowGate.Naive_CSignedPhaseProd` | — | `ctrl : W`, `phi`, `x z` |
| `pp_body` | `compileOpsToSignedGate` | `k, hk, ops, coeff := fun l => coeff(l, m)` | `phi`, `x z`, layout slots |
| `phase_product` | `standardSignedPhaseLoweringPlan` + `lowerGateRec` | `k, hk, ops` | `phi`, `x z` |
| `cphase_product` | controlled variants | same | + `ctrl` |
| `qft` | `lowerQFT` via `standardQFTLoweringPlan` | `k, hk, ops` | `r : R` |
| `shor_gate` | `orderFindingApprox` | — | `a N : W`, `x y work scratch : R`, `flag : W` |
| `shor` | `referenceShorCircuit` | `lowering` (from `k`, `ops`) | `inst.a inst.N m : W` |

`referenceShorCircuit`'s layout `allocateReferenceLayout` unfolds to
`Reg.interval` at offsets that are `WExpr`s in `n, m` through
`referenceXWidth` (opaque `log2`), so `x, y, work, scratch, flag` become
register expressions in the parameters, not fresh parameters.

### 5.4 `Driver.lean`

- **Run time.** `runExtract (src : TableSource) (k : ℕ) : IO (Except String Doc)`:
  `initSearchPath (← findSysroot)`, `importModules #[{module := `FastMultiplication.Emit.Reflect.Targets}]`,
  then `MetaM.run'` of `extractDoc` in a `CoreM` context built from that
  environment. `lake exe` supplies the search path.
- **Build time.** An elaborator command
  `extract_ir_doc <declName> (k := 2) (src := .standard)` producing
  `def declName : Doc := <quoted Doc>`, used only in `Tests.lean`.

### 5.5 R2.1 spike: findings, before writing `Extract.lean` itself

Ground rule 4 time-boxes R2.1 and says to stop and reconsider before
building downstream of it. Before writing `Extract.lean`/`Targets.lean` for
real, `Quote.lean` was built (below) and then spent against a throwaway,
uncommitted `#eval`-driven `MetaM` script — never a file in this tree —
that hand-built the specialised `compileOpsToSignedGate k hk phi x z layout
phaseCoeff ops` application (`k = 2`, standard table) and watched what
`whnf`/`unfoldDefinition?` actually do to it. Findings:

- **The mechanism works.** `whnf` unfolds `compileOpsToSignedGate`'s
  top-level `let`s cleanly to `allocs ;; body ;; deallocs`
  (`compileSignedAllocations`/`compileAnnotatedOpsToSignedGateAux`/
  `compileSignedDeallocations`, each still applied to unreduced
  sub-arguments — expected, since `whnf` only normalises the head, not
  argument positions; a real extractor must recurse into each argument and
  `whnf` it again, which is exactly what `normalize`/`translate` are for).
  Concrete `Fin k`-recursion (`compileSignedAllocationsAux` at `k = 2`)
  iota-reduces automatically. A structure projection composed with an
  unreduced `def` application (`(targetSignedLayoutState stInit
  need).xslot ⟨1,_⟩`) *does* keep unfolding when `whnf`'d directly —
  confirmed empirically, not assumed — cascading through
  `growExtRegTo`/`ExtReg.grow` down to a literal `{active := …, reserve :=
  …}` structure, `.active` built from real `Reg.take`/`Reg.drop` arithmetic.
  So a proper recursive normalize loop should work; nothing here is
  fundamentally stuck.

- **Finding 1 — a bare opaque `layout` doesn't work; build it with
  fine-grained fresh variables instead.** A `layout : Gate.PhaseProductLayout
  x z k` introduced as *one* free variable leaves `layout.xSplit.reserve i`
  permanently stuck at an unnamed, unstructured `Reg` for every `i` — not a
  formula, nothing `RegExpr` (as specified) can name, since `RegExpr` only
  has slice/qubit/`ext` shapes, not "opaque register indexed by a free
  variable's projection". Fix, confirmed to work: construct `layout` as a
  real structure literal (`PhaseSplitLayout.mk`/`Gate.PhaseProductLayout.mk`)
  whose `reserve : Fin k → Reg` field is built from *k* fresh per-child `Reg`
  free variables (selected by an `ite` chain on `i.val` — `k` is always
  concrete at extraction time, so this is finite and mechanical for any
  `k`), and whose `Prop`-typed fields (`valid`, `active_reserve_disjoint`,
  `reserve_partition`, `child_owned_pairwise`, `cross_owned_disjoint`) are
  free variables too (harmless: they're erased by translation regardless,
  per the existing "Prop arguments become free variables" rule). Once built
  this way, `.xSplit`/`.reserve` project off a literal `.mk` and reduce; only
  the genuinely-opaque reserve qubits stay stuck, as a *plain named
  variable* — which `RegExpr.var` already covers. This generalises: any
  register-parameterised target whose real argument is a dependent
  structure with both formula-shaped and genuinely-opaque data fields needs
  this same "reconstruct with per-leaf freshness" treatment at Specialise
  time, not a single opaque free variable of the whole structure type.

- **Finding 2 — a fully generic `Expr → Node`/`Expr → WExpr` translator is
  more machinery than this target needs; a hybrid is simpler, still generic
  in `k`, and does not weaken D4.** First stated this wrong (as "width/
  layout bookkeeping depends only on `k`, never on the table") and was
  corrected: `RecursivePhaseWorkspace.nextWidth ops wx wz` unfolds to
  `nextSignedWidth … ops = commonNeededWidth (scanNeededWidths x z ops)`,
  and `scanNeededWidths` walks the *actual op list* (`shiftL i n`,
  `addScaled dst src _ sh`, …), accumulating a max-width bookkeeping from
  their concrete indices/shift-amounts — so the target width every chunk
  gets grown to (`Wwork`) genuinely depends on the table; different tables
  give different numbers. That is not in question.
  What *is* still true, more narrowly: (a) the **allocation structure** —
  how many alloc/dealloc gate pairs, at which chunk indices, in which order
  — comes from `compileSignedAllocationsAux`/`compileSignedDeallocationsAux`,
  which take no `ops` argument at all, only `k`; that structure really is
  table-independent. (b) `Wwork` itself is exactly `RecursivePhaseWorkspace.
  nextWidth`, which D4 *already* mandates be opaque — the extractor is not
  permitted to inline/compute it for any table, not because its value is
  table-independent (it is not) but because the plan says not to reflect
  into `scanNeededWidths`'s internals at all. So the extractor recognises
  `commonNeededWidth (scanNeededWidths x z ops)` by constant name and
  emits `WExpr.opaque "nextWidth" [xw, zw]` without inspecting the argument
  — the real, table-dependent number is resolved later, at `instantiate`
  time, by calling the real function with the real `ops` (closed over in
  `Env.opaqueW`). Only `compileAnnotatedOpsToSignedGateAux`'s walk over
  `annOps` — whose *shape* (which ops, how many phase-product leaves) is the
  genuinely table-dependent part the IR must actually capture — needs real
  reflection: `whnf`, recognise the concrete op at the head, recurse.
  Register/width arguments appearing there are looked up against the
  extractor's own precomputed per-slot table (matched by `isDefEq` against
  the handful of `Expr`s it already built, e.g. `stFinal.xslot i` for each
  concrete `i`) rather than re-derived by a general-purpose reflective
  width/register translator. R2.1's `Finset.univ.sup` question (D4's
  optional follow-up, i.e. whether `nextWidth` could instead be *proven*
  reducible to a closed formula and leave the opaque set for a *specific*
  table) is accordingly untested and left open, not resolved either way —
  and does not change any of the above, since D4's default is to leave it
  opaque regardless.

Status: the spike is evidence the approach works and de-risks D2/D3/D7 for
this target; it is not `Extract.lean`. Writing the real, tested,
`native_decide`-backed `Extract.lean`/`Targets.lean` against this hybrid
design (reflect the op-sequence walk; compute width/layout bookkeeping
directly) is the next work, and is substantial enough — plus the further
open question of how `phaseCoeff` applications (`phi * phaseCoeff l`) get
recognised syntactically and turned into `AExpr.coeff` — that it was
reported back rather than pushed through uninterrupted in the same sitting
as this spike.

## 6. R2 — extraction targets and exit criteria

Each row is one step. "Equals" means `instantiate` (or `instantiateGate`)
of the extracted template, with `Env` built from the real opaque functions,
is `DecidableEq`-equal to the real term. Each criterion becomes a
`native_decide` example in `Tests.lean` and a run-time check in `template`.

| step | target | new machinery exercised | exit criterion |
|---|---|---|---|
| R2.1 | `pp_body` at `k = 2`, standard table | `match` collapse, `dite` on `extraDelta`, `RegExpr` slices, `WExpr` | equals `compileOpsToSignedGate … coeff ops` as `Gate`, for `x z` of widths 4..16 |
| R2.2 | `phase_product` | `.eq_def` rewrite of `WellFounded.fix`, `Node.call` to self, `cond` on `nextSignedWidth < phaseInputSize` | equals `standardSignedPhaseLoweringPlan` + `lowerGateRec` at `n = 8` (base) and `n = 16` (recurses) — done, §6.5 |
| R2.3 | `naive_leaf` | `loop` over `signedTerms` of a symbolic register, `AExpr.mul` with two's-complement weights | equals `Naive_SignedPhaseProd` at widths 1..6 |
| R2.4 | `cphase_product`, `naive_cleaf` | `ctrl` parameter, `CCPhase` | as R2.2 at `n = 8`/`n = 16`, and `Naive_CSignedPhaseProd` at widths 1..6 — done, §6.6 |
| R2.5 | `qft` | three-way `by_cases` on symbolic width (not literally `Nat.casesOn`, see §6.7), `qftXWork`/`qftZWork` slices, `RadixReverse` | equals `lowerQFT` at `w = 4, 8` — done, §6.7 |
| R2.6 | `shor_gate`, `shor` | `loop` over exponent bits, `adj`, `AExpr.ratio`, `Prop'.testBit`, `translateLowerGate` (own `Gate → LowGate` structural walk) | `shor_gate` equals `orderFindingApprox` as `Gate`, and `shor` equals `referenceShorCircuit`/`lowerGate ∘ orderFindingApprox`, at `k = 2, a = 2, N = 15, m = 0` — done, §6.8 |
| R2.7 | genericity | none (`Driver.lean`'s surface syntax gained a `--table generate` form) | R2.2 and R2.5 criteria at `k = 3` standard and at `k = 2 --table generate`, with **no change** to `Extract.lean` or `Targets.lean` — done, §6.9 |

R2.1 is the prototype and is time-boxed (ground rule 4). D4's `nextWidth`
question is answered during R2.1: try unfolding
`commonNeededWidth (scanNeededWidths x z ops)` with the quoted table; if the
`Finset.univ.sup` over `Fin k` reduces to nested `max` under a `Fin`
enumeration simp set, `nextWidth` becomes a `WExpr` and leaves the opaque set.

### 6.1 R2.1 status: done

`Emit/Reflect/Extract.lean` and `Emit/Reflect/Targets.lean` (`extractPPBody`)
are real, working code (not the §5.5 spike): they build the specialised
`compileOpsToSignedGate` application per Findings 1–2, `whnfR`+
`unfoldDefinition?`-drive normalisation (never a blanket `whnf` — see
`translateW`'s doc comment: plain `whnf` blows straight through `Min.min`,
`dite`, and even `ite`/`dite` themselves into raw `Decidable.rec` case
splits, destroying the very heads this file needs to recognise; a fully
ground matcher application, e.g. `annotatePhaseTermsAux`'s `phaseTerm?`
match, is the one place a *plain* `whnf` is used, and only as the very last
fallback, after every structural recognizer has already had its chance),
and translate the result into an `IR.Template` named `pp_body`.
`Emit/Reflect/R2_1Test.lean` (a spike file, not `Tests.lean` yet — see
below) instantiates it at `k = 2`, standard table, `x`/`z` both width 4,
with enough reserve that `targetSignedLayoutState`'s growth to
`commonNeededWidth (scanNeededWidths x z ops) = 7` is not truncated, and
checks the result against `compileOpsToSignedGate` itself. Both hold:
`Doc.wellFormed = true`, and the two `Gate`s' flattened leaf sequences
(`Gate` has no `List Gate` field, so plain `BEq`, unlike `IR.Node`, derives
without the R0 nested-inductive limitation — but raw `BEq` still compares
*tree shape*, so `Gate.seq` bracketing differences between the extracted
and real terms, harmless semantically, would read as unequal; flattening
first, exactly `Lower/Instantiate.lean`'s `check1_annotatedEqFlat`
convention, is what actually gets checked) are identical, all 19 leaves,
in order.

One real bug surfaced and fixed along the way: an early test build used an
`ExtReg` with *insufficient* reserve capacity, so `ExtReg.grow` silently
truncated (`Reg.take` past a list's end just returns what's there) instead
of reaching the opaque `nextWidth` — not an extraction bug, a test-setup
bug (a real caller is required to satisfy `SignedRecursiveWorkspaceOK`,
which the test wasn't). Caught by comparing per-slot widths directly
(`(stFinal.xslot i).width` for each `i`) once the flattened leaf counts
disagreed (19 extracted vs 15 real) — the "false" `wellFormed`-adjacent
signal that something was wrong, not proof the extraction was broken.

Since then, done in full:
1. `Driver.lean`'s `ToExpr` (manual for `WExpr`/`Node` — the two
   self-recursive-through-`List` types, same fix shape as R0's `BEq`;
   `deriving instance ToExpr` for everything else, which now just works once
   those two exist) and its build-time `extract_ir_doc <declName> <k>`
   command (§5.4; `.standard` table only so far — no surface syntax for
   `--table generate` yet, that is R2.7's job), which runs the extractor and
   splices the resulting `Doc` in as a real `def`.
2. The R2.1 check itself moved into `Emit/Tests.lean` (§15 there) as an
   actual `example … := by native_decide` against `extract_ir_doc`-pinned
   `pp_body_doc_k2` — superseding the `#eval`-only spike
   (`Reflect/R2_1Test.lean`, `Reflect/DriverTest.lean`, both deleted per
   ground rule 3, one mechanism only). `lake build forshor_emit EmitTests`
   is green with it in.

`IR/Syntax.lean` grew two constructors beyond §4.1's original spec along
the way, discovered by what R2.1 actually needed: `WExpr.min`
(`phaseLimbWidth` is `min`, not just `max`) and `RegExpr.grow` (naming
`ExtReg.grow` directly, D2-style — a grown register's active part is an
append of two *different* sources, the original active slice and a prefix
of whatever the reserve turned out to be, not a single nameable slice).
Both are threaded through `Json.lean`/`WellFormed.lean`/`Instantiate.lean`
too.

Since then, `runExtract`'s run-time half is also done: `Driver.lean`'s
`runExtract (src) (k) : IO (Except String Doc)`, `importModules`-based per
§5.4, wired up as `forshor_emit extract_ir <k>` (not `template <k>` — D1's
literal name is already the *old* hand-written `Symbolic/Template.lean`
view via `sectionNames`/`buildSection`, and per R4 that only gets replaced
once the whole call chain is extracted; colliding the names now would break
the existing `template` command for no reason). One real bug caught getting
this to work: `importModules` defaults `loadExts := false`, which leaves
every environment extension — including the instance-resolution registry —
at its *initial* value, so even `LT Nat` typeclass search failed the first
time this ran. Fix: `loadExts := true`, which per `importModules`'s own doc
comment needs `enableInitializersExecution` (`unsafe`, propagated up
through `runExtract`/`runExtractIR`/`main` — a plain `lake exe` process
never calls it automatically the way the `lean` frontend does; running
arbitrary imported `initialize`-block code is exactly what makes this
`unsafe` in the type-theoretic sense, same category as `native_decide`).
Confirmed working for both `k = 2` and `k = 3` via `lake exe forshor_emit
extract_ir <k>` (no code change between them — D2's genericity, checked
against the actual binary, not just the extraction library code), and
`k = 1` refused cleanly (`exit 3`, `error: runExtract: k = 1 must be > 1`).

Not yet done: R2.2–R2.7 (every other call-chain target — `WellFounded.fix`,
`Nat.casesOn`, `Gate.CSignedPhaseProd`, QFT, Shor — is new machinery this
file hasn't exercised).

### 6.2 R2.2 spike: the `.eq_1` lemma exists and shows exactly what D3 promised

Before building R2.2 (`phase_product` = `standardSignedPhaseLoweringPlan` +
`lowerGateRec`, producing a `LowGate` rather than `Gate`), the one load-bearing
uncertainty was checked directly: `standardSignedPhaseLoweringPlan` is
defined by a **tactic proof** (`:= by by_cases hrec : … · … · …`) under
`termination_by`, not equation-compiler pattern-matching syntax — does Lean
still generate an unfolding equation lemma for a definition shaped like
that? `#check standardSignedPhaseLoweringPlan.eq_1` says yes, and it is
exactly the one-step body D3/the plan's algorithm wants:

```
standardSignedPhaseLoweringPlan k hk phi x z ops hworkspace =
  if hrec : nextSignedWidth x z ops < phaseInputSize x z then
    let step := canonicalSignedStep hk ops x z hrec hworkspace
    …
    have recurse := fun i theta => … standardSignedPhaseLoweringPlan k hk theta
      (dst.xslot i) (dst.zslot i) ops hchild …
    have child := planCompiledSignedPhaseGate hk … (id recurse)
    PhaseLoweringPlan.signedStep phi x z step.layout hrec ⋯ child
  else PhaseLoweringPlan.signedBase phi x z hrec
```

So: rewriting with `.eq_1` (`simp only`/direct term rewriting at the meta
level — never `whnf`/`unfoldDefinition?`, which would unfold the
`WellFounded.fix` underneath into `Acc.rec` noise) exposes the recursion
guard (`nextSignedWidth x z ops < phaseInputSize x z` — opaque `nextWidth`
compared against `phaseLimbWidth`'s already-handled `max xw zw`, both
already things `translateW`/`translateProp` recognise) directly as an
`if`, and the self-call by name (`standardSignedPhaseLoweringPlan k hk theta
(dst.xslot i) (dst.zslot i) ops hchild`) inside a `recurse` helper — this
becomes `Node.call "phase_product" […]` once instantiated at a concrete
`(i, theta)` pair, which happens where `planCompiledSignedPhaseGate`'s own
recursion (parallel to `pp_body`'s `compileAnnotatedOpsToSignedGateAux`,
but building `PhaseLoweringPlan` proof terms instead of plain `Gate`s) hits
a `phaseProduct` leaf and calls `recurse i theta`.

Two things this adds to R2.2's scope, beyond R2.1's machinery:
1. **A new `Doc` dependency.** `lowerGateRec`'s `.signedBase phi x z _ =>
   LowGate.Naive_SignedPhaseProd phi x z` means `phase_product`'s base case
   is a `Node.call` to `naive_leaf` (R2.3) — `phase_product`'s `Doc` is not
   well-formed without `naive_leaf` in it too. Building R2.3 first (no
   recursion, "just" a new construct — `Node.loop` over a register's
   `signedTerms`, not yet exercised either) is the more tractable order.
2. **A new translate case**: recognising `standardSignedPhaseLoweringPlan`
   applications specifically (rewrite with `.eq_1`, not `whnf`/
   `unfoldDefinition?`) before falling through to the generic dispatch —
   `Extract.lean`'s normalize loop needs a per-declaration override, not
   just per-construct-name matching.

Status: spike only, de-risking done; `Extract.lean`/`Targets.lean` do not
yet have a `phase_product` target. `naive_leaf` (R2.3), below, is done.

### 6.3 R2.3 done: `naive_leaf`, a named-construct translation, not a reflected one

Attempting to reflect `naiveSignedPhaseGates`/`signedTerms` the way
`pp_body` reflects `compileOpsToSignedGate` runs straight into what §6.2
flagged: `(signedTerms x).flatMap fun xTerm => (signedTerms z).map fun
zTerm => …` is recursion over `x.active.qubits`/`z.active.qubits`, lists
whose *length* (`x.width`/`z.width`) is symbolic. There is no `.eq_1`-style
equation lemma that turns "structural recursion over a symbolic-length
list" into a visible loop the way one turns `WellFounded.fix` into a
visible self-call — genuinely different shape of problem, not a harder
version of the same one.

Resolution: recognise `Naive_SignedPhaseProd` **by name** and state its
known double-loop shape directly (`Reflect/Targets.lean`'s
`naiveLeafTemplate`, a plain `def`, no `MetaM`/reflection at all — the
function takes no `k`/`TableSource`, so there is nothing to specialise
either). This is the same escape hatch D2 already licenses for one
sub-formula at a time (`RegExpr.grow` for `ExtReg.grow`, `AExpr.coeff` for
the interpolation weight) — D2's translation table is keyed by *construct*,
and a whole named function is as much a construct as `Gate.seq` is; nothing
here is per-`k`/per-table (there is no `k`/table to be per-). One more such
addition: `AExpr.signedPair (phi : AExpr) (xi xw zi zw : WExpr)` names
`signedPairAngle`/`signedBitWeight` directly, for the same reason —
`signedBitWeight`'s sign flip on the *last* loop iteration relative to a
*symbolic* width isn't a fixed branch, and isn't expressible in
add/sub/mul/div/max/min (no negation, no exponentiation) either.
`IR/Instantiate.lean` also grew a `"CPhase"` op case, calling
`LowGate.CPhase` directly rather than decomposing it — its `ctrl = target`
branch is only meaningfully decidable once both are concrete qubits, so
(same idea as `RegExpr.grow`) let the real function decide it at
`instantiate` time instead of forcing a symbolic guard.

What makes a hand-specified (not reflected) template trustworthy is
unchanged: D7's checked-not-assumed standard. `Emit/Tests.lean` §16
`native_decide`-checks `instantiate` of `naiveLeafTemplate` against the
real `LowGate.Naive_SignedPhaseProd` at six `(xw, zw)` pairs spanning widths
1..6 on both sides, and `Doc.wellFormed`. All pass.

### 6.4 R2.2: `phase_product` extracts and is well-formed; `native_decide` verification still open

`Reflect/Targets.lean`'s `extractPhaseProductBody` and the new
`Reflect/Extract.lean` machinery it calls (`translatePlan`,
`translateAnnotatedOps`) now produce a `phase_product` `Doc` for `k = 2`
that passes `Doc.wellFormed` (`Emit/Reflect/R22Test.lean`, a spike, not yet
promoted into `Tests.lean`). Three things had to be solved beyond §6.2's
spike, none of them anticipated there:

1. **`lowerGateRec` on an already-concrete `PhaseLoweringPlan` constructor.**
   It isn't `@[reducible]`, so `whnfR` never exposes its match, and a blind
   full `whnf` overshoots past intended recognition points (e.g. straight
   through `LowGate.Naive_SignedPhaseProd` into `LowGate.sequence
   (naiveSignedPhaseGates …)`, since that's a further-unfoldable `def`, not
   a constructor). Fixed by a dedicated `translatePlan` that mirrors
   `lowerGateRec`'s match table by name (D2), the same technique as
   `naive_leaf`, extended to `PhaseLoweringPlan`'s constructors,
   `dite`/`ite`/bare `Decidable.rec` splits (`planAllocChunkGate`'s
   allocated-width comparisons), and `Eq.rec`/`▸` casts (from builders
   proved via `simpa`, which only repackage the type, never the value).

2. **`planCompileAnnotatedOpsToSignedGateAux`'s `.phaseProduct` leaf case
   cannot be exposed by *any* reduction, however narrowly scoped.** Its
   dependent match's motive mentions `st.xslot i`/`st.zslot i`
   (`Gate.SignedPhaseProd`'s own index type), so exposing it — full `whnf`,
   `whnf` of one argument in isolation, a scan for "whichever argument
   `whnf` changes" — always ends up forcing `LayoutState`/
   `RecursivePhaseWorkspace`/`ReserveBudget` reduction while type-checking
   the result, the same cascade class `Min`/`Max`/`nextWidth` warned about
   in R2.1, just reached through a dependent match's motive rather than an
   unfolded `Decidable` instance. Confirmed empirically several times
   (timeouts with full diagnostics dumps showing exactly this reduction
   set). Resolution: a genuine named-construct translation (D2),
   `translateAnnotatedOps`/`translateAnnotatedOpsGo` — walk the
   *already-concrete* `ops` list embedded (never reduced) in
   `annotatePhaseTermsAux k n ops`'s own syntactic argument list, replicate
   `annotatePhaseTermsAux`+`planCompileAnnotatedOpsToSignedGateAux`'s
   combined logic directly in `MetaM`, and hand `st.xslot i`/`st.zslot i`
   (rebuilt as `Expr`s) to `translateReg`/`translateW`'s existing
   isDefEq-based registry lookup — never reduced directly, exactly the
   technique that already resolves the allocation/deallocation plans and
   the base case.

3. **`natLit?` missed an `OfNat`-wrapped literal after `whnfR`**
   (`Fin.val ⟨0, h⟩` reduces to `@OfNat.ofNat ℕ 0 inst`, not a raw
   `Expr.lit`) — a real, standalone bug, confirmed to have silently broken
   the *already-done* R2.1 test (`extract_ir_doc pp_body_doc_k2 2` failed to
   elaborate) since some earlier point in R2.2 prep extended `translateA`'s
   phase-coefficient recognition down this path. Fixed in `natLit?` itself
   (re-check `getNatValue?` after `whnfR`, not just before); a companion
   `finValLit?` (safe to use a full `whnf`, since a `Fin (q k)` index is
   always `k`-bounded arithmetic, never a D4 opaque quantity) handles
   `Fin.val` uses specifically, including plain unreduced arithmetic like
   `Fin.val ⟨0 + 1, _⟩`. `Emit.Tests` (R2.1 + R2.3) reconfirmed green after
   the fix.

Also fixed along the way: `phase_product`'s self-`call` was missing its
`xCap`/`zCap` width arguments entirely (only `xw`/`zw` were passed) — caught
by `Doc.wellFormed`'s call-arity check once reachable at all. The child
register's own capacity is `reserveNeed_x`/`reserveNeed_z` at
`nextWidth`/`nextWidth` (exactly what `canonicalSignedStep` guarantees it
has), built directly as `WExpr.opaque`, not via `translateW` — `ExtReg.
capacity` was never registered against these slots the way `ExtReg.width`
was, so a registry miss there would have fallen through to the same
reduction risk item 2 describes.

One more, orthogonal finding: `IR/WellFormed.lean`'s rule 3
(`guardLicensesRecursion`) only recognised `lt`/`le` between a bare
`wParam` and anything else. `phase_product`'s real guard is `nextWidth(xw,
zw) < max(xw, zw)` — neither side a bare parameter, both sides formulas
*of* the parameters. Since the left side is the opaque `nextWidth` — by D4
precisely the quantity guaranteed to strictly decrease across the
recursive call — a comparison against it is exactly the evidence rule 3
looks for, one step removed from a bare parameter. `guardLicensesRecursion`
now accepts either shape (`wLicenses`); rule 3's description above and in
`WellFormed.lean`'s own docstring updated to match.

### 6.5 R2.2 status: done

`Emit/Tests.lean` §17 (`section R2_2`) checks `IR.instantiate` against
`Shor.standardSignedPhaseLoweringPlan` + `Shor.lowerGateRec` — not
`lowerSignedPhaseProdWithWorkspace` as §1's table originally named it; that
name doesn't exist, the real call chain reflection actually walks is the
one `Reflect/Targets.lean`'s `extractPhaseProductBody` docstring names — at
`n = 8` (base: `nextWidth ops 8 8 = 9 ≥ 8`, guard false, real term is
`LowGate.Naive_SignedPhaseProd`) and `n = 16` (recursive: `nextWidth ops 16
16 = 13 < 16`, `reserveNeed ops 16 16 = (72, 72)`, 100 qubits of reserve on
each side is enough). Both pass `native_decide`, and `IR.Doc.wellFormed
r2_2_doc = true` does too. `Reflect.Driver`'s `buildDoc` now bundles
`pp_body`, `phase_product`, and `naive_leaf` in one `Doc` — R2.1's own test
(`extract_ir_doc pp_body_doc_k2 2`) still only checks `pp_body` within it,
unaffected.

Two more things had to be fixed to get the `native_decide` checks running,
beyond §6.4's three extraction bugs:

1. **`extract_ir_doc`'s `PrettyPrinter.delab`-then-reparse pinning strategy
   doesn't scale to `phase_product`'s size.** Once `buildDoc` extracts
   `phase_product` too (thousands of nested `WExpr`/`Node` constructors),
   delaborating the whole `Doc` into surface syntax starts eliding
   subterms as unreconstructable placeholders, which then fail to
   re-elaborate. Fixed by skipping the surface-syntax round-trip entirely:
   `extract_ir_doc` now builds a `Declaration.defnDecl` directly from the
   already-computed `Expr` (`toExpr doc`) and registers it with
   `addDecl`/`compileDecl`, resolving the declaration name against
   `getCurrNamespace` itself rather than delegating that to `elabCommand`.
2. **`Env.call` (`IR/Instantiate.lean`) carries `opaqueW`/`coeff` unchanged
   into a recursive `call`'s own environment** — and the child level's own
   interpolation width `m` (`phaseLimbWidth` at the child's smaller
   widths) genuinely differs from the top level's. An `Env.coeff` keyed to
   one fixed `m` (which would have been enough for a non-recursive target)
   silently errors every recursive call. Fixed by having `coeff` recompute
   `cramerCoeffFromPtsWidth` at whatever `m` it is asked for, exactly like
   the real `loweringPhaseCoeff` does for any `x`/`z` — this is a general
   lesson for `qft`/`shor`'s own recursive/looping `Env`s later, not
   specific to `phase_product`.

### 6.6 R2.4 status: done — `cphase_product` and `naive_cleaf`

The controlled counterparts of R2.2/R2.3 reused essentially all of that
machinery unchanged, parameterised by `ctrl`. `Emit/Tests.lean` §18
(`naive_cleaf`) and §19 (`cphase_product`) both pass `native_decide` — the
latter at the same `n = 8`/`n = 16` widths as R2.2, since `ctrl` plays no
part in the layout/reserve bookkeeping (`canonicalSignedStep`, `reserveNeed`
— all unaware of any control qubit), only in which qubit the phase leaves
are controlled by.

Two design points, not fixes:

1. **`ctrl : ℕ` is a bare qubit index, not sliced from any register — but
   `IR/Instantiate.lean`'s `buildLowGate` already had a documented
   convention for exactly this shape** (`CSignedPhaseProd`'s own `ctrl` is
   named in that docstring): carry it as a single-qubit register parameter
   (`RegExpr`/`rParams`), not a width one, going through the same
   `ExtReg.singleQubit?` path as every other qubit-shaped operand. Extended
   `buildLowGate` with a `"CCPhase"` case (`LowGate.CCPhase`, the same
   "opaque named function" treatment `"CPhase"` already got, since its
   three pairwise qubit-equality branches are no more symbolically
   decidable than `CPhase`'s one). `naive_cleaf`'s `rParams := ["ctrl", "x",
   "z"]`; `extractCPhaseProductBody` registers the free `ctrl` variable
   against `RegExpr.var "ctrl"` directly, in the same registry as `x`/`z`,
   even though its Lean type is `ℕ` — `translateReg` never inspects a
   candidate's type, only its shape, so this is unremarkable to it.
2. **`translateAnnotatedOps`/`translateAnnotatedOpsGo` took a `ctrl :
   Option Expr` parameter** rather than duplicating the whole function for
   the controlled case — `planCompileAnnotatedOpsToCSignedGateAux` is
   structurally identical to `planCompileAnnotatedOpsToSignedGateAux`
   (confirmed by reading both in full) except that its `.phaseProduct` leaf
   calls `cphase_product` with `ctrl` instead of `phase_product`, so one
   shared walk covers both, dispatched on `plan.getAppFn.constName?` in
   `translatePlan`.

One real bug, caught immediately by the wellFormed extraction test showing
only one `cphase_product` call and zero `AddScaled` ops where R2.2's own
output had three and eight respectively: a stray `return` inside a `match`
arm nested inside a `do` block (`some ctrlE => return .call "cphase_product"
…`) performed an early return from the *entire* enclosing
`translateAnnotatedOpsGo` call, discarding `tail` — everything in the ops
list after the first `.phaseProduct` occurrence silently vanished. The
exact same failure mode `PLAN.md`'s R2.1 notes already document once
(`Return` misuse in do-notation) recurred verbatim; fixed with `pure <| ...`
instead of `return ...`, matching the `none` branch's own style.

### 6.7 R2.5 status: done — `qft`

`standardQFTLoweringPlan` (`.eq_1`, three-way `by_cases`: `regSize r = 0` /
`= 1` / recurse) + `lowerQFTPlan` (a plain structural match over
`QFTLoweringPlan`, an inductive *certificate* shaped like `PhaseLoweringPlan`
— its own `translateQFTPlan`, not a `PhaseLoweringPlan` case). `Emit/
Tests.lean` §20 checks `IR.instantiate` against `lowerQFT` at `w = 4` (two
levels of `qft`'s own recursion) and `w = 8` (three levels) — both pass
`native_decide`, and `Doc.wellFormed`. `qftWorkspaceNeed ops _ = (1, 1)`
for every width in the standard `k = 2` table, so a 2-qubit reserve always
suffices regardless of `w` — the fixtures didn't need scaling per width.

This one was genuinely new machinery — `Reg` (not `ExtReg`) as the
recursion variable, two recursive self-calls per split plus one embedded
`phase_product` call, `regSize`/`ExtReg.width`/`.capacity` needing to be
computed structurally on composed slices instead of read off a registered
top-level variable — but every fix followed patterns this file had already
established, just applied to new shapes:

1. **`LowGate.H`/`.RadixReverse` had no `translateNode` case yet** (`qft`
   is the first target to use either). `H`'s argument is `Reg.lowQubit`, a
   raw-`ℕ` projection named directly (D2), not reduced — same reasoning as
   `Naive_CSignedPhaseProd`'s `ctrl`. `RadixReverse`'s register argument was
   already anticipated in `IR/Instantiate.lean`'s `buildLowGate` (a bare
   `Reg`, treated as an `ExtReg` with that `.active`) but never exercised
   until now.
2. **`leftReg`/`rightReg` (`Split.lean`)** — `r.take (regSize r / 2)`/
   `r.drop (regSize r / 2)` — named directly in both `translateW` (for
   `regSize (leftReg _)`/`(rightReg _)`) and `translateReg` (as
   `RegExpr.activeSlice`, which composes correctly under arbitrary nesting:
   each level slices *relative* to its immediate parent, exactly matching
   `Reg.take`/`.drop`'s own semantics — verified by hand against
   `evalReg`'s `.activeSlice` case before relying on it).
3. **`qftPhi (m : ℕ) : Angle := 2 / 2 ^ m`** — a new `AExpr.qftPhi`
   constructor (D2: not expressible in `add`/`sub`/`mul`/`div2`/`neg`, no
   exponentiation), threaded through `Json`/`WellFormed`/`Instantiate`.
4. **A new `wellFormed` rule 3 shape**: `qft`'s recursion guard is a
   *chain* of `eq`s ruling out base-case widths (`regSize r = 0`, then
   `= 1`), never an `lt`/`le` at all. `guardLicensesRecursion` extended to
   treat `eq` the same as `lt`/`le` — marking a base case's own `then`
   branch "guarded" too is harmless, rule 3 only ever *permits* recursion,
   never requires it.
5. **`ExtReg.width`/`.capacity`/`regSize` on a *computed* register
   (`qft`'s `ws.xExt.grow 1`, `ws.xReserve`, …) needed one-structural-layer-
   at-a-time unfolding, not a blind `unfoldDefinition?` on the whole width
   expression.** The latter only ever unfolds the *outermost* head; once
   that head becomes a non-unfoldable primitive like `List.length`, the
   argument underneath (still carrying the actual structure —
   `ExtReg.grow`, `ExtReg.withReserve`, …) is stuck unreduced forever,
   confirmed empirically (`(⋯).active.qubits.length` with `⋯` untouched).
   Fixed by unfolding the *argument* one step at a time, re-wrapping in the
   same head so each newly-exposed layer gets a fresh chance at the named
   cases (`ExtReg.grow n` → `width parent + n`; `ExtReg.withReserve active
   reserve _` → `regSize active`/`regSize reserve`; …).
6. **`Gate.PhaseProdWorkspace.xReserve`/`.zReserve` (`ws.xExt`'s reserve
   pool) sit behind a raw structure-field accessor on `ws := hworkspace.
   phaseWorkspace hlarge`** — itself a `by ...; exact {xReserve := xWork,
   zReserve := zWork, ...}` tactic-mode def, the same shape as
   `planCompiledSignedPhaseGate`. A blind `whnf` of the whole projection
   gets stuck partway through (confirmed empirically — `.1` stops appearing
   before the struct literal is ever reached), so `QFTWorkspaceOK.
   phaseWorkspace` needed the same `.eq_1` treatment (a new shared
   `unfoldPhaseWorkspace` helper) before the projection onto the exposed
   struct literal could iota-reduce.
7. **`translateWFallback` gained a genuine last-resort full `whnf`**,
   mirroring `translateNode`'s own — safe for the same reason: every
   D4-opaque-headed shape (`nextWidth`, `reserveNeed`, `qftWorkspaceNeed`)
   is already caught by name earlier in `translateW`, so anything that
   reaches this point is ordinary ground arithmetic a stuck non-unfoldable
   head (a bare projection) is blocking, not a cascade risk.

### 6.8 R2.6 status: done — `shor_gate` and `shor`

`shor_gate` (`Shor.orderFindingApprox`, `Gate`-valued, no `k`/`hk`/`ops` at
all) and `shor` (`Shor.lowerGate k hk ops (orderFindingApprox …)
hLowerWorkspace`, i.e. `referenceShorCircuit`'s whole body, `LowGate`-valued)
both extract and pass `native_decide` against the real implementation at
`k = 2, a = 2, N = 15, m = 0` (`Emit/Tests.lean` §21/§22, reusing the
pre-existing `smallLowering`/`smallInst` fixture), plus `Doc.wellFormed` for
both. This is the largest target by far — the whole of Algorithm 1 — and
needed the most new machinery of any R2 phase, almost all of it a *deeper*
instance of failure modes R2.2–R2.5 had already named once:

1. **`H_reg`/`initY1`/`modExpApproxValid`**: three more `naive_leaf`-shaped
   symbolic-list recursions (D2). `modExpApproxValid`'s loop body
   (`CmodMulInPlaceCore`, keyed to the loop variable `e`) is the first one
   whose body is itself a *multi-step circuit*, not a single leaf gate — its
   handler introduces fresh free variables for `e` and `c := (a^(2^e)) % N`
   (registered directly against `.var "e"`/an `.opaque "modpow"` term) and
   re-runs `translateNode`/`translateLowerGate` on one generic step body,
   rather than reducing the recursion at all.
2. **New D4-opaque `WExpr`/`AExpr` primitives**: `HMod.hMod` → `.opaque
   "mod"`, `HPow.hPow`/`Nat.pow` → `.opaque "pow"`, `Shor.step5Constant`
   (built from `Nat.find` — not just non-reducible but genuinely stuck as a
   `Decidable.rec` case split under `whnf`) → `.opaque "step5Const"`, and a
   new `AExpr.ratio (num denom : WExpr)` lifting a `(num : ℚ)/(denom : ℚ)`
   nat fraction into an angle — Step 1/2/5's phase-load constants are raw
   `ℚ` arithmetic on `ℕ`-cast operands, not calls through any existing
   `AExpr` vocabulary. Recognising the `ℚ`-typed literal factor in `2 * (↑X :
   ℚ)` needed its own check (`natLit?`'s `getNatValue?`/`whnfR` chain is
   built for `ℕ`-typed literals and returns `none` on `(2 : ℚ)`; the fix
   reads the `OfNat` literal argument directly). A power-of-two denominator
   (Step 2's `(2 * N) / 2 ^ e`) is instead `N * qftPhi(e)`, reusing the
   existing constructor rather than growing a second one.
3. **`lowerCopyConstFromUnit N dst ctrl := lowerCopyBitPowers dst ctrl
   N.bitIndices`** (Step 3's constant write, `ModularExponentiation/
   Lowering/ConstArithmetic.lean`): recursion over a symbolic-length list
   again, reformulated (D2) from "recurse over `N.bitIndices`" to "loop over
   every bit position of `dst`, guarded on whether `N` has that bit set" —
   the two coincide by `Nat.bitIndices`'s own definition (its values are
   exactly `{i | N.testBit i}`, sorted ascending, matching `Node.loop`'s own
   ascending fold order). Needed a new `Prop'.testBit (n i : WExpr)` guard
   (`IR/Syntax.lean`/`WellFormed.lean`/`Json.lean`/`Instantiate.lean`, mirrors
   `.lt`/`.le`/`.eq`); never licenses recursion (rule 3), since nothing
   recurses inside its `Node.cond`.
4. **`translateLowerGate` (`shor`'s own top-level walk)**: a new function
   mirroring `Shor.lowerGate`'s match table by hand (D2 — `lowerGate` isn't
   `@[reducible]`), taking `ops` as an explicit extra argument (needed only
   to rebuild `Gate.QFT`'s `qftXWork ops r`/`qftZWork ops r`) but *never*
   threading the workspace proof through at all: `GateWorkspaceOK` is a
   `Prop`, and by inspection every case of `lowerGate`/`lowerQFT`/
   `lowerSignedPhaseProdWithWorkspace`/… reads its registers/widths straight
   off the `Gate`'s own constructor arguments, never off the workspace value
   — confirmed by grepping each definition, not assumed. `Gate.QFT`/
   `.SignedPhaseProd`/`.CSignedPhaseProd` become `Node.call`s into `qft`/
   `phase_product`/`cphase_product` exactly the way each template's own
   internal self-call already does (reusing that construction verbatim, not
   duplicating it); `Gate.CmpGeConst`/`.CSubConst` delegate to
   `translateNode`'s ordinary `unfoldDefinition?` fallback (`lowerCmpGeConst`/
   `lowerCSubConst` are plain defs, no further lowering needed inside them);
   `modExpApproxValid`'s loop body is the one case that must recurse via
   `translateLowerGate` and not `translateNode`, or the `CSignedPhaseProd`/
   `QFT` calls inside `CmodMulInPlaceCore` would wrongly stay Gate-level `.op`
   nodes instead of lowered `.call`s.
5. **A cluster of `.proj`/`isDefEq` bugs, all instances of one root cause,
   found and fixed in this order:**
   - `reg.lookupReg`/`lookupWidth`'s blanket (unbounded-transparency)
     `isDefEq` against a query still headed by a plain, non-reducible `def`
     like `ModMulCircuitWorkspaceOK.step1Workspace` forces Lean's own
     reduction machinery to try to unfold straight through the `ofExtRegs`
     tactic proof looking for a match — independently of and far more
     expensively than `unfoldPhaseWorkspace`'s targeted `.eq_1` shortcut.
     Confirmed to be the actual R2.6 `isDefEq` "hang" (easily mistaken for
     non-termination at 1–4 million heartbeats). Fixed not by weakening
     `lookupReg`/`lookupWidth` (an earlier attempt broke R2.2–2.5's
     `targetSignedLayoutState`-style lookups, which *do* need full-transparency
     `isDefEq` to match) but by factoring the `.xReserve`/`.zReserve`
     resolution into a new `resolvePhaseReserve` helper that `.xExt`/`.zExt`
     call *directly*, skipping `translateReg`'s public entry (and its
     registry pre-check) for freshly-built, never-registered queries.
   - `unfoldDefinition?` on a *named* structure-projector constant applied
     to a literal (e.g. `ws.xReserve` once `ws` is a struct literal) reduces
     to Lean's low-level `Expr.proj` form, not the named-constant application
     `translateReg`/`translateW`'s `getAppFnArgs`-keyed dispatch expects —
     invisible to every case, always falling through to the generic
     fallback. Fixed with a new `unfoldProj` helper, called at `translateReg`'s
     top and wherever `translateW`/`resolvePhaseReserve` recurse past an
     `unfoldDefinition?` step.
   - `unfoldProj`'s first version rebuilt the named form via `mkAppM`, which
     *elaborates* through the surface application and, for a parameter-free
     structure like `ExtReg`, immediately re-lowers it right back to the same
     `.proj` node — an infinite `unfoldProj ↔ mkAppM` loop (the actual cause
     of an observed stack overflow, not `resolvePhaseReserve`/`translateReg`'s
     own mutual recursion, which only ever re-*visited* the identical stuck
     term because of it). Fixed with `mkAppN`/`mkConst` (no elaboration).
   - Even with `mkAppN`, rebuilding the named projector never actually
     *reduces* it when the scrutinee is already a literal constructor —
     `unfoldDefinition?`/a rebuilt named form both just reproduce the same
     stuck shape, since neither performs iota reduction. Fixed by having
     `unfoldProj` check whether the (`whnfR`'d) scrutinee is already the
     structure's own constructor application and, if so, index straight into
     its args (`getStructureCtor`'s `numParams + idx`) instead of rebuilding
     anything.
   - `translateWFallback`'s final resort was a single unbounded `whnf`,
     which — once a `.proj` chain like `Fin.val ⟨scratch.width - 1, _⟩`
     needed resolving — didn't stop at the recognisable `HSub.hSub` shape;
     it cascaded straight through `Nat.sub`'s own well-founded recursion,
     stranding a raw `Nat.pred`-style `match` on a symbolic `scratch.width`
     (the same cascade risk already documented for `Min.min`/`Nat.mod`).
     Fixed by running `unfoldProj` on `unfoldDefinition?`'s result before
     recursing, so `translateW`'s own dispatch gets a look at
     `scratch.width - 1` before anything cascades past it.
6. **Two bare-slice `translateReg`/`translateW` cases neither earlier target
   needed**: a *bare* `Reg.take`/`Reg.drop` (no outer `.drop`/`.take`
   wrapping — `ExtReg.newBits n := e.reserve.take n`,
   `ModMulCircuitWorkspaceOK.step1Workspace`'s `data.reserve.drop 1`), and
   `regSize (ExtReg.reserve parentE) = ExtReg.capacity parentE` /
   `regSize (ExtReg.active parentE) = ExtReg.width parentE` by definition
   (mirrors the existing `.grow`/`.withReserve` cases one level up).
7. **`LowGate.X`/`.CNOT`/`.Toffoli`/`.adj` had no `translateNode` case**
   (`qft`'s `LowGate.H` was the only primitive any earlier target lowered
   to directly) — `lowerPrepareNegConst`/`cmpLtNWSignQubit`'s sign-copy
   produce them directly. Added with the same `translateQubitIndex`
   treatment as their `Gate` counterparts.
8. **Test-side canonicalisation**: `orderFindingApprox`/`referenceShorCircuit`
   are the first targets whose *adjoints* wrap multi-gate sub-sequences
   (`step5`'s `†(H_reg ;; CPhaseProdUsing ;; IQFT)`, `cmpLtNW`'s `†diff ;;
   †mul`) — the established `_flatten` idiom (flatten one top-level `;;`
   chain, compare lists) leaves a mismatch hidden inside an unflattened `adj`
   body invisible, since `Node.seq`'s `foldGateSeq`/`foldLowGateSeq` folding
   introduces a trailing `.id` a real direct `;;` chain never has. Both
   `r2_6g_flatten`/`r2_6_flatten` now recurse into `.adj` bodies too,
   rebuilding a canonical (trailing-`.id`-normalised) adjoint on both sides
   before comparing — `translateNode`'s own `.seq`/`.adj` cases needed no
   change, this was purely a test-comparison gap.

Per the R2.6 research fork's finding (confirmed by direct inspection of
`Shor.Lowering.LowerGate.lean`): `lowerGate`'s per-constructor match is a
near-trivial structural walk with the QFT/phase-product/controlled-phase-
product legs the only non-primitive dispatches, and `lowerCmpGeConst`/
`lowerCSubConst` are plain (non-tactic-mode) defs built from already-handled
`LowGate` primitives plus the one `N.bitIndices` recursion — this matched
reality exactly; no further surprises turned up once each piece above was
in place.

### 6.9 R2.7 status: done — genericity checkpoint

R2.2's and R2.5's exit criteria both hold at `k = 3` (standard table) and at
`k = 2` with the `generate` table source (`Emit/Tests.lean` §23, four
sections: `phase_product`@k3-standard, `phase_product`@k2-generate,
`qft`@k3-standard, `qft`@k2-generate) — all `native_decide`, all
`Doc.wellFormed`. **No change to `Extract.lean`/`Targets.lean`**: both files
were already generic in `k`/`src` (`extractPhaseProductBody`/
`extractQFTBody` always took `src : TableSource` as a plain argument; nothing
about the reflection/translation logic ever inspects `k` or `src` beyond
threading them through). The one change needed was to `Driver.lean`'s
*surface syntax*, exactly as PLAN.md always said it would be
(`extract_ir_doc` was `.standard`-only, `--table generate` "not wired into
the surface syntax yet"): a second `elab` alternative, `extract_ir_doc <id>
(<k>, generate)`, alongside the original `extract_ir_doc <id> <k>` form (now
sharing one `elabExtractIrDoc` helper parameterized by `TableSource`).

One genuine, pre-existing finding surfaced by testing `.generate` at all
(not a bug in this extractor, and not something either test needed to work
around by changing `Extract.lean`): `standardSignedPhaseLoweringPlan`/
`standardQFTLoweringPlan` (`PlanBuilders.lean`) hardcode
`genInterpolationPoints k` — the *standard* table's own interpolation
points — for every phase coefficient, regardless of what `ops : Prog k` they
are actually handed (visible directly in their own recursive obligation's
stated type). Passing `.generate`'s `ops` in still produces a *structurally*
correct gate sequence (the recursion/allocation logic genuinely does follow
`ops`), but the resulting *angles* are always the standard table's
coefficients — a property of the verified implementation itself, orthogonal
to extraction. The `.generate` test sections' `env.coeff` callbacks
therefore look up `(tableInstance .standard k hk).points` even though their
`ops`/`opaqueW` callbacks are built from `.generate` — matching what
`standardSignedPhaseLoweringPlan` itself actually computes, which is exactly
what a "does the extractor faithfully reproduce the real function" check
needs to compare against. (Confirmed by first setting `env.coeff` to
`.generate`'s own points, as the naive generalization from R2.2's `.standard`
env would suggest, and watching the comparison fail on specific `Phase`
angles deep inside a recursive leaf — chasing that down to
`standardSignedPhaseLoweringPlan`'s hardcoded `recurse` obligation, not a
translation bug, was what surfaced this.)

Two smaller fixture notes, both about the `.generate` table specifically
having different `RecursivePhaseWorkspace.reserveNeed`/`nextSignedWidth`
values than `.standard` at the same widths:
- The width-8, no-reserve fixture that serves as R2.2's own base case
  (`nextSignedWidth = q k`-or-above, no recursion needed) is *not* a base
  case for `.generate` at the same width (`reserveNeed (8, 8)` is nonzero) —
  needed a generous `withReserve` fixture (matching R2.2's own *recursive*-
  case fixture) instead of a bare `ExtReg.ofReg`.
- With that larger reserve, `SignedRecursiveWorkspaceOK.owned_disjoint`
  needed `native_decide`, not `decide` — `decide`'s kernel evaluator hits
  `maxRecDepth` on the larger owned-qubit-list disjointness check once the
  reserve is added, exactly the same tactic choice R2.2's own recursive-case
  fixture already made for the same reason.

## 7. R3 — bundle integration

- `Bundle.lean`: `template` becomes the extracted `Doc` (printed by
  `IR/Json.lean`), preceded by `Doc.wellFormed` and by the R2 instance
  checks at a ladder of small widths; any failure refuses the whole bundle
  with exit 3.
- `bundle` gains `--no-template` to skip the environment load; `template <k>`
  prints the `Doc` alone.
- Value tables trimmed to opaque functions (D4): `coeff_poly` unchanged;
  `width` = `nextWidth`, `reserveNeed_x/z` over `w = 1..wMax`; `qft_plan` =
  `qftWorkspaceNeed` only; `shor_plan` = widths and reserves only. `schedule`
  keeps `ops` and `points`.
- `--w-max` default rises to cover a full ladder; the consumer's unrolling
  needs `nextWidth` at every width it visits. `template` refuses if
  `--w-max` is below the largest width its own instance checks use.
- `provenance.template`: "extracted by reflection from the named constants;
  trusted: translation table and Lean normalisation; checked: instantiate =
  real term at the listed widths; not a theorem."

### 7.1 R3 status: done

**The bundle-integration design.** `buildBundle`/`buildSection`
(`Symbolic/Bundle.lean`) were pure, `native_decide`-testable functions —
but embedding the extracted `Doc` needs `Reflect.runExtract`'s
`importModules` environment reload (D1: extraction is a run-time,
`unsafe`/`IO` operation; there is no way to reflect over a fresh
`Environment` value from plain `IO` code otherwise). Rather than making the
*whole* bundle pipeline `unsafe`/`IO` (which would have made
`buildBundle`/`buildSection` un-`native_decide`-able and broken several
existing `Tests.lean` checks), the file split in two:

- `buildBundleCore` (pure): `schedule`, `coeff_poly`, `width`, `qft_plan`,
  `shor_plan` — everything that was always a plain evaluation of an opaque
  function or a Toom-Cook table lookup. Still `native_decide`-testable.
- `buildTemplateDoc`/`buildBundle` (`unsafe`, `IO`): extract, verify, and
  either print the `Doc` alone (`template <k>`) or splice it into
  `buildBundleCore`'s result under `"template"` (`bundle`, unless
  `--no-template`).

**What "the R2 instance checks at a ladder of small widths" means here.**
`Tests.lean`'s R2.1–R2.7 suite checks `instantiate` against the real term
at *fixed* small `k`/widths, pinned at build time via `extract_ir_doc`
(§6). `template`/`bundle` extract a `Doc` for whatever `(k, src)` the
caller asks for at *run* time, so that fixed suite can't be what gates a
run-time `k = 37` request. The safety net is instead `Reflect/Verify.lean`:
a *generic-in-`(k, src)`* re-run of the same style of check — `Doc.
wellFormed`, then `instantiate`/`instantiateGate` agreeing with the real
compiled/reference term — at one representative width per template
(`4 * k`, chosen only to be comfortably past `k` so slot splitting is
exercised; not a search for a width that forces recursion). This is a
canary, not exhaustive re-verification: exhaustive base/recursive coverage
is what the fixed-width R2 suite already established, and D2 (the
extractor is keyed by Lean construct, never by `k`) is exactly the
argument for why agreement at one representative width generalizes to
every other `(k, src)`. `shor_gate`/`shor` are only checked for
`.standard` — `.generate` has no `ShorLoweringSetup` to build a reference
Shor instance from, and R2.7 never established that genericity claim
either (only `phase_product`/`qft`).

Concretely: `Reflect.Verify.verifyDoc` runs this canary and
`Reflect.runExtractAndVerify` composes it with `runExtract`; any failure
(extraction error, well-formedness failure, or a canary disagreement)
refuses the whole `bundle`/`template` output with exit 3, before anything
is printed — satisfying "preceded by `Doc.wellFormed` and by the R2
instance checks … any failure refuses the whole bundle."

**`pp`/`cpp`/`qft`'s own checks got the same treatment, generalized
further.** Their old `template_match`/`ladder`/`split` checks compared the
annotated plan against the *hand-written* `Symbolic/Template.lean`
one level deep. With that file gone, they now run the *exact* same
`instantiate_eq_real` check `Reflect/Verify.lean`'s canary runs, but at
whatever concrete `n`/`w` the caller actually asked for (not just the
canary's own representative `4 * k`) — a strictly more meaningful,
full-depth check than the one-level structural comparison it replaced.
This is why `buildPP`/`buildCPP`/`buildQFT` are `unsafe`/`IO` now too, and
why the corresponding `Tests.lean` `native_decide` examples (which cannot
run `IO`) were removed — R2.1–R2.7's own compile-time suite already
established the extraction is correct in general; these commands'
per-invocation check is about *this build's* extracted `Doc` agreeing with
*this invocation's* real term, which is exactly what a live CLI tool
should re-confirm, not something `native_decide` could check anyway (it
would need `k`/`n` fixed at proof-elaboration time, defeating the point of
a live check for the caller's own arguments).

`Json/PlanJson.lean` gained `deepFlattenPlanJsonList`/`wrapFlattened`/
`check1_annotatedEqFlat` (moved from the deleted `Lower/Instantiate.lean` —
`annotated_eq_flat` has nothing to do with the extracted `Doc`, so it
didn't belong in `Reflect/Verify.lean`). `Lower/Registers.lean` is new:
`ppRegisters`/`qftRegister` moved out of `PhaseProduct.lean`/`Qft.lean` so
`Reflect/Verify.lean` can build the same registers those commands do
without an import cycle (`Verify.lean` needs to be importable *by*
`PhaseProduct.lean`/`Qft.lean`, so it can't itself depend on them).

`Tests.lean`: `buildBundleCore` replaces `buildBundle` in the two
compile-time bundle checks (§10's old test 8); the old tests checking the
hand-written E7 template's leaf count, the bundle's old four-part
`template` section, and `pp`/`cpp`/`qft`'s `template_match`/`ladder`/
`split` fields (old tests 9–11) were deleted — superseded by R2.1–R2.7's
own exit criteria against the *real* extracted `Doc`, which is a strictly
stronger claim than anything those tests were checking. The `#guard`
anchors on `widthLadder`/`recursionLevels` (old test 12) were deleted along
with `Symbolic/Recursion.lean` (§8). `deriving instance BEq for Shor.
{Gate,LowGate}` moved to `Reflect/Verify.lean` (needed there for the canary,
and `Tests.lean` gets them back transitively via `Symbolic.Bundle`).

`--w-max`'s default rose from 32 to 64 (covers `template`'s own checked
width `4 * k` for `k` up to 16 without the caller having to raise it);
`buildTemplateDoc` refuses if `wMax < 4 * k` for the requested `k`.

**Two real bugs surfaced by actually running the CLI** (not caught by
`Tests.lean`'s `native_decide` suite, since neither can happen inside a
proof):

1. `Reflect.Driver.runExtract`'s `Core.Context` had no `maxHeartbeats`
   override. `Tests.lean`'s `extract_ir_doc` calls for the heavier targets
   (`shor_gate`/`shor`) needed `set_option maxHeartbeats 4000000` at *build*
   time — but that `set_option` is local to the command elaborator's
   context and never reaches `runExtract`'s own, separately-constructed
   `Core.Context`. At run time this hit Lean's plain default (200000) and
   failed with a deterministic `whnf` timeout on every `template`/`bundle`
   invocation, unconditionally — this was latent since R2.6 added the first
   target expensive enough to need the bump, just never exercised at run
   time until now. Fixed: `maxHeartbeats := 0` (unlimited) in that
   `Core.Context` — a run-time request can be any `k`, so there is no
   single finite bound to pick the way `Tests.lean` picks one per pinned
   target.
2. `Reflect.Verify.coeffDispatch` took `src` and used `tableInstance src k
   hk`'s own points — for `.generate`, this disagreed with the real term:
   `standardSignedPhaseLoweringPlan`/`standardCSignedPhaseLoweringPlan`/
   `standardQFTLoweringPlan` hardcode `genInterpolationPoints k` (§6.9's
   finding again) regardless of the `ops` they're handed, so the canary's
   `coeff` oracle must too. `forshor_emit template 2 --table generate`
   failed with `instantiate disagrees with the real term` until fixed.
   `coeffDispatch` now always resolves `.standard`'s points, independent of
   `src` (documented in its own doc comment, pointing back to §6.9).

Both were caught by actually running `lake exe forshor_emit template …`
(the deliverable checklist's own commands), not by the build — a reminder
that `native_decide`-testable code and `IO`-only code need different kinds
of verification.

## 8. R4 — removals and README

Delete in the step that makes each redundant:

| removed | replaced by | step |
|---|---|---|
| `Symbolic/Template.lean` | extracted `Doc` | R2.6 |
| `Lower/Instantiate.lean` (one-level template check, `template_match`) | `IR/Instantiate.lean` full-depth check | R2.2 |
| `Symbolic/Recursion.lean` (E6 ladder, cost per level) | consumer derives from `nextWidth` table + resource model | R3 |
| `Table/Census.lean`, `schedule.census`, `resources_at_width` | counts fall out of the `Doc`; resource formulas are the repo's `shorGateResourceModel` | R3 |
| `affineTail` and its fields in `Width.lean`, `ShorPlan.lean` | none (advisory, one was spurious) | R3 |
| split-width columns of `qftPlanTable` | `qft` template | R3 |
| `meta.checks.template_match` in `pp`/`cpp`/`qft` | `meta.checks.instantiate_eq_real` | R2.2 |

README rewritten around three artifacts: extracted templates (the IR),
opaque value tables, reference instances; with the D-table from §1, the
trust statement from D7, and the R2 exit criteria as the test list.

### 8.1 R4 status: done

All seven rows of the removal table are done:

- `Symbolic/Template.lean`, `Symbolic/Recursion.lean`, `Table/Census.lean`
  deleted outright (`git rm`).
- `Lower/Instantiate.lean` deleted; the one piece of it still needed
  (`check1_annotatedEqFlat` and its helpers, `annotated_eq_flat` — nothing
  to do with the extracted `Doc`) moved into `Json/PlanJson.lean`; the rest
  (`check2_*`/`template_match`, `check3_*`/`ladder`/`split`) is gone,
  replaced by `instantiate_eq_real` (§7.1).
- `affineTail` deleted from `Symbolic/Width.lean` (which also lost its
  `widthTableByM`/`limbWidth` column — D4's opaque set is only `nextWidth`/
  `reserveNeed`, so that's all the width table carries now) and its
  `work_width_affine_tail` field deleted from `Symbolic/ShorPlan.lean`'s
  JSON (`shorPlanRowJson`).
- `qftPlanTable`'s split-width columns (`left`, `right`, `qftPhi`,
  `radixReverseCost`) dropped — only `qftWorkspaceNeed`'s two values remain
  (the `qft` template itself now prints the split-width formulas).
- `meta.checks.template_match` in `pp`/`cpp` replaced by
  `instantiate_eq_real` (§7.1); `qft` never had a `template_match` field,
  only `split` (`Lower/Instantiate.lean`'s QFT-specific check), which is
  dropped the same way (subsumed by `instantiate_eq_real`).
- README rewritten (top-level `Emit/README.md`, plus `Symbolic/README.md`,
  `Table/README.md`, `Lower/README.md`) around the three artifacts, the
  D-table, D7's trust statement, and the R2.1–R2.7 exit criteria as the
  test list.

A literal `grep -rn "Template.lean\|affineTail\|census\|template_match" Emit`
is **not** empty — this plan (§0, §1, §6, §7, this section) and several
`Lean` doc comments deliberately keep the deleted names in prose,
explaining what replaced them and why (deleting the historical trail along
with the mechanism would make the migration's own reasoning unrecoverable
later). What *is* true, checked directly: no `.lean` file imports
`Symbolic.Template`, `Symbolic.Recursion`, `Table.Census`, or
`Lower.Instantiate`; no code calls `affineTail`, `OpCensus`/`opCensus`, or
constructs a `template_match`/`ladder`/`split` field; `phaseProductTemplateJson`/
`qftTemplateJson`/`shorTemplateJson`/`recursionLevels`/`widthLadder` are
gone. The checklist item below is read as "no functional/code reference
remains", not "the string never appears in a comment or in this plan".

## 9. Risks and fallbacks

| risk | fallback |
|---|---|
| `WellFounded.fix` unfolds into `Acc.rec` noise | never unfold `fix`; use the generated `.eq_def` lemma via `simp only`, which shows the body with the recursive call by name |
| matchers (`match_1` helpers) on `Fin`/`Nat` do not reduce | `Split.simpMatch`, the matcher's `.eq_n` lemmas; a matcher stuck on a symbolic scrutinee becomes `cond` |
| `Finset.univ.sup` in `commonNeededWidth` does not reduce | keep `nextWidth` opaque (D4 default) |
| `Decidable` instances stuck on symbolic `n` inside `dite` | key on `dite` itself, read the `Prop`, ignore the instance |
| `Reg.append` proofs during instantiation | decide `Disjoint` with `if h : …`; refuse otherwise |
| environment load cost at run time (seconds, GBs) | `--no-template`; optional write-once cache of the `Doc` per `(k, src)` |
| a future refactor of ForShor uses a construct the table lacks | extraction fails loudly on the constant; add the construct, never special-case a table |

## 10. Deliverable checklist

- [x] `Emit/IR/{Syntax,Json,WellFormed,Instantiate}.lean` build.
- [x] `Emit/Reflect/{Quote,Extract,Targets,Driver}.lean` build.
- [x] R2.1–R2.7 exit criteria as `native_decide` in `Tests.lean`, all green (§6.1, §6.3, §6.4–6.5, §6.6, §6.7, §6.8, §6.9).
- [x] `forshor_emit template 2`, `template 3`, `template 2 --table generate` exit 0 with `instantiate_eq_real: true` (§7.1; verified by actually running all three).
- [x] `forshor_emit bundle 2` contains the extracted `template` and the trimmed tables; `--no-template` skips the load (verified: `bundle 2` has `template.checks.instantiate_eq_real: true` and the trimmed `width`/`qft_plan` rows; `bundle 2 --no-template` has no `template` key at all).
- [x] Old files and fields removed per §8 (§8.1); `grep -rn "Template.lean\|affineTail\|census\|template_match" Emit` is **not** empty by design — see §8.1's note on what "removed" means here (no code/import reference; the plan and doc comments keep the names in prose deliberately).
- [x] README rewritten (`Emit/README.md`, `Symbolic/README.md`, `Table/README.md`, `Lower/README.md`); `PLAN.md` statuses updated per step (§7.1, §8.1, this checklist).
- [x] Whole-project `lake build` (3305 jobs) and `lake build FastMultiplication.Emit.Tests` (3314 jobs) both succeed after all of the above.

## 11. R5 — the table is a `ShorLoweringSetup`, supplied through Lean

**status:** done — see §11.5

### 11.1 Why

R0–R4 made the extractor generic in the table: every `extract*Body` reads a
closed `ops : Prog k` and nothing downstream is keyed to which generator
produced it (D2). But the *interface* still says `TableSource.standard |
.generate`, so a user cannot hand the emitter a table of their own, and
`.generate` slips through even though the verified lowering does not cover
it: `StandardPhaseLoweringPlan` (`PhaseProduct/Lowering/Plan.lean:272`)
fixes the interpolation points to `genInterpolationPoints k`, and
`.generate`'s tables visit a different point set (`0, ∞, 1` at `k = 2`), so
the extracted IR is a faithful description of a circuit whose leaf
coefficients do not match the points its program evaluates — R2.7 shows
extractor fidelity for it, not circuit correctness.

The verified code already names the right interface. `referenceProgramAt`'s
first argument is a `Shor.ShorLoweringSetup` (`Shor/Spec/Setup.lean:21`):

```
k        : ℕ
hk       : 1 < k
ops      : Prog k
consumes : ProgConsumesPtsSafe (k := k) _ State.start_state ops (genInterpolationPoints k)
returns  : run? ops State.start_state = some State.start_state
```

Those two proof fields are exactly the properties every correctness theorem
on the chain requires of a table. A table that can be packaged as a
`ShorLoweringSetup` is, by definition, a table the theorems cover. So the
emitter's table input becomes that structure, and "any table" means "any
value of that type".

### 11.2 What changes

1. **Signatures.** `extractPhaseProductBody`, `extractCPhaseProductBody`,
   `extractQFTBody`, `extractShorBody` (`Reflect/Targets.lean`) and
   `extractPPBody` take `(setup : ShorLoweringSetup)` instead of `(k) (hk)
   (src : TableSource)`, and read `setup.k`, `setup.hk`, `setup.ops`.
   `buildDoc` and `runExtract` (`Reflect/Driver.lean`) likewise.
   `extractShorGateBody` is table-independent and is unchanged.
   Extraction needs only `ops`; the proof fields are consumed by the
   concrete reference instance the checks compare against
   (`referenceProgramAt setup m inst`), which is where they were always
   needed.
2. **Build-time command.** `extract_ir_doc <id> <setupIdent>`: the second
   argument is the *name of a `ShorLoweringSetup` declaration* in scope,
   resolved with `resolveGlobalConstNoOverload` and evaluated with
   `evalExpr`/`Lean.Meta.evalExpr` to a value. The existing numeric and
   `(k, generate)` forms are removed; `Tests.lean`'s pins become
   `extract_ir_doc r2_2_doc k2Standard` with `def k2Standard :=
   standardLoweringSetup 2 (by decide)`.
3. **`TableSource` shrinks to a convenience.** `standard k` is
   `standardLoweringSetup k`. `.generate` is **removed** from the symbolic
   path: it has no `ShorLoweringSetup`, so it cannot be an input. If a
   demonstration of extractor genericity on a non-standard table is still
   wanted, it lives only in `Tests.lean` as a `Prog k` fed to
   `extractPhaseProductBody`'s ops-only core, clearly named as uncovered
   by the theorems — it never reaches `bundle`/`template`.
4. **Run-time CLI.** `template <k>` and `bundle <k>` keep working for the
   standard table (`standardLoweringSetup k` built at run time). There is
   deliberately **no** `--table file` option: a user table enters through a
   Lean file (item 5), where its proofs are checked by the kernel, not
   through a parser.
5. **User workflow.** The user writes, in any Lean file importing
   `FastMultiplication.Emit.Reflect.Driver`:

   ```lean
   def myTable : Shor.ShorLoweringSetup :=
     { k := 3, hk := by decide, ops := myOps
       consumes := by <decide / native_decide / a proof>
       returns := by native_decide }

   extract_ir_doc myDoc myTable
   #eval IO.println (Shor.IR.docJson myDoc).compress
   ```

   **Proof obligations, by hand or by tactic (owner decision).** The
   default is that the user proves `consumes` and `returns` by hand, as
   the standard table does generically in `k` (`genOpsWithProduct_*` in
   `Programs/WithProduct.lean`, by induction over the generator). For a
   *concrete* `k` and a *concrete* `ops`, both fields are decidable, and
   R5 provides the instances so that `by decide` / `by native_decide`
   closes them:

   - `returns : run? ops State.start_state = some State.start_state` is an
     equality of `Option (State k)` with `State k = Fin k → Fin k → ℤ`;
     Mathlib's `Fintype.decidablePiFintype` gives `DecidableEq` for
     functions out of `Fin k`, so this is already decidable. Kernel
     `decide` evaluates `run?` over `ℤ` arithmetic and may be slow for
     large tables; `native_decide` is the pragmatic route.
   - `consumes.consumes : ProgConsumesPts hk σ ops pts`
     (`Core/Language.lean:367`) is a structural recursion on `ops` whose
     existentials are uniquely determined by the data (`pts = pt :: tail`
     fixes `pt`/`tail`; `applyOp? σ op = some σ'` fixes `σ'`). R5 adds
     `instance : Decidable (ProgConsumesPts hk σ ops pts)` in `Emit/` by the
     same recursion: on `phaseProduct i`, match `pts` (`[]` → `isFalse`;
     `pt :: tail` → `decide (matchesAt_pointRow_state hk σ i pt = true)`
     and recurse); on any other op, match `applyOp? σ op` (`none` →
     `isFalse`; `some σ'` → recurse). Soundness and completeness are the
     definition read off constructor by constructor. This subsumes the
     Boolean checker `progConsumesPtsCheck` (`Table/Source.lean:73`), which
     can then be deleted or kept as the instance's `decide` reflection.
   - `consumes.safe_add : SafeProg ops` (`Core/Coverage.lean:17`) is stated
     as a `∀` over list decompositions `ops = pre ++ addScaled d s _ _ ::
     rest → d ≠ s`, which is not decidable by shape. R5 adds the lemma
     `SafeProg ops ↔ ops.all (fun op => match op with | .addScaled d s _ _
     => d ≠ s | _ => true)` (one direction via `List.mem_iff_append`, the
     other by `List.mem_append`/`List.mem_cons_self`) and a `Decidable`
     instance through it.

   With those in place the user's setup is
   `consumes := ⟨by decide, by decide⟩, returns := by native_decide`, or a
   one-word wrapper tactic `table_ok` that tries `decide` then
   `native_decide` on each field. None of this is required for the
   standard table, whose proofs already exist generically in `k`.

6. **Verify canary** (`Reflect/Verify.lean`): `verifyDoc` takes the
   `setup` and builds its reference instances from it, so the
   `shor_gate`/`shor` canary that §7.1 could only run for `.standard` now
   runs for every input table.

### 11.3 Exit criteria

- `extract_ir_doc r2_2_doc k2Standard` and every other pin in `Tests.lean`
  rebuild green with the setup-taking command; no `TableSource.generate`
  reaches `buildDoc`.
- A `Tests.lean` section defines a hand-written `ShorLoweringSetup` at
  `k = 2` whose `ops` differ from `standardLoweringSetup 2` but still
  consume `genInterpolationPoints 2` in order (e.g. the standard ops with a
  redundant `shiftL`/`shiftR` pair inserted), discharges both proof fields
  by `decide`/`native_decide` using the new instance, extracts it, and
  `native_decide`s `instantiate` against `lowerSignedPhaseProdWithWorkspace`
  for that `ops` at `n = 16`. This is the "any table the theorems cover"
  test.
- `lake exe forshor_emit template 2` still prints the standard-table `Doc`;
  `--table generate` is rejected with exit 2 and a message pointing at this
  section.
- README's "The table" section rewritten: the interface is
  `ShorLoweringSetup`; `standard` is an instance of it; `generate` is
  described as a table the theorems do not cover and is no longer an
  emitter input.

### 11.4 Not in scope

Point sets other than `genInterpolationPoints k`. `PhaseLoweringPlan` is
generic in `pts`, but `StandardPhaseLoweringPlan`,
`lowerSignedPhaseProdWithWorkspace`, and `ShorLoweringSetup.consumes` fix
them. Lifting that is a change inside `ShorVerification/` with its own
correctness obligation, outside this folder's remit (ground rule 1).

### 11.5 R5 status: done

All six points of §11.2 are implemented, in the same file set §11.1
predicted, plus one new file (`Table/Decide.lean`, §11.2 point 5):

1. **Signatures.** `extractPPBody`/`extractPhaseProductBody`/
   `extractCPhaseProductBody`/`extractQFTBody`/`extractShorBody`
   (`Reflect/Targets.lean`) now take `(setup : Shor.ShorLoweringSetup)`;
   each body's first two lines became `let k := setup.k; let ops :=
   setup.ops` (`extractShorBody` doesn't need `k` at all, only `ops`, so it
   skips the first). `hk` dropped out of every one of them entirely — it
   was only ever used to call `Shor.tableInstance src k hk`, never
   reflected into an `Expr` directly (`hkE` is separately rebuilt via
   `mkDecideProof`), so once `ops` comes from `setup.ops` there was nothing
   left needing the real proof term. `buildDoc`/`Reflect/Driver.lean`
   likewise takes `setup` and threads it through unchanged.
2. **Build-time command.** `extract_ir_doc <id> <setupIdent>`:
   `setupIdent` is resolved with `resolveGlobalConstNoOverload` and read out
   to a value with `Lean.Meta.evalExpr` — `unsafe`, since `evalExpr`
   compiles and runs the constant exactly like `native_decide` does. The
   numeric and `(k, generate)` forms are gone. One wrinkle not anticipated
   in §11.2: `elab "..." : command => ...` does not accept an `unsafe`
   modifier directly ("unexpected token 'elab'; expected 'lemma'" — Lean's
   `elab` syntax has no unsafe variant). Fixed the same way Aesop's own
   config elaborators do it (`Aesop/Frontend/Tactic.lean`'s `elabOptions`):
   the real logic is a separate `unsafe def elabExtractIrDocImpl`, and the
   `elab` command calls it through the term-level `unsafe <expr>` escape
   (`elab "extract_ir_doc " id:ident setupIdent:ident : command => unsafe
   elabExtractIrDocImpl id setupIdent`) — this is the sanctioned way to
   call an `unsafe` function from a declaration that must stay safely
   typed, not a new pattern invented here.
3. **`TableSource` shrinks to a convenience.** Unchanged code-wise from R3
   (`Table/Source.lean` still has both constructors) — the shrinkage is
   that `.generate` is no longer *reachable* from extraction: `Reflect/*`
   never sees a `TableSource` at all anymore, only `ShorLoweringSetup`
   values, and `Main.lean`/`Symbolic/Bundle.lean` refuse `.generate`
   explicitly before it could reach `buildDoc`. `TableSource` remains
   exactly what it was for the *value tables* (`bundle`'s pure sections),
   which never claimed extraction fidelity and so have nothing to lose by
   still accepting `.generate`.
4. **Run-time CLI.** `runExtract`/`runExtractAndVerify` (`Reflect/
   Driver.lean`/`Reflect/Verify.lean`) dropped their `src` parameter
   entirely — standard table only, built via a plain (non-reflected)
   `standardLoweringSetup k h` call, exactly as before R5 just one level
   up. `Main.lean`'s old `extract_ir <k>` command (superseded by `template
   <k>` since R3, per its own doc comment, but never actually deleted) was
   deleted now — ground rule 3.
5. **Proof obligations.** `Table/Decide.lean` (new): `Decidable
   (ProgConsumesPts hk σ ops pts)` built term-mode, mirroring
   `ProgConsumesPts`'s own recursion on `ops` constructor by constructor —
   `phaseProduct i`'s existential witness is `pts`'s own head, every other
   op's is whatever `applyOp?` computes. One thing the plan's sketch didn't
   flag: `ProgConsumesPts` is a `def`, not an `inductive`, so its internal
   `match op with …` is *stuck* (does not reduce, even to decide which
   existential shape applies) whenever `op` is an abstract bound variable
   rather than a literal constructor — an OR-pattern arm (`| .shiftL .. |
   .shiftR .. | .negate _ | .addScaled .. =>`) sharing one proof body hits
   this immediately (the shared body's own nested `match h : applyOp? …`
   leaves `op` abstract in `h`'s type while the surrounding goal has
   already substituted the concrete constructor, a mismatch Lean reports
   as an `Application type mismatch`), and so does a plain wildcard `| _ =>`
   arm (the anonymous-constructor proof needs `ProgConsumesPts` to have
   already reduced to an `Exists`, which needs `op` concrete). Fixed by
   matching each of `shiftL`/`shiftR`/`negate`/`addScaled` in its own
   arm (four literal patterns, no `|`, no wildcard) and factoring the
   identical proof body into `decideProgConsumesPtsOther`, called once per
   arm with an `Iff.rfl` that only typechecks *because* `op` is concrete at
   each call site. `SafeProg`'s decidability went through cleanly as
   originally sketched: `safeProgCheck` (a `List.all` scan) plus
   `safeProg_iff_check` (`List.mem_iff_append` one way,
   `List.mem_append_right`/`List.mem_cons_self` the other) via
   `decidable_of_iff`. `decidableProgConsumesPtsSafe` bundles both so
   `consumes := by native_decide` (or `by decide` for small tables) closes
   the whole `ProgConsumesPtsSafe` field in one line, matching §11.2's own
   worked example. Verified directly (not just by the exit criterion
   below): a standalone smoke test discharged both `ProgConsumesPts`/
   `SafeProg` for the real standard `k = 2` table via `native_decide` using
   only these instances.
6. **Verify canary.** `Reflect/Verify.lean`'s `opaqueDispatch`/
   `phaseProductAgrees`/`cPhaseProductAgrees`/`qftAgrees` now take `ops`
   (or `(hk, ops)`) directly instead of `(k, hk, src)` — used both by the
   canary (`checkPhaseProduct`/etc., unpacking `setup.k`/`setup.ops`) and
   by `pp`/`cpp`/`qft`'s own `instantiate_eq_real` check
   (`Lower/PhaseProduct.lean`/`Lower/Qft.lean`, passing their own `ops`
   directly, no `TableSource` involved at all anymore on that path).
   `checkShorGate`/`checkShor`/`shorEnv` take `setup` directly —
   `Reference.referenceShorCircuit` already took a whole `ShorLoweringSetup`
   even before R5, so this simplified rather than complicated. `verifyDoc`
   now always runs all five checks unconditionally (no more `match src
   with | .standard => … | .generate => pure ()`): every `setup` reaching
   it is, by construction, one the reference-instance machinery is proven
   to work over.

**§11.3's exit criteria, all met:**

- Every `extract_ir_doc` pin in `Tests.lean` rebuilds green with the
  setup-taking command (`smallLowering`/`k3Lowering` — both already
  existed in `Tests.lean` from R2 as plain `ShorLoweringSetup` values, so
  no new "k2Standard"-style constant was needed); no `TableSource.generate`
  reaches `buildDoc` anywhere.
- `R2_7_PhaseProduct_CustomTable`/`R2_7_Qft_CustomTable` (replacing
  `R2_7_PhaseProduct_K2Generate`/`R2_7_Qft_K2Generate`) define
  `r2_7c_ops : Prog 2 := (standardLoweringSetup 2 _).ops ++ [shiftL i 0,
  shiftR i 0]` (a redundant, semantically-inert pair — shift-by-`0` is the
  identity and `shiftRReg?` never fails at `n = 0` — appended after the
  standard ops, so `ops`'s *list structure* differs from the standard
  table's own while what it consumes/returns to does not), packages it as
  `r2_7c_setup : ShorLoweringSetup` with `consumes := by native_decide` /
  `returns := by native_decide`, extracts it with one `extract_ir_doc`
  (both `phase_product` and `qft` land in the same `Doc`, so the QFT half
  reuses it rather than re-extracting), and `native_decide`s `instantiate`
  against `lowerSignedPhaseProdWithWorkspace`/`lowerQFT` for that `ops` at
  `n = 16`/`w = 4`. All pass.
- `lake exe forshor_emit template 2` still prints the standard-table `Doc`
  (verified directly); `--table generate` is rejected with exit 2 pointing
  at this section, for both `template` and `bundle` (without
  `--no-template`) — verified directly by running all three.
- `Emit/README.md`'s "Decisions" (D5), `Table/README.md`'s "The table"
  section, and a new "Using a custom table" section in `Emit/README.md`
  rewritten around the `ShorLoweringSetup` interface.

Whole-project `lake build` (3305 jobs) and `lake build FastMultiplication.
Emit.Tests` (3315 jobs) both succeed; `lake exe forshor_emit` re-verified
for `template 2`, `template 2 --table generate` (exit 2),
`bundle 2 --table generate` (exit 2), `bundle 2 --table generate
--no-template` (exit 0, no `template` key).

## 12. R6 — a correctness theorem for every extracted `Doc`

**status:** in progress — prerequisite done (§12.0), R6.1 next

### 12.0 Prerequisite (discovered, not in the original plan): `evalW`/`evalReg`/`evalNode`/`evalNodeGate` must not be `partial`

§12.6's own "Fuel" risk says `instantiate` is "`partial`-free only because
of" the `fuel` parameter — true *conceptually* (the fuel argument is what
makes the recursion actually terminate), but the literal code in
`IR/Instantiate.lean` still declared `evalW`, `evalA`, `evalReg`, `evalNode`,
`evalNodeGate` with the `partial` keyword (left over from an earlier draft,
predating fuel, never revisited). Checked directly, before writing a single
R6 lemma: `simp [evalW]`, `unfold evalW`, and `rfl` all fail to make *any*
progress on a `partial def` in this toolchain — no `.eq_1`-style lemma
exists at all. `partial def` compiles via an opaque fixpoint outside the
normal termination-proof/equation-lemma machinery (the same machinery that
gives every `.eq_1` this plan's earlier R2 sections already relied on, e.g.
`standardSignedPhaseLoweringPlan.eq_1`) — it is simply a different, harder
kind of "not proved terminating" than ordinary well-founded recursion, and
every one of R6.2's `simp [evalW]`/`simp [evalProp, evalW]` proof sketches
is impossible against it. This blocks R6 entirely until fixed, is not
mentioned anywhere in §12.1–§12.6, and had to be found and fixed before any
of R6.1 could start.

Fixed in `IR/Instantiate.lean`, confirmed by rebuilding `forshor_emit` and
`EmitTests` (all R2.1–R2.7 `native_decide` checks, which exercise these
functions pervasively, still pass unchanged) plus a direct CLI check
(`template 2` still exits 0 with both checks `true`):

- `evalW`: restructured as a `mutual` block with a new `evalWList`
  (mirrors `Reflect/Driver.lean`'s own `wexprToExpr`/`wexprListToExpr`
  shape, added for the same reason in R1) — the only reason it was
  `partial` was the nested `List WExpr` recursion in `.opaque`'s arguments,
  which Lean's ordinary structural-recursion compiler handles fine once
  it's phrased as an explicit paired list-recursion instead of
  `args.mapM (evalW env)` needing to see through `List.mapM`.
- `evalA`, `evalReg`: just dropped `partial` — neither `AExpr` nor
  `RegExpr` has a `List Self` field, so both were already ordinary
  structural recursion; `partial` was unnecessary caution (`evalReg`'s own
  old doc comment said as much: "no nested `List RegExpr` occurs, but this
  mutually threads through `evalW`, which is" — calling a function that
  used to be opaque does not itself require the caller to be `partial`).
- `evalNode`/`evalNodeGate`: the one genuinely non-structural case. Every
  constructor but `.call` recurses on a strictly smaller `Node` at the
  *same* `fuel`; `.call` recurses on an unrelated (possibly larger) `Node`
  (`t.body`, from `d.templates`) at strictly smaller `fuel`. Named the
  `Node` parameter explicitly (`termination_by` needs a name to refer to)
  and gave the lexicographic measure `termination_by (fuel, sizeOf node)`,
  with an explicit `decreasing_by` (`Prod.Lex.left _ _ (by omega)` for the
  `.call` case, `Prod.Lex.right _ (by omega)` for the structural cases,
  `List.sizeOf_lt_of_mem` for `.seq`'s `body.mapM` case) — Lean's own
  default termination heuristics do not find this measure unaided.

### 12.1 What is proved, and what is not

Two claims must not be confused:

- *Claim A* — the extractor program (`Reflect/Extract.lean`) is correct for
  every input. Not attempted. It is a statement about `MetaM` code over
  `Expr` and the semantics of `whnfR`/`unfoldDefinition?`/`isDefEq`; no one
  proves this for tactics or `simp` either. The extractor stays trusted.
- *Claim B* — **each extracted `Doc`**, a closed Lean constant pinned by
  `extract_ir_doc` for one `(k, table)`, denotes the verified circuit for
  **all** widths. This is R6. Both sides of the equation are ordinary
  computable definitions over the same `ops`; no metaprogramming appears in
  the statement. It is the standard translation-validation pattern: verify
  every output, not the translator. A bug in the extractor shows up as a
  theorem that does not close, and the extraction is rejected.

D7 is amended accordingly: for a `Doc` that carries its R6 theorem, the
trust statement is "proved for all widths, per table"; the instance checks
of R2/§7.1 remain as a fast smoke test and as the check that the *Python*
consumer's interpreter agrees with Lean's.

### 12.2 Statements

With `env` binding each `wParam` to the real width/capacity (`xw ↦
x.width`, `xCap ↦ x.capacity`, …), each `rParam` to the real register, each
`aParam` to the real angle, and the opaque functions to the real Lean
functions (`RecursivePhaseWorkspace.nextWidth ops`, `reserveNeed ops`,
`qftWorkspaceNeed ops`, `cramerCoeffFromPtsWidth k _ pts hpts`, `Nat.log2`,
`step5Constant`, …), exactly as `Reflect/Verify.lean` already builds it:

```lean
theorem <doc>_phase_product_correct
    (x z : ExtReg) (phi : Angle) (h : SignedRecursiveWorkspaceOK ops x z)
    (fuel : ℕ) (hfuel : phaseInputSize x z < fuel) :
    IR.instantiate <doc> "phase_product" (ppEnv x z phi) fuel
      = .ok (lowerGateRec (standardSignedPhaseLoweringPlan k hk phi x z ops h))

theorem <doc>_cphase_product_correct   -- same, controlled
theorem <doc>_qft_correct
    (r : ExtReg) (h : QFTReserveOK ops r) (fuel) (hfuel : regSize r.active < fuel) :
    IR.instantiate <doc> "qft" (qftEnv r) fuel = .ok (lowerQFT k hk ops r h)
theorem <doc>_shor_gate_correct
    (a N : ℕ) (x y work scratch : ExtReg) (flag : ℕ) (hws) (hstep4) (fuel) (hfuel) :
    IR.instantiateGate <doc> "shor_gate" (shorEnv …) fuel
      = .ok (orderFindingApprox a N x y work scratch flag hws hstep4)
theorem <doc>_shor_correct
    … = .ok (lowerGate k hk ops (orderFindingApprox …) hlower)
```

Composition with the verified tree: `<doc>_shor_correct` at
`allocateReferenceLayout ops inst m`'s registers gives `instantiate … =
.ok (referenceShorCircuit lowering inst m)`, to which `Shor.Shor_correct`
applies at `m = referenceChosenPrecision N`.

### 12.3 Proof structure (phase product; the others follow it)

Well-founded induction on `phaseInputSize x z`, the plan's own measure.

1. Rewrite the right side with `standardSignedPhaseLoweringPlan.eq_1`; both
   sides are now an `if nextSignedWidth x z ops < phaseInputSize x z`.
2. Unfold `instantiate`/`evalNode` on the concrete `Doc` body: the top node
   is `cond guard then else`; `evalProp env guard = decide (nextWidth … <
   max …)` by `simp [evalProp, evalW]`, matching the real guard.
3. *Base branch*: `evalNode` of `call "naive_leaf" …` equals
   `Naive_SignedPhaseProd phi x z`. One lemma, `evalNode_naive_leaf`:
   the nested `loop i < xw, loop j < zw, CPhase …` fold equals
   `LowGate.sequence (naiveSignedPhaseGates phi x z)`, i.e. the double
   loop equals `flatMap`/`map` over `signedTerms`, with `evalA
   (signedPair …) = signedPairAngle …` and `evalReg (qubit x i) =
   x.active.get i`.
4. *Recursive branch*: the body is a fixed `seq` of nodes, so the goal
   splits node by node against `lowerGateRec` of `planCompiledSignedPhaseGate
   … step.layout` (which itself unfolds to `compileSignedAllocations ;;
   compileAnnotatedOps… ;; compileSignedDeallocations`). Per-node lemmas:
   - `evalW` of each extracted width tree equals the real expression
     (`min (xw/2) (zw/2)` for `phaseLimbWidth`, `nextWidth − slotWidth i`
     for `extraDelta`, …): `simp [evalW]` after unfolding the real side.
   - `evalReg` of `ext(x.active[i·m : i·m+w_i], x.reserve[off_i : off_i +
     req_i])` equals `layout.xSplit.child i`, and `evalReg (grow … δ)` equals
     `growExtRegTo (child i) W'`. This is the substantive part: the real
     child registers are `PhaseSplitLayout.ofBudget`'s `Reg.take`/`Reg.drop`
     /`Reg.append` with `ReserveBudget.offset` as the reserve offset; the
     lemmas show `evalReg`'s slices compute the same lists and that its `if
     h : Disjoint …` takes the `then` branch, using the layout's own
     disjointness proofs (`PhaseSplitLayout`'s fields).
   - `evalA (coeff phi l m) = phi * loweringPhaseCoeff k x z pts hpts l` by
     `Env.coeff`'s definition and `phaseLimbWidth`.
   - each `call "phase_product" …` node: `Env.call` yields exactly the
     child's environment (`ppEnv (child i x) (child i z) (phi * c_l)`), and
     the induction hypothesis applies because `step.childInputSize i` gives
     `phaseInputSize (child i) (child i) = nextSignedWidth x z ops <
     phaseInputSize x z`; `hfuel` decreases in step.
   - the `cond ((W' − w_i) = 0) id (zeroExtend …)` allocation nodes match
     `allocChunkGate`'s own `if extraDelta = 0 then id else …`.
5. `seq` bracketing: `evalNode (.seq …)` right-folds with `LowGate.seq`;
   the real term's bracketing differs, so the statement is up to
   `LowGate.flattenSeq`, or the fold lemma is stated to match
   `compileSignedAllocationsAux`'s nesting exactly. Decide once; the
   existing `check1_annotatedEqFlat` convention (compare flattened) is the
   pragmatic choice and is what `instantiate_eq_real` already does.

`qft`: induction on `regSize r`, `standardQFTLoweringPlan.eq_1`, the
`phase_product` theorem for the twiddle. `shor_gate`: no recursion; the
`loop` over exponent bits against `modExpApproxStepsValid`'s list recursion
(one lemma: `evalNode (.loop e 0 xW body)` equals the fold over `x.qubits`
with `e` as position). `shor`: `shor_gate` plus the three `call` theorems
through `translateLowerGate`'s cases of `lowerGate`.

### 12.4 Generating the proof with the `Doc`

The proof has the same shape for every table; only the number of body
nodes changes. So `extract_ir_doc` grows a sibling: `extract_ir_doc! <id>
<setup>` emits both `def <id> : Doc` **and** `theorem <id>_phase_product_correct
…` (etc.), where the tactic script is assembled from the extracted
structure and calls a fixed lemma library in `Emit/Proofs/Correct.lean`
(`evalW_*`, `evalReg_slice_child`, `evalReg_grow`, `evalA_coeff`,
`evalNode_naive_leaf`, `evalNode_loop_modExp`, `Env_call_child`). If the
generated proof fails to elaborate, the extraction is rejected — the
theorem is the acceptance test. A hand-written proof for the `k = 2`
standard `Doc` comes first (§12.5 step 1), then the script generator is
built from it.

### 12.5 Staging and exit criteria

**Placement (owner decision).** Every R6 proof lives under `Emit/Proofs/`,
nothing else does, and nothing under `Emit/` outside that folder states a
theorem: `Proofs/Correct.lean` (the lemma library), `Proofs/PhaseProduct.lean`,
`Proofs/Qft.lean`, `Proofs/Shor.lean` (the hand-written per-template
theorems of R6.2–R6.4, each about the pinned `Doc`s from `Tests.lean`/
`Driver.lean`), and `Proofs/Generated.lean` (the output of `extract_ir_doc!`,
R6.5; regenerated, never hand-edited). A `lean_lib EmitProofs` rooted at
`FastMultiplication.Emit.Proofs.Shor` (which imports the rest) is added to
`lakefile.lean` so `lake build EmitProofs` checks them; `Main.lean` does not
import `Proofs/`, so the executable neither needs nor waits for them. The
two existing small proof files stay where they are because they are not R6
theorems but decidability instances the emitter runs
(`Lower/Decide.lean`, `Table/Decide.lean`).


| step | deliverable | exit criterion |
|---|---|---|
| R6.1 | `Proofs/Correct.lean`: lemma library for `evalW`, `evalReg` slices/`grow`/`ext`, `evalA`, `Env.call`, `evalNode` on `seq`/`cond`/`loop` | lemmas build; used in R6.2 |
| R6.2 | hand-written `r2_2_doc_phase_product_correct` (k = 2 standard) | theorem closes; `#print axioms` shows no `sorryAx`, and no `Lean.ofReduceBool` (i.e. no `native_decide` inside the proof) |
| R6.3 | `r2_4_doc_cphase_product_correct`, `r2_5_doc_qft_correct` | same |
| R6.4 | `shor_gate` and `shor` theorems for the k = 2 standard `Doc` | same; plus the corollary `instantiate … = .ok (referenceShorCircuit …)` |
| R6.5 | proof-script generator in `extract_ir_doc!`; regenerate all of the above from it | generated proofs close for k = 2 and k = 3 standard with no per-k edits |
| R6.6 | D7/README/provenance updated: `template.provenance` says "proved for all widths (R6)" when the theorem exists for that `Doc` | text matches what is proved |

### 12.6 Risks

- **Register lemmas.** `Reg.append` carries `Disjoint` proofs and
  `ReserveBudget.offset` is a prefix sum; showing `evalReg`'s slices are
  definitionally the layout's children may need `Reg` extensionality
  (`Reg.qubits` equality suffices, proofs are irrelevant) and a small
  `offset` arithmetic lemma. Budget the most time here.
- **Term size.** The concrete `Doc` body has thousands of constructors;
  `simp` over `evalNode` on it must be driven node by node (a custom
  `simp` set plus `rfl` for the structural steps), not by one global
  `simp`, or elaboration time explodes.
- **Brittleness.** Cosmetic changes in the extractor's output (e.g.
  simplifying `0 * m`) change the `Doc` and thus the theorem's left side;
  the generated script must be re-run, which is the intended workflow, but
  the hand-written R6.2 proof will need updating if the extractor changes
  before R6.5 exists.
- **Bracketing.** If the `seq` nesting of `evalNode` and of the real term
  differ, state the theorem up to `flattenSeq`; do not fight the fold.
- **Fuel.** State with an explicit `fuel` and `hfuel`; do not try to remove
  it, `instantiate` is `partial`-free only because of it.
