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

**status:** R6.3 is now fully **done** — prerequisites done (§12.0, §12.0b).
R6.1 (`Proofs/Correct.lean`, `evalNode_naive_leaf`/`evalNode_naive_cleaf`) and
R6.2 (`Proofs/PhaseProduct.lean`, `evalNode_phase_product_correct`) are
**done**, no `sorry`. R6.3's `cphase_product` half (`Proofs/CPhaseProduct.lean`,
`evalNode_cphase_product_correct`/`r2_4_doc_cphase_product_correct`, §12.7)
and its `qft` half (`Proofs/Qft.lean`, `evalNode_qft_correct`/
`r2_5_doc_qft_correct`, §12.8 below) are both **done**, no `sorry`,
`#print axioms` clean on every closed theorem. R6.4's `shor_gate` half is now
**done**: `evalNodeGate_shor_gate` (§12.9–§12.11), the full Gate-level
correctness theorem for `orderFindingApprox`, closes with no `sorry`,
`#print axioms` clean. R6.4's `shor` half (the `LowGate`-level theorem
composing `qft`/`phase_product`/`cphase_product` through
`translateLowerGate`) is **in progress — all 3 needed leaf theorems closed,
top-level assembly not started** (§12.12–§12.16): the full 14-`Node.call`
body is ground-truthed; `evalNode_dind` (doc-independence) and `evalNode_ind`
(the combined doc-*and*-env/opaqueW-independence bridge letting R6.2/R6.3's
theorems be reused as black boxes at `shor`'s `.call` sites) are both proved
and merged, no `sorry`, `#print axioms` clean; the hybrid-env leaf-assembly
technique they unlock is now validated end-to-end and is generic *per
template name* (one theorem covers every call site using that name, not one
per site — a count correction made in §12.15): `evalNode_call_cphase_product`
(§12.14, covers both `cphase_product` sites), `evalNode_call_phase_product`
(§12.15, covers all 3 `phase_product` sites), and `evalNode_call_qft`
(§12.16, covers all 9 `qft` sites) are all three merged into
`Proofs/Shor.lean`, no `sorry`, no `native_decide`, `#print axioms` clean —
`shor`'s leaf-lemma-engineering phase is **done**. Step 3 (`CmpGeConst`/
`CSubConst`) is now also **done** (§12.17–§12.18): `LowGate.flattenSeqAdj`
(a required new adjoint-recursing equality notion — `LowGate.flattenSeq`'s
own `.adj g => [g]` doesn't recurse the way `Gate.flattenSeq`'s does, a
genuine gap discovered this round, not merely an inconvenience) and the
bit-copy loop lemma (a new `Nat.bitIndices`-vs-loop combinatorial
correspondence) came first (§12.17), then the full composite-circuit
assembly — `evalNode_lowerPrepareNegConst`/`_lowerPrepFromFlag`/`_diffCmp`/
`_lowerCmpGeConst`/`_lowerCSubConst`/`_lowerStep3` — closed on top of it
(§12.18), generic over register/weight expressions like the three `.call`-site
theorems. No `sorry`, no `native_decide`, `#print axioms` clean throughout.
What remains for `shor`: the `modExpApproxValid` loop-body assembly and the
top-level `H_reg`/`initY1`/loop/`IQFT` assembly — wiring every leaf/Step-3
theorem's generic parameters to `r2_6_env`'s actual variable lookups at each
concrete site, plus the `flattenSeq`/`flattenSeqAdj` bridge lemma §12.17
flagged for combining Step 3/4/IQFT's adjoint-aware results with Steps
1/2/5's plain-`.flattenSeq` ones — not started. R6.5 (the proof-script
generator) is not started.

### 12.7 R6.3 (`cphase_product`) status: done

`Proofs/CPhaseProduct.lean` proves `evalNode_cphase_product_correct` (the
`cphase_product` analogue of R6.2's `evalNode_phase_product_correct`) and the
`IR.instantiate`-level wrapper `r2_4_doc_cphase_product_correct`, both closed,
no `sorry`, `#print axioms` clean (`propext`/`Classical.choice`/`Quot.sound`
only). `lake build EmitProofs` and `lake build forshor_emit EmitTests` are
green.

The key discovery that made this tractable, beyond what §12.2's header
comment already anticipated (`cphase_product`'s reserve-split bookkeeping is
identical to `phase_product`'s, since `precomputePhaseProductSlots` never
looks at `ctrl`): **`r2_4_ops` (R2.4's table) and `r2_2_ops` (R2.2's table)
are not just equal in value, they are *definitionally* equal** —
`r2_4_hk`/`r2_2_hk` are both `by decide`-generated proofs of the same `1 < 2`
proposition, and Lean 4's definitional proof irrelevance makes any two
proofs of a `Prop` defeq, so `(tableInstance .standard 2 r2_4_hk).ops` and
`(tableInstance .standard 2 r2_2_hk).ops` are the same term up to
reducibility (`r2_4_ops_eq_r2_2_ops : r2_4_ops = r2_2_ops := rfl`). Confirmed
empirically before committing to the approach: a lemma stated and proved
entirely in terms of `r2_2_ops` (e.g. `requiredXChildReserve_fits`,
`child_capacity_0x`) applies *directly*, via ordinary term elaboration and
defeq, to a goal stated in terms of `r2_4_ops` — no bridging rewrite needed
at the call site. Consequence: every lemma in `PhaseProduct.lean` that is
about `canonicalSignedStep`'s layout/`growExtRegTo`/capacities *and does not
mention `ppEnv`* (`nextWidth_eq_nextSignedWidth`, `child_width_0`/`_1`,
`PhaseSplitLayout.child_capacity`, `ExtReg.capacity_grow`,
`requiredXChildReserve_fits`/`requiredZChildReserve_fits`,
`child_capacity_0x`/`_0z`, `capacity_grow0x`/`_0z`, `width_grow0x`/`_0z`/`_1x`/`_1z`,
`extraDelta_grow0x`/`_0z`/`_1x`/`_1z`, the cast-erasure tools `eqmp_heq`/
`lowerGateRec_heq`/`lowerGateRec_eqmp_final`/`lowerGateRec_heq_gate`/
`lowerGateRec_planAllocChunkGate`/`lowerGateRec_planDeallocChunkGate`/
`lowerGateRec_planCompileSignedAllocations_2`/`_Deallocations_2`, and even
`r2_2_ops_eq`/`r2_2_annotatedOps_eq` themselves) is reused **directly**, with
zero restatement, for `cphase_product`. A further ground-truth check
(`Node.opRegsByName` applied to `r2_4_cppThen`) confirmed the extractor
produces *byte-identical* register/allocation/deallocation subterms for
`phase_product` and `cphase_product` (`r2_4_ext0x = r2_2_ext0x` by `rfl`,
`r2_4_ppAlloc = r2_2_ppAlloc` by `rfl`, `r2_4_ppDealloc = r2_2_ppDealloc` by
`rfl`) — only the 12-leaf annotated-ops body differs, and only by one extra
`.var "ctrl"` prepended to each of the three recursive `.call
"cphase_product"` leaves' `rArgs` (`r2_4_ppBodyNode_eq`, `rfl`).

What genuinely needed new proof (not reuse): every `Env`-dependent fact,
since `cppEnv ≠ ppEnv` as terms (the extra `"ctrl"` arm in `cppEnv`'s `r`
field) even though they agree at every name `cppEnv`'s register-slicing
subexpressions actually reference — `evalW_cpp_nextWidth`/`_limbW`/
`_reserveNeedX`/`_reserveNeedZ`/`_growDeltaX0`/`_growDeltaZ0`/`_growDeltaX1`/
`_growDeltaZ1`, `evalA_cpp_coeff`, `evalReg_cpp_ext0x`/`_0z`/`_1x`/`_1z`,
`evalReg_cpp_grow0x`/`_0z`/`_1x`/`_1z`, `evalNode_cpp_cond0x`/`_0z`/`_1x`/`_1z`,
`evalNode_cpp_dealloc0x`/`_0z`/`_1x`/`_1z`, `evalNode_cpp_AS`,
`evalNode_cpp_alloc`/`_dealloc` — each a near-mechanical copy of
`PhaseProduct.lean`'s `ppEnv`-based counterpart, `unfold cppEnv` in place of
`unfold ppEnv`. One real pitfall hit repeatedly this way: a `have h :=
r2_2_named_lemma x z ... hrec hworkspace` applied at `r2_4_ops`-typed
`hrec`/`hworkspace` type-checks fine (by the defeq argument above) but the
resulting `h`'s *displayed/stored* type still literally mentions
`r2_2_hk`/`r2_2_ops` (Lean does not rewrite the borrowed lemma's conclusion
to use the caller's terms) — so a later `simp only [..., h, ...]` silently
fails to rewrite anything, since `simp`'s matcher requires syntactic (not
merely defeq) agreement and does not unfold opaque `def`s like `r2_2_ops`/
`r2_4_ops` by default. Fix, applied wherever this bit (`extraDelta_grow0x`
etc. in the four `evalNode_cpp_cond*`/four `evalNode_cpp_dealloc*` proofs):
give the `have` an explicit type ascription spelled out in terms of the
caller's own names (`r2_4_hk`/`r2_4_ops`) rather than binding the bare
applied term — the ascription forces the defeq check at elaboration time and
the resulting hypothesis is then syntactically `r2_4`-shaped for later
`simp`/`rw` calls.

Two more new pieces, both in `envCall_cphase_product_eq`/`evalNode_cpp_call`:
(1) the extra `"ctrl"` case in the `Env.call`/`cppEnv` field-equality proof
(mirrors `envCall_naive_cleaf_eq`'s `ctrl` handling in `Correct.lean`, one
more `by_cases` layer); (2) nothing else — `ctrl` passes through every
recursive level *unchanged* (same physical qubit, no growth/slicing), so no
new width/capacity fact was needed for it at all.

The one genuinely new *obstacle* (not just new bookkeeping): unfolding
`planCompiledCSignedPhaseGate` (unlike `planCompiledSignedPhaseGate`) leaves
a real `Eq.mpr`-shaped `Gate`-index cast, because its tactic-mode body's
final `simpa` needs the extra `controlPhaseLeaves`/
`controlPhaseLeaves_compileSignedAllocations`/
`controlPhaseLeaves_compileSignedDeallocations` rewrites (`Lowering/
PlanBuilders.lean`) that `planCompiledSignedPhaseGate`'s simpler `simpa`
never needed — confirmed empirically (`unfold planCompiledCSignedPhaseGate;
dsimp only` exposes the cast directly, where the uncontrolled version's
`unfold` was already clean, per R6.2's "Third round" notes). Rather than
deriving a fresh fix, `GateCount/PhaseProduct/Lemmas.lean` turned out to
already have solved exactly this (for gate-counting purposes):
`lowerGateRec_mpr_gate_of_eq`, the `Eq.mpr` orientation of the same
`Subsingleton.elim`-based cast-erasure technique as `lowerGateRec_cast`/
`lowerGateRec_heq_gate`. Restated locally in `CPhaseProduct.lean` (same
proof) rather than importing the whole `GateCount` hierarchy into
`Emit/Proofs/`. With that, `rw [lowerGateRec_mpr_gate_of_eq (hUV := by simp
[compiledCSignedPhaseGate, compileOpsToCSignedGate, compileOpsToSignedGate,
controlPhaseLeaves, controlPhaseLeaves_compileSignedAllocations,
controlPhaseLeaves_compileSignedDeallocations])]` collapses the cast and the
rest of the induction's final `flattenSeq` assembly proceeds exactly like
R6.2's (`planCompileAnnotatedOpsToCSignedGateAux` unfolds via `simp only`
just like `planCompileAnnotatedOpsToSignedGateAux` did, `lowerGateRec_cSignedStep`/
`lowerGateRec_cSignedBase` — already-existing `@[simp]` equation lemmas,
symmetric to `lowerGateRec_signedStep`/`_signedBase` — replace the
uncontrolled pair).

The controlled workspace for the induction's recursive call is built the
same way `standardCSignedPhaseLoweringPlan`'s own recursive case builds it
(`Lowering/PlanBuilders.lean`): `Gate.PhaseProductLayout.controlDisjoint_of_ctrlDisjoint`
turns `hworkspace.control_disjoint : ExtReg.CtrlDisjoint ctrlIdx x z` into
`layout.ControlDisjoint ctrlIdx`, then `controlDisjoint_target` (`Compiler/
Workspace.lean`) shows growing every chunk to the target width preserves
that disjointness, giving `ExtReg.CtrlDisjoint ctrlIdx cX0 cZ0` for the
chunk-0 children the recursion actually uses — combined with the (already
generic, phase_product-derived) signed child workspace `hcw0` into a
`CSignedRecursiveWorkspaceOK` record literal for the induction hypothesis to
consume. No new facts about `controlDisjoint_target` itself were needed; it
was already proved, generally, for the real compiler.

`qft`'s R6 theorem (R2.5/R6.3's other half) is now also done — see §12.8.
R6.4 (`shor_gate`/`shor`) has its shared infrastructure done — see §12.9 —
but no leaf lemma yet. R6.5 (the proof-script generator) remains entirely
open.

### 12.8 R6.3 (`qft`) status: done

`Proofs/Qft.lean` proves `evalNode_qft_correct` and the `IR.instantiate`-level
`r2_5_doc_qft_correct` (§12.2's exact stated form, using a single `ExtReg r`
and `QFTReserveOK`), for `r2_5_doc` (k = 2, standard table, `Emit/Tests.lean`'s
R2.5 section). No `sorry` anywhere in the file; `#print axioms` on both
theorems shows only `propext`/`Classical.choice`/`Quot.sound`.

**Key finding, discovered before writing a single register-slicing lemma**:
`r2_5_doc = r2_2_doc`, `r2_5_ops = r2_2_ops`, and `r2_5_k = r2_2_k` all hold
by plain `rfl`. `extract_ir_doc <name> smallLowering` bundles *every* target
(`pp_body`, `phase_product`, `cphase_product`, `qft`, `shor_gate`, `shor`,
`naive_leaf`, `naive_cleaf`) into one `Doc` per `(k, table)` — R2.2's and
R2.5's `Tests.lean` sections each independently re-run that same extraction
for `k = 2` standard, and since extraction is a deterministic pure
computation, the results are the *same closed term*, not merely equal ones.
This means `qft`'s embedded `.call "phase_product"` leaf (see below) can cite
R6.2's already-proved `evalNode_phase_product_correct` directly — no
register-slicing, width, or angle lemma about `phase_product` needed
restating for `qft` at all, mirroring exactly what R6.3's `cphase_product`
half found for `r2_4_ops`/`r2_2_ops` (§12.7), except one level more useful
here since it's the whole `Doc`, not just the table.

**`qft`'s extracted shape, established once by direct inspection**
(`extractQFTBody`, `Reflect/Targets.lean`): `body = .cond (w=0) id (.cond
(w=1) (H (qubit r 0)) split)`, where `split = .seq [rightCall, mid, leftCall,
radix]` — `rightCall`/`leftCall` are `.call "qft"` nodes on `r`'s
`activeSlice` halves (`leftReg`/`rightReg`, named directly per D2, exactly
mirroring `Reflect/Extract.lean`'s own already-documented `translateW`/
`translateReg` cases for them), `radix` is a plain `.op "RadixReverse"`
leaf, and `mid = .seq [zeroExtend x, .seq [zeroExtend z, .seq [.call
"phase_product" …, .seq [zeroDealloc z, zeroDealloc x]]]]` — the embedded
unsigned phase product, extracted as a genuine `Node.call`, not inlined,
because `Reflect/Extract.lean`'s `translatePlan` recognises
`standardSignedPhaseLoweringPlan` by name *inside* `standardPhaseProdUsingPlan`'s
own `.eq_1` unfolding (documented already, `Extract.lean`'s own comments) —
confirmed directly by `#eval`-printing `r2_5_doc`'s `"qft"` template body
before writing any proof.

**The `qftEnv`/`ppEnv` compatibility obstacle — the one genuinely new
technical problem this half of R6.3 needed, beyond mirroring cphase_product's
playbook.** `Emit/Tests.lean`'s own `r2_5_env` (the environment its R2.5
`native_decide` smoke test uses) carries two extra `opaqueW` cases
(`"qftXWork"`/`"qftZWork"`) that `qft`'s own template body never queries —
they exist only for `shor`'s template, which calls into `qft` externally and
needs to compute `qftXWork ops r`'s width symbolically. Naively reusing
`r2_5_env` as the R6 environment would have made `Env.call`'s carried-through
`opaqueW` (at the embedded `phase_product` leaf) a *different closure* from
`Proofs/PhaseProduct.lean`'s `ppEnv` — same behaviour at every value
`phase_product`'s body actually queries, but not the same *term*, and
`evalNode_phase_product_correct` is stated against `ppEnv` literally, not
generically over any behaviourally-equivalent environment (unlike
`naiveLeafEnv`/`naiveCLeafEnv` in `Correct.lean`, which took `opaqueW`/
`coeff` as parameters specifically so a caller's *own* environment could be
reused directly). Two ways to fix this were available: generalize R6.2's
`ppEnv`/`evalNode_phase_product_correct` to take `opaqueW`/`coeff` as
parameters (matching `naiveLeafEnv`'s precedent) — invasive, since the whole
~1850-line proof cites `ppEnv`'s hardcoded closures directly throughout, so
this would need re-verifying most of it; or define `qft`'s *own* R6
environment (`qftEnv`, mirroring `cppEnv`'s already-established precedent as
a distinct-from-`Tests.lean` R6 environment) with `opaqueW`/`coeff`
restricted to exactly `ppEnv`'s three cases (`"nextWidth"`, `"reserveNeed_x"`,
`"reserveNeed_z"`) plus the same catch-all. The second is what `Proofs/Qft.lean`
does, confirmed the cheap way before writing anything downstream:
`(qftEnv x z z).opaqueW = (ppEnv x z phi).opaqueW` and `.coeff` likewise
close by plain `rfl`, once `r2_5_ops = r2_2_ops`/`r2_5_k = r2_2_k` are
unfolded — the two closures really are the same normal form, not merely
extensionally equal, so `Env.call`'s carry-through at the `phase_product`
leaf produces literally `ppEnv`'s own environment and
`evalNode_phase_product_correct` applies with zero restatement.

**The fuel bound needed a genuine "+1" strengthening beyond §12.2's literal
suggested form.** The naive hypothesis `regSize r.active < fuel` is *not*
sufficient: the embedded `.call "phase_product"` leaf is a direct child of
`qft`'s own body (not behind another `.call`), so it runs with `fuel - 1`
available, and needs `phaseInputSize (grown children) < fuel - 1` per
R6.2's own theorem. `phaseInputSize` at that leaf works out to
`⌈w/2⌉ + 1`, which equals `w` exactly (not less) at `w = 2` and `w = 3` — so
at the boundary fuel value permitted by the naive hypothesis (`fuel = w + 1`),
`fuel - 1 = w = phaseInputSize`, failing the required *strict* inequality.
`Proofs/Qft.lean` states `evalNode_qft_correct`/`r2_5_doc_qft_correct` with
`regSize r.active + 1 < fuel` instead (one unit more headroom) — checked to
propagate correctly through the induction's own recursive `qft`-to-`qft`
calls too (their own decrease is generous enough that the same "+1" survives
unchanged at every level). A concrete instance of the "Fuel" risk (§12.6)
already flagged in the abstract; this is the first target where the naive
bound was actually insufficient, not just unproved.

**A reproducible `open`-merging parser quirk, unrelated to the math, cost
real time and is worth recording.** `Proofs/Qft.lean` needs both `r2_2_*`
names (inherited from importing `Proofs/PhaseProduct.lean`, which opens
`Shor.Emit.Tests` *restricted* to `(r2_2_k r2_2_hk r2_2_ops r2_2_doc)`) and
`r2_5_*` names live at once — the first thing this file needs is
`r2_5_doc = r2_2_doc` by `rfl`. Writing this file's own `open Shor.Emit.Tests
(r2_5_k r2_5_hk r2_5_ops r2_5_doc)` (restricted to the *other* subset) made
that `rfl` fail with a genuine "not definitionally equal" error — not a
timeout — even though the identical statement, either fully qualified
(`Shor.Emit.Tests.r2_5_doc = Shor.Emit.Tests.r2_2_doc`) or under one
*unrestricted* `open Shor.Emit.Tests`, closes by `rfl` instantly. Root cause
not fully diagnosed (some interaction between two restricted `open`s of the
same namespace with disjoint name lists, one inherited via import, one
written locally); the workaround — use one unrestricted `open Shor.Emit.Tests`
instead of restricting it — is unconditionally safe and is what
`Proofs/Qft.lean` does. Anyone writing a future R6 file that needs names from
*two* different `Tests.lean` sections at once should expect this and open
unrestricted from the start, rather than losing time to it.

**Proof architecture, following R6.2's/R6.3's established shape**: ground-truth
structural decomposition of `r2_5_doc`'s `"qft"` template body (all `rfl`,
mirroring `r2_2_ppBody`'s style exactly) → guard lemmas (`evalProp_qft_guard0`/
`_guard1`, deciding `regSize r.active = 0`/`= 1`) → the two base cases
(`evalNode_qft_empty`/`_singleton`, the latter needing `Reg.lowQubit`'s
`Fin`-proof-irrelevance the same way `evalNode_naive_leaf`'s `qb` does) →
register-slicing lemmas for `leftReg`/`rightReg` (`evalReg_qft_leftSlice`/
`_rightSlice`, genuinely simpler arithmetic than `phase_product`'s own
`fillSlack`/prefix-sum bookkeeping, since `Reg.take`/`Reg.drop` compose
directly — `List.take_length` after `List.length_drop` is the whole
`rightSlice` proof) → `.ext`/`.grow` register lemmas for the phase leaf's
arguments (`evalReg_qft_ext_left`/`_right`, `_grow_left`/`_right`, using
`disjoint_of_left_subset`/`leftReg_mem_parent`/`rightReg_mem_parent` — already
general lemmas in `ShorVerification/Implementation/QFT/Split.lean`/
`Lowering/Workspace.lean`, nothing new needed — plus `ExtReg`'s proof-field
irrelevance, exactly `evalReg_pp_ext*`'s own technique) → the angle lemma
(`evalA_qft_phi`, trivial: `qftPhi m := 2/2^m` matches `AExpr.qftPhi`'s
`evalA` case by definition) → `RadixReverse`'s leaf lemma → `Env.call`
lemmas for the two self-recursive `.call "qft"` leaves (`envCall_qft_right_eq`/
`_left_eq`, simpler than `phase_product`'s own recursive `envCall` since
`xWork`/`zWork` pass through *unchanged* — never re-split, never grown, per
R2.5's own already-documented extraction finding) → `standardPhaseProdUsingPlan`'s
own cast obstacle, resolved with the *already-committed*, fully general
`lowerGateRec_eqmp_final` from `Proofs/PhaseProduct.lean` (no new cast-erasure
machinery needed — this tactic-mode plan builder has the identical `by let
…; simpa […] using completePlan` shape as `planCompiledSignedPhaseGate`, so
the exact same fix applies) → the alloc/dealloc leaf lemmas (structurally
simpler than `phase_product`'s own, since there is no `extraDelta`/
`isTopChunk` case split here — always a plain, unconditional `zeroExtend`/
`zeroDealloc`) → assembling the `mid` node (alloc, phase, dealloc) into one
`flattenSeq` statement against `lowerGateRec (standardPhaseProdUsingPlan …)`
→ assembling the whole `split` node (right, mid, left, radix) against
`lowerQFTPlan`'s own `.split` case, taking the two recursive calls' results
as hypotheses → unfolding the two `.call "qft"` leaves down to a fresh
recursive instance of `evalNode`/`qftEnv` at the child register (mirroring
`evalNode_pp_call`'s self-referential unfolding) → the main induction itself,
strong induction on `regSize r.active`, base cases via `standardQFTLoweringPlan.eq_1`
+ `dif_pos`, split case via `dif_neg`/`dif_neg` + the split-assembly lemma,
feeding the two children into the induction hypothesis with the "+1"-adjusted
fuel bound established above. The one recurring tactic pitfall (same as
R6.2's own "Sixth round" note): `refine ⟨_, ?_, ?_⟩` on `∃ g, P g ∧ Q g` fails
to unify the witness whenever it isn't syntactically pinned by `P`/`Q` alone
— every existential in this file is discharged by first proving the witness
as a fully-explicit `have`, then `refine ⟨_, hFirst, ?_⟩` — and a second,
narrower one specific to this file: stating a `simp only` call with *both* a
generic equation-lemma name (bare `evalReg`/`evalW`) *and* a specific
pre-computed fact about the *same* redex in one call is unreliable — the
generic equation sometimes wins the rewrite race, consuming the redex before
the specific fact gets a chance, silently reported only as an "unused simp
argument" warning rather than a failure. Fixed throughout by *either* using
`rw` (which takes exactly the named lemma, no competition) for one redex at a
time, *or* precomputing the entire `List.mapM` result as one atomic `have`
(e.g. `hwAll`/`hrAll` in the `.call "qft"` unfolding lemmas) so the generic
name never needs to appear in the same `simp only` call as the specific one.

### 12.9 R6.4 (`shor_gate`/`shor`) status: in progress — shared infrastructure done, no leaf lemma yet

`shor_gate`'s theorem (`Emit/PLAN.md` §12.2: `IR.instantiateGate <doc>
"shor_gate" (shorEnv …) fuel = .ok (orderFindingApprox …)`) and `shor`'s
(the `LowGate`-level composition through `translateLowerGate`) are R6.4,
the last unproved R6 target besides R6.5's proof-script generator. This
section records what a scoping pass plus initial proof-engineering found,
before the leaf-by-leaf assembly itself — the same kind of "round of
research findings" entry R6.2/R6.3 accumulated several of before closing,
not a final status.

**Scope, established by direct reading of the real definitions before
writing any proof** (`ShorVerification/Implementation/Shor/Circuit/
OrderFinding.lean`, `.../ModularExponentiation/Circuit/{Steps,ModExp,
Workspace,CmpLtNW}.lean`): `orderFindingApprox = H_reg x.active ;; initY1
y.active ;; modExpApproxValid a N x.active y work scratch flag hworkspace
hstep4 ;; IQFT x`. `modExpApproxValid` loops over `x.active.qubits`
(symbolic length, hence a `Node.loop` at extraction, exactly mirroring
`naive_leaf`'s already-proved `signedTerms` loop — no new IR construct
needed). Each loop iteration is `CmodMulInPlaceCore c N ctrl data work
scratch flag hworkspace hstep4 = step1 ;; step2 ;; step3 ;; step4 ;; step5`
(`c := (a^(2^e)) % N`, `ctrl := x`'s `e`-th qubit, `data := y`), Algorithm
1's five steps (`step1`/`step2`/`step5` are `H_reg`/`IQFT` wrapped around a
`Gate.CPhaseProdUsing`/`Gate.PhaseProdUsing` call; `step3` is two plain
`Gate.CmpGeConst`/`.CSubConst` leaves; `step4 = cmpLtNW` is itself `mul ;;
diff ;; CNOT ;; †diff ;; †mul`, `mul := fastConstMulInto` another
QFT+`PhaseProdUsing`+adjoint-QFT sandwich, `diff := cmpLtNWDifference` four
plain leaves). Confirmed directly by `#eval`-printing `r2_6g_doc`'s
`"shor_gate"` template body (596 lines of `repr` output, read in full, not
sampled) against this structure, leaf for leaf, before writing anything —
every leaf matched exactly, no surprises against the real definitions.

**Key de-risking finding: `orderFindingApprox`/`lowerGate`'s whole call
chain is genuinely free of the universe-cast obstacle `phase_product`/`qft`
needed `eqmp_heq`/`lowerGateRec_eqmp_final` for.** Every definition in this
chain (`orderFindingApprox`, `H_reg`, `initY1`, `modExpApproxValid`,
`modExpApproxStepsValid`, `CmodMulInPlaceCore`, `step1`–`step5`, `cmpLtNW`,
`fastConstMulInto`, `cmpLtNWDifference`, `Gate.PhaseProdUsing`/
`.CPhaseProdUsing`) is a plain structural `def` — no `WellFounded.fix`/
`by_cases`-compiled recursion anywhere at the `Gate` level (unlike
`standardSignedPhaseLoweringPlan`/`standardQFTLoweringPlan`, which build a
*dependently-typed proof witness* alongside the `Gate`). The one place a
tactic-mode `def` does appear — `ModMulCircuitWorkspaceOK.step1Workspace`/
`.step2Workspace`/`.step5Workspace` and `Gate.PhaseProdWorkspace.ofExtRegs`,
which *build* the workspace values `Gate.CPhaseProdUsing`/`PhaseProdUsing`
consume — turned out to be a **non-issue**, confirmed directly: `ofExtRegs
x z hx hz howned`'s tactic body is `refine { xReserve := x.reserve, zReserve
:= z.reserve, x_can_grow := ?_, … }` — the *data* fields (`xReserve`/
`zReserve`) are literal, untouched by any of the `?_`-deferred proof
obligations, so `(ofExtRegs x z hx hz howned).xExt = ExtReg.withReserve
x.active x.reserve _ = x` and `.zExt = z` by a **plain `unfold` + `rfl`**
(no `dif_pos`/`eqmp_heq` needed at all — confirmed by direct proof, not
assumed), since `x = ExtReg.withReserve x.active x.reserve x.
active_reserve_disjoint` always (structure eta) and the third field is
`Prop`-valued (proof-irrelevant). This makes `step2Workspace.xExt = work`/
`.zExt = data.grow 1` and `step5Workspace.xExt = data.grow 1`/`.zExt = work`
immediate (`ofExtRegs` applied directly, no further slicing). Only
`step1Workspace` needs one register-slicing step beyond this (it first
builds `dataNoCarry := ExtReg.withReserve data.active (data.reserve.drop 1)
_` before calling `ofExtRegs`, dropping the reserve bit `step2` will later
grow into) — and `CmpLtNWWorkspace`'s `mulWorkspace` (Step 4's workspace,
used by `fastConstMulInto`) is not `ofExtRegs`-derived at all, but the
*structure itself* carries `mul_xReserve_eq : mulWorkspace.xReserve =
work.reserve`/`mul_zReserve_eq : mulWorkspace.zReserve = scratch.reserve`
as explicit fields — evidently placed there for exactly this reuse — so
`mulWorkspace.xExt = work`/`.zExt = scratch` follows the same
`ExtReg.withReserve`-reconstruction argument directly from those two fields,
no tactic-mode unfolding needed at all.

**Consequence for scale**: R6.4 is "wide, not deep" — the extraction-side
`PLAN.md` §6.8 called it "the largest target by far… needed the most new
machinery of any R2 phase," and that holds for the *proof* too (five
Algorithm-1 steps, each with its own `H_reg`/QFT/`PhaseProdUsing`/register
bookkeeping, means many more leaves than `phase_product`'s 21 or `qft`'s
handful) — but unlike `phase_product`/`qft`, `shor_gate` is **not itself a
recursive template** (`orderFindingApprox`/`lowerGate` have no `Node.call`
back to `shor_gate`/`shor`), so no well-founded induction is needed
anywhere in this proof — only the one `Node.loop` (already a solved
problem, `naive_leaf`'s pattern) and a long but non-recursive leaf-by-leaf
assembly. Net assessment: comparable in total *volume* to `phase_product`
plus `qft` combined, but each individual obstacle is easier (no casts, no
induction) — "wide but shallow," not deeper than what's already been done.

**Established, and independently `#print axioms`-verified clean, in
`Proofs/Shor.lean`** (no `sorry` anywhere in the file):
- `Gate.flattenSeq` (mirroring `LowGate.flattenSeq`, but recursing into
  `.adj` bodies too — `Emit/Tests.lean`'s pre-existing `r2_6g_flatten`/
  `r2_6_flatten` already established that this target's adjoints wrap
  *multi-gate* sub-sequences, unlike every earlier target's single-leaf
  adjoints, so comparing extracted output to the real `Gate` needs this
  recursion; not `partial`, ordinary structural recursion on the strictly
  smaller `.adj` body) and `flattenSeq_foldGateSeq` (the `foldGateSeq`
  bridge, mirroring `Correct.lean`'s `flattenSeq_sequence`).
- `evalReg_ext_full`: the extracted `.ext (.activeSlice r 0 W)
  (.reserveSlice r 0 C)` pattern equals `X` whenever `r`/`W`/`C` evaluate to
  `X`/`X.width`/`X.capacity` — i.e. slicing a register's *entire* range and
  re-`ext`ing it reconstructs the register itself. This single general
  lemma (parametrized over an arbitrary `RegExpr r`, not tied to one named
  variable) covers every "`work`/`scratch`/`y.grow 1` used at its own full
  width" leaf in `CmodMulInPlaceCore` — the large majority of its register
  arguments — with no per-site restatement.
- `evalReg_grow_bare`: the extracted `.grow r n` pattern equals `X.grow k`
  given `r`/`n` evaluate to `X`/`k` — trivial, reusable at every `.grow`
  site.
- `evalNodeGate_Hreg_loop`: the extracted `H_reg`-loop pattern (`.loop "i" 0
  W (.op "H" [.qubit r' (W-1-i)] …)`) equals `foldGateSeq (Y.active.qubits.
  reverse.map Gate.H)`, for *any* register `Y` (used for both `H_reg x` at
  the top level and `H_reg work` inside Step 1/Step 5) — proved via a clean
  intermediate fact worth recording for reuse: `H_reg r = foldGateSeq
  (r.qubits.reverse.map Gate.H)` *exactly* (not just up to `flattenSeq`),
  from the general identity `l.foldl (fun acc q => f q ;; acc) e =
  List.foldr (fun q acc => f q ;; acc) e l.reverse` (`List.foldr_reverse`)
  composed with `List.foldr (fun a acc => f a ;; acc) id l = foldGateSeq
  (l.map f)` (immediate induction) — then a reindexing lemma
  (`range_getD_reverse`/`map_getD_H_eq_reg`) connecting the loop's ascending
  `List.range`-indexed unrolling to this descending-`.reverse` form.
- `Env_bindW_self`: `(env.bindW name v).w name = some v` — a small but
  load-bearing fact, needed because of the **same recurring `simp`
  ambiguity R6.3 already documented** (§12.8's own closing note): once
  `evalW`'s generic `.var` equation is in a `simp only` call, it consumes a
  `.var name` redex *before* a lemma stated about the pre-unfolded
  `evalW (env.bindW name v) (.var name)` form gets a chance to fire — the
  fix, as before, is a lemma stated at the *post-unfold* (raw field) level.
  This bit R6.4's very first non-trivial lemma (`evalNodeGate_Hreg_loop`),
  confirming it is a genuinely recurring pattern in this codebase, not a
  one-off from R6.3, and any future R6 work should reach for a raw-field
  lemma immediately rather than rediscovering the same failure.

**Not yet started**: ground-truth extraction of `CmodMulInPlaceCore`'s own
five-step body (the `#eval` inspection above was done by reading, not
turned into named `rfl` lemmas yet), the `Gate.PhaseProdUsing`/
`.CPhaseProdUsing` generic leaf-group lemma (5-node assembly: two
`zeroExtend`s, one `SignedPhaseProd`/`CSignedPhaseProd`, two
`zeroDealloc`s — parametrized over the two operand registers and angle, for
reuse at all four `PhaseProdUsing`/`CPhaseProdUsing` call sites: `step1`,
`step2`, `step5`, `fastConstMulInto`), the `modExpApproxValid` loop-body
lemma (connecting the loop's `.var "e"`-indexed unrolling to
`CmodMulInPlaceCore`'s own per-bit invocation, mirroring
`evalNodeGate_Hreg_loop`'s technique but with a non-trivial loop body
instead of one leaf), the five step-assembly lemmas themselves, and the
final top-level `.seq` assembly (`H_reg x ;; initY1 y ;; modExpLoop ;;
IQFT x`). Whoever continues should start from `evalReg_ext_full`/
`evalReg_grow_bare`/`evalNodeGate_Hreg_loop` (already proved, reusable
as-is) and the `ModMulCircuitWorkspaceOK`/`CmpLtNWWorkspace` `xExt`/`zExt`
identities documented above (not yet stated as committed lemmas, but
verified true and how to prove them) as the starting toolkit — the
per-leaf mechanical pattern (ground-truth `rfl`, then `simp`/`rw` with the
right register/width facts, `flattenSeq`-not-raw-equality throughout) is
already fully established by `PhaseProduct.lean`/`Qft.lean` and this
section's own findings; what remains is volume, not a new kind of
difficulty. `shor` (the `LowGate` composition through `translateLowerGate`,
embedding `qft`/`phase_product`/`cphase_product` as `Node.call`s) is
untouched and explicitly out of scope for this pass.

### 12.10 R6.4 progress: `CmodMulInPlaceCore` Steps 1 and 2 closed

Following on from §12.9's scoping pass, this round did the ground-truth
extraction and leaf assembly it left as "not yet started," for the first two
of `CmodMulInPlaceCore`'s five steps. Both are now closed in
`Proofs/Shor.lean`, no `sorry`, `#print axioms` clean; `lake build
EmitProofs` green throughout.

**Ground-truth decomposition of `r2_6g_sgBody`** (the full extracted
"shor_gate" template body) is now done end to end, not just read — every
node named by an `rfl`-provable `def` and every structural equation
(`_eq`/`_eq_seq`/`_eq_adj`) proved by `rfl`: the top-level `H_reg x ;; initY1
;; modExpLoop ;; IQFT x` split (`r2_6g_HloopX`/`_initY1`/`_modExpLoop`/
`_iqftX`), the `modExpApproxValid` loop body split into
`CmodMulInPlaceCore`'s five steps (`r2_6g_step1`..`r2_6g_step5`), and each
step's own internal structure — including Step 4's nested `cmpLtNW = mul ;;
diff ;; CNOT ;; †diff ;; †mul` (`r2_6g_step4_mul_QFT`/`_core`/`_adjQFT` plus
`_diff`/`_cnot`/`_adjDiff`/`_adjMul`) and Step 5's `.adj`-wrapped
`H_reg ;; PhaseProdUsing ;; †QFT` shape (`r2_6g_step5_inner`/`_Hloop`/`_core`/
`_adjQFT`) — all matched exactly against the real definitions, no surprises.
One correction found during this pass: an earlier assumption (recorded only
informally, not yet committed as a lemma) that Step 5 reuses the same
drop-1-reserve register as Step 1 (`r2_6g_yDataReg`) was wrong — direct
inspection of the dumped extraction showed Step 5 actually uses
`r2_6g_yGrow1Reg` (the full `y.grow 1` register), matching the real `step5`'s
`Gate.CPhaseProdUsing ctrl phi (data.grow 1).active work.active
hworkspace.step5Workspace` call. Caught before any proof was built on the
wrong register, by checking the ground-truth statement against the dump
before using it.

**Generic assembly lemmas for the `PhaseProdUsing`/`CPhaseProdUsing` leaf
group** (the 5-node `zeroExtend;;zeroExtend;;SignedPhaseProd/
CSignedPhaseProd;;zeroDealloc;;zeroDealloc` pattern used at all four call
sites — Step 1, Step 2, Step 5, and Step 4's `fastConstMulInto`) are now
proved once and reused: `evalNodeGate_PhaseProdUsing`/
`evalNodeGate_CPhaseProdUsing`, parametrized over the two operand registers
and the angle, each returning both the `evalNodeGate` result and a
`flattenSeq` equation to `PhaseProdUsingGate`/`CPhaseProdUsingGate` directly
(the plain, non-tactic-mode macros) — no per-call-site restatement needed.

**`evalNodeGate_step1`** (Step 1: `H_reg work ;; CPhaseProdUsingGate ctrl
step1Workspace.xExt step1Workspace.zExt phi ;; †QFT work`, matching the real
`step1 = H_reg work.active ;; Gate.CPhaseProdUsing ctrl phi dataNoCarry.active
work.active hworkspace.step1Workspace ;; IQFT work.active`) is closed. Needed
one new register-slicing fact beyond §12.9's toolkit,
`evalReg_ext_dropReserve1`/`evalReg_yDataReg` (the extracted register for
`dataNoCarry := ExtReg.withReserve y.active (y.reserve.drop 1) _`), plus
`step1Workspace_xExt_eq`/`_zExt_eq` (confirming §12.9's "no cast obstacle"
finding *by proof*, not just inspection: both are a plain `unfold + rfl`) and
`evalA_step1_phi` (the extracted angle expression — a `2 * (((a^(2^e)) % N) +
N - 1) % N`-shaped `AExpr.ratio`/`.mul` term — reducing to the real angle via
plain `simp [evalA, evalW, …]`, no `qftPhi` involved here since Step 1's
angle is stated as a raw ratio, not via `qftPhi`). The final `flattenSeq`
equality needed `push_cast; ring_nf` to reconcile a `↑(2*x)` vs `2*↑x`
cast-order mismatch between the extracted and real angle expressions.

**`evalNodeGate_step2`** (Step 2: `QFT (y.grow 1) ;; PhaseProdUsingGate
step2Workspace.xExt step2Workspace.zExt phi ;; †QFT (y.grow 1)`, matching the
real `step2 = Gate.QFT data.grow 1 ;; Gate.PhaseProdUsing (qftPhi (work.width
+ (data.grow 1).width) * N) work.active (data.grow 1).active
hworkspace.step2Workspace ;; IQFT (data.grow 1)`) is also closed. Needed
`evalReg_yGrow1` (the extracted `.grow (.var "y") (.lit 1)` register,
built from a new general `evalReg_ext_full`-style call plus
`ExtReg.width_grow`/`ExtReg.capacity_grow` — the latter's real signature
turned out to require an explicit `y.CanGrow 1` hypothesis, not the
unconditional form glimpsed earlier in `PhaseProduct.lean`; supplied from
`hworkspace.data_canGrow_one`) and `step2Workspace_xExt_eq`/`_zExt_eq`
(again a plain `unfold + rfl`, confirming §12.9's finding for this second
`ofExtRegs` call site too). One new proof-engineering point for whoever
continues to Steps 3–5: Step 2's angle is stated via `AExpr.qftPhi`
directly (unlike Step 1's raw ratio), and `evalA`'s own `.qftPhi` case
unfolds to the *same* `2 / 2^m` shape as the real `qftPhi` definition — so
the natural move is to add `qftPhi` to the `simp` set used to evaluate the
extracted angle (closing the environment-lookup match statement) and *also*
to the `simp only [qftPhi]; ring` step used to prove the two angle
expressions equal (reconciling `regSize`-computed vs `width`-computed
exponents) — but these must stay **separate goals**: doing the environment
unfold with `simp only` instead of full `simp` leaves the string-key
`if`-chains from `Env.w`/`Env.a` unreduced (full `simp`'s default simprocs
are what collapse `"workW" == "e"`-style literal `Bool` decisions; `simp
only` does not, even with every needed lemma named explicitly), while doing
the final angle-equality step with full `simp` instead of `ring` risks
Mathlib's `div_eq_div_iff`-style simp set introducing a spurious `∨ N = 0`
disjunction from the division rather than just closing by commutativity —
each needs the tactic matched to what it's actually doing (environment
reduction vs. field arithmetic), not the same hammer for both.

**Not yet started**: Steps 3 (`Gate.CmpGeConst ;; Gate.CSubConst`, two plain
leaves — should be the simplest of the five), 4 (`cmpLtNW`'s five-leaf
`mul;;diff;;CNOT;;†diff;;†mul` structure, reusing the `r2_6g_step4_mul_*`/
`_diff`/`_cnot`/`_adjDiff`/`_adjMul` ground truth already established in
§12.9's decomposition pass), 5 (an `.adj`-wrapped version of Step 1's
pattern, using `r2_6g_yGrow1Reg` per the correction above, and a
`step5Workspace_xExt_eq`/`_zExt_eq` pair analogous to Steps 1/2's — not yet
written, though `CpModMulInPlaceCore`'s workspace-construction pattern from
§12.9 says it should be equally routine), the `modExpApproxValid` loop-body
assembly (connecting the `.loop "e" 0 xW (…)` unrolling to the five-step
invocation, mirroring `evalNodeGate_Hreg_loop`'s technique but with a
non-trivial 5-step loop body instead of one leaf), and the top-level
`orderFindingApprox` assembly (`H_reg x ;; initY1 y ;; modExpLoop ;; IQFT
x`, now that `r2_6g_HloopX`/`_initY1`/`_iqftX` ground truth is already in
hand from this round's decomposition pass).

### 12.11 R6.4 `shor_gate` half: done — Steps 3–5, the loop assembly, and the top-level theorem all closed

This round finished what §12.10 left open: `CmodMulInPlaceCore`'s Steps
3–5, the `modExpApproxValid` loop-body assembly, and the top-level
`orderFindingApprox` theorem. **`evalNodeGate_shor_gate` — R6.4's target
theorem for `shor_gate` — is now closed**, no `sorry` anywhere in
`Proofs/Shor.lean`, `lake build EmitProofs` green, `#print axioms` clean on
every new theorem. This completes the `shor_gate` half of R6.4; `shor` (the
`LowGate`-level composition through `translateLowerGate`) remains untouched
and out of scope for this pass, per standing instruction.

**Step 3** (`CmpGeConst ;; CSubConst`, two plain leaves) was the simplest of
the five, closing directly from the existing `r2_6g_step3_cmp_eq`/`_sub_eq`
ground truth with no new register-slicing machinery — only two new raw-field
facts (`evalReg_scratchVar`, `evalReg_flagVar` + `flagVar_singleQubit`,
the latter confirming `(ExtReg.ofReg (Reg.interval flag 1)).singleQubit? =
some flag` by `simp [ExtReg.singleQubit?, ExtReg.ofReg, Reg.interval]`, no
`decide`/`omega` needed since `Reg.interval flag 1`'s single-qubit list
reduces directly).

**Step 4** (`cmpLtNW = mul ;; diff ;; CNOT ;; †diff ;; †mul`) was the
largest single leaf-assembly of the five, and surfaced three genuinely new
proof-engineering points worth recording for any future R6 work on
`CmpLtNWWorkspace`-shaped targets:
- `CmpLtNWWorkspace.mulWorkspace`'s `.xExt`/`.zExt` are **not** `ofExtRegs`-
  derived (unlike every earlier `Gate.PhaseProdWorkspace` in this file), so
  the `unfold + rfl` trick that closed `step1Workspace_xExt_eq` etc. does
  not apply here. Instead the structure carries `mul_xReserve_eq`/
  `mul_zReserve_eq` as *propositional* fields (`mulWorkspace.xReserve =
  work.reserve`, not defeq), so recovering `mulWorkspace.xExt = work`
  needs an explicit `ExtReg` extensionality lemma
  (`ExtReg.ext' : e1.active = e2.active → e1.reserve = e2.reserve → e1 =
  e2`, by `cases e1; cases e2; simp_all` — the third field is `Prop`-valued
  so proof-irrelevance closes it) plus one `rw` of the propositional
  reserve-equality field — a plain `rw [ExtReg.withReserve, ...]` chain
  fails with "motive is not type correct" since the reserve argument
  appears inside a later field's *type* (`x_reserve_disjoint : Disjoint
  work.active mulWorkspace.xReserve`), the same dependent-rewrite failure
  documented before for `let`/`have`-bound terms, here triggered by a
  structure field instead.
- Raw `Gate`-level equality between `cmpLtNW`'s unfolded definition and a
  hand-written nested `;;`-chain is **not safe to state directly** once a
  sequence has more than ~3 leaves with sub-blocks of different depth (here
  `mul`/`diff` are themselves 3- and 4-leaf `;;`-trees substituted as single
  elements into the outer 5-way chain): `Gate.seq`/`;;` is a raw two-argument
  constructor, not associative as a term, so a hand-typed RHS chain
  and the actual substituted-unfold LHS can describe the *same flattened
  circuit* while being different terms, and trying to prove them equal
  *before* flattening produces genuine (not just tedious) bracket-matching
  errors. Fix: skip the intermediate raw-equality `have` entirely for
  compound assemblies — go straight to `Gate.flattenSeq` on both sides of
  the final goal and let `simp only [Gate.flattenSeq, flattenSeq_foldGateSeq,
  List.flatMap_cons, List.flatMap_nil, List.append_nil, …]` normalize both
  through list-append (associative, so bracket differences vanish for free);
  reserve the raw-equality `have` style (used successfully for Steps 1/2/5)
  for assemblies that stay within one flat `;;`-chain of already-atomic
  leaves.
- `simp only [cmpLtNW, fastConstMulInto, cmpLtNWDifference]` (zeta-reducing
  the `let mul := …; let diff := …; have hscratch := …; let sign := …`
  chain inside `cmpLtNW`'s tactic-adjacent body) fully inlines everything
  down to a flat `Gate` term with no residual `let`/`have` binders — same
  technique as §12.10's `simp only [step1, IQFT]`, confirmed to scale to a
  4-`let`-deep body, not just the 1–2 seen before.
- `cmpLtNWSignQubit`'s own definition (`scratch.active.get ⟨regSize
  scratch.active - 1, _⟩`) needs `ExtReg.width`/`regSize`/`Reg.width`
  unfolded on *both* the hypothesis (`0 < regSize scratch.active`) and the
  goal (`scratch.width - 1 < scratch.active.qubits.length`) before `omega`
  can see they're the same fact — unfolding one side only leaves omega
  looking at unrelated opaque atoms (confirmed by testing: doing `unfold …
  at h ⊢` in one call throws "failed to unfold X" when X only occurs in one
  of the two, so unfold the goal and the hypothesis in separate calls).

**Step 5** (`.adj`-wrapped `H_reg ;; CPhaseProdUsing ;; adj QFT`, using
`r2_6g_yGrow1Reg` per §12.10's already-recorded correction) closed by
direct reuse of Step 1's exact technique — one new workspace pair
(`step5Workspace_xExt_eq : h.step5Workspace.xExt = data.grow 1`/
`_zExt_eq : .zExt = work`, both plain `unfold + rfl` since `step5Workspace`
*is* `ofExtRegs`-derived, unlike Step 4's `mulWorkspace`) and one new angle
fact (`evalA_step5_phi`, mirroring `evalA_step1_phi`'s `step5Const`/
`modpow`/`mod` opaque chain) were all that was needed; the `.adj`-wrapping
itself was mechanical (`evalNodeGate`'s `.adj` case is `return .adj (←
evalNodeGate … body)`, so once the inner `.seq` assembly closes, `rw
[evalNodeGate, hInner]; simp only [Except.instMonad, Monad.toBind,
Except.bind, Except.pure]` discharges the wrapper).

**The `modExpApproxValid` loop-body assembly** (`evalNodeGate_modExpBody`
+ `evalNodeGate_modExpLoop_aux` + `evalNodeGate_modExpLoop`) was the one
piece with no earlier R6 precedent (`naive_leaf`'s loop has a single-leaf
body; `H_reg`'s loop, reused here for the top-level Hadamard fan-out, is
the same single-leaf shape). The technique that made it tractable:
- `evalNodeGate_modExpBody` first *combines* Steps 1–5's individual
  theorems (each already parametrized by a free `e : ℕ` and an `e < x.width`
  side-condition) into one theorem matching `CmodMulInPlaceCore` at a fixed
  `e` — a direct `obtain`-five-times-and-reassemble, no new proof
  technique, just volume.
- `evalNodeGate_modExpLoop_aux` proves the general shape by induction on the
  *count* of remaining iterations `n`, generalizing the start offset `e0`
  (hypothesis `e0 + n = x.width`), rather than trying to induct on `e0`
  directly or on the qubit list itself — this made both sides' recursion
  match structurally: the real `modExpApproxStepsValid`'s `ctrl :: ctrls`
  recursion peels the list `x.active.qubits.drop e0`'s head via
  `List.drop_eq_getElem_cons` (`l.drop i = l[i] :: l.drop (i+1)` given
  `i < l.length`), while the extracted `List.range (n+1)`'s matching peel
  uses `List.range_succ_eq_map` (`range (n+1) = 0 :: (range n).map (·+1)`)
  followed by `List.mapM_map` to reindex the tail from `(fun i => f
  (e0+(i+1)))` to `(fun i => f ((e0+1)+i))` — both sides then match the
  induction hypothesis at `e0+1` exactly. The base case (`n = 0`) needs
  `List.drop_eq_nil_of_le` (`e0 ≥ l.length → l.drop e0 = []`) to confirm the
  real recursion also bottoms out at `Gate.id`, matching `foldGateSeq [] =
  Gate.id`'s `flattenSeq = []`.
- `evalNodeGate_modExpLoop` is the corollary at `e0 = 0`, `n = x.width`,
  connecting the extracted `.loop "e" 0 xW modExpBody` node (whose
  `evalNodeGate` semantics is literally `foldGateSeq ((List.range (hiV-loV))
  .mapM (evalNodeGate … (env.bindW var (loV+i))) body)`, i.e. exactly the
  aux lemma's LHS shape at `loV=0`) to `modExpApproxValid`.

**The top-level assembly** (`evalNodeGate_shor_gate`) needed two new leaf
facts for the pieces outside the loop — `evalNodeGate_HloopX` (reusing
`evalNodeGate_Hreg_loop` directly with `Y := x`, no new technique) and
`evalNodeGate_initY1` (a `.cond`-guarded `id`/`X q` pair matching
`initY1 y.active`'s `match y.qubits with | [] => id | q :: _ => X q`; the
one new pattern here is deriving the extracted qubit index `y.active.qubits.
getD 0 0` equals the real match's bound `q` by `cases hcase :
y.active.qubits with | nil => … | cons q rest => …` and then closing the
final register-index equality with `simp [hcase]` rather than a manual
`rw`/`List.getD_eq_getElem` chain — plain `rw` hit the same dependent-motive
failure as Step 4's `mulWorkspace` rewrite (the bound-index proof term's
type mentions the list being rewritten), and `simp [hcase]` sidesteps it by
handling the dependency itself) — then assembled the four top-level pieces
(`H_reg x`, `initY1 y`, the loop, `IQFT x`) exactly as Steps 1/2/5 assembled
their own three-piece bodies, closing the final `flattenSeq` goal with
`simp only [Gate.flattenSeq, Hreg_eq_foldGateSeq, hLoopFlat, List.append_nil,
IQFT]`.

**Verification, this round**: `lake build EmitProofs` → `Build completed
successfully (3321 jobs)`; `grep -c sorry Proofs/Shor.lean` → `0`;
`#print axioms Shor.IR.evalNodeGate_shor_gate` → `[propext, Classical.choice,
Quot.sound]` (also checked on `evalNodeGate_step3`/`_step4`/`_step5`/
`_modExpBody`/`_modExpLoop`/`_modExpLoop_aux`, all clean).

### 12.12 R6.4 `shor` half: scoping + core infrastructure (doc-independence lemma proved and merged; leaf composition not yet built)

This round moved from `shor_gate` (Gate level, done — §12.11) to `shor`
(the `LowGate`-level theorem, `Emit/PLAN.md` §12.2: `IR.instantiate <doc>
"shor" (shorEnv …) fuel = .ok (lowerGate k hk ops (orderFindingApprox …)
hlower)`), per the coordinator's explicit go-ahead to continue past the
earlier checkpoint. This section records the scoping pass and one
substantial, **fully proved and merged** piece of new infrastructure; the
leaf-by-leaf assembly itself (mirroring `shor_gate`'s Steps 1–5) is not
started yet — this is a "round of research findings" entry, not a closing
one.

**Scope, established by reading the real definitions and the extractor
before writing any proof**: `shor`'s `Node.call`s reach into `qft`/
`phase_product`/`cphase_product`'s own template bodies — `translateLowerGate`
(`Emit/Reflect/Extract.lean`, a `MetaM` walk over `lowerGate`'s own equation
structure, run at *extraction* time, not runtime) splices a `Node.call
"qft"/"phase_product"/"cphase_product"` in place of a raw `.op "QFT"/
"SignedPhaseProd"/"CSignedPhaseProd"` leaf wherever `lowerGate`'s own match
calls `lowerQFT`/`lowerSignedPhaseProdWithWorkspace`/
`lowerCSignedPhaseProdWithWorkspace`; every other `Gate` constructor
(`.seq`/`.adj`/`.H`/`.CNOT`/`.zeroExtend`/…) lowers by direct 1-1
translation, same as `shor_gate`. `Gate.CmpGeConst`/`.CSubConst` (Step 3) are
a third case: `translateLowerGate` doesn't reconstruct a `Node.call` for
them at all — it recurses via `translateNode` on `lowerCmpGeConst`/
`lowerCSubConst`'s own *unfolded* body (a `mkSorry`-supplied workspace proof
stands in, since these lowerers are plain non-tactic-mode `def`s whose
*value* never depends on the proof argument), so Step 3 stays a direct
`.op`-leaf translation, no new composition machinery needed there.
`Shor.modExpApproxValid` itself is a third exception: since its loop isn't a
literal `Gate.seq` at the object level (a `List`-driven Lean-level fold, not
directly `whnf`-matchable), `translateLowerGate` special-cases the *name*
`Shor.modExpApproxValid` and rebuilds the `.loop "e" 0 xW body` node fresh,
recursing into `CmodMulInPlaceCore`'s structure via `translateLowerGate`
again (not `translateNode`) so the QFT/phase-product leaves *inside* the
loop body also get lowered to `Node.call`s — meaning `shor`'s extracted body
has **the same `H_reg`/`initY1`/`.loop "e"`/`IQFT` top-level skeleton as
`shor_gate`**, with `Node.call` leaves standing in for `shor_gate`'s raw
`.op "QFT"/"SignedPhaseProd"/"CSignedPhaseProd"` ops.

**Ground truth, confirmed by a full `#eval`-dump of `r2_6_doc`'s "shor"
template body (1150 lines, read in full)**: exactly **14** `Node.call`
sites — 2× `"cphase_product"` (Step 1's core, Step 5's core), 3×
`"phase_product"` (Step 2's core, Step 4's `mul`'s core, Step 4's `†mul`'s
own independent core — `translateLowerGate` re-walks `†mul`'s body fresh
under the `.adj` wrapper rather than reusing `mul`'s translation, so `mul`
and `†mul` each contribute their own QFT/phase-product triple), and 9×
`"qft"` (one QFT/†QFT pair each for Step 1, Step 2, `mul`, `†mul`, Step 5 —
10 expected, but Step 1/Step 5's *leading* `H_reg` isn't a QFT at all, it's
the plain Hadamard loop already handled — the count reconciles to 2+2+2+2+1
= 9, the `+1` being the top-level `IQFT x`) — no surprises against the
skeleton predicted from `shor_gate`'s own already-proved structure.

**Key discovery — `r2_6_doc`'s shared templates are `rfl`-*identical* to
their solo-extracted counterparts, not just semantically equivalent**:
checked directly, before assuming it —
```
theorem r2_6_pp_template_eq :
    r2_6_doc.templates.find? (fun t => t.name == "phase_product") =
    r2_2_doc.templates.find? (fun t => t.name == "phase_product") := by rfl
```
holds by **plain `rfl`** (not `native_decide`), and likewise for
`"cphase_product"` against `r2_4_doc`, `"qft"` against `r2_5_doc`, and
`"naive_leaf"`/`"naive_cleaf"` against their respective docs. This makes
sense given D2's genericity discipline (R2.7, §6.9: extraction is keyed by
Lean construct name only) but is not something the plan assumed —
`extract_ir_doc r2_6_doc smallLowering`'s macro independently rediscovers
"phase_product" while walking `shor`'s dependency closure, and it was worth
checking whether that rediscovery produces byte-identical `Template`
records (name, `wParams`/`aParams`/`rParams`, and body) or merely
equivalent ones. It's the former — which means **R6.2's/R6.3's already-
proved theorems can be reused as black boxes at every `.call` site inside
`shor`, with no re-derivation of `phase_product`/`cphase_product`/`qft`'s
own recursion**, provided the *evaluator* can be shown indifferent to which
`Doc` it's running against once the relevant templates agree.

**`evalNode_dind` (new, proved, merged into `Proofs/Shor.lean`, no
`sorry`, `#print axioms` clean)** supplies exactly that indifference:
given two `Doc`s `d1`/`d2` and a name set `names` closed under the call
graph (every name in `names` has `d1`/`d2` agreeing on `.templates.find?`,
and every template reachable *through* a name in `names` only calls further
names still in `names`), `evalNode d1 fuel env node = evalNode d2 fuel env
node` for any `node` whose own `.call`s land in `names`. Two proof-
engineering notes, both already-documented `Node`/`evalNode` obstacles
(§12.0/§12.0b) recurring in a new spot:
- `Node.callNames` (the new helper collecting a node's *syntactic* `.call`
  names, not unrolling recursion — that's what the "closed under the call
  graph" hypothesis is for) had to be written using explicit `Node.callNames
  x` calls throughout its own recursive equations, never `x.callNames` dot
  notation — a `def Node.callNames` written under `open Shor.IR` (rather
  than inside `namespace Shor.IR … end`) registers the constant as the
  *root*-level `Node.callNames`, not `Shor.IR.Node.callNames`, so dot
  notation on a `Shor.IR.Node` value can't find it. Easy to miss since
  `#check @Node.callNames` after the `def` still reports the (root-level)
  type correctly — only *later* dot-notation *uses* fail.
- `evalNode_dind`'s own proof needed nested nested nested (`fuel`, then
  `sizeOf node`) strong induction via `Nat.strong_induction_on`, *not* the
  `induction`/`cases` tactics on `node` — confirmed directly: `induction
  node with …` fails outright with "the induction tactic does not support
  the type `Shor.IR.Node` because it is a nested inductive type"
  (`Node.seq : List Node → Node`'s nested-`List`-of-`Self` shape, the same
  documented obstacle `Emit/IR/Syntax.lean`'s own docstring gives for
  `deriving DecidableEq`/`LawfulBEq`). A plain `match node, hle, hsub with`
  *pattern match* (not the `induction` tactic) works fine for destructuring,
  since the recursion is driven entirely by the two explicit
  `Nat.strong_induction_on` calls rather than an auto-generated recursor —
  this is the general fix for "need to case on a `Node`/`WExpr`/… value
  inside a proof" anywhere else in R6 that hits the same wall. A first
  attempt at threading the well-founded recursion through a `mutual … end`
  block (mirroring `evalW`/`evalWList`'s own mutual structure) compiled the
  *syntax* successfully but left several `decreasing_by` obligations that
  automatic tooling couldn't discharge (the auto-generated goal for a
  recursive call mediated through an external helper lemma, e.g.
  `List.mapM_congr'`, doesn't carry the same auto-introduced membership
  hypothesis a *direct* `List.mapM (evalNode d fuel env)` self-reference
  gets) — abandoned in favor of the two-level `Nat.strong_induction_on`
  version above, which sidesteps needing any automatic `decreasing_by` at
  all (every recursive call is justified by an explicit `have`-derived
  inequality passed to the strong-induction IH directly).

**Register-level wiring resolved but not yet turned into a committed
lemma, for whoever continues**: `shor`'s `"qft"` `Node.call`s pass a
reserve-*stripped* register for `qft`'s own `"r"` parameter (the extracted
rArg is a bare `.activeSlice (.var "work") 0 workW`, not wrapped in `.ext`
with a reserve slice, evaluating to `ExtReg.ofReg work.active` — reserve
empty) — yet `Qft.lean`'s `evalNode_qft_correct` is stated generally enough
for this to be a non-issue: its workspace hypothesis is the *weaker*
`QFTWorkspaceOK r2_5_ops r.active xWork.active zWork.active` (already
`.active`-only), not the *stronger* `QFTReserveOK r2_5_ops r` (which needs
`r`'s own nonempty capacity and would fail at `r := ExtReg.ofReg work.active`
since that has no reserve at all) — so the right call site is
`evalNode_qft_correct` directly, at `r := ExtReg.ofReg work.active`,
`xWork/zWork := ExtReg.ofReg (qftXWork/qftZWork r2_6g_ops work)` (matching
the extracted rArgs' evaluated values field-for-field against `qftEnv`'s
three positional `ExtReg` parameters), with the workspace hypothesis
supplied as `(the real QFTReserveOK r2_6g_ops work).explicitWorkspace` —
*not* the already-established convenience corollary `r2_5_doc_qft_correct`
(which insists on the full, reserve-carrying `r` and would need an
extra reserve-invariance lemma to bridge). The resulting conclusion
(`lowerQFTPlan (standardQFTLoweringPlan … r.active xWork.active zWork.active
…)`) only ever mentions `.active` projections, so `r := ExtReg.ofReg
work.active` gives exactly the same value as `r := work` would — confirmed
by inspection of `evalNode_qft_correct`'s and `lowerQFT`'s own statements,
not yet turned into a standalone committed fact.

**Not yet started**: the LowGate-level analogues of `evalNodeGate_
PhaseProdUsing`/`_CPhaseProdUsing` (composing the `zeroExtend`/`zeroDealloc`
leaves with a bridged `Node.call "phase_product"/"cphase_product"` leaf via
`evalNode_dind` + R6.2/R6.3's theorems — the middle leaf's value collapses
to `lowerSignedPhaseProdWithWorkspace`/`lowerCSignedPhaseProdWithWorkspace`
directly, since both unfold by a plain `def`-chain to `lowerGateRec
(standardSignedPhaseLoweringPlan …)`, exactly R6.2's own theorem target —
confirmed by reading `PhaseProduct/Lowering/Lower.lean`, not yet stated as a
lemma), a "qft" leaf-bridging lemma using the register wiring above, Steps
1/2/4(`mul`,`†mul`)/5 assembled from those two pieces (mirroring `shor_gate`'s
already-proved Steps 1/2/4/5 leaf-for-leaf, one level lower), Step 3
(`CmpGeConst`/`CSubConst` lowering — direct translation, no new leaf-bridging
needed, should be the most mechanical of the five), the `modExpApproxValid`
loop-body assembly (should transplant `evalNodeGate_modExpLoop_aux`'s
induction near-verbatim, swapping `evalNodeGate`/`Gate` for `evalNode`/
`LowGate`), and the top-level `H_reg`/`initY1`/loop/`IQFT` assembly. Net
assessment: comparable in *volume* to the entire `shor_gate` effort (§12.9–
§12.11), since every one of `shor_gate`'s already-proved leaves needs a
LowGate-level counterpart — but with the two hardest new ingredients (the
doc-independence bridge and the register-wiring resolution above) now
already worked out, what remains is the same kind of leaf-by-leaf assembly
`shor_gate` needed, not a new kind of difficulty.

**Verification, this round**: `lake build EmitProofs` → `Build completed
successfully (3321 jobs)`; `grep -c sorry Proofs/Shor.lean` → `0`;
`#print axioms Shor.IR.evalNode_dind` → `[propext, Classical.choice,
Quot.sound]`. `Proofs/Shor.lean` now imports `Proofs/PhaseProduct.lean`/
`Proofs/CPhaseProduct.lean`/`Proofs/Qft.lean` (previously only
`Proofs/Correct.lean`/`Emit/Tests.lean`) — this exposed one real naming
collision, not a proof bug: `Proofs/PhaseProduct.lean` declares its own
general `Shor.IR.ExtReg.capacity_grow (e : ExtReg) (n : ℕ) : (e.grow
n).capacity = e.capacity - n` (unconditional), which now shadows
`ShorVerification`'s `Shor.ExtReg.capacity_grow` (the one `CanGrow`-gated
version §12.10's Step 2 work needed) under `Shor.lean`'s `open Shor
Shor.IR` — fixed by fully qualifying the one call site that needed the
`ShorVerification` version (`Shor.ExtReg.capacity_grow` instead of the bare,
now-ambiguous name); nothing about the already-verified Step 1/2 theorems
changed.

### 12.13 R6.4 `shor` half: `evalNode_ind` (doc *and* env indifference), a second required bridge — proved and merged; leaf assembly still not started

§12.12 found and closed the *first* gap between `shor`'s `.call` sites and
R6.2/R6.3's theorems (`evalNode_dind`, doc-independence — do `d1`/`d2` agree
on template lookup?). This round found a **second, independent gap** at the
same `.call` sites, closed it the same way (a general, proved, merged
lemma), and got as far as fully working out — but not yet committing — the
two-environment technique the leaf assembly itself needs. Still a "round of
research findings" entry, not a closing one for `shor`.

**The second gap.** `evalNode_dind` alone is not enough to reuse
`r2_4_doc_cphase_product_correct` (etc.) at a `shor`-internal `.call`
site, because `Env.call` (`IR/Instantiate.lean`) rebuilds only `w`/`a`/`r`
fresh from the callee template's own parameter list — `opaqueW`/`coeff` are
carried over **unchanged** from the caller's env (`{env with w := …, a :=
…, r := …}`, no `opaqueW`/`coeff` field touched). `shor`'s calling env,
`Emit/Tests.lean`'s `r2_6_env`, has a strictly larger `opaqueW` match (it
needs `"mod"`/`"pow"`/`"modpow"`/`"step5Const"`/`"log2"`/`"qftXWork"`/
`"qftZWork"` on top of `"nextWidth"`/`"reserveNeed_x"`/`"reserveNeed_z"`,
since it also serves `shor_gate`'s own needs) than `ppEnv`/`cppEnv`/
`qftEnv`'s three-case `opaqueW`. Per `Proofs/Qft.lean`'s own already-recorded
finding (`qftEnv_opaqueW_eq_ppEnv`'s docstring: "a function with more
pattern-match arms is a different closure, even where the arms overlap"),
this means `Env.call`'s result at a `shor`-internal `.call "cphase_product"`
site is genuinely **not** `rfl`/`funext`-equal to `cppEnv ctrl x z phi` as a
whole `Env` value — only its `w`/`a`/`r` projections are (confirmed
separately, see below); `opaqueW` differs at inputs `cphase_product` never
queries (`"mod"`, `"pow"`, …) but is otherwise the same function.

**The fix, mirroring `evalNode_dind`'s own shape exactly.** Since a `Doc`'s
evaluator only ever touches `opaqueW`/`coeff` by *applying* them at specific
`(name, args)` pairs — never by comparing them as whole functions — the same
"agree on what's actually queried, and the reachable call graph never
queries outside that set" argument that justified swapping `Doc`s justifies
swapping `opaqueW`/`coeff` too. Built and merged into `Proofs/Shor.lean`,
each independently `#print axioms`-verified clean, no `sorry`:
- `Node.opaqueNames`/`WExpr.opaqueNames`/`AExpr.opaqueNames`/
  `RegExpr.opaqueNames`/`Prop'.opaqueNames`: the syntactic-occurrence
  counterpart of `Node.callNames`, one per IR type, collecting every
  `.opaque fn _` name literally written in the expression (not unrolling
  `.call` — same "closure handles recursion, occurrence-collection doesn't"
  split as `Node.callNames`/`evalNode_dind`'s `hclosed`).
- `evalW_oind`/`evalWList_oind_aux`: `evalW`'s own opaqueW-indifference,
  proved *first* and separately, since `WExpr.opaque`'s `List WExpr` nesting
  needs the same `Nat.strong_induction_on (sizeOf ·)` treatment as `Node`
  (no `induction`/`cases` tactic) — this piece has **no fuel dimension at
  all** (unlike `evalNode`, `evalW` doesn't recurse through `.call`), so
  it's a single-measure induction, simpler than `evalNode_dind`'s.
  `evalWList_oind_aux` had to be factored out as its *own* recursive
  definition (not inlined via a generic `List.mapM_congr'` call) after a
  first attempt at inlining hit exactly the "recursive call mediated
  through an external helper loses the auto-introduced membership
  hypothesis `decreasing_by` needs" problem §12.12 already flagged for
  `evalNode_dind`'s own construction — confirming that's a *general* trap
  for this codebase's `List Self`-nested types, not a one-off.
- `evalA_oind`/`evalReg_oind`/`evalProp_oind`: the same fact for `AExpr`/
  `RegExpr`/`Prop'`, each by the *ordinary* `induction e with …` tactic
  (these three types have no nested-list occurrence, confirmed directly by
  attempting `induction`/`cases` — no obstacle, unlike `Node`/`WExpr`), using
  `evalW_oind` as a black box wherever a `WExpr` subterm appears. One Lean
  quirk hit and worked around: the `AExpr.neg` constructor's case tag in
  `induction … with | neg a ih => …` fails to parse ("unexpected token
  `neg`", though the *error message itself* still asks for exactly `neg` as
  the expected alternative name) — `neg` collides with a reserved parser
  token; escaping it as `` | «neg» a ih => … `` (Lean's guillemet syntax for
  using a keyword as a plain identifier) fixes it with no other change.
- `evalNode_ind`: the combined result, `Node`-level, by the same nested
  `Nat.strong_induction_on (fuel)` then `Nat.strong_induction_on (sizeOf
  node)` skeleton as `evalNode_dind`, now threading `env1 env2 : Env`
  through the induction too (universally re-quantified at every recursive
  step, *not* fixed parameters of the outer theorem — an early draft fixed
  them at the top and only discovered the mistake when the `.loop`/`.call`
  cases' recursive calls needed the theorem to hold at the `bindW`-extended/
  `Env.call`-rebuilt envs, not the original pair). `opaqueW`/`coeff` are
  instead carried as **named functions** (`opaqueW1 opaqueW2 : String →
  List ℕ → Option ℕ`, `coeff1 coeff2 : ℕ → ℕ → Option ℚ`) with `env1.opaqueW
  = opaqueW1` (etc.) as a hypothesis re-derivable in one line at every
  `bindW`/`Env.call` step (`Env.bindW` never touches `opaqueW`/`coeff`;
  `Env.call`'s `{env with w:=…,a:=…,r:=…}` doesn't either) — this is what
  lets the *same* top-level `hop`/`hcoeff` proof keep working arbitrarily
  deep into the recursion without re-proving anything.

**The leaf-assembly technique this unlocks (worked out, not yet a
committed lemma).** A `shor`-internal `.call "cphase_product" wArgs aArgs
rArgs` node cannot be bridged to `r2_4_doc_cphase_product_correct` by a
*single* `evalNode_ind` application with `env1 :=` (the real calling env)
and `env2 := cppEnv ctrl x z phi` directly — tried first, and it doesn't
typecheck: `evalNode_ind`'s own hypotheses are about `env1`/`env2`
*themselves*, evaluated at `wArgs`/`aArgs`/`rArgs` to produce `Env.call`'s
inputs, and if `env2 := cppEnv ctrl x z phi` from the very top, `env2.w`
already disagrees with `env1.w` (`cppEnv`'s `w` only knows `"xw"`/`"zw"`/
`"xCap"`/`"zCap"`, not `shor`'s `"xW"`/`"workW"`/…), breaking `hw` long
before reaching the `.call`. The fix is a **hybrid env**: `env2 :=
{env1 with opaqueW := (cppEnv _ _ _ _).opaqueW, coeff := (cppEnv _ _ _
_).coeff}` — identical to the real calling env in `w`/`a`/`r` (so `hw`/`ha`/
`hr` are `rfl`), but with `cppEnv`'s `opaqueW`/`coeff` already installed
(so `hop`/`hcoeff` are the `hop_cpp`-style pointwise facts below, and *not*
`rfl`-blocked by `cppEnv`'s narrower match). `cppEnv`'s `opaqueW`/`coeff`
fields don't depend on their own `ctrl`/`x`/`z`/`phi` arguments at all, so
`(cppEnv _ _ _ _).opaqueW` is well-defined without committing to values
yet. `evalNode_ind` at `(env1, env2)` this way gives `evalNode r2_6_doc
fuel env1 node = evalNode r2_4_doc fuel env2 node`; since `env2`'s `w`/`a`/
`r` still equal `env1`'s, `env2`'s *behavior* at the `.call` node's own
`wArgs`/`aArgs`/`rArgs` matches whatever was already established about
`env1` (`hctrl`/`hx`/`hz`/`hphi`-style facts, same as `shor_gate`'s), and
after `Env.call` rebuilds `env2`'s `w`/`a`/`r` fresh from the callee's
params, `evalNode_dind`/`envcall_cpp_*_eq`'s combination identifies the
result with `evalNode r2_4_doc fuel' (cppEnv ctrl X Z phi) r2_4_cppBody`
exactly. Confirmed piece-by-piece, not yet assembled into one theorem
(see below).

**Established and independently verified this round** (`grep -c sorry` →
`0`, `lake build EmitProofs` → green, `#print axioms` clean on each):
- `envcall_cpp_w_eq`/`_a_eq`/`_r_eq`: `Env.call env ["xw","zw","xCap","zCap"]
  [X.width,Z.width,X.capacity,Z.capacity] ["phi"] [phi] ["ctrl","x","z"]
  [C,X,Z]`'s `w`/`a`/`r` fields equal `cppEnv C X Z phi`'s, for arbitrary
  `env` — proved via two new general helper lemmas worth keeping,
  `List.lookup_eq_ite1`/`_ite2`/`_ite3`/`_ite4` (an *n*-key association-list
  lookup unfolds to the expected `if`-chain, for 1–4 keys — covers every
  `wParams`/`aParams`/`rParams` list length these templates use), proved by
  `cases h : n == kᵢ <;> …  <;> simp_all` (**Bool** `cases`, not `by_cases`
  on the `Prop` form — the latter leaves the `match _==_ with` scrutinee
  from `List.lookup`'s own equation lemma unrewritten, since `split_ifs`
  only recognizes literal `ite`/`dite` terms, not the bare `match` shape
  `List.lookup`'s recursion actually produces; `cases` on the `Bool`
  expression directly sidesteps needing that conversion at all).
- `hop_cpp`: `r2_6_env`'s `opaqueW` agrees with `cppEnv`'s at
  `"nextWidth"`/`"reserveNeed_x"`/`"reserveNeed_z"` for every argument list
  — by `fin_cases` on the name then `rcases`-on-the-args `rfl` (both sides'
  formula is literally `RecursivePhaseWorkspace.nextWidth/reserveNeed
  r2_6g_ops/r2_4_ops xw zw`, and `r2_6g_ops = r2_4_ops` is `rfl`, already
  established in §12.12 for the `.call`-target-lookup identity — the *same*
  `ops` identity turns out to be exactly what's needed for the opaque-value
  identity too). `coeff` needed no restriction at all: `r2_6_env.coeff =
  cppEnv/ppEnv/qftEnv.coeff` holds **fully**, by plain `rfl`, for every
  target — unlike `opaqueW`, `coeff`'s formula has no extra match arms in
  `r2_6_env` (it's the same single `if l < q 2 then … else none` in every
  env this project defines), so there is no "different closure" problem
  for `coeff` at all.
- `hnames_cpp`/`hclosedC_cpp`/`hclosedO_cpp`: `r2_6_doc`'s "cphase_product"/
  "naive_cleaf" templates agree with `r2_4_doc`'s (§12.12's `rfl` fact,
  restated as a `fin_cases`-closed `∀ n ∈ names, …`), and `r2_4_cppBody`'s
  own `callNames`/`opaqueNames` stay inside `{"cphase_product",
  "naive_cleaf"}`/`{"nextWidth","reserveNeed_x","reserveNeed_z"}` — checked
  by `native_decide` (plain `decide` times out / gets stuck on `String`
  equality's kernel reduction at this size, confirmed directly; `#eval`
  first, to see the actual — much smaller than it looks from the AST size —
  deduplicated name lists, then `native_decide` to discharge the `⊆` fact
  the induction actually needs).

**Not yet started**: assembling the pieces above into one closed
`evalNode_call_cphase_product`-style leaf lemma (the last step — combining
`evalNode_ind` at the hybrid env with `r2_4_doc_cphase_product_correct` —
was reached but not finished this round), then the *same* pattern for
`"phase_product"` (3 call sites) and `"qft"` (9 call sites, plus the
register-wiring resolution already recorded in §12.12), Step 3's direct
`CmpGeConst`/`CSubConst` translation (no `.call`, should be the most
mechanical of the five steps, same shape as `shor_gate`'s own Step 3 one
level lower), the `modExpApproxValid` loop-body assembly (expected to
transplant `evalNodeGate_modExpLoop_aux`'s induction near-verbatim,
`evalNode`/`LowGate` in place of `evalNodeGate`/`Gate`), and the top-level
`H_reg`/`initY1`/loop/`IQFT` assembly. Net assessment, updated from §12.12:
the *scale* is still "comparable to the whole `shor_gate` effort," but the
count of genuinely *new* obstacle types this pass has now found and closed
is three (doc-independence, env/opaqueW-independence, the hybrid-env
leaf technique) — every one now a proved, general, reusable lemma or a
confirmed technique, not an open question. What remains is applying the
established `evalNode_call_<name>` pattern 14 times (mechanical but not
short) plus the four structural-assembly pieces above, none of which need
further new machinery beyond what `shor_gate` and this round already built.

### 12.14 R6.4 `shor` half: first leaf theorem closed (`evalNode_call_cphase_product`), `native_decide` removed

§12.13 left the hybrid-env leaf technique fully worked out but not yet
assembled into a closed theorem, and its `hclosedC_cpp`/`hclosedO_cpp`
closure facts leaning on `native_decide` (flagged there as a stopgap:
"`native_decide` … plain `decide` times out / gets stuck"). This round
closed both gaps: `evalNode_call_cphase_product` is now a fully-assembled,
merged, `native_decide`-free leaf theorem — the **first** of the 14
`.call`-site leaves `shor`'s theorem needs, and the one that validates the
whole pipeline end-to-end for the first time.

**Assembly.** `evalNode_call_cphase_product` (`Proofs/Shor.lean`, appended
after `evalNode_ind`) takes the hybrid env `env2 := {env1 with opaqueW :=
(cppEnv C X Z phi).opaqueW, coeff := (cppEnv C X Z phi).coeff}` from §12.13,
applies `evalNode_ind` to get `evalNode r2_6_doc fuel env1 node = evalNode
r2_4_doc fuel env2 node` at the `.call "cphase_product" …` node, rewrites
the RHS one fuel step through `evalNode`'s `.call` case using
`evalW_oind`/`evalA_oind`/`evalReg_oind` to carry `hwx`/`hwz`/`hphi`/`hctrl`/
`hx`/`hz`-style facts from `env1` to `env2` (opaqueW-independence applies
here too — the *argument expressions* `wxR`/`phiR`/etc. are themselves
opaque-free, `hOwx`/`hOphi`/… hypotheses), identifies the resulting
`Env.call env2 [...] r2_4_cppBody` with `cppEnv C X Z phi`/`r2_4_cppBody` via
`envcall_cpp_w_eq`/`_a_eq`/`_r_eq` (§12.13) plus the `opaqueW`/`coeff` fields
(already `rfl`-equal by `env2`'s own construction) — destructured via `cases
… with | mk … =>` on both sides to combine five separately-proved field
equalities into one whole-`Env` equality — and closes with
`r2_4_doc_cphase_product_correct` directly. One new wrinkle not in §12.13's
preview: `phaseInputSize X Z < fuel` (the natural hypothesis) isn't quite
enough once `fuel = fuel' + 1` is peeled off for the `.call` step; the
theorem's hypothesis is stated as `phaseInputSize X Z + 1 < fuel` instead,
with the needed bound re-derived by `omega` at the call site.

**The `native_decide` fix.** `hclosedC_cpp`/`hclosedO_cpp` need `Node.callNames
r2_4_cppBody ⊆ cpp_names` and `Node.opaqueNames r2_4_cppBody ⊆ cpp_oNames`.
Confirmed directly (a minimal 2-leaf example) that neither `Node.callNames`
nor `Node.opaqueNames` reduces via `rfl`/`decide` in the kernel — both
compile via well-founded recursion over the `List Node`/`List WExpr` nesting,
a known Lean 4 kernel-reduction limitation — so `decide` gets stuck and the
original draft reached for `native_decide`, which was then caught by this
project's own R6.2 exit criterion (no `Lean.ofReduceBool`/`Lean.trustCompiler`
axioms: confirmed via `#print axioms` showing exactly those two extra axioms
before the fix). Both closure facts are now proved without it:
- `r2_4_cppBody_callNames_sub`: chains through `r2_4_cppBody`'s own
  already-established ground-truth `_eq` lemmas (`r2_4_cppBody_eq_cond`,
  `r2_4_cppThen_eq_seq`, `r2_4_cppElse_eq`, `r2_4_ppAlloc_eq`,
  `r2_4_ppRest_eq_seq`, `r2_4_ppDealloc_eq`, `r2_2_ppDealloc_eq`,
  `r2_4_ppBodyNode_eq`, `r2_2_ppAlloc_eq`) via `rw`/`unfold`, exposing
  concrete `Node` constructors one layer at a time so `simp only
  [Node.callNames, …]`'s *equation lemmas* fire (they do fire once the
  scrutinee is a literal constructor — the kernel-reduction obstacle is only
  for fully-automatic `whnf`/`decide`, not for `simp`'s targeted rewriting),
  then `intro z hz; simp_all` closes the final membership goal.
- `r2_4_cppBody_opaqueNames_sub`: same chaining technique, but
  `Node.opaqueNames`'s dependency chain is much deeper (`nextWidthW`/
  `limbW`/`reserveNeedXW`/`reserveNeedZW`/`r2_2_offsetX1W`/`r2_2_sizeX1W`/
  `r2_2_offsetZ1W`/`r2_2_sizeZ1W`/`r2_2_growDeltaX0W`–`Z1W`, each nested
  inside others, and several call sites repeat the same sub-expressions). A
  first attempt closing the fully-unfolded goal with `intro z hz; tauto` hit
  a **deterministic timeout at `whnf`** even with `maxRecDepth 4000` and
  `maxHeartbeats 1000000` raised — the final disjunction has 50+ terms once
  everything is flattened, and `tauto`'s search does not scale linearly in
  disjunct count. Fixed by abandoning element-level case analysis for
  list-structural subset-splitting: `simp only [List.append_subset]` turns
  an `(l1 ++ l2) ⊆ l3` goal into a conjunction tree *without* introducing any
  `z`/membership reasoning (pure structural rewriting, cheap regardless of
  size), `repeat' apply And.intro` flattens the tree into independent leaf
  goals with no need to know the exact nesting shape in advance, and
  `all_goals (first | exact List.nil_subset _ | exact <one of eight small
  per-subexpression ⊆-lemmas> | (intro a ha; simp_all [cpp_oNames] <;>
  tauto))` closes each leaf — `tauto` now only ever runs on tiny (2–4
  disjunct) per-leaf goals instead of the one global 50-term goal, and the
  whole proof runs in seconds. The eight per-subexpression lemmas
  (`nextWidthW_opaqueNames_eq`, `limbW_opaqueNames_eq`,
  `reserveNeedXW_opaqueNames_eq`, `reserveNeedZW_opaqueNames_eq`,
  `r2_2_offsetX1W_opaqueNames_sub`, `r2_2_sizeX1W_opaqueNames_sub`,
  `r2_2_offsetZ1W_opaqueNames_sub`, `r2_2_sizeZ1W_opaqueNames_sub`) are each
  proved the same way, small enough that plain `tauto` on their own final
  goals is fine — the blowup was specifically a function of running `tauto`
  once on the *fully assembled* 50-term goal, not of the individual facts.
- The `"naive_cleaf"` branch of `hclosedC_cpp`/`hclosedO_cpp` (the other
  name in `cpp_names`) needed the same treatment made explicit: unfolding
  `Reflect.naiveCLeafTemplate`'s body via `simp only [Reflect.naiveCLeafTemplate,
  Node.callNames/opaqueNames, …]` reduces the membership hypothesis to `n' ∈
  ([] : List String)`, closed by `cases hn'` — previously folded silently
  into the `native_decide` call and had to be split out as its own step.

**Result.** `evalNode_call_cphase_product` merged into `Proofs/Shor.lean`
(after `evalNode_ind`, before `end Shor.IR`), along with `cpp_names`/
`cpp_oNames`, `hnames_cpp`, `r2_4_cppBody_callNames_sub`/
`_opaqueNames_sub` and their eight helper lemmas, `hclosedC_cpp`/
`hclosedO_cpp`, `envcall_cpp_w_eq`/`_a_eq`/`_r_eq`, `hop_cpp`, `hcoeff_cpp`.
`lake build EmitProofs` succeeds (3321 jobs, only pre-existing-style unused-
simp-arg lint warnings, zero errors). `grep -c sorry` on the file is 0; grep
for `native_decide`/`Lean.ofReduceBool`/`Lean.trustCompiler` finds none in
actual code (only in this section's own prose, describing the fix).
`#print axioms evalNode_call_cphase_product` → `[propext, Classical.choice,
Quot.sound]`, clean.

**Net assessment.** This closes the "not yet started: assembling the pieces
above into one closed leaf theorem" gap §12.13 left open, and confirms the
hybrid-env + `evalNode_ind` + kernel-clean-closure technique is a *working,
reusable template* — not just a plan. What remains unchanged in kind from
§12.13's assessment: 13 more `.call` sites need the identical pattern
applied (1 more `cphase_product` at Step 5, 3 `phase_product` at Steps 2/
4mul/4†mul, 9 `qft`), each needing its own `hop_<name>`/`hcoeff_<name>`/
`envcall_<name>_*_eq`/`hclosedC_<name>`/`hclosedO_<name>` instantiated for
that template (mechanical, following this round's file line-for-line, but
not short — the `callNames`/`opaqueNames` closure lemmas in particular are
the most labor-intensive part per site since each template's dependency
chain differs), then Step 3 (`CmpGeConst`/`CSubConst`, no `.call`/leaf
machinery needed at all) and the `modExpApproxValid` loop/top-level assembly.

### 12.15 R6.4 `shor` half: second leaf theorem closed (`evalNode_call_phase_product`) — a correction to §12.14's "13 more sites" count

§12.14 framed the remaining work as "13 more `.call` sites need the
identical pattern applied." Building the second leaf theorem this round
surfaced that framing was **counting the wrong thing**: `evalNode_call_phase_product`
(mirroring `evalNode_call_cphase_product` exactly, target
`evalNode_phase_product_correct` from `Proofs/PhaseProduct.lean` instead of
`r2_4_doc_cphase_product_correct`) is fully **generic** in its register/weight/
angle-expression arguments (`xR zR wxR wzR wxCapR wzCapR phiR`, all
universally quantified, plus opaqueNames-empty/eval hypotheses about them) —
it is not tied to any one concrete call site's argument expressions. One
theorem per **template name**, not per call site, covers every `.call
"<name>" …` site using that name anywhere in `shor`'s body, as long as the
site-specific hypotheses (the `evalReg`/`evalW`/`evalA` facts, workspace
precondition, fuel bound) are separately established at each site during the
top-level assembly. So the real remaining count of *new leaf theorems* was
never 13 — it was **2**: one generic `evalNode_call_phase_product` (covering
Step 2, Step 4's `mul`, and Step 4's `†mul` — all 3 `phase_product` sites at
once) and one generic `evalNode_call_qft` (covering all 9 `qft` sites). Both
`cphase_product` call sites (Steps 1 and 5) are already covered by
`evalNode_call_cphase_product` from §12.14, with no second lemma needed.
"13 more sites" remains an accurate count of how many *site-specific
hypothesis packages* the final top-level assembly step must supply — that
work doesn't disappear — but it is not 13 more leaf-lemma-engineering
rounds; it is 1 more (`qft`), then assembly.

**What was built.** `evalNode_call_phase_product` (`Proofs/Shor.lean`,
appended after `evalNode_call_cphase_product`), plus its supporting
`pp_names := ["phase_product", "naive_leaf"]`, `hnames_pp`,
`r2_2_ppBody_callNames_sub`/`_opaqueNames_sub`, `hclosedC_pp`/`hclosedO_pp`,
`envcall_pp_w_eq`/`_a_eq`/`_r_eq`, `hop_pp`, `hcoeff_pp` — the exact same
eleven-lemma shape as `cphase_product`'s leaf, with `cppEnv`/`r2_4_*`
replaced by `ppEnv`/`r2_2_*` throughout and the `ctrl`-related hypotheses
dropped (`phase_product`'s `rParams = ["x","z"]`, no control qubit). One
structural wrinkle, not present in `cphase_product`'s case: `phase_product`'s
own body (`r2_2_ppBody`) is **self-recursive** — its `.cond`'s else-branch
calls `"naive_leaf"` (the base case) but its then-branch contains 3 internal
`.call "phase_product"` leaves (the recursive step `evalNode_phase_product_correct`
itself inducts over) — so `pp_names` contains `"phase_product"` itself, and
`hclosedC_pp`/`hclosedO_pp`'s `"phase_product"` branch is self-referential
(unproblematic: the closure argument only requires the callee's own
`callNames`/`opaqueNames` stay inside the declared set, which self-reference
trivially satisfies once established). A second reuse discovery: `r2_2_ppBody`
shares its allocation/deallocation subtree and every `nextWidthW`/
`reserveNeedXW`/`reserveNeedZW`/`r2_2_offsetX1W`–`r2_2_sizeZ1W` opaque-name
helper fact with `r2_4_cppBody` (§12.14 already found `cphase_product`
reuses `phase_product`'s chunk-0/1 allocation machinery directly) — so
`r2_2_ppBody_opaqueNames_sub`'s target set is `cpp_oNames` again (unchanged,
same three names) and **all eight** `opaqueNames`-closure helper lemmas from
§12.14 (`nextWidthW_opaqueNames_eq` through `r2_2_sizeZ1W_opaqueNames_sub`)
were reused verbatim, zero new helper lemmas needed for this round beyond
the top-level `r2_2_ppBody_callNames_sub`/`_opaqueNames_sub` pair itself. The
proof assembled and closed on the **first attempt** after fixing three small
mechanical slips (a missing `rw [r2_2_ppAlloc_eq]`/`r2_2_ppGuard_eq` step
each, and two `rw […]` calls that needed `at hn'` and were instead — wrongly
— rewriting the goal) — the `List.append_subset` + `repeat' apply And.intro`
+ per-leaf `all_goals first | …` technique from §12.14 scaled to this body
with no further tuning.

**Result.** `lake build EmitProofs` succeeds (3321 jobs, only unused-simp-arg
lint warnings, zero errors). `grep -c sorry` is 0; no `native_decide`/
`Lean.ofReduceBool`/`Lean.trustCompiler` in actual code. `#print axioms
evalNode_call_phase_product` → `[propext, Classical.choice, Quot.sound]`,
clean.

**Net assessment.** Two of the three needed generic leaf theorems
(`cphase_product`, `phase_product`) are done; `qft` remains as the third and
last. Once `qft`'s leaf theorem closes, all `.call`-site leaf-lemma
engineering for `shor` is finished, and everything remaining is Step 3
(`CmpGeConst`/`CSubConst`, no leaf machinery) plus the top-level assembly:
supplying each of the 14 concrete call sites' site-specific hypotheses and
composing the pieces the same way `shor_gate`'s own Steps 1–5/loop/top-level
assembly (§12.9–§12.11) already did one level higher (`evalNodeGate` instead
of `evalNode`).

### 12.16 R6.4 `shor` half: third and last leaf theorem closed (`evalNode_call_qft`) — all `.call`-site leaf-lemma engineering done

`evalNode_call_qft` (`Proofs/Shor.lean`, appended after `evalNode_call_phase_product`)
closes R6.4's leaf-lemma phase: the same hybrid-env + `evalNode_ind`
technique as §12.14/§12.15, target `evalNode_qft_correct` (`Proofs/Qft.lean`,
R6.3's closed theorem). Two structural differences from the first two
leaves, both handled without new machinery: `qft` has no angle parameter
(`aParams = []`), so there is no `phi`/`hphi`/`hOphi` anywhere in this
theorem — `Env.call`'s `a` field for an empty `aParams`/`aVals` pair is
`fun n => ([].zip []).lookup n`, definitionally `fun _ => none`, matching
`qftEnv`'s `a` field by plain `rfl` (`envcall_qft_a_eq` is a one-line
`funext n; rfl`, no case split needed at all, unlike `_w_eq`/`_r_eq`). And
`qft`'s closure set needs **three** names, not two: `qft_names := ["qft",
"phase_product", "naive_leaf"]` — `qft` is self-recursive on two of its four
split leaves (`r2_5_qftRight`/`r2_5_qftLeft`, both `.call "qft" …`,
`lowerQFTPlan`'s left/right recursion) and embeds one `.call "phase_product"`
leaf (`r2_5_qftPhase`, the split's middle chunk, `Qft.lean`'s own header
comment already flagged this: "the middle of each split is an embedded
unsigned phase product … discharges it by citing `evalNode_phase_product_correct`
… as a black box"), so `"phase_product"` and (transitively, through it)
`"naive_leaf"` both had to join the closure set — `hclosedC_qft`/`hclosedO_qft`'s
`"phase_product"` branch reuses `r2_2_ppBody_callNames_sub`/`_opaqueNames_sub`
from §12.15 directly rather than restating them, just weakening `pp_names ⊆
qft_names` (`{"phase_product","naive_leaf"} ⊆ {"qft","phase_product","naive_leaf"}`,
one `tauto` call). A discovery that simplified the `opaqueNames` side
further than either prior leaf: `r2_5_qftBody`'s own syntactic structure —
every leaf *outside* the two `.call`s (`RadixReverse`, `zeroExtend`/
`zeroDealloc`, the three guards) — references **no** `.opaque` name at all;
every `w`/`r` expression in `qft`'s own body is built purely from `.var`/
`.lit`/`.div`/`.sub`/`.add`. So `r2_5_qftBody_opaqueNames_sub` closes by
unfolding straight down to `List.nil_subset`, no `List.append_subset`/
`repeat' apply And.intro`/per-leaf-lemma machinery needed at all (unlike
`r2_4_cppBody_opaqueNames_sub`/`r2_2_ppBody_opaqueNames_sub`, both of which
needed the full technique) — `cpp_oNames` is still the right closure target
only because of what the *embedded* `phase_product` leaf transitively
reaches (`r2_2_ppBody_opaqueNames_sub`, reused unchanged), not because of
anything in `qft`'s own leaves. The whole proof (all four closure lemmas,
then the full leaf theorem) closed after fixing one small syntax slip: a
`set env2 : Env := { env1 with …, … }` written with the two struct-update
fields split across two lines (rather than both on the line with the
opening `{`, `with henv2` alone on the continuation) parses but silently
drops the second field from the elaborated term and reports an unrelated-
looking "unexpected identifier; expected `}`" one line later — reverting to
the exact one-line-then-`with` layout §12.14/§12.15 already used fixed it
immediately; not a new technique, just a reminder to copy the working
layout verbatim rather than reflowing it.

**Result.** `lake build EmitProofs` succeeds (3321 jobs, only unused-simp-arg
lint warnings, zero errors). `grep -c sorry` is 0; no `native_decide`/
`Lean.ofReduceBool`/`Lean.trustCompiler` in actual code. `#print axioms
evalNode_call_qft` → `[propext, Classical.choice, Quot.sound]`, clean — and
re-checked alongside the other two, all three still clean together.

**Net assessment.** All three needed generic leaf theorems
(`evalNode_call_cphase_product`, `evalNode_call_phase_product`,
`evalNode_call_qft`) are now closed and merged, covering all 14 of `shor`'s
`.call` sites (2 `cphase_product` + 3 `phase_product` + 9 `qft`) between
them. `shor`'s R6.4 leaf-lemma-engineering phase is **done**. What remains,
unchanged in kind from every prior round's assessment: Step 3's direct
`CmpGeConst`/`CSubConst` translation (no `.call`, no leaf machinery — the
most mechanical of the five steps, same shape as `shor_gate`'s own Step 3
one level lower, already closed in §12.11), the `modExpApproxValid`
loop-body assembly (expected to transplant `evalNodeGate_modExpLoop_aux`'s
induction near-verbatim, `evalNode`/`LowGate` in place of `evalNodeGate`/
`Gate`), and the top-level `H_reg`/`initY1`/loop/`IQFT` assembly — supplying
each of the 14 concrete call sites' own register/weight-expression
arguments and site-specific hypotheses (workspace preconditions, fuel
bounds, `evalReg`/`evalW`/`evalA` facts) to the now-generic leaf theorems
and composing the results, exactly mirroring how `shor_gate`'s own Steps
1–5/loop/top-level assembly (§12.9–§12.11) did the same one level higher
(`evalNodeGate`/`Gate` instead of `evalNode`/`LowGate`).

### 12.17 R6.4 `shor` half: Step 3 core infrastructure — `LowGate.flattenSeqAdj` (a required new equality notion) and the bit-copy loop lemma, both closed; the full Step 3 assembly not yet started

Starting Step 3 (`CmpGeConst`/`CSubConst`) surfaced a **genuinely new
representational obstacle**, not present anywhere in R6.1–R6.3 or in
`shor_gate`'s own Steps 1–5 (§12.9–§12.11): `LowGate`-level adjoints don't
compare the way `Gate`-level ones do, and the fix is a new equality notion
(`LowGate.flattenSeqAdj`) that every future `.adj`-touching piece of `shor`'s
LowGate theorem (Step 3, Step 4's `†diff`/`†mul`, the top-level `IQFT`) will
need to use in place of plain `.flattenSeq`.

**Ground truth first.** `translateLowerGate`'s own comment (`Reflect/Extract.lean`,
already read in §12.12 but not fully appreciated until this round) says
`lowerCmpGeConst`/`lowerCSubConst` are "plain (non-tactic-mode) `def`s" that
`translateNode`'s ordinary `unfoldDefinition?` fallback inlines directly —
**no `.call` splicing at all** for Step 3, unlike every other recursive
target R6.4 has handled so far. Ground-truthing `r2_6_step3` (`r2_6_doc`'s
"shor" template body, decomposed the same `.seq`/`.loop` `def`+`rfl` way as
`r2_6g_sgBody`'s own Steps 1–5, §12.9) confirms this exactly matches
`ConstArithmetic.lean`'s `lowerCmpGeConst`/`lowerCSubConst`/
`lowerPrepareNegConst`/`lowerCopyBitPowers` structure, inlined verbatim —
with one translated piece: `lowerCopyConstFromUnit N dst ctrl :=
lowerCopyBitPowers dst ctrl N.bitIndices` (the controlled binary-constant
write) is recognised **by name** (`translateNode`'s own case for it,
`Extract.lean` line ~1217) and reformulated as `.loop "i" 0 dstW (.cond
(.testBit N i) (.op "CNOT" …) (.op "id" …))` — a genuinely new IR construct
(`Prop'.testBit`, added specifically for this) needing its own correctness
bridge, since `Nat.bitIndices`-driven recursion (skip unset bits entirely)
and "iterate every position, guard on `testBit`" (my loop) are *not* the
same raw shape, only equal as circuits.

**Obstacle 1 (structural, worked around): `lowerCopyBitPowers` vs the
extracted loop, a combinatorial correspondence not needed anywhere earlier
in R6.** `ConstArithmetic.lean`'s own `mem_bitIndices_iff_testBit` (the exact
fact needed: `i ∈ N.bitIndices ↔ N.testBit i`) is `private`, so re-proved
here from public Mathlib primitives (`Nat.binaryRec`, `Nat.bitIndices_bit_true`/
`_bit_false`, `Nat.testBit_succ`) — same induction shape as the private
original, ~20 lines. Combined with `Nat.two_pow_le_of_mem_bitIndices` (public)
to get `i ∈ N.bitIndices → i < w` whenever `N < 2^w` (`ConstArithmeticWorkspace`'s
own `constant_fits : N < 2^(scratch.width - 1)` guarantees this at the real
call sites), then `(range w).filter testBit = N.bitIndices` follows from
both being ascending-sorted lists with the same membership set
(`List.SortedLT.eq_of_mem_iff` — note this project's Mathlib checkout has
already migrated `List.Sorted r l` to the newer `List.SortedLT`/`SortedLE`
API, `sorted_lt_range`/`Sorted.eq_of_mem_iff` etc. all deprecated in favor of
`sortedLT_range`/`SortedLT.eq_of_mem_iff` — worth remembering for anyone
reaching for the old names). `lowerCopyBitPowers_flattenSeqAdj` (a clean
induction, since every one of `N.bitIndices`' positions is `< dst.width` by
the bound above, so the `dif`-guarded skip branch never actually fires) then
gives `lowerCopyBitPowers dst ctrl N.bitIndices`'s value as a flat
`.map CNOT` list, matching the loop's own (proved separately,
`evalNode_copyConstLoop`, ordinary `List.mapM_except_ok_of_mem` +
per-iteration `.cond`/`testBit` case split, `List.getD`/`getElem` qubit-index
bookkeeping mirroring `Correct.lean`'s own `evalNode_naive_leaf`/
`evalNode_naive_cleaf` idiom throughout) once both are expressed as
`filterMap`/`filter`-over-`range` forms tied together by the combinatorial
fact above.

**Obstacle 2 (representational, the real finding of this round): raw
`LowGate.flattenSeq` cannot compare `.adj`-wrapped values that came from
different derivations, even when their contents are circuit-equivalent.**
`Json/LowGateJson.lean`'s `LowGate.flattenSeq` — the notion every R6.1–R6.3
leaf theorem states its `g.flattenSeq = target.flattenSeq` goal in — has
`.adj g => [g]` (an **opaque leaf**, no recursion into `g`), unlike
`Gate.flattenSeq` (`Proofs/Shor.lean`, custom-defined specifically for
`shor_gate`'s own Steps 1–5, which DOES recurse: `.adj g => [Gate.adj
(foldGateSeq (flattenSeq g))]`). This never mattered for R6.1–R6.3 or for
any of `shor`'s `.call`-site leaf theorems (`cphase_product`/`phase_product`/
`qft`'s own bodies never emit a raw `.adj` node — confirmed by grep, zero
hits in `CPhaseProduct.lean`/`Qft.lean`), so nobody had hit this before.
Step 3's own `†diff`/`†prep` are the first place it bites: `evalNode`'s
`.loop`/`.seq` unrolling of the *extracted* `†prep`/`†diff` subtree produces
a different raw `LowGate` value than `lowerPrepareNegConst`/the `diff` local
(extra trailing `foldLowGateSeq`-introduced `.id`s, different bracketing) —
*flattenSeq-equal but not raw-equal* — and since plain `LowGate.flattenSeq`
doesn't recurse into `.adj`, `(.adj extracted).flattenSeq = [extracted] ≠
[real] = (.adj real).flattenSeq` as **lists**, blocking the whole outer
comparison even though the circuits are identical. The actually-used
ground-truth comparison function this whole project already relies on for
"are two circuits the same" — `Tests.lean`'s own `r2_6_flatten`/
`r2_6g_flatten`, what the R2.6 `native_decide` smoke test itself compares —
**does** recurse into `.adj` (`.adj g => [LowGate.adj ((r2_6_flatten
g).foldr LowGate.seq .id)]`), confirming this is the *right* notion, just
missing as a non-`partial`, reusable, provable definition. Fixed by adding
`LowGate.flattenSeqAdj` (`Proofs/Shor.lean`, next to `Gate.flattenSeq`,
mirroring both `Gate.flattenSeq`'s own adj-recursion and `r2_6_flatten`'s
exact re-fold-via-`foldLowGateSeq` choice, structural recursion, not
`partial`) plus its own `.seq`-unfold bridge lemma
(`flattenSeqAdj_foldLowGateSeq`, `(foldLowGateSeq l).flattenSeqAdj =
l.flatMap flattenSeqAdj`, mirroring `Correct.lean`'s existing
`flattenSeq_sequence`). **Key realization that resolves the obstacle**: the
proof technique needed is *not* raw equality anywhere — congruence through
`flattenSeqAdj`'s own recursive definition means proving `g.flattenSeqAdj =
target.flattenSeqAdj` (an ordinary flattenSeqAdj-level/list-level goal,
exactly the same proof shape every earlier R6 theorem already uses, just
with `flattenSeqAdj` standing in for `flattenSeq`) is *sufficient* — the
`.adj` case's own `foldLowGateSeq (flattenSeqAdj g)` re-normalization is a
*function of* `flattenSeqAdj g`, so equal `flattenSeqAdj g`s give equal
re-normalized results automatically, without ever needing to touch the raw,
differently-bracketed underlying `LowGate` values directly.

**Result.** `evalNode_copyConstLoop_flattenSeqAdj` — the reusable, generic
(over destination/control register expressions and the constant/width
expressions) bit-copy loop lemma both Step 3 occurrences of
`lowerCopyConstFromUnit` need — is closed, merged into `Proofs/Shor.lean`,
no `sorry`, `#print axioms` clean (`[propext, Classical.choice, Quot.sound]`
or fewer per lemma). `lake build EmitProofs` succeeds (3321 jobs, only
unused-simp-arg lint warnings, zero errors). `grep -c sorry` is 0; no
`native_decide` anywhere in actual code.

**Not yet started, and now clearly scoped** (all mechanical given the two
obstacles above are resolved, but real work, comparable in size to Step 1/2's
own assembly in §12.10): `evalNode_lowerPrepareNegConst` (`X q ;; loop ;;
Negate`, composing the now-proved loop lemma with two single-op leaves, same
shape as `evalNodeGate_PhaseProdUsing`'s "generic leaf-group" pattern),
`evalNode_lowerCmpGeConst`/`evalNode_lowerCSubConst` (the two 8-element/
5-element composite assemblies, including the `sign`/`q` qubit-index facts
already checked semantically equivalent this round — `constArithmeticUnitQubit
scratch h = (scratch.reserve.take 1).get ⟨0,_⟩` matches the extracted
`.reserveSlice(scratch,0,1).qubit(0)` via `ExtReg.newBits e n := e.reserve.take
n`, confirmed by direct definition lookup, not yet turned into a committed
lemma), then the final `evalNode_step3` assembling both against `r2_6_env`'s
actual var lookups, mirroring `evalNodeGate_step3`'s own proof shape
(§12.11) exactly one level lower. **A note for whoever does the top-level
assembly (task #5)**: Step 3's target must be stated via `flattenSeqAdj`, not
`.flattenSeq` — and Step 4's `†diff`/`†mul` and the top-level `IQFT` will
need the same, while Steps 1/2/5's own `qft`/`phase_product`/`cphase_product`
`.call`-site results remain `.flattenSeq`-stated (proved that way in
§12.14–§12.16, unaffected). Combining an adj-free `.flattenSeq` fact with a
`flattenSeqAdj`-stated one at the top level needs a small bridge lemma (e.g.
"if `g` has no `.adj` subterm, `g.flattenSeqAdj = g.flattenSeq`") that
doesn't exist yet — flagged here so it isn't rediscovered from scratch.

### 12.18 R6.4 `shor` half: Step 3 done — `evalNode_lowerStep3` closed, mechanical assembly on top of §12.17's infrastructure

§12.17 left Step 3 with its two hard obstacles resolved (`LowGate.flattenSeqAdj`,
the bit-copy loop lemma) but the actual `lowerCmpGeConst`/`lowerCSubConst`
composite circuits and the top-level `evalNode_lowerStep3` theorem not yet
built. This round closed all of it — no further new obstacles, exactly the
"mechanical but not short" assembly §12.17 anticipated.

**Qubit-index facts.** Two small lemmas ground-truth the two qubit positions
`lowerCmpGeConst`/`lowerCSubConst`/`lowerPrepareNegConst` reference, matching
them against the extracted `.qubit`-expressions:
`evalReg_scratchUnitQubit` (`constArithmeticUnitQubit scratch h =
(scratch.reserve.take 1).get ⟨0,_⟩`, matching the extracted
`.qubit(.reserveSlice(scratchR,0,1),0)`, via `ExtReg.newBits e n :=
e.reserve.take n`) and `evalReg_scratchSignQubit` (the comparator's `sign =
scratch.active.get ⟨scratch.width-1,_⟩`, matching
`.qubit(.activeSlice(scratchR,0,scratchW),scratchW-1)`) — both by unfolding
`evalReg`'s `.reserveSlice`/`.activeSlice`/`.qubit` cases down to a bare
`List.get`/`Reg.drop`/`Reg.take` computation and closing with
`List.getD_eq_getElem?_getD`/`List.getElem_take`-style conversions, the same
idiom `evalNodeGate_Hreg_loop`/`Correct.lean`'s `evalNode_naive_leaf` already
established. One proof-engineering note: `omega` cannot bridge
`scratch.active.width` and `scratch.width` on its own (they're definitionally
equal — `ExtReg.width e := regSize e.active = e.active.width` — but
*syntactically* distinct atoms to `omega`); every place this bound was
needed, an explicit `have heq : scratch.active.width = scratch.width := rfl`
had to be fed to `omega` alongside it, not folded into a single tactic call.

**Composite circuit lemmas**, each following the exact `evalNodeGate_PhaseProdUsing`-
style "generic leaf-group" pattern from §12.9, now one level lower and with
`flattenSeqAdj` in place of `flattenSeq`:
- `evalNode_lowerPrepareNegConst` (`X q ;; loop ;; Negate scratch`, using
  §12.17's `evalNode_copyConstLoop_flattenSeqAdj` for the loop and the new
  qubit-index fact for `q`) and `evalNode_lowerPrepFromFlag` (the
  `lowerCSubConst`-side variant, `CNOT flag q` in place of `X q` — same
  proof shape, different first leaf).
- `evalNode_diffCmp` (`zeroExtend data 1 ;; AddScaled scratch (data.grow 1)
  false 0 ;; zeroDealloc data 1`, `lowerCmpGeConst`'s `diff`, no loop
  involved, the simplest of the four).
- `flattenSeqAdj_adj_congr` (`g.flattenSeqAdj = t.flattenSeqAdj →
  (LowGate.adj g).flattenSeqAdj = (LowGate.adj t).flattenSeqAdj`, one line
  via `LowGate.flattenSeqAdj`'s own `.adj` equation) — the general form of
  §12.17's "key realization," used at every `†diff`/`†prep`/`†prep2`
  occurrence rather than re-deriving the congruence each time.
- `evalNode_lowerCmpGeConst` (the 8-leaf assembly: `prep`, `diff`'s three
  leaves inlined at the top level — confirmed by ground-truthing `r2_6_step3`
  that the extractor keeps `diff`'s own three ops as flat top-level siblings
  rather than nesting them, exactly as `§12.6`'s "Sixth round" finding
  already flagged for `phase_product`'s annotated-ops body — `X flag`, `CNOT
  sign flag`, then `†diff`/`†prep` each re-using the SAME evaluated `g1`/`g2`
  from the forward occurrences by determinism of `evalNode`, combined via
  `flattenSeqAdj_adj_congr`) and `evalNode_lowerCSubConst` (the simpler
  3-leaf assembly: `prep2`, `AddScaled data scratch false 0`, `†prep2`).
- `evalNode_lowerStep3`: `CMP ;; SUB`, combining the two composites,
  mirroring `step3 N dataCarry scratch flag := Gate.CmpGeConst N dataCarry
  scratch flag ;; Gate.CSubConst N dataCarry scratch flag` (`Circuit/Steps.lean`)
  one level lower, target `(lowerCmpGeConst N data scratch flag h ;;
  lowerCSubConst N data scratch flag h).flattenSeqAdj`. Generic over
  register/weight expressions and a `ConstArithmeticWorkspace N data scratch
  flag` hypothesis, matching `evalNode_call_cphase_product`/`_phase_product`/
  `_qft`'s own convention (site-specific `r2_6_env` var-lookup wiring — the
  `evalReg_yVar`/`evalReg_scratchVar`/`evalReg_flagVar`/`evalW_NVar` analogues
  `evalNodeGate_step3` needed one level up — deferred to the top-level
  assembly, same as those three leaves).

**Result.** All nine theorems (`evalReg_scratchUnitQubit`,
`evalReg_scratchSignQubit`, `evalNode_lowerPrepareNegConst`,
`flattenSeqAdj_adj_congr`, `evalNode_diffCmp`, `evalNode_lowerPrepFromFlag`,
`evalNode_lowerCmpGeConst`, `evalNode_lowerCSubConst`,
`evalNode_lowerStep3`) merged into `Proofs/Shor.lean`. `lake build
EmitProofs` succeeds (3321 jobs, only unused-simp-arg lint warnings, zero
errors). `grep -c sorry` is 0; no `native_decide` anywhere in actual code.
`#print axioms evalNode_lowerStep3` → `[propext, Classical.choice,
Quot.sound]`, clean. **Step 3 (task #4) is done.**

**Net assessment.** `shor`'s LowGate-level theorem now has all 5 Steps'
worth of *leaf*-level machinery in hand: Steps 1/2/4mul/5 via the three
generic `.call`-site theorems (§12.14–§12.16), Step 3 via
`evalNode_lowerStep3` (this round). What remains is exactly what §12.11's
own Gate-level precedent already did one level up, transplanted: the
`modExpApproxValid` loop-body assembly (`evalNodeGate_modExpLoop_aux`'s
induction, `evalNode`/`LowGate` in place of `evalNodeGate`/`Gate`) and the
top-level `H_reg`/`initY1`/loop/`IQFT` assembly — wiring every leaf theorem's
generic register/weight-expression parameters to `r2_6_env`'s actual
`.var`/`.opaque` lookups at each of the 14 concrete call sites plus Step 3's
two occurrences, and building the `flattenSeq`/`flattenSeqAdj` bridge lemma
§12.17 already flagged for combining Step 3/4/IQFT's adjoint-aware results
with Steps 1/2/5's plain-`.flattenSeq` ones. Task #5, not yet started.

### 12.19 R6.4 `shor` half: the NoAdj-bridge — closed and merged; **correction to §12.17's framing** of which steps need it

§12.17 flagged the missing bridge lemma as needed for "combining an adj-free
`.flattenSeq` fact with a `flattenSeqAdj`-stated one at the top level" and
suggested it was only Step 3/4/IQFT's problem, with "Steps 1/2/5's own
`qft`/`phase_product`/`cphase_product` `.call`-site results remain
`.flattenSeq`-stated ... unaffected." **That framing was wrong.** Re-reading
`modExpBody`'s actual structure (`evalNodeGate_modExpBody`,
`evalNodeGate_HloopX`/`_initY1`/`_iqftX`, `Circuit/Steps.lean`): Steps 1, 2,
4mul, 4†mul, and 5 each embed a `qft`/`phase_product`/`cphase_product` call
*inside* an `.adj (...)` wrapper (every step of `CmodMulInPlaceCore` is
itself a QFT-conjugated phase-multiplication — `step1`/`step5`'s own bodies
are `... ;; Gate.adj (...)`-shaped, per §12.9–§12.11's Gate-level precedent,
now confirmed to hold one level down at the `Node` level too). So essentially
*every* step, not just Step 3/4/IQFT, needs the already-proven
`.flattenSeq`-stated leaf theorems (`evalNode_call_cphase_product`,
`evalNode_call_phase_product`, `evalNode_call_qft` — §12.14–§12.16) lifted to
`flattenSeqAdj`-level facts wherever they occur inside an `.adj(...)`
wrapper, not merely at the three sites originally flagged.

**The bridge, now built.** Two new syntactic `NoAdj` predicates, mirroring
`Node.callNames`'s recursive shape exactly (same well-founded-recursion
opacity applies — see the tactical note below):
- `LowGate.NoAdj : LowGate → Prop` (`namespace Shor`, alongside
  `LowGate.flattenSeqAdj`): `True` on every constructor except `.adj _ =>
  False` and `.seq a b => NoAdj a ∧ NoAdj b`.
- `LowGate.flattenSeqAdj_eq_flattenSeq_of_noAdj : g.NoAdj → g.flattenSeqAdj =
  g.flattenSeq` — the actual bridge lemma §12.17 asked for, by structural
  induction on `g` (the `.adj` case is vacuous since `NoAdj` rules it out).
- `Node.NoAdj : Node → Prop` (`namespace Shor.IR`): the `Node`-level analogue,
  `.adj _ => False`, `.seq body => ∀ n ∈ body, NoAdj n`, `.cond _ t f => NoAdj
  t ∧ NoAdj f`, `.loop _ _ _ body => NoAdj body`, `True` on `.op`/`.call`
  (calls are checked separately via closure, same as `Node.callNames`).
- `evalNode_noAdj` — the main theorem: given a `hclosed`-style
  transitive-call-closure hypothesis (every named template's body is `NoAdj`
  *and* its own further calls stay inside the name set — identical shape to
  `evalNode_dind`/`evalNode_ind`'s own `hclosed` parameters), evaluating any
  `NoAdj` node whose call-closure stays in that name set produces a `NoAdj`
  `LowGate`. Structurally mirrors `evalNode_dind`'s proof skeleton exactly —
  same fuel-then-sizeOf double strong induction, same seven `Node`-constructor
  cases. Supporting lemmas: `foldLowGateSeq_noAdj`, `buildLowGate_noAdj`
  (`buildLowGate`'s ~15 named-gate cases, resolved the same 4-nested-`split`
  way as earlier rounds — **note**: `LowGate.CPhase`/`CCPhase`
  (`ShorVerification/.../NaiveLeaf.lean`) genuinely expand to `.seq` in their
  non-trivial branches, so `buildLowGate_noAdj` needed real (non-vacuous)
  `LowGate.CPhase_noAdj`/`CCPhase_noAdj` lemmas, not a "this case is
  impossible" dismissal — an earlier attempt assuming `buildLowGate` never
  produces `.seq` was wrong and had to be corrected), and `List.mapM_ok_noAdj`
  (a small generic "`mapM` preserves an elementwise postcondition" helper).

**Two tactical notes worth keeping**, both already seen earlier this
project but re-triggered here: (1) `Node.NoAdj`/`LowGate.NoAdj`, like
`Node.callNames`, compile via well-founded recursion and so do **not**
reduce via defeq/type ascription — `simp only [Node.NoAdj] at hna` (or
`[LowGate.NoAdj]`) must precede any `.1`/`.2` projection or
function-application use. (2) A tactic-mode `cases hg with | inl hg => ... |
inr hg => ...` splitting an `Or` hypothesis in `List.mapM_ok_noAdj`'s `cons`
case silently compiled to a term containing a bare `sorry` in one branch —
**with zero reported compile errors** (confirmed via `#print`, not via any
error message) — for reasons not fully diagnosed. Fixed by replacing it with
a direct term-mode `hg.elim (fun hg => ...) (fun hg => ...)`, which closed
with 0 errors and clean axioms. Flagging this generally: if a `cases`/`rcases`
split on an `Or` looks suspiciously easy relative to how it's used
downstream, `#print` the resulting theorem and check for embedded `sorry`
before trusting a clean compile — don't assume "no errors" means "no sorry."

**Result.** All seven theorems (`LowGate.NoAdj`, `flattenSeqAdj_eq_flattenSeq_of_noAdj`,
`LowGate.CPhase_noAdj`, `LowGate.CCPhase_noAdj`, `Node.NoAdj`,
`foldLowGateSeq_noAdj`, `buildLowGate_noAdj`, `List.mapM_ok_noAdj`,
`evalNode_noAdj` — nine total definitions/theorems) merged into
`Proofs/Shor.lean` (the `LowGate`-level four inside `namespace Shor` near
`LowGate.flattenSeqAdj`'s own definition; the `Node`-level five inside
`namespace Shor.IR`, right before Step 3's closing theorems). `lake build
EmitProofs` succeeds (3321 jobs, only unused-simp-arg lint warnings, zero
errors). `grep -c sorry` is 0 in the file (the two `native_decide` string
matches are both inside prose comments, not tactic code). `#print axioms`
on all seven, re-checked standalone against the merged file, shows only
`propext`/`Classical.choice`/`Quot.sound` (no `sorryAx`) throughout. **The
NoAdj-bridge is done** — the actual gap §12.17 flagged is closed, and the
scope is now understood correctly (essentially every `modExp` step needs it,
not just three). Task #5 (top-level `shor` assembly) is otherwise unchanged
in status — this round built a prerequisite for it, not the assembly itself;
Step 1's `evalNode`-level assembly (the next concrete deliverable, blocked on
this bridge) has not yet been started.

### 12.20 R6.4 `shor` half: NoAdj-bridge completed — the real-circuit half (`lowerGateRec`/`lowerQFTPlan`) and the extracted-IR half (`Node.NoAdj` on `qft`/`phase_product`/`cphase_product`/`naive_leaf`/`naive_cleaf`'s own bodies), plus the three `.flattenSeqAdj`-lifted leaf theorems — closed and merged

§12.19 built `evalNode_noAdj` (extracted `Node`/`LowGate` values only) but
left two things needed to actually *use* it: a `LowGate.NoAdj` fact about
the *real* lowered circuits R6.2/R6.3's leaf theorems compare against
(`lowerCSignedPhaseProdWithWorkspace`/`lowerGateRec (standardSignedPhase-
LoweringPlan …)`/`lowerQFTPlan (standardQFTLoweringPlan …)`), and a
`Node.NoAdj` fact about `qft`/`phase_product`/`cphase_product`/`naive_leaf`/
`naive_cleaf`'s own extracted bodies (needed by `evalNode_noAdj`'s `hclosed`
hypothesis, since evaluating a `.call` node recurses into the callee's
actual body). This round closed both, plus the three leaf theorems restated
via `flattenSeqAdj`.

**Real-circuit side.** `LowGate.sequence_noAdj` (`LowGate.sequence`, the
`;;`-fold `Naive_SignedPhaseProd`/`Naive_CSignedPhaseProd` use, same shape
as `IR.foldLowGateSeq` — same proof as `foldLowGateSeq_noAdj`),
`LowGate.Naive_SignedPhaseProd_noAdj`/`_CSignedPhaseProd_noAdj` (via
`sequence_noAdj` + `CPhase_noAdj`/`CCPhase_noAdj` on every element of
`naiveSignedPhaseGates`/`naiveCSignedPhaseGates`). **Key discovery, found by
reading `PhaseProduct/Lowering/Plan.lean`'s `lowerGateRec` and
`QFT/Lowering/Plan.lean`'s `lowerQFTPlan` directly before assuming
anything**: neither function's equation set has an `.adj` case anywhere —
`lowerGateRec`'s 17 cases bottom out at `Naive_SignedPhaseProd`/
`Naive_CSignedPhaseProd` (the two base cases) or recurse structurally
(`.seq`/`.signedStep`/`.cSignedStep`), and `lowerQFTPlan`'s `.split` case
combines two recursive `lowerQFTPlan` calls with one `lowerGateRec
phasePlan`, all via `;;` — so `lowerGateRec_noAdj`/`lowerQFTPlan_noAdj`
(`∀ plan, (lowerGateRec/lowerQFTPlan plan).NoAdj`) are unconditional
structural inductions over `PhaseLoweringPlan`/`QFTLoweringPlan`, no
side-hypothesis needed. `lowerSignedPhaseProdWithWorkspace_noAdj`/
`lowerCSignedPhaseProdWithWorkspace_noAdj` unfold to `lowerGateRec_noAdj`
directly (both are literally `lowerGateRec plan` under the hood, confirmed
by reading `PhaseProduct/Lowering/Lower.lean`/`Plan.lean` — `lowerSigned-
PhaseProd`/`lowerCSignedPhaseProd` are `lowerGateRec plan` with no further
wrapping). **One correction against an initial guess**: `evalNode_call_
phase_product`'s actual stated target (re-checked directly, not assumed) is
`(lowerGateRec (standardSignedPhaseLoweringPlan …)).flattenSeq`, not
`(lowerSignedPhaseProdWithWorkspace …).flattenSeq` — the lifted corollary
had to be restated to match, using `lowerGateRec_noAdj` directly rather
than the `lowerSignedPhaseProdWithWorkspace_noAdj` wrapper (the wrapper is
still proved and kept, for whichever future call site states its target
that way instead).

**Extracted-IR side.** `naiveLeafTemplate_body_noAdj`/`naiveCLeafTemplate_
body_noAdj` close directly (`Reflect/Targets.lean`'s hand-authored literal
bodies — one `.loop`/`.loop`/`.op` chain each). For the three large,
doc-lookup-opaque template bodies (`r2_2_ppBody`/`r2_4_cppBody`/
`r2_5_qftBody`), the key move was reusing R6.2/R6.3's *already-proved*
top-to-leaf `rfl`-decomposition lemmas (`r2_2_ppBody_eq_cond`/
`_ppThen_eq_seq`/`_ppAlloc_eq`/`_ppDealloc_eq`/`_ppBodyNode_eq`/… and their
`r2_4_cpp*`/`r2_5_qft*` analogues, all established while building §12.14–
§12.16's leaf theorems) rather than re-deriving any structure: feeding the
*entire* lemma set for one body into a single `simp [Node.NoAdj, <all the
_eq lemmas>]` call fully unfolds and discharges it in one shot (every leaf
these decompositions bottom out at is `.op`/`.call`, both trivially `True`
under `Node.NoAdj`, and `.cond`/`.seq` just distribute) — no manual
per-leaf case analysis needed, and no timeout despite each body being
40–60 nodes (`set_option maxHeartbeats 4000000`, matching the heartbeat
budget the original `_eq` proofs themselves already needed). `r2_4_ppAlloc_
eq`/`_ppDealloc_eq` reduce to `r2_2_ppAlloc_eq`/`r2_2_ppDealloc_eq` (already
known identical, §12.7's finding) so no new alloc/dealloc work was needed
for `cphase_product`. `hclosedNA_cpp`/`_pp`/`_qft` (per-name `Node.NoAdj`
lookup, mirroring `hclosedC_cpp`/`_pp`/`_qft`'s existing `fin_cases`
structure exactly) combine with the already-proved `hclosedC_*` (callNames
closure) into `hclosed_cpp`/`_pp`/`_qft`, the exact `hclosed` shape
`evalNode_noAdj` needs.

**The three lifted leaf theorems.** `evalNode_call_cphase_product_
flattenSeqAdj`/`_phase_product_flattenSeqAdj`/`_qft_flattenSeqAdj`: each
takes the original leaf theorem's hypotheses, calls the original theorem to
get `g` and its `.flattenSeq` fact, derives `g.NoAdj` via `evalNode_noAdj`
applied at the `.call` node itself (trivially `Node.NoAdj` — the `.call`
case of `Node.NoAdj` is `True` unconditionally, `hclosed_*` supplies the
one substantive premise), derives the real target's `NoAdj` via the
real-circuit lemmas above, then closes with `LowGate.flattenSeqAdj_eq_
flattenSeq_of_noAdj` on both sides bridging through the existing
`.flattenSeq` equality — `g.flattenSeqAdj = g.flattenSeq = t.flattenSeq =
t.flattenSeqAdj`. Mechanical once both NoAdj halves were in hand.

**Result.** All twenty pieces (4 `LowGate`-level NoAdj lemmas in
`namespace Shor`; `naiveLeafTemplate_body_noAdj`/`naiveCLeafTemplate_body_
noAdj`/`r2_2_ppBody_noAdj`/`r2_4_cppBody_noAdj`/`r2_5_qftBody_noAdj`/
`hclosedNA_cpp`/`_pp`/`_qft`/`hclosed_cpp`/`_pp`/`_qft`/the 3 lifted leaf
theorems in `namespace Shor.IR`) merged into `Proofs/Shor.lean`. `lake
build EmitProofs` succeeds (3321 jobs, only unused-simp-arg lint warnings,
zero errors). `grep -c sorry` is 0; the two `native_decide` text matches
remain prose-only. `#print axioms`, re-checked standalone against the
merged file for every new theorem, shows only `propext`/`Classical.choice`/
`Quot.sound` throughout — no `sorryAx`. **The NoAdj-bridge is now fully
usable, both halves done.** Task #5's concrete next deliverable — Step 1's
`evalNode`-level LowGate assembly, mirroring `evalNodeGate_step1` (lines
~656–716) one level down, using `evalNode_call_cphase_product_
flattenSeqAdj` for the core and `evalNode_call_qft_flattenSeqAdj` for the
`.adj`-wrapped QFT — still needs `r2_6_modExpBody`/`r2_6_step1`/
`_step1_Hloop`/`_step1_core`/`_step1_adjQFT`-style ground-truth
decomposition of `r2_6_doc`'s "shor" template body at the `Node` level
(mirroring `r2_6g_modExpBody`/`r2_6g_step1`'s existing Gate-level
decomposition, `Proofs/Shor.lean` lines ~363–393) — not yet started; this
is genuinely new work, since §12.12's "Ground-truth r2_6_doc's shor
template body" task only covered a `#eval`-dump *inspection* (confirming
14 `.call` sites, no surprises), not committing any Lean-level
decomposition lemmas the way `r2_6g_*` already has for `shor_gate`.

### 12.21 R6.4 `shor` half: `Node`-level ground truth for `r2_6_shorBody` through Step 1's `Hloop`/`core`/`adjQFT` — closed and merged, all `rfl`; Step 1's actual assembly not yet started

The concrete deliverable §12.20 identified as next: the `Node`-level
counterpart of `r2_6g_sgBody`'s decomposition, which didn't exist yet
despite §12.12 claiming the "ground-truth" task done (that task only
covered an inspection pass, not committed decomposition lemmas — see
§12.20's closing note). This round built it, through Step 1.

**Method: probe with `nodeJson`, don't guess blind.** `Emit/IR/Json.lean`
has a `nodeJson : Node → Json` printer (used elsewhere for output tooling,
not previously used as a *proof-development* tool). Writing the projector
`def`s (`r2_6_HloopX := match r2_6_shorBody with | .seq [a, _] => a | n =>
n`, etc.) and immediately `#eval IO.println (nodeJson r2_6_HloopX).pretty`
against them in scratch — before committing any `_eq` theorem — let each
guess be checked against the real extracted structure directly, rather
than writing a guessed `_eq` statement and hoping `rfl` closes it blind.
**First guess was wrong and caught immediately**: assumed `r2_6_shorBody`'s
top-level `.seq` was a flat 4-element list (`[HloopX, initY1, modExpLoop,
iqftX]`), mirroring `r2_6g_sgBody`'s own flat shape exactly — this
compiled (the fallback `| n => n` arm silently absorbed the non-matching
pattern) but the `nodeJson` dump for the assumed `iqftX` printed the
*entire rest of the body*, immediately revealing the mismatch. Second
guess — **2-element right-nested** `.seq [a, .seq [b, .seq [c, d]]]`,
matching the convention every *other* extracted body in this file already
turned out to use (`r2_2_ppThen`, `r2_5_qftSplit`, …), not `shor_gate`'s
own flatter Gate-level shape — checked clean on the first try, `rfl`
throughout. Lesson for whoever continues into Steps 2–5: don't assume
`r2_6g_step2..5`'s flat-list shape carries over; probe each with
`nodeJson` before writing the `_eq` lemma.

**Result, confirmed exactly matching §12.12's prediction**: `r2_6_shorBody`
shares `shor_gate`'s `H_reg`/`initY1`/`.loop "e"`/`IQFT` top-level
skeleton, with `Node.call "qft"`/`"cphase_product"`/`"phase_product"`
leaves standing in for `shor_gate`'s raw `.op "QFT"`/`"CSignedPhaseProd"`/
`"SignedPhaseProd"` — no other structural surprise anywhere probed.
`r2_6_shorBody_eq_seq`/`_rest1_eq_seq`/`_rest2_eq_seq` give the top-level
skeleton; `r2_6_HloopX_eq`/`_initY1_eq` are byte-identical to their
Gate-level `r2_6g_*` counterparts (unaffected by the Node.call
substitution, since neither routes through QFT/phase-product); `r2_6_
iqftX_eq` is the first concrete confirmation of the register-wiring §12.12
flagged but never turned into a committed fact — `qft`'s `.call` passes a
reserve-*stripped* `.activeSlice` for `r`, plus two `.reserveSlice`s
derived from the new `qftXWork`/`qftZWork` opaque functions for `xWork`/
`zWork` (`qftRArgs`, a small reusable helper capturing this exact 3-arg
pattern, confirmed identical at both `r2_6_iqftX` and `r2_6_step1_adjQFT`).
`r2_6_modExpBody_eq_seq`/`_restA_eq_seq`/`_restB_eq_seq`/`_restC_eq_seq`
give the 5-step skeleton (`r2_6_step1..5`, same 2-element right-nesting).
`r2_6_step1_eq_seq`/`_rest_eq_seq` decompose Step 1 itself into `Hloop`/
`core`/`adjQFT`; `r2_6_step1_Hloop_eq` matches `r2_6g_step1_Hloop_eq`
exactly; `r2_6_step1_adjQFT_eq` is `qftRArgs` at `work`/`workW`; `r2_6_
step1_core_eq` is the full literal — `zeroExtend`/`zeroExtend`/`.call
"cphase_product" [yW+1, workW+1, (yCap-1)-1, workCap-1] [phiExpr] [ctrl,
grow(yData,1), grow(work,1)]`/`zeroDealloc`/`zeroDealloc`, matching
`evalNode_call_cphase_product`'s expected argument shape exactly (`r2_6_
step1_phiExpr` is byte-identical to `evalA_step1_phi`'s Gate-level target,
unaffected by the substitution since it's plain `AExpr` data, not circuit
structure). All twelve new theorems close by plain `rfl`.

**Not yet done**: `evalNode_step1` itself (the actual assembly, combining
`r2_6_step1_Hloop_eq` with a new `evalNode`-level Hadamard-loop lemma — no
`evalNode_Hreg_loop` counterpart to `evalNodeGate_Hreg_loop` exists yet,
needs building first — `r2_6_step1_core_eq` with `evalNode_call_
cphase_product_flattenSeqAdj`, and `r2_6_step1_adjQFT_eq` with
`evalNode_call_qft_flattenSeqAdj` through the `.adj` wrapper), Steps 2–5's
own ground-truth decomposition (not yet probed at all), and everything
downstream (`modExpApproxValid` loop assembly, top-level assembly). Also
not yet built: `r2_6_env`-specific versions of the small `evalReg_yDataReg`/
`_workVar`/`_ctrlQubit`/`evalA_step1_phi`-style var-lookup facts
`evalNode_step1` will need — the existing ones are stated for `r2_6g_env`,
and while `r2_6_env`'s `w`/`r` fields are the *same* formula (`rfl`-equal,
checked directly), its `opaqueW`/`coeff` fields are a strict superset (adds
`nextWidth`/`reserveNeed_x`/`_z`/`qftXWork`/`qftZWord`/`coeff`, all absent
from `r2_6g_env`) — the "mod"/"modpow" cases `evalA_step1_phi` needs are
handled identically in both, so its proof should transfer verbatim with
the env swapped, but this hasn't been re-proved or bridged yet, only
identified as low-risk.

**Verification, this round**: `lake build EmitProofs` → `Build completed
successfully (3321 jobs)`; `grep -c sorry Proofs/Shor.lean` → `0`; no
`native_decide` outside prose comments; every new theorem closes by plain
`rfl` (no `#print axioms` needed for `rfl`-only theorems — they carry no
axioms beyond what `rfl` itself needs, i.e. none beyond the kernel's own).

### 12.22 R6.4 `shor` half: `evalNode`-level Hadamard-loop lemma and `r2_6_env` var-lookup facts — closed and merged

The concrete next deliverable §12.21 left open: `evalNode_Hreg_loop` (the
`evalNode`/`LowGate` counterpart of `evalNodeGate_Hreg_loop`, §12.9 — same
proof shape, `buildLowGate`/`foldLowGateSeq`/`LowGate.H` in place of
`buildGate`/`foldGateSeq`/`Gate.H`, needing a new `map_getD_LowH_eq`/
`_reg` mirroring `map_getD_H_eq`/`_reg`), and the dozen small `r2_6_env`
var-lookup facts (`evalReg_yVar_ir`/`evalW_yW_ir`/`_yCap_ir`/`_workCap_ir`/
`evalReg_yDataReg_ir`/`_workVar_ir`/`evalW_workW_ir`/`evalReg_step1_
Hloop_active_ir`/`evalW_xW_ir`/`evalReg_xVar_ir`/`evalW_eVar_ir`/
`evalReg_ctrlQubit_ir`/`evalW_NVar_ir`/`evalW_aVar_ir`/`evalA_step1_phi_ir`)
`evalNode_step1` needs — proved fresh against `r2_6_env` rather than bridged
from the existing `r2_6g_env` versions, since `r2_6_env`'s `w`/`r` fields
are the same formula as `r2_6g_env`'s but its `opaqueW`/`coeff` fields are a
strict superset, so bridging would need its own per-field equality lemmas
anyway.

**Tactical note, worth remembering generally**: `simp [r2_6_env]` (the exact
idiom `r2_6g_env`'s versions use) loops — "Possibly looping simp theorem:
`r2_6_env.eq_1`" — because `r2_6_env`'s `coeff` field is a genuine `dite`
(`if h : l < q 2 then some (...) else none`), unlike `r2_6g_env`'s trivial
`coeff := fun _ _ => none` — unfolding the whole record via `simp` exposes
the `dite` even when the goal never touches `.coeff`, and simp's rewrite
traversal loops trying to normalize it. Fixed by using bare `rfl` in place
of every trailing `simp [r2_6_env]` (a `.w`/`.r`/`.opaqueW` projection at a
literal key reduces by plain kernel `rfl`, which doesn't invoke simp's
rewrite/congruence machinery at all); `evalA_step1_phi_ir` (needing the
"mod"/"modpow" opaqueW cases too) closes by a single bare `rfl` with no
`simp` call whatsoever — the same fix taken further. Any future `r2_6_env`
fact should reach for `rfl` first, not `simp [r2_6_env]`.

**Verification, this round**: `lake build EmitProofs` → `Build completed
successfully (3321 jobs)`; `grep -c sorry` → `0`; no `native_decide`
outside prose comments.

### 12.23 R6.4 `shor` half: `work`'s QFT-workspace register facts closed and merged; assembling `evalNode_step1` hits a genuine, documented gap in `evalNode_call_cphase_product`'s genericity — not yet resolved

This round attempted the actual `evalNode_step1` assembly §12.20–§12.22
were building toward, and got most of the way there before finding a real
blocker — recorded here in full since it blocks not just Step 1 but Steps
2/4mul/4†mul/5 too (see below).

**What got built and merged, independent of the blocker**: `evalReg_
workActive_ir` (the `.activeSlice` piece of `qftRArgs`, mirroring `evalReg_
step1_Hloop_active_ir` without the `"i"` binding), `evalW_qftXWork_ir`/
`evalW_qftZWork_ir` (`r2_6_env`'s `"qftXWork"`/`"qftZWork"` opaqueW cases,
`(qftWorkspaceNeed r2_5_ops work.width).1`/`.2`), `evalReg_workXWork_ir`/
`evalReg_workZWork_ir` (the two `.reserveSlice` pieces of `qftRArgs`,
evaluating exactly to `ExtReg.ofReg (qftXWork/qftZWork r2_5_ops work)` —
confirmed by reading `evalReg`'s `.reserveSlice` case directly:
`ExtReg.ofReg ((rv.reserve.drop loV).take (hiV - loV))`, matching `qftXWork`/
`qftZWork`'s own definitions in `QFT/Lowering/Workspace.lean` field-for-
field), and `yDataReg_canGrow_ir` (`y.CanGrow 2` ⟹ Step 1's `yDataReg`
value `.CanGrow 1`, needed for `ExtReg.width_grow` at the core piece).
`QFTReserveOK.explicitWorkspace`/`regSize_qftXWork`/`regSize_qftZWork`
(`QFT/Lowering/Workspace.lean`, pre-existing) turned out to supply exactly
the `QFTWorkspaceOK`/width facts needed, once found — no new QFT-side
machinery had to be invented, just wired up. All `#print`-clean, no
`sorry`, confirmed via `lake env lean` in isolation before merging.

**The blocker.** `evalNode_call_cphase_product` (§12.14) requires
`AExpr.opaqueNames phiR = []`. Step 1's actual extracted angle argument
(`r2_6_step1_phiExpr`, §12.21) is `2·mod(modpow(a,e,N)+N-1, N)/N` — it
genuinely contains `.opaque "mod"`/`"modpow"` subexpressions, so the
hypothesis is **unsatisfiable**, not just hard to discharge. Traced to the
root cause, not just observed: `evalNode_call_cphase_product`'s proof
bridges `r2_6_doc`/`env1` to `r2_4_doc`/`cppEnv`/`env2` (`evalNode_ind`,
§12.13) and needs `evalA env2 phiR = evalA env1 phiR`, proved via
`evalA_oind` — which only guarantees opaqueW agreement on `cpp_oNames =
["nextWidth", "reserveNeed_x", "reserveNeed_z"]`, the only names `cppEnv.
opaqueW` defines at all (`| _, _ => none` otherwise, genuinely undefined,
not just unproven-equal) — so no auxiliary fact can bridge `evalA cppEnv
phiR` to `evalA r2_6_env phiR` for a `phiR` using `"mod"`/`"modpow"`;
`AExpr.opaqueNames phiR = []` is the theorem's way of sidestepping the
question, and is a real precondition of its proof *method*, not a
conservative over-restriction that a cleverer tactic could discharge.

**Scope of the gap**: specific to `cphase_product`/`phase_product`'s leaf
theorems (whose `.call`s carry an angle argument built this way) —
`evalNode_call_qft`/`_flattenSeqAdj` has no `aArgs` at all (`qft` takes no
angle parameter) and is unaffected. It also bites only at the *outer*,
`shor`-level call sites — R6.2/R6.3's own recursion theorems (`evalNode_
phase_product_correct` etc.) are fine, since phase_product's *internal*
recursive `.call` sites pass `phi` via `.coeff (.var "phi") l limbW`
(opaque-free by construction). Concretely this means: Step 1's `cphase_
product` core (found this round), Step 5's `cphase_product` core, and Step
2/4mul/4†mul's three `phase_product` cores are **all** blocked the same
way — this is not a Step-1-specific problem, it is the actual shape of the
remaining task #5 work.

**Likely fix, not attempted — a design decision for whoever continues, not
just plumbing**: `evalNode_call_cphase_product`/`_phase_product`'s `hRHS`
derivation (`Proofs/Shor.lean`, immediately after `hnode1` in each) re-
evaluates `phiR` against `env2` via `evalA_oind` specifically to get a
*value* to feed `Env.call`'s `aVals` argument — but the caller already has
that value directly, as `hphi : evalA env1 phiR = .ok phi`. If `Env.call`'s
`aVals` list can be supplied as `[phi]` (from `hphi`) rather than re-derived
via `aArgs.mapM (evalA env2)`, the `evalA_oind` step — and hence `hOphi` —
is avoidable entirely, a genuinely general fix rather than a Step-1-shaped
workaround. This is a change to existing, already-verified theorems (§12.14
–§12.15), not new plumbing: re-verify `#print axioms` on every existing use
of `evalNode_call_cphase_product`/`_phase_product` after changing them, not
just the new call sites, and rebuild the full project before considering it
closed. An alternative, more conservative fix — leave `evalNode_call_
cphase_product`/`_phase_product` untouched and instead build a *second*,
specialized leaf theorem for angle arguments with nonempty opaqueNames —
was not evaluated against the "modify existing theorem" approach for
relative cost; whoever picks this up should weigh both before starting.

**Verification, this round**: `lake build EmitProofs` → `Build completed
successfully (3321 jobs)`; `grep -c sorry` → `0`; no `native_decide` outside
prose comments; the abandoned `evalNode_step1` attempt itself was **not**
merged (confirmed blocked, not just unfinished) — only the independently-
useful, fully-verified pieces above were kept.

### 12.24 R6.4 `shor` half: the §12.23 blocker fixed — `evalNode_call_cphase_product`/`_phase_product` restructured to drop `phiR`'s opaqueNames restriction entirely, not just for Step 1

Took the "likely fix" §12.23 identified — avoid re-deriving `phi` via
`evalA_oind` since the caller already supplies its value via `hphi` — and
implemented it, on the coordinator's explicit go-ahead (nothing committed
to git, safe to iterate). The actual fix needed more than the one-line
framing suggested: it isn't enough to skip `evalA_oind` for `phi`
specifically, because the *outer* `.call` node's own bridge step
(`evalNode_ind`, doc **and** env swapped together) needs `Node.opaqueNames
(.call …) ⊆ oNames` for *every* argument expression syntactically present
on that node — `phiR` included — before it can even begin, regardless of
which sub-step inside it would go on to use that fact. No choice of
`oNames` can satisfy this for a `phiR` using `"mod"`/`"modpow"`, since
`cppEnv`/`ppEnv`'s `opaqueW` has no case for those names at all (`| _, _ =>
none`) — widening the tracked name set doesn't help, because the *target*
env genuinely can't evaluate them, agreement is not just unproven but
impossible.

**The real fix: split the single combined bridge into two.** Proved at the
term level (not just described) that this is possible because `evalNode_
dind` (§12.12, the *doc-only* bridge) has no `opaqueNames` hypothesis on
the node at all — checked its signature directly rather than assuming:
`∀ fuel node env, Node.callNames node ⊆ names → evalNode d1 fuel env node =
evalNode d2 fuel env node`, env held completely fixed. New proof shape,
same for both theorems:
1. `evalNode_dind r2_6_doc r2_4_doc/r2_2_doc cpp_names/pp_names hnames_cpp/
   hnames_pp hclosedC_cpp/hclosedC_pp` swaps the *doc* only, `env1`
   (`r2_6_env`-based) held fixed throughout — needs only `Node.callNames
   (.call …) ⊆ cpp_names/pp_names`, trivially true, no mention of `phiR` at
   all.
2. The `.call` node is then unfolded directly under `env1` via `evalNode`'s
   own `.call` equation (`simp only [evalNode, hfuel', …, hwx, hwz, hwxCap,
   hwzCap, hphi, hctrl/hx, hx, hz]`) — `hphi : evalA env1 phiR = .ok phi` is
   used exactly as given, no re-evaluation under any other env, so `phiR`'s
   own opaqueness is irrelevant here.
3. Only the *callee's* body (`r2_4_cppBody`/`r2_2_ppBody` — which never
   itself contains `"mod"`/`"modpow"`, those names only ever appeared in
   the caller's now-already-consumed argument expression) needs a bridge —
   and that bridge is env-only (`evalNode_ind r2_4_doc r2_4_doc …`/`r2_2_doc
   r2_2_doc …`, *same* doc on both sides, only `Env.call env1 […] [phi]
   […]` vs `cppEnv`/`ppEnv` differ), needing agreement only on `cpp_oNames`
   — exactly what the already-existing `hop'`/`hcoeff'` (built from `hop_
   cpp`/`hcoeff_cpp`/`hop_pp`/`hcoeff_pp`, §12.14–§12.15, untouched) already
   supply. `Env.call`'s `opaqueW`/`coeff` fields are inherited unchanged
   from the calling env (`Env.call`'s own doc comment: "the oracle … carried
   over unchanged" — confirmed by reading `IR/Instantiate.lean` directly,
   not assumed), so `(Env.call env1 …).opaqueW = env1.opaqueW` by `rfl`,
   letting `hop'`/`hcoeff'` apply to the *called* env with no restatement.
   `envcall_cpp_w_eq`/`_a_eq`/`_r_eq` (already generic over any calling
   `env`, not tied to a `cppEnv`-flavored one) supply the `w`/`a`/`r`
   agreement directly. Two small wrapper lemmas per theorem
   (`hclosedC_cpp4`/`hclosedO_cpp4`, `hclosedC_pp2`/`hclosedO_pp2`) restate
   the existing `hclosedC_cpp`/`hclosedO_cpp`/`hclosedC_pp`/`hclosedO_pp`
   (stated w.r.t. `r2_6_doc.find?`) against `r2_4_doc.find?`/`r2_2_doc.find?`
   instead, via `hnames_cpp`/`hnames_pp`'s existing equality — one line each.

**Net effect — a strict generalization, not a patch**: `hOwx`/`hOwz`/
`hOwxCap`/`hOwzCap`/`hOphi`/`hOctrl`(`cphase_product` only)/`hOx`/`hOz` — all
eight `opaqueNames = []` hypotheses — are gone from both theorems'
signatures entirely, and from the two `_flattenSeqAdj` wrappers built on top
of them (§12.20). The theorems now place **no restriction whatsoever** on
`wxR`/`wzR`/`wxCapR`/`wzCapR`/`phiR`/`ctrlR`/`xR`/`zR`'s syntactic shape —
any expression evaluating to the right value under `r2_6_env` now works,
`"mod"`/`"modpow"`-based angles included. `evalNode_call_qft`/`_flattenSeqAdj`
needed no change (already had no angle argument to restrict) — re-verified
anyway per the coordinator's request.

**One real bug caught and fixed during this round, not by design**: the
first attempt wrote `apply evalNode_dind r2_6_doc r2_4_doc cpp_names
hnames_cpp hclosedC_cpp fuel env1` — passing `fuel`/`env1` as further
positional arguments after the `hclosed` proof, matching `evalNode_ind`'s
own (different) argument order out of habit. `evalNode_dind`'s actual
signature takes `fuel`/`node`/`env` as the *conclusion*'s bound variables,
not extra explicit arguments to supply after `hclosed` — `apply` needs to
unify them against the goal, not receive them positionally. Lean reported
this immediately and precisely (`Application type mismatch: env1 has type
Env but is expected to have type Node`) — fixed by dropping the trailing
`fuel env1` from both `apply evalNode_dind …` calls, letting unification
supply them from the goal. Build went from 2 errors to 0 with just that
one-line-each fix; nothing else in the new proof shape needed correction.

**Verification, this round**: `lake build EmitProofs` → `Build completed
successfully (3321 jobs)`; `grep -c sorry` → `0`; no `native_decide` outside
prose comments; `#print axioms` re-checked standalone on all six
potentially-affected theorems (`evalNode_call_cphase_product`, `_phase_
product`, both `_flattenSeqAdj` wrappers, and `evalNode_call_qft`/`_flattenSeqAdj`
re-checked defensively at the time, believed unchanged — **turned out to be
wrong, see §12.25**) — all show only `propext`/`Classical.choice`/
`Quot.sound`, no `sorryAx`. **The §12.23 blocker (its `cphase_product`/
`phase_product` half) is closed.** Task #5's status at the time: Steps
1/2/4mul/4†mul/5's cores can now all use their real `"mod"`/`"modpow"`-based
angle arguments — `evalNode_step1`'s assembly (the next concrete
deliverable, abandoned mid-attempt in §12.23) believed unblocked.

### 12.25 R6.4 `shor` half: resuming `evalNode_step1` immediately surfaced a *second* instance of the same bug, in `evalNode_call_qft` — fixed the same way

§12.24's closing note ("`evalNode_call_qft` needed no change — already had
no angle argument to restrict") was **wrong**, caught immediately on
resuming the actual `evalNode_step1` assembly (not by inspection — by
`lake env lean` reporting `⊢ False` at the QFT leaf's opaqueNames
obligations, same failure shape as §12.23). The oversight: §12.23's finding
was framed around `phiR`'s *angle* argument specifically, but the same
class of bug afflicts `evalNode_call_qft`'s *register* arguments —
`xWorkR`/`zWorkR` at every outer QFT call site (Step 1's `adjQFT`, and by
the same reasoning every other step's) are `.reserveSlice (.var "work") …
(.opaque "qftXWork"/"qftZWork" […])` (`qftRArgs`, §12.21) — genuinely
non-empty `RegExpr.opaqueNames`, and `qftEnv`'s own `opaqueW` has no case
for `"qftXWork"`/`"qftZWork"` at all, the identical shape of impossibility
`cppEnv`/`ppEnv` had for `"mod"`/`"modpow"`. `evalNode_call_qft`'s old
`hOxWork`/`hOzWork` hypotheses were just as unsatisfiable at every real
adjoint-QFT call site as `hOphi` was — this was already true before §12.24,
just not noticed until an actual call site was attempted against it.

**Fix**: identical restructuring to §12.24, applied to `evalNode_call_qft`
and `evalNode_call_qft_flattenSeqAdj` — `evalNode_dind` (doc-only, `env1`
fixed) for the outer `.call`, direct unfolding under `env1` using `hr`/
`hxWork`/`hzWork`/`hw`/`hxWorkW`/`hzWorkW` as given, then an env-only
`evalNode_ind` bridge (`r2_5_doc` both sides) for just `r2_5_qftBody` (which
per its own ground-truth decomposition, §12.21, never itself references
`"qftXWork"`/`"qftZWork"` — those names only appear in the caller's
register-argument expressions, already consumed). Two small wrapper lemmas
(`hclosedC_qft4`/`hclosedO_qft4`, mirroring `hclosedC_cpp4`/`hclosedO_cpp4`)
restate `hclosedC_qft`/`hclosedO_qft` against `r2_5_doc.find?` via
`hnames_qft`. `hOw`/`hOxWorkW`/`hOzWorkW`/`hOr`/`hOxWork`/`hOzWork` (all six
opaqueNames-emptiness hypotheses) are gone from both theorems.

**Lesson for whoever continues past this point**: don't assume a leaf
theorem is unaffected by this class of bug just because it has no *angle*
parameter — check every `RegExpr`/`WExpr` argument position a call site
will actually instantiate with a non-trivial (`.opaque`-containing)
expression, not just the ones that happened to be the first one found. The
general symptom, worth recognizing on sight: `lake env lean` reports
`unsolved goals ⊢ False` (not a type error) at a `by simp [opaqueNames]`-
style hypothesis discharge — that shape means the hypothesis is *actually
false* for the expression being supplied, not merely hard to prove; check
whether it's structurally satisfiable at all before trying harder tactics.

**Verification, this round**: `lake build EmitProofs` → `Build completed
successfully (3321 jobs)`; `grep -c sorry` → `0`; no `native_decide` outside
prose comments; `#print axioms Shor.IR.evalNode_call_qft` and `_flattenSeqAdj`
re-checked standalone, both clean (`propext`/`Classical.choice`/
`Quot.sound`, no `sorryAx`). **All three leaf theorems (`evalNode_call_
cphase_product`/`_phase_product`/`_qft`) now place no `opaqueNames`
restriction whatsoever on their call-site arguments.** `evalNode_step1`'s
assembly resumes from here, genuinely unblocked this time.

### 12.26 R6.4 `shor` half: `evalNode_step1` closed — the first full `evalNode`-level Step assembly, `Node.call` leaves and all

The actual payoff of §12.19–§12.25's infrastructure work: `evalNode_step1`,
mirroring `evalNodeGate_step1` (§12.9, lines ~656–716) one level down —
`evalNode`/`LowGate` in place of `evalNodeGate`/`Gate`, `.call
"cphase_product"`/`.call "qft"` leaves in place of raw `.op
"CSignedPhaseProd"`/`.op "QFT"`, `flattenSeqAdj` in place of `flattenSeq`
throughout (needed since the adjQFT piece sits under `.adj(...)`, §12.19's
finding). No `sorry`, `#print axioms` clean.

**One correction to the theorem's own target, caught before merging, not
after**: the initial draft stated the core piece's target as bare
`lowerCSignedPhaseProdWithWorkspace ...`, omitting the `zeroExtend`/
`zeroDealloc` wrapping `CPhaseProdUsingGate` (§12.9's Gate-level composite)
actually has around its `CSignedPhaseProd` core — an oversight found by
`lake env lean` itself (a `'show' tactic failed` mismatch, not by manual
review), not a guess corrected preemptively. Fixed by rebuilding the full
5-piece composite (`zeroExtend(yData,1) ;; zeroExtend(work,1) ;;
lowerCSignedPhaseProdWithWorkspace(...) ;; zeroDealloc(work,1) ;;
zeroDealloc(yData,1)`) explicitly at the `evalNode` level — new leaf facts
(`hZeroExt1`/`hZeroExt2`/`hZeroDealloc1`/`hZeroDealloc2`, direct `buildLowGate`
unfolds via `simp only [evalNode, ..., buildLowGate]`, same idiom as
`evalNode_diffCmp`'s §12.18 zeroExtend/AddScaled/zeroDealloc triple)
combined with `hCore` through `r2_6_step1_core_eq`'s actual 4-level
right-nested `.seq` structure (confirmed via §12.21's ground truth, not
assumed flat) — this is the `evalNode`-level counterpart of `evalNodeGate_
CPhaseProdUsing` (§12.9), built inline here rather than as a separate
generic lemma (worth factoring out if Step 5's own `cphase_product` core
needs the identical shape, which it should).

**Proof-engineering note on combining nested `flattenSeqAdj`/`foldLowGateSeq`
facts, worth remembering**: `rw [flattenSeqAdj_foldLowGateSeq]` (leaving the
list argument implicit) is ambiguous once the goal contains *multiple*
nested `(foldLowGateSeq ?l).flattenSeqAdj`-shaped subterms at different
depths (here: the outer `[Hloop, rest]` pair *and* the deeply-nested
5-piece core composite both match) — `rw` picked an unintended occurrence
and left the goal in a form no subsequent `show` could match. Fixed by
supplying the list argument *explicitly* at each `rw [flattenSeqAdj_
foldLowGateSeq [...]]` call, pinning down exactly which occurrence gets
unfolded — the general lesson: when a rewrite lemma's LHS pattern can match
at more than one nesting depth in the same goal, make the instantiation
explicit rather than relying on `rw`'s occurrence-selection to guess right.
A second, smaller gap of the same flavor: the final combination step left
`X` (a local `set`-introduced abbreviation) unmatched against the
`ExtReg.withReserve ...`-literal form on the target's other side — closed
by adding `hXdef` (the `set`-generated equation) and `ExtReg.ofReg` (for a
similar `.active`-projection defeq gap on the QFT piece) to the closing
`simp only` call, rather than assuming `set`'s substitution reaches
occurrences introduced by the theorem's *own stated conclusion* (written
before the `set` call and never touched by it).

**Verification, this round**: `lake build EmitProofs` → `Build completed
successfully (3321 jobs)`; `grep -c sorry` → `0`; no `native_decide` outside
prose comments; `#print axioms Shor.IR.evalNode_step1` (re-checked in the
merged-file context) → `[propext, Classical.choice, Quot.sound]`, clean.
**Step 1's full `evalNode`-level assembly is done.** Task #5's next
deliverable: the same assembly for Step 2 (`phase_product` core, no `ctrl`)
and Step 5 (`cphase_product` core again, different register roles), Step
4's `mul`/`†mul` (two independent `phase_product` cores under one `.adj`
wrapper for `†mul`), then the `modExpApproxValid` loop-body assembly and
the top-level `H_reg`/`initY1`/loop/`IQFT` assembly — none started; Steps
2–5's own `Node`-level ground-truth decomposition (mirroring §12.21's
`nodeJson`-probed approach for Step 1) is also not yet built.

### 12.27 R6.4 `shor` half: `evalNode_step2` closed — second full `evalNode`-level Step assembly, QFT-first shape

Step 2's own `Node`-level ground-truth decomposition, probed the same way
as Step 1 (§12.21) via a throwaway `nodeJson`-dumping projector script
rather than assumed from the Gate-level skeleton: `r2_6_step2 = .seq
[QFT1, rest]`, `rest = .seq [core, adjQFT]` — the **same** two-level
right-nesting convention as Step 1, but with the QFT piece *first* and the
`H_reg` loop absent (Step 2 doesn't re-Hadamard; it reuses `y`'s existing
superposition, grown by 1). The register argument at both QFT call sites
resolves to `r2_6g_yGrow1Reg`, the pre-existing Gate-level ground-truth
register def (§12.9 era) — confirmed to match the real extraction
byte-for-byte, not merely isomorphic, so no new register-shape lemma was
needed, only a new `evalReg` fact for it (`evalReg_yGrow1_ir`, built from
`evalReg_grow_bare` plus `evalW_yW_ir`/`evalW_yCap_ir` fed through
`ExtReg.width_grow`/`Shor.ExtReg.capacity_grow`).

`evalNode_step2` itself mirrors `evalNode_step1`'s method exactly:
`evalNode_call_qft_flattenSeqAdj` for the QFT1/adjQFT pair (same call twice,
second one under `.adj`, matching §12.19's `NoAdj`-lift pattern), `evalNode_
call_phase_product_flattenSeqAdj` for the core (no `ctrl` argument here,
unlike Step 1's `cphase_product`), wrapped in the same `zeroExtend`/
`zeroExtend`/`.call`/`zeroDealloc`/`zeroDealloc` 5-piece composite pattern
built directly at the `evalNode` level via `buildLowGate`-unfold facts. No
`sorry`, `#print axioms` clean.

**Three proof-engineering traps hit and fixed, all recognized from earlier
sections' notes rather than re-discovered from scratch:**

1. **`evalW`-fact restructuring for opaque-width arguments** (`hxWorkW`/
   `hzWorkW`, the `qftXWork`/`qftZWork` widths at the *grown* register's
   width): the naive one-shot `rw [...]; congr 1; show ...; rwa [...] at
   this` chain failed because the target pattern didn't literally appear in
   the still-do-notation-wrapped goal at that point. Fixed by splitting into
   a clean intermediate fact at the raw `qftWorkspaceNeed`-pair level
   (`hxWorkW0`/`hzWorkW0`, mirroring `evalW_qftXWork_ir`'s own proof shape
   exactly) and only then bridging to the `ExtReg.ofReg (qftXWork ...)`-
   stated form via `congr 1; exact (regSize_qftXWork ...).symm`.
2. **`ExtReg.capacity_grow` unqualified-vs-qualified argument-count trap**
   (recurring from earlier sections, hit twice more here, in `hY1cg` and
   `hwzCapr`'s inner `hstep`): under `open Shor Shor.IR`, bare `ExtReg.
   capacity_grow` resolves to the *unconditional* 2-argument `Shor.IR.
   ExtReg.capacity_grow` (defined in `Proofs/PhaseProduct.lean`), not the
   3-argument `CanGrow`-gated `Shor.ExtReg.capacity_grow` — passing a
   `CanGrow` proof as a third positional argument to the unqualified name
   is a "Function expected" error, not a type mismatch, so it's easy to
   misdiagnose. Fixed by dropping the extra argument at the two unqualified
   call sites (the fully-qualified 3-arg form, correctly needed, stays as
   `Shor.ExtReg.capacity_grow y 1 hy1` inside `evalReg_yGrow1_ir`, which
   really does need the `CanGrow`-gated version, matching the original
   Gate-level `evalReg_yGrow1`'s proof obligation).
3. **`r2_6_env` `simp`-looping trap, recurred a third time** (`hphi`): any
   `simp [..., r2_6_env, ...]` call loops because `r2_6_env`'s `coeff` field
   is a genuine `dite`, not the trivial `fun _ _ => none` that `r2_6g_env`
   has (documented earlier this session for `evalNode_step2`'s Step-1-era
   analogue). Fixed by never `simp`-unfolding `r2_6_env` at all: `rw
   [ExtReg.width_grow y 1 hy1]; rfl` exposes the one needed width equality
   and closes by pure computation, no looping risk.

**Verification, this round**: developed and fully debugged in an isolated
scratch file (`lake env lean` on the standalone copy, 0 errors, `#print
axioms` clean, `sorry`-free) before merging, per the established workflow;
after merging into `Shor.lean`, `lake build EmitProofs` → `Build completed
successfully (3321 jobs)` (only pre-existing lint-level "unused simp
argument" warnings, no errors); `grep -c sorry` on the whole file → `0`; no
`native_decide`/`Lean.ofReduceBool`/`Lean.trustCompiler` outside prose
comments; `#print axioms` re-checked in the merged-file context for
`evalNode_step2` **and** re-checked on `evalNode_step1`/`evalNode_call_
cphase_product`/`_phase_product`/`_qft` (the theorems §12.24–§12.26 touched
or depend on) — all five show only `[propext, Classical.choice,
Quot.sound]`, no `sorryAx`, confirming the merge didn't silently invalidate
anything upstream. **Step 2's full `evalNode`-level assembly is done.**
Remaining for Task #5: Steps 3 (may already be largely done — §12.17–
§12.18's generic `evalNode_lowerCmpGeConst`/`_lowerCSubConst`/`_lowerStep3`
lemmas exist but haven't yet been wired against Step 3's own `Node`-level
ground-truth decomposition, which — like Steps 2–5 generally — is not yet
probed), 4mul/4†mul (two independent `phase_product` cores, the second
under `.adj`), and 5 (`cphase_product` again, different register roles);
then the `modExpApproxValid` loop-body assembly and the top-level `H_reg`/
`initY1`/loop/`IQFT` assembly — none of these started yet.

### 12.28 R6.4 `shor` half: Step 3's §12.17–§12.18 leaf theorems had never been checked against `r2_6_step3`'s real `Node` extraction — two genuine structural mismatches found and fixed

Resuming Step 3 (probing `r2_6_step3`'s real shape via `nodeJson`/`repr`, same
discipline as §12.21/§12.27) surfaced that `evalNode_lowerPrepareNegConst`/
`_lowerPrepFromFlag`/`_lowerCmpGeConst`/`_lowerCSubConst`/`_lowerStep3`
(§12.17–§12.18, previously marked "done") were never actually cross-checked
against Step 3's own `Node`-level extraction — only assumed correct by
analogy with the Gate-level skeleton. Two independent mismatches surfaced:

1. **The loop-body qubit lookup needs an `.activeSlice` wrapper.** The real
   extraction indexes `scratch`'s `i`-th active qubit inside the
   const-copy loop as `.qubit (.activeSlice scratchR 0 wExpr) (.var "i")`,
   not the bare `.qubit scratchR (.var "i")` all five theorems stated —
   confirmed via `#eval toString (repr ...)`, not just `nodeJson`'s
   pretty-printer (checked both independently, since a printer bug was a
   live hypothesis worth ruling out). Fixed by rewiring `evalNode_
   copyConstLoop_flattenSeqAdj`'s `dstR`/`dst` arguments in the two base
   theorems (`_lowerPrepareNegConst`/`_lowerPrepFromFlag`) to
   `.activeSlice scratchR 0 wExpr` / `ExtReg.ofReg scratch.active`, and a
   blanket text substitution of the literal across all five theorems'
   *statements* (`.qubit scratchR (.var "i")` → `.qubit (.activeSlice
   scratchR (.lit 0) wExpr) (.var "i")`, 21 occurrences, all within this
   section) — a strict fix to what was previously simply a wrong claim, not
   a generalization.
2. **`CSubConst`'s `prep` sub-circuit is extracted FLATTENED into its
   parent `.seq`, unlike `CmpGeConst`'s.** `CmpGeConst`'s `prep` (`X ;; loop
   ;; Negate`) stays nested as one `.seq [X,loop,Negate]` element inside the
   outer 8-element list (confirmed matching `evalNode_lowerCmpGeConst`'s
   existing literal, once (1) was fixed) — but `CSubConst`'s `prep` (`CNOT
   ;; loop ;; Negate`) is extracted as three SEPARATE siblings directly in
   the parent's 5-element list (`CNOT, loop, Negate, AddScaled, .adj(.seq
   [CNOT,loop,Negate])`), not nested as a first element the way `evalNode_
   lowerCSubConst`'s old statement assumed. Both `def lowerCmpGeConst`/
   `lowerCSubConst` build `prep` via an identical-looking `let prep := ...`
   in their own Lean source (`ConstArithmeticWorkspace.lean`), so this
   asymmetry is *not* explainable by source-level structure — it's whatever
   `extract_ir_doc`'s reflection macro happened to produce, underscoring
   the standing rule: never assume an extracted shape by analogy, always
   probe it. Fixed by restating `evalNode_lowerCSubConst`'s (and `_lowerStep3`'s
   inlined copy of it) literal as the flat 5-element list, and rebuilding
   its proof to build `hCNOTeval`/`hloopEval`/`hNegEval` as three separate
   `List.mapM` facts (mirroring `evalNode_lowerPrepFromFlag`'s own internal
   fact-building, not reusing it as one opaque `.seq`-shaped black box for
   this occurrence) while still reusing `evalNode_lowerPrepFromFlag` as-is
   for the second (adjoint, still genuinely nested) occurrence. The two
   shapes are `flattenSeqAdj`-equal regardless (list append is associative),
   so this is a statement-only correction, not a change to what's proved.

**A new reusable lemma, `lowerCopyBitPowers_active_eq`**: needed because
`dst := ExtReg.ofReg scratch.active` (from fix 1) has an *empty* reserve,
so it is never literally `scratch` itself (whose reserve is generally
nonempty) — yet `lowerPrepareNegConst`/`lowerCopyConstFromUnit`'s own
definitions are stated against `scratch` directly, so the final
`flattenSeqAdj` equality needs a bridge. `lowerCopyBitPowers` only ever
reads `.width`/`.active` (checked directly, never `.reserve`), so it agrees
for any two `ExtReg`s sharing the same `.active` field — proved not via a
propositional-equality congruence argument (which produced an unresolvable
`Fin`/`HEq` obligation, since two `ExtReg`s' `.width`-derived `Fin` *types*
genuinely differ even when the widths are propositionally equal) but by
`obtain`-destructuring both `ExtReg`s and `subst`-ing the shared `.active`
field so it becomes the literal *same* term on both sides — after which
`.width` and the `.get`-index proofs unify definitionally, no casting
needed, and a plain structural induction on the bit list closes it.

**A second Lean tactical lesson, worth stating plainly for whoever
continues:** a *single* `rfl` proving `r2_6_step3 = <full literal>` fails
even with `set_option maxRecDepth 100000` / `maxHeartbeats 0` (reporting
"is not definitionally equal", not a resource-exhaustion message) — yet the
IDENTICAL content, decomposed into a list-level `_eq_seq` split (`r2_6_
step3 = .seq [cmp, sub]`, cheap, bare `rfl`) plus one small `_eq` lemma per
list element (only the `.loop`/`.cond`-containing elements need the
elevated `set_option`s; the flat `.op` elements are instant even bare),
succeeds throughout, every time. The general lesson, now confirmed a third
time this session (after Step 1/Step 2's own `flattenSeqAdj_foldLowGateSeq`
occurrence-ambiguity lessons): never state one large `rfl` across
`r2_6_doc`-sourced content, no matter how deep `set_option` limits go —
always decompose to the smallest matchable piece first, exactly as every
other ground-truth section in this file already does.

**Verification, this round**: all fixes developed and checked incrementally
in throwaway scratch files (`lake env lean` on standalone copies) before
merging, per the established workflow; `lake env lean` on the full merged
`Shor.lean` → 0 errors (only pre-existing lint-level "unused simp argument"
warnings); `lake build EmitProofs` → `Build completed successfully (3321
jobs)`; `grep -c sorry` on the whole file → the one remaining match is this
prose sentence itself (`No sorry, #print axioms clean. -/`), not code; no
`native_decide`/`Lean.ofReduceBool`/`Lean.trustCompiler` outside prose
comments; `#print axioms` re-checked on all five restructured Step-3 leaf
theorems, the new `lowerCopyBitPowers_active_eq`/`evalReg_
scratchActiveFull` helpers, and (as a downstream sanity check, since they
were never touched but sit in the same file) `evalNode_step1`/`evalNode_
step2` — all ten show only `[propext, Classical.choice, Quot.sound]`
(`lowerCopyBitPowers_active_eq`/`evalReg_scratchActiveFull` show a strict
subset, `[propext]`/`[propext, Quot.sound]`, since they don't need
`Classical.choice`), no `sorryAx`.

### 12.29 R6.4 `shor` half: `evalNode_step3` closed — third full `evalNode`-level Step assembly, generic leaves reused unchanged

With §12.28's leaf-theorem fixes in place, `r2_6_step3`'s own ground-truth
decomposition was built the same decomposed way (`r2_6_step3_eq_seq` down
to sixteen `_eq`/`_eq_seq` lemmas covering both the 8-element `cmp` half and
the (now correctly flat) 5-element `sub` half — sixteen small `rfl`s, four
of them needing the elevated `maxRecDepth`/`maxHeartbeats` options, none of
them a monolithic literal match). `evalNode_step3` itself is then *pure*
`rw` — no `rfl`/`exact`-level literal unification at all — chaining all
sixteen `_eq`/`_eq_seq` lemmas to turn the opaque `r2_6_step3` into exactly
`evalNode_lowerStep3`'s expected literal shape, then closing with a single
`exact`. Six small new `r2_6_env`-lookup helpers were needed (`evalReg_
scratchVar_ir`/`_loop_ir`, `evalReg_flagVar_ir`, `evalW_scratchW_ir`/`_loop_ir`,
`evalW_NVar_loop_ir`), all mirroring the established `Env_bindW_r_ne`/
`_w_ne` idiom from §12.22–§12.23 exactly; `data := y.grow 1` reuses Step 2's
`hyGrow1`-style `evalReg_grow_bare` construction directly (the *bare*-grow
form, `.grow (.var "y") (.lit 1)`, not Step 2's `r2_6g_yGrow1Reg` full-ext
form — a different register expression plays the "data" role here than
played the QFT-input role in Step 2, confirmed by probing, not assumed).
`h3 : ConstArithmeticWorkspace N (y.grow 1) scratch flag` and `hNw`'s
derivation from `h3.constant_fits` are both taken/derived exactly as Step 1/
Step 2 took their own workspace hypotheses directly (not decomposed from
`ModMulCircuitWorkspaceOK`/`CmpLtNWWorkspace` — that decomposition is
top-level-assembly work, deferred like Step 1/2's was).

**Verification, this round**: `lake build EmitProofs` → `Build completed
successfully (3321 jobs)`, `grep -c sorry` clean (prose-only), no forbidden
tactics; `#print axioms Shor.IR.evalNode_step3` → `[propext, Classical.choice,
Quot.sound]`, `sorryAx`-free. **Steps 1, 2, and 3's full `evalNode`-level
assemblies are now all done.** Remaining for Task #5: Step 4mul/4†mul (two
independent `phase_product` cores, the second under `.adj`) and Step 5
(`cphase_product` again, different register roles) — own `Node`-level
ground-truth decomposition not yet probed for either, and per §12.28's
lesson, their own Gate-level-analogous leaf theorems (if any exist) must be
independently re-verified against real extraction before reuse, not assumed
correct by analogy; then the `modExpApproxValid` loop-body assembly and the
top-level `H_reg`/`initY1`/loop/`IQFT` assembly wiring `ShorApproxSetup`/
`ShorWorkspaceLargeEnough` down into each step's own workspace hypotheses
(mirroring `gateWorkspaceOK_orderFindingApprox`'s Gate-level pattern) — none
of this started yet.

### 12.30 R6.4 `shor` half: Step 4 and Step 5's own `Node`-level ground-truth decomposition, plus `evalNode_step4`/`evalNode_step5` — closed, all five Steps' `evalNode`-level assemblies now done

`r2_6_step4`/`r2_6_step5` had, per §12.21's comment, never been decomposed
past their top `r2_6_step4`/`r2_6_step5` projections. Ground truth for both
was probed fresh via a scratch `#eval IO.println (nodeJson r2_6_step4/5).pretty`
(`lake env lean` on a throwaway file, deleted afterward — not assumed from
the Gate-level `r2_6g_step4*`/`r2_6g_step5*` decomposition, per §12.28's
lesson), confirming: both are right-nested 2-element `.seq` throughout, the
same convention every other extracted body in this file already follows;
Step 4's `mul`'s `QFT`/`phase_product`-core/`adjQFT` triple renders through
`r2_6g_scratchReg`/`r2_6g_workReg` (the full-`.ext` register expressions
already defined for the Gate-level Step 4 decomposition) character-for-
character, confirmed not assumed; Step 4's `diff`/`cnot` carry no `.call` at
all (plain ops, identical shape to their Gate-level counterparts) and
`adjDiff`/`adjMul` are each a bare `.adj` of `diff`/`mul`; Step 5's own
`Hloop`/`adjQFT` turned out to be the **literal same** `Node` value as Step
1's (both act on `work`), and its core reuses `r2_6g_yGrow1Reg` (already
defined for Step 2). All decomposition theorems are plain `rfl`, checked
against the real extraction (`Proofs/Shor.lean`, new §12.30 section).

`evalNode_step5` was assembled first (closely mirrors `evalNode_step1`,
§12.26 — same `Hloop`/`adjQFT`-on-`work` machinery reused verbatim, same
`cphase_product` ctrl pattern reused from Step 1, Step 2's `(y.grow 1).grow 1`/
`work.grow 1` width/capacity arithmetic reused verbatim since Step 5's core
grows the same two registers just with `cphase_product`'s `ctrl` signature
swapping which argument position plays which role) plus one extra outer
`.adj` (Step 5's whole body is `.adj (Hloop ;; core ;; adjQFT)`, unlike Step
1) — handled by computing the inner `Hloop ;; core ;; adjQFT` piece's own
`flattenSeqAdj` fact first (`hInnerFlat`, built exactly the way `evalNode_
step1` builds its own final fact) and then lifting it through the outer
`.adj` with `flattenSeqAdj_adj_congr` in one line, rather than duplicating
the whole derivation under the extra wrapper.

Step 4 was assembled in two theorems: `evalNode_step4_mul` (`mul` alone —
`QFT scratch ;; phase_product-core ;; adj QFT scratch` — standalone so its
own `flattenSeqAdj` fact can be reused for `adjMul` via `flattenSeqAdj_adj_
congr`, exactly as Step 1/2/5 reuse one `evalNode_call_qft` result for their
own forward/adjoint occurrences, just one level up here since the whole
`mul` sub-circuit, not a single `.call`, is what gets reused under `.adj`)
and `evalNode_step4` (the full five-piece assembly: `mul`, `diff`, `cnot`,
`adjDiff`, `adjMul`). `mul`'s core arithmetic mirrors Step 1's *single-grow*
pattern (`work`/`scratch` each grown exactly once from their own base
register expression), not Step 2's chained double-grow — a genuine
structural difference from Step 2 caught by probing rather than assumed by
analogy, since Step 4's `mul` has no pre-existing `initY1`-style growth
layer under it the way Step 2's `y.grow 1` does. `diff`/`cnot`/`adjDiff` are
handled the same way `evalNodeGate_step4`'s own Gate-level `hDiff`/`hCNOT`
were (§12.9-era code, one level up): no `.call` at all, so no leaf theorem
or `flattenSeqAdj`-abstraction gap — direct literal `LowGate` values, and
`adjDiff` reuses `hDiff`'s own computed value under one more `.adj` exactly
as `adjMul` reuses `hMul`'s. Two hypotheses (`work.CanGrow 1`/`scratch.CanGrow
1`) had to be added as raw theorem parameters rather than derived from
`SignedRecursiveWorkspaceOK`, which turned out not to carry them (that
structure is about the *already-grown* registers' reserve sufficiency, not
about whether the ungrown registers have a free reserve slot to grow into at
all) — the same "take exactly what's needed, let the not-yet-started
top-level assembly derive it later" choice Step 1/5 already made for their
own `hworkspaceCPP`/`hworkspaceQFT` hypotheses.

One proof-engineering trap, worth flagging for whoever does the next
`evalNode`-level assembly: the `set env := … with henv` abbreviation (used
nowhere else in this file's Step assemblies, all of which spell the full
`(r2_6_env a N x y work scratch flag).bindW "e" e` out every time) silently
breaks reuse of `_ir` helper lemmas obtained *after* the `set` — `set`
abstracts the pattern only in hypotheses already in context at the point it
runs, not in facts introduced by later `have`/`obtain`, so `simp [foo_ir]`
then fails to fire with no hint beyond a generic "unrecognised op" unsolved-
goal dump. Fixed by dropping `set` entirely and writing the full expression
every time, matching the rest of the file's own established (if verbose)
convention — not a one-off; avoid `set` here again.

**Verification**: `lake build EmitProofs` → `Build completed successfully
(3321 jobs)`; `grep -c sorry Proofs/Shor.lean` → prose-only (one line reading
"No `sorry`…" inside a comment); no `native_decide` in any new theorem (the
file's only two hits are pre-existing prose mentions); `#print axioms` on
`evalNode_step4_mul`, `evalNode_step4`, and `evalNode_step5` all report
`[propext, Classical.choice, Quot.sound]`, `sorryAx`-free. **All five Steps
(1 through 5) now have a closed, verified `evalNode`-level assembly** — the
Task #5 work this section originally called out (Step 4mul/4†mul and Step 5)
is done. Each Step's theorem still takes its own workspace/fuel hypotheses
raw (not yet derived from `ShorApproxSetup`/`ShorWorkspaceLargeEnough`/
`CmpLtNWWorkspace`/`ModMulCircuitWorkspaceOK`), by the same deliberate choice
Steps 1–3 already made. **Still not started**: the `modExpApproxValid`
loop-body assembly (stitching the five Steps together for one loop
iteration) and the top-level `H_reg`/`initY1`/loop/`IQFT` assembly wiring
the umbrella workspace hypotheses down into each Step's own raw hypotheses
(mirroring `gateWorkspaceOK_orderFindingApprox`'s Gate-level pattern,
§12.11) — this is R6.4 `shor`'s only remaining work.

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

### 12.0b Prerequisite (discovered, not in the original plan): equality of `LowGate` terms must mean `flattenSeq`-equality, not raw equality

R6.1's first concrete target, `evalNode_naive_leaf` (`naive_leaf` against
`LowGate.Naive_SignedPhaseProd`, chosen — per §12.4's reasoning — as the
easiest theorem, with no table dependence and no register-slicing), turned
out to be **false** as a literal `Except LowGate` equality. `evalNode`'s
`.loop`/`.loop` unrolling produces *nested* `LowGate.sequence`s (one
`sequence` per loop level: an outer sequence of per-`i` results, each
itself a `sequence` over `j`), while `Naive_SignedPhaseProd` unfolds to one
*flat* `sequence` over a `flatMap`-built list. These are different
`LowGate` ASTs (different `.seq`/`.id` nesting) — provably different by
direct term inspection, not just hard to unify — even though they describe
the same circuit. This was not a proof-engineering obstacle to grind
through; it meant the theorem *as first stated* needed to be restated.

The fix is not a new convention invented for R6: it is the one this project
already uses everywhere else. `Json/README.md`'s `lowGateJson` compares
`LowGate`s via `LowGate.flattenSeq` (flattening nested `seq` nodes into an
ordered leaf list, dropping `id`s), and every R2 `native_decide` check in
`Tests.lean` that compares an `instantiate` result against a real term
does so via `lowGateJson`, never via raw `LowGate` equality (`r2_3_check`
in particular: `lowGateJson g == lowGateJson real`). So "the extracted
`Doc`, instantiated, equals the real circuit" has always meant "same
flattened gate sequence," not "same tree" — R6 needed to state that
explicitly instead of assuming raw equality would go through.

Two changes, both in `Emit/Json/LowGateJson.lean` and
`Emit/Proofs/Correct.lean`:

- `LowGate.flattenSeq` was `partial` (a second instance of §12.0's issue,
  found the same way): dropped, since `.seq a b`'s two recursive calls are
  on the strictly smaller subterms `a`/`b` — ordinary structural recursion,
  `partial` was unnecessary caution, exactly like `evalA`/`evalReg` in
  §12.0. Needed non-`partial` so R6 proofs get its equation lemmas.
- `flattenSeq_sequence : (LowGate.sequence l).flattenSeq = l.flatMap LowGate.flattenSeq`
  (in `Correct.lean`, proved by induction on `l`) is the general bridge:
  `flattenSeq` distributes over `sequence` exactly the way `List.flatMap`
  distributes over itself (`List.flatMap_map`/`List.flatMap_assoc` from
  Lean core do the rest). Every R6 theorem about a template whose extracted
  body loops (i.e. everything except leaf templates with no loop at all)
  will need this same lemma to reconcile nested-`sequence`-from-`.loop`
  against whatever flat-or-different-nesting shape the real term has.

Consequence for every remaining R6 theorem's *statement*: state it as
`∃ g, evalNode ... = .ok g ∧ g.flattenSeq = (real term).flattenSeq`, not
`evalNode ... = .ok (real term)`. `Correct.lean`'s `evalNode_naive_leaf` is
the template for this shape.

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
R6.5; regenerated, never hand-edited). A `lean_lib EmitProofs` is added to
`lakefile.lean` so `lake build EmitProofs` checks them; `Main.lean` does not
import `Proofs/`, so the executable neither needs nor waits for them.
Currently rooted at `FastMultiplication.Emit.Proofs.Correct` (the only file
R6.1 has produced so far) rather than `...Proofs.Shor` as originally
planned — `lean_lib` roots must name files that exist, and `Shor.lean`
doesn't yet; repoint at `...Proofs.Shor` once R6.4 adds it importing
`PhaseProduct`/`Qft`/`Shor`'s theorems (which will in turn import
`Correct`), the same way `Main.lean` isn't rooted at a file until it
exists. The two existing small proof files stay where they are because
they are not R6 theorems but decidability instances the emitter runs
(`Lower/Decide.lean`, `Table/Decide.lean`).


| step | deliverable | exit criterion |
|---|---|---|
| R6.1 | `Proofs/Correct.lean`: lemma library for `evalW`, `evalReg` slices/`grow`/`ext`, `evalA`, `Env.call`, `evalNode` on `seq`/`cond`/`loop` | lemmas build; used in R6.2 — **done for the leaf case**: `foldLowGateSeq_eq_sequence`, `flattenSeq_sequence`, `List.mapM_except_ok`/`_of_mem`, `signedTermsAux_eq`/`signedTerms_eq` proved (no `sorry`); `evalNode_naive_leaf` (stated via `flattenSeq` per §12.0b) closes, `#print axioms` shows only `propext`/`Classical.choice`/`Quot.sound`. The `evalReg` slice/`grow`/`ext` lemmas `phase_product` itself needs (§12.6's register-slicing risk) are folded into R6.2 below, since they're specific to `PhaseSplitLayout`/`ReserveBudget`, not general like the rest of this file |
| R6.2 | hand-written `r2_2_doc_phase_product_correct` (k = 2 standard) | theorem closes; `#print axioms` shows no `sorryAx`, and no `Lean.ofReduceBool` (i.e. no `native_decide` inside the proof) — **done** (as `evalNode_phase_product_correct`; see the row's tail for the closing note), `Proofs/PhaseProduct.lean`: ground truth for `r2_2_doc`'s `"phase_product"` template established by direct inspection (57 `Node`s; `body = .cond guard thenNode (.call "naive_leaf" …)`; `thenNode`'s 21 leaves — 5 alloc, 12 annotated-ops (3 recursive `call`s + 8 `AddScaled` + 1 `id`), 5 dealloc — read off and cross-checked against `r2_2_ops`'s 7 concrete operations and the compiler's own recursion, documented in the file's header comment). Proved: `evalProp_phase_product_guard` (the extracted guard decides exactly `nextSignedWidth x z ops < phaseInputSize x z`, via a lifted-and-generalized `nextWidth_eq_nextSignedWidth`), `evalNode_phase_product_base` (the `¬hrec` branch — `Env.call`'s result agrees with `naiveLeafEnv` on `w`/`a`/`r`, differing only in `opaqueW`/`coeff`, which `naiveLeafEnv` was generalized to take as parameters specifically so this reuse works — reduces directly to `evalNode_naive_leaf`). §12.6's register-slicing risk is now **resolved, not just assessed**: `evalReg_pp_ext0x`/`_ext0z`/`_ext1x`/`_ext1z` prove the extracted `.ext (.activeSlice …) (.reserveSlice …)` expression for each of the 4 `(side, chunk)` pairs equals the real `canonicalSignedStep`'s `PhaseSplitLayout.child`, for *every* `x, z` (not just `r2_2_k = 2`'s sampled widths) — including chunk 1's `fillSlack`/top-chunk-slack case, no `sorry`, `#print axioms` clean. The key discovery that made this tractable: `canonicalSignedStep`, despite being written in tactic mode, is an ordinary (non-recursive) definition, so `(canonicalSignedStep …).layout.xSplit.reserve i` for a *concrete* `i : Fin 2` reduces via plain `simp`/`rfl` in seconds — no need for the general `fillSlack_sum`/prefix-sum induction lemmas `Compiler/Workspace.lean` proves for symbolic `k` (`r2_2_k = 2` is concrete, so `List.ofFn`/`Fin` computation just runs). `Node.opRegsByName` (a `mutual`-recursive, non-`partial` tree search, `Correct.lean`-style) extracts each register expression's exact AST directly from `r2_2_ppThen`, `rfl`-checked, never hand-transcribed. The `.grow(extNy, delta)` lemmas are now **also done**: `evalReg_pp_grow0x`/`_grow0z`/`_grow1x`/`_grow1z` prove each extracted `.grow` expression equals `growExtRegTo (layout.child i) (nextSignedWidth x z ops)`, for every `x, z`, no `sorry`, `#print axioms` clean — turned out not to need the arithmetic fact the previous attempt stalled on (`(r.take n).qubits.length = n`); the width target `commonNeededWidth need` is *definitionally* `nextSignedWidth x z ops` (`Compiler/Widths.lean`), so `growExtRegTo`'s own definition (`e.grow (W - e.width)`) matches `evalReg`'s `.grow` case directly once `nextWidth_eq_nextSignedWidth` and each chunk's known width (`child_width_0`/`child_width_1`) are in hand — no new machinery beyond what `evalReg_pp_ext*` already established. (Proof-engineering note for whoever continues: getting these 4 lemmas to `simp`-close needed each one's lemma set tuned individually — e.g. `evalReg_pp_ext1x`'s rewrite needs `ppEnv` to stay folded, so reach for `evalW_ppEnv_xw`/`evalW_ppEnv_zw` for a bare `.var "xw"`/`"zw"` subterm rather than unfolding `ppEnv` wholesale, and close with a trailing `rfl` once `simp only` gets the goal down to a pure delta/iota reduction — see `Correct.lean`'s own `Except.bind`-reduction notes for why `simp only` alone sometimes can't finish what `rfl` can.) The angle-coefficient lemma is also **done**: `evalA_pp_coeff` proves `evalA (ppEnv x z phi) (.coeff (.var "phi") l limbW) = .ok (phi * loweringPhaseCoeff r2_2_k x z (genInterpolationPoints r2_2_k) (generatedInterpolationPoints_length r2_2_k) ⟨l, hl⟩)` for every `l < q r2_2_k`, no `sorry`, `#print axioms` clean — the bridge is `tableInstance .standard r2_2_k r2_2_hk`'s fields being *definitionally* `genInterpolationPoints r2_2_k`/`generatedInterpolationPoints_length r2_2_k` (`Table/Source.lean`'s `tableInstance`, `.standard` case), so `rfl` connects `ppEnv`'s `coeff` field (built from `tableInstance`) to `loweringPhaseCoeff`'s definition (built from `genInterpolationPoints` directly) with no new arithmetic. The base-case bridge to §12.2's actual target RHS is also **done**: `lowerGateRec_standardSignedPhaseLoweringPlan_base` proves the `¬hrec` branch of `standardSignedPhaseLoweringPlan.eq_1` lowers to `Naive_SignedPhaseProd phi x z` (`dif_neg` + the existing `@[simp] lowerGateRec_signedBase`, both by `rfl`), and `evalNode_phase_product_base'` restates `evalNode_phase_product_base` against `lowerGateRec (standardSignedPhaseLoweringPlan ...)` directly rather than the intermediate `Naive_SignedPhaseProd` — the exact base-case shape `evalNode_phase_product_correct`'s induction needs. `envCall_phase_product_eq` is also **done** (see the "Second round of research findings" paragraph below for its ground truth): `Env.call` at each recursive `.call "phase_product"` leaf's evaluated args equals `ppEnv` at the grown chunk-0 children and the scaled angle, for every `x, z, phi, l`, no `sorry`, `#print axioms` clean — needed a `.capacity` fact `evalReg_pp_grow*` didn't cover (`ExtReg.capacity_grow`, `child_capacity_0x`/`_0z`, `requiredXChildReserve_fits`/`requiredZChildReserve_fits`, `capacity_grow0x`/`_0z`) plus `width_grow0x`/`_0z` (reusing `Compiler/Widths.lean`'s already-proven `targetSignedLayoutState_xslot_width_scan`/`_zslot_width_scan` at `i = 0` — no new width-dominance fact needed). `r2_2_ops` itself now reduces to a literal too (`r2_2_ops_eq`, see the "Fourth round of research findings" paragraph below — a second, independent obstacle to the 21-leaf assembly, found and resolved this round). The allocation/deallocation plans are now **also done**: `lowerGateRec_planAllocChunkGate`/`lowerGateRec_planDeallocChunkGate` prove `lowerGateRec (planAllocChunkGate/planDeallocChunkGate initSize i src dst)` equals the expected `if extraDelta src dst = 0 then LowGate.id else if isTopChunk i then LowGate.signExtend/signDealloc … else LowGate.zeroExtend/zeroDealloc …`, for *every* `initSize, i, src, dst` (general, not tied to `r2_2_k`/`r2_2_ops` at all), no `sorry`, `#print axioms` clean — see the "Fifth round of research findings" paragraph below: a *third*, independent cast obstacle (this time on the `Gate` index, not `initSize`), found and resolved with the same `HEq`-erasure technique as the Third round's universe-cast fix, extended to this index (`lowerGateRec_heq_gate` + Lean core's `eqRec_heq`). The full allocation/deallocation plans at `k = 2` are now **also done**: `lowerGateRec_planCompileSignedAllocations_2`/`lowerGateRec_planCompileSignedDeallocations_2` unfold `planCompileSignedAllocations`/`planCompileSignedDeallocations` (ordinary structural recursion on `n`, no cast obstacle at this level) down to the full concrete 5-leaf `LowGate.seq` tree — reusing `lowerGateRec_planAllocChunkGate`/`lowerGateRec_planDeallocChunkGate` per leaf — no `sorry`, `#print axioms` clean. The allocation leaves' `evalNode` correspondence is now **also done**: `r2_2_ppAlloc` (the extracted allocation-branch subtree, `r2_2_ppThen`'s top-level `.seq [_, _]`'s first element) is ground-truthed by `rfl` (`r2_2_ppAlloc_eq`) as `.seq [.seq [id, .seq [cond0x, cond0z]], .seq [cond1x, cond1z]]`, and `evalNode_pp_cond0x`/`_cond0z`/`_cond1x`/`_cond1z` each prove `evalNode` on the corresponding `.cond`-guarded `zeroExtend`/`signExtend` node equals `lowerGateRec (planAllocChunkGate ...)` at that `(side, chunk)`'s child/grown-child — the extracted `extraDelta = 0` guard and the real `if extraDelta src dst = 0` branch agree (`extraDelta_grow0x`/`_grow0z`/`_grow1x`/`_grow1z`, chaining `width_grow0x`/`_0z` — already proved — with two **new** `width_grow1x`/`_1z` lemmas for chunk 1, same pattern), no `sorry`, `#print axioms` clean on all four. **A real bug was found and fixed in the process**: `r2_2_growDeltaX1W`/`r2_2_growDeltaZ1W` (chunk 1's `.grow` delta expressions, defined during the `.grow`-lemmas round) were missing a `.mul (.lit 1)` wrapper around `limbW` that the actual extracted term has (`nextWidth - (xw - 1·limbW)`, not `nextWidth - (xw - limbW)`) — numerically identical (`1 * n = n`), so the earlier `evalReg_pp_grow1x`/`_grow1z` were never *false*, just not yet checked against the real extracted AST (only `r2_2_ext1x`/`_ext1z`, the register side, had been `rfl`-ground-truthed so far, not the grow-delta side) — `rfl`-checking `r2_2_ppAlloc_eq` against the real term surfaced the mismatch immediately. Fixed by correcting the two `def`s (adding `.mul (.lit 1)`) and re-verifying every lemma that depends on them (`evalReg_pp_grow1x`/`_grow1z` needed one `Nat.one_mul` added to their `simp only` sets, then still closed by the same trailing `rfl` as before). The deallocation leaves are now **also done**, mirroring the allocation pattern exactly: `r2_2_ppRest`/`r2_2_ppBodyNode`/`r2_2_ppDealloc` (`r2_2_ppThen`'s remaining `.seq [alloc, .seq [body, dealloc]]` structure, `r2_2_ppThen_eq_seq`/`r2_2_ppRest_eq_seq`, both `rfl`) and `r2_2_ppDealloc_eq` (ground-truthed as `.seq [dealloc1z, .seq [dealloc1x, .seq [dealloc0z, .seq [dealloc0x, id]]]]`, top-first per `compileSignedDeallocationsAux`'s decreasing order), then `evalNode_pp_dealloc0x`/`_dealloc0z`/`_dealloc1x`/`_dealloc1z` — same `extraDelta`/`isTopChunk` case split as the allocation leaves, reusing the same `evalReg_pp_ext*`/`extraDelta_grow*` facts, no `sorry`, `#print axioms` clean on all four. **Both the allocation and deallocation branches are now fully assembled**: `evalNode_pp_alloc`/`evalNode_pp_dealloc` prove `evalNode` of `r2_2_ppAlloc`/`r2_2_ppDealloc` equals (up to `flattenSeq`) `lowerGateRec (planCompileSignedAllocations/planCompileSignedDeallocations ...)` at the concrete `initSignedLayoutState`/`targetSignedLayoutState` src/dst pair, assembling the 4+4 leaf lemmas via `flattenSeq`'s own `.seq`/`.id` equations (bridging the extracted side's `LowGate.sequence`-shaped list nesting, with a trailing `id` `LowGate.sequence [] = id` contributes nothing to, against the real plan's binary nesting), no `sorry`, `#print axioms` clean on both. A reusable `evalNode_pp_AS` lemma (`evalNode` of an extracted `AddScaled` leaf equals `LowGate.AddScaled dst src negSrc 0` given its two register arguments evaluate to `dst`/`src`) is proved for the 8 `AddScaled` leaves in the body to reuse. The recursive `.call` leaves are also **unfolded**: `r2_2_ppTemplate`/`r2_2_call_lookup`/`r2_2_ppTemplate_wParams`/`_aParams`/`_rParams`/`_body` ground-truth `phase_product`'s own template record (`rfl`, same `getD`-fallback method `r2_2_ppBody` itself uses), and `evalNode_pp_call` proves `evalNode` of a recursive `.call "phase_product"` leaf reduces to `evalNode` of `r2_2_ppBody` again at the grown chunk-0 children and scaled angle, one fuel step down — exactly the self-referential unfolding step the well-founded induction hypothesis is meant to discharge, no `sorry`, `#print axioms` clean. **R6.2 is done.** `evalNode_phase_product_correct` (§12.2's target theorem) closes: strong induction on `phaseInputSize x z`, base case `evalNode_phase_product_base'`, recursive case assembling `evalNode_pp_alloc`, the 12-leaf body (inlined directly in the induction's recursive case rather than as a standalone lemma, per the "Seventh round" note below — the 3 `.call` leaves via `evalNode_pp_call` composed with the induction hypothesis at `(canonicalSignedStep ...).childInputSize 0`/`.childWorkspace 0`, the 8 `AddScaled` leaves via `evalNode_pp_AS`), and `evalNode_pp_dealloc`. No `sorry`, no `native_decide`, `#print axioms` shows only `propext`/`Classical.choice`/`Quot.sound`. Two proof-engineering notes for R6.3/R6.4 (same shapes recur): (1) `refine ⟨_, ?_, ?_⟩` (even `refine ⟨_, ?_⟩; constructor`) on a goal `∃ g, P g ∧ Q g` fails with "don't know how to synthesize implicit argument/placeholder" whenever `P`/`Q` doesn't immediately pin the witness — always prove the first component as a fully-explicit-type `have` first (spelling out the witness value, even when tedious — e.g. nested `LowGate.sequence [...]` matching the real leaf structure), then `refine ⟨_, hFirst, ?_⟩`. (2) `set x := e with hx` abbreviations do *not* reliably get unfolded by `simp [hx]`/`simp [← hx]` once `x` appears alongside a proof term whose type also mentions `x` (here `standardSignedPhaseLoweringPlan ... cX0 cZ0 ... hcw0` with `hcw0 : SignedRecursiveWorkspaceOK r2_2_ops cX0 cZ0`) — `simp` silently declines the motive-incorrect rewrite rather than erroring; no rewrite is needed at all, since `cX0 = e` is definitional and any two proofs of the same `Prop` are proof-irrelevant, so the two sides are already defeq — close with a trailing `rfl` after `simp only`, don't force a syntactic rewrite.

**Seventh round of research findings — the precise remaining gap, after the eighth commit above** (not yet closed): every *leaf-level* correspondence R6.2 needs is now proved (alloc, dealloc, `AddScaled`, and the recursive-call unfolding step). What remains is strictly the *assembly*: (1) a ground-truth lemma for the 12-leaf annotated-ops body's `lowerGateRec` value, analogous to `lowerGateRec_planCompileSignedAllocations_2`, and (2) the well-founded induction on `phaseInputSize x z` itself (`evalNode_phase_product_correct`, PLAN.md §12.2's stated theorem, via the `∀ n, ... → phaseInputSize x z = n → ... → Nat.strong_induction_on` pattern). Item (1) is harder than the allocation/deallocation case for a structural reason, not a new cast/reduction obstacle: `planCompileAnnotatedOpsToSignedGateAux` takes an explicit `recurse` *function parameter* (`∀ i theta, PhaseLoweringPlan ... (Gate.SignedPhaseProd theta (st.xslot i) (st.zslot i))`), and the *specific* `recurse'` value `planCompiledSignedPhaseGate` (the caller) supplies is itself a `have recurse' := by simpa [src, dst, need] using recurse` — a value local to that other tactic-mode proof, not exposed under any name usable from `Proofs/PhaseProduct.lean`. So a body-level lemma cannot be stated purely in terms of `r2_2_ops`/`k = 2` the way the allocation/deallocation lemmas were (those needed no `recurse`-shaped parameter at all); it must either (a) take `recurse`/`recurse'` as an explicit generic hypothesis parameter (mirroring `planCompileAnnotatedOpsToSignedGateAux`'s own signature) and defer instantiating it with `standardSignedPhaseLoweringPlan`'s actual recursive call to the point where this lemma is *used*, inside the main induction (where `ih` is in scope to supply exactly the needed fact at each `.phaseProduct` leaf), or (b) skip a standalone body lemma entirely and inline the full 12-leaf `simp only [planCompileAnnotatedOpsToSignedGateAux]` unfolding (using `r2_2_annotatedOps_eq`) directly inside the induction's recursive case, where `ih` and `lowerGateRec_eqmp_final`/`hn0 := (canonicalSignedStep ...).childInputSize 0` are already available to discharge each `.phaseProduct` leaf as it's exposed. (b) is very likely the right approach — it avoids ever having to name the `recurse'`-parametrized intermediate lemma at all, matching the "Third round" notes' own advice to skip intermediate granularity and go straight for the fully-unfolded statement. Whoever continues should write the induction skeleton first (base case is a one-line application of `evalNode_phase_product_base'`; the guard/fuel bookkeeping for the recursive case — showing `phaseInputSize (grown chunk-0 children) < fuel - 1` given `hrec`/`hfuel` — is routine `omega`), then tackle the body assembly as the final step inside it, using `evalNode_pp_call`+`ih` for the 3 recursive leaves and `evalNode_pp_AS` for the 8 `AddScaled` leaves, combined via `flattenSeq`'s `.seq` equation and `List.append_assoc` the same way `evalNode_pp_alloc`/`evalNode_pp_dealloc` already bridge their own list/binary nesting mismatch (§12.0b's convention, applied at every level of nesting per the Sixth round's finding, not just the top level).

**Sixth round of research findings — the 12-leaf annotated-ops body's exact structure, discovered by direct probing rather than assumed** (`r2_2_ppBodyNode_eq`, now proved, `rfl`): the extractor's `.seq` grouping for the annotated-ops body is *not* a uniform one-leaf-at-a-time right-nested chain the way `planCompileAnnotatedOpsToSignedGateAux`'s own two-level `PhaseLoweringPlan.seq (AddScaled x) (PhaseLoweringPlan.seq (AddScaled z) tail)` shape (one extra `.seq` wrap per `addScaled` op, beyond the one for the op itself) would suggest by itself. Instead, `translateNode` groups each source op's own leaf gate(s) together with the tail as *one flat list*: `.seq [call, tail]` (2 elements) for a `phaseProduct` op (one leaf), `.seq [ASx, ASz, tail]` (3 elements) for an `addScaled` op (two leaves) — confirmed by building small ad-hoc `Node`-tree probes (`Node.seqLen`/`Node.seqFst`/`Node.seqNth`, discarded after use, not part of the committed lemma library) rather than guessing the shape and hoping `rfl` would silently confirm or deny it. Full structure: `.seq [call0, .seq [ASx2, ASz2, .seq [call1, .seq [ASx4, ASz4, .seq [ASx5, ASz5, .seq [call2, .seq [ASx7, ASz7, id]]]]]]]]` (`r2_2_ppBodyChain`). **Consequence for the remaining assembly**: since this extractor-side grouping genuinely differs in bracket shape from `lowerGateRec`'s own strictly-binary `PhaseLoweringPlan.seq`-mirrored nesting for the *same* leaves, the final per-leaf-group assembly (next) cannot use raw structural equality even at the level of one op's own leaf pair — it needs `flattenSeq`-based equality (§12.0b's convention) at this granularity too, not just at the top level between the whole extracted body and the whole real term. `LowGate.flattenSeq (.seq a b) = flattenSeq a ++ flattenSeq b` (`flattenSeq`'s own defining equation, `Json/LowGateJson.lean`) is what bridges a 3-element flat list against a 2-level-nested pair-plus-tail with the same leaf order — no new lemma needed beyond what's already committed, just applying `Correct.lean`'s `flattenSeq_sequence`/`foldLowGateSeq_eq_sequence` at each group the way `evalNode_naive_leaf` already did for its `.loop`-vs-`flatMap` mismatch.

Not yet done: the `evalNode` ↔ `lowerGateRec` correspondence for the 12 body leaves (content is now ground-truthed by `r2_2_ppBodyNode_eq`; connecting it to the real compiled values via `evalReg_pp_grow*`/`evalA_pp_coeff`/`envCall_phase_product_eq` — the call leaves' correspondence in particular needs either the well-founded induction hypothesis already in scope, or must be proved *inside* the induction directly, since a `.call "phase_product"` leaf recurses into the very theorem being proved); `evalNode_pp_alloc`/`evalNode_pp_dealloc` themselves (assembling the leaf lemmas already proved into one `flattenSeq`-equality statement per branch against `lowerGateRec_planCompileSignedAllocations_2`/`_Deallocations_2` — mechanical given the leaf lemmas, but not yet written, and needs the flattenSeq-not-raw-equality approach noted above); and the well-founded induction on `phaseInputSize x z` itself, which should be set up first (per the standard pattern: `∀ n, ∀ x z phi fuel hworkspace, phaseInputSize x z = n → phaseInputSize x z < fuel → ...`, `induction n using Nat.strong_induction_on`) since the recursive branch's `.call` leaves need the induction hypothesis, not a freestanding lemma about `ppEnv`/`r2_2_ppBody` alone.

**Fourth round of research findings** (one lemma proved, `r2_2_ops_eq`; a second, independent blocker on the 21-leaf assembly found and resolved): attempting the full assembly directly (`unfold planCompileAnnotatedOpsToSignedGateAux` then `simp`/`rfl`) exposed a *second*, separate obstacle from the universe-cast one above: `annotatePhaseTermsAux 2 0 r2_2_ops` — needed to know *which* of the 21 leaves is which, since `compileAnnotatedOpsToSignedGateAux` genuinely pattern-matches on `r2_2_ops`'s own structure (unlike the *extracted* IR side, where `r2_2_doc` is already a baked-in literal `IR.Node` AST the extractor computed once, needing no re-computation of `r2_2_ops` at proof time at all) — would not reduce via `rfl`/`unfold`, not slowly, but *genuinely stuck*. Bisected by testing `computeLocal2`/`addConstFrom` at concrete points in isolation: `Point.int 0` reduces fine (trivially, since `computeLocalAux`'s `nonzeroFins`-indexed loop hits `addConstFrom`'s `c = 0` fast path for every term when `z = 0`, never touching the `else` branch), but `Point.int (-1)` — i.e. any *real* point — does not, tracing to `addConstAux` in `Table_Generation/Builders/Fragments.lean`. Unlike every other definition in this computation chain, `addConstAux` is declared with `termination_by n _ => n` / `decreasing_by omega`, not plain structural recursion on a list argument — exactly the same class of issue `Emit/PLAN.md` §12.0 already found and fixed for `evalW`/`evalNode` (there, literally `partial def`): a `termination_by`-compiled definition has real `.eq_n` equation lemmas but compiles via `WellFounded.fix`, and its underlying `Acc.rec` does not reduce through plain `rfl`/`unfold`, only through `simp` using those equation lemmas. Once `addConstAux` is supplied to `simp` (alongside `genOpsWithProduct`/`opsForPointWithProduct`/`computeLocal2`/`computeFracLocal2`/`apply_Op_inverse`/`Operations.inv` and the standard `List.range`/`List.map`/`List.filter`/`Fin.finRange` unfolding lemmas), `r2_2_ops` reduces cleanly in a few seconds (not the "possibly minutes" its `Matrix.det`-adjacent coefficient-computation neighbours in this file might suggest — `addConstAux` was the only genuinely stuck step, not a performance problem). `r2_2_ops_eq` proves this concretely, matching the file's own header-comment ground truth exactly (`[phaseProduct 0, addScaled 0 1 true 0, phaseProduct 0, addScaled 0 1 false 0, addScaled 0 1 false 0, phaseProduct 0, addScaled 0 1 true 0]`), no `sorry`, `#print axioms` clean. Whoever continues the 21-leaf assembly should `rw [r2_2_ops_eq]` once, early, rather than including the whole reduction lemma set in every subsequent `simp` call on the giant goal — repeating the full reduction at every occurrence (there are many, since `r2_2_ops` appears inside `nextSignedWidth`/`scanNeededWidths`/`targetSignedLayoutState`/etc. at nearly every subterm) is expensive and was observed to make `simp` give up making progress on some occurrences partway through a single giant call. `r2_2_annotatedOps_eq` takes this further: `annotatePhaseTermsAux 2 0 r2_2_ops`'s own concrete value (the three `phaseProduct` leaves get interpolation terms `l = 0, 1, 2` in source order, everything else `none`), proved directly off `r2_2_ops_eq` (10s). This matters for *ordering*: unfolding `planCompileAnnotatedOpsToSignedGateAux` while `annotatePhaseTermsAux 2 0 r2_2_ops` is still symbolic (i.e. `unfold` before `rw [r2_2_ops_eq]`) timed out at 4M heartbeats — the static 5-case `match op with | .shiftL | .shiftR | .negate | .addScaled | .phaseProduct` gets instantiated once per (still-unresolved) list position, and the resulting term is too large for `simp`/`rfl` to push through in reasonable time. `rw [r2_2_annotatedOps_eq]` before unfolding `planCompileAnnotatedOpsToSignedGateAux` avoids this entirely, since the recursion then only ever sees concrete list positions.

**Fifth round of research findings** (a *third*, independent cast obstacle found and resolved — allocation/deallocation, not the recursive `.phaseProduct` leaves): `planAllocChunkGate`/`planDeallocChunkGate` (`PlanBuilders.lean`) are tactic-mode proofs (`unfold allocChunkGate; dsimp; split; · ⋯; · split; · ⋯; · ⋯`) whose *return type* — `PhaseLoweringPlan k hk pts hpts ops initSize (allocChunkGate i src dst)` — has the `Gate`-valued index `allocChunkGate i src dst` itself built from a `dite` (`extraDelta src dst = 0`, then `isTopChunk i`). Splitting a tactic-mode goal whose *type* depends on the branch (not just a hypothesis) forces Lean to generalize the motive over the index, producing `Decidable.rec`/`cast` terms in the result — confirmed genuinely stuck (not slow): `unfold planAllocChunkGate` followed by any of `split_ifs`, `by_cases` + `simp`, or `split <;> split` left a bare `lowerGateRec (Decidable.rec (fun h ↦ cast ⋯ ⋯) (fun h ↦ cast ⋯ ⋯) (instDecidableEqNat ⋯))` that no combination of `simp`/`rfl`/`simp_all` could push `lowerGateRec` through, because `dif_pos`/`dif_neg` are stated for `dite`, not the raw `Decidable.rec` eliminator the tactic-generated term actually uses. The fix mirrors the Third round's universe-cast fix, extended from the `initSize` index to the `Gate` index: `lowerGateRec_heq_gate` (respects `HEq` across a `Gate`-index change, exactly like `lowerGateRec_heq` does for `initSize` — `lowerGateRec`'s output, `LowGate`, doesn't depend on *either* index) combined with Lean core's `eqRec_heq : HEq (h ▸ a) a` (the `▸`-flavored counterpart of `eqmp_heq`, no new general lemma needed) lets you cast `planAllocChunkGate`'s *opaque* value along a **proven** `Gate`-level equality (e.g. `allocChunkGate i src dst = Gate.id`, itself just `unfold allocChunkGate; simp [h0]` once `h0 : extraDelta src dst = 0` is in hand from `by_cases`) rather than trying to reduce through whatever cast is already baked into the term. Once the cast value's `Gate` index is a literal constructor application, `cases (hU ▸ p : PhaseLoweringPlan … Gate.id) with | id _ => rfl` closes it directly (`lowerGateRec`'s own pattern match has only one viable case for that index, so the case split is total and the remaining goal is `rfl`). `lowerGateRec_heq_gate`/`lowerGateRec_planAllocChunkGate`/`lowerGateRec_planDeallocChunkGate` are committed, no `sorry`, `#print axioms` clean, and fully general (not tied to `r2_2_k`/`r2_2_ops`/any concrete `i, src, dst` — reusable for R6.3's `cphase_product` too, whose `planAllocChunkGate`/`planDeallocChunkGate` calls are identical).

**The universe-cast obstacle (Third round's blocker) is now resolved, generally.** Rather than trying to predict the cast's exact syntactic shape (the `congrArg`-based guess `lowerGateRec_cast` needed did not match the real term — `simp` reported it unused), the fix sidesteps knowing the shape at all: `eqmp_heq {α β : Type} (h : α = β) (p : α) : HEq (Eq.mp h p) p` (general, not `PhaseLoweringPlan`-specific — true by proof irrelevance for the `Prop`-valued equality `α = β`, regardless of which specific term proves it, `by cases h; rfl`) combined with `lowerGateRec_heq` (respects `HEq` given the `initSize` equality supplied *directly*, not extracted from the cast) gives `lowerGateRec_eqmp_final : lowerGateRec (Eq.mp h p) = lowerGateRec p` for *any* `h`, needing only the index equality (`hn0`, from `(canonicalSignedStep ...).childInputSize 0`, already available per the Second round's notes) as an explicit argument. Confirmed empirically: `simp only [lowerGateRec_eqmp_final hn0]` — one `hn0`, since all three recursive `.phaseProduct` leaves recurse into the same chunk-0 children (Second round's finding) — collapses all three casts cleanly. Combined with `simp only [planCompileAnnotatedOpsToSignedGateAux]` (not `unfold`, which only unfolds one list position at a time; `simp only` repeats until the whole concrete 12-element list from `r2_2_annotatedOps_eq` is consumed) and `PhaseLoweringPlan.lowerGateRec_seq`, this produces the **full 12-leaf body**, all three recursive calls already in clean, cast-free `lowerGateRec (standardSignedPhaseLoweringPlan ...)` form (confirmed by direct inspection of the resulting goal — every leaf concrete: three recursive calls at `l = 0, 1, 2`, eight `AddScaled`s with concrete slot/sign arguments, one trailing `.id`). No remaining unresolved cast anywhere in the body. `eqmp_heq`/`lowerGateRec_heq`/`lowerGateRec_eqmp_final` are committed, no `sorry`, `#print axioms` clean (`eqmp_heq` needs no axioms at all).

**What's left for R6.2, now that both major obstacles (register-slicing, and this one) are resolved**: `planCompileSignedAllocations`/`planCompileSignedDeallocations` still need the same "expand fully to concrete leaves" treatment (structurally simpler than the body — no casts, no recursive calls, just `zeroExtend`/`signExtend`/`zeroDealloc`/`signDealloc`/`cond`/`id` per chunk); then the full per-leaf correspondence against `evalNode`'s evaluation of `r2_2_ppThen`'s matching 21 leaves (reusing `evalReg_pp_ext*`/`evalReg_pp_grow*`/`evalA_pp_coeff`/`envCall_phase_product_eq` for each leaf's arguments, `Correct.lean`'s `foldLowGateSeq_eq_sequence`/`flattenSeq_sequence`/`List.mapM_except_ok_of_mem` for the sequencing, per §12.0b's `flattenSeq`-based equality); and the well-founded induction itself, invoking the induction hypothesis at each of the 3 recursive leaves via `hn0`-style measure-decrease facts. The two hardest, most uncertain pieces are now behind this work — what remains is large but mechanical, following the same patterns already established and verified throughout this file.

**Research findings for whoever tackles the assembly/induction** (traced through `Lowering/Plan.lean` and `Lowering/PlanBuilders.lean`, not yet turned into proofs): `lowerGateRec` does *not* walk `compileOpsToSignedGate`'s `Gate` value directly — it walks a *dependently-typed* `PhaseLoweringPlan` witness that `standardSignedPhaseLoweringPlan` builds alongside it, constructor-for-constructor (`planCompileSignedAllocationsAux`/`planCompileAnnotatedOpsToSignedGateAux`/`planCompileSignedDeallocationsAux` in `PlanBuilders.lean`, one `PhaseLoweringPlan` constructor per `Gate` constructor). `lowerGateRec`'s equations for every *primitive* constructor (`.id`, `.seq`, `.AddScaled`, `.zeroExtend`, …) are already `@[simp]` lemmas named `lowerGateRec_*` in `Proofs/Lowering/Lowerable.lean`, so once a concrete plan is in hand, unfolding it to a concrete `LowGate` is mechanical `simp`. The one non-mechanical step is `standardSignedPhaseLoweringPlan`'s recursive case (`by_cases hrec`, `PlanBuilders.lean` L359-409): at each `.phaseProduct i` leaf with interpolation term `l`, the plan's `recurse i theta` field calls `standardSignedPhaseLoweringPlan k hk theta (dst.xslot i) (dst.zslot i) ops hchild` where `theta = phi * phaseCoeff l` (exactly `evalA_pp_coeff`'s RHS), `dst.xslot i`/`dst.zslot i` are `targetSignedLayoutState`'s *grown* slots (exactly `evalReg_pp_grow0x`/etc.'s RHS for `r2_2_k = 2`'s three `phaseProduct` positions), and `step.childInputSize i : phaseInputSize (dst.xslot i) (dst.zslot i) = nextSignedWidth x z ops` (already proved in `Compiler/Workspace.lean`, reusable directly — this is exactly the well-founded measure decrease the induction needs, so it does not need re-deriving). So `lowerGateRec (standardSignedPhaseLoweringPlan k hk phi x z ops h)`, at each recursive leaf, equals `lowerGateRec (standardSignedPhaseLoweringPlan k hk theta childX childZ ops hchild)` — i.e. the *same theorem being proved*, applied to strictly smaller `phaseInputSize`, which is exactly what `evalNode_phase_product_correct`'s well-founded induction hypothesis should discharge each `.call "phase_product"` leaf with, *without* needing to unfold `PhaseLoweringPlan`'s dependent machinery inside `Proofs/PhaseProduct.lean` at all — the target statement can stay purely in terms of `lowerGateRec (standardSignedPhaseLoweringPlan ...)`, letting `Lowering/Plan.lean`'s own `@[simp]` lemmas and `PlanBuilders.lean`'s existing constructions do the `Gate`-level unfolding.

**Second round of research findings** (confirmed empirically, not yet turned into proofs): `planCompiledSignedPhaseGate`'s tactic-mode `by ... simpa [...] using completePlan` body unfolds *cleanly* via plain `unfold planCompiledSignedPhaseGate` — no `Eq.mpr`/cast noise blocks further reduction, it reduces straight to a `let`-chain ending in `PhaseLoweringPlan.seq allocationPlan (PhaseLoweringPlan.seq bodyPlan deallocationPlan)`, so `PhaseLoweringPlan.lowerGateRec_seq` applies directly afterward — one less risk than expected. Extracted the 3 recursive `.call "phase_product"` leaves' exact `wArgs`/`aArgs`/`rArgs` from `r2_2_ppThen` by direct inspection (a `Node.callArgsByName` walker, same method as `Node.opRegsByName`): all three calls share *identical* `wArgs = [nextWidthW, nextWidthW, reserveNeedXW, reserveNeedZW]` and `rArgs = [grow(ext0x, growDeltaX0W), grow(ext0z, growDeltaZ0W)]` — i.e. every one of `r2_2_ops`'s three `phaseProduct` operations references register-slot index `0`, so all three recurse into *chunk 0* only, never chunk 1 (chunk 1's `ext1x`/`ext1z`/`grow1x`/`grow1z` lemmas are needed for the *allocation*/*deallocation* leaves' `zeroExtend`/`signExtend`/`zeroDealloc`/`signDealloc` arguments, not for any recursive call) — and they differ *only* in `aArgs = [phi * coeff(l, limbW)]` for `l = 0, 1, 2` respectively, matching `annotatePhaseTermsAux`'s left-to-right numbering of `r2_2_ops`'s three `phaseProduct` leaves. This pins down exactly what `envCall_phase_product_eq` (the self-referential analogue of `envCall_naive_leaf_eq`, needed to show `Env.call` at a `.call "phase_product"` leaf's evaluated args equals `ppEnv (child-x) (child-z) theta` for the induction hypothesis to apply to) needs to state.

**The `.capacity` gap, now resolved**: `ppEnv`'s `w` field maps `"xCap"`/`"zCap"` to `x.capacity`/`z.capacity`, and `Env.call`'s substitution at the `.call` leaf plugs in `reserveNeed_x`/`reserveNeed_z` (evaluated) for those slots, so `envCall_phase_product_eq` needs a fact about how `ExtReg.grow` changes `.capacity`, not just `.width` (`width_growExtRegTo` in `Compiler/Layout.lean` only covers the width side). Four new lemmas in `Proofs/PhaseProduct.lean`, no `sorry`, `#print axioms` clean: `ExtReg.capacity_grow (e n) : (e.grow n).capacity = e.capacity - n` (general — `List.length_drop` is *unconditional*, unlike the width/active side, which needs `CanGrowTo`; no bound required at all here). `child_capacity_0x`/`_0z`: `((canonicalSignedStep …).layout.xSplit/zSplit.child 0).capacity = RecursivePhaseWorkspace.requiredXChildReserve/requiredZChildReserve r2_2_ops x.width z.width 0` — needed re-deriving the one bound `canonicalSignedStep`'s own tactic-mode proof establishes locally but doesn't expose (`hxfit`/`hzfit`, `(List.ofFn reqX).sum ≤ x.capacity`): pulled out as standalone `requiredXChildReserve_fits`/`requiredZChildReserve_fits`, reusing the *already-exposed* `requiredXChildReserve_sum`/`requiredZChildReserve_sum` plus `SignedRecursiveWorkspaceOK`'s own `x_reserve_sufficient`/`z_reserve_sufficient` fields and `reserveNeed_fst`/`_snd` — without this bound `List.take`'s length clamps at the parent's *actual* capacity rather than the requested size, so `List.length_take`'s `min` doesn't collapse to the right side. Finally `capacity_grow0x`/`_0z`: `(growExtRegTo (layout.xSplit/zSplit.child 0) (nextSignedWidth x z ops)).capacity = (RecursivePhaseWorkspace.reserveNeed r2_2_ops (nextSignedWidth …) (nextSignedWidth …)).1/.2` — chains `capacity_grow` with `child_capacity_0x`/`child_width_0` and `requiredChildReserve`'s arithmetic definition (`(Wnext − childWidth) + reserveComponent`): the `Wnext − childWidth` summand cancels exactly against `capacity_grow`'s `− n`, leaving the `reserveComponent` alone — precisely `envCall_phase_product_eq`'s needed fact. `evalW_pp_reserveNeedX`/`_reserveNeedZ` round out the `wArgs`: `evalW (ppEnv x z phi) reserveNeedXW/reserveNeedZW = .ok (RecursivePhaseWorkspace.reserveNeed r2_2_ops (nextSignedWidth …) (nextSignedWidth …)).1/.2`, same `.opaque`-unfolding pattern as `evalW_pp_nextWidth`. And the last piece needed to match `Env.call`'s substituted `"xw"`/`"zw"` slots against `ppEnv (growExtRegTo …) (growExtRegTo …) theta`'s own `w` field — `width_grow0x`/`_0z`: `(growExtRegTo (layout.xSplit/zSplit.child 0) (nextSignedWidth x z ops)).width = nextSignedWidth x z ops` — turned out to already be proven, generally, in `Compiler/Widths.lean` (`targetSignedLayoutState_xslot_width_scan`/`_zslot_width_scan`, using `CanonicalSignedStep`'s own `.capacity` field as the `CanGrowToNeeds` hypothesis they need) — no new width-dominance fact had to be derived at all, just cited at `i = 0`. `envCall_phase_product_eq` is now **done**: `Env.call (ppEnv x z phi) ["xw","zw","xCap","zCap"] [nextWidth, nextWidth, reserveNeed_x, reserveNeed_z] ["phi"] [phi * coeff_l] ["x","z"] [grow0x, grow0z] = ppEnv grow0x grow0z (phi * coeff_l)`, for every `x, z, phi, l < q r2_2_k` — no `sorry`, `#print axioms` clean. Proof mirrors `envCall_naive_leaf_eq`'s `congr 1`/`funext`/`by_cases` structure (4 `w`-cases instead of 2), using `width_grow0x`/`_0z` and `capacity_grow0x`/`_0z` for the four `w`-slot facts; `opaqueW`/`coeff` need no case analysis at all, since `ppEnv`'s fields for those never reference `x, z, phi` (only the fixed `r2_2_ops`/`r2_2_k`), so `Env.call`'s `{env with …}` carry-over is *syntactically* the same closed term either way. One tactic pitfall hit and fixed along the way: plain `simp` (not `simp only`) on a goal containing `RecursivePhaseWorkspace.reserveNeed r2_2_ops (nextSignedWidth …) (nextSignedWidth …)` hits `maximum recursion depth` — `reserveNeed_fst`/`_snd` are `@[simp]`, and applying them to *symbolic* `nextSignedWidth x z r2_2_ops` arguments (never reducing to a literal base case) unfolds indefinitely; fixed the same way `evalReg_pp_ext0x` etc. already do, `-RecursivePhaseWorkspace.reserveNeed_fst -RecursivePhaseWorkspace.reserveNeed_snd` in every `simp` call that touches a `reserveNeed`-shaped term. Not yet done: the 21-leaf assembly, and the well-founded induction. |

**Third round of research findings** (confirmed empirically; one general lemma proved, the full assembly still open): the top-level split of `lowerGateRec (standardSignedPhaseLoweringPlan …)`'s `hrec` branch is now `rfl`-checked exactly as predicted. `rw [standardSignedPhaseLoweringPlan.eq_1, dif_pos hrec]; simp only [PhaseLoweringPlan.lowerGateRec_signedStep]; unfold planCompiledSignedPhaseGate; simp only [id, PhaseLoweringPlan.lowerGateRec_seq]` turns `lowerGateRec (standardSignedPhaseLoweringPlan r2_2_k r2_2_hk phi x z r2_2_ops hworkspace)` into exactly `LowGate.seq (lowerGateRec allocationPlan) (LowGate.seq (lowerGateRec bodyPlan) (lowerGateRec deallocationPlan))` — the stray `id` wrapper around the whole thing (an artifact of `planCompiledSignedPhaseGate`'s `have …; have …; id recurse`-shaped tactic proof) unfolds away for free once `id` itself is in the `simp only` set. `standardSignedPhaseLoweringPlan`'s own recursive case (`PlanBuilders.lean` L371–384) confirms the induction-hypothesis shape directly: `recurse i theta`'s body is `have childPlan := standardSignedPhaseLoweringPlan k hk theta (dst.xslot i) (dst.zslot i) ops hchild; have hsize : phaseInputSize (dst.xslot i) (dst.zslot i) = nextSignedWidth x z ops := …; simpa [hsize] using childPlan` — literally a recursive call to the theorem being proved, cast along `hsize` (which is exactly `(canonicalSignedStep …).childInputSize i`, already available). Tried to state an *intermediate* lemma stopping at this alloc/body/dealloc split (with `bodyPlan`'s `recurse` argument left as an explicit lambda using `(canonicalSignedStep …).childInputSize i ▸ standardSignedPhaseLoweringPlan …`) and hit a real obstacle: after all the same unfolding, the goal's cast (from `simpa`'s auto-generated `Eq.mp`) and the hand-written statement's cast (`▸`) reduce to `Eq.rec.{1, 2} …` vs `Eq.rec.{1, 1} …` — a *universe-level* mismatch in the inferred motive, not just a proof-term difference, so bare `rfl` (which does respect ordinary proof irrelevance) genuinely fails here. Proved the general fix instead of chasing the specific motive: `lowerGateRec_cast {…} (h : n1 = n2) (p : PhaseLoweringPlan k hk pts hpts ops n1 U) : lowerGateRec (h ▸ p) = lowerGateRec p := by subst h; rfl` (no `sorry`, `#print axioms` clean) — `lowerGateRec`'s output (`LowGate`) doesn't depend on the `initSize` index at all, so a cast along *any* proof of `n1 = n2` is `lowerGateRec`-irrelevant, sidestepping the motive question entirely by substituting the equality away before comparing. The catch: this lemma's LHS pattern (`lowerGateRec (h ▸ p)`) can only match once `lowerGateRec` is applied *directly* to the cast term — but at the alloc/body/dealloc granularity, the cast is buried inside `bodyPlan`'s `recurse` *function argument* (passed to `planCompileAnnotatedOpsToSignedGateAux`, never itself wrapped in `lowerGateRec` at that level), so `simp only [lowerGateRec_cast]` reports the lemma unused — there's nothing to rewrite yet. The fix is not a better cast lemma; it's the right granularity: `lowerGateRec (recurse i theta)` only becomes a literal subterm once `planCompileAnnotatedOpsToSignedGateAux` is itself unfolded over the concrete `annotatePhaseTermsAux r2_2_k 0 r2_2_ops` list down to its 12 leaves (at the `.phaseProduct` case, `PhaseLoweringPlan.seq (recurse i theta) tail`'s `lowerGateRec` splits via `lowerGateRec_seq` into `LowGate.seq (lowerGateRec (recurse i theta)) (lowerGateRec tail)`, exposing `lowerGateRec (recurse i theta)` directly) — at which point `lowerGateRec_cast` applies cleanly and the recursive leaf collapses to `lowerGateRec (standardSignedPhaseLoweringPlan r2_2_k r2_2_hk theta childX childZ r2_2_ops hchild)` with no cast at all, ready to match against the induction hypothesis. Whoever continues should skip the intermediate alloc/body/dealloc-level lemma entirely and go straight for the fully-unfolded 21-leaf statement, applying `lowerGateRec_cast` (already committed, reusable) at each of the 3 phase-product leaves as they're exposed.
| R6.3 | `r2_4_doc_cphase_product_correct`, `r2_5_doc_qft_correct` | same — both **done**: `r2_4_doc_cphase_product_correct` (§12.7: `Proofs/CPhaseProduct.lean`) and `r2_5_doc_qft_correct` (§12.8: `Proofs/Qft.lean`), no `sorry`, `#print axioms` clean on both |
| R6.4 | `shor_gate` and `shor` theorems for the k = 2 standard `Doc` | same; plus the corollary `instantiate … = .ok (referenceShorCircuit …)` — `shor_gate` half **done** (§12.9–§12.11): `evalNodeGate_shor_gate` (`Proofs/Shor.lean`) is the full Gate-level correctness theorem for `orderFindingApprox`, closed, no `sorry`, `#print axioms` clean; `shor` half **in progress — leaf-lemma engineering done, top-level assembly not started** (§12.12–§12.16): the 14-`Node.call` body is ground-truthed; `evalNode_dind` (doc-independence) and `evalNode_ind` (doc+env/opaqueW-independence, the second required bridge) are both proved and merged, no `sorry`, `#print axioms` clean; the hybrid-env leaf technique they unlock is generic per template name (one theorem covers every call site of that name) and all three needed leaves are now closed and merged — `evalNode_call_cphase_product` (§12.14, both `cphase_product` sites), `evalNode_call_phase_product` (§12.15, all 3 `phase_product` sites), `evalNode_call_qft` (§12.16, all 9 `qft` sites) — `native_decide` removed from every closure-verification lemma (`Node.callNames`/`Node.opaqueNames` don't kernel-reduce, worked around via chaining through ground-truth `_eq` lemmas), no `sorry`, `#print axioms` clean on all three; Step 3 (`CmpGeConst`/`CSubConst`) **done** (§12.17–§12.18): `LowGate.flattenSeqAdj` (a required new adjoint-recursing equality notion, plain `LowGate.flattenSeq`'s `.adj g => [g]` doesn't recurse and blocks comparing `.adj`-wrapped Step 3 values) and the bit-copy loop lemma (a new `Nat.bitIndices`-vs-loop combinatorial bridge) came first, then the full composite assembly (`evalNode_lowerPrepareNegConst`/`_lowerPrepFromFlag`/`_diffCmp`/`_lowerCmpGeConst`/`_lowerCSubConst`/`_lowerStep3`), generic over register/weight expressions; no `sorry`, no `native_decide`, `#print axioms` clean throughout; the NoAdj-bridge (`LowGate.NoAdj`/`Node.NoAdj`/`evalNode_noAdj`, §12.19–§12.20) is also **fully done, both halves** — corrects §12.17's framing (essentially every step 1/2/4mul/4†mul/5, not just Step 3/4/IQFT, embeds a QFT+adjQFT pair and needs `.flattenSeq`-stated leaf facts lifted to `flattenSeqAdj` inside the `.adj(...)` wrapper via `flattenSeqAdj_eq_flattenSeq_of_noAdj`); §12.20 closed the two pieces §12.19 left open — `LowGate.NoAdj` facts about the real lowered circuits (`lowerGateRec_noAdj`/`lowerQFTPlan_noAdj`, unconditional since neither function's equations ever emit `.adj`) and `Node.NoAdj` facts about `qft`/`phase_product`/`cphase_product`/`naive_leaf`/`naive_cleaf`'s own extracted bodies (via R6.2/R6.3's existing `_eq` decomposition lemmas fed into one `simp [Node.NoAdj, ...]` call each) — plus the three lifted leaf theorems `evalNode_call_cphase_product_flattenSeqAdj`/`_phase_product_flattenSeqAdj`/`_qft_flattenSeqAdj`, no `sorry`, `#print axioms` clean; the `Node`-level ground-truth decomposition of `r2_6_doc`'s "shor" body through Step 1's `Hloop`/`core`/`adjQFT` is now also **done** (§12.21, `r2_6_shorBody_eq_seq` through `r2_6_step1_core_eq`, twelve theorems, all plain `rfl`, probed against real `nodeJson` dumps rather than guessed blind — confirms §12.12's predicted skeleton exactly, register-wiring at QFT call sites now a committed fact via `qftRArgs`); the `evalNode`-level Hadamard-loop lemma, all `r2_6_env` var-lookup facts, and `work`'s QFT-workspace register facts are now **also done** (§12.22–§12.23, all merged, no `sorry`); the §12.23 blocker (`evalNode_call_cphase_product`/`_phase_product` required `AExpr.opaqueNames phiR = []`, unsatisfiable for Step 1/2/4mul/4†mul/5's real `a^(2^e) mod N`-shaped angles) is now **fixed** (§12.24): both theorems restructured to split the doc-swap (`evalNode_dind`, env fixed, no opaqueNames condition) from the env-swap (`evalNode_ind`, applied only to the *callee's* body, which never itself uses `"mod"`/`"modpow"`) — all eight `opaqueNames = []` hypotheses (on both theorems and their `_flattenSeqAdj` wrappers) are gone entirely, a strict generalization; resuming the actual assembly immediately surfaced a **second instance of the identical bug** in `evalNode_call_qft` (§12.25 — `xWorkR`/`zWorkR`'s `.opaque "qftXWork"`/`"qftZWork"` reserve-split expressions, not an angle argument this time, hit the exact same unsatisfiable-opaqueNames shape) — fixed the same way, all six of `evalNode_call_qft`'s opaqueNames hypotheses also gone; `lake build EmitProofs` green, `#print axioms` re-verified clean on all eight now-restructured theorems (both leaf pairs plus their `_flattenSeqAdj` wrappers, plus `evalNode_call_qft`/`_flattenSeqAdj`); `evalNode_step1` is now **done** (§12.26) — the first complete `evalNode`-level Step assembly, `H_reg` loop + the `zeroExtend`/`zeroExtend`/`.call "cphase_product"`/`zeroDealloc`/`zeroDealloc` core composite + the `.adj (.call "qft" …)` piece, all combined via `flattenSeqAdj`, no `sorry`, `#print axioms` clean; `evalNode_step2` is now **also done** (§12.27) — same method, QFT-first shape (no `H_reg` loop, `.call "qft"` piece before the `phase_product` core rather than after), reusing the pre-existing `r2_6g_yGrow1Reg` ground-truth register def, no `sorry`, `#print axioms` clean; resuming Step 3 found that §12.17–§12.18's `evalNode_lowerPrepareNegConst`/`_lowerPrepFromFlag`/`_lowerCmpGeConst`/`_lowerCSubConst`/`_lowerStep3` had never actually been checked against `r2_6_step3`'s real extraction — two genuine structural mismatches (a missing `.activeSlice` wrapper on the loop-body qubit lookup, and `CSubConst`'s `prep` sub-circuit being extracted flattened into its parent `.seq` rather than nested the way `CmpGeConst`'s is) — both **fixed** (§12.28, statement-only corrections, `flattenSeqAdj`-equal either way, plus a new reusable `lowerCopyBitPowers_active_eq` helper and a confirmed-a-third-time lesson that `r2_6_doc`-sourced `rfl`s must always be decomposed to the smallest matchable piece, never attempted as one large literal even with elevated `set_option maxRecDepth`/`maxHeartbeats`); `evalNode_step3` is now **also done** (§12.29) — Step 3's own sixteen-lemma ground-truth decomposition plus a pure-`rw` assembly (no literal-matching `rfl`/`exact` needed at all once the leaves were fixed), no `sorry`, `#print axioms` clean. Step 4 and Step 5's own `Node`-level ground-truth decompositions (probed fresh via `nodeJson`, not assumed from the Gate-level decomposition) and their `evalNode`-level assemblies (`evalNode_step4_mul`/`evalNode_step4`/`evalNode_step5`) are now **also done** (§12.30) — Step 5 mirrors Step 1 closely (literally the same `Hloop`/`adjQFT` `Node` values, on `work`), Step 4 is assembled as `evalNode_step4_mul` standalone (so `adjMul` can reuse its `flattenSeqAdj` fact via `flattenSeqAdj_adj_congr`, one level up from how Step 1/2/5 reuse a single `.call "qft"` result) plus `evalNode_step4` combining `mul`/`diff`/`cnot`/`adjDiff`/`adjMul` (`diff`/`cnot` are plain ops with no `.call`, handled the same way Gate-level `evalNodeGate_step4`'s own `hDiff`/`hCNOT` were); no `sorry`, no `native_decide`, `#print axioms` clean on all three. **All five Steps (1 through 5) now have a closed, verified `evalNode`-level assembly.** Remaining: the `modExpApproxValid` loop-body assembly, and the top-level assembly wiring all 14 concrete `.call` sites plus Step 3's two occurrences to `r2_6_env`'s actual var lookups and `ShorApproxSetup`/`ShorWorkspaceLargeEnough` down into each step's own workspace hypothesis — not yet started |
| R6.5 | proof-script generator in `extract_ir_doc!`; regenerate all of the above from it | generated proofs close for k = 2 and k = 3 standard with no per-k edits |
| R6.6 | D7/README/provenance updated: `template.provenance` says "proved for all widths (R6)" when the theorem exists for that `Doc` | text matches what is proved |

### 12.6 Risks

- **Register lemmas — resolved for `r2_2` (k = 2).** `evalReg_pp_ext0x`/
  `_ext0z`/`_ext1x`/`_ext1z` in `Proofs/PhaseProduct.lean` prove `evalReg`'s
  slices are the layout's children, for every `x, z`. Turned out easier
  than feared: `canonicalSignedStep`'s tactic-mode body is still an ordinary
  term, so its data (not just its type) reduces via `simp`/`rfl` once `k`
  is concrete — no `Reg` extensionality or hand-rolled `offset` arithmetic
  lemma was needed, `ReserveBudget.offset`/`fillSlack`'s `List.ofFn`/
  `Function.update` just compute. The one wrinkle: `simp [ppEnv, ...]` in
  one call loops (`ppEnv.eq_1` against `RecursivePhaseWorkspace.
  reserveNeed_fst`, both `@[simp]`) — fixed by `unfold ppEnv` first, then
  `simp` without `ppEnv` in the same call, and separately excluding
  `reserveNeed_fst`/`_snd` from the `simp` that normalizes the disjointness
  hypothesis (same loop, different trigger).
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
