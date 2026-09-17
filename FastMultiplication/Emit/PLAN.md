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
| D5 | **Concrete table required.** Inputs to the symbolic emitter are exactly `k` and `TableSource`. Symbolic: `n, m, a, N` (Shor), `W, phi, x, z` (phase product), `w, r` (QFT). |
| D6 | **Reference instances stay.** `pp`, `cpp`, `qft`, `shor` and their annotated views remain; they are what the extracted IR is checked against. |
| D7 | **Not a theorem.** Trusted: the translation table and Lean's normaliser. Evidence: `instantiate` unrolls the IR at concrete widths and compares byte for byte with the real term, at every depth, at emit time and in tests. The provenance says exactly this. |

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
| R2.2 | `phase_product` | `.eq_def` rewrite of `WellFounded.fix`, `Node.call` to self, `cond` on `nextSignedWidth < phaseInputSize` | equals `lowerSignedPhaseProdWithWorkspace` at `n = 8` (base) and `n = 16` (recurses) |
| R2.3 | `naive_leaf` | `loop` over `signedTerms` of a symbolic register, `AExpr.mul` with two's-complement weights | equals `Naive_SignedPhaseProd` at widths 1..6 |
| R2.4 | `cphase_product`, `naive_cleaf` | `ctrl` parameter, `CCPhase` | as R2.2 at `n = 16` |
| R2.5 | `qft` | `Nat.casesOn` on symbolic width, `qftXWork`/`qftZWork` slices, `RadixReverse` | equals `lowerQFT` at `w = 2..8` |
| R2.6 | `shor_gate`, `shor` | `loop` over exponent bits, `adj`, instance parameters, `allocateReferenceLayout` offsets | `shor_gate` equals `orderFindingApprox` as `Gate`, and `shor` equals `referenceProgramAt` at `k = 2, a = 2, N = 15, m = 0` |
| R2.7 | genericity | none | R2.2 and R2.5 criteria at `k = 3` standard and at `k = 2 --table generate`, with **no change** to `Extract.lean` or `Targets.lean` |

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
- [ ] R2.1–R2.7 exit criteria as `native_decide` in `Tests.lean`, all green (R2.1 done; R2.2–R2.7 not started).
- [ ] `forshor_emit template 2`, `template 3`, `template 2 --table generate` exit 0 with `instantiate_eq_real: true`.
- [ ] `forshor_emit bundle 2` contains the extracted `template` and the trimmed tables; `--no-template` skips the load.
- [ ] Old files and fields removed per §8; `grep -rn "Template.lean\|affineTail\|census\|template_match" Emit` is empty.
- [ ] README rewritten; `PLAN.md` statuses updated per step.
