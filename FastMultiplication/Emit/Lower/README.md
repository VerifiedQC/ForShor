# `Lower/`

Concrete-width instances — the real, verified circuits at a width you
choose, not the n-free `bundle`/`template` document. This is where `pp`,
`cpp`, `qft`, and `shor` are built, and where the extracted templates
(`Reflect/`, `IR/`) get checked against the real compiled term at whatever
width the caller actually asked for (`instantiate_eq_real`).

Import order: `Decide.lean, Registers.lean → Reflect/Verify.lean →
PhaseProduct.lean, Qft.lean`. `Shor.lean` is independent of the others (it
doesn't need `Decide.lean` — it has no workspace precondition to discharge
on the fly, and `--annotated` isn't implemented for it; see below).

## `Decide.lean`

Every workspace precondition the rest of this folder needs to discharge
(`SignedRecursiveWorkspaceOK`, `CSignedRecursiveWorkspaceOK`, `QFTReserveOK`,
and the plain `Disjoint active reserve` needed just to build an `ExtReg` at
all) is a `Prop`-valued structure built entirely from `≤` on `ℕ` (already
decidable) and `ExtReg.OwnedDisjoint`/`ExtReg.CtrlDisjoint` (disjointness of
concrete `List ℕ` qubit lists). **No `Decidable` instance for the latter two
existed anywhere in the repo or in `.lake/packages`** before this file —
every existing construction of these structures elsewhere is an abstract
tactic proof from assumed hypotheses, never a decidability check against
concrete registers.

- `decidableRegDisjoint`, `decidableExtRegOwnedDisjoint`,
  `decidableExtRegCtrlDisjoint` — the two base instances, via `unfold;
  infer_instance` (the same idiom already used twice elsewhere in the repo
  for other decidable `Prop`s: `isTopChunk`, `Layout.lean:104-107`;
  `outcomePred`, `MeasureClass.lean:16-20`). `List.Disjoint`'s `∀ ⦃a⦄, a ∈
  l₁ → a ∈ l₂ → False` shape is exactly the bounded-forall form
  `List.decidableBAll` already covers for `DecidableEq α`.
- `decidableSignedRecursiveWorkspaceOK`, `decidableCSignedRecursiveWorkspaceOK`,
  `decidableQFTReserveOK` — whole-structure instances via `decidable_of_iff`
  against the conjunction of each structure's fields, so callers can write
  one `if h : ... then ... else refuse` instead of nesting one per field.

Everything downstream discharges these at a **concrete** width supplied on
the command line — there is no abstract proof for general `n`/`w` anywhere
in `Lower/`.

## `Registers.lean`

Concrete register construction, shared by `PhaseProduct.lean`/`Qft.lean`
(the `pp`/`cpp`/`qft` CLI commands) **and** `Reflect/Verify.lean`'s
instance-check canary — split into its own file specifically so
`Verify.lean` can build the same registers those commands do without
importing them back (they need `Verify.lean` for their own
`instantiate_eq_real` check, so the dependency has to run this direction).

- `ppRegisters {k} (ops) (n) : Except String (ExtReg × ExtReg × ℕ)` —
  registers `x = [0, n)`, `z = [n, 2n)`, reserves placed immediately after
  each, sized by `RecursivePhaseWorkspace.reserveNeed ops n n` plus one bit
  each; a control qubit (for `cpp`) placed past both registers' full extent.
  Active/reserve disjointness (needed just to call `ExtReg.withReserve`) is
  discharged with `if hx : Disjoint xActive xReserve then ... else .error
  ...` — decidable at this concrete `n`, from `Decide.lean`.
- `qftRegister {k} (ops) (w) : Except String ExtReg` — one register of
  width `w`, reserve sized by `qftWorkspaceNeed ops w`, active/reserve
  disjointness discharged the same way.

## `Shor.lean`

`Emit.Lower.Shor.runEmit (k a N m) : IO UInt32` — the `shor` subcommand:
builds `Shor.standardLoweringSetup k hk`, the instance, and
`Reference.referenceProgramAt lowering m inst`, then prints it via
`emitProgram`. Also prints a `layout` block (`Shor.Reference.layoutJson`,
`allocateReferenceLayout`'s four registers and flag qubit).

`--annotated` is **not implemented**: it would need the raw pre-lowering
`Gate` tree, which `referenceProgramAt` doesn't expose separately from its
already-lowered `LowGate` result, plus a per-leaf workspace-discharge walk
over `Gate.QFT`/`(C)SignedPhaseProd`/`CmpGeConst`/`CSubConst` (the last two
needing a new `ConstArithmeticWorkspace` `Decidable` instance, alongside
this file's own `Decide.lean`) — its own research-and-implementation arc
beyond what `PhaseProduct.lean`/`Qft.lean` already cover for the phase-product
and QFT leaves individually.

## `PhaseProduct.lean`

The `pp`/`cpp` subcommands: concrete-width signed (and controlled) phase
product via the real lowering. `unsafe`/`IO` since the annotated view
extracts the template by reflection (`Reflect.runExtractAndVerify`) to run
`instantiate_eq_real`.

- `buildPP`/`buildCPP (k n) (phiNum phiDen) (annotated) : IO (Except String
  Json)` — discharge `SignedRecursiveWorkspaceOK`/`CSignedRecursiveWorkspaceOK`
  (via `ppRegisters`, `Decide.lean`), then either:
  - `annotated = true` (the default): build `standardSignedPhaseLoweringPlan`/
    `standardCSignedPhaseLoweringPlan`, extract+verify the `Doc`
    (`Reflect.runExtractAndVerify k` — standard table only; R5, §11), run
    `check1_annotatedEqFlat` (`Json/PlanJson.lean`) and
    `Reflect.phaseProductAgrees`/`cPhaseProductAgrees` (now `(hk) (ops)`,
    not `(k) (hk) (src)` — `instantiate_eq_real`: the extracted template,
    instantiated at *this* `n`, agreeing with the real compiled term),
    embed both under `meta.checks`, and refuse (`.error`) if either failed;
    otherwise print `planJson` via `emitPlanDoc`.
  - `annotated = false` (`--flat`): print `lowerSignedPhaseProdWithWorkspace`/
    `lowerCSignedPhaseProdWithWorkspace` via `emitLowGateDoc` directly, no
    checks, no reflection.

`Emit/PLAN.md` R3/R4: this replaced the old `template_match`/`ladder`
checks (`Symbolic/Template.lean`/`Symbolic/Recursion.lean`, both deleted)
with a check against the *extracted* template directly.

## `Qft.lean`

The `qft` subcommand, same shape as `PhaseProduct.lean`:

- `buildQFT (k w) (annotated) : IO (Except String Json)` — discharges
  `QFTReserveOK` (via `qftRegister`), then either builds
  `reserveQFTLoweringPlan`, extracts+verifies the `Doc`, runs
  `annotated_eq_flat` and `Reflect.qftAgrees` (`instantiate_eq_real`),
  embeds them under `meta.checks`, and prints via
  `qftPlanJsonOf`/`emitPlanDoc`; or (`--flat`) prints `lowerQFT` directly
  via `emitLowGateDoc`.

(The old `split` check, tied to `Symbolic/Recursion.lean`-adjacent
`Lower/Instantiate.lean`, was dropped along with that file in R3/R4 —
`instantiate_eq_real`'s full-depth agreement subsumes what it was checking.)
