# `Lower/`

Concrete-width instances — the real, verified circuits at a width you
choose, not the n-free `bundle` document. This is where `pp`, `cpp`, `qft`,
and `shor` are built, and where the E7 templates get checked against the
real compiled term.

Import order: `Decide.lean → Instantiate.lean → PhaseProduct.lean, Qft.lean`.
`Shor.lean` is independent of the other three (it doesn't need `Decide.lean`
or `Instantiate.lean` — it has no workspace precondition to discharge on the
fly, and `--annotated` isn't implemented for it; see below).

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
product via the real lowering.

- `ppRegisters {k} (ops) (n) : Except String (ExtReg × ExtReg × ℕ)` —
  registers `x = [0, n)`, `z = [n, 2n)`, reserves placed immediately after
  each, sized by `RecursivePhaseWorkspace.reserveNeed ops n n` plus one bit
  each; a control qubit (for `cpp`) placed past both registers' full extent.
  Active/reserve disjointness (needed just to call `ExtReg.withReserve`) is
  discharged with `if hx : Disjoint xActive xReserve then ... else .error
  ...` — decidable at this concrete `n`, from `Decide.lean`.
- `buildPP`/`buildCPP (k n) (phiNum phiDen) (annotated) : Except String
  Json` — discharge `SignedRecursiveWorkspaceOK`/`CSignedRecursiveWorkspaceOK`
  the same way, then either:
  - `annotated = true` (the default): build `standardSignedPhaseLoweringPlan`/
    `standardCSignedPhaseLoweringPlan`, run all three `Lower/Instantiate.lean`
    checks against it, embed the results under `meta.checks`, and refuse
    (`.error`) if any failed; otherwise print `planJson` via `emitPlanDoc`.
  - `annotated = false` (`--flat`): print `lowerSignedPhaseProdWithWorkspace`/
    `lowerCSignedPhaseProdWithWorkspace` via `emitLowGateDoc` directly, no
    checks.

## `Qft.lean`

The `qft` subcommand, same shape as `PhaseProduct.lean`:

- `qftRegister {k} (ops) (w) : Except String ExtReg` — one register of
  width `w`, reserve sized by `qftWorkspaceNeed ops w`, active/reserve
  disjointness discharged the same way.
- `buildQFT (k w) (annotated) : Except String Json` — discharges
  `QFTReserveOK`, then either builds `reserveQFTLoweringPlan`, runs check 1
  (`annotated_eq_flat`) and check 3's QFT variant (`split`), embeds them
  under `meta.checks`, and prints via `qftPlanJsonOf`/`emitPlanDoc`; or
  (`--flat`) prints `lowerQFT` directly via `emitLowGateDoc`.

## `Instantiate.lean`

The three instantiation checks tying the annotated plan, the flat
`LowGate`, and the E7 template together at a concrete checked width.
Re-scoped from a literal "byte for byte" / multi-level design: full fidelity
would mean recursively unrolling the template and replaying
`PhaseSplitLayout.ofBudget`'s exact physical-qubit assignment algorithm — a
new sub-system, not a check.

1. **Annotated = flat** (`check1_annotatedEqFlat`). `deepFlattenPlanJsonList`
   splices `seq` nodes fully and substitutes `SignedPhaseProd`/
   `CSignedPhaseProd` annotations with their `expansion`/`body` (recursing
   into the `expansion` too — it's itself `lowGateJson`'s output for a
   `LowGate.seq`, not an opaque leaf; this was a real bug the first time
   check 1 ran, caught immediately by testing at a recursion-triggering
   width). `wrapFlattened` then presents the result the same way
   `lowGateJson` would (single item as itself, `id` as `{"op":"id"}`,
   otherwise one `seq` node), and it's compared to `lowGateJson` of the
   independently-computed flat term via `BEq Json`. Scoped to `pp`/`cpp`/`qft`
   (their terms contain no `Gate.adj`, which this flattener doesn't
   descend into).
2. **Template ≈ annotated, one level** (`check2_signed`/`check2_csigned`).
   Two halves:
   - *Widths*: `WExpr.eval` interprets a `Symbolic/Template.lean` `WExpr` at
     a concrete `W`, realizing `nextWidth` as
     `RecursivePhaseWorkspace.nextWidth ops`. The template's `limb_width`
     and each slot's width, evaluated this way, must equal the real
     compiler's own numbers — `phaseLimbWidth` and `PhaseSplitLayout.child`'s
     width, read directly off the annotated plan's `layout` field (obtained
     by pattern-matching the plan on `.signedStep`/`.cSignedStep`).
   - *Shape*: `shallowFlattenPlanJsonList` splices `seq` nodes but stops at
     a nested `SignedPhaseProd`/`CSignedPhaseProd` (unlike check 1's deep
     flatten — this is what makes the comparison "one level"). `opSignature`
     projects each op down to its shape-relevant fields (the tag, plus
     `negSrc`/`shift` for `AddScaled`); a phase-product node — `PhaseProduct`/
     `CPhaseProduct` on the template, `SignedPhaseProd`/`CSignedPhaseProd`
     on the real plan — normalizes to one canonical tag with no further
     fields, since the template's `child` interpolation-point index has no
     counterpart on the real plan's node (which carries all `q k`
     coefficients, not one selected index) — this exact mismatch was the
     second bug check 2 caught on first use. `check2_shapeMatch` compares
     the two projected sequences for equality.
   `none` if the plan is already at a base case — nothing for check 2 to
   compare (the template's own `recursion` field already says the naive
   primitive applies there).
3. **Ladder** (`check3_ladder`, `check3_qftSplit`). `planDepth`/
   `planLeafCount` walk the plan counting `.signedStep`/`.cSignedStep`
   nesting and `.signedBase`/`.cSignedBase` leaves; compared against
   `Symbolic/Recursion.lean`'s `widthLadder`'s length and `q k ^ depth`.
   `qftPlanSplits`/`check3_qftSplit` do the same for `QFTLoweringPlan`,
   comparing every `.split` node's widths to E4's `splitM`-based formula.

`PhaseProduct.lean`/`Qft.lean` run all of these automatically whenever
`--annotated` is requested (the default), embedding the results under
`meta.checks` and refusing with exit `3` if any fails — so a failing check
here is not just a test-suite signal, it's a live gate on what the CLI will
print.
