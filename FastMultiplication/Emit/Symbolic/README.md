# `Symbolic/`

The n-free `bundle` document: sections E2 through E7, plus `Bundle.lean`,
which assembles them (and E1, from `Table/Census.lean`) into one JSON
document and exposes the CLI-facing builders (`buildBundle`, `buildSection`,
`buildPhases`).

The `E1`–`E7` names are the top `README.md`'s cross-reference labels for
"the section of the `bundle` document that answers this question" — they
appear in code comments throughout this folder and in the top-level
`README.md`'s `referenceProgramAt` diagram.

Import order: `CoeffPoly.lean, Width.lean, Recursion.lean, QftPlan.lean,
ShorPlan.lean, Template.lean` are all mutually independent within this
folder (`Recursion.lean` additionally depends on `Table/Census.lean`, one
level up) `→ Bundle.lean`, which imports all six plus `Table/Census.lean`
and `Json/Common.lean`.

## `CoeffPoly.lean` — E2, interpolation-weight polynomials

The leaf weights solve `M · c = (1, b, b², …)ᵀ` with `M_{j,l} = interpEntry k
pts[l] j` and `b = 2^m`, so `c_l(b) = Σ_j (M⁻¹)_{j,l} b^j` is a polynomial in
`b` determined by `k` and the point list alone.

`M⁻¹` is computed by exact **Gauss-Jordan elimination over `ℚ`**
(`gaussJordanInverseRows`, `O(n³)`) — **not** Mathlib's
`Matrix.adjugate`/`Matrix.det`. Those are Leibniz-formula sums over
`Equiv.Perm`, meant for proofs, not computation: one adjugate entry is
already an `O(n!)` determinant, so a whole inverse that way is `O(n²·n!)` —
already impractical at `k = 5` (`q 5 = 9`; `81` entries × `9! = 362880`).

- `coeffMatrix (k) (pts) (hpts) : Matrix (Fin (q k)) (Fin (q k)) ℚ` —
  `interpMatrix k (ptsToFin k pts hpts)`.
- `matrixToRows`, `gaussJordanInverseRows (n) (rows) : Option (Array (Array
  ℚ))` — dense row-major exact elimination; `none` if singular (shouldn't
  happen — `GoodToomCookPoints` is what the compiler's own
  `cramerCoeffFromPtsWidth` already relies on).
- `coeffInverse (k) (pts) (hpts) : Option (Array (Array ℚ))` — `M⁻¹`,
  computed once.
- `coeffPolyRowOf (inv) (l) : Fin n → ℚ` — row `l`'s coefficient-of-`bʲ`
  vector, read off a precomputed `M⁻¹` (`coeffPolyRowOf inv l j = (M⁻¹) j l`).
- `polyEval (c) (b) : ℚ` — evaluate a coefficient vector at concrete `b`.
- `check1_inverseOf (M) (inv) : Bool` — `M · M⁻¹ = I` exactly, entrywise,
  `O(n³)` plain arithmetic (no `Matrix.det`).
- `check2_agreesWithCramer (inv) (k) (pts) (hpts) (mMax) : Bool` —
  cross-checks the polynomials, evaluated at `b = 2^m`, against the
  compiler's own `cramerCoeffFromPtsWidth` (the function `loweringPhaseCoeff`
  actually calls). Unlike everything else in this file, `cramerCoeffFromPtsWidth`
  is pre-existing and unmodifiable, and it **is** one of the expensive
  `Matrix.det`/`Matrix.cramer` calls — at `k = 5` it overflows the stack
  almost immediately (a recursion-depth limit in Mathlib's `Equiv.Perm`
  machinery, not merely slow). `Bundle.lean`'s `coeffPolyJson` is what
  actually gates this: unconditional for `k ≤ 3`, opt-in via
  `--check-cramer` for `k = 4`, always skipped from `k = 5`, capped at `m ≤
  6` even then.
- `pointsDistinct (pts) : Bool` — pairwise distinct by `ToomCookMath`'s
  coordinate (`int z ↦ z`, `frac c ↦ 1/c`).
- `degenerateMs (pts) (mMax) : List ℕ` — every `m ≤ mMax` where `2^m`
  coincides with one of the (integer) points — there the weight vector is a
  selector and any downstream differential is vacuous. Advisory only.

## `Width.lean` — E3, width tables

Over `m = 1..mMax` (uniform limbs, `w = k·m`) and over general `w =
k..wMax`: `RecursivePhaseWorkspace.nextWidth`, `.limbWidth`, `.reserveNeed`
— read directly off the compiler's own definitions, no recomputation.

- `widthTableByM {k} (ops) (mMax) : List (ℕ × ℕ × ℕ)` — `(m, nextWidth,
  limbWidth)` rows.
- `widthTableByW {k} (ops) (wMax) : List (ℕ × ℕ × ℕ × ℕ)` — `(w, nextWidth,
  reserve_x, reserve_z)` rows.
- `affineTail (widths : List (ℕ × ℕ)) : Option (ℕ × ℕ)` — least `(m₀, β)`
  such that `W(m) = m + β` for every `m ≥ m₀` in a contiguous `(m, W m)`
  table (equivalently `W(m+1) = W(m) + 1`), scanning backward from the last
  entry. Shared by `ShorPlan.lean` for its own per-column affine tails.

## `Recursion.lean` — E6, recursion skeleton

- `widthLadder {k} (ops) (w) : List ℕ` — `[W₀, W₁, …, W_d]`, `W₀ = w`,
  `W_{i+1} = nextWidth W_i` while it keeps shrinking, stopping at the
  leaf/base width. Mirrors `RecursivePhaseWorkspace.reserveNeed`'s own
  well-founded recursion (`termination_by w`).
- `RecursionLevel` — `{depth, width, leafMultiplicity, adderCost, baseCost}`.
- `recursionLevels {k} (ops) (w) : List RecursionLevel` — per-level cost
  breakdown along the ladder (`partial`, mirroring `widthLadder`'s
  recursion — this is output-only tooling with no proof obligations, like
  `LowGateJson.lean`'s `flattenSeq`/`lowGateJson`). `leafMultiplicity := q k
  ^ depth`; `adderCost` uses `OpCensus.adderClassTotal × (addScaledResourcesAt
  nextWidth).totalGates`; `baseCost` (leaf level only) from
  `naiveLeafResourcesAt` at the ladder's final width.
- `recursionTotalCost (levels) : ℕ` — summed under `shorGateCostModel`.
  Evaluated, not a theorem — the asymptotic statement it evaluates is
  `Shor.phaseProductGateCountBound_of_programOK` / `Shor.exists_shorGateCountBound`.

## `QftPlan.lean` — E4, QFT plan

- `qftPlanTable {k} (ops) (wMax) : List (ℕ × ℕ × ℕ × Angle × ℕ × ℕ × ℕ)` —
  for `w = 2..wMax`: `(w, leftWidth, rightWidth, qftPhi w,
  radixReverseCost, xWorkspaceNeed, zWorkspaceNeed)`. `left := w/2`, `right
  := w − w/2` matches both `QFT/Split.lean`'s `leftReg`/`rightReg` and
  `qftWorkspaceNeed`'s own local convention.

## `ShorPlan.lean` — E5, Shor register plan

For a ladder of modulus bit-lengths `n` and precision levels `m`, on
synthetic instances `N = 2^n − 1, a = 2` (`N` is always odd, so `gcd a N =
1` always holds; `a < N` holds for `n ≥ 2`).

- `ShorPlanPerM` — `{m, workWidth, scratchWidth, exponentReserve,
  dataReserve, auxiliaryReserve, scratchReserve}`.
- `ShorPlanRow` — `{n, xWidth, dataWidth, perM : List ShorPlanPerM}`.
- `shorPlanRow {k} (ops) (n) (mMax) : Option ShorPlanRow` — one row, `none`
  if the synthetic instance is invalid (defensive; can't happen for `n ≥
  2`). Uses `referenceXWidth`, `referenceDataWidth`, `referenceWorkWidth`
  (through `algorithm1ExtraBitsNat m`), `referenceScratchWidth`, and the
  four reserve sizes from `referenceWorkspaceNeed`.
- `shorPlanTable {k} (ops) (nMin nMax mMax) : List ShorPlanRow`.

The constant-arithmetic primitives `lowerCmpGeConst`/`lowerCSubConst` (steps
U3, U4 of `CmodMulInPlaceCore`) are **not** tabulated here — they're linear
in register width with no recursion and no table dependence, so their
per-width counts are meant to be read off concrete `shor` documents and
fitted outside Lean (`Bundle.lean`'s `provenanceJson` says so).

## `Template.lean` — E7, the symbolic templates

The IR proper: the ops with the width left as a variable. Possible because
the compiler's op *sequence* is fixed by the table — only slot widths,
allocation amounts, leaf angles, and the recurse-or-not decision vary with
the width, and each has an n-free rule. Printed **one level deep**: a
`PhaseProduct`/`CPhaseProduct` child is referenced by its interpolation-term
index (`"child": l`) and described by the `recursion` field's rule text, not
unrolled into a nested copy at `W' = nextWidth(W)` (unrolling to a chosen
depth, and the `x0.x1`-style nested slot naming that would need, is left for
whenever something actually consumes multiple levels).

- `WExpr` — a small typed width-expression language: `var`, `const`, `add`,
  `sub`, `mul`, `div`, `max`, and one opaque `nextWidth` (its values live in
  E3's table, not re-derived here). `WExpr.render : WExpr → String` prints
  it as a formula string (e.g. `"(W div 2)"`, `"nextWidth(W)"`) —
  fully parenthesized, not minimal-precedence.
- `SlotSide (.x | .z)`, `slotName (side) (i) : String` — a slot's symbolic
  name, `x0 … x{k-1}` / `z0 … z{k-1}` at this level. There is no existing
  nested-slot naming anywhere in the compiler to reuse (checked); this is
  `Emit/`'s own convention, for whenever multi-level unrolling lands.
- `limbWidthExpr`, `slotWidthExpr`, `nextWidthExpr`, `allocDeltaExpr` — the
  width formulas: `W div k` (limb), `if isTop then W - i*limbWidth else
  limbWidth` (per-slot, the top chunk absorbs the remainder), `nextWidth(W)`
  (opaque — every slot in `compileOpsToSignedGate` is grown to the *same*
  uniform target width, not a per-slot value), and `nextWidth(W) −
  slotWidth` (alloc/dealloc delta).
- `phaseProductTemplateJson {k} (ops) (isCtrl) : Json` — walks
  `annotatePhaseTermsAux k 0 ops` and replays `compileOpsToSignedGate`'s
  shape **exactly**, verified against the real source
  (`compileSignedAllocationsAux`/`compileAnnotatedOpsToSignedGateAux`/
  `compileSignedDeallocationsAux` in `Compiler/Compile.lean`): allocations
  in slot order interleaved by index (`x0, z0, x1, z1, …` — not grouped by
  side), each table op replayed on both the `x` and `z` operand (in that
  order), each `phaseProduct` with an assigned term as a
  `(C)PhaseProduct` leaf carrying `phi · c_l`, then deallocations in
  reverse (`z, x` per chunk, largest index first).
- `qftTemplateJson : Json` — one level: `left = w/2`, `right = w − w/2`,
  `qftPhi w` (opaque, printed as `"qftPhi(w)"`), radix-reverse cost `3·(w/2)`.
- `shorTemplateJson : Json` — fully symbolic in `a, N, m, n` (no concrete
  instance data — `bundle` takes none, and the document stays `n_free`):
  the `Gate` tree of `orderFindingApprox`/`modExpApproxValid`/
  `CmodMulInPlaceCore` with registers replaced by E5's named width formulas
  and each atomic leaf pointing at the phase-product/QFT templates *by
  name* (`"phase_product_ref": "template.phase_product"`, etc.), not
  inlined.

## `Bundle.lean` — assembly

Turns E1–E7 into JSON objects and assembles the `forshor.emit/v1` document;
also the home of the CLI-facing per-section and `phases` builders.

- `scheduleJson`, `coeffPolyJson`, `widthJson`, `recursionJson`,
  `qftPlanJson`, `shorPlanJson`, `templateSectionJson` — one JSON builder
  per E-section, each taking a `TableInstance`/`Prog k` plus whatever
  options that section needs (`mMax`, `wMax`, `checkCramer`).
- `provenanceJson (src) : Json` — per-section text naming the Lean
  declaration each section evaluates, and whether it's a theorem (`table`)
  or "evaluated, not proved" (`coeff_poly`, `width`, `recursion`,
  `qft_plan`, `shor_plan`, `template`).
- `buildBundle (src) (k) (hk) (mMax) (wMax) (checkCramer) : Except String
  Json` — the whole document. Refuses (via `checkTable`) only for
  `TableSource.generate`. `recursion` uses the ladder from `wMax`;
  `schedule.resources_at_width` is evaluated at `wMax`; `shor_plan` covers
  `n = 2 .. min wMax 16`.
- `sectionNames : List String` — the seven names `buildSection` understands
  (every field of `buildBundle`'s document except the envelope fields).
- `buildSection (sectionName) (src) (k) (hk) (mMax) (wMax) (checkCramer) :
  Except String Json` — one named section, same envelope and same blocking
  check as `buildBundle`, so a section can never drift from what `bundle`
  itself would print for the same options — there is exactly one builder
  per section either way.
- `buildPhases (k) (m) (phiNum) (phiDen) : Except String (List String)` —
  `forshor_emit phases`: exactly `q k` lines, each row `l`'s E2 coefficient
  polynomial evaluated at chunk width `m` and scaled by `phi`, printed as a
  reduced `num/den` string. Always the standard table.
