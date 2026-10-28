# `Symbolic/`

The opaque value tables: `CoeffPoly.lean`,
`Width.lean`, `QftPlan.lean`, `ShorPlan.lean` — the values of the few
functions the extracted templates (`Reflect/`, `IR/`) call by name but
never evaluate symbolically — plus `Bundle.lean`, which assembles them (and
the extracted `template`, via `Reflect/Verify.lean`) into the `forshor.
emit/v1` document and exposes the CLI-facing builders (`buildBundle`,
`buildSection`, `buildTemplateDoc`, `buildPhases`). `Dispatcher.lean` is
the one template in a policy document that is built rather than extracted:
the width dispatcher, with the theorem that it routes as the policy does.

Import order: `CoeffPoly.lean`, `Width.lean`, `QftPlan.lean`, `ShorPlan.lean`
are mutually independent within this folder → `Bundle.lean`, which imports
all four plus `Json/Common.lean`, `IR/Json.lean`, `Table/Source.lean` and
`Reflect/Verify.lean`. `Dispatcher.lean` imports only `IR/Syntax.lean` and
`Framework/Policy.lean`; it is used by `Reflect/PolicyTargets.lean`,
`Reflect/PolicyVerify.lean` and `Reflect/Driver.lean`, not by `Bundle.lean`.

## `CoeffPoly.lean` — interpolation-weight polynomials

The leaf weights solve `M · c = (1, b, b², …)ᵀ` with `M_{j,l} = interpEntry k
pts[l] j` and `b = 2^m`, so `c_l(b) = Σ_j (M⁻¹)_{j,l} b^j` is a polynomial in
`b` determined by `k` and the point list alone.

`M⁻¹` is computed by exact **Gauss-Jordan elimination over `ℚ`**
(`gaussJordanInverseRows`, `O(n³)`, defined in
`Implementation/PhaseProduct/Compiler/GaussJordan.lean` since the compiler
uses it too) — **not** Mathlib's
`Matrix.adjugate`/`Matrix.det`. Those are Leibniz-formula sums over
`Equiv.Perm`, meant for proofs, not computation: one adjugate entry is
already an `O(n!)` determinant, so a whole inverse that way is `O(n²·n!)` —
already impractical at `k = 5` (`q 5 = 9`; `81` entries × `9! = 362880`).

- `coeffMatrix (k) (pts) (hpts) : Matrix (Fin (q k)) (Fin (q k)) ℚ` —
  `interpMatrix k (ptsToFin k pts hpts)`.
- `matrixToRows`, `gaussJordanInverseRows (n) (rows) : Option (Array (Array
  ℚ))` — dense row-major exact elimination; `none` if singular (shouldn't
  happen — `GoodToomCookPoints` is what the compiler's own
  `cramerCoeffFromPtsWidth` already relies on). Both are re-exported from
  `Compiler/GaussJordan.lean`, where `isRightInverseRows` and the lemma
  `mul_rowsToMatrix_eq_one_of_isRightInverseRows` turn the re-multiplication
  check into the `Matrix` equation the compiler's `@[csimp]` proof needs.
- `coeffInverse (k) (pts) (hpts) : Option (Array (Array ℚ))` — `M⁻¹`,
  computed once.
- `coeffPolyRowOf (inv) (l) : Fin n → ℚ` — row `l`'s coefficient-of-`bʲ`
  vector, read off a precomputed `M⁻¹` (`coeffPolyRowOf inv l j = (M⁻¹) j l`).
- `polyEval (c) (b) : ℚ` — evaluate a coefficient vector at concrete `b`.
- `check1_inverseOf (M) (inv) : Bool` — `M · M⁻¹ = I` exactly, entrywise,
  `O(n³)` plain arithmetic (no `Matrix.det`); an `abbrev` for the compiler's
  `isRightInverseRows`.
- `check2_agreesWithCramer (inv) (k) (pts) (hpts) (mMax) : Bool` —
  cross-checks the polynomials, evaluated at `b = 2^m`, against the
  compiler's own `cramerCoeffFromPtsWidth` (the function `loweringPhaseCoeff`
  actually calls). That function is now `@[csimp]`-compiled through the same
  eliminator (`Compiler/Coefficients.lean`, `gjCoeffFromPts`), so both sides
  are cubic; `Bundle.lean`'s `coeffPolyJson` runs the check unconditionally
  at every `k`, capped at `m ≤ 6`. What it still verifies is that the
  *polynomial* read off `M⁻¹` (`coeffPolyRowOf`/`polyEval`) matches the
  compiler's *pointwise* weights.
- `pointsDistinct (pts) : Bool` — pairwise distinct by `ToomCookMath`'s
  coordinate (`int z ↦ z`, `frac c ↦ 1/c`).
- `degenerateMs (pts) (mMax) : List ℕ` — every `m ≤ mMax` where `2^m`
  coincides with one of the (integer) points — there the weight vector is a
  selector and any downstream differential is vacuous. Advisory only.

## `Width.lean` — width table

`RecursivePhaseWorkspace.nextWidth`/`.reserveNeed` — read directly off the
compiler's own definitions, no recomputation — over `w = 1..wMax`.

- `widthTable {k} (ops) (wMax) : List (ℕ × ℕ × ℕ × ℕ)` — `(w, nextWidth,
  reserve_x, reserve_z)` rows. The **diagonal** only: `nextWidth w w`.
- `splitWidthTable {k} (ops) (wMax) : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)` —
  `(w, xw, zw, nextWidth, reserve_x, reserve_z)` at the **unequal** pair
  `(w / 2, w - w / 2)`. The diagonal suffices for `phase_product`, whose
  recursion grows both children to `nextWidth` and so stays symmetric
  forever after; it does not suffice for `qft`, which splits its register at
  `regSize r / 2` and hands `phase_product` an unequal pair at
  every odd width. Without these rows a consumer holding only the bundle
  cannot instantiate `qft` at an odd width at all — `Emit/Tests.lean`'s
  `TableOracle` section is the check that, with them, it can.
- `tableOpaqueW (wrows) (srows) (qrows) : String → List ℕ → Option ℕ` — the
  `IR.Env.opaqueW` oracle built from the published rows **by lookup**, with
  no call into `nextWidth`/`reserveNeed`/`qftWorkspaceNeed`. This is the
  consumer's side of the contract, written down in Lean so it can be run:
  anything it cannot resolve is a `none`, which `instantiate` reports as an
  error rather than papering over. `modpow`/`step5Const` are deliberately
  absent — they are `shor`'s, modulus-dependent rather than table-dependent,
  and a consumer implements them directly.

`nextWidth`/`reserveNeed` are the only opaque values the extracted
template calls by name from this table.

## `QftPlan.lean` — QFT workspace table

- `qftPlanTable {k} (ops) (wMax) : List (ℕ × ℕ × ℕ)` — for `w = 1..wMax`:
  `(w, xWorkspaceNeed, zWorkspaceNeed)`. `qftWorkspaceNeed` is the only
  opaque value the extracted `qft` template calls by name — `left`/`right`
  split widths, `qftPhi`, and the radix-reverse cost are printed directly by
  the template itself.

## `ShorPlan.lean` — Shor register plan

For a ladder of modulus bit-lengths `n` and precision levels `m`, on
synthetic instances `N = 2^n − 1, a = 2` (`N` is always odd, so `gcd a N =
1` always holds; `a < N` holds for `n ≥ 2`).

- `ShorPlanPerM` — `{m, workWidth, scratchWidth, exponentReserve,
  dataReserve, auxiliaryReserve, scratchReserve}`.
- `ShorPlanRow` — `{n, xWidth, dataWidth, perM : List ShorPlanPerM}`.
- `shorPlanRow (pol : ShorLoweringPolicy) (n) (mMax) : Option ShorPlanRow` — one row, `none`
  if the synthetic instance is invalid (defensive; can't happen for `n ≥
  2`). Uses `referenceXWidth`, `referenceDataWidth`, `referenceWorkWidth`
  (through `algorithm1ExtraBitsNat m`), `referenceScratchWidth`, and the
  four reserve sizes from `referenceWorkspaceNeed`.
- `shorPlanTable (pol) (nMin nMax mMax) : List ShorPlanRow` — widths and
  reserves only.

The constant-arithmetic primitives `lowerCmpGeConst`/`lowerCSubConst` (steps
U3, U4 of `CmodMulInPlaceCore`) are **not** tabulated here — they're linear
in register width with no recursion and no table dependence, so their
per-width counts are meant to be read off concrete `shor` documents and
fitted outside Lean (`Bundle.lean`'s `provenanceJson` says so).

## `Dispatcher.lean` — the policy width dispatcher

Every other template in a `Doc` is extracted from a Lean term. A policy's
choice of table at a width is `ShorLoweringPolicy.choose`, a `List.find?`
over the bands — data, not a circuit — so its template is built directly: a
chain of `Node.cond` guards `t_i ≤ max xw zw`, in band order, each calling
`phase_product_<i>` and falling through to `naive_leaf`. No `MetaM`, no
`Expr`, no trust in the translation table.

- `dispatcherName`, `dispatcherLeafName`, `bandBodyName (controlled) (i)` —
  the template names: `phase_product`/`cphase_product` for the dispatcher
  itself, `naive_leaf`/`naive_cleaf` for the fallthrough,
  `phase_product_<i>`/`cphase_product_<i>` for band `i`'s body.
- `dispatcherChain (controlled) (i) (bands) : Node` — the guard chain,
  structurally recursive on the bands so the proof below is a list
  induction.
- `dispatcherTemplate (P) (controlled) : Template` — the dispatcher for `P`,
  with exactly the parameter lists `extractPhaseProductBody` gives the
  single-table `phase_product`, so `qft`, `shor` and the band bodies call it
  by that name with no edit.
- `dispatcherCallAt (node) (xw zw) : Option String` — walks an emitted chain
  at concrete widths and names the template it lands on; an oracle for
  `dispatcherChain`'s own node shapes, not a general evaluator.
- `chooseIdx (P) (n)` and `chooseIdx_map` — `choose` with the chosen band's
  index attached, and the proof that it picks the table `choose` picks.
- **`dispatcherCallAt_dispatcherTemplate`** — the one proved result in
  `Emit/`: the dispatcher calls band `j`'s body exactly where `chooseIdx`
  picks band `j`, and the leaf exactly where the policy offers no table.
  With `chooseIdx_map`, the emitted guards and `ShorLoweringPolicy.choose`
  cannot drift apart; what the evaluation tier samples is only whether each
  band's body matches the circuit.
- `shiftCoeffA (d)`, `shiftCoeffN (d)` — shift every `coeff` point index in
  an angle expression / template body by `d`. `Reflect/Driver.lean`'s
  `policyBandBodies` uses them to reuse one band's body for a later band
  with the same table; `Reflect/PolicyVerify.lean`'s `bandCopyOK` checks a
  reused body is exactly that shifted copy.

## `Bundle.lean` — assembly

Turns the value tables above (plus the extracted `template`) into JSON
objects and assembles the `forshor.emit/v1` document; also the home of the
CLI-facing per-section, `template`, and `phases` builders.

- `scheduleJson`, `coeffPolyJson`, `widthJson`, `splitWidthJson`,
  `qftPlanJson`, `shorPlanJson` — one JSON builder per pure section, each taking a `TableInstance`/
  `Prog k` plus whatever options that section needs (`mMax`, `wMax`,
  `checkCramer`). `scheduleJson` holds `ops`/`points` only; per-op resource
  counts fall out of the extracted `Doc` plus the repository's own
  `shorGateResourceModel`.
- `provenanceJson : Json` — per-section text naming the Lean
  declaration each section evaluates, and whether it's a theorem (`table`)
  or "evaluated, not proved" (`coeff_poly`, `width`, `qft_plan`,
  `shor_plan`); `templateProvenance` is the `template` section's trust
  statement verbatim (extracted by reflection; trusted: translation table
  and Lean normalisation; checked: instantiate = real term at the listed
  widths; not a theorem).
- `buildBundleCore (k) (hk) (mMax) (wMax) (checkCramer) : Except
  String Json` — the pure sections only (no `template` — that needs `IO`,
  see below). `native_decide`-testable; `Tests.lean` uses this, not
  `buildBundle`, for its compile-time bundle checks.
- `buildTemplateDoc (k) (hk) (wMax) : IO (Except String Json)` — extracts
  the `Doc` (`Reflect.runExtractAndVerify`, which also runs
  `Reflect.Verify`'s instance-check canary), refusing if `wMax` doesn't
  cover the canary's own checked width (`templateCheckWidth k hk`, the
  maximum of the table's own derived width ladders). Backs
  `forshor_emit template <k>`.
- `buildBundle (k) (hk) (mMax) (wMax) (checkCramer) (noTemplate) : IO
  (Except String Json)` — `buildBundleCore` plus `buildTemplateDoc`'s
  result under `"template"`, unless `noTemplate` (`--no-template`, which
  skips the environment load entirely).
- `sectionNames : List String` — the six pure section names `buildSection`
  understands (`template` is a dedicated command, not a `buildSection`
  case, since it needs `IO`).
- `buildSection (sectionName) (k) (hk) (mMax) (wMax) (checkCramer) :
  Except String Json` — one named pure section, same envelope as
  `buildBundleCore`.
- `buildPhases (k) (m) (phiNum) (phiDen) : Except String (List String)` —
  `forshor_emit phases`: exactly `q k` lines, each row `l`'s coefficient
  polynomial evaluated at chunk width `m` and scaled by `phi`, printed as a
  reduced `num/den` string. Always the standard table.
