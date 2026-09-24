# `Symbolic/`

The D4-opaque value tables (R3): `CoeffPoly.lean`,
`Width.lean`, `QftPlan.lean`, `ShorPlan.lean` — the values of the few
functions the extracted templates (`Reflect/`, `IR/`) call by name but
never evaluate symbolically — plus `Bundle.lean`, which assembles them (and
the extracted `template`, via `Reflect/Verify.lean`) into the `forshor.
emit/v1` document and exposes the CLI-facing builders (`buildBundle`,
`buildSection`, `buildTemplateDoc`, `buildPhases`).

`Symbolic/Template.lean` (the old hand-transcribed E7 template) and
`Symbolic/Recursion.lean` (the old E6 recursion-cost ladder) were deleted in
R3/R4: the extracted `Doc` (`Reflect/`, `IR/`) replaced the former, and a
consumer deriving cost from the `width` table plus the repository's own
`shorGateResourceModel` replaced the latter — see the top-level `README.md`.

Import order: `CoeffPoly.lean`, `Width.lean`, `QftPlan.lean`, `ShorPlan.lean`
are mutually independent within this folder → `Bundle.lean`, which imports
all four plus `Json/Common.lean`, `IR/Json.lean`, and `Reflect/Verify.lean`.

## `CoeffPoly.lean` — interpolation-weight polynomials

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

## `Width.lean` — width table

`RecursivePhaseWorkspace.nextWidth`/`.reserveNeed` — read directly off the
compiler's own definitions, no recomputation — over `w = 1..wMax`.

- `widthTable {k} (ops) (wMax) : List (ℕ × ℕ × ℕ × ℕ)` — `(w, nextWidth,
  reserve_x, reserve_z)` rows.

(The old `widthTableByM`/`limbWidth` column and the `affineTail` advisory
helper were dropped in R3/R4 — `nextWidth`/`reserveNeed` are the only D4
values the extracted template actually calls by name.)

## `QftPlan.lean` — QFT workspace table

- `qftPlanTable {k} (ops) (wMax) : List (ℕ × ℕ × ℕ)` — for `w = 1..wMax`:
  `(w, xWorkspaceNeed, zWorkspaceNeed)`. `qftWorkspaceNeed` is the only D4
  value the extracted `qft` template calls by name — `left`/`right` split
  widths, `qftPhi`, and the radix-reverse cost are printed directly by the
  template itself now (R3/R4 dropped the old split-width columns).

## `ShorPlan.lean` — Shor register plan

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

(The old per-column `affineTail` advisory field was dropped in R3/R4 —
widths and reserves only.)

The constant-arithmetic primitives `lowerCmpGeConst`/`lowerCSubConst` (steps
U3, U4 of `CmodMulInPlaceCore`) are **not** tabulated here — they're linear
in register width with no recursion and no table dependence, so their
per-width counts are meant to be read off concrete `shor` documents and
fitted outside Lean (`Bundle.lean`'s `provenanceJson` says so).

## `Bundle.lean` — assembly

Turns the value tables above (plus the extracted `template`) into JSON
objects and assembles the `forshor.emit/v1` document; also the home of the
CLI-facing per-section, `template`, and `phases` builders.

- `scheduleJson`, `coeffPolyJson`, `widthJson`, `qftPlanJson`, `shorPlanJson`
  — one JSON builder per pure section, each taking a `TableInstance`/
  `Prog k` plus whatever options that section needs (`mMax`, `wMax`,
  `checkCramer`). `scheduleJson` keeps only `ops`/`points` (the old op
  census/per-width `LowGate` resource counts were dropped along with
  `Table/Census.lean` — they fall out of the extracted `Doc` plus the
  repository's own `shorGateResourceModel`).
- `provenanceJson : Json` — per-section text naming the Lean
  declaration each section evaluates, and whether it's a theorem (`table`)
  or "evaluated, not proved" (`coeff_poly`, `width`, `qft_plan`,
  `shor_plan`); `templateProvenance` is D7's trust statement verbatim.
- `buildBundleCore (k) (hk) (mMax) (wMax) (checkCramer) : Except
  String Json` — the pure sections only (no `template` — that needs `IO`,
  see below). `native_decide`-testable; `Tests.lean` uses this, not
  `buildBundle`, for its compile-time bundle checks.
- `buildTemplateDoc (k) (hk) (wMax) : IO (Except String Json)` — extracts
  the `Doc` (`Reflect.runExtractAndVerify`, which also runs
  `Reflect.Verify`'s instance-check canary), refusing if `wMax` doesn't
  cover the canary's own checked width (`templateCheckWidth k = 4 * k`).
  Backs `forshor_emit template <k>`. The old `src = .generate` refusal, and
  the `src` parameter that carried it, went with `TableSource`
  (`SUBMISSION_PLAN.md` S1.6).
- `buildBundle (k) (hk) (mMax) (wMax) (checkCramer) (noTemplate) : IO
  (Except String Json)` — `buildBundleCore` plus `buildTemplateDoc`'s
  result under `"template"`, unless `noTemplate` (`--no-template`, which
  skips the environment load entirely).
- `sectionNames : List String` — the five pure section names `buildSection`
  understands (`template` is a dedicated command, not a `buildSection`
  case, since it needs `IO`).
- `buildSection (sectionName) (k) (hk) (mMax) (wMax) (checkCramer) :
  Except String Json` — one named pure section, same envelope as
  `buildBundleCore`.
- `buildPhases (k) (m) (phiNum) (phiDen) : Except String (List String)` —
  `forshor_emit phases`: exactly `q k` lines, each row `l`'s coefficient
  polynomial evaluated at chunk width `m` and scaled by `phi`, printed as a
  reduced `num/den` string. Always the standard table.
