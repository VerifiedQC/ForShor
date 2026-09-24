import FastMultiplication.Emit.Json.Common
import FastMultiplication.Emit.Symbolic.CoeffPoly
import FastMultiplication.Emit.Symbolic.Width
import FastMultiplication.Emit.Symbolic.QftPlan
import FastMultiplication.Emit.Symbolic.ShorPlan
import FastMultiplication.Emit.IR.Json
import FastMultiplication.Emit.Reflect.Verify

/-!
# The `forshor.emit/v1` bundle

Assembles E2 (`Symbolic/CoeffPoly.lean`), E3 (`Symbolic/Width.lean`), E4
(`Symbolic/QftPlan.lean`), E5 (`Symbolic/ShorPlan.lean`) — the D4-opaque
value tables — and E7 (the extracted `Doc`, `Reflect/Verify.lean`) into one
document, `n`-free: every quantity depends on `k`, never on a modulus
bit-length `n` (except `shor_plan`'s own explicit `n`-ladder, which is the
whole point of that section). `k` enters everywhere; `n` never does outside
`shor_plan`.

R3 (`Emit/PLAN.md` §7) split this file's old single pure `buildBundle` in
two: `buildBundleCore` (schedule/coeff_poly/width/qft_plan/shor_plan — pure,
`native_decide`-testable, no reflection) and `buildBundle`/`buildTemplateDoc`
(`unsafe`, `IO`, since embedding the extracted `Doc` needs
`Reflect.runExtract`'s environment reload). `--no-template` skips the load
entirely; `buildTemplateDoc` is also what backs the standalone `template`
CLI command.
-/

namespace Shor

open Lean (Json)

/-- `bundle` CLI options. -/
structure BundleOpts where
  mMax : ℕ
  wMax : ℕ
  checkCramer : Bool

def optsJson (o : BundleOpts) : Json :=
  Json.mkObj [
    ("m_max", (o.mMax : Json)),
    ("w_max", (o.wMax : Json)),
    ("check_cramer", Json.bool o.checkCramer)
  ]

/-- E1: the schedule (`ops`, `points` only — census/per-width `LowGate`
resource counts are not D4-opaque, so R3 dropped them: they fall out of the
extracted `Doc` plus the repository's own `shorGateResourceModel`, not out
of a separate table here). -/
def scheduleJson {k : ℕ} (inst : TableInstance k) : Json :=
  Json.mkObj [
    ("ops", progJson inst.ops),
    ("points", Json.arr (inst.points.map pointJson).toArray)
  ]

/-- E2: interpolation-weight polynomials. `M⁻¹` is computed once via
Gauss-Jordan (`coeffInverse`, `O(n³)`) — fast for any `k` this repository's
tables reach, unlike calling Mathlib's `Matrix.adjugate` per entry. Only
`check2` (cross-checking against the pre-existing, unmodifiable
`cramerCoeffFromPtsWidth`) is gated, and more tightly than the README's own
`k ≤ 5` text: at `k = 5` (`q k = 9`), evaluating `Matrix.det`'s generic
`Equiv.Perm`-sum construction there crashes with a stack overflow almost
immediately (this is a recursion-depth limit of Mathlib's proof-oriented
`Fintype`/`Equiv.Perm (Fin 9)` machinery, not merely slow — confirmed even
with `ulimit -s` raised well past its default). So `check2` runs
unconditionally for `k ≤ 3`, opt-in via `--check-cramer` up to `k ≤ 4`, and
is always skipped from `k = 5` up — capped at `m ≤ 6` even then, so an
explicit `--check-cramer --m-max` request can't blow up the check past what's
actually tractable. -/
def coeffPolyJson {k : ℕ} (inst : TableInstance k) (checkCramer : Bool) (mMaxCheck : ℕ) : Json :=
  match coeffInverse k inst.points inst.hlen with
  | none =>
      Json.mkObj [
        ("error", Json.str "singular interpolation matrix (unexpected: GoodToomCookPoints failed)")
      ]
  | some inv =>
      let doCheck2 := k ≤ 3 ∨ (checkCramer ∧ k ≤ 4)
      let mCheck := min mMaxCheck 6
      let rows :=
        (List.finRange (q k)).map fun (l : Fin (q k)) =>
          Json.mkObj [
            ("l", ((l : ℕ) : Json)),
            ("coeffs",
              Json.arr
                (((List.finRange (q k)).map
                  (fun (j : Fin (q k)) => ratJson (coeffPolyRowOf inv l j))).toArray))
          ]
      Json.mkObj [
        ("points_distinct", Json.bool (pointsDistinct inst.points)),
        ("degenerate_m",
          Json.arr ((degenerateMs inst.points mMaxCheck).map (fun m => (m : Json))).toArray),
        ("check1_inverse", Json.bool (check1_inverseOf (coeffMatrix k inst.points inst.hlen) inv)),
        ("check2",
          if doCheck2 then
            Json.mkObj [
              ("checked", Json.bool true),
              ("m_max_checked", (mCheck : Json)),
              ("agrees_with_cramer",
                Json.bool (check2_agreesWithCramer inv k inst.points inst.hlen mCheck))
            ]
          else
            Json.mkObj [
              ("checked", Json.bool false),
              ("reason", Json.str "k > 3 without --check-cramer, or k ≥ 5 regardless")
            ]),
        ("rows", Json.arr rows.toArray)
      ]

/-- E3: the width table (`nextWidth`, `reserveNeed_x/z`, D4-opaque). -/
def widthJson {k : ℕ} (ops : Prog k) (wMax : ℕ) : Json :=
  Json.mkObj [
    ("rows",
      Json.arr ((widthTable ops wMax).map (fun row =>
        Json.mkObj [
          ("w", (row.1 : Json)), ("next_width", (row.2.1 : Json)),
          ("reserve_x", (row.2.2.1 : Json)), ("reserve_z", (row.2.2.2 : Json))
        ])).toArray)
  ]

/-- E4: the QFT workspace table (`qftWorkspaceNeed`, D4-opaque). -/
def qftPlanJson {k : ℕ} (ops : Prog k) (wMax : ℕ) : Json :=
  Json.mkObj [
    ("rows",
      Json.arr ((qftPlanTable ops wMax).map (fun row =>
        Json.mkObj [
          ("w", (row.1 : Json)),
          ("x_workspace_need", (row.2.1 : Json)),
          ("z_workspace_need", (row.2.2 : Json))
        ])).toArray)
  ]

def shorPlanPerMJson (r : ShorPlanPerM) : Json :=
  Json.mkObj [
    ("m", (r.m : Json)),
    ("work_width", (r.workWidth : Json)),
    ("scratch_width", (r.scratchWidth : Json)),
    ("exponent_reserve", (r.exponentReserve : Json)),
    ("data_reserve", (r.dataReserve : Json)),
    ("auxiliary_reserve", (r.auxiliaryReserve : Json)),
    ("scratch_reserve", (r.scratchReserve : Json))
  ]

def shorPlanRowJson (row : ShorPlanRow) : Json :=
  Json.mkObj [
    ("n", (row.n : Json)),
    ("x_width", (row.xWidth : Json)),
    ("data_width", (row.dataWidth : Json)),
    ("per_m", Json.arr (row.perM.map shorPlanPerMJson).toArray)
  ]

/-- E5: the Shor register plan (widths and reserves only — no affine tail;
`Emit/PLAN.md` R4). -/
def shorPlanJson {k : ℕ} (ops : Prog k) (nMin nMax mMax : ℕ) : Json :=
  Json.mkObj [
    ("rows", Json.arr ((shorPlanTable ops nMin nMax mMax).map shorPlanRowJson).toArray)
  ]

/-- The extracted-`Doc` provenance string (`Emit/PLAN.md` §7, D7's trust
statement, verbatim). -/
def templateProvenance : String :=
  "extracted by reflection from the named constants; trusted: translation " ++
  "table and Lean normalisation; checked: instantiate = real term at the " ++
  "listed widths; not a theorem."

/-- Per-section provenance: which Lean declaration each section evaluates,
and whether that declaration is a theorem (see README "What is and is not a
theorem"). -/
def provenanceJson : Json :=
  Json.mkObj [
    ("table", Json.str
      ("Shor.standardLoweringSetup: length/GoodToomCookPoints/ProgConsumesPtsSafe/" ++
      "returns-to-start are theorems (generatedInterpolationPoints_length, " ++
      "genInterpolationPoints_good, genOpsWithProduct_ProgConsumesPtsSafe, " ++
      "genOpsWithProduct_returns_to_original)")),
    ("coeff_poly", Json.str
      ("M⁻¹ computed exactly by Gauss-Jordan elimination over ℚ (gaussJordanInverseRows); " ++
      "agreement with cramerCoeffFromPtsWidth is a run-time check over the checked m range " ++
      "(gated: unconditional k ≤ 3, --check-cramer up to k ≤ 4, skipped from k = 5), and " ++
      "cramerCoeffFromPtsWidth = phaseCoeffFromPtsWidth is the theorem " ++
      "cramerCoeffFromPtsWidth_eq_phaseCoeffFromPtsWidth")),
    ("width", Json.str
      "RecursivePhaseWorkspace.nextWidth/reserveNeed evaluated directly (D4: opaque)"),
    ("qft_plan", Json.str "qftWorkspaceNeed evaluated directly (D4: opaque)"),
    ("shor_plan", Json.str
      ("referenceXWidth/referenceDataWidth/referenceWorkWidth/referenceScratchWidth/" ++
      "referenceWorkspaceNeed evaluated on synthetic instances N = 2^n - 1, a = 2. The " ++
      "constant-arithmetic primitives lowerCmpGeConst/lowerCSubConst (steps U3, U4 of " ++
      "CmodMulInPlaceCore) are linear in register width with no recursion and no table " ++
      "dependence, so they are not tabulated here: their per-width counts are meant to be read " ++
      "off concrete `shor` documents at small N and fitted outside Lean")),
    ("template", Json.str templateProvenance)
  ]

/-- The pure sections of the bundle document (E2-E5): everything but
`template`, which needs `IO` (see `buildBundle`/`buildTemplateDoc`). Kept
separate so this stays `native_decide`-testable (`Tests.lean`). -/
def buildBundleCore (k : ℕ) (hk : 1 < k) (mMax wMax : ℕ) (checkCramer : Bool) :
    Except String Json :=
  let inst := standardTableInstance k hk
  let nMin := 2
  let nMax := min wMax 16
  .ok (Json.mkObj [
    ("schema", Json.str "forshor.emit/v1"),
    ("k", (k : Json)),
    ("table", Json.str "standard"),
    ("n_free", Json.bool true),
    ("opts", optsJson { mMax := mMax, wMax := wMax, checkCramer := checkCramer }),
    ("schedule", scheduleJson inst),
    ("coeff_poly", coeffPolyJson inst checkCramer mMax),
    ("width", widthJson inst.ops wMax),
    ("qft_plan", qftPlanJson inst.ops wMax),
    ("shor_plan", shorPlanJson inst.ops nMin nMax mMax),
    ("provenance", provenanceJson)
  ])

/-- The section names `buildSection` understands (the pure sections only —
`template` is a dedicated command, see `Main.lean`). -/
def sectionNames : List String := ["schedule", "coeff_poly", "width", "qft_plan", "shor_plan"]

/-- Build a single named pure section of the bundle document, in the same
envelope (`schema, k, table, n_free, opts, provenance`) but with only that
one section's data under its own name. -/
def buildSection (sectionName : String) (k : ℕ) (hk : 1 < k) (mMax wMax : ℕ)
    (checkCramer : Bool) : Except String Json :=
  let inst := standardTableInstance k hk
  let nMin := 2
  let nMax := min wMax 16
  let sectionJson? : Except String Json :=
    match sectionName with
    | "schedule" => .ok (scheduleJson inst)
    | "coeff_poly" => .ok (coeffPolyJson inst checkCramer mMax)
    | "width" => .ok (widthJson inst.ops wMax)
    | "qft_plan" => .ok (qftPlanJson inst.ops wMax)
    | "shor_plan" => .ok (shorPlanJson inst.ops nMin nMax mMax)
    | other => .error s!"unknown section: {other} (expected one of {sectionNames})"
  match sectionJson? with
  | .error e => .error e
  | .ok sj =>
      .ok (Json.mkObj [
        ("schema", Json.str "forshor.emit/v1"),
        ("k", (k : Json)),
        ("table", Json.str "standard"),
        ("n_free", Json.bool true),
        ("section", Json.str sectionName),
        ("opts", optsJson { mMax := mMax, wMax := wMax, checkCramer := checkCramer }),
        (sectionName, sj),
        ("provenance", provenanceJson)
      ])

/-- The largest width `Reflect.Verify`'s canary checks exercise for a given
`k` (`4 * k`, `phase_product`/`cphase_product`/`qft`'s own representative
width — see `Reflect/Verify.lean`). `--w-max` must cover at least this much
of the width table, or the value tables published alongside `template`
would have a gap right where the check itself looked. -/
def templateCheckWidth (k : ℕ) : ℕ := 4 * k

/-- Build the standalone `template` document (`Emit/PLAN.md` §7, §11/R5):
extract the `Doc` by reflection, verify it (`Reflect.Verify.verifyDoc`), and
print it together with the checks that passed and this section's
provenance. Refuses (`.error`) if extraction/verification fails or if `wMax`
doesn't cover the verifier's own checked width. `SUBMISSION_PLAN.md` S1.6
retired `TableSource`, so the old third refusal — `src = .generate`, a table
with no `ShorLoweringSetup` and therefore nothing the lowering theorems
cover — has no input left to reject. -/
unsafe def buildTemplateDoc (k : ℕ) (_hk : 1 < k) (wMax : ℕ) :
    IO (Except String Json) := do
  if wMax < templateCheckWidth k then
    let msg :=
      s!"--w-max {wMax} is below the largest width template's own instance checks use " ++
        s!"({templateCheckWidth k}); raise --w-max"
    return .error msg
  match ← Reflect.runExtractAndVerify k with
  | .error e => return .error e
  | .ok doc =>
      return .ok (Json.mkObj [
        ("schema", Json.str "forshor.ir/v1"),
        ("k", (k : Json)),
        ("table", Json.str "standard"),
        ("entry", Json.str doc.entry),
        ("opaque", Json.arr (doc.opaqueFns.map (fun (name, arity) =>
          Json.mkObj [("name", Json.str name), ("arity", (arity : Json))])).toArray),
        ("templates", Json.arr (doc.templates.map IR.templateJson).toArray),
        ("checks", Json.mkObj [
          ("wellformed", Json.bool true), ("instantiate_eq_real", Json.bool true)
        ]),
        ("provenance", Json.str templateProvenance)
      ])

/-- Build the full `forshor.emit/v1` bundle: the pure sections
(`buildBundleCore`) plus the extracted `template`, unless `noTemplate` is
set (`--no-template`, which skips the environment load entirely). -/
unsafe def buildBundle
    (k : ℕ) (hk : 1 < k) (mMax wMax : ℕ) (checkCramer noTemplate : Bool) :
    IO (Except String Json) := do
  match buildBundleCore k hk mMax wMax checkCramer with
  | .error e => return .error e
  | .ok coreJson =>
      if noTemplate then
        return .ok coreJson
      else
        match ← buildTemplateDoc k hk wMax with
        | .error e => return .error e
        | .ok templateJ => return .ok (coreJson.setObjVal! "template" templateJ)

/-- `forshor_emit phases <k> <m> <phiNum/phiDen>`: exactly `q k` lines, each
`c_l(2^m) · phi` as a reduced `num/den` (row `l`'s E2 coefficient polynomial,
evaluated at the chunk width `m` and scaled by `phi`). Always the standard
table (the `bundle` default). -/
def buildPhases (k m : ℕ) (phiNum phiDen : ℤ) : Except String (List String) :=
  if hk : 1 < k then
    let inst := standardTableInstance k hk
    match coeffInverse k inst.points inst.hlen with
    | none => .error "singular interpolation matrix (unexpected: GoodToomCookPoints failed)"
    | some inv =>
        let phi : Angle := (phiNum : ℚ) / (phiDen : ℚ)
        .ok
          ((List.finRange (q k)).map fun l =>
            let v := polyEval (coeffPolyRowOf inv l) ((2 : ℚ) ^ m) * phi
            s!"{v.num}/{v.den}")
  else
    .error s!"need k > 1 (k={k})"

end Shor
