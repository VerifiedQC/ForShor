import FastMultiplication.Emit.Json.Common
import FastMultiplication.Emit.Table.Census
import FastMultiplication.Emit.Symbolic.CoeffPoly
import FastMultiplication.Emit.Symbolic.Width
import FastMultiplication.Emit.Symbolic.Recursion
import FastMultiplication.Emit.Symbolic.QftPlan
import FastMultiplication.Emit.Symbolic.ShorPlan
import FastMultiplication.Emit.Symbolic.Template

/-!
# The `forshor.emit/v1` bundle

Assembles E1 (`Table/Census.lean`), E2 (`Symbolic/CoeffPoly.lean`), E3
(`Symbolic/Width.lean`), E4 (`Symbolic/QftPlan.lean`), E5
(`Symbolic/ShorPlan.lean`), E6 (`Symbolic/Recursion.lean`) into one document,
`n`-free: every quantity depends on `k`, never on a modulus bit-length `n`
(except `shor_plan`'s own explicit `n`-ladder, which is the whole point of
that section). `k` enters everywhere; `n` never does outside `shor_plan`.
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

def opCensusJson (c : OpCensus) : Json :=
  Json.mkObj [
    ("phaseProduct", (c.phaseProduct : Json)),
    ("addScaled", (c.addScaled : Json)),
    ("negate", (c.negate : Json)),
    ("shiftL", (c.shiftL : Json)),
    ("shiftR", (c.shiftR : Json)),
    ("adderClassTotal", (c.adderClassTotal : Json))
  ]

/-- E1: the schedule (ops, points, census, and per-op-class `LowGate`
resources at a representative width). -/
def scheduleJson {k : ℕ} (inst : TableInstance k) (wRep : ℕ) : Json :=
  Json.mkObj [
    ("ops", progJson inst.ops),
    ("points", Json.arr (inst.points.map pointJson).toArray),
    ("q", (q k : Json)),
    ("census", opCensusJson (opCensus inst.ops)),
    ("resources_at_width", Json.mkObj [
      ("width", (wRep : Json)),
      ("addScaled", gateResourcesJson (addScaledResourcesAt wRep)),
      ("negate", gateResourcesJson (negateResourcesAt wRep)),
      ("radixReverse", gateResourcesJson (radixReverseResourcesAt wRep))
    ])
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

/-- E3: width tables. -/
def widthJson {k : ℕ} (ops : Prog k) (mMax wMax : ℕ) : Json :=
  let byM := widthTableByM ops mMax
  let byW := widthTableByW ops wMax
  let tail := affineTail (byM.map (fun p => (p.1, p.2.1)))
  Json.mkObj [
    ("by_m",
      Json.arr (byM.map (fun p =>
        Json.mkObj [
          ("m", (p.1 : Json)), ("width", (p.2.1 : Json)), ("limb_width", (p.2.2 : Json))
        ])).toArray),
    ("by_w",
      Json.arr (byW.map (fun p =>
        Json.mkObj [
          ("w", (p.1 : Json)), ("next_width", (p.2.1 : Json)),
          ("reserve_x", (p.2.2.1 : Json)), ("reserve_z", (p.2.2.2 : Json))
        ])).toArray),
    ("affine_tail",
      match tail with
      | some (m0, β) => Json.mkObj [("m0", (m0 : Json)), ("beta", (β : Json))]
      | none => Json.null)
  ]

def recursionLevelJson (l : RecursionLevel) : Json :=
  Json.mkObj [
    ("depth", (l.depth : Json)),
    ("width", (l.width : Json)),
    ("leaf_multiplicity", (l.leafMultiplicity : Json)),
    ("adder_cost", (l.adderCost : Json)),
    ("base_cost", (l.baseCost : Json))
  ]

/-- E6: the recursion skeleton, starting the ladder from `w`. -/
def recursionJson {k : ℕ} (ops : Prog k) (w : ℕ) : Json :=
  let levels := recursionLevels ops w
  Json.mkObj [
    ("levels", Json.arr (levels.map recursionLevelJson).toArray),
    ("total_cost", (recursionTotalCost levels : Json))
  ]

/-- E4: the QFT plan. -/
def qftPlanJson {k : ℕ} (ops : Prog k) (wMax : ℕ) : Json :=
  Json.mkObj [
    ("rows",
      Json.arr ((qftPlanTable ops wMax).map (fun row =>
        Json.mkObj [
          ("w", (row.1 : Json)), ("left", (row.2.1 : Json)), ("right", (row.2.2.1 : Json)),
          ("qft_phi", angleJson row.2.2.2.1),
          ("radix_reverse_cost", (row.2.2.2.2.1 : Json)),
          ("x_workspace_need", (row.2.2.2.2.2.1 : Json)),
          ("z_workspace_need", (row.2.2.2.2.2.2 : Json))
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
  let workTail := affineTail (row.perM.map (fun p => (p.m, p.workWidth)))
  Json.mkObj [
    ("n", (row.n : Json)),
    ("x_width", (row.xWidth : Json)),
    ("data_width", (row.dataWidth : Json)),
    ("per_m", Json.arr (row.perM.map shorPlanPerMJson).toArray),
    ("work_width_affine_tail",
      match workTail with
      | some (m0, β) => Json.mkObj [("m0", (m0 : Json)), ("beta", (β : Json))]
      | none => Json.null)
  ]

/-- E5: the Shor register plan. -/
def shorPlanJson {k : ℕ} (ops : Prog k) (nMin nMax mMax : ℕ) : Json :=
  Json.mkObj [
    ("rows", Json.arr ((shorPlanTable ops nMin nMax mMax).map shorPlanRowJson).toArray)
  ]

/-- Per-section provenance: which Lean declaration each section evaluates,
and whether that declaration is a theorem (see README "What is and is not a
theorem"). -/
def provenanceJson (src : TableSource) : Json :=
  Json.mkObj [
    ("table", Json.str
      (match src with
        | .standard =>
            "Shor.standardLoweringSetup: ProgConsumesPtsSafe/returns-to-start are " ++
            "theorems (genOpsWithProduct_ProgConsumesPtsSafe, " ++
            "genOpsWithProduct_returns_to_original)"
        | .generate =>
            "Table_Generation.generate: checked at run time only, no correctness theorem")),
    ("coeff_poly", Json.str
      ("M⁻¹ computed exactly by Gauss-Jordan elimination over ℚ (gaussJordanInverseRows); " ++
      "agreement with cramerCoeffFromPtsWidth is a run-time check over the checked m range " ++
      "(gated: unconditional k ≤ 3, --check-cramer up to k ≤ 4, skipped from k = 5), and " ++
      "cramerCoeffFromPtsWidth = phaseCoeffFromPtsWidth is the theorem " ++
      "cramerCoeffFromPtsWidth_eq_phaseCoeffFromPtsWidth")),
    ("width", Json.str
      ("RecursivePhaseWorkspace.nextWidth/limbWidth/reserveNeed evaluated directly; " ++
      "affine tails are detected numerically and are advisory")),
    ("recursion", Json.str
      ("shorGateCostModel evaluated on the width ladder; the asymptotic statement is " ++
      "Shor.phaseProductGateCountBound_of_programOK / Shor.exists_shorGateCountBound " ++
      "(evaluated here, not proved)")),
    ("qft_plan", Json.str
      ("qftWorkspaceNeed/qftPhi evaluated directly, matching standardQFTLoweringPlan's own " ++
      "recursion")),
    ("shor_plan", Json.str
      ("referenceXWidth/referenceDataWidth/referenceWorkWidth/referenceScratchWidth/" ++
      "referenceWorkspaceNeed evaluated on synthetic instances N = 2^n - 1, a = 2. The " ++
      "constant-arithmetic primitives lowerCmpGeConst/lowerCSubConst (steps U3, U4 of " ++
      "CmodMulInPlaceCore) are linear in register width with no recursion and no table " ++
      "dependence, so they are not tabulated here: their per-width counts are meant to be read " ++
      "off concrete `shor` documents at small N and fitted outside Lean")),
    ("template", Json.str
      ("Symbolic/Template.lean's phase-product/QFT/Shor templates, evaluated structurally " ++
      "from the compiler's own op sequence and gate-tree shape (Compile.lean, Gates.lean, " ++
      "OrderFinding.lean/ModExp.lean/Steps.lean) — not checked against the real lowering at " ++
      "any concrete width (that is Phase 2's job); nextWidth is opaque, its values are the " ++
      "width section's table"))
  ]

/-- The `template` section's object (E7, one level — see `Symbolic/Template.lean`). -/
def templateSectionJson {k : ℕ} (inst : TableInstance k) : Json :=
  Json.mkObj [
    ("phase_product", phaseProductTemplateJson inst.ops false),
    ("controlled_phase_product", phaseProductTemplateJson inst.ops true),
    ("qft", qftTemplateJson),
    ("shor", shorTemplateJson)
  ]

/-- Build the `forshor.emit/v1` document, or refuse with a message if the
table's blocking checks fail (`TableSource.generate` only). -/
def buildBundle
    (src : TableSource) (k : ℕ) (hk : 1 < k) (mMax wMax : ℕ) (checkCramer : Bool) :
    Except String Json :=
  let inst := tableInstance src k hk
  match checkTable src k hk inst with
  | .error e => .error e
  | .ok () =>
      let nMin := 2
      let nMax := min wMax 16
      .ok (Json.mkObj [
        ("schema", Json.str "forshor.emit/v1"),
        ("k", (k : Json)),
        ("table", Json.str (match src with | .standard => "standard" | .generate => "generate")),
        ("n_free", Json.bool true),
        ("opts", optsJson { mMax := mMax, wMax := wMax, checkCramer := checkCramer }),
        ("schedule", scheduleJson inst wMax),
        ("coeff_poly", coeffPolyJson inst checkCramer mMax),
        ("width", widthJson inst.ops mMax wMax),
        ("qft_plan", qftPlanJson inst.ops wMax),
        ("shor_plan", shorPlanJson inst.ops nMin nMax mMax),
        ("recursion", recursionJson inst.ops wMax),
        ("template", templateSectionJson inst),
        ("provenance", provenanceJson src)
      ])

/-- The section names `buildSection` understands, i.e. every field of
`buildBundle`'s document except `schema`/`k`/`table`/`n_free`/`opts`/
`provenance`. -/
def sectionNames : List String :=
  ["schedule", "coeff_poly", "width", "qft_plan", "shor_plan", "recursion", "template"]

/-- Build a single named section of the bundle document, in the same
envelope (`schema, k, table, n_free, opts, provenance`) but with only that
one section's data under its own name — same blocking checks as `bundle`. -/
def buildSection
    (sectionName : String) (src : TableSource) (k : ℕ) (hk : 1 < k) (mMax wMax : ℕ)
    (checkCramer : Bool) : Except String Json :=
  let inst := tableInstance src k hk
  match checkTable src k hk inst with
  | .error e => .error e
  | .ok () =>
      let nMin := 2
      let nMax := min wMax 16
      let sectionJson? : Except String Json :=
        match sectionName with
        | "schedule" => .ok (scheduleJson inst wMax)
        | "coeff_poly" => .ok (coeffPolyJson inst checkCramer mMax)
        | "width" => .ok (widthJson inst.ops mMax wMax)
        | "qft_plan" => .ok (qftPlanJson inst.ops wMax)
        | "shor_plan" => .ok (shorPlanJson inst.ops nMin nMax mMax)
        | "recursion" => .ok (recursionJson inst.ops wMax)
        | "template" => .ok (templateSectionJson inst)
        | other => .error s!"unknown section: {other} (expected one of {sectionNames})"
      match sectionJson? with
      | .error e => .error e
      | .ok sj =>
          .ok (Json.mkObj [
            ("schema", Json.str "forshor.emit/v1"),
            ("k", (k : Json)),
            ("table", Json.str (match src with | .standard => "standard" | .generate => "generate")),
            ("n_free", Json.bool true),
            ("section", Json.str sectionName),
            ("opts", optsJson { mMax := mMax, wMax := wMax, checkCramer := checkCramer }),
            (sectionName, sj),
            ("provenance", provenanceJson src)
          ])

/-- `forshor_emit phases <k> <m> <phiNum/phiDen>`: exactly `q k` lines, each
`c_l(2^m) · phi` as a reduced `num/den` (row `l`'s E2 coefficient polynomial,
evaluated at the chunk width `m` and scaled by `phi`). Always the standard
table (the `bundle` default). -/
def buildPhases (k m : ℕ) (phiNum phiDen : ℤ) : Except String (List String) :=
  if hk : 1 < k then
    let inst := tableInstance .standard k hk
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
