import FastMultiplication.Emit.Json.LowGateJson
import FastMultiplication.ShorVerification.Implementation.QFT.Lowering.PlanBuilders

/-!
# Annotated plan printer

A printer over `PhaseLoweringPlan` (constructor for constructor) and
`QFTLoweringPlan` (`split` carries the twiddle). Unlike `lowGateJson` (which
walks the flat `LowGate` term `lowerGateRec`/`lowerQFTPlan` produce), this
walks the *plan* term those functions consume, so the recursive structure —
where each phase-product/QFT level begins and what its layout data was — is
still visible. It is not a mirror: `signedStep`/`cSignedStep` print exactly
the fields `standardSignedPhaseLoweringPlan`'s `.signedStep`/`.cSignedStep`
constructor carries (`phi, x, z, input_size, next_width, limb_width, coeffs`)
plus the nested `body`; `signedBase`/`cSignedBase` print
`NaiveSignedPhaseProd`/`NaiveCSignedPhaseProd` together with their flat
`CPhase` expansion (obtained by handing this same leaf to `lowGateJson`)
under `expansion`, so a consumer can compare census on the same footing
without re-deriving the expansion itself.
-/

namespace Shor

open Lean (Json)
open Operations

/-- Printer over `PhaseLoweringPlan`, constructor for constructor. -/
partial def planJson {k : ℕ} {hk : 1 < k} {pts : List Point} {hpts : pts.length = q k}
    {ops : Prog k} {initSize : ℕ} {U : Gate} :
    PhaseLoweringPlan k hk pts hpts ops initSize U → Json
  | .id _ => Json.mkObj [("op", Json.str "id")]
  | .seq left right =>
      Json.mkObj [("op", Json.str "seq"), ("body", Json.arr #[planJson left, planJson right])]
  | .H _ q => Json.mkObj [("op", Json.str "H"), ("q", (q : Json))]
  | .X _ q => Json.mkObj [("op", Json.str "X"), ("q", (q : Json))]
  | .ShiftL _ r n => Json.mkObj [("op", Json.str "ShiftL"), ("r", extRegJson r), ("n", (n : Json))]
  | .ShiftR _ r n => Json.mkObj [("op", Json.str "ShiftR"), ("r", extRegJson r), ("n", (n : Json))]
  | .Negate _ r => Json.mkObj [("op", Json.str "Negate"), ("r", extRegJson r)]
  | .AddScaled _ dst src negSrc shift =>
      Json.mkObj [
        ("op", Json.str "AddScaled"), ("dst", extRegJson dst), ("src", extRegJson src),
        ("negSrc", Json.bool negSrc), ("shift", (shift : Json))
      ]
  | .zeroExtend _ r n =>
      Json.mkObj [("op", Json.str "zeroExtend"), ("r", extRegJson r), ("n", (n : Json))]
  | .signExtend _ r n =>
      Json.mkObj [("op", Json.str "signExtend"), ("r", extRegJson r), ("n", (n : Json))]
  | .zeroDealloc _ r n =>
      Json.mkObj [("op", Json.str "zeroDealloc"), ("r", extRegJson r), ("n", (n : Json))]
  | .signDealloc _ r n =>
      Json.mkObj [("op", Json.str "signDealloc"), ("r", extRegJson r), ("n", (n : Json))]
  | .RadixReverse _ r m =>
      Json.mkObj [("op", Json.str "RadixReverse"), ("r", regJson r), ("m", (m : Json))]
  | .signedBase phi x z _ =>
      Json.mkObj [
        ("op", Json.str "NaiveSignedPhaseProd"),
        ("phi", angleJson phi), ("x", extRegJson x), ("z", extRegJson z),
        ("expansion", lowGateJson (LowGate.Naive_SignedPhaseProd phi x z))
      ]
  | .signedStep phi x z _layout _hrec _hcapacity child =>
      Json.mkObj [
        ("op", Json.str "SignedPhaseProd"),
        ("phi", angleJson phi), ("x", extRegJson x), ("z", extRegJson z),
        ("input_size", (initSize : Json)),
        ("next_width", ((nextSignedWidth x z ops : ℕ) : Json)),
        ("limb_width", ((phaseLimbWidth x z k : ℕ) : Json)),
        ("coeffs",
          Json.arr
            (((List.finRange (q k)).map
              (fun l => ratJson (loweringPhaseCoeff k x z pts hpts l))).toArray)),
        ("body", planJson child)
      ]
  | .cSignedBase ctrl phi x z _ =>
      Json.mkObj [
        ("op", Json.str "NaiveCSignedPhaseProd"),
        ("ctrl", (ctrl : Json)), ("phi", angleJson phi), ("x", extRegJson x), ("z", extRegJson z),
        ("expansion", lowGateJson (LowGate.Naive_CSignedPhaseProd ctrl phi x z))
      ]
  | .cSignedStep ctrl phi x z _layout _hrec _hcapacity _hctrl child =>
      Json.mkObj [
        ("op", Json.str "CSignedPhaseProd"),
        ("ctrl", (ctrl : Json)), ("phi", angleJson phi), ("x", extRegJson x), ("z", extRegJson z),
        ("input_size", (initSize : Json)),
        ("next_width", ((nextSignedWidth x z ops : ℕ) : Json)),
        ("limb_width", ((phaseLimbWidth x z k : ℕ) : Json)),
        ("coeffs",
          Json.arr
            (((List.finRange (q k)).map
              (fun l => ratJson (loweringPhaseCoeff k x z pts hpts l))).toArray)),
        ("body", planJson child)
      ]

/-- Check 1's deep flattener: splice `seq` nodes fully (matching
`LowGate.flattenSeq`), substitute `SignedPhaseProd`/`CSignedPhaseProd`
annotations with their `expansion`/`body`, drop `id`. Moved here from the
now-deleted `Lower/Instantiate.lean` (R4) — still used by
`pp`/`cpp`'s `annotated_eq_flat` check, which has nothing to do with the
extracted `Doc`. -/
partial def deepFlattenPlanJsonList (j : Json) : List Json :=
  match (j.getObjValD "op").getStr?.toOption with
  | some "id" => []
  | some "seq" =>
      match (j.getObjValD "body").getArr?.toOption with
      | some arr => arr.toList.flatMap deepFlattenPlanJsonList
      | none => [j]
  | some "SignedPhaseProd" | some "CSignedPhaseProd" =>
      deepFlattenPlanJsonList (j.getObjValD "body")
  | some "NaiveSignedPhaseProd" | some "NaiveCSignedPhaseProd" =>
      -- `expansion` is itself `lowGateJson`'s output for a `LowGate.seq` term
      -- (or a single leaf) — splice it the same way, don't embed it opaquely.
      deepFlattenPlanJsonList (j.getObjValD "expansion")
  | _ => [j]

/-- Canonicalize a flattened list the same way `lowGateJson` would present a
top-level term: a single item as itself, `id` (an empty list) as `{"op":
"id"}`, otherwise as one `seq` node wrapping the whole n-ary list. -/
def wrapFlattened (items : List Json) : Json :=
  match items with
  | [] => Json.mkObj [("op", Json.str "id")]
  | [single] => single
  | _ => Json.mkObj [("op", Json.str "seq"), ("body", Json.arr items.toArray)]

/-- Check 1: deep-flattening the annotated plan's JSON equals `lowGateJson`
of the independently-computed flat term. -/
def check1_annotatedEqFlat (planJ : Json) (flat : LowGate) : Bool :=
  wrapFlattened (deepFlattenPlanJsonList planJ) == lowGateJson flat

/-- Printer over `QFTLoweringPlan`: `split` carries the twiddle angle and the
recursive left/right plans; the phase-product body between them is printed
through `planJson` (it is itself a `StandardPhaseLoweringPlan`, so its
`seq`/`zeroExtend`/`signedStep`/`zeroDealloc` shape prints exactly as any
other plan node — no special case is needed for it). -/
partial def qftPlanJsonOf
    {k : ℕ} {hk : 1 < k} {pts : List Point} {hpts : pts.length = q k} {ops : Prog k} {r : Reg} :
    QFTLoweringPlan k hk pts hpts ops r → Json
  | .empty r _ => Json.mkObj [("op", Json.str "id"), ("r", regJson r)]
  | .singleton r _ => Json.mkObj [("op", Json.str "H"), ("r", regJson r)]
  | .split r _hsize _ws _phaseInitSize phasePlan rightPlan leftPlan =>
      Json.mkObj [
        ("op", Json.str "QFT"),
        ("r", regJson r),
        ("left", regJson (leftReg r)),
        ("right", regJson (rightReg r)),
        ("phi", angleJson (qftPhi (regSize r))),
        ("phase_body", planJson phasePlan),
        ("right_body", qftPlanJsonOf rightPlan),
        ("left_body", qftPlanJsonOf leftPlan),
        ("radix_reverse_m", ((splitM r : ℕ) : Json))
      ]

end Shor
