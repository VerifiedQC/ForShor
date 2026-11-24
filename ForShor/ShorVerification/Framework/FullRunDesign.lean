import Lean.Data.Json

namespace Shor

open Lean (Json)

/-! # The full-run design surface

This mirrors the consumer's design surface field for field, so the *type* is
orthogonal: any combination of multiplier, per-family QFT choice, per-family rotation backend
and per-step phase backend is expressible.

The *accepted set* is deliberately narrower than the type. `FullRunDesign.qualified` lists the
eight selections that have been qualified, and `FullRunDesign.label?` is `none` for everything
else, which the submission executable refuses. Widening the accepted set is a separate change
that needs a price path and a per-point witness; it is not done here.
-/

inductive FullRunMultiplier where
  | reference | splitCompare | quotientStream
  deriving BEq

inductive QftBackend where
  | rossSelinger | catalytic
  deriving BEq

/-- Mirrors the consumer's QFT backend label. These two strings are the consumer's `BACKENDS`
    (`evaluation/export_v2/qft_overlay.py`); anything else is refused there by name. -/
def QftBackend.label : QftBackend → String
  | .rossSelinger => "ross_selinger"
  | .catalytic => "catalytic"

/-- An exact positive decimal smaller than one, serialized without a floating conversion.
    Mirrors the consumer's error-ceiling field. -/
structure ErrorCeiling where
  units : Nat
  scale : Nat
  positive : 0 < units
  belowOne : units < 10 ^ scale
  scaleBound : scale ≤ 60

/-- Equality on the two data fields only. The remaining fields are proofs, so by proof
    irrelevance two ceilings agreeing on `units` and `scale` are equal; comparing the proofs
    would be both impossible to derive and meaningless. -/
instance : BEq ErrorCeiling where
  beq a b := a.units == b.units && a.scale == b.scale

inductive QftTarget where
  | exact | approximate (ceiling : ErrorCeiling)
  deriving BEq

structure QftChoice where
  backend : QftBackend
  target : QftTarget
  deriving BEq

/-- Byte for byte the consumer's per-family QFT choice. This shape *is* the
    contract the consumer parses: `evaluation/export_v2/qft_overlay.py` `parse_design` accepts
    exactly `{"backend", "target"}` plus `"max_error"` iff the target is `"approximate"`, and the
    ceiling is spelled `<units>e-<scale>` because `parse_max_error` accepts that form and
    nothing else -- not a float, not `1.5e-6`, not `1E-6`. Serializing the ceiling through a
    floating conversion would be refused there, so it is written out of `Nat`s. -/
def QftChoice.json (q : QftChoice) : Json :=
  let common := [("backend", Json.str q.backend.label)]
  match q.target with
  | .exact => Json.mkObj (common ++ [("target", Json.str "exact")])
  | .approximate e => Json.mkObj (common ++ [("target", Json.str "approximate"),
      ("max_error", Json.str s!"{e.units}e-{e.scale}")])

/-- The phase-product route for one step. Named as in the consumer's per-step backend field. -/
inductive PhaseBackend where
  | rossSelinger | fallback | selectiveKick
  deriving BEq

inductive RotationBackend where
  | rossSelinger | fallback
  deriving BEq

/-- A typed full-run selection, separate from the table policy and standalone synthesis.
    The verifier attests the choice; a separate circuit checker must qualify its implementation. -/
structure FullRunDesign where
  multiplier : FullRunMultiplier := .reference
  data : Option QftChoice := none
  work : Option QftChoice := none
  scratch : Option QftChoice := none
  exponent : Option QftChoice := none
  dataRotations : Option RotationBackend := none
  workRotations : Option RotationBackend := none
  scratchRotations : Option RotationBackend := none
  exponentRotations : Option RotationBackend := none
  step1 : Option PhaseBackend := none
  step2 : Option PhaseBackend := none
  step4 : Option PhaseBackend := none
  step5 : Option PhaseBackend := none
  deriving BEq

/-- No selection at all. For the consumer this is "no compiled selection", *not* an empty
    design record: the empty selection is not a design. `compiledSelection?` below keeps that
    asymmetry, so this value never reaches the document as a design object. -/
def FullRunDesign.reference : FullRunDesign := {}

private def ceil25e5 : ErrorCeiling := ⟨25, 5, by decide, by decide, by decide⟩
private def exactDirect : QftChoice := ⟨.rossSelinger, .exact⟩
private def bandedDirect : QftChoice := ⟨.rossSelinger, .approximate ceil25e5⟩
private def apxCatalytic : QftChoice := ⟨.catalytic, .approximate ceil25e5⟩

def FullRunDesign.quotientExact : FullRunDesign :=
  { multiplier := .quotientStream, data := some exactDirect, work := some exactDirect }

def FullRunDesign.quotientCatalytic : FullRunDesign :=
  { multiplier := .quotientStream, data := some apxCatalytic, work := some apxCatalytic }

def FullRunDesign.quotientBandedDataCatalyticWork : FullRunDesign :=
  { multiplier := .quotientStream, data := some bandedDirect, work := some apxCatalytic }

def FullRunDesign.quotientFallbackDataCatalyticWork : FullRunDesign :=
  { FullRunDesign.quotientBandedDataCatalyticWork with dataRotations := some .fallback }

def FullRunDesign.quotientStep2Fallback : FullRunDesign :=
  { FullRunDesign.quotientCatalytic with step2 := some .fallback }

def FullRunDesign.splitStep4Kicks : FullRunDesign :=
  { multiplier := .splitCompare, data := some apxCatalytic, work := some apxCatalytic,
    scratch := some apxCatalytic, step4 := some .selectiveKick }

def FullRunDesign.splitStep2FallbackStep4Kicks : FullRunDesign :=
  { FullRunDesign.splitStep4Kicks with step2 := some .fallback }

/-- The qualified selections, in the order they were qualified, each with the profile name the
    document attests. A well-typed design that is not on this list is refused, never priced and
    never labelled. -/
def FullRunDesign.qualified : List (FullRunDesign × String) :=
  [(.reference, "reference"),
   (.quotientExact, "quotient-exact"),
   (.quotientCatalytic, "quotient-catalytic"),
   (.quotientBandedDataCatalyticWork, "quotient-banded-data-catalytic-work"),
   (.quotientFallbackDataCatalyticWork, "quotient-fallback-data-catalytic-work"),
   (.quotientStep2Fallback, "quotient-step2-fallback"),
   (.splitStep4Kicks, "split-step4-kicks"),
   (.splitStep2FallbackStep4Kicks, "split-step2-fallback-step4-kicks")]

/-- `some` exactly for a qualified selection. `none` means "well typed but not qualified":
    the caller refuses, and must not fall back to a neighbouring profile. -/
def FullRunDesign.label? (d : FullRunDesign) : Option String :=
  (FullRunDesign.qualified.find? fun p => p.1 == d).map Prod.snd

/-- The compiled selection, mirroring the consumer's: `none` is "no design at
    all", which is what `reference` means. A caller merging a `submitted_full_run` key must
    branch on this rather than on the record's contents, so that the default emits no key
    instead of an empty design object. -/
def FullRunDesign.compiledSelection? (d : FullRunDesign) : Option FullRunDesign :=
  if d == FullRunDesign.reference then none else some d

/-! ## The design body

A qualified selection is attested by its profile label. A well-typed selection that is *not*
qualified has no label, and rather than naming nothing it attests its own design BODY: the
serialization below, inside the envelope the compiled exports already use.

Only the QFT BACKEND AXIS is serialized -- the four families' `backend`/`target` choices, on the
reference topology. `modmul`, `phase_product` and the per-family `rotation_backend` are
deliberately NOT emitted, because the consumer refuses every one of them by name
(`evaluation/export_v2/full_run_design.py`: the topology gate, the `phase_product` refusal and
the `rotation_backend` refusal). Emitting them would turn a priceable design into a refusal.
-/

/-- Everything outside the QFT backend axis that this design could set, and that `json` does not
    serialize: the multiplier topology, the four per-family rotation backends and the four
    per-step phase-product routes.

    A design setting any of them must NOT be serialized, and `body?` below is the only way to
    reach `json` for that reason. The consumer reads an absent `modmul` as the reference topology
    (`full_run_design.py` `_design_of_body`: `body.get(MULTIPLIER_KEY) or MULTIPLIER_REFERENCE`),
    so emitting a body for a `quotientStream` design would price a quotient-stream run on
    REFERENCE-topology numbers -- the silent default the release forbids. It is refused in
    `PolicyMain` instead. -/
def FullRunDesign.qftOnly (d : FullRunDesign) : Bool :=
  d.multiplier == .reference
    && d.dataRotations.isNone && d.workRotations.isNone
    && d.scratchRotations.isNone && d.exponentRotations.isNone
    && d.step1.isNone && d.step2.isNone && d.step4.isNone && d.step5.isNone

/-- The `forshor.design-local/v1` body, mirroring the consumer's design serialization
    restricted to the keys that carry the QFT families.

    `readout` is not a body key: production carries `submitted_readout` as its own top-level
    key beside `submitted_full_run`, and the consumer refuses `readout` inside the body as an
    `unknown-body-key`. A family the design leaves `none` is omitted, which the consumer reads as
    "unchanged from the engine default"; it is not written as an explicit null. -/
def FullRunDesign.json (d : FullRunDesign) : Json :=
  let families := [("data", d.data), ("work", d.work), ("scratch", d.scratch),
                   ("exponent", d.exponent)]
  Json.mkObj [("schema", Json.str "forshor.design-local/v1"),
    ("qft", Json.mkObj (families.filterMap fun (name, q) => q.map fun v => (name, v.json)))]

/-- The body to attest for an unlabelled selection, or `none` when the design sets an axis
    `json` does not serialize. The caller refuses on `none`; it must never serialize the design
    anyway, and must never fall back to the reference price. -/
def FullRunDesign.body? (d : FullRunDesign) : Option Json :=
  if d.qftOnly then some d.json else none

end Shor
