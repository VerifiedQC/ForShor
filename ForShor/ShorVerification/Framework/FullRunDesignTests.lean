import ForShor.ShorVerification.Framework.FullRunDesign

/-! # Tests for the orthogonal full-run design surface

Each group names the production change it would catch. Built by hand with
`lake env lean` rather than wired into `lean_lib PolicyTests`, because that target is inside the
`PolicySubmission` build closure and adding to it would widen every submission's build. This
file imports only `Framework/FullRunDesign.lean`, which has no imports of its own, so checking
it costs well under a second and needs no lakefile change.

The byte-level export-identity obligation is *not* here: `#guard` is Lean-internal and proves
nothing about compiled output. That half lives in the external harness.
-/

namespace Shor

/-! ## 1. The bundles are the values of the §1.1 mapping table

Catches a transcription error in any bundle `def`: a wrong multiplier, a wrong backend, a
wrong target, a ceiling other than 25e-5, or a field set on the wrong family. Written as
explicit field reads rather than as a comparison against a second copy of the same record
literal, which would be vacuous.
-/

private def ceil : ErrorCeiling := ⟨25, 5, by decide, by decide, by decide⟩
private def exactDirect : QftChoice := ⟨.rossSelinger, .exact⟩
private def bandedDirect : QftChoice := ⟨.rossSelinger, .approximate ceil⟩
private def apxCatalytic : QftChoice := ⟨.catalytic, .approximate ceil⟩

-- row 1: quotient-exact
#guard FullRunDesign.quotientExact.multiplier == .quotientStream
#guard FullRunDesign.quotientExact.data == some exactDirect
#guard FullRunDesign.quotientExact.work == some exactDirect
#guard FullRunDesign.quotientExact.scratch == none
#guard FullRunDesign.quotientExact.step2 == none
#guard FullRunDesign.quotientExact.step4 == none
#guard FullRunDesign.quotientExact.dataRotations == none

-- row 2: quotient-catalytic
#guard FullRunDesign.quotientCatalytic.multiplier == .quotientStream
#guard FullRunDesign.quotientCatalytic.data == some apxCatalytic
#guard FullRunDesign.quotientCatalytic.work == some apxCatalytic
#guard FullRunDesign.quotientCatalytic.scratch == none
#guard FullRunDesign.quotientCatalytic.step2 == none

-- row 3: quotient-banded-data-catalytic-work
#guard FullRunDesign.quotientBandedDataCatalyticWork.multiplier == .quotientStream
#guard FullRunDesign.quotientBandedDataCatalyticWork.data == some bandedDirect
#guard FullRunDesign.quotientBandedDataCatalyticWork.work == some apxCatalytic
#guard FullRunDesign.quotientBandedDataCatalyticWork.dataRotations == none

-- row 4: quotient-fallback-data-catalytic-work -- banded data, catalytic work, fallback rotations
#guard FullRunDesign.quotientFallbackDataCatalyticWork.multiplier == .quotientStream
#guard FullRunDesign.quotientFallbackDataCatalyticWork.data == some bandedDirect
#guard FullRunDesign.quotientFallbackDataCatalyticWork.work == some apxCatalytic
#guard FullRunDesign.quotientFallbackDataCatalyticWork.dataRotations == some .fallback
#guard FullRunDesign.quotientFallbackDataCatalyticWork.workRotations == none

-- row 5: quotient-step2-fallback
#guard FullRunDesign.quotientStep2Fallback.multiplier == .quotientStream
#guard FullRunDesign.quotientStep2Fallback.data == some apxCatalytic
#guard FullRunDesign.quotientStep2Fallback.work == some apxCatalytic
#guard FullRunDesign.quotientStep2Fallback.step2 == some .fallback
#guard FullRunDesign.quotientStep2Fallback.step4 == none

-- row 6: split-step4-kicks -- the only family that sets scratch
#guard FullRunDesign.splitStep4Kicks.multiplier == .splitCompare
#guard FullRunDesign.splitStep4Kicks.data == some apxCatalytic
#guard FullRunDesign.splitStep4Kicks.work == some apxCatalytic
#guard FullRunDesign.splitStep4Kicks.scratch == some apxCatalytic
#guard FullRunDesign.splitStep4Kicks.step4 == some .selectiveKick
#guard FullRunDesign.splitStep4Kicks.step2 == none

-- row 7: split-step2-fallback-step4-kicks
#guard FullRunDesign.splitStep2FallbackStep4Kicks.multiplier == .splitCompare
#guard FullRunDesign.splitStep2FallbackStep4Kicks.scratch == some apxCatalytic
#guard FullRunDesign.splitStep2FallbackStep4Kicks.step2 == some .fallback
#guard FullRunDesign.splitStep2FallbackStep4Kicks.step4 == some .selectiveKick

/-! §1.1 "fields never set by any bundle". Catches a bundle that silently acquires an
exponent family (all seven are semiclassical readout, so exponent is inactive by construction)
or a step1/step5 route, neither of which has any construction at all. -/
#guard FullRunDesign.qualified.all fun p =>
  p.1.exponent == none && p.1.exponentRotations == none && p.1.scratchRotations == none
    && p.1.step1 == none && p.1.step5 == none

/-! `workRotations` is never set by any bundle either -- only row 4's `dataRotations` is.
Catches the fallback-rotation variant being attached to the wrong family, which the
consumer hard-refuses. -/
#guard FullRunDesign.qualified.all fun p => p.1.workRotations == none

/-! ## 2. Labels round-trip

Catches a renamed or misspelt profile string, which would break the attested
`submitted_full_run.profile` and so the downstream comparison against it.
These eight strings are a wire format.
-/
#guard FullRunDesign.reference.label? == some "reference"
#guard FullRunDesign.quotientExact.label? == some "quotient-exact"
#guard FullRunDesign.quotientCatalytic.label? == some "quotient-catalytic"
#guard FullRunDesign.quotientBandedDataCatalyticWork.label?
  == some "quotient-banded-data-catalytic-work"
#guard FullRunDesign.quotientFallbackDataCatalyticWork.label?
  == some "quotient-fallback-data-catalytic-work"
#guard FullRunDesign.quotientStep2Fallback.label? == some "quotient-step2-fallback"
#guard FullRunDesign.splitStep4Kicks.label? == some "split-step4-kicks"
#guard FullRunDesign.splitStep2FallbackStep4Kicks.label?
  == some "split-step2-fallback-step4-kicks"

/-! ## 3. `reference` is the all-defaults value, and is "no design at all"

Catches a port that gives `reference` a non-default field (the perturbation used for the
non-vacuity half of the byte test), and catches `compiledSelection?` being made total, which
would make the default emit an empty design object instead of suppressing the key.
-/
#guard FullRunDesign.reference == ({} : FullRunDesign)
#guard FullRunDesign.reference.compiledSelection? == none
#guard (FullRunDesign.quotientExact.compiledSelection?.map FullRunDesign.multiplier)
  == some .quotientStream

/-! Every non-reference qualified bundle has a compiled selection. Catches `compiledSelection?`
comparing against the wrong value and silently suppressing a real selection's key. -/
#guard (FullRunDesign.qualified.filter fun p => p.1.compiledSelection?.isNone).length == 1

/-! ## 4. No two qualified entries collide

The length check alone is vacuous: `label?` uses `find?`, so two equal designs would resolve
to the first label and the length would still be 8. The second guard is the real one -- it
asserts each entry's own label round-trips, which fails if any earlier entry shadows it.
Catches a copy-paste bundle that duplicates another, e.g. `splitStep2FallbackStep4Kicks`
losing its `step2` and becoming `splitStep4Kicks`.
-/
#guard FullRunDesign.qualified.length == 8
#guard FullRunDesign.qualified.all fun p => p.1.label? == some p.2

/-! ## 5. Off-menu designs have no label

The type is orthogonal, the accepted set is not. Catches `label?` being widened to a total
function or defaulting to a neighbouring profile -- the lane doc's "a refusal must not fall
back to a different family or legacy route".
-/

-- `exactCatalytic`, a typed QFT choice no bundle reaches (§2.1).
#guard (({ multiplier := .quotientStream,
           data := some ⟨.catalytic, .exact⟩ } : FullRunDesign)).label? == none
-- Step 1, which has no construction at all.
#guard (({ step1 := some .fallback } : FullRunDesign)).label? == none
-- The reference multiplier with a QFT choice: budget-recomputable, but not qualified.
#guard (({ data := some apxCatalytic } : FullRunDesign)).label? == none
-- A ceiling other than 25e-5, refused downstream as an off-menu ceiling.
#guard (({ multiplier := .quotientStream,
           data := some ⟨.catalytic, .approximate ⟨5, 5, by decide, by decide, by decide⟩⟩,
           work := some apxCatalytic } : FullRunDesign)).label? == none
-- `quotient-catalytic` plus an unqualified extra field is not `quotient-catalytic`.
#guard ({ FullRunDesign.quotientCatalytic with step4 := some .selectiveKick }).label? == none
-- Step 4 adaptive fallback: no construction exists.
#guard ({ FullRunDesign.splitStep4Kicks with step4 := some .fallback }).label? == none

/-! ## 6. `BEq ErrorCeiling` ignores the proof fields but not the data

Catches an `ErrorCeiling` equality that compares `units` only, which would make 25e-5 and
25e-6 interchangeable and silently accept an off-menu ceiling as a qualified bundle.
-/
#guard (⟨25, 5, by decide, by decide, by decide⟩ : ErrorCeiling)
  == ⟨25, 5, by decide, by decide, by decide⟩
#guard !((⟨25, 5, by decide, by decide, by decide⟩ : ErrorCeiling)
  == ⟨25, 6, by decide, by decide, by decide⟩)
#guard !((⟨25, 5, by decide, by decide, by decide⟩ : ErrorCeiling)
  == ⟨2, 5, by decide, by decide, by decide⟩)

/-! ## 7. `QftChoice.json` is the consumer's per-family contract, character for character

The per-family value is not this repo's invention: it is the consumer's per-family QFT choice
shape, and it is
what `evaluation/export_v2/qft_overlay.py` `parse_design` reads. Each guard below pins the
compressed bytes, so it catches a renamed key, a renamed backend label, a `max_error` emitted
beside `target: "exact"` (refused there as "an exact QFT has no band"), a missing `max_error`
beside `"approximate"` (refused as "there is no band to derive"), and any floating or padded
rendering of the ceiling (`parse_max_error` accepts `<units>e-<scale>` and nothing else).
-/
#guard (QftChoice.json ⟨.rossSelinger, .exact⟩).compress
  == "{\"backend\":\"ross_selinger\",\"target\":\"exact\"}"
#guard (QftChoice.json ⟨.catalytic, .exact⟩).compress
  == "{\"backend\":\"catalytic\",\"target\":\"exact\"}"
#guard (QftChoice.json bandedDirect).compress
  == "{\"backend\":\"ross_selinger\",\"max_error\":\"25e-5\",\"target\":\"approximate\"}"
#guard (QftChoice.json apxCatalytic).compress
  == "{\"backend\":\"catalytic\",\"max_error\":\"25e-5\",\"target\":\"approximate\"}"

/-! The ceiling's scale reaches the wire. Catches a serializer that drops or hardcodes the
exponent, which would silently reprice a 25e-9 request as 25e-5. -/
#guard (QftChoice.json ⟨.rossSelinger,
    .approximate ⟨25, 9, by decide, by decide, by decide⟩⟩).compress
  == "{\"backend\":\"ross_selinger\",\"max_error\":\"25e-9\",\"target\":\"approximate\"}"
#guard (QftChoice.json ⟨.rossSelinger,
    .approximate ⟨1, 6, by decide, by decide, by decide⟩⟩).compress
  == "{\"backend\":\"ross_selinger\",\"max_error\":\"1e-6\",\"target\":\"approximate\"}"

/-! ## 8. The design body carries the QFT families and NOTHING else

`full_run_design.py` refuses `modmul` (any non-reference topology), `phase_product` (any step),
a per-family `rotation_backend` and any unknown body key including `readout`. Pinning the whole
compressed body catches an emitter that starts carrying one of them -- which would turn a
priceable design into a refusal -- and catches a dropped or misspelled `schema`, which is
refused as `body-schema`. An absent family is OMITTED, never written as an explicit null:
`parse_design` reads absent as "unchanged from the engine default".
-/
#guard (FullRunDesign.json { data := some apxCatalytic, work := some exactDirect }).compress
  == "{\"qft\":{\"data\":{\"backend\":\"catalytic\",\"max_error\":\"25e-5\","
     ++ "\"target\":\"approximate\"},\"work\":{\"backend\":\"ross_selinger\",\"target\":\"exact\"}},"
     ++ "\"schema\":\"forshor.design-local/v1\"}"
#guard (FullRunDesign.json { scratch := some bandedDirect }).compress
  == "{\"qft\":{\"scratch\":{\"backend\":\"ross_selinger\",\"max_error\":\"25e-5\","
     ++ "\"target\":\"approximate\"}},\"schema\":\"forshor.design-local/v1\"}"
#guard (FullRunDesign.json { exponent := some exactDirect }).compress
  == "{\"qft\":{\"exponent\":{\"backend\":\"ross_selinger\",\"target\":\"exact\"}},"
     ++ "\"schema\":\"forshor.design-local/v1\"}"

/-! All four families at once, in the consumer's family order. Catches a family wired to the
wrong key -- `data` priced at the `work` width would be a wrong price, not a refusal. -/
private def apx1e6 : QftChoice := ⟨.rossSelinger, .approximate ⟨1, 6, by decide, by decide, by decide⟩⟩

private def allFour : FullRunDesign :=
  { data := some exactDirect, work := some bandedDirect, scratch := some apxCatalytic,
    exponent := some apx1e6 }

#guard (FullRunDesign.json allFour).compress
  == "{\"qft\":{\"data\":{\"backend\":\"ross_selinger\",\"target\":\"exact\"},"
     ++ "\"exponent\":{\"backend\":\"ross_selinger\",\"max_error\":\"1e-6\",\"target\":\"approximate\"},"
     ++ "\"scratch\":{\"backend\":\"catalytic\",\"max_error\":\"25e-5\",\"target\":\"approximate\"},"
     ++ "\"work\":{\"backend\":\"ross_selinger\",\"max_error\":\"25e-5\",\"target\":\"approximate\"}},"
     ++ "\"schema\":\"forshor.design-local/v1\"}"

/-! ## 9. `body?` refuses every axis the body cannot carry

This is the gate that keeps a dropped axis from becoming a wrong price. The consumer reads an
absent `modmul` as the REFERENCE topology, so serializing a `quotientStream` design would price
a quotient-stream run on reference-topology numbers. Each guard names the axis it catches.
-/
#guard (({ multiplier := .quotientStream, data := some apxCatalytic } : FullRunDesign)).body?
  == none
#guard (({ multiplier := .splitCompare, data := some apxCatalytic } : FullRunDesign)).body? == none
#guard (({ data := some apxCatalytic, dataRotations := some .fallback } : FullRunDesign)).body?
  == none
#guard (({ workRotations := some .rossSelinger } : FullRunDesign)).body? == none
#guard (({ scratchRotations := some .fallback } : FullRunDesign)).body? == none
#guard (({ exponentRotations := some .fallback } : FullRunDesign)).body? == none
#guard (({ step1 := some .fallback } : FullRunDesign)).body? == none
#guard (({ step2 := some .fallback } : FullRunDesign)).body? == none
#guard (({ step4 := some .selectiveKick } : FullRunDesign)).body? == none
#guard (({ step5 := some .rossSelinger } : FullRunDesign)).body? == none

/-! Every one of the seven non-reference qualified bundles selects a topology, so NONE of them is
body-serializable: all seven stay on the profile path. Catches a `qftOnly` that ignores the
multiplier, which would start emitting a body beside (or instead of) a qualified label. -/
#guard (FullRunDesign.qualified.filter fun p => p.1.body?.isSome).length == 1
#guard FullRunDesign.reference.body?.isSome

/-! The QFT backend axis on the reference topology does serialize. Catches a `qftOnly` that is
`false` everywhere, which would refuse the whole working path. -/
#guard (({ data := some apxCatalytic, work := some exactDirect } : FullRunDesign)).body?.isSome
#guard (({ data := some ⟨.catalytic, .exact⟩ } : FullRunDesign)).body?.isSome

/-! ## 10. `profile` and `design` are alternatives, exactly one

`full_run_design.design_of` refuses a selection naming both (`profile-and-design`) and a
selection naming neither. `PolicyMain` chooses on `label?` first, so the obligation here is that
every body-serializable design is either unlabelled or is `reference` -- and `reference` is
suppressed by `compiledSelection?` before either key is written. Catches a new bundle being
added with the reference topology, which would make a label and a body both available.
-/
#guard FullRunDesign.qualified.all fun p => p.1.body?.isNone || p.1 == FullRunDesign.reference
#guard FullRunDesign.reference.compiledSelection?.isNone

/-! The `reference` body is well formed but unreachable: `compiledSelection?` is `none`, so the
default emits no key at all rather than this empty-`qft` object. Pinned so that a port which
makes `compiledSelection?` total is visibly emitting THIS. -/
#guard (FullRunDesign.json FullRunDesign.reference).compress
  == "{\"qft\":{},\"schema\":\"forshor.design-local/v1\"}"

end Shor
