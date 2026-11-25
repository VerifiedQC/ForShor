import ForShor.ShorVerification.Submission.PolicyTemplate
import ForShor.ShorVerification.Submission.PolicyDecide
import ForShor.ShorVerification.Submission.PolicyMain
import ForShor.ShorVerification.Framework.Gatecount.PolicyModel

/-!
# Worked examples on the shipped policy

These are statements about the example policy that `PolicyTemplate.lean`
ships with, not about policies in general. They document how `choose`
routes a width to a band and show that the advisory shrink check can fire.
They live here, in `lean_lib PolicyTests`, and not in `PolicyCheck.lean`,
because `lean_lib PolicySubmission` is the acceptance check: anything in its
root that names the shipped bands or thresholds would reject every other
admissible policy. CI builds this library against the shipped template.
-/

namespace PolicySubmission

open Shor Operations

/-! The bands written in the template are the bands the policy carries, so
the policy `PolicyMain.lean` prints and the policy C1–C4 were proved about
are the same policy. `rfl`, because `policy` is built from them. -/

example : policy.bands = [(40, band0), (14, band1)] := rfl
example : band0.k = band0K := rfl
example : band0.ops = band0Ops := rfl
example : band1.k = band1K := rfl
example : band1.ops = band1Ops := rfl

/-! ## What the shipped policy chooses

One width per band, and one below the last threshold where the schoolbook
leaf takes over. These reduce by `rfl`: `choose` is a `List.find?` over a
literal band list. -/

example : policy.policy.choose 100 = some band0.table := rfl
example : policy.policy.choose 40 = some band0.table := rfl
example : policy.policy.choose 39 = some band1.table := rfl
example : policy.policy.choose 14 = some band1.table := rfl
example : policy.policy.choose 13 = none := rfl

/-! ## The advisory shrink check

Not an admissibility condition (see `PolicyDecide.lean`): a band whose table
does not shrink the width on its own range is dead weight, not unsound.
`PolicyMain` reports it per band (`"shrinks"` in `policy.json`). -/

/-- The check has teeth: dropping band 1's threshold to `12` is still a
perfectly admissible policy, but `bandShrinks` reports it as dead weight,
because this `k = 2` table maps `12 ↦ 12` and `13 ↦ 13` and so declines to
recurse at the bottom two widths of its own band. This is the warning a
submitter is meant to act on by raising the threshold. -/
example :
    _root_.Shor.Policy.bandShrinks
      { bands := [(40, band0), (12, band1)], sorted := by decide : ShorPolicySubmission }.policy 1
      = false := by decide +kernel

/-! ## The negation option

A policy chooses how a negation is built and priced, `oneQubit` unless it says `scratch`
(`ShorPolicySubmission.negation`). It is not an admissibility condition, so a policy that sets it is
accepted exactly as one that does not, and the document it prints (`negationFields`) names the method and
reports its charge. The charges are `Framework/Gatecount/ResourceModel.lean`'s, evaluated by the kernel. -/

/-- The shipped bands, with the field left out, so that it takes its default. -/
def policyNoField : ShorPolicySubmission := { bands := policy.bands, sorted := policy.sorted }

example : Shor.SubmissionDesign.resolved.readout = .coherent := rfl

/-! The pre-opt-in source API accepts positional construction, the original
constructor type, and destructuring as well as named records. -/

private def policyPositional : ShorPolicySubmission :=
  ⟨policy.bands, policy.sorted, policy.widthRule, policy.negation⟩

private def legacyConstructor :
    (bands : List (ℕ × ShorLoweringSetup)) → (bands.map Prod.fst).IsChain (· > ·) →
    WidthRule → NegationMethod → ShorPolicySubmission := @ShorPolicySubmission.mk

private def legacyWidthRule : ShorPolicySubmission → WidthRule
  | ⟨_, _, rule, _⟩ => rule

example : policyPositional.policy = policy.policy := rfl
example : (legacyConstructor policy.bands policy.sorted policy.widthRule policy.negation).policy =
    policy.policy := rfl
example : legacyWidthRule policyPositional = policy.widthRule := rfl

/-- The shipped bands on the scratch method. -/
def policyScratch : ShorPolicySubmission := { policy with negation := .scratch }

example : policyNoField.negation = .oneQubit := rfl
example : policyScratch.negation = .scratch := rfl
-- the shipped template names the default explicitly
example : policy.negation = .oneQubit := rfl

-- the option changes neither the bands nor what `choose` routes to
example : policyScratch.bands = policy.bands := rfl
example : policyScratch.policy.choose 100 = some band0.table := rfl
example : policyScratch.policy.choose 14 = some band1.table := rfl

-- the scratch policy is admissible, and the generic certificate applies to it exactly as to the default
example : policyScratch.policy.Admissible := ShorPolicySubmission.policy_admissible _
example : policyNoField.policy.Admissible := ShorPolicySubmission.policy_admissible _

theorem correct_scratch {qs : QSemantics} [RegEncoding qs.Basis] [MeasureClass qs]
    [GateSemanticsFacts qs] [LowerGateClass qs] :
    type_of% (_root_.Shor.policy_submission_correct (qs := qs) policyScratch) :=
  _root_.Shor.policy_submission_correct (qs := qs) policyScratch

#assert_axioms _root_.PolicySubmission.policyScratch

-- the policy is priced under the method it names
example : policyScratch.policy.resourceModel = shorGateResourceModelFor .scratch := rfl
example : policyNoField.policy.resourceModel = shorGateResourceModel := rfl

-- the charge each reports, at the benchmark width: scratch `3w-4, 5w-7, 2w-3, w+1`, default `5w-3, 17w-22, 12w-28, 1`
example : negateChargeAt policyScratch.negation 2048 =
    { x := 6140, cnot := 10233, toffoli := 4093, cleanAnc := 2049 } := by decide +kernel
example : negateChargeAt policyNoField.negation 2048 =
    { x := 10237, cnot := 34794, toffoli := 24548, cleanAnc := 1 } := by decide +kernel
example : negateChargeAt policyScratch.negation 2048 ≠ negateChargeAt policyNoField.negation 2048 := by
  decide +kernel

-- The printed fields: a policy without the option reports `oneQubit` and its charge, one with
-- `negation := .scratch` reports `scratch` and the scratch charge.
#eval show IO Unit from do
  let get (j : Lean.Json) (k : String) : String :=
    match j.getObjVal? k with | .ok v => v.compress | .error _ => "<missing>"
  let fields (s : ShorPolicySubmission) : Lean.Json := Lean.Json.mkObj (negationFields s)
  let one := fields policyNoField
  let scr := fields policyScratch
  unless get one "negation" == "\"oneQubit\"" do throw (IO.userError "default policy does not report oneQubit")
  unless get scr "negation" == "\"scratch\"" do throw (IO.userError "scratch policy does not report scratch")
  unless get one "negate_charge" == (_root_.Shor.negateChargeJson .oneQubit).compress do
    throw (IO.userError "default policy reports the wrong charge")
  unless get scr "negate_charge" == (_root_.Shor.negateChargeJson .scratch).compress do
    throw (IO.userError "scratch policy reports the wrong charge")
  unless get one "negate_charge" != get scr "negate_charge" do
    throw (IO.userError "the two methods report the same charge")
  IO.println s!"policy negation fields: default {get one "negation"}, scratch {get scr "negation"}"

end PolicySubmission

namespace Shor.SubmissionDesignTests

def explicitCoherent : SubmissionDesign := { readout := .coherent }
def explicitMeasured : SubmissionDesign := { readout := .semiclassical }

private def omitted : SubmissionDesign := by_elab
  SubmissionDesign.resolveDeclaration `Shor.SubmissionDesignTests.absent

private def coherent : SubmissionDesign := by_elab
  SubmissionDesign.resolveDeclaration `Shor.SubmissionDesignTests.explicitCoherent

private def measured : SubmissionDesign := by_elab
  SubmissionDesign.resolveDeclaration `Shor.SubmissionDesignTests.explicitMeasured

example : omitted = coherent := rfl
example : measured.readout = .semiclassical := rfl

def wrongType : Nat := 1

/-- error: optional declaration 'Shor.SubmissionDesignTests.wrongType' must have type Shor.SubmissionDesign -/
#guard_msgs in
example : SubmissionDesign := by_elab
  SubmissionDesign.resolveDeclaration `Shor.SubmissionDesignTests.wrongType

private def hidden : SubmissionDesign := explicitMeasured

/-- error: optional declaration 'Shor.SubmissionDesignTests.hidden' must be public; remove 'private' to opt in -/
#guard_msgs in
example : SubmissionDesign := by_elab
  SubmissionDesign.resolveDeclaration `Shor.SubmissionDesignTests.hidden

axiom unchecked : SubmissionDesign

noncomputable def uncheckedDesign : SubmissionDesign := by_elab
  SubmissionDesign.resolveDeclaration `Shor.SubmissionDesignTests.unchecked

/--
error: 'Shor.SubmissionDesignTests.uncheckedDesign' is not kernel-checked. Axioms outside the allowlist (propext, Classical.choice, Quot.sound):
  Shor.SubmissionDesignTests.unchecked  -- declared by the submission
-/
#guard_msgs in
#assert_axioms _root_.Shor.SubmissionDesignTests.uncheckedDesign

end Shor.SubmissionDesignTests

/-! ## The other optional declarations, and the opt-in combinations

The same resolver (`Shor.resolveOptional`) reads `submittedPrimitive` and
`submittedFullRunDesign`, so each is pinned here the way `submittedDesign` is above: absent
chooses the default, a declared value is read, and a private, wrongly typed or unchecked one is an
error. `optInRefusal` and `attestFullRun` are pure, so every refusal and every printed shape is
pinned without building a second policy. -/

namespace Shor.OptInTests

def explicitB2 : PrimitiveSynthesis := .catalyticB2
def explicitFullRun : FullRunDesign := FullRunDesign.quotientExact

private def noPrimitive : PrimitiveSynthesis := by_elab
  resolveOptional ``Shor.PrimitiveSynthesis ``Shor.PrimitiveSynthesis.rossSelinger
    `Shor.OptInTests.absent

private def b2 : PrimitiveSynthesis := by_elab
  resolveOptional ``Shor.PrimitiveSynthesis ``Shor.PrimitiveSynthesis.rossSelinger
    `Shor.OptInTests.explicitB2

example : noPrimitive = .rossSelinger := rfl
example : b2 = .catalyticB2 := rfl

private def noFullRun : FullRunDesign := by_elab
  resolveOptional ``Shor.FullRunDesign ``Shor.FullRunDesign.reference `Shor.OptInTests.absent

private def someFullRun : FullRunDesign := by_elab
  resolveOptional ``Shor.FullRunDesign ``Shor.FullRunDesign.reference `Shor.OptInTests.explicitFullRun

#guard noFullRun == FullRunDesign.reference
#guard someFullRun == FullRunDesign.quotientExact

def wrongType : Nat := 1

/-- error: optional declaration 'Shor.OptInTests.wrongType' must have type Shor.PrimitiveSynthesis -/
#guard_msgs in
example : PrimitiveSynthesis := by_elab
  resolveOptional ``Shor.PrimitiveSynthesis ``Shor.PrimitiveSynthesis.rossSelinger `Shor.OptInTests.wrongType

/-- error: optional declaration 'Shor.OptInTests.wrongType' must have type Shor.FullRunDesign -/
#guard_msgs in
example : FullRunDesign := by_elab
  resolveOptional ``Shor.FullRunDesign ``Shor.FullRunDesign.reference `Shor.OptInTests.wrongType

private def hiddenB2 : PrimitiveSynthesis := .catalyticB2
private def hiddenFullRun : FullRunDesign := FullRunDesign.quotientExact

/-- error: optional declaration 'Shor.OptInTests.hiddenB2' must be public; remove 'private' to opt in -/
#guard_msgs in
example : PrimitiveSynthesis := by_elab
  resolveOptional ``Shor.PrimitiveSynthesis ``Shor.PrimitiveSynthesis.rossSelinger `Shor.OptInTests.hiddenB2

/-- error: optional declaration 'Shor.OptInTests.hiddenFullRun' must be public; remove 'private' to opt in -/
#guard_msgs in
example : FullRunDesign := by_elab
  resolveOptional ``Shor.FullRunDesign ``Shor.FullRunDesign.reference `Shor.OptInTests.hiddenFullRun

axiom uncheckedFullRun : FullRunDesign

noncomputable def uncheckedFullRunDesign : FullRunDesign := by_elab
  resolveOptional ``Shor.FullRunDesign ``Shor.FullRunDesign.reference `Shor.OptInTests.uncheckedFullRun

/--
error: 'Shor.OptInTests.uncheckedFullRunDesign' is not kernel-checked. Axioms outside the allowlist (propext, Classical.choice, Quot.sound):
  Shor.OptInTests.uncheckedFullRun  -- declared by the submission
-/
#guard_msgs in
#assert_axioms _root_.Shor.OptInTests.uncheckedFullRunDesign

/-! `refuseOptional` is what keeps full-run synthesis off the PhaseTripleProduct board: it fails for
a public or a private declaration and is silent for an absent one. -/

def declared : Nat := 1
private def declaredPrivately : Nat := 1

run_cmd (refuseOptional `Shor.OptInTests.neverDeclared
  `ForShor.ShorVerification.Submission.PolicyTests "refused")

/-- error: refused -/
#guard_msgs in
run_cmd (refuseOptional `Shor.OptInTests.declared
  `ForShor.ShorVerification.Submission.PolicyTests "refused")

/-- error: refused -/
#guard_msgs in
run_cmd (refuseOptional `Shor.OptInTests.declaredPrivately
  `ForShor.ShorVerification.Submission.PolicyTests "refused")

/-! ### `optInRefusal`: every refusal, and the combinations that pass -/

-- args: fullRun primitive submitted balanced exact widthTable
#guard (optInRefusal .reference .rossSelinger false false false false).isNone
#guard (optInRefusal FullRunDesign.quotientExact .rossSelinger true true true false).isNone
#guard (optInRefusal FullRunDesign.quotientExact .rossSelinger false true true false).isSome
#guard (optInRefusal FullRunDesign.quotientExact .rossSelinger true false true false).isSome
#guard (optInRefusal FullRunDesign.quotientExact .rossSelinger true true true true).isSome
#guard (optInRefusal .reference .catalyticB2 false true true false).isNone
#guard (optInRefusal .reference .catalyticB2 false false false false).isSome
#guard (optInRefusal .reference .adaptiveB3 false true true true).isSome

/-! ### `attestFullRun`: the three printed shapes -/

private def base : Lean.Json := Lean.Json.mkObj [("schema", Lean.Json.str "base")]

-- `reference` is no design at all: the document is unchanged, no key.
#guard (attestFullRun .reference base).compress == base.compress
-- a qualified selection names its profile, and carries no design body
#guard (attestFullRun FullRunDesign.quotientExact base).compress
  == "{\"schema\":\"base\",\"submitted_full_run\":{\"profile\":\"quotient-exact\","
     ++ "\"schema\":\"forshor.full-run-selection/v1\"}}"
-- an unqualified, body-serializable selection carries its design, and no profile
#guard (attestFullRun { data := some ⟨.catalytic, .exact⟩ } base).compress
  == "{\"schema\":\"base\",\"submitted_full_run\":{\"design\":{\"qft\":{\"data\":"
     ++ "{\"backend\":\"catalytic\",\"target\":\"exact\"}},\"schema\":\"forshor.design-local/v1\"},"
     ++ "\"schema\":\"forshor.full-run-selection/v1\"}}"
-- an unattestable selection adds nothing; `PolicyCheck.fullRun_attestable` refuses it at build time
#guard (attestFullRun { step1 := some .fallback } base).compress == base.compress

end Shor.OptInTests
