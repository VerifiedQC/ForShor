import FastMultiplication.ShorVerification.Submission.PolicyTemplate
import FastMultiplication.ShorVerification.Submission.PolicyDecide

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

end PolicySubmission
