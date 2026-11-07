import ForShor.ShorVerification.Submission.Policies.Common
import ForShor.ShorVerification.Submission.Policies.FaultyPointOrder
import ForShor.ShorVerification.Submission.Policies.FaultyWidth
import ForShor.ShorVerification.Submission.Policies.K5Sixband2048
import ForShor.ShorVerification.Submission.Policies.RefPp2048
import ForShor.ShorVerification.Submission.Policies.RefPtp2048
import ForShor.ShorVerification.Submission.Policies.ThresholdDeclaredPp
import ForShor.ShorVerification.Submission.Policies.ThresholdDegeneratePp
import ForShor.ShorVerification.Submission.Policies.ThresholdDegeneratePtp
import ForShor.ShorVerification.Submission.Policies.ThresholdNoshrinkPp
import ForShor.ShorVerification.Submission.Policies.ThresholdNoshrinkPtp
import ForShor.ShorVerification.Submission.Policies.ThresholdScanonlyPp
import ForShor.ShorVerification.Submission.Policies.ThresholdScanonlyPtp

/-!
# The twelve sister-repository policies, as Lean

Root of a library that builds all of `Submission/Policies/`. Each module is one `policies/*.json`
(generated from the sister repository's JSON); see `Common.lean` for the checks they share. The negative controls
(`FaultyPointOrder`, `FaultyWidth`, `Threshold{Declared,Degenerate,Noshrink}{Pp,Ptp}`) build
*because* their rejection is a proved theorem (`... = false` or `¬ ...`), not because they are accepted.
-/
