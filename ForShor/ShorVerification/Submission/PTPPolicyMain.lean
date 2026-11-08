import ForShor.ShorVerification.Submission.PTPPolicyCheck
import ForShor.Emit.Json.Common

/-!
# `forshor_ptp_policy_submission`: the printed document of a PhaseTripleProduct policy

The executable of [`PTPPolicyCheck.lean`](PTPPolicyCheck.lean), as `forshor_policy_submission` is of
[`PolicyCheck.lean`](PolicyCheck.lean). It runs after `lake build PTPPolicySubmission`, which has already
kernel-checked the table contract, the strict decrease of the thresholds and the exact-width threshold rule
(`PTPPolicySubmission.check`, `PTPPolicySubmission.chain_exact`) and audited their axioms, so an executable that
exists is the executable of an accepted policy. It does not evaluate them again: at a `k = 8` band the compiled
evaluation of the exact-width recursion takes many minutes where the kernel takes seconds. It prints the document:

```
lake build PTPPolicySubmission forshor_ptp_policy_submission
lake exe forshor_ptp_policy_submission > policy.json
```

The bands are printed in the spelling `forshor_policy_submission` uses for a PhaseProduct policy (`threshold`, `k`,
`points`, `ops`), so one reader serves both. Unlike the PhaseProduct document there is no IR here: a PhaseTripleProduct
policy has no ForShor emitter, and the boards price it with the Qualtran leaf of the results engine. The exact-width
ladder and the peak qubit count are not printed: the boards' engine and the mirror's kernel certificate compute and
prove them, and a number evaluated here would only be a third, slower copy.

Exit status: 0 printed.
-/

open Lean (Json)
open Shor

namespace PTPPolicySubmission

/-- One band, in the PhaseProduct document's spelling. -/
def bandJson (i : ℕ) (b : _root_.Shor.PTP.PTPBand) : Json :=
  Json.mkObj [
    ("index", (i : Json)),
    ("threshold", (b.threshold : Json)),
    ("k", (b.table.k : Json)),
    ("points", Json.arr (b.table.pts.map _root_.Shor.pointJson).toArray),
    ("ops", _root_.Shor.progJson b.table.ops)]

/-- The printed document. -/
def policyDoc (P : _root_.Shor.PTP.PTPPolicy) : Json :=
  Json.mkObj [
    ("schema", Json.str "forshor.ptp-policy-submission/v1"),
    ("negation", _root_.Shor.negationMethodJson P.negation),
    ("bands", Json.arr (P.bands.zipIdx.map (fun p => bandJson p.2 p.1)).toArray),
    ("benchmark", Json.mkObj [("bits", (2048 : Json))]),
    ("checks", Json.mkObj [
      ("check", Json.str "kernel-checked at build time (PTPPolicySubmission.check): thresholds strictly decrease and every table passes the PTP contract"),
      ("threshold_rule", Json.str "kernel-checked at build time (PTPPolicySubmission.chain_exact): the exact-width threshold rule from 2048"),
      ("axioms", Json.str "propext, Classical.choice, Quot.sound only (#assert_axioms)"),
      ("not_proved", Json.str "the T count and the qubit count are counted by the boards' engine and are not proved in Lean (the correctness, the threshold rule and the peak bound are theorems at this policy)")])]

end PTPPolicySubmission

def main : IO UInt32 := do
  IO.println (_root_.PTPPolicySubmission.policyDoc _root_.PTPPolicySubmission.policy).pretty
  return 0
