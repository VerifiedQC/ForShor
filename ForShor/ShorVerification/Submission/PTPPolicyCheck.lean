import ForShor.ShorVerification.Submission.PTPPolicyTemplate
import ForShor.ShorVerification.Submission.Audit
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Main

/-!
# The acceptance check for a PhaseTripleProduct policy submission

`lean_lib PTPPolicySubmission` is rooted here, so **building this file is the check**. Nothing in it is
edited by a submitter; everything it touches comes from
[`PTPPolicyTemplate.lean`](PTPPolicyTemplate.lean), the file a submitter owns. It is the
PhaseTripleProduct counterpart of [`PolicyCheck.lean`](PolicyCheck.lean).

## Kernel-checked, and audited

* `check`: the thresholds strictly decrease and every table passes the PTP table contract
  (`PTPPolicy.check`), reduced by the kernel (`decide +kernel`).
* `chain_exact`: the exact-width threshold rule from the benchmark width 2048
  (`PTPPolicy.chainContractsTight`): on the recursion the policy takes from 2048 at exact widths, every band
  applied at width `w` has `k ≤ w` and strictly shrinks the width. This is what the boards require of a
  submission.
* `#assert_axioms` reads the axioms the finished terms depend on and fails unless they lie inside
  `propext`, `Classical.choice`, `Quot.sound`, so `native_decide`, `sorry` and a submitter's own `axiom` are
  rejected by name (see [`Audit.lean`](Audit.lean)).

## Stated at this policy (generic theorems, nothing to prove here)

`correct_exact` (the exact board computes `φ · x₀ · x₁ · x₂` at every width), `thresholds_at_target` (the
threshold rule without the ladder) and `peak_exact` (a gate-level circuit following the policy has framework
qubit count at most `3 n + ptpWsTD + ptpCleanAncD`) are ForShor's theorems for any accepted `PTPPolicy`,
instantiated at this one. The T count itself is not proved here: the boards count it in Python (Qualtran).

Every repo-owned name below is written with `_root_.`, for the reason given in `Check.lean`: inside
`namespace PTPPolicySubmission` a partly qualified name resolves one namespace deeper first, where a submitter
could place a decoy.
-/

namespace PTPPolicySubmission

open Shor.Audit

/-- The benchmark width the threshold rule is checked from. -/
def target : ℕ := 2048

/-- Acceptance: thresholds strictly decrease and every table passes the PTP contract. -/
theorem check : _root_.PTPPolicySubmission.policy.check = true := by decide +kernel

/-- The exact-width threshold rule from 2048. -/
theorem chain_exact :
    _root_.PTPPolicySubmission.policy.chainContractsTight _root_.PTPPolicySubmission.target = true := by
  decide +kernel

#assert_axioms _root_.PTPPolicySubmission.policy
#assert_axioms _root_.PTPPolicySubmission.check
#assert_axioms _root_.PTPPolicySubmission.chain_exact

/-- The exact PTP board is correct at every width. -/
theorem correct_exact :
    type_of% (_root_.Shor.PTP.evalPhaseTight_correct _root_.PTPPolicySubmission.policy
      _root_.PTPPolicySubmission.check) :=
  _root_.Shor.PTP.evalPhaseTight_correct _root_.PTPPolicySubmission.policy _root_.PTPPolicySubmission.check

/-- The acceptance rule without the ladder: every table chosen at every width the exact recursion from 2048
reaches has `k ≤ width` and strictly shrinks it. -/
theorem thresholds_at_target :
    type_of% (_root_.Shor.PTP.ptp_chainContractsTight_iff_reach _root_.PTPPolicySubmission.policy
      _root_.PTPPolicySubmission.target) :=
  _root_.Shor.PTP.ptp_chainContractsTight_iff_reach _root_.PTPPolicySubmission.policy
    _root_.PTPPolicySubmission.target

/-- The single-product peak on the exact board, at this policy. -/
theorem peak_exact :
    type_of% (_root_.Shor.PTP.ptp_peak_qubits_exact _root_.PTPPolicySubmission.policy) :=
  _root_.Shor.PTP.ptp_peak_qubits_exact _root_.PTPPolicySubmission.policy

end PTPPolicySubmission
