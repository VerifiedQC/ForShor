import Lake
open Lake DSL

package «ForShor» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here
  -- This project's files are ordinary (non-`module`) Lean files. Mathlib is built for the
  -- module system, and without this Lake warns on every file that imports it.
  allowNonModules := true

-- Pinned. `lake-manifest.json` records the same revision, but without `@ rev`
-- a `lake update` silently jumps to Mathlib master. This rev matches
-- `lean-toolchain` (v4.36.0-rc1) and is the one `lake exe cache get` fetches.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "4dc43842a11f257ffba2a611c943a133a65cb4b2"

@[default_target]
lean_lib «ForShor» where
  -- add any library configuration options here

lean_exe forshor_emit where
  root := `ForShor.Emit.Main

lean_lib «EmitTests» where
  roots := #[`ForShor.Emit.Tests]

-- Building this library *is* the acceptance check for a submitted table.
-- `Submission/Template.lean` is the submitter's file: the table plus the
-- proofs of its four side conditions. `Submission/Check.lean` is the root
-- here, and is repo-owned: it audits `setup`'s axioms (so the side
-- conditions really did go through the kernel and not through
-- `native_decide`), extracts the IR, and pins that IR against the real
-- circuit at the sampled widths. A submissions repo's whole CI is
--   lake build Submission && lake exe forshor_submission > ir.json
-- see Submission/README.md.
lean_lib «Submission» where
  roots := #[`ForShor.ShorVerification.Submission.Check]

lean_exe forshor_submission where
  root := `ForShor.ShorVerification.Submission.Main

-- The same thing for a *policy* submission: a width-indexed list of tables
-- rather than one table. `Submission/PolicyTemplate.lean` is the submitter's
-- file, `Submission/PolicyCheck.lean` is the repo-owned root and is the
-- check. It audits the policy's axioms and kernel-checks C1-C4 per band plus
-- the thresholds' strict decrease, extracts the per-band IR and checks it is
-- well formed; the executable then runs the evaluation tier against the real
-- circuit at sampled widths and prints only if it passes. A policy
-- submissions repo's CI is
--   lake build PolicySubmission && lake exe forshor_policy_submission > policy.json
-- see Submission/README.md.
lean_lib «PolicySubmission» where
  roots := #[`ForShor.ShorVerification.Submission.PolicyCheck]

lean_exe forshor_policy_submission where
  root := `ForShor.ShorVerification.Submission.PolicyMain
  -- drop-in: the IR is extracted at run time (MetaM over the imported environment)
  supportInterpreter := true

-- The PhaseTripleProduct counterpart of the policy submission above. `Submission/PTPPolicyTemplate.lean` is the
-- submitter's file (a `Shor.PTP.PTPPolicy`), `Submission/PTPPolicyCheck.lean` is the repo-owned root and is the
-- check (the table contract, the strict decrease of the thresholds and the exact-width threshold rule by
-- `decide +kernel`, then the axiom audit); the executable prints the policy's document only if both hold. A
-- PhaseTripleProduct submissions repo's CI is
--   lake build PTPPolicySubmission forshor_ptp_policy_submission && lake exe forshor_ptp_policy_submission > policy.json
lean_lib «PTPPolicySubmission» where
  roots := #[`ForShor.ShorVerification.Submission.PTPPolicyCheck]

lean_exe forshor_ptp_policy_submission where
  root := `ForShor.ShorVerification.Submission.PTPPolicyMain

-- The unconditionally balanced IR (Emit/BalancedU/): the `--balanced` path of
-- forshor_policy_submission for `Shor.Balanced.balanceU`, which splits every site.
lean_exe forshor_balanced_u where
  root := `ForShor.Emit.BalancedU.Main
  supportInterpreter := true

-- Worked examples on the *shipped* policy template: `choose` at particular
-- widths, the advisory shrink check firing. Kept out of `PolicySubmission`
-- on purpose, since that library's build is the acceptance check and must
-- hold for any admissible policy, not only the shipped one.
lean_lib «PolicyTests» where
  roots := #[`ForShor.ShorVerification.Submission.PolicyTests]

-- Kernel-evaluated order-finding peaks of the sister-repository policies under the `exact` width rule.
-- Each module peaks at 9-12 GB, so they are NOT in the `ForShor` umbrella: they form an import chain (one
-- heavy evaluation at a time) and CI builds this library in a step of its own.
lean_lib «PolicyNumeralsExact» where
  roots := #[`ForShor.ShorVerification.Implementation.QubitCount.Proofs.PolicyNumeralsExact]

-- Same for the PhaseProduct board policies: the five rows whose exact-rule numerals fit a CI runner
-- (at most about 12 GB, about 3 minutes). Another chain, built in its own CI step after `PolicyNumeralsExact`; its first
-- module imports the last of that chain, so all exact evaluations are one serial order whatever is built.
lean_lib «PolicyNumeralsBoardExact» where
  roots := #[`ForShor.ShorVerification.Implementation.QubitCount.Proofs.PolicyNumeralsBoardExact]

-- The four rows that need 13-15 GB (the top 8-way policy among them): kernel-checked locally, NOT built in CI.
-- `lake build PolicyNumeralsBoardExactHeavy` on a machine with 16 GB or more of free memory (it builds the light chain first).
lean_lib «PolicyNumeralsBoardExactHeavy» where
  roots := #[`ForShor.ShorVerification.Implementation.QubitCount.Proofs.PolicyNumeralsBoardExactHeavy]

-- Drop-in: exact-width worked instances and fault challenge (not part of PolicySubmission).
lean_lib «ExactWidthTests» where
  roots := #[`ForShor.ShorVerification.Submission.ExactWidthTests]

-- Merged from the balanced-split work (ForShor-split): balanced phase products for unequal
-- operands, new leaf modules only (Implementation/Reference/Balanced/). The roots are its
-- three leaves, which import the rest. `forshor_policy_submission --balanced` emits the
-- balanced IR.
lean_lib «Balanced» where
  roots := #[`ForShor.ShorVerification.Implementation.Reference.Balanced.Main,
    `ForShor.ShorVerification.Implementation.Reference.Balanced.Proofs.Fault,
    `ForShor.ShorVerification.Implementation.Reference.Balanced.Proofs.Checks]
