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
lean_lib «FastMultiplication» where
  -- add any library configuration options here

lean_exe forshor_emit where
  root := `FastMultiplication.Emit.Main

lean_lib «EmitTests» where
  roots := #[`FastMultiplication.Emit.Tests]

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
  roots := #[`FastMultiplication.ShorVerification.Submission.Check]

lean_exe forshor_submission where
  root := `FastMultiplication.ShorVerification.Submission.Main

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
  roots := #[`FastMultiplication.ShorVerification.Submission.PolicyCheck]

lean_exe forshor_policy_submission where
  root := `FastMultiplication.ShorVerification.Submission.PolicyMain
  -- drop-in: the IR is extracted at run time (MetaM over the imported environment)
  supportInterpreter := true

-- Worked examples on the *shipped* policy template: `choose` at particular
-- widths, the advisory shrink check firing. Kept out of `PolicySubmission`
-- on purpose, since that library's build is the acceptance check and must
-- hold for any admissible policy, not only the shipped one.
lean_lib «PolicyTests» where
  roots := #[`FastMultiplication.ShorVerification.Submission.PolicyTests]

-- Drop-in: exact-width worked instances and fault challenge (not part of PolicySubmission).
lean_lib «ExactWidthTests» where
  roots := #[`FastMultiplication.ShorVerification.Submission.ExactWidthTests]

-- Merged from the balanced-split work (ForShor-split): balanced phase products for unequal
-- operands, new leaf modules only (Implementation/Reference/Balanced/). The roots are its
-- three leaves, which import the rest. `forshor_policy_submission --balanced` emits the
-- balanced IR.
lean_lib «Balanced» where
  roots := #[`FastMultiplication.ShorVerification.Implementation.Reference.Balanced.Reference,
    `FastMultiplication.ShorVerification.Implementation.Reference.Balanced.Fault,
    `FastMultiplication.ShorVerification.Implementation.Reference.Balanced.Checks]
