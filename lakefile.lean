import Lake
open Lake DSL

package «Fast_multiplication» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «FastMultiplication» where
  -- add any library configuration options here

lean_exe forshor_emit where
  root := `FastMultiplication.Emit.Main

lean_lib «EmitTests» where
  roots := #[`FastMultiplication.Emit.Tests]

-- `SUBMISSION_PLAN.md` S4.1. Building this library *is* the acceptance check:
-- the template's four side conditions go through the kernel and its
-- `native_decide` lines pin the IR against the real circuit at the sampled
-- widths. A submissions repo's whole CI is
--   lake build Submission && lake exe forshor_submission > ir.json
lean_lib «Submission» where
  roots := #[`FastMultiplication.ShorVerification.Submission.Template]

lean_exe forshor_submission where
  root := `FastMultiplication.ShorVerification.Submission.Main
