import Lake
open Lake DSL

package «ForShor» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

-- Pinned. `lake-manifest.json` records the same revision, but without `@ rev`
-- a `lake update` silently jumps to Mathlib master. This rev matches
-- `lean-toolchain` (v4.28.0) and is the one `lake exe cache get` fetches.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "fadcf92bfcfe7575bbdf04c6f83ab3ada53e3d42"

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
-- plus `lean4checker` on the built `.olean`s; see Submission/README.md.
lean_lib «Submission» where
  roots := #[`FastMultiplication.ShorVerification.Submission.Check]

lean_exe forshor_submission where
  root := `FastMultiplication.ShorVerification.Submission.Main
