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

lean_lib «EmitProofs» where
  roots := #[`FastMultiplication.Emit.Proofs.Shor]
