import FastMultiplication.ShorVerification.Implementation.Reference.StandardLoweringSetup
import FastMultiplication.ShorVerification.Implementation.Reference.ReferenceShorImplementation
import FastMultiplication.ShorVerification.Implementation.Reference.ReferenceLayout
import FastMultiplication.Emit.Json.LowGateJson

/-!
# `shor` subcommand: the reference lowered Shor circuit

Prints the reference lowered Shor circuit for `(k, a, N, m)` as JSON on
stdout (`Shor.emitProgram`'s `forshor.lowgate/v2` schema), plus a `layout`
block (`allocateReferenceLayout`'s four registers and flag qubit). This is
the existing `referenceProgramAt` path (moved here from the old `Main.lean`,
which is now dispatch-only, per `Emit/README.md`'s Phase 0).

`--annotated`'s `Gate`-tree-of-`orderFindingApprox` view (README, Phase 2) is
not implemented here: it needs the raw pre-lowering `Gate` tree, which
`referenceProgramAt` does not expose separately from its already-lowered
`LowGate` result, and re-deriving it (plus a per-leaf workspace-discharge
walk over `Gate.QFT`/`(C)SignedPhaseProd`/`CmpGeConst`/`CSubConst`, the last
two needing a new `ConstArithmeticWorkspace` `Decidable` instance) is its own
research-and-implementation arc beyond what `pp`/`cpp`/`qft` already cover.
-/

namespace Shor.Reference

open Lean (Json)

def layoutJson (layout : ReferenceShorLayout) : Json :=
  Json.mkObj [
    ("x", extRegJson layout.x),
    ("data", extRegJson layout.data),
    ("work", extRegJson layout.work),
    ("scratch", extRegJson layout.scratch),
    ("flag", (layout.flag : Json))
  ]

end Shor.Reference

namespace Emit.Lower.Shor

def runEmit (k a N m : ℕ) : IO UInt32 := do
  if hk : 1 < k then
    if hrange : 0 < a ∧ a < N then
      if hcop : Nat.gcd a N = 1 then
        let lowering := Shor.standardLoweringSetup k hk
        let inst : Shor.ShorOrderFindingInstance := ⟨a, N, hrange, hcop⟩
        let prog := Shor.Reference.referenceProgramAt lowering m inst
        let layout := Shor.Reference.allocateReferenceLayout lowering.ops inst m
        let metaJson : Lean.Json :=
          Lean.Json.mkObj [
            ("k", (k : Lean.Json)),
            ("a", (a : Lean.Json)),
            ("N", (N : Lean.Json)),
            ("m", (m : Lean.Json)),
            ("source", Lean.Json.str "Shor.Reference.referenceProgramAt"),
            ("layout", Shor.Reference.layoutJson layout)
          ]
        IO.println (Shor.emitProgram prog metaJson).compress
        return 0
      else
        IO.eprintln s!"error: need gcd a N = 1 (a = {a}, N = {N})"
        return 2
    else
      IO.eprintln s!"error: need 0 < a < N (a = {a}, N = {N})"
      return 2
  else
    IO.eprintln s!"error: need k > 1 (k = {k})"
    return 2

end Emit.Lower.Shor
