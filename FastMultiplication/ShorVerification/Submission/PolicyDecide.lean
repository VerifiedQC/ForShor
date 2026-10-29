import FastMultiplication.ShorVerification.Framework.Policy
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Workspace

/-!
# An advisory check a policy submitter can run

Nothing here is an admissibility condition. A policy is admissible when every
band's table satisfies C1–C4 and the thresholds strictly decrease — that is
all `Submission/PolicyCheck.lean` requires, and all
`Shor.policy_submission_correct` needs.

What this file adds is a *performance* check, because the one thing a policy
can get wrong without being unsound is to include a band whose table never
actually recurses on the widths that band covers. The recursion falls back to
the schoolbook leaf whenever the chosen table does not shrink the operand
width (`ShorLoweringPolicy.Stops`), so such a band is simply dead weight: it
is selected, it declines to recurse, and the leaf runs instead. The policy is
still correct; it is just paying for a band that does nothing.

`bandShrinks` scans the finite width range a band covers and reports whether
the band's table shrinks at every width in it. `false` is a warning, not a
failure.

Unlike `PolicyTemplate.lean`, this file imports `Implementation/`
(`nextWidth` lives there), so a submitter who wants to iterate on thresholds
without building the construction can use the template alone and run this
check only at the end.
-/

namespace Shor.Policy

open ShorLoweringPolicy

/-- The half-open width range band `i` covers: `[tᵢ, tᵢ₋₁)`, and for the top
band (`i = 0`) just the single width `t₀`, since there is no upper threshold
and the widths above it are unbounded. -/
def bandWidths (P : ShorLoweringPolicy) (i : ℕ) : List ℕ :=
  match P.bands[i]? with
  | none => []
  | some b =>
      match P.bands[i - 1]? with
      | none => [b.threshold]                              -- the top band
      | some prev =>
          if i = 0 then [b.threshold]
          else (List.range (prev.threshold - b.threshold)).map (fun j => b.threshold + j)

/-- Does band `i`'s table shrink the operand width at every width that band
covers?

`true` means the band earns its place. `false` means that at some width in
its range the recursion falls through to the schoolbook leaf, so the band is
dead weight there — a performance warning, never an admissibility failure.
The child width is the policy's own (`P.widthRule`). -/
def bandShrinks (P : ShorLoweringPolicy) (i : ℕ) : Bool :=
  match P.bands[i]? with
  | none => false
  | some b =>
      (bandWidths P i).all fun n =>
        decide (RecursivePhaseWorkspace.nextWidthBy P.widthRule b.table.ops n n < n)

end Shor.Policy
