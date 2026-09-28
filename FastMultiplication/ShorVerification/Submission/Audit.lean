import Lean

/-!
# `#assert_axioms`: the build fails unless a declaration is kernel-checked

"Kernel-checked" is a claim about a *declaration*, not about the tactic that
wrote it. Lean records the difference in the axioms a term depends on, and
there is exactly one way to read it off: `Lean.collectAxioms`, the same
traversal `#print axioms` uses.

`#assert_axioms c` fails the build unless `c`'s axiom dependencies lie inside

    propext, Classical.choice, Quot.sound

— the three Lean itself is founded on. That is a *subset* test, not an exact
match: what a submission needs is often fewer than all three. A table closed
by `decide +kernel` alone depends on no axioms at all; the shipped one
depends on all three, because C2 goes through Mathlib's Vandermonde
determinant.

What it catches:

* `native_decide` — `Lean.ofReduceBool` and `Lean.trustCompiler`. This is the
  one the repository shipped with and the reason this file exists: a
  `native_decide` proof is checked by the compiled evaluator, not by the
  kernel, so a submission closed that way is not kernel-checked whatever the
  documentation says.
* `sorry`, and any tactic that failed and was admitted — `sorryAx`.
* Any `axiom` the submitter declares, by name.

What it does *not* catch: `set_option debug.skipKernelTC true`, which skips
the kernel without adding an axiom. Nothing visible in the environment does;
that is what replaying the built `.olean`s through `lean4checker` is for, and
why `Submission/README.md` asks a submissions repo to run it.
-/

namespace Shor.Audit

open Lean Elab Command

/-- The axioms a kernel-checked declaration may depend on. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Why a disallowed axiom is there, when the name alone does not say. -/
def axiomNote (a : Name) : String :=
  if a == ``Lean.ofReduceBool || a == ``Lean.ofReduceNat || a == ``Lean.trustCompiler then
    "  -- `native_decide`: the compiled evaluator is trusted, the kernel is not run"
  else if a == ``sorryAx then
    "  -- `sorry`, or a tactic that failed and was admitted"
  else
    "  -- declared by the submission"

/-- The check itself, factored out of the elaborator so `#assert_axioms` can
run it over every constant an ambiguous identifier resolves to. -/
def assertAxiomsOf (constName : Name) : CommandElabM Unit := do
  let axs ← collectAxioms constName
  let bad := (axs.filter (fun a => !allowedAxioms.contains a)).qsort Name.lt
  if bad.isEmpty then
    logInfo m!"'{constName}' is kernel-checked; axioms: {(axs.qsort Name.lt).toList}"
  else
    throwError MessageData.joinSep
      (m!"'{constName}' is not kernel-checked. Axioms outside the allowlist \
          (propext, Classical.choice, Quot.sound):"
        :: bad.toList.map (fun a => m!"  {a}{axiomNote a}"))
      "\n"

/-- `#assert_axioms c` is an error unless every axiom `c` depends on is one
of `propext`, `Classical.choice`, `Quot.sound`. On success it reports the
axioms it did find, so a green build says which they were. -/
elab "#assert_axioms " id:ident : command => withRef id do
  let cs ← liftCoreM <| realizeGlobalConstWithInfos id
  cs.forM assertAxiomsOf

end Shor.Audit

/-! =========================================================
    Tests

    One declaration per rejection class, each with the message
    `#assert_axioms` is supposed to produce. `#guard_msgs` turns the
    expected failures into passes, so this file stays green while
    demonstrating that the command fails when it should — including the
    `sorry` warning, which is captured rather than emitted.

    `declared_bad` states something *true*: the point is that an `axiom` is
    rejected for being an axiom, not for what it says, and a shipped file
    has no business adding a false one to the environment.
========================================================= -/

namespace Shor.Audit.Test

theorem kernel_ok : (2 : Nat) + 2 = 4 := by decide +kernel

/-- info: 'Shor.Audit.Test.kernel_ok' is kernel-checked; axioms: [] -/
#guard_msgs in
#assert_axioms kernel_ok

theorem classical_ok : ∀ p : Prop, p ∨ ¬ p := Classical.em

/--
info: 'Shor.Audit.Test.classical_ok' is kernel-checked; axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#assert_axioms classical_ok

theorem native_bad : (2 : Nat) + 2 = 4 := by native_decide

/--
error: 'Shor.Audit.Test.native_bad' is not kernel-checked. Axioms outside the allowlist (propext, Classical.choice, Quot.sound):
  Lean.ofReduceBool  -- `native_decide`: the compiled evaluator is trusted, the kernel is not run
  Lean.trustCompiler  -- `native_decide`: the compiled evaluator is trusted, the kernel is not run
-/
#guard_msgs in
#assert_axioms native_bad

/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem sorry_bad : (2 : Nat) + 2 = 4 := by sorry

/--
error: 'Shor.Audit.Test.sorry_bad' is not kernel-checked. Axioms outside the allowlist (propext, Classical.choice, Quot.sound):
  sorryAx  -- `sorry`, or a tactic that failed and was admitted
-/
#guard_msgs in
#assert_axioms sorry_bad

axiom declared_bad : (2 : Nat) + 2 = 4

/--
error: 'Shor.Audit.Test.declared_bad' is not kernel-checked. Axioms outside the allowlist (propext, Classical.choice, Quot.sound):
  Shor.Audit.Test.declared_bad  -- declared by the submission
-/
#guard_msgs in
#assert_axioms declared_bad

end Shor.Audit.Test
