# `Proofs/Lowering/`

Correctness of the `Lowering/` plan machinery: that lowering a `PhaseLoweringPlan`
to a `LowGate` (via `lowerGateRec`) preserves semantics, given the plan is
"ready" (`PhaseLoweringReady`, `Spec/Readiness.lean`). Internal order: `EvalL`
→ `Lowerable` → `PlanSemantics` → `Linearity` → `Workspace` → `PlanReadiness/*`
→ `Correctness` (each may use anything from the ones before it).

The two results this folder's proofs ultimately exist to feed `Main.lean`:

- **`evalL_lowerGateRec_correct`** (`PlanSemantics.lean`) — the core
  interpreter theorem: for *any* `PhaseLoweringPlan` that is ready on a state
  `ψ` (and the source program satisfies the usual interpolation-safety side
  conditions), `LowerGateClass.evalL (lowerGateRec plan) ψ = qs.eval U ψ`,
  i.e. the lowered circuit evaluates exactly like the high-level gate `U` the
  plan certifies. Proved by structural induction on the plan.
- **`evalL_lowerSignedPhaseProd_of_plan`** (`Correctness.lean`) — the same
  fact repackaged for the *standard* uncontrolled plan specifically (fixing
  `U := Gate.SignedPhaseProd phi x z`); this is the lemma `Main.lean` calls
  directly for the uncontrolled headline theorem. (`Main.lean` calls
  `evalL_lowerGateRec_correct` itself for the controlled case, since no
  separate wrapper for it was needed.)

Getting to those two required: `EvalL.lean`'s simp lemmas for `evalL` on each
primitive; `Lowerable.lean` showing every gate the compiler emits is a valid
lowering target; `Linearity.lean` lifting basis-ket facts to arbitrary clean
states; `Workspace.lean` showing allocation produces a fitted, still-clean
target encoding; and the readiness proofs in `PlanReadiness/` (see its own
README) showing the *standard* planners actually produce ready plans.
