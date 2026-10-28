# `Proofs/Lowering/`

Correctness of the `Lowering/` plan machinery: that lowering a
`QFTLoweringPlan` to a `LowGate` (via `lowerQFTPlan`) preserves semantics
given the plan is "ready" (`QFTLoweringReady`, defined in `PlanSemantics.lean`), and
that the canonical planners built in `Lowering/PlanBuilders.lean` actually
produce ready, workspace-preserving plans.

The two results this folder's proofs ultimately exist to feed `Main.lean`:

- **`evalL_lowerQFTPlan`** (`PlanSemantics.lean`) — the core interpreter
  theorem: for *any* `QFTLoweringPlan` that is ready on a state `ψ` (and the
  source program satisfies the usual interpolation-safety side conditions),
  `LowerGateClass.evalL (lowerQFTPlan plan) ψ = qs.eval (Gate.QFT r) ψ`.
  Proved by induction on the plan: the base cases fall out of
  `eval_QFT_size0`/`eval_QFT_size1` (this file's own opening section), and
  the split case calls `Proofs/Decomposition.lean`'s `eval_QFT_split` to
  match the plan's right/phase/left/radix-reversal shape against the
  high-level decomposition. `evalL_lowerQFTPlan_add`/`_smul`/`_zero` and
  `QFTLoweringReady.add`/`.smul`/`.zero` extend both notions from basis kets
  to arbitrary states.
- **`Policy.evalL_lowerQFT`** (`Readiness.lean`) — the file and folder's
  capstone: for any admissible policy and any state with a valid, clean
  `Policy.QFTWorkspaceStateOK` workspace, `Policy.lowerQFT`'s output
  evaluates exactly like `Gate.QFT r`. It follows from `evalL_lowerQFTPlan`
  once the canonical reserve-backed plan (`Policy.reserveQftPlan`) is shown
  ready — which is most of this file's work. **`evalL_lowerQFT`** is the
  fixed-table spelling, the same statement at the constant policy, proved
  through the policy theorem. `Main.lean` packages the two as
  `Policy.lowerQFT_correct` and `lowerQFT_correct`.

Getting to `Policy.evalL_lowerQFT` required: converting fresh-zero reserve
facts into the phase-product macro's own clean-state hypothesis
(`QFTWorkspaceCleanState.phaseCleanState`/`.signedCleanState`); showing both
the phase-product macro and recursive QFT calls preserve
`QFTWorkspaceCleanState` on the *shared* workspace pools
(`eval_PhaseProdUsing_preserves_QFTWorkspaceCleanState`,
`eval_QFT_preserves_QFTWorkspaceCleanState`); readiness for the
phase-product bridge itself (`Policy.phaseProdUsingPlan_ready_and_clean`);
and finally assembling all of that, by recursion on register width, into
readiness and clean-preservation for the planner
(`Policy.qftPlan_ready_and_clean_explicit`, specialized to the public
reserve-backed plan as `Policy.qftPlan_ready_and_clean`).
