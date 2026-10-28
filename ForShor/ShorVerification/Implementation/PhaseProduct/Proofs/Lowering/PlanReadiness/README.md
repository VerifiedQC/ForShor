# `Proofs/Lowering/PlanReadiness/`

Proves that the *standard* planners in `Lowering/PlanBuilders.lean`
(`standardSignedPhaseLoweringPlan`/`standardCSignedPhaseLoweringPlan`)
actually produce plans satisfying `PhaseLoweringReady`, given a clean
recursive workspace. Files run in order `BodyReadiness` → `AllocDeallocReadiness`
→ `RecursiveReadiness` (each may use anything from the ones before it).

The two results this subfolder exists to prove, both in **`RecursiveReadiness.lean`**:

- **`standardSignedPhaseLoweringPlan_ready_of_workspace`** — given
  `SignedRecursiveWorkspaceStateOK` on a state `ψ` (plus the usual
  interpolation-safety side conditions), the standard signed plan built from
  that workspace is ready on `ψ`.
- **`standardCSignedPhaseLoweringPlan_ready_of_workspace`** — the same for
  the controlled planner and `CSignedRecursiveWorkspaceStateOK`.

`Main.lean` uses both directly to discharge the readiness hypothesis before
invoking the plan-lowering correctness theorems in `Proofs/Lowering/`.
Getting there required: `BodyReadiness.lean` proving readiness for the
compiled annotated body (mirroring `Proofs/Compiler/Body/`'s correctness
proof, one level up at the plan level), and `AllocDeallocReadiness.lean`
proving the allocation/deallocation plan fragments are (trivially) ready.
