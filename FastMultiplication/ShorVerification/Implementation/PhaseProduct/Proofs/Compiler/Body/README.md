# `Proofs/Compiler/Body/`

Proves the compiled annotated-body circuit (`compileAnnotatedOpsToSignedGateAux`)
evaluates to the phase scalar the interpolation coefficients prescribe. Files
run in dependency order and build toward the two theorems in `Dealloc.lean`:

`SingleStep.lean` (one arithmetic instruction preserves the encoded state) →
`NoPhaseRuns.lean` (lift that across a whole no-phase segment) →
`PhaseBlocks.lean` (identify the phase each block's gate contributes) →
`Controlled.lean` (push `controlPhaseLeaves` through, get the public
uncontrolled/controlled body theorems) → `Dealloc.lean` (transport through
deallocation back to the original basis state).

The two results this subfolder exists to prove, both in **`Dealloc.lean`**:

- **`eval_compileAnnotatedOpsToSignedGateAux_of_blocks_then_dealloc`** —
  allocate, run the annotated body, then deallocate: the net effect on the
  original input basis ket is exactly the phase-scalar multiplication the
  interpolation coefficients specify.
- **`eval_controlPhaseLeaves_compileAnnotatedOpsToSignedGateAux_of_blocks_then_dealloc`**
  — the same, with every phase-product leaf wrapped by a shared control qubit
  (the controlled variant).

These feed directly into `Proofs/Compiler/Compilation.lean` and from there
into `Proofs/Compiler/Correctness.lean`'s two apex theorems.
