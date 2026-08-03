# AlgorithmCorrectness

This directory contains the high-level algorithm correctness layer of the Shor verification project. It proves semantic facts about high-level `Gate` circuits before they are lowered to the `LowGate` abstract machine.

The folder has three largely independent branches:

- `PhaseProduct/`: proves the correctness of the recursive Toom-Cook phase-product compiler.
- `QFT/`: proves the high-level QFT split identity used by recursive QFT lowering.
- `ModMulBounds/`: proves quantitative approximation bounds for the modular-multiplication and modular-exponentiation circuits used by Shor.

The final approach is:

1. Prove exact semantic component theorems for phase products and QFT at the high-level `Gate` layer.
2. Prove valid-input approximation bounds for Algorithm-1 modular multiplication and modular exponentiation.
3. Export these results to the outer layers: `AbstractMachine/` uses the exact phase-product and QFT theorems for lowering correctness, while `ShorCorrectness.lean` uses the modular-exponentiation bounds for the approximate order-finding theorem.

## Main Endpoints

The most important exported results are:

```lean
lemma eval_compileOpsToSignedGate_correct
lemma eval_compileOpsToCSignedGate_correct
```

from `PhaseProduct/CompilationCorrectness.lean`. These say the compiled signed and controlled signed phase-product circuits evaluate like the corresponding high-level phase-product gates.

```lean
theorem eval_QFT_split
```

from `QFT/Decomposition.lean`. This says a QFT over a register decomposes into right-QFT, phase product, left-QFT, and radix reversal.

```lean
theorem modMul_approx_valid_dist_uniform
theorem modExpApprox_valid_dist_uniform
```

from `ModMulBounds/FinalModMul.lean` and `ModMulBounds/ModExp.lean`. These are the quantitative approximation bounds used by the final Shor correctness layer.

## `PhaseProduct/`

This folder proves correctness of the phase-product compiler.

The input is a symbolic source program `ops : Prog k` from `MathBackbone/Table_Generation`. The compiler uses that program, Toom-Cook interpolation points, and a physical chunk layout to build a high-level circuit implementing a signed phase product. The final proof says the compiled circuit has the same semantics as `Gate.SignedPhaseProd` or `Gate.CSignedPhaseProd`.

The proof strategy is:

1. Define layouts, width scans, interpolation coefficients, and compiler syntax.
2. Prove width bookkeeping is sound for the source program.
3. Prove allocation puts basis states into the intended widened layout.
4. Prove the compiled body follows the symbolic source program and deallocation restores the original layout.
5. Prove the accumulated point phases equal the target Toom-Cook product phase.
6. Assemble these into the signed and controlled phase-product compiler theorems.

### `Core.lean`

This is the definition-level core of the phase-product compiler.

It defines:

- layout structures such as `LayoutState`, `PhaseSplitLayout`, and `Gate.PhaseProductLayout`;
- width bookkeeping such as `WidthState`, `NeededWidths`, `scanNeededWidths`, and `nextSignedWidth`;
- interpolation data such as `q`, `interpMatrix`, `phaseCoeffFromPtsWidth`, and `phaseScalarFrom`;
- compiler syntax such as `compileSignedAllocations`, `compileAnnotatedOpsToSignedGateAux`, `compileOpsToSignedGate`, `controlPhaseLeaves`, and `compileOpsToCSignedGate`;
- semantic invariants such as `EncodesStateFrom`, `EncodesStateFromFits`, `WidthStateSoundPlus`, `CompilerWorkspaceOK`, and `CleanWorkspaceState`;
- reserve-budget construction for splitting extended registers into recursive child layouts.

This file answers: what objects does the phase-product compiler manipulate, and what invariants must later proofs preserve?

### `SupportLemmas.lean`

This file collects reusable facts that would otherwise clutter the main proofs.

It proves facts about split extended registers, chunk values, row evaluation, layout disjointness, phase-term annotation, generated interpolation points, and source-program block structure.

Later files use these lemmas to avoid reopening low-level arithmetic and layout arguments in every proof.

### `WidthSoundness.lean`

This file proves that the compiler's width scan is sound.

The main endpoint is:

```lean
lemma allocated_widths_sound
```

It says that the widths computed by scanning the symbolic source program dominate every intermediate symbolic state reached during execution. This is what justifies allocating enough physical room before running the compiled body.

### `AllocationCorrectness.lean`

This file proves correctness of the allocation phase.

The important endpoints include:

```lean
lemma eval_compileSignedAllocations_ket
lemma eval_compileSignedAllocations_ket_fits
```

They say that running the allocation circuit on a clean basis state creates the target encoded layout, and that the resulting encoded state fits the allocated widths.

This file supplies the starting state needed by the compiled body proof.

### `BodyCorrectness.lean`

This file proves that the compiled annotated operation body tracks the source program.

It handles each source operation case, proves that no-phase prefixes preserve the encoded-state invariant, proves that phase leaves add the intended phase factors, and shows that deallocation cancels the temporary allocation.

The main endpoints include:

```lean
lemma eval_compileAnnotatedOpsToSignedGateAux_of_blocks
lemma eval_controlPhaseLeaves_compileAnnotatedOpsToSignedGateAux_of_blocks
lemma eval_compileSignedDeallocations_ket
lemma eval_compileAnnotatedOpsToSignedGateAux_of_blocks_then_dealloc
```

This file is the operational heart of the compiler proof: it connects the symbolic program execution to the generated high-level circuit.

### `InterpolationCorrectness.lean`

This file proves the algebraic phase equality.

It bridges the compiler's accumulated interpolation-point phase scalar to the desired signed product phase. Important ingredients include:

- `phaseCoeffFromPtsWidth_eq_interpCoeff`;
- `expectedRow_mul_expectedRow_eq_interpEntry`;
- `evalAtRadix_tcProductCoeff_eq_ext_product`;
- `toom_cook_interpolation`.

The main endpoint is:

```lean
lemma toom_cook_interpolation
```

This is where the Toom-Cook algebra from `MathBackbone/Toom_Cook_formula.lean` enters the compiler proof.

### `CompilationCorrectness.lean`

This file assembles the complete phase-product compiler theorem.

It combines:

- allocation correctness,
- body/deallocation correctness,
- interpolation correctness,
- source-program coverage and successful execution,
- and linear extension from basis states to general quantum states.

The final exported theorems are:

```lean
lemma eval_compileOpsToSignedGate_correct
lemma eval_compileOpsToCSignedGate_correct
```

These are consumed by `AbstractMachine/PhaseProductLoweringCorrectness`, which recursively lowers high-level phase-product gates to `LowGate`.

## `QFT/`

This folder currently contains the high-level QFT decomposition theorem.

### `Decomposition.lean`

This file proves the recursive split identity for QFT.

It develops:

- register split helpers for `leftReg`, `rightReg`, and `splitM`;
- finite-index reindexing facts for `Fin A × Fin B` versus `Fin (A * B)`;
- normalization and phase-factor identities for QFT sums;
- basis-ket proofs for the split circuit;
- radix-reversal facts;
- and finally the arbitrary-state theorem by linearity.

The final endpoint is:

```lean
theorem eval_QFT_split
```

Conceptually, it proves that for a register of size at least two, QFT can be expressed as:

```text
QFT(right half)
  -> PhaseProdUsing(left half, right half)
  -> QFT(left half)
  -> RadixReverse
```

This theorem is consumed by `AbstractMachine/QFTLoweringCorrectness/PlanSemantics.lean` to prove that the recursive low-level QFT plan implements the high-level `Gate.QFT`.

## `ModMulBounds/`

This folder proves approximation bounds for the modular multiplication and modular exponentiation circuits used by Shor's algorithm.

Unlike `PhaseProduct/` and `QFT/`, this branch is not an exact equality proof for a compiler. It proves norm-distance bounds between an approximate circuit and an ideal specification, under valid-input and layout hypotheses.

For the detailed file-by-file guide, see [`ModMulBounds/README.md`](ModMulBounds/README.md).

## How the Proofs Fit Together

The dependency flow is:

```text
PhaseProduct/Core
  -> PhaseProduct/SupportLemmas
  -> PhaseProduct/WidthSoundness
  -> PhaseProduct/AllocationCorrectness
  -> PhaseProduct/BodyCorrectness
  -> PhaseProduct/InterpolationCorrectness
  -> PhaseProduct/CompilationCorrectness
  -> AbstractMachine/PhaseProductLoweringCorrectness

QFT/Decomposition
  -> AbstractMachine/QFTLoweringCorrectness

ModMulBounds/Core
  -> ModMulBounds/Algorithm1Expansion
  -> ModMulBounds/Step1QPE
  -> ModMulBounds/Step1Bound
  -> ModMulBounds/Step2Bound
  -> ModMulBounds/Step34Exact
  -> ModMulBounds/FinalModMul
  -> ModMulBounds/ModExp
  -> ShorCorrectness
```

In short:

1. `PhaseProduct/` proves exact correctness of the compiled Toom-Cook phase-product circuit.
2. `QFT/` proves the exact recursive QFT identity.
3. `ModMulBounds/` proves approximation bounds for the modular arithmetic used by order finding.
4. The outer layers combine these with abstract-machine lowering, measurement, and classical number theory to state the final Shor correctness theorems.
