# Architecture: a file-by-file guide

This document walks through the Lean development in detail. For an overview and build instructions, see the [README](README.md).

The repo is easiest to understand if you separate `ShorVerification` into the core semantics, three proof layers, and the final Shor statement:

- `Basic.lean` is the shared semantic core: registers, extended registers, the high-level `Gate` language, quantum semantics, and general semantic facts.
- `MathBackBone/` contains source-level arithmetic, interpolation algebra, and the classical number-theoretic/postprocessing material needed by the Shor statement.
- `AlgorithmCorrectness/` contains high-level circuit identities and algorithm-level component proofs, including phase-product compilation correctness, QFT decomposition, and modular-exponentiation bounds.
- `AbstractMachine/` contains the low-level `LowGate` machine, recursive lowering from `Gate` to `LowGate`, and lowering correctness theorems.
- `ShorCorrectness.lean` is the top-level order-finding/Shor correctness statement.

The most important dependency story is:

- `MathBackBone/Table_Generation` produces the source programs and phase-point structure.
- `MathBackBone/Toom_Cook_formula.lean` supplies the interpolation algebra.
- `AlgorithmCorrectness/PhaseProduct/InterpolationCorrectness.lean` proves the high-level Toom-Cook phase identity.
- `AlgorithmCorrectness/PhaseProduct/CompilationCorrectness.lean` uses that identity to prove correctness of the compiled signed phase-product circuit.
- `AlgorithmCorrectness/QFT/Decomposition.lean` proves the high-level QFT split identity.
- `AbstractMachine/QFTLoweringCorrectness.lean` and `AbstractMachine/WholeProgramCorrectness.lean` lift phase-product and QFT lowering to the full `Gate` language.
- `MathBackBone/ShorAlgorithm.lean`, `AlgorithmCorrectness/ModExpBounds.lean`, and the lowering theorem feed into `ShorCorrectness.lean`.

## `FastMultiplication/ShorVerification/Basic.lean`

This is the foundational semantics file for the verification layer. It defines ordinary registers `Reg`, extended registers `ExtReg`, the abstract high-level gate language `Gate`, the typeclass `QSemantics`, and the semantic typeclasses for QFT, phase gates, extensions, arithmetic, and general gate facts.

It also proves the core semantic facts that later files repeatedly invoke, such as `eval_PhaseProd_ket`, `eval_RadixReverse_split_ket`, `eval_isometry`, and `eval_norm_preserved`.

## `FastMultiplication/ShorVerification/MathBackBone`

This folder is the mathematical backbone of the project. It contains the symbolic source-program generator, Toom-Cook interpolation algebra, and the classical Shor/order-finding definitions.

### `MathBackBone/Table_Generation`

This folder is the source-level arithmetic side of the project. It works entirely with symbolic registers and symbolic programs before any concrete bit-level or abstract quantum semantics enter the picture.

The internal dependency chain is:

`Basic.lean -> Language.lean -> Basic_lemmas.lean/Tactics.lean/Lemmas_and_Theorems.lean -> Synthesis_programs.lean -> One_register_synthesis_combined.lean -> Table_Blocks.lean`

### `FastMultiplication/ShorVerification/MathBackBone/Table_Generation/Basic.lean`

This is the foundational definitions file for the source language. It defines symbolic registers, symbolic states, and the core register operations such as shift, negate, and add-scaled. It also defines inverse source operations.

This file is not trying to prove one global theorem. Instead, it establishes the local algebraic facts that every later file uses. Typical results here show how shifts compose, how exact right shifts behave, and how `addScaledReg` interacts with the other basic operations.

### `FastMultiplication/ShorVerification/MathBackBone/Table_Generation/Language.lean`

This file turns the raw operations into a programming language. It defines:

- `Prog`
- single-step execution `applyOp?`
- whole-program execution `run?`
- well-formedness predicates
- phase-point matching and the coverage predicate `PhaseProductCoverage`

Conceptually, this is the file that says what a symbolic multiplication program means. It is mostly definitional, but it introduces one of the key predicates used later throughout the repo: `PhaseProductCoverage`.

### `FastMultiplication/ShorVerification/MathBackBone/Table_Generation/Basic_lemmas.lean`

This is a helper lemma file. Its role is to make the source language usable in proofs. The important results here are not "main theorems" of the repo; they are structural lemmas such as:

- `run?_append`
- exact interaction between inverses and execution
- `run?_inverse_undoes_WF`

This file is best thought of as infrastructure for reasoning about source programs.

### `FastMultiplication/ShorVerification/MathBackBone/Table_Generation/Tactics.lean`

This is also a helper file. It contains tactic support and small example programs used to test or automate phase-coverage arguments. It is not a conceptual endpoint of the project.

### `FastMultiplication/ShorVerification/MathBackBone/Table_Generation/Lemmas_and_Theorems.lean`

Despite the name, this is not the main climax of the folder. It records useful source-level example results and local program identities. Theorems here are mainly sanity checks and algebraic rewrites rather than the final purpose of the table-generation pipeline.

### `FastMultiplication/ShorVerification/MathBackBone/Table_Generation/Synthesis_programs.lean`

This file begins the actual synthesis story. It defines the source programs that implement the table generation.

It also shows that the synthesized source programs are executable and well-behaved. Important results here prove existence of successful runs for the generated programs, for example:

- `run_some_addConstFrom`
- `run_some_computeLocalAux`
- `computeLocal2_some_state`

In other words, this file produces the symbolic programs that later become the input to the phase-product story.

### `FastMultiplication/ShorVerification/MathBackBone/Table_Generation/One_register_synthesis_combined.lean`

This is the largest and most important file in `Table_Generation`. It gathers the synthesis material into one long proof development and pushes it to the point where the phase-product machinery can use it.

The main source-level theorems this file is aiming at are:

- `opsForPointWithProduct_returns_to_original`
- `genOpsWithProduct_returns_to_original`
- `genOpsWithProduct_PhaseProductCoverage`

The first two say that the generated arithmetic programs return the symbolic state to its original form after doing the needed work. The last theorem is the crucial one for the rest of the repo: it proves that the generated source program consumes the right interpolation points in the right way. That is exactly the bridge needed by the later phase-product correctness proofs.

### `FastMultiplication/ShorVerification/MathBackBone/Table_Generation/Table_Blocks.lean`

This file repackages phase coverage into a block-decomposition form that is easier to use in the large `AlgorithmCorrectness/PhaseProduct` proofs.

Its important theorems are:

- `progConsumesPts_has_blockDecomposition`
- `progConsumesPts_implies_phaseProductCoverage`
- `phaseProductCoverage_peel_block`

Conceptually, this file says that a covered source program can be broken into phase blocks with clean interfaces. This is the version of the source-level result that the quantum correctness proofs actually want to consume.

### `FastMultiplication/ShorVerification/MathBackBone/Toom_Cook_formula.lean`

This file is a self-contained interpolation file. It defines interpolation matrices, evaluation-at-radix maps, and generic nonsingularity statements for good interpolation points.

Its purpose is to support `AlgorithmCorrectness/PhaseProduct/InterpolationCorrectness.lean`. It is not specific to the gate semantics by itself, but it supplies the Toom-Cook algebra that the phase-product proof needs.

### `FastMultiplication/ShorVerification/MathBackBone/ShorAlgorithm.lean`

This file contains the classical Shor/order-finding math used by the final theorem: the multiplicative-order predicate, the register-size assumptions, good measurement outcomes, the continued-fraction postprocessing interface, and the success-probability constant `κ`.

## `FastMultiplication/ShorVerification/AbstractMachine`

This folder contains the low-level abstract machine and the translation story from high-level `Gate` syntax to `LowGate` syntax.

### `AbstractMachine/LowGate.lean`

This file defines the low-level target language `LowGate` and its basic notation. It is intentionally separate from the phase-product correctness stack.

### `AbstractMachine/Lowering.lean`

This file defines the recursive lowering pass from `Gate` to `LowGate`, the `LowerGateClass` semantic interface, and the correctness lemmas for lowered phase products.

### `AbstractMachine/QFTLoweringCorrectness.lean`

This file uses the high-level QFT split theorem to prove correctness of recursive QFT lowering. Its main endpoint is `eval_lowerQFT`.

### `AbstractMachine/WholeProgramCorrectness.lean`

This file proves the whole-program lowering theorem `lowerGate_correctness`, guarded by the geometric side-condition predicate `GateGeomOK`.

## `FastMultiplication/ShorVerification/AlgorithmCorrectness`

This folder contains high-level circuit identities and component correctness statements. It avoids owning the low-level translation machinery; those proofs live under `AbstractMachine`.

### `AlgorithmCorrectness/PhaseProduct/Core.lean`

This is the main definitions file for the phase-product compiler. It introduces layout and width-tracking structures, interpolation bookkeeping, annotated operations, allocation and deallocation circuits, and encoded-state predicates.

### `AlgorithmCorrectness/PhaseProduct/SupportLemmas.lean`

This file centralizes reusable facts about split extended registers, width bounds, row evaluation under source operations, layout disjointness, and generated interpolation points.

### `AlgorithmCorrectness/PhaseProduct/WidthSoundness.lean`

This file proves that the width bookkeeping extracted from a symbolic source program is sound for every symbolic state reached during execution. The main endpoint is `allocated_widths_sound`.

### `AlgorithmCorrectness/PhaseProduct/AllocationCorrectness.lean`

This file proves that allocation moves basis states into the widened target layout in the intended encoded form. Important endpoints include `eval_compileSignedAllocations_ket` and `eval_compileSignedAllocations_ket_fits`.

### `AlgorithmCorrectness/PhaseProduct/BodyCorrectness.lean`

This file proves the semantic behavior of the compiled annotated operation body and the subsequent deallocation step. Its endpoints include `eval_compileAnnotatedOpsToSignedGateAux_of_blocks`, `eval_compileSignedDeallocations_ket`, and `eval_compileAnnotatedOpsToSignedGateAux_of_blocks_then_dealloc`.

### `AlgorithmCorrectness/PhaseProduct/InterpolationCorrectness.lean`

This file is the algebraic half of the phase-product story. It proves that the phase scalar accumulated from interpolation points is exactly the target signed phase-product scalar. The key endpoint is `toom_cook_interpolation`.

### `AlgorithmCorrectness/PhaseProduct/CompilationCorrectness.lean`

This file assembles allocation, body/deallocation, and interpolation correctness into the main theorem for `compileOpsToSignedGate`: `eval_compileOpsToSignedGate_correct`.

### `AlgorithmCorrectness/QFT/Decomposition.lean`

This file proves the high-level QFT split identity: QFT over a register can be decomposed into QFT on the right half, a phase product, QFT on the left half, and radix reversal. The main theorem is `eval_QFT_split`.

### `AlgorithmCorrectness/ModExpBounds.lean`

This file is a separate branch of the story. Instead of exact circuit equality, it develops approximation bounds for modular multiplication and modular exponentiation.

It introduces the specification classes used to talk about ideal and approximate modular multiplication, defines the approximate and ideal modular-exponentiation gates, and then proves quantitative error bounds. The important theorems here are:

- `modExpSteps_dist_bound`
- `modExp_dist_bound`
- `modExp_overlap_bound_sqrt`

These theorems say, in increasingly packaged form, that the approximate modular exponentiation remains close to the ideal one, first in norm distance and then in overlap. This file is important because the final Shor statement needs both exact lowering results and approximation-control results.

## `FastMultiplication/ShorVerification/ShorCorrectness.lean`

This is the top file of the repository.

It defines the order-finding circuits, the measurement interface, the success-probability expression, and the top-level Shor-style correctness theorem. It depends on the exact lowering branch from `AbstractMachine/WholeProgramCorrectness.lean`, the approximation branch from `AlgorithmCorrectness/ModExpBounds.lean`, and the classical math in `MathBackBone/ShorAlgorithm.lean`.

The culminating theorem is:

- `Shor_correct`

Conceptually, this file is where everything finally comes together. The earlier files prove that the required subcircuits are lowered correctly or approximated within control; this file turns those ingredients into the final order-finding statement.

