# Fast_multiplication

The repo is easiest to understand if you separate it into two main Lean layers, plus auxiliary Python experiments:

- `ShorVerification/MathBackbone` contains the source-level arithmetic and interpolation material. In particular, `Table_Generation` defines the algorithm for generating the interpolation tables and proves its correctness. This is one of the mathematical backbones needed to prove the correctness of Phase Product.
- `ShorVerification` is the main abstract semantic formalization. It proves that the synthesized phase-product and QFT constructions really implement the intended quantum gates, and it is the conceptual heart of the repo.

The most important dependency story is:

- `ShorVerification/MathBackbone/Table_Generation` produces the source programs and phase-point structure.
- `ShorVerification/MathBackbone/Toom_Cook_formula.lean` supplies the interpolation algebra.
- `ShorVerification/PhaseProduct` imports that material and proves correctness of compiled signed phase-product circuits.
- `ShorVerification/QFT` then uses the phase-product result to prove correctness of lowered QFT.
- `ShorVerification/compilation_correctness.lean` lifts this to general gate lowering, and `ShorVerification/Shor_definition.lean` sits at the top of the stack.

## ShorVerification/MathBackbone/Table_Generation

This folder is the source-level arithmetic side of the project. It works entirely with symbolic registers and symbolic programs before any concrete bit-level or abstract quantum semantics enter the picture.

The internal dependency chain is:

`Basic.lean -> Language.lean -> Basic_lemmas.lean/Tactics.lean/Lemmas_and_Theorems.lean -> Synthesis_programs.lean -> One_register_synthesis_combined.lean -> Table_Blocks.lean`

### `FastMultiplication/ShorVerification/MathBackbone/Table_Generation/Basic.lean`

This is the foundational definitions file for the source language. It defines symbolic registers, symbolic states, and the core register operations such as shift, negate, and add-scaled. It also defines inverse source operations.

This file is not trying to prove one global theorem. Instead, it establishes the local algebraic facts that every later file uses. Typical results here show how shifts compose, how exact right shifts behave, and how `addScaledReg` interacts with the other basic operations.

### `FastMultiplication/ShorVerification/MathBackbone/Table_Generation/Language.lean`

This file turns the raw operations into a programming language. It defines:

- `Prog`
- single-step execution `applyOp?`
- whole-program execution `run?`
- well-formedness predicates
- phase-point matching and the coverage predicate `PhaseProductCoverage`

Conceptually, this is the file that says what a symbolic multiplication program means. It is mostly definitional, but it introduces one of the key predicates used later throughout the repo: `PhaseProductCoverage`.

### `FastMultiplication/ShorVerification/MathBackbone/Table_Generation/Basic_lemmas.lean`

This is a helper lemma file. Its role is to make the source language usable in proofs. The important results here are not "main theorems" of the repo; they are structural lemmas such as:

- `run?_append`
- exact interaction between inverses and execution
- `run?_inverse_undoes_WF`

This file is best thought of as infrastructure for reasoning about source programs.

### `FastMultiplication/ShorVerification/MathBackbone/Table_Generation/Tactics.lean`

This is also a helper file. It contains tactic support and small example programs used to test or automate phase-coverage arguments. It is not a conceptual endpoint of the project.

### `FastMultiplication/ShorVerification/MathBackbone/Table_Generation/Lemmas_and_Theorems.lean`

Despite the name, this is not the main climax of the folder. It records useful source-level example results and local program identities. Theorems here are mainly sanity checks and algebraic rewrites rather than the final purpose of the table-generation pipeline.

### `FastMultiplication/ShorVerification/MathBackbone/Table_Generation/Synthesis_programs.lean`

This file begins the actual synthesis story. It defines the source programs that implement the table generation.

It also shows that the synthesized source programs are executable and well-behaved. Important results here prove existence of successful runs for the generated programs, for example:

- `run_some_addConstFrom`
- `run_some_computeLocalAux`
- `computeLocal2_some_state`

In other words, this file produces the symbolic programs that later become the input to the phase-product story.

### `FastMultiplication/ShorVerification/MathBackbone/Table_Generation/One_register_synthesis_combined.lean`

This is the largest and most important file in `Table_Generation`. It gathers the synthesis material into one long proof development and pushes it to the point where the phase-product machinery can use it.

The main source-level theorems this file is aiming at are:

- `opsForPointWithProduct_returns_to_original`
- `genOpsWithProduct_returns_to_original`
- `genOpsWithProduct_PhaseProductCoverage`

The first two say that the generated arithmetic programs return the symbolic state to its original form after doing the needed work. The last theorem is the crucial one for the rest of the repo: it proves that the generated source program consumes the right interpolation points in the right way. That is exactly the bridge needed by the later phase-product correctness proofs.

### `FastMultiplication/ShorVerification/MathBackbone/Table_Generation/Table_Blocks.lean`

This file repackages phase coverage into a block-decomposition form that is easier to use in the large `ShorVerification/PhaseProduct` proofs.

Its important theorems are:

- `progConsumesPts_has_blockDecomposition`
- `progConsumesPts_implies_phaseProductCoverage`
- `phaseProductCoverage_peel_block`

Conceptually, this file says that a covered source program can be broken into phase blocks with clean interfaces. This is the version of the source-level result that the quantum correctness proofs actually want to consume.

## A Supporting Math File

### `FastMultiplication/ShorVerification/MathBackbone/Toom_Cook_formula.lean`

This file is a self-contained interpolation file. It defines interpolation matrices, evaluation-at-radix maps, and generic nonsingularity statements for good interpolation points.

Its purpose is to support `ShorVerification/PhaseProduct/InterpolationCorrectness.lean`. It is not specific to the gate semantics by itself, but it supplies the Toom-Cook algebra that the phase-product proof needs.

## ShorVerification

This is the core of the repository. The guiding idea is:

- define an abstract gate language and the semantic interfaces it should satisfy,
- build a verified phase-product implementation using the source programs from `ShorVerification/MathBackbone/Table_Generation`,
- use that verified phase-product to derive a verified QFT decomposition,
- lift that to a correctness theorem for general gate lowering,
- and finally formulate the top-level Shor/order-finding statement.

The important dependency chain inside this folder is:

`Basic.lean`
-> `PhaseProduct/Core.lean`
-> `PhaseProduct/SupportLemmas.lean`
-> `PhaseProduct/WidthSoundness.lean`
-> `PhaseProduct/AllocationCorrectness.lean`
-> `PhaseProduct/BodyCorrectness.lean`

and in parallel

`PhaseProduct/SupportLemmas.lean`
-> `PhaseProduct/InterpolationCorrectness.lean`

then these meet in

`PhaseProduct/CompilationCorrectness.lean`
-> `PhaseProduct/PhaseDecomposition.lean`
-> `QFT/QFT_decomposition_one_layer.lean`
-> `QFT/QFT_decomp_correctness.lean`
-> `compilation_correctness.lean`
-> `Shor_definition.lean`

There is also a second branch

`Basic.lean -> ModExpBounds.lean -> Shor_definition.lean`

which handles approximation bounds for modular exponentiation rather than exact lowering.

### `FastMultiplication/ShorVerification/Basic.lean`

This is the foundational semantics file for the entire verification layer. It defines:

- ordinary registers `Reg`
- extended registers `ExtReg`
- the abstract gate language
- the typeclass `QSemantics`
- semantic typeclasses for QFT, phase gates, extensions, arithmetic, and general gate facts

This file is not merely a list of definitions. It also proves the core semantic facts that later files repeatedly invoke. In particular, it contains canonical basis-state evaluations such as:

- `eval_PhaseProd_ket`
- `eval_RadixReverse_split_ket`

and general functional-analytic facts such as:

- `eval_isometry`
- `eval_norm_preserved`

So `Basic.lean` is the semantic contract of the whole verification story. Almost every later theorem in `ShorVerification` is phrased in terms of the interfaces and lemmas introduced here.

### `FastMultiplication/ShorVerification/ModExpBounds.lean`

This file is a separate branch of the story. Instead of exact circuit equality, it develops approximation bounds for modular multiplication and modular exponentiation.

It introduces the specification classes used to talk about ideal and approximate modular multiplication, defines the approximate and ideal modular-exponentiation gates, and then proves quantitative error bounds. The important theorems here are:

- `modExpSteps_dist_bound`
- `modExp_dist_bound`
- `modExp_overlap_bound_sqrt`

These theorems say, in increasingly packaged form, that the approximate modular exponentiation remains close to the ideal one, first in norm distance and then in overlap. This file is important because the final Shor statement needs both exact lowering results and approximation-control results.

## ShorVerification/PhaseProduct

This folder is the largest proof pipeline in the repo. Its job is to show that a source-level phase-product program generated from interpolation data really implements the intended signed phase-product gate.

The internal organization is deliberate:

- `Core.lean` contains definitions.
- `SupportLemmas.lean` contains the reusable small lemmas.
- `WidthSoundness.lean`, `AllocationCorrectness.lean`, and `BodyCorrectness.lean` prove the semantic behavior of the compiled circuit.
- `InterpolationCorrectness.lean` proves the Toom-Cook algebra.
- `CompilationCorrectness.lean` assembles everything into the final phase-product correctness theorem.
- `PhaseDecomposition.lean` then turns that theorem into a lowering theorem for abstract gates.

### `FastMultiplication/ShorVerification/PhaseProduct/Core.lean`

This is a definitions file. It introduces the low-level gate language `LowGate`, layout and width-tracking structures, interpolation bookkeeping, annotated operations, allocation and deallocation circuits, and the compiled signed phase-product constructions.

It also defines the semantic predicates that the later correctness proofs use, such as encoded-state predicates and width-soundness predicates.

This file is not trying to prove the main theorem of the phase-product development. Its role is to fix the objects that the later files reason about.

### `FastMultiplication/ShorVerification/PhaseProduct/SupportLemmas.lean`

This is the main helper lemma file for the phase-product development. It contains the reusable facts about:

- splitting extended registers
- width bounds
- evaluation of rows under shift, negate, and add-scaled operations
- layout disjointness and equality outside the layout
- interpolation-point generation

This file is not a "main theorem" file. Its point is to centralize the small and medium lemmas that the larger semantic proofs would otherwise have to carry inline.

One especially important output of this file is `genInterpolationPoints_good`, which certifies that the chosen interpolation points are mathematically good for the Toom-Cook argument.

### `FastMultiplication/ShorVerification/PhaseProduct/WidthSoundness.lean`

This is a helper proof file, but it has a very clear endpoint. The file proves that the width bookkeeping extracted from the symbolic source program is sound with respect to the symbolic values encountered during execution.

The main theorem here is:

- `allocated_widths_sound`

Everything else in the file supports that statement. This theorem is crucial because the allocation correctness proofs need to know that the target layout is actually wide enough for the values that later operations will place into it.

### `FastMultiplication/ShorVerification/PhaseProduct/AllocationCorrectness.lean`

This file proves that the allocation phase of the compiled circuit does the right thing on basis states.

The key theorems are:

- `eval_compileSignedAllocations_ket`
- `eval_compileSignedAllocations_ket_fits`

These results say that after running the allocation circuit, the basis state is moved into the enlarged target layout in the right encoded form, and the encoded chunk values fit the promised widths. In other words, this file establishes the correctness of the transition from the initial layout to the working layout used by the body of the phase-product computation.

### `FastMultiplication/ShorVerification/PhaseProduct/BodyCorrectness.lean`

This is the longest semantic proof file in the phase-product stack. It studies what happens after allocation, when the compiled symbolic operations run and when the temporary layout is deallocated again.

The file first proves one-step preservation lemmas for each source operation, then lifts them to no-phase runs, then handles matched phase steps, and finally proves that deallocation cancels the earlier allocation.

The most important endpoints are:

- `eval_compileAnnotatedOpsToSignedGateAux_of_blocks`
- `eval_compileSignedDeallocations_ket`
- `eval_compileAnnotatedOpsToSignedGateAux_of_blocks_then_dealloc`

Conceptually, this file proves the semantic heart of the compiler: the compiled body applies exactly the phase that the source block decomposition predicts, while preserving the intended encoded state throughout the computation.

### `FastMultiplication/ShorVerification/PhaseProduct/InterpolationCorrectness.lean`

This file is the algebraic half of the phase-product story. It does not reason primarily about gate execution; instead, it proves that the phase scalar accumulated from the interpolation points is exactly the scalar that should appear in the target signed phase-product.

The key endpoint is:

- `toom_cook_interpolation`

Along the way, the file also proves important bridge lemmas such as:

- `phaseScalarFrom_eq_phaseScalarFromList`
- `tcPointTerm_eq_evalAtPoint_tcProductCoeff`
- `evalAtRadix_tcProductCoeff_eq_ext_product`

So this is the file that turns the pointwise interpolation data into the final algebraic identity needed by the semantic proof.

### `FastMultiplication/ShorVerification/PhaseProduct/CompilationCorrectness.lean`

This file assembles the allocation proof, body proof, and interpolation proof into the main correctness theorem for the compiled signed phase-product circuit.

Its important theorems are:

- `eval_compileOpsToSignedGate_correct_ket_of_blocks`
- `eval_compileOpsToSignedGate_correct_ket`
- `eval_compileOpsToSignedGate_correct`

The last theorem is the real endpoint of the phase-product compiler story: it states that the compiled circuit is semantically equal to the intended `Gate.SignedPhaseProd`. This is the one level correctness proof or the Quantum gate identity based on which the recursive breakdown of PhaseProduct is done.

### `FastMultiplication/ShorVerification/PhaseProduct/PhaseDecomposition.lean`

Once the exact compiled signed phase-product has been verified, this file uses it to justify a lowering procedure from the abstract gate language to the low-level gate language.

It defines the lowering infrastructure and proves the important lowering theorems:

- `evalL_lowerSignedPhaseProd`
- `evalL_lowerPhaseProd`

The many other lemmas in the file show that the generated low-level circuits are syntactically lowerable and satisfy the side conditions needed by the recursive lowering procedure. So this file is where the verified compiled phase-product becomes usable as part of a larger lowered circuit.

## ShorVerification/QFT

The QFT files sit directly on top of the phase-product result. The main idea is that once signed phase-product gates have been lowered correctly, one can recursively decompose QFT by splitting the register, inserting the appropriate phase-product, and finishing with a radix reversal.

### `FastMultiplication/ShorVerification/QFT/QFT_decomposition_one_layer.lean`

This file contains the actual decomposition argument. It proves an exact split identity for QFT, first on basis states and then on arbitrary states.

The main theorem is:

- `eval_QFT_split`

Everything else in the file is in service of that result: split-register bookkeeping, phase identity lemmas, reindexing lemmas, and digit-reversal manipulations. This is the conceptual place where the phase-product theorem is converted into a QFT theorem.

### `FastMultiplication/ShorVerification/QFT/QFT_decomp_correctness.lean`

This file packages the split-QFT result into the form needed by the general lowering pipeline.

Its main theorem is:

- `eval_lowerQFT`

So while `QFT_decomposition_one_layer.lean` proves the exact mathematical identity, `QFT_decomp_correctness.lean` is the file that says the implemented low-level lowering procedure for QFT is semantically correct.

### `FastMultiplication/ShorVerification/compilation_correctness.lean`

This file is the whole-program exact lowering theorem.

It introduces the geometric side-condition predicate `GateGeomOK` and proves:

- `lowerGate_correctness`

This theorem says that, assuming the needed register-disjointness and well-formedness conditions, the recursive lowering pass on gates preserves semantics. In the overall project, this is the theorem that lifts the verified phase-product and QFT components to arbitrary composite gates built from them.

### `FastMultiplication/ShorVerification/Shor_definition.lean`

This is the top file of the repository.

It defines the order-finding circuits, the success-probability expressions, and the continued-fraction postprocessing assumptions used to state a Shor-style correctness theorem. It depends on two earlier branches:

- the exact lowering branch coming from `compilation_correctness.lean`
- the approximation branch coming from `ModExpBounds.lean`

The culminating theorem is:

- `Shor_correct`

Conceptually, this file is where everything finally comes together. The earlier files prove that the required subcircuits are lowered correctly or approximated within control; this file turns those ingredients into the final order-finding statement.

## Auxiliary Python Files

The Python files in `ModularExponentiation/` and `ModularMultiplication/` are auxiliary experiments and prototypes. They are not part of the main Lean proof dependency chain described above.
