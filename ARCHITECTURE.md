# Architecture: a file-by-file guide

This document walks through the Lean development in detail. For an overview
and build instructions, see the [README](README.md). Every folder named below
also has its own `README.md` with the full file-by-file breakdown; this page
is the map between them.

# FastMultiplication Shor Verification

This repository is a Lean 4 verification project for a fast-multiplication-based
implementation of the phase-product, QFT, modular multiplication, modular
exponentiation, and order-finding pieces used in Shor's algorithm.

The tree splits in two. `FastMultiplication/ShorVerification/Framework/` is the
specification: the register/gate vocabulary every theorem is stated in, the
abstract semantic classes those theorems quantify over, the cost model, the
classical number theory, the correctness contract, and what makes a submitted
Toom-Cook table admissible. `FastMultiplication/ShorVerification/Implementation/`
is the construction: the phase-product compiler, the QFT, modular
exponentiation, the Shor assembly, the gate-count proofs, and the concrete
`Reference/` circuit family. `FastMultiplication/Emit/` serialises that circuit
family to JSON, and `FastMultiplication/ShorVerification/Submission/` is the
public surface a submissions repo builds against.

Within `Implementation/`, the development has five parts:

1. **Classical mathematics** — `Implementation/PhaseProduct/Math/` and
   `Framework/Math/`: source-level arithmetic programs, Toom-Cook interpolation
   algebra, recurrence solving, and the classical Shor/factoring probability
   arguments.
2. **High-level circuit identities** — `Implementation/{PhaseProduct,QFT,
   ModularExponentiation}/Proofs/`: the structured `Gate` circuits implement
   the intended mathematical transformations.
3. **Lowering correctness** — `Implementation/{PhaseProduct,QFT}/Proofs/Lowering/`
   and `Implementation/Shor/Proofs/Lowering.lean`, over the lowerer at
   `Implementation/Shor/Lowering/LowerGate.lean`: those high-level gates lower
   correctly onto `Framework/AbstractMachine/LowGate.lean`'s language.
4. **Cost** — `Implementation/GateCount/`: asymptotic gate-count bounds for the
   lowered circuits.
5. **Assembly** — `Implementation/Shor/`, plus `Implementation/Reference/` for
   the concrete submission: the algorithmic correctness story for Shor and
   order finding.

The mathematics supplies the facts the circuit proofs are allowed to call, the
identity proofs establish the high-level circuit equations, the lowering proofs
carry those equations down to the low-level gates, and `GateCount` proves the
lowered circuits have the intended asymptotic size.

## The `Framework/` vocabulary

Every definition the single file this development began with once held now
lives under `Framework/`.
It deliberately avoids committing to one concrete Hilbert-space implementation:
it defines registers, gate syntax, and abstract semantic interfaces that later
files instantiate or reason against.

| concept | file | main names |
| --- | --- | --- |
| Registers, encodings, extended registers | `Framework/Quantum/Registers.lean` | `Reg` (an ordered list of distinct physical qubits, so layouts need not be contiguous), `Reg.width`/`ASize`/`Reg.append`/`SplitPoint`; `RegEncoding` (the basis-level read/write interface: `toNat`, `writeNat`, `bit`, read-after-write and disjoint-write laws, `basis_ext`); `ExtReg` (an active register plus an owned inactive reserve: `CanGrow`, `newBits`, `grow`, `ownedQubits`, the `*Disjoint` conditions), the signed/two's-complement decodings (`tcDecodeWidth`, `extToInt`, `FitsSignedWidth`) and the freshness predicates (`FreshZero`, `ExtReg.FreshFor`) that say workspace is clean |
| Abstract quantum semantics | `Framework/Quantum/QSemantics.lean` | `QSemantics`: a basis type, an inner-product state space, `ket`, `eval : Gate → State → State`, and laws for identity, sequencing, linearity, adjoints and inner-product preservation, plus a state induction principle. Circuit equations are proved in *any* model satisfying these axioms |
| Measurement | `Framework/Quantum/Measurement.lean` | `MeasureClass`, the outcome-probability interface the success bounds are stated against |
| High-level gate language | `Framework/AbstractMachine/Gates.lean`, `Angle.lean` | `Gate`: structural (`id`, `seq`, `adj`), elementary and structured (`H`, `X`, `QFT`, `RadixReverse`, `SignedPhaseProd`, `CSignedPhaseProd`, `Prim`), and arithmetic/workspace (`ShiftL`, `ShiftR`, `Negate`, `AddScaled`, `zeroExtend`/`signExtend`, `zeroDealloc`/`signDealloc`); the QFT phase helpers `qftPhi`, `qftPhase`, `radixReverseIndex`; `Angle` |
| Low-level target language | `Framework/AbstractMachine/LowGate.lean` | `LowGate`, the abstract machine the whole development lowers onto |
| Gate-family semantic classes | `Framework/Semantics/GateSemantics.lean` | `GateSemanticsCore` plus one class per gate family — `QFTSemantics`, `HadamardSemantics`, `PauliXSemantics`, `RadixReverseSemantics`, `PhaseSemantics`, `ExtensionSemantics`, `ArithmeticSemantics`, `ClassicalReversibleSemantics`, `ModularArithmeticSemantics`, `IdealCtrlModMulExactSemantics` — and `GateSemanticsFacts`, the convenience bundle large theorems take instead of eight separate instances |
| `LowGate` semantics | `Framework/Semantics/LowGateSemantics.lean` | `LowerGateClass`, which gives the lowered circuits their evaluation meaning |
| Cost model | `Framework/Gatecount/CostModel.lean`, `ResourceModel.lean` | `LowGateCostModel` and `LowGate.gateCount`, the fold that prices a lowered circuit; `GateResources`, `LowGateResourceModel`, `shorGateCostModel` |
| Classical number theory | `Framework/Math/ShorDefinition.lean`, `Math/Factoring_Reduction/` | `ord`, `GoodOutcome`, the continued-fraction postprocessing vocabulary (`continuedFractionConvergent`, `OrderVerifier`, `OF_post`); `shors_classical_reduction` and `shors_probability_bound` |
| The correctness contract | `Framework/Contract.lean` | `ShorOrderFindingInstance` (the arithmetic/register data for one order-finding problem), `ShorOrderFindingProgram`, `probability_of_success`, and `ShorImplementation` — one `LowGate` circuit per valid instance, a declared success probability, a trial count, and proofs that both are honest |
| What a submission is | `Framework/ToomCookTable.lean` | `Register`, `State`, `Prog`, `run?`, `expectedRow`, `ProgConsumesPtsSafe`, `interpMatrix`, `GoodToomCookPoints`, and the records `ShorLoweringSetup` / `ShorSubmission`. Imports Mathlib and nothing else |

Two design points are worth stating separately, because the rest of the
development leans on them constantly. Registers are explicit qubit *lists*
rather than intervals, which is what lets the construction support
non-contiguous layouts and workspace carved out of a reserve. And the
semantics is a class, not a model, so no theorem below depends on how basis
states happen to be represented.

## Folder Guide and Main Results

### `Implementation/PhaseProduct/Math/` and `Framework/Math/` — the mathematics

The non-circuit mathematics the verification needs: source-level arithmetic
programs, Toom-Cook interpolation algebra, recurrence-solving facts, and
classical Shor/factoring probability arguments.

Important parts:

- `PhaseProduct/Math/Table_Generation/` defines a symbolic program language and
  synthesizes interpolation-table programs. Its main results show that
  generated programs are well formed, return to the original symbolic state,
  and cover the required phase-product interpolation points. Important names
  include `genOpsWithProduct_returns_to_original` and
  `genOpsWithProduct_PhaseProductCoverage` (`Table_Generation/Programs/WithProduct.lean`)
  and `phaseProductCoverage_peel_block` (`Table_Generation/Core/Coverage.lean`).
- `PhaseProduct/Math/ToomCook.lean` proves the interpolation algebra used by
  phase product. The key theorem is `interpCoeff_correct`.
- `PhaseProduct/Math/MasterTheorem.lean` proves a shifted recurrence theorem
  used by the gate-count proof. The key endpoint is
  `shifted_master_theorem_exact_family`.
- `Framework/Math/Factoring_Reduction/` contains the classical number-theoretic
  reduction/probability material behind Shor's postprocessing. Important
  probability lemmas include `general_unsuccessful_bound`
  (`Factoring_Reduction/ProbabilityBound.lean`).
- `Framework/Math/ShorDefinition.lean` contains the classical definitions around
  Shor/order finding that the top-level theorems are phrased in.

The final role of this layer is to provide the mathematical facts that the
circuit proofs are allowed to call.

### `Implementation/{PhaseProduct,QFT,ModularExponentiation}/Proofs/` — high-level circuit identities

These folders prove that the structured `Gate` circuits implement the desired
mathematical transformations. They are not primarily the lowering layer: the
proofs that those high-level gates lower correctly to the low-level abstract
machine are the next section.

Important parts:

- `PhaseProduct/Proofs/Compiler/` proves correctness of the generated
  phase-product compiler. The layout, width scanner, annotations and compiler
  state are defined next door in `PhaseProduct/Compiler/`
  (`Layout.lean`, `Widths.lean`, `Coefficients.lean`, `Compile.lean`);
  `WidthSoundness.lean`, `Allocation.lean`, `Body/` and `Interpolation.lean`
  prove the main ingredients, and `Correctness.lean` assembles them into
  `eval_compileOpsToSignedGate_correct` and the controlled analogue
  `eval_compileOpsToCSignedGate_correct`.
- `QFT/Proofs/Decomposition.lean` proves the high-level split identity for QFT:
  a QFT over a register can be expressed through right-half QFT, a phase
  product, left-half QFT, and radix reversal. The main results are
  `eval_QFT_split` and `eval_QFT_split_ofReg`.
- `ModularExponentiation/Proofs/` develops the approximation analysis for
  modular multiplication and modular exponentiation. The main
  modular-multiplication endpoint is `modMul_approx_valid_dist_uniform`
  (`Proofs/FinalModMul.lean`); the modular-exponentiation endpoint is
  `modExpApprox_valid_dist_uniform` (`Proofs/ModExp.lean`).

The final role of this layer is to prove that the high-level algorithmic
circuits are mathematically correct, or close to the ideal circuit in the
approximate modular-arithmetic branch.

### `Implementation/{PhaseProduct,QFT}/Proofs/Lowering/` and `Implementation/Shor/Lowering/` — lowering correctness

The low-level target language and the lowering correctness story. The language
itself, `LowGate`, is framework vocabulary
(`Framework/AbstractMachine/LowGate.lean`); everything that maps onto it lives
here.

Important parts:

- `PhaseProduct/Lowering/` defines plan-directed lowerings for signed and
  controlled signed phase products (`Plan.lean`, `PlanBuilders.lean`,
  `Lower.lean`), with the workspace/readiness predicates in
  `PhaseProduct/Spec/`. `PhaseProduct/Proofs/Lowering/` proves them correct;
  main endpoints are `evalL_lowerGateRec_correct` (`Lowering/PlanSemantics.lean`)
  and `standardSignedPhaseLoweringPlan_ready` /
  `standardCSignedPhaseLoweringPlan_ready`
  (`Lowering/PlanReadiness/RecursiveReadiness.lean`). `PhaseProduct/Main.lean`
  states the two headline results, `lowerSignedPhaseProduct_correct` and
  `lowerCSignedPhaseProduct_correct`.
- `QFT/Lowering/` defines the QFT workspace requirements and the plan builders;
  `QFT/Proofs/Lowering/` proves correctness and readiness of recursive QFT
  lowering. Main endpoints are `evalL_lowerQFTPlan`
  (`Lowering/PlanSemantics.lean`), and `standardQFTLoweringPlan_ready_and_clean`
  and `evalL_lowerQFT` (`Lowering/Readiness.lean`). `QFT/Main.lean` states
  `lowerQFT_correct`.
- `Shor/Lowering/LowerGate.lean` defines `GateWorkspaceOK` and the recursive
  `lowerGate` function from high-level `Gate` to `LowGate`;
  `Shor/Proofs/Lowering.lean` proves whole-program lowering correctness. The
  main theorem is `lowerGate_correctness`.

The final role of this layer is to connect high-level semantic correctness to
the actual lowered circuit representation.

### `Implementation/GateCount/` — cost

`GateCount` proves asymptotic size bounds for the lowered circuits, over the
cost model `Framework/Gatecount/` defines.

Important parts:

- `Definitions.lean` defines the concrete Shor cost model, comparison rates,
  and the bound predicates `PhaseProductGateCountBound`,
  `CPhaseProductGateCountBound` and `QFTGateCountBound`.
- `PhaseProduct/` proves the PhaseProduct gate-count theorem. `Lemmas.lean`
  contains the recurrence, width-growth, and controlled-comparison machinery.
  `Main.lean` proves `phaseProductGateCountBound_of_programOK` and
  `cPhaseProductGateCountBound_of_programOK`.
- `QFT_GateCount.lean` proves that QFT lowering is bounded assuming the
  PhaseProduct bound. Main endpoints are `qftGateCountBound_of_phaseProduct`
  and `qftGateCountBound_of_programOK`.
- `Shor_GateCount.lean` assembles the component costs for controlled modular
  multiplication, modular exponentiation, order finding, and the final Shor
  rate. Main endpoints are `shorGateCountBound_of_components`,
  `shorGateCountBound_of_programOK`, `exists_shorGateCountBound`, and
  `exists_k_shorGateCountBound_of_programOK`.

The final gate-count result is that for every positive epsilon and delta, there
exists a PhaseProduct program such that the lowered Shor order-finding circuit
satisfies the asymptotic `shorGateRate epsilon n`, i.e. the intended
`O(n^(2+epsilon))` bound.

### `Implementation/Shor/` — the correctness assembly

`Shor/` is the top-level correctness assembly, and `Shor/Main.lean` is where
the exact-lowering branch, the approximation branch and the classical
postprocessing branch meet.

The setup records it works over:

- `ShorOrderFindingInstance` (`Framework/Contract.lean`), the
  arithmetic/register data for order finding.
- `ShorLoweringSetup` (`Framework/ToomCookTable.lean`), the assumptions needed
  to lower the chosen circuit. It moved out of this folder, gained the
  interpolation points as a field, and became the submission record itself —
  see "The submission boundary" below.
- `ShorFactoringInstance` (`Shor/Spec/Setup.lean`), the classical factoring
  setup.
- `ShorCleanInput` (`Shor/Spec/Cleanliness.lean`), the clean-register predicate
  for initial states.
- `ShorApproxSetup` (`Shor/Spec/Setup.lean`), the complete approximate-circuit
  setup used by the final statements.

The circuits themselves are in `Shor/Circuit/OrderFinding.lean`
(`orderFindingApprox` and its lowered form `orderFindingApproxLow`).

Important results include:

- `ShorApproxSetup.toIdealOrderFindingInput` (`Shor/Proofs/Setup.lean`), which
  extracts the ideal input assumptions from the approximate setup.
- `ShorApproxSetup.prepared_state_valid` (`Shor/Proofs/Correctness.lean`), which
  proves the prepared state satisfies the validity predicate needed by modular
  exponentiation.
- `Shor_correct_approx_uniform` (`Shor/Proofs/Correctness.lean`), which packages
  correctness of approximate order finding against the ideal behavior with a
  uniform error bound, and `Shor_correct_approx_lowered_uniform`
  (`Shor/Main.lean`), its lowered counterpart.
- `Shor_correct` (`Shor/Proofs/NaiveShor/Correctness.lean`), the ideal
  order-finding theorem, proved over the analysis in
  `Shor/Math/OrderFindingAnalysis.lean`.
- `shors_probability_bound` (`Framework/Math/Factoring_Reduction/ProbabilityBound.lean`),
  which states the postprocessing success probability bound.
- `Shor_end_to_end_factoring` (`Shor/Main.lean`), which combines order finding
  with the classical factoring reduction.

`Shor_correct` and every other theorem in the development are fully proved — no
proof anywhere in the codebase uses `sorry`, and `#print axioms` on the headline
theorems reports only `propext`, `Classical.choice`, and `Quot.sound`.
(`grep -rn sorry FastMultiplication` is not empty, but every hit is in
`Submission/Audit.lean`, which deliberately writes one so it can demonstrate
that `#assert_axioms` rejects it; the resulting warning is captured by
`#guard_msgs` rather than emitted.)

### `Implementation/Reference/` — the concrete instance

`Reference/` makes every remaining choice concrete — physical register layout
(`ReferenceLayout.lean`), the precision schedule (`ReferencePrecision.lean`),
the readiness side conditions (`ReferenceReadiness.lean`) — and turns an
admissible table into a circuit family: `referenceProgramAt` and
`referenceProgramAt_success` (`ReferenceShorImplementation.lean`), packaged as
a `ShorImplementation`. `Reference2048Headline.lean` instantiates
`exists_shorGateCountBound` at the 2048-bit benchmark. The construction is
generic in the table, which is what makes the four side conditions a complete
acceptance test.

## The submission boundary

The tail of the development has a second organising split, later than the
identities/lowering one described above and orthogonal to it: the line
between *the rules* and *a construction satisfying them*.

| where | what |
| --- | --- |
| `Framework/ToomCookTable.lean` | The rules, implementation-free. The table language (`Register`, `State`, `Prog`, `run?`), the point-row vocabulary (`expectedRow`, `ProgConsumesPtsSafe`), the interpolation vocabulary (`interpMatrix`, `GoodToomCookPoints`), and the record `ShorLoweringSetup` / `ShorSubmission` that bundles them. Imports Mathlib and nothing else, so the specification can be read without the construction. |
| `Framework/Contract.lean` | The semantic contract: `probability_of_success`, `ShorImplementation`. Formerly `Framework/Submission.lean`; renamed because it is now the framework's *internal* contract, not what a submitter writes. |
| `Implementation/` | The Toom-Cook construction. Every file that used to define one of the moved definitions now imports `Framework/ToomCookTable.lean` instead; the lemmas about them, the point generator and the compiler all stayed. |
| `Implementation/Reference/` | `setup ↦ referenceProgramAt`, and `referenceProgramAt_success` — generic in the setup, which is what makes the four side conditions a complete acceptance test. |
| `Submission/` | The public surface: `Decide.lean` (the four conditions, decidable *in the kernel*; `Framework/` + Mathlib only), `Audit.lean` (`#assert_axioms`, `Lean` only), `Correct.lean` (the fixed precision and the certificate), `Score.lean` (the declared bound and a computable trial count), `Template.lean` (**the submitter's file**: the table and its C1–C4 proofs), `Check.lean` (the acceptance check: the axiom audit, the IR extraction, the evaluation tier, the certificate) and `Main.lean` (the printer). |
| `Emit/` | `setup ↦ IR`: reflection over the verified construction, producing a `Doc` a resource estimator prices. |

The consequence worth stating plainly: correctness is proved *once*, generic
in the table. There is no per-submission correctness obligation, which is the
whole reason the challenge was narrowed to the table.

What a submission does owe is C1–C4 on its own table, and those are the
submitter's proofs rather than the template's. `Template.lean` holds `k`,
`pts`, `ops` and the `ShorSubmission` record with every field proved by
`decide +kernel`; `Check.lean` then runs `#assert_axioms Submission.setup`,
which fails the build unless the finished term's axioms lie inside `propext`,
`Classical.choice`, `Quot.sound`. That is what rules out `native_decide`
(`Lean.ofReduceBool`), `sorry` (`sorryAx`) and a submitter's own `axiom`, and
it is what makes "kernel-checked" a checked claim rather than a documented
intention. C2 would be the one condition too expensive to reduce — a
determinant over `(2k-1)!` permutations — except that the interpolation
matrix is a projective Vandermonde, so `Submission/Decide.lean` proves C2
*equivalent* to the points being pairwise distinct as projective points and a
quadratic scan discharges it at every supported `k`.

The IR tier is different in kind and is deliberately left so: `Check.lean`
pins `Shor.Reflect.submissionChecks` with `native_decide`, which is
evaluation at sampled widths rather than a theorem. Those are repo-owned
`example`s about the *extractor*, not fields of `setup`, so they never enter
the audit above.

## Big Picture

The repo proves two complementary things:

1. Correctness: the generated and lowered circuits implement the intended high-level Shor/order-finding behavior, with quantitative approximation control for modular arithmetic.
2. Cost: the lowered implementation has the asymptotic gate-count behavior expected from fast PhaseProduct recursion, culminating in `exists_shorGateCountBound` and `exists_k_shorGateCountBound_of_programOK`.

The central architectural split is that `Implementation/{PhaseProduct,QFT,ModularExponentiation}/Proofs/` prove high-level gate identities, while `Implementation/{PhaseProduct,QFT}/Proofs/Lowering/` and `Implementation/Shor/Proofs/Lowering.lean` prove that those high-level gates lower correctly. That separation keeps the mathematical circuit reasoning independent from the engineering details of recursive workspace allocation and low-level gate syntax.
