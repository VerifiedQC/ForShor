# Architecture: a file-by-file guide

This document walks through the Lean development in detail. For an overview and build instructions, see the [README](README.md).

# FastMultiplication Shor Verification

This repository is a Lean 4 verification project for a fast-multiplication-based implementation of the phase-product, QFT, modular multiplication, modular exponentiation, and order-finding pieces used in Shor's algorithm.

The development has six main pieces:

1. `FastMultiplication/ShorVerification/Basic.lean` defines the shared register, gate, and quantum-semantics vocabulary.
2. `MathBackbone/` proves the classical algebra and number theory used by the circuits.
3. `AlgorithmCorrectness/` proves high-level circuit identities and approximation bounds.
4. `AbstractMachine/` proves that the high-level gates lower correctly to the low-level abstract machine.
5. `GateCount/` proves asymptotic gate-count bounds for the lowered circuits.
6. `ShorCorrectness.lean` assembles the algorithmic correctness story for Shor/order finding.

`MathBackbone` supplies the mathematics, `AlgorithmCorrectness` proves the high-level circuit equations, `AbstractMachine` proves the lowering from those high-level gates to low-level gates, and `GateCount` proves that the lowered circuits have the intended asymptotic size.



## Core Definitions in `Basic.lean`

`FastMultiplication/ShorVerification/Basic.lean` is the common language of the whole verification. It deliberately avoids committing to one concrete Hilbert-space implementation. Instead, it defines registers, gate syntax, and abstract semantic interfaces that later files can instantiate or reason against.

### Registers

`Reg` is an ordered list of distinct physical qubits. The order is logical: position `i` in the list is bit `i` of the encoded number. This is why registers do not need to be contiguous intervals of physical qubit indices.

Important register definitions:

- `Reg.qubits` stores the physical qubit list.
- `Reg.nodup` proves the list has no duplicate qubits.
- `Reg.width` and `regSize` are the logical width of a register.
- `ASize r` is `2 ^ regSize r`, the number of basis values representable by `r`.
- `Reg.get r i` returns the physical qubit used for logical bit `i`.
- `Reg.singleton`, `Reg.empty`, and `Reg.interval` build common registers.
- `Reg.take` and `Reg.drop` split a register by logical position.
- `Disjoint a b` means two registers share no physical qubits.
- `Reg.append left right h` concatenates two disjoint registers into one ordered register.
- `SplitPoint`, `splitLeft`, and `splitRight` package legal register splits.

These definitions are fundamental because every later theorem needs to talk about which qubits a circuit reads or writes. Using explicit lists rather than intervals is what lets the development support non-contiguous layouts and workspace carved out of reserves.

### `RegEncoding`

`RegEncoding Basis` is the basis-level interface for reading and writing finite registers inside an abstract basis type.

It provides:

- `toNat r b`, the natural number encoded by register `r` in basis state `b`.
- `writeNat r v b`, the basis state obtained by writing value `v` into `r`.
- `bit q b`, the Boolean value of physical qubit `q` in `b`.
- bounds such as `toNat_lt_ASize`.
- read-after-write laws such as `toNat_writeNat_of_lt` and `writeNat_toNat`.
- locality laws saying writes outside a register do not affect it.
- commutation laws for writes to disjoint registers.
- split and append laws explaining how encoded values decompose across register splits.
- `basis_ext`, which says a basis state is determined by all its physical bits.

This class exists because the verification should not depend on one concrete representation of computational basis states. Later proofs need a reliable interface for register reads and writes, but they should be reusable for any basis type satisfying the expected bit-level laws.

### Extended Registers

`ExtReg` is an active register plus an ordered reserve of owned but inactive workspace qubits.

Important definitions:

- `ExtReg.active` is the currently meaningful register.
- `ExtReg.reserve` is inactive workspace that can be activated later.
- `ExtReg.width` is the active width.
- `ExtReg.capacity` is the number of reserve bits available.
- `ExtReg.CanGrow e n` says the reserve has at least `n` bits.
- `ExtReg.newBits e n` selects the next `n` reserve bits.
- `ExtReg.remainingReserve e n` leaves the rest of the reserve.
- `ExtReg.grow e n` appends the next `n` reserve bits to the active register.
- `ExtReg.ownedQubits` lists both active and reserved qubits.
- `ExtReg.ActiveDisjoint`, `ExtReg.OwnedDisjoint`, and `ExtReg.CtrlDisjoint` express the disjointness conditions used by workspace proofs.

Extended registers are needed because many lowerings allocate temporary sign or carry bits. The proof must distinguish active data from reserved workspace, and must prove that growing a register does not use qubits from another register.

### Numeric Decoding and Freshness

`Basic.lean` defines unsigned and signed interpretations of register contents:

- `ExtReg.toNat e b` reads the active portion of an extended register as a natural number.
- `tcDecodeWidth w n` decodes a `w`-bit natural as a two's-complement integer.
- `extToInt e b` reads an extended register as a signed integer.
- `tcModWidth`, `tcWrapInt`, and `tcModExt` describe wrapping modulo a fixed bit width.
- `signedMin`, `signedMax`, and `FitsSignedWidth` describe the signed range representable at width `w`.

Freshness predicates record clean workspace:

- `FreshZero r b` says an ordinary register is all zero in basis state `b`.
- `ExtReg.FreshFor e n b` says the next `n` reserve bits of `e` are zero.

These definitions are essential for extension and deallocation gates. They let the proof state that temporary bits are initially clean, become active when needed, and can later be removed without changing the represented value.

### Gate Language

`Gate` is the high-level circuit language used by the algorithmic proofs.

It contains structural gates:

- `Gate.id`
- `Gate.seq`
- `Gate.adj`

It contains elementary and structured gates:

- `Gate.H` and `Gate.X`
- `Gate.QFT`
- `Gate.RadixReverse`
- `Gate.SignedPhaseProd`
- `Gate.CSignedPhaseProd`
- `Gate.Prim` for opaque reversible arithmetic primitives

It contains arithmetic and workspace gates:

- `Gate.ShiftL`, `Gate.ShiftR`, `Gate.Negate`, `Gate.AddScaled`
- `Gate.zeroExtend`, `Gate.signExtend`
- `Gate.zeroDealloc`, `Gate.signDealloc`

The high-level gate language is intentionally more structured than the low-level machine. `AlgorithmCorrectness` proves identities about this language, while `AbstractMachine` later lowers it to `LowGate`.

### PhaseProduct Workspace Macros

`Gate.PhaseProdWorkspace x z` records the temporary reserves and disjointness facts needed to implement an unsigned phase product using a signed phase product on one-bit-grown registers.

Important definitions:

- `PhaseProdWorkspace.xExt` and `PhaseProdWorkspace.zExt` package the operands as extended registers.
- `PhaseProdWorkspace.Clean` says the one-bit reserves are initially zero.
- `PhaseProdWorkspace.ControlDisjoint` says a control qubit is outside every qubit touched by the unsigned-to-signed bridge.
- `Gate.PhaseProdUsing` performs zero-extension, a signed phase product, and zero-deallocation.
- `Gate.CPhaseProdUsing` is the controlled version.

These macros exist because the algorithm naturally uses unsigned operands, while the recursive phase-product compiler is most convenient over signed two's-complement operands.

### QFT Phase Helpers

The QFT helper definitions are:

- `qftPhi m = 2*pi / 2^m`, the phase angle used by QFT decomposition.
- `omega N`, a primitive complex `N`-th root of unity.
- `omegaPow N k`, powers of that root.
- `qftPhase N x y`, the scalar `omega_N^(x*y)`.

These definitions isolate the analytic phase factors used in QFT and phase-product identities.

## Classes in `Basic.lean`

### `RegEncoding`

`RegEncoding` was described above because it is as fundamental as `Reg` itself. It exists to decouple bit-level register reasoning from a concrete basis representation.

Without this class, every theorem would need to know how basis states are implemented. With it, the rest of the development only assumes the expected laws of register reads, writes, bits, splits, and disjoint writes.

### `QSemantics`

`QSemantics` is the abstract Hilbert-space semantics of the high-level gate language.

It supplies:

- a basis type `Basis`.
- a state space `State` with normed additive group and complex inner-product-space structure.
- `ket : Basis -> State`.
- `eval : Gate -> State -> State`.
- laws for identity, sequencing, linearity, adjoints, and inner-product preservation.
- orthonormality/injectivity facts for kets.
- an induction principle saying states can be reasoned about from `0`, sums, scalar multiples, and basis kets.

The project proves circuit equations in any quantum model satisfying these axioms.

### `QFTSemantics`

`QFTSemantics qs` specifies the behavior of `Gate.QFT` and its adjoint on basis kets, including the special zero-width and one-width cases.

It exists because QFT is a structured gate whose mathematical behavior is much richer than a primitive one-qubit gate. Keeping QFT facts in their own class lets files that do not reason about QFT avoid carrying those assumptions.

### `HadamardSemantics`

`HadamardSemantics qs` specifies the basis action of a one-qubit Hadamard gate.

It exists because Hadamards are used both directly and in register-wide initialization. Separating this class keeps the elementary gate facts modular.

### `PauliXSemantics`

`PauliXSemantics qs` specifies the basis action of `Gate.X`, including a helper law for applying `X` to the low qubit of a zero register to initialize the register to one.

It exists because order finding needs to prepare the `y = 1` state, and that preparation should be proved from the semantics of `X` rather than baked into the algorithm.

### `RegisterHadamardSemantics`

`RegisterHadamardSemantics qs` describes the result of applying Hadamards across a whole register as a finite superposition over all register values.

It exists because many proofs need the existence of a register-wide superposition without unfolding every one-qubit Hadamard interaction manually.

### `RadixReverseSemantics`

`RadixReverseSemantics qs` specifies the basis action of `Gate.RadixReverse` after a QFT split.

It exists because the QFT decomposition ends with a structured register permutation. That permutation has a clean mathematical description in terms of split halves, and it deserves a separate semantic interface.

### `PhaseSemantics`

`PhaseSemantics qs` specifies signed and controlled signed phase-product gates:

- `Gate.SignedPhaseProd phi x z` multiplies a basis ket by `exp(phi*i*extToInt(x)*extToInt(z))`.
- `Gate.CSignedPhaseProd ctrl phi x z` does the same only when the control bit is true.

This class exists because phase products are the central expensive operation in the fast multiplication construction. The recursive compiler and gate-count proofs are built around replacing these high-level phase gates with cheaper structured lowerings.

### `ExtensionSemantics`

`ExtensionSemantics qs` specifies zero-extension, zero-deallocation, sign-extension, and sign-deallocation.

It exists because extended registers change which owned bits are active. The semantics must say that zero-extension is value-preserving on clean reserves, and sign-extension preserves the signed interpretation while keeping disjoint registers unchanged.

### `ArithmeticSemantics`

`ArithmeticSemantics qs` specifies the exact or wrapped behavior of structured arithmetic gates:

- `ShiftL`
- `ShiftR`
- `Negate`
- `AddScaled`

It exists so the phase-product compiler can reason about arithmetic transformations on signed integer interpretations without depending on a concrete reversible circuit implementation.

### `GateSemanticsFacts`

`GateSemanticsFacts qs` bundles the gate-family semantic classes:

- `QFTSemantics`
- `PhaseSemantics`
- `ExtensionSemantics`
- `ArithmeticSemantics`
- `RadixReverseSemantics`
- `HadamardSemantics`
- `PauliXSemantics`
- `RegisterHadamardSemantics`

It also adds `eval_Hreg_zero_eq_QFT`, which connects register-wide Hadamard preparation of zero to QFT of zero.

This class exists as a convenience boundary. Large correctness theorems usually need nearly all gate-family facts, and passing one bundled class keeps theorem statements readable.

## Folder Guide and Main Results

### `MathBackbone/`

`MathBackbone` contains the non-circuit mathematics needed by the verification. It is the place for source-level arithmetic programs, Toom-Cook interpolation algebra, recurrence-solving facts, and classical Shor/factoring probability arguments.

Important parts:

- `Table_Generation/` defines a symbolic program language and synthesizes interpolation-table programs. Its main results show that generated programs are well formed, return to the original symbolic state, and cover the required phase-product interpolation points. Important names include `genOpsWithProduct_returns_to_original`, `genOpsWithProduct_PhaseProductCoverage`, and `phaseProductCoverage_peel_block`.
- `Toom_Cook_formula.lean` proves the interpolation algebra used by phase product. The key theorem is `interpCoeff_correct`.
- `MasterTheoremProof.lean` proves a shifted recurrence theorem used by the gate-count proof. The key endpoint is `shifted_master_theorem_exact_family`.
- `Factoring_Reduction/` contains the classical number-theoretic reduction/probability material behind Shor's postprocessing. Important probability lemmas include `general_unsuccessful_bound`.
- `ShorDefinition.lean` contains classical definitions around Shor/order finding used by the top-level file.

The final role of this folder is to provide the mathematical facts that the circuit proofs are allowed to call.

### `AlgorithmCorrectness/`

`AlgorithmCorrectness` is mostly about high-level circuit identities. It proves that the structured `Gate` circuits implement the desired mathematical transformations. It is not primarily the lowering layer.

That distinction matters: the files here prove identities about high-level gates such as QFT, PhaseProduct, modular multiplication, and modular exponentiation. The proofs that those high-level gates lower correctly to the low-level abstract machine live in `AbstractMachine/`.

Important parts:

- `PhaseProduct/` proves correctness of the generated phase-product compiler. `Core.lean` defines the layout, width scanner, annotations, and compiler state. `WidthSoundness.lean`, `AllocationCorrectness.lean`, `BodyCorrectness.lean`, and `InterpolationCorrectness.lean` prove the main ingredients. `CompilationCorrectness.lean` assembles them into `eval_compileOpsToSignedGate_correct` and the controlled analogue `eval_compileOpsToCSignedGate_correct`.
- `QFT/Decomposition.lean` proves the high-level split identity for QFT: a QFT over a register can be expressed through right-half QFT, a phase product, left-half QFT, and radix reversal. The main result is the QFT split/decomposition theorem in that file.
- `ModMulBounds/` develops the approximation analysis for modular multiplication and modular exponentiation. The main modular-multiplication endpoint is `modMul_approx_valid_dist_uniform`. The modular-exponentiation endpoint is `modExpApprox_valid_dist_uniform`.

The final role of this folder is to prove that the high-level algorithmic circuits are mathematically correct, or close to the ideal circuit in the approximate modular-arithmetic branch.

### `AbstractMachine/`

`AbstractMachine` contains the low-level target language and the lowering correctness story.

Important parts:

- `LowGate.lean` defines the low-level gate language `LowGate`.
- `PhaseProductLoweringCorrectness/` defines plan-directed lowerings for signed and controlled signed phase products, workspace/readiness predicates, and semantic correctness of recursive lowering. Main endpoints include `evalL_lowerGateRec_correct`, `standardSignedPhaseLoweringPlan_ready`, and `standardCSignedPhaseLoweringPlan_ready`.
- `QFTLoweringCorrectness/` defines QFT workspace requirements and proves correctness/readiness of recursive QFT lowering. Main endpoints include `evalL_lowerQFTPlan`, `standardQFTLoweringPlan_ready_and_clean`, and `evalL_lowerQFT`.
- `WholeProgramCorrectness.lean` defines `GateWorkspaceOK`, the recursive `lowerGate` function from high-level `Gate` to `LowGate`, and proves whole-program lowering correctness. The main theorem is `lowerGate_correctness`.

The final role of this folder is to connect high-level semantic correctness to the actual lowered circuit representation.

### `GateCount/`

`GateCount` proves asymptotic size bounds for the lowered circuits.

Important parts:

- `Definitions.lean` defines the low-gate cost model, concrete Shor cost model, comparison rates, and bound predicates such as `PhaseProductGateCountBound`, `CPhaseProductGateCountBound`, and `QFTGateCountBound`.
- `PhaseProduct/` proves the PhaseProduct gate-count theorem. `Lemmas.lean` contains the recurrence, width-growth, and controlled-comparison machinery. `Main.lean` proves `phaseProductGateCountBound_of_programOK` and `cPhaseProductGateCountBound_of_programOK`.
- `QFT_GateCount.lean` proves that QFT lowering is bounded assuming the PhaseProduct bound. Main endpoints are `qftGateCountBound_of_phaseProduct` and `qftGateCountBound_of_programOK`.
- `Shor_GateCount.lean` assembles the component costs for controlled modular multiplication, modular exponentiation, order finding, and the final Shor rate. Main endpoints are `shorGateCountBound_of_components`, `shorGateCountBound_of_programOK`, `exists_shorGateCountBound`, and `exists_k_shorGateCountBound_of_programOK`.

The final gate-count result is that for every positive epsilon and delta, there exists a PhaseProduct program such that the lowered Shor order-finding circuit satisfies the asymptotic `shorGateRate epsilon n`, i.e. the intended `O(n^(2+epsilon))` bound.

### `ShorCorrectness.lean`

`ShorCorrectness.lean` is the top-level correctness assembly file.

It defines:

- `ShorOrderFindingInstance`, the arithmetic/register data for order finding.
- `ShorLoweringSetup`, the assumptions needed to lower the chosen circuit.
- `ShorFactoringInstance`, the classical factoring setup.
- `ShorCleanInput`, the clean-register predicate for initial states.
- `ShorApproxSetup`, the complete approximate-circuit setup used by the final statements.

Important results include:

- `ShorApproxSetup.toIdealOrderFindingInput`, which extracts the ideal input assumptions from the approximate setup.
- `ShorApproxSetup.prepared_state_valid`, which proves the prepared state satisfies the validity predicate needed by modular exponentiation.
- `Shor_correct_approx_uniform`, which packages correctness of approximate order finding against the ideal behavior with a uniform error bound.
- `shors_probability_bound`, which states the postprocessing success probability bound.
- `Shor_end_to_end_factoring`, which combines order finding with the classical factoring reduction.

This file is where the exact-lowering branch, approximation branch, and classical postprocessing branch meet. In the current repository state, Lean reports that `Shor_correct` itself still uses `sorry`; the surrounding approximate and gate-count developments are organized as separate supporting branches.

## Big Picture

The repo proves two complementary things:

1. Correctness: the generated and lowered circuits implement the intended high-level Shor/order-finding behavior, with quantitative approximation control for modular arithmetic.
2. Cost: the lowered implementation has the asymptotic gate-count behavior expected from fast PhaseProduct recursion, culminating in `exists_shorGateCountBound` and `exists_k_shorGateCountBound_of_programOK`.

The central architectural split is that `AlgorithmCorrectness` proves high-level gate identities, while `AbstractMachine` proves that those high-level gates lower correctly. That separation keeps the mathematical circuit reasoning independent from the engineering details of recursive workspace allocation and low-level gate syntax.
