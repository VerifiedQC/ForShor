# `Implementation/ModularExponentiation/`

This folder implements and proves correct **Algorithm 1**: in-place
classical-quantum modular multiplication and, by recursing over the exponent
register, modular exponentiation —

```text
|x⟩ |0⟩  |->  |c·x mod N⟩ |0⟩
```

approximated by a fractional-load-and-cleanup circuit (QFT-based phase
products, an inverse-QFT comparator, and a constant-arithmetic subtraction),
with a quantitative error bound uniform in the precision parameter `η`.

The folder is organized in layers (below). **Every import is "justified":** a
file may only import another file if it directly uses a declaration that
file defines — never a declaration it merely re-exports transitively.
`scripts/check_modexp_layers.sh` (repo root) enforces both the layer order
and the absence of umbrella files (a file that only imports and declares
nothing of its own).

## Layer order

```
Math  <  Circuit  <  Lowering  <  Spec  <  Proofs  <  Main
```

A file may import its own folder or any folder to its left.

Reading order for newcomers: start at `Main.lean`, then follow imports
*backwards* — `Spec/Assertions.lean` for what is claimed, `Proofs/ModExp.lean`
for how the claim is proved, and outward from there into `Proofs/`, `Spec/`,
`Lowering/`, `Circuit/`, `Math/` as needed. The one-line descriptions below
are grouped in dependency order (lowest layer first) to match that traversal.

## `Math/` — pure math, no framework/register dependencies

| File | Purpose |
|---|---|
| `QPETail.lean` | The semantics-free numerical core of Algorithm 1's Step-1 QPE tail-mass bound: the finite QPE kernel `qpeKernel`, its chord-bound estimate, and the floor-shell summation argument giving the closed-form tail bound `qpeKernel_bad_mass_le_grid_ratio`. See its own README. |

## `Circuit/` — the concrete Algorithm-1 circuit

Internal order: `Workspace → CmpLtNW → Steps → ModExp` (each may import the
ones before it).

| File | Purpose |
|---|---|
| `Workspace.lean` | The static workspace structures the circuit needs: `ModMulCoreLayout` (register/qubit-disjointness layout for one core invocation), `ModMulCircuitWorkspaceOK` (+ the concrete Step 1/2/5 phase-product workspaces it carves), `cmpLtNWWidth`/`CmpLtNWWorkspace` (Step 4's comparator workspace), and `ConstArithmeticWorkspace` (Step 3's concrete lowering workspace). |
| `CmpLtNW.lean` | The concrete Step-4 comparator circuit (`cmpLtNW`): a fast constant multiplication into scratch, the signed difference against the data register, and copying its sign bit to the flag. |
| `Steps.lean` | The reusable high-level gates (`IQFT`, `H_reg`), the five circuit steps (`step1`…`step5`, `step5Constant`), and the controlled in-place modular-multiplication core (`CmodMulInPlaceCore`) they assemble. |
| `ModExp.lean` | The ideal specification (`tbits`, `modExpIdealSteps`, `modExpIdeal'`) and the approximate modular-exponentiation recursion over a list of control qubits (`ModExpLayout`, `ModExpArithmeticOK`, `modExpApproxStepsValid`, `modExpApproxValid`), built from `CmodMulInPlaceCore`. |

## `Lowering/` — turning typed source gates into `LowGate` primitives

| File | Purpose |
|---|---|
| `ConstArithmetic.lean` | Concrete `LowGate` lowering of Step 3's typed `Gate.CmpGeConst`/`Gate.CSubConst`, using one reserve qubit of `scratch` as the signed constant `-1` (`lowerCmpGeConst`, `lowerCSubConst`). |

## `Spec/` — the public specification surface

| File | Purpose |
|---|---|
| `Precision.lean` | The concrete precision schedule for Algorithm 1 (`algorithm1ExtraBits`, `Algorithm1Precision`) and the per-core norm error scale used by the hybrid bound (`stepErr`). |
| `Validity.lean` | The clean-input predicates for the valid-input subspace the approximation theorems work on (`GoodModMulBasisInput`, `ValidModMulState`, `GoodAlgorithm1BasisInput`, `ValidAlgorithm1State`), and the state-level cleanliness predicates consumed by the two concrete constant-arithmetic lowerers (`ConstArithmeticCleanBasis`, `CSubConstCleanBasis`, `CmpGeConstCleanState`, `CSubConstCleanState`). |
| `Config.lean` | Compact configuration records so the bound files don't repeatedly thread the modulus, registers, precision proof, workspace proof, layout proof, and coprimality hypotheses: `Algorithm1Env`, `ModExpConfig` (+ `approxGate`/`idealGate`/`ValidUnitState`), `ModMulConfig` (+ `approxGate`/`idealGate`/`ValidState`/`ValidUnitState`). |
| `Assertions.lean` | `ModExpApproxValidDistUniform` — the final claim: a single `η`-independent constant `K` bounds the approximate-vs-ideal modular-exponentiation distance uniformly over valid unit states. Proved in `Main.lean`. |

## `Proofs/` — everything below is proof-only; nothing outside `Proofs/`/`Main.lean` may import it

See `Proofs/README.md` for the full breakdown, including the Algorithm-1
proof outline (how Steps 1–5's error analysis is split across files).

| File | Purpose |
|---|---|
| `Model.lean` | The shared analysis vocabulary: staged gates (`U1`/`U2`/`U34`/`U5`/`stagedGate`), the QPE target/good-label definitions, `Alg1Trace`, and the closed-form Step-1/Step-5 phase-coefficient chain. |
| `Core.lean` | Basic facts about the model: ideal-gate exactness/validity-preservation, Step-3/4 basis-ket semantics (`eval_step3_clean_ket`, `eval_step4_cancels_ket`), and capacity/coprimality side facts. |
| `CmpLtNW.lean` | Exact correctness of the concrete Step-4 comparator circuit (`eval_cmp_lt_nw_ket`). |
| `ConstArithmetic.lean` | Correctness of the concrete Step-3 constant-arithmetic lowering (`evalL_lowerCmpGeConst`, `evalL_lowerCSubConst`). |
| `Algorithm1Expansion.lean` | Expands `U1` on valid basis inputs, building the finite `Alg1Trace` (`alg1_trace_of_valid`) the quantitative bounds are stated over. |
| `Step1QPE.lean` | Proves the QPE tail estimate for the fractional load (`alg1_qpe_tail_basis_uniform`), on top of `Math/QPETail.lean`. |
| `Step1Bound.lean` | Lifts the basis-state QPE estimate to arbitrary valid unit states, covering both the Step-1 load and the Step-5 cleanup (`alg1_qpe_tail_uniform`) — why Step 5 has no separate file. |
| `Step2Bound.lean` | The quantitative Fourier stability bound for Step 2 (`alg1_step2_good_label_branch_uniform`): one retained label first, then orthogonal work-label fibers recombined. |
| `Step34Exact.lean` | Exactness (not approximation) of Steps 3 and 4 on the reference state (`alg1_step34_reference_exact`). |
| `FinalModMul.lean` | Combines the Step 1/2/5 error bounds, Step 3/4 exactness, and a three-link triangle inequality into the single-call bound (`modMul_approx_valid_dist_uniform`). |
| `ModExp.lean` | Lifts the single-call theorem across all exponent/control qubits into the full modular-exponentiation bound (`modExpApprox_valid_dist_uniform`). |

## `Main.lean`

Proves the folder's public theorem, `modExpApprox_correct`, packaging
`Spec.Assertions.ModExpApproxValidDistUniform` from
`Proofs.ModExp.modExpApprox_valid_dist_uniform`. Imports only `Spec.Assertions`
and `Proofs.ModExp` — every other dependency is transitive through those two.
