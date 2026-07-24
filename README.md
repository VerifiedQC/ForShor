# ForShor

[![Lean](https://img.shields.io/badge/Lean-v4.28.0-blue)](https://leanprover.github.io/)
[![Mathlib](https://img.shields.io/badge/mathlib4-required-9cf)](https://github.com/leanprover-community/mathlib4)
[![License](https://img.shields.io/badge/license-Apache_2.0-green)](LICENSE)

A formal verification of **Shor's algorithm** in Lean 4 — including its **gate-count complexity**.

The development verifies an implementation of order finding built on fast (Toom-Cook) multiplication, from a high-level gate language down to a low-level abstract machine, and proves that the whole circuit uses only `O(n^(2+ε))` gates.

## Main results

**Correctness** (`FastMultiplication/ShorVerification/ShorCorrectness.lean`): the ideal order-finding circuit recovers the multiplicative order with at least the standard inverse-polylogarithmic probability.

```lean
theorem Shor_correct (T : ℕ → ℕ) (inst : ShorOrderFindingInstance)
    (ψ0 : qs.State) (hψ0 : ‖ψ0‖ = 1) :
    probability_of_success ... ≥ κ / (Nat.log2 inst.N : ℝ)^4
```

**Gate count** (`FastMultiplication/ShorVerification/GateCount/Shor_GateCount.lean`): for every `ε > 0` there is a recursion parameter `k` such that the compiled Shor circuit satisfies the gate-count bound `O(n^(2+ε))`.

```lean
theorem exists_shorGateCountBound (qs : QSemantics) ... (ε δ : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ k : ℕ, ∃ hk : 1 < k, ∃ ops : Prog k,
      PhaseProductProgramOK k hk ops ∧ ShorGateCountBound qs ε δ k hk ops
```

### Status

All components are proved: phase-product compilation, QFT decomposition, lowering correctness, modular-exponentiation error bounds, and the full gate-count stack. Two statements are still `sorry`:

- `Shor_correct` — the final assembly of the top-level success-probability bound.
- `CF_recovers_denominator` — the classical continued-fraction postprocessing fact.

## Repository layout

| Directory | Contents |
| --- | --- |
| `FastMultiplication/ShorVerification/Basic.lean` | Semantic core: registers, the high-level `Gate` language, `QSemantics`, and general semantic facts. |
| `FastMultiplication/ShorVerification/MathBackbone/` | Symbolic source programs and table generation, Toom-Cook interpolation algebra, and the classical Shor/order-finding math. |
| `FastMultiplication/ShorVerification/AlgorithmCorrectness/` | Phase-product compiler correctness, the QFT split identity, and modular-multiplication/exponentiation error bounds. |
| `FastMultiplication/ShorVerification/AbstractMachine/` | The low-level `LowGate` machine, recursive lowering from `Gate`, and whole-program lowering correctness. |
| `FastMultiplication/ShorVerification/GateCount/` | Gate-count definitions and bounds for the phase product, the QFT, and the complete Shor circuit. |
| `FastMultiplication/ShorVerification/ShorCorrectness.lean` | Order-finding circuits, the measurement interface, and the top-level theorem `Shor_correct`. |
| `docs/` | An interactive visualization of the proof architecture. |

For a detailed file-by-file guide, see [ARCHITECTURE.md](ARCHITECTURE.md).

## Proof architecture

The dependency story in one paragraph: `MathBackbone/Table_Generation` produces the symbolic source programs and phase-point structure, and `MathBackbone/Toom_Cook_formula.lean` supplies the interpolation algebra. `AlgorithmCorrectness/PhaseProduct` uses both to prove the high-level Toom-Cook phase identity and the correctness of the compiled signed phase-product circuit; `AlgorithmCorrectness/QFT` proves the QFT split identity. `AbstractMachine` lifts these to the full `Gate` language via the lowering theorems. Finally, the lowering results, the modular-exponentiation bounds, and the classical math in `MathBackbone/ShorAlgorithm.lean` feed into `ShorCorrectness.lean`, while `GateCount/` bounds the size of the compiled circuit.

You can explore the proof graph interactively:

```sh
cd docs && python3 -m http.server 8765
# then open http://localhost:8765
```

## Building

The project uses Lean `v4.28.0` (pinned in `lean-toolchain`) and depends on [mathlib4](https://github.com/leanprover-community/mathlib4). With [elan](https://github.com/leanprover/elan) installed:

```sh
lake exe cache get   # fetch prebuilt mathlib oleans
lake build
```

## License

Released under the Apache License 2.0. See [LICENSE](LICENSE).
