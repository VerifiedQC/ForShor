# ForShor

[![Lean](https://img.shields.io/badge/Lean-v4.28.0-blue)](https://leanprover.github.io/)
[![Mathlib](https://img.shields.io/badge/mathlib4-required-9cf)](https://github.com/leanprover-community/mathlib4)
[![License](https://img.shields.io/badge/license-Apache_2.0-green)](LICENSE)

A formal verification of **Shor's algorithm** in Lean 4 — including its **resource estimation**.

The development verifies an implementation of order finding built on fast (Toom-Cook) multiplication, from a high-level gate language down to a low-level abstract machine, and proves that the whole circuit uses only `O(n^(2+ε))` gates.

## Main results

**Correctness** (`FastMultiplication/ShorVerification/ShorCorrectness.lean`): the ideal order-finding circuit recovers the multiplicative order with at least the standard inverse-polylogarithmic probability.

```lean
theorem Shor_correct (T : ℕ → ℕ) (inst : ShorOrderFindingInstance)
    (ψ0 : qs.State) (hψ0 : ‖ψ0‖ = 1) :
    probability_of_success ... ≥ κ / (Nat.log2 inst.N : ℝ)^4
```

**Resource estimation** (`FastMultiplication/ShorVerification/GateCount/Shor_GateCount.lean`): for every `ε > 0` there is a recursion parameter `k` such that the compiled Shor circuit uses `O(n^(2+ε))` elementary gates.

```lean
theorem exists_shorGateCountBound (qs : QSemantics) ... (ε δ : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ k : ℕ, ∃ hk : 1 < k, ∃ ops : Prog k,
      PhaseProductProgramOK k hk ops ∧ ShorGateCountBound qs ε δ k hk ops
```

Here `ShorGateCountBound` says the count of elementary gates in the fully lowered order-finding circuit is at most `C · n^(2+ε)`, where `n` is the size of the modulus register (typeclass arguments elided):

```lean
def ShorGateCountBound (qs : QSemantics) (ε δ : ℝ) (k : ℕ) (hk : 1 < k) (ops : Prog k) : Prop :=
  ∃ C : ℝ, 0 < C ∧
  ∃ n₀ : ℕ, 1 ≤ n₀ ∧
    ∀ (inst : ShorOrderFindingInstance) (work : Reg) (flag : ℕ) (b0 : qs.Basis),
      let n := Reg.width inst.y
      n₀ ≤ n →
      ShorApproxSetup qs (shorEta δ (Reg.width inst.y)) inst.a inst.N inst.x inst.y work flag b0 →
      (shorOrderFindingGateCount qs k hk ops inst.a inst.N inst.x inst.y work flag : ℝ)
        ≤ C * shorGateRate ε n
```

The two quantities being compared are honest counts, not abstract measures: `shorOrderFindingGateCount` counts the `LowGate` operations of the compiled circuit under the cost model `shorGateCostModel`, and `shorGateRate ε n` is just `n^(2+ε)`.

```lean
noncomputable def shorOrderFindingGateCount ... : ℕ :=
  LowGate.gateCount shorGateCostModel (orderFindingApproxLow qs k hk ops a N x y work flag)

noncomputable def shorGateRate (ε : ℝ) (n : ℕ) : ℝ :=
  Real.rpow (((max 1 n : ℕ) : ℝ)) (2 + ε)
```

### Status

All components are proved: phase-product compilation, QFT decomposition, lowering correctness, modular-exponentiation error bounds, and the full resource-estimation stack. Two statements are still `sorry`:

- `Shor_correct` — the final assembly of the top-level success-probability bound.
- `CF_recovers_denominator` — the classical continued-fraction postprocessing fact.

## Repository layout

| Directory | Contents |
| --- | --- |
| `FastMultiplication/ShorVerification/Basic.lean` | Semantic core: registers, the high-level `Gate` language, `QSemantics`, and general semantic facts. |
| `FastMultiplication/ShorVerification/MathBackbone/` | Symbolic source programs and table generation, Toom-Cook interpolation algebra, and the classical Shor/order-finding math. |
| `FastMultiplication/ShorVerification/AlgorithmCorrectness/` | Phase-product compiler correctness, the QFT split identity, and modular-multiplication/exponentiation error bounds. |
| `FastMultiplication/ShorVerification/AbstractMachine/` | The low-level `LowGate` machine, recursive lowering from `Gate`, and whole-program lowering correctness. |
| `FastMultiplication/ShorVerification/GateCount/` | Resource estimation: the gate cost model and counting bounds for the phase product, the QFT, and the complete Shor circuit. |
| `FastMultiplication/ShorVerification/ShorCorrectness.lean` | Order-finding circuits, the measurement interface, and the top-level theorem `Shor_correct`. |
| `docs/` | An interactive visualization of the proof architecture. |

For a current, user-oriented path through the framework, see
[Framework Reading Guide](FastMultiplication/ShorVerification/Framework/README.md).
`ARCHITECTURE.md` and the interactive visualization still describe the
pre-restructure layout and are retained as historical proof-organization notes.

## Proof architecture

The dependency story in one paragraph: `MathBackbone/Table_Generation` produces the symbolic source programs and phase-point structure, and `MathBackbone/Toom_Cook_formula.lean` supplies the interpolation algebra. `AlgorithmCorrectness/PhaseProduct` uses both to prove the high-level Toom-Cook phase identity and the correctness of the compiled signed phase-product circuit; `AlgorithmCorrectness/QFT` proves the QFT split identity. `AbstractMachine` lifts these to the full `Gate` language via the lowering theorems. Finally, the lowering results, the modular-exponentiation bounds, and the classical math in `MathBackbone/ShorAlgorithm.lean` feed into `ShorCorrectness.lean`, while `GateCount/` supplies the resource estimates for the compiled circuit.

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
