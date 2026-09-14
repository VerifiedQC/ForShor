# ForShor

[![Lean](https://img.shields.io/badge/Lean-v4.28.0-blue)](https://leanprover.github.io/)
[![Mathlib](https://img.shields.io/badge/mathlib4-required-9cf)](https://github.com/leanprover-community/mathlib4)
[![License](https://img.shields.io/badge/license-Apache_2.0-green)](LICENSE)

A formal verification of **Shor's algorithm** in Lean 4 — including its **resource estimation**.

The development verifies an implementation of order finding built on fast (Toom-Cook) multiplication, from a high-level gate language down to a low-level abstract machine, and proves that the whole circuit uses only `O(n^(2+ε))` gates.

## Main results

**Correctness** (`FastMultiplication/ShorVerification/Implementation/Shor/Proofs/NaiveShor/Main.lean`): the ideal order-finding circuit recovers the multiplicative order with at least the standard inverse-polylogarithmic probability.

```lean
theorem Shor_correct (T : ℕ → ℕ) (inst : ShorOrderFindingInstance)
    (ψ0 : qs.State) (hψ0 : ‖ψ0‖ = 1) :
    probability_of_success ... ≥ κ / (Nat.log2 inst.N : ℝ)^4
```

**Resource estimation** (`FastMultiplication/ShorVerification/Implementation/GateCount/Shor_GateCount.lean`): for every `ε > 0` there is a recursion parameter `k` such that the compiled Shor circuit uses `O(n^(2+ε))` elementary gates.

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
      let n := regSize inst.y
      n₀ ≤ n →
      ShorApproxSetup qs (shorEta δ (regSize inst.y)) inst.a inst.N inst.x inst.y work flag b0 →
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

All components are proved: phase-product compilation, QFT decomposition, continued-fraction recovery, lowering correctness, modular-exponentiation error bounds, and the full resource-estimation stack. No `sorry` remains anywhere in the codebase, and `#print axioms` on the headline theorems reports only `propext`, `Classical.choice`, and `Quot.sound`.

The reference implementation (`FastMultiplication/ShorVerification/Implementation/Reference/`) instantiates the whole framework concretely and is fully computable end to end: `Shor.Reference.referenceProgramAt` lowers to an executable `LowGate` circuit with no noncomputable interpolation step (the phase-product coefficients are computed via `Matrix.cramer`, not `Matrix.inv`). `FastMultiplication/Emit/` prints that circuit as JSON (`forshor.lowgate/v2` schema); `lake exe forshor_emit <k> <a> <N> <m>` writes it to stdout.

## Repository layout

| Directory | Contents |
| --- | --- |
| `FastMultiplication/ShorVerification/Framework/` | Semantic core, shared by every implementation: registers (`Quantum/`), the high-level `Gate` and low-level `LowGate` languages (`AbstractMachine/`), `QSemantics` and the other semantic classes (`Semantics/`), the cost model (`Gatecount/`), general classical math (`Math/`), and the public submission interface (`Submission.lean`). |
| `FastMultiplication/ShorVerification/Implementation/PhaseProduct/` | The recursive phase-product compiler: Toom-Cook interpolation, table generation, and compilation/lowering correctness. |
| `FastMultiplication/ShorVerification/Implementation/QFT/` | The QFT split identity and QFT lowering correctness. |
| `FastMultiplication/ShorVerification/Implementation/ModularExponentiation/` | Modular-multiplication/exponentiation approximation bounds. |
| `FastMultiplication/ShorVerification/Implementation/Shor/` | Order-finding circuits, the top-level theorem `Shor_correct`, and whole-program lowering correctness. |
| `FastMultiplication/ShorVerification/Implementation/GateCount/` | Resource estimation: counting bounds for the phase product, the QFT, and the complete Shor circuit. |
| `FastMultiplication/ShorVerification/Implementation/Shared/` | Lemma libraries over Framework vocabulary shared by every subroutine folder; imports nothing from them. |
| `FastMultiplication/ShorVerification/Implementation/Reference/` | The concrete, fully computable reference implementation submitted against the framework. |
| `FastMultiplication/Emit/` | JSON printer for the reference circuit and the `forshor_emit` executable. |
| `docs/` | An interactive visualization of the proof architecture. |

For a detailed file-by-file guide, see [ARCHITECTURE.md](ARCHITECTURE.md) (some paths there predate this layout; see the note at the top of that file).

## Proof architecture

The dependency story in one paragraph: `Implementation/PhaseProduct/Math/Table_Generation` produces the symbolic source programs and phase-point structure, and `Implementation/PhaseProduct/Math/Toom_Cook_formula.lean` supplies the interpolation algebra. `Implementation/PhaseProduct/Proofs/` uses both to prove the high-level Toom-Cook phase identity, the correctness of the compiled signed phase-product circuit, and its lowering to `LowGate`; `Implementation/QFT/Proofs/` proves the QFT split identity and its lowering. Together with `Implementation/ModularExponentiation/`'s approximation bounds, these feed into `Implementation/Shor/`, which assembles order finding and whole-program lowering correctness, while `Implementation/GateCount/` supplies the resource estimates for the compiled circuit. `Implementation/Reference/` instantiates all of this concretely into an executable circuit family, which `FastMultiplication/Emit/` serializes to JSON.

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

To print the reference circuit for an instance `(k, a, N, m)` as JSON:

```sh
lake exe forshor_emit 2 2 15 0
```

## License

Released under the Apache License 2.0. See [LICENSE](LICENSE).

## Citation

If you use ForShor in your research, please cite it. A machine-readable
[`CITATION.cff`](CITATION.cff) is provided (GitHub renders a "Cite this
repository" button); a BibTeX entry:

```bibtex
@misc{suresh2026forshor,
  author       = {Anirudh Suresh and Jai Patel and Yudong Cao and Runzhou Tao},
  title        = {{ForShor}: Formal Verification of {Shor}'s Algorithm in {Lean~4}
                  with Verified Resource Estimation},
  year         = {2026},
  howpublished = {\url{https://github.com/VerifiedQC/ForShor}},
  note         = {Apache-2.0 licensed Lean~4 development}
}
```
