# ForShor

[![Lean](https://img.shields.io/badge/Lean-v4.28.0-blue)](https://leanprover.github.io/)
[![Mathlib](https://img.shields.io/badge/mathlib4-required-9cf)](https://github.com/leanprover-community/mathlib4)
[![License](https://img.shields.io/badge/license-Apache_2.0-green)](LICENSE)

A formal verification of **Shor's algorithm** in Lean 4 — including its **resource estimation**.

The development verifies an implementation of order finding built on fast (Toom-Cook) multiplication, from a high-level gate language down to a low-level abstract machine, and proves that the whole circuit uses only `O(n^(2+ε))` gates.

## Main results

**Correctness** (`FastMultiplication/ShorVerification/Implementation/Shor/Proofs/NaiveShor/Correctness.lean`): the ideal order-finding circuit recovers the multiplicative order with at least the standard inverse-polylogarithmic probability.

```lean
theorem Shor_correct (T : ℕ → ℕ) (inst : ShorOrderFindingInstance)
    (ψ0 : qs.State) (hψ0 : ‖ψ0‖ = 1) :
    probability_of_success ... ≥ κ / (Nat.log2 inst.N : ℝ)^4
```

Unpacking the five pieces, since the inequality alone does not say much:

- `probability_of_success` (`Framework/Contract.lean`) is `∑ o : Fin Q, r_found T verify o Q r * probMeas x o (evalC C ψ)` — the probability that the measured outcome, *after* classical post-processing, is exactly the order `r`. Not the probability of landing in a good window.
- `r_found` (`Framework/Math/ShorDefinition.lean`) is the 0/1 indicator that scanning the first `T Q` continued-fraction convergents of `o/Q`, keeping those whose denominator `d` satisfies `a^d ≡ 1 (mod N)`, returns `r`.
- `T` is any classical budget with `continuedFractionSearchBound Q ≤ T Q`. It bounds the convergent scan, is not a circuit parameter, and costs no gates.
- `κ = 4e⁻²/π² ≈ 0.0548`.
- The exponent register has `log₂(2N²)` bits and the modulus register `log₂(2N)`, and the input is the ideal `IdealOrderFindingInput`: all registers clean, exponent register in uniform superposition.

The same bound survives compilation, up to a factor of two, once the per-step precision `η` is chosen as a function of `N` (`Implementation/Shor/Main.lean`):

```lean
theorem Shor_correct_approx_lowered (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T) :
    ShorCorrectApproxLowered T hT
-- at any η ≤ shorPrecision N x:  probability_of_success ... ≥ κ / (2 * (Nat.log2 N : ℝ)^4)
```

The lowering itself is exact; the loss is the modular-exponentiation approximation, bounded by `2 · tbits(x) · √(2 · 2048 · η)`. Holding that to half the ideal bound needs `η = Θ(1/n¹⁰)`, which costs `O(log n)` extra work bits — well inside the budget the resource estimate allows. At 2048 bits this is `η ≈ 2⁻¹³⁶`, about 270 extra work bits; the constant is `κ²/65536` and the exponents come from inverting the square root in the per-step error bound. `shorPrecision` is a closed form — there is no existential constant a circuit builder would have to guess.

**Resource estimation** (`FastMultiplication/ShorVerification/Implementation/GateCount/Shor_GateCount.lean`): for every `ε > 0` there is a recursion parameter `k` such that the compiled Shor circuit uses `O(n^(2+ε))` elementary gates.

```lean
theorem exists_shorGateCountBound (qs : QSemantics) ... (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, ∃ hk : 1 < k, ∃ ops : Prog k,
      PhaseProductProgramOK k hk ops ∧ ShorGateCountBound qs ε k hk ops
```

The bound is not special to the table this repository generates. `PhaseProductProgramOK` is the four submission conditions C1–C4, so any `ShorLoweringSetup` — any submission — satisfies it by construction, and the companion theorem applies to it directly:

```lean
theorem shorGateCountBound_of_setup (qs : QSemantics) ... (s : ShorLoweringSetup) (ε : ℝ)
    (hExponent : phaseProductExponent s.k ≤ 1 + ε) :
    ShorGateCountBound qs ε s.k s.hk s.ops s.pts s.hpts
```

The two forms differ in who chooses `k`. A submitted table fixes its own arity, and with it its own exponent `phaseProductExponent k = log(2k−1)/log k` — a `k = 2` table runs at roughly `n^2.585` — so `shorGateCountBound_of_setup` takes the `ε` that table supports as a hypothesis. Reaching every positive `ε` means letting `k` grow, which is why `exists_shorGateCountBound` quantifies over `k` existentially.

Here `ShorGateCountBound` says the count of elementary gates in the fully lowered order-finding circuit is at most `C · n^(2+ε)`, where `n` is the size of the modulus register (typeclass arguments elided):

```lean
def ShorGateCountBound (qs : QSemantics) (ε : ℝ) (k : ℕ) (hk : 1 < k) (ops : Prog k) : Prop :=
  ∀ cWork : ℕ, 1 ≤ cWork →
  ∃ C : ℝ, 0 < C ∧
  ∃ n₀ : ℕ, 1 ≤ n₀ ∧
    ∀ (inst : ShorOrderFindingInstance) (work : Reg) (flag : ℕ) (b0 : qs.Basis) (η : ℝ),
      let n := regSize inst.y
      n₀ ≤ n →
      ShorApproxSetup qs η inst.a inst.N inst.x inst.y work flag b0 →
      algorithm1ExtraBits η ≤ (cWork - 1) * regSize inst.y →
      (shorOrderFindingGateCount qs k hk ops inst.a inst.N inst.x inst.y work flag : ℝ)
        ≤ C * shorGateRate ε n
```

The precision `η` is a parameter of the circuit, not of the bound: fix any work-width budget `cWork`, and the estimate holds for every `η` whose prescribed extra bits fit that budget. Shor's own schedule `η = δ/n²` is one such choice, and `shorGateCountBoundShorEta_of_setup` specialises to it — that corollary is the only public statement mentioning `δ`.

The two quantities being compared are honest counts, not abstract measures: `shorOrderFindingGateCount` counts the `LowGate` operations of the compiled circuit under the cost model `shorGateCostModel`, and `shorGateRate ε n` is just `n^(2+ε)`.

```lean
noncomputable def shorOrderFindingGateCount ... : ℕ :=
  LowGate.gateCount shorGateCostModel (orderFindingApproxLow qs k hk ops a N x y work flag)

noncomputable def shorGateRate (ε : ℝ) (n : ℕ) : ℝ :=
  Real.rpow (((max 1 n : ℕ) : ℝ)) (2 + ε)
```

### Status

All components are proved: phase-product compilation, QFT decomposition, continued-fraction recovery, lowering correctness, modular-exponentiation error bounds, and the full resource-estimation stack. No proof in the codebase uses `sorry` — the one occurrence is a deliberate test that `Submission/Audit.lean`'s axiom check rejects it — and `#print axioms` on the headline theorems reports only `propext`, `Classical.choice`, and `Quot.sound`.

The reference implementation (`FastMultiplication/ShorVerification/Implementation/Reference/`) instantiates the whole framework concretely and is fully computable end to end: `Shor.Reference.referenceProgramAt` lowers to an executable `LowGate` circuit with no noncomputable interpolation step (the phase-product coefficients are computed via `Matrix.cramer`, not `Matrix.inv`). `FastMultiplication/Emit/` prints that circuit as JSON (`forshor.lowgate/v2` schema); `lake exe forshor_emit <k> <a> <N> <m>` writes it to stdout.

The reference is no longer the only implementation the development admits. `FastMultiplication/ShorVerification/Framework/ToomCookTable.lean` states what makes a Toom-Cook table admissible, and `referenceProgramAt` is generic in it, so any table passing four decidable side conditions gets the same proved correctness theorem — see [Submitting a table](#submitting-a-table).

## Repository layout

| Directory | Contents |
| --- | --- |
| `FastMultiplication/ShorVerification/Framework/` | Semantic core, shared by every implementation: registers (`Quantum/`), the high-level `Gate` and low-level `LowGate` languages (`AbstractMachine/`), `QSemantics` and the other semantic classes (`Semantics/`), the cost model (`Gatecount/`), general classical math (`Math/`), the correctness contract (`Contract.lean`), what makes a submitted Toom-Cook table admissible (`ToomCookTable.lean`, which imports Mathlib and nothing else), and what makes a submitted *policy* admissible (`Policy.lean`: a policy is a list of width-indexed bands, and a table is the one-band policy at threshold `0`; it imports `ToomCookTable.lean`, never the reverse). |
| `FastMultiplication/ShorVerification/Implementation/PhaseProduct/` | The recursive phase-product compiler: Toom-Cook interpolation, table generation, and compilation/lowering correctness. |
| `FastMultiplication/ShorVerification/Implementation/QFT/` | The QFT split identity and QFT lowering correctness. |
| `FastMultiplication/ShorVerification/Implementation/ModularExponentiation/` | Modular-multiplication/exponentiation approximation bounds. |
| `FastMultiplication/ShorVerification/Implementation/Shor/` | Order-finding circuits, the top-level theorem `Shor_correct`, and whole-program lowering correctness. |
| `FastMultiplication/ShorVerification/Implementation/GateCount/` | Resource estimation: counting bounds for the phase product, the QFT, and the complete Shor circuit. |
| `FastMultiplication/ShorVerification/Implementation/Shared/` | Lemma libraries over Framework vocabulary shared by every subroutine folder; imports nothing from them. |
| `FastMultiplication/ShorVerification/Implementation/Reference/` | The construction that turns an admissible table into a circuit family: fully computable, and generic in the table rather than tied to one. |
| `FastMultiplication/ShorVerification/Submission/` | The public surface a submissions repo builds against: deciding the four side conditions, auditing the axioms behind them, the certificate, the score, and the template a submitter copies. |
| `FastMultiplication/Emit/` | JSON printer for a lowered circuit, the symbolic IR extractor, and the `forshor_emit` executable. |
| `docs/` | An interactive visualization of the proof architecture. |

For a detailed file-by-file guide, see [ARCHITECTURE.md](ARCHITECTURE.md). Each folder also has its own `README.md`.

## Proof architecture

The dependency story in one paragraph: `Implementation/PhaseProduct/Math/Table_Generation` produces the symbolic source programs and phase-point structure, and `Implementation/PhaseProduct/Math/ToomCook.lean` supplies the interpolation algebra. `Implementation/PhaseProduct/Proofs/` uses both to prove the high-level Toom-Cook phase identity, the correctness of the compiled signed phase-product circuit, and its lowering to `LowGate`; `Implementation/QFT/Proofs/` proves the QFT split identity and its lowering. Together with `Implementation/ModularExponentiation/`'s approximation bounds, these feed into `Implementation/Shor/`, which assembles order finding and whole-program lowering correctness, while `Implementation/GateCount/` supplies the resource estimates for the compiled circuit. `Implementation/Reference/` instantiates all of this concretely into an executable circuit family, which `FastMultiplication/Emit/` serializes to JSON.

You can explore the proof graph interactively:

```sh
cd docs && python3 -m http.server 8765
# then open http://localhost:8765
```

## Submitting a table

The challenge this repository defines is narrower than "write a Shor
circuit", and deliberately so. The one degree of freedom the verified
construction exposes is its Toom-Cook table: an arithmetic program `ops` over
`k` limb registers, plus the interpolation points `pts` its `phaseProduct`
checkpoints evaluate at. Everything else — the quantum construction, its
correctness proof, the precision, the trial count — is fixed here and is the
same for every submission.

A submission is therefore a value of `Shor.ShorSubmission`
(`Framework/ToomCookTable.lean`): the table, plus the submitter's proofs of
four conditions.

(A second kind of submission is being built on top of this one: a
`Shor.ShorPolicySubmission` (`Framework/Policy.lean`) is a list of such
tables indexed by operand width — Toom-6 at the top, Karatsuba near the
leaves, the schoolbook leaf below an explicit threshold — each band carrying
the same four proofs, plus one decidable field saying the thresholds strictly
decrease. A table submission is the one-band policy at threshold `0`, so
nothing below changes for it.)

| | condition | proved by |
| --- | --- | --- |
| C1 | `pts.length = 2k - 1` — one point per product coefficient | `rfl` |
| C2 | `det (interpMatrix …) ≠ 0` — the points interpolate a degree-`2k-2` polynomial | `goodToomCookPoints_of_distinct _ (by decide +kernel)` |
| C3 | running `ops` from the start state, the `i`-th checkpoint holds exactly `pts[i]`'s row, all points are consumed, and no `addScaled` has `dst = src` | `by decide +kernel` |
| C4 | `run? ops start = some start` — the table uncomputes itself | `by decide +kernel` |

All four are decidable *in the kernel*, so the kernel checks a submission
rather than a parser or the compiled evaluator. C2 would be the exception —
its determinant is a sum over `(2k-1)!` permutations — except that the
interpolation matrix is a projective Vandermonde, so `Submission/Decide.lean`
proves C2 equivalent to the points being pairwise distinct as projective
points, which is a quadratic scan.

`decide +kernel`, not `native_decide`, and that is enforced rather than
requested: `Submission/Check.lean` runs `#assert_axioms Submission.setup`,
which fails the build unless the finished term's axioms lie inside `propext`,
`Classical.choice`, `Quot.sound` — so `native_decide` (`Lean.ofReduceBool`),
`sorry` (`sorryAx`) and a submitter's own `axiom` are all rejected by name.

Passing C1–C4 is not evidence of admissibility, it *is* admissibility:
`Shor.submission_correct` is proved once, generic in the table, and applies
with no per-submission proof.

Copy `FastMultiplication/ShorVerification/Submission/Template.lean` — the
only file a submitter owns — edit the three definitions it marks (`k`, `pts`,
`ops`), prove the four conditions for them, and run:

```sh
lake build Submission && lake exe forshor_submission > ir.json
```

Building is the check. The executable is a printer: it emits the table, the
extracted IR a resource estimator reads, the fixed precision, and the trial
count the score is multiplied by. See
[`Submission/README.md`](FastMultiplication/ShorVerification/Submission/README.md)
for what the two tiers of checking do and do not establish, and for the CI
rules a submissions repo should enforce.

## Building

The project uses Lean `v4.28.0` (pinned in `lean-toolchain`) and depends on [mathlib4](https://github.com/leanprover-community/mathlib4) at revision `fadcf92bfcfe7575bbdf04c6f83ab3ada53e3d42`, pinned in both `lakefile.lean` and `lake-manifest.json`. `lake exe cache get` fetches the prebuilt oleans for that exact revision, so the pin is what makes the cache usable. With [elan](https://github.com/leanprover/elan) installed:

```sh
lake exe cache get   # fetch prebuilt mathlib oleans
lake build
```

To print the reference circuit for an instance `(k, a, N, m)` as JSON:

```sh
lake exe forshor_emit 2 2 15 0
```

The other build targets:

```sh
lake build EmitTests     # the emitter's native_decide acceptance suite
lake build Submission    # checks the table and proofs in Submission/Template.lean
lake exe forshor_submission
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
