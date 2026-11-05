# `Implementation/Shor/`

This folder builds the order-finding circuit of Shor's algorithm from the QFT,
phase-product and modular-exponentiation subroutines, lowers it to elementary
gates, and proves a lower bound on the probability that running it and
post-processing the measured outcome with continued fractions returns the
order.

`Statement.lean` is the only file needed to see what is claimed: it holds
every definition the claims depend on and imports nothing else from this
folder. `Main.lean` proves the claims stated in `Statement.lean`; `Proofs/`
holds the lemmas those proofs use.

## Background

**The problem.** Given N and a with gcd(a, N) = 1, find the order r of a
modulo N: the least r > 0 with aʳ ≡ 1 (mod N).

**The circuit.** It uses an exponent register of t qubits, with Q = 2ᵗ ≥ N²,
and a data register.

1. Put the exponent register in uniform superposition and the data register in
   |1⟩, giving (1/√Q) Σₓ |x⟩|1⟩.
2. Apply modular exponentiation, giving (1/√Q) Σₓ |x⟩|aˣ mod N⟩.
3. Apply the inverse QFT to the exponent register and measure it, giving an
   outcome o.

**The outcome.** o/Q is close to k/r for a uniformly random k < r: with
probability at least 4/π², |o/Q − k/r| ≤ 1/(2Q).

**Post-processing.** Since Q ≥ N² > r², that error is less than 1/(2r²), so by
Legendre's theorem k/r in lowest terms is a convergent of the continued
fraction of o/Q. Its denominator is r when gcd(k, r) = 1.

**Success probability.** A run returns r when o lands near some k·Q/r, which
happens with probability at least 4/π², and that k is coprime to r, which
holds for a fraction φ(r)/r ≥ 1/(4 · log(log₂ N + 1)) of the k. So

```
P(success) ≥ (4/π²) · φ(r)/r ≥ κ / log(log₂ N + 1),   κ = 1/π²
```

**The approximation.** The circuit here uses the approximate modular
exponentiation of `ModularExponentiation/`. At per-step precision η it costs at
most 2 · t · √(2Kη) of that probability.

## `Statement.lean`

The following explains each section of the code in the Statement.lean file

**Problem instance.** `ShorOrderFindingInstance`: a base `a` and a modulus `N`
with `0 < a < N` and `gcd(a, N) = 1`.

**The order and continued-fraction post-processing.** `ord` is the order `r`.
`orderCandidates` collects the denominators of the first `T Q` convergents of
`o / Q` that are positive and pass `verify` (in the claims, `aᵈ ≡ 1 (mod N)`),
and `OF_post` returns the least of them, or `0` if there is none.
`ContinuedFractionSearchComplete T` says `T Q` convergents are enough: the
expansion of every `o / Q` with `o < Q` terminates before step `T Q`.
`r_found` is `1` if post-processing returns `r`, and `0` otherwise.

**Workspace budget.** The number of spare qubits the lowered circuit needs on
the exponent, data, work and comparator scratch registers, computed from the
QFT and phase-product recursions; the condition that each register has that
many; and the condition that the exponent register's qubits are not reused by
the work register, the scratch register or the comparator flag.

**Hypotheses.** `ShorApproxSetupMinimal`: the comparator's register layout, the
exponent and data registers disjoint, the work register wide enough for
precision `η`, and every active register starting at zero.
`ShorWorkspaceCleanInput`: every spare qubit starts at zero. `LoweredShorReady`
collects these with the workspace budget and isolation conditions.

**Success probability.** `probability_of_success`: the sum over outcomes `o` of
the probability of measuring `o` times `r_found`. `κ = 1/π²`, and
`shorPrecision N x`, the precision at which the approximation loss is at most
half of `κ / log(log₂ N + 1)`.

**The order-finding circuit.** `initY1` sets the data register to `1`, and
`orderFindingApprox` is the circuit above: Hadamards on the exponent register,
`initY1`, the approximate modular exponentiation, and the inverse QFT.
`LoweredShorReady.circuit` is that circuit on a readiness package's registers.

**Correctness.** The lowered circuit is `Policy.lowerGate P hready.circuit hws`
(`Compiler/`), where `hws` is a proof that every block in the circuit has the
workspace its lowering needs. `ShorCorrectApproxLoweredUniform`: at any
precision `η`, the success probability is at least
`κ / log(log₂ N + 1) − 2 · t · √(2Kη)` for a constant `K ≤ 1600`, where `t` is
the width of the exponent register.
`ShorCorrectApproxLowered`: at any `η ≤ shorPrecision N x`, it is at least
`κ / (2 · log(log₂ N + 1))`.

## `Main.lean`

Proves `ShorCorrectApproxLoweredUniform` and `ShorCorrectApproxLowered`.
