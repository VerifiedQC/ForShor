# `Implementation/`

`Framework/` defines what correctness means: `Framework/Contract.lean`'s
`ShorImplementation` structure asks for one `LowGate` circuit per valid
order-finding instance, a declared success probability, a trial count
amplifying that probability to 99% on 2048-bit moduli, and proofs that both
are honest. Everything under `Implementation/` exists to build values of that
structure and hand them to the framework.

**This folder is the construction, not the submission.** It used to be both.
A submission is now a Toom-Cook table — `Framework/ToomCookTable.lean`'s
`ShorSubmission`: an arithmetic program and the interpolation points it
evaluates at, plus four decidable side conditions — and `Reference/` is what
turns any admissible table into a circuit family. The distinction matters
because `referenceProgramAt_success` is *generic* in the table, so passing
those four conditions is a complete acceptance test with no per-submission
proof. See `ShorVerification/Submission/README.md`.

The work splits into three independently-verified subroutines
(`PhaseProduct/`, `QFT/`, `ModularExponentiation/`), a library of lemmas
shared across them (`Shared/`), the assembly folder that composes the
subroutines into the full order-finding circuit and proves Shor's algorithm
correct (`Shor/`), the resource-estimation layer (`GateCount/`), and the
folder that makes every remaining choice concrete and turns a table into a
`ShorImplementation` (`Reference/`).

```
PhaseProduct, QFT, ModularExponentiation  <  Shor  <  Reference
                                    Shared (cross-cutting)
                                 GateCount (consumes Shor + PhaseProduct + QFT)
```

Each folder below has its own `README.md` with the full file-by-file
breakdown; this page is the map between them.

## `PhaseProduct/` — the recursive phase-product subroutine

**Tackles:** computing `exp(i·φ·x·z)` on two registers `x`, `z` (signed and
controlled-signed) with a circuit whose size scales better than the naive
`O(n²)` construction. A Toom-Cook-style interpolation compiler recursively
splits the operands into `k`-way chunks, reconstructs the product phase from
`2k-1` smaller phase-product calls plus classical interpolation arithmetic,
and the result is lowered to primitive `LowGate`s.

**Final theorems** (`Main.lean`): `lowerSignedPhaseProduct_correct` and
`lowerCSignedPhaseProduct_correct` — the lowered signed/controlled-signed
circuit evaluates exactly as the abstract phase-product gate specifies,
given a satisfied recursive workspace precondition and a clean input state.

## `QFT/` — the recursive Quantum Fourier Transform

**Tackles:** the recursive QFT: splitting a register's QFT into two half-size
recursive QFTs joined by an unsigned phase-product macro (built from
`PhaseProduct/`) and a radix reversal, plus the workspace budget model that
lets both recursive halves safely reuse the same reserve pools, and the
lowering machinery turning the recursive plan into primitive gates.

**Final theorem** (`Main.lean`): `lowerQFT_correct` — the canonical recursive
lowering of `Gate.QFT` has the same semantics as the high-level QFT gate, on
states with valid, clean recursive workspace.

## `ModularExponentiation/` — Algorithm 1: in-place modular multiplication/exponentiation

**Tackles:** `|x⟩|0⟩ ↦ |c·x mod N⟩|0⟩` and, by recursing over the exponent
register, modular exponentiation — approximated by a fractional-load-and-cleanup
circuit built from QFT-based phase products (`QFT/`), an inverse-QFT
comparator, and constant-arithmetic subtraction, together with a quantitative
error bound uniform in the precision parameter `η`.

**Final theorem** (`Main.lean`): `modExpApprox_correct` — a single
`η`-independent constant `K` bounds the distance between the approximate and
ideal modular-exponentiation circuits uniformly over valid unit states.

## `Shared/` — lemma libraries used by every subroutine above

**Tackles:** nothing on its own — it holds the derived register/encoding
laws, `QSemantics`/evaluator algebra, Hadamard-superposition facts, per-gate
semantic-class lemmas, and lowered-gate evaluation rewrites that
`PhaseProduct/`, `QFT/`, `ModularExponentiation/`, and `Shor/` all need and
none of them owns individually. See `Shared/README.md` for the admission rule
and the file-by-file breakdown.

**Final theorem:** none — this is a support library, not a subroutine with a
correctness claim of its own.

## `Shor/` — assembling the subroutines into order-finding, and proving Shor's algorithm correct

**Tackles:** building the concrete approximate order-finding circuit (register
Hadamards, the verified modular-exponentiation circuit, inverse QFT) from the
three subroutines above; proving workspace readiness for the whole lowered
circuit; and the two mathematical results that make it *Shor's algorithm*:
the ideal circuit's success-probability lower bound (via quantum phase
estimation and the continued-fraction classical reduction) and the transfer
of that bound across the modular-exponentiation implementation's
approximation error.

**Final theorems** (`Main.lean`):
* `Shor_end_to_end_factoring` — the complete mathematical payoff: for a
  well-formed factoring instance, order finding succeeds with the stated
  probability *and* a successful outcome yields a nontrivial factor of `N`
  via the classical continued-fraction reduction. Stated at the ideal
  (unlowered) circuit level.
* `Shor_correct_approx_lowered_uniform` — the version that actually connects
  to a submitted circuit: the fully lowered, approximate order-finding
  circuit's success probability is uniformly bounded below, for a single
  `K` independent of the modulus, precision, or instance.

## `GateCount/` — the resource-estimation layer

**Tackles:** proving the lowered Shor circuit's gate count is
`O(n^(2+ε))`, by giving `LowGate` a concrete cost model, bounding
`PhaseProduct/`'s and `QFT/`'s lowered gate counts at a shared comparison
rate `n^(log_k(2k-1))`, summing one modular-multiplication core's bound over
the whole exponentiation, and choosing the recursion arity `k` large enough
that the rate collapses to `2 + ε`.

**Final theorem:** `exists_shorGateCountBound` — for every `ε > 0` there is a
recursion arity `k` and a generated interpolation program such that the
complete lowered Shor circuit's gate count is bounded by `n^(2+ε)`.

## `Reference/` — table ↦ circuit family

**Tackles:** making every choice the folders above leave abstract (which
physical register layout, which precision schedule as a function of the
framework's natural-number precision level `m`) into one deterministic,
fully computable construction, discharging the implementation-specific
readiness obligations against it, and packaging the result as a value of the
framework's `ShorImplementation` structure.

One choice it no longer makes: the interpolation-point program. That is the
*input* now — a `ShorLoweringSetup`, i.e. a submission — and
`standardLoweringSetup` is merely this folder's own default, the canonical
ladder `0, -1, 1, -2, 2, …`, not a constant baked into anything's type.

**Final theorem/definition:** `referenceProgramAt_success`, which is where
the genericity lives: it holds for *every* `ShorLoweringSetup`, so a
submitted table needs no correctness proof of its own.
`referenceShorImplementation lowering` packages a table into the framework's
structure. Everything else here (`ReferenceLayout.lean`,
`ReferenceReadiness.lean`, `ReferencePrecision.lean`, `ShorProgram.lean`,
`Reference2048Headline.lean`) exists to construct those fields and discharge
their obligations. `Reference2048Headline.lean` fixes the explicit precision
`m2048` (`η = 2⁻¹⁵⁰`) and proves the single-run bound at it retains at
least 99% of the ideal `κ / (log₂ N)⁴` baseline — which is what
`Submission/Score.lean` turns into the trial count the score multiplies by.

## Reading order for newcomers

Start at `Reference/ReferenceShorImplementation.lean`'s
`referenceShorImplementation` and follow imports *backwards*: `Shor/Main.lean`
for what "Shor's algorithm is correct" means at the circuit level,
`ModularExponentiation/Main.lean` for the implementation error bound
`Shor/` transfers across, and `QFT/Main.lean` /
`PhaseProduct/Main.lean` for the two subroutines the circuit is built from.
`GateCount/` and `Shared/` are consumed along the way rather than sitting on
this main spine.
