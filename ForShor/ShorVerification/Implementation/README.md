# `Implementation/`

`Shor/Interface.lean` defines what correctness means, over the
`Framework/` vocabulary: its `ShorImplementation` structure asks for one `LowGate` circuit per valid
order-finding instance, a declared success probability, a trial count
amplifying that probability to 99% on 2048-bit moduli, and proofs that both
are honest. Everything else under `Implementation/` exists to build values
of that structure.

**This folder is the construction, not the submission.** A submission is a
Toom-Cook table — `Framework/ToomCookTable.lean`'s `ShorSubmission`: an
arithmetic program and the interpolation points it evaluates at, plus four
decidable side conditions — or a width-indexed list of such tables, a
`ShorPolicySubmission` (`Framework/Policy.lean`); a single table is the
one-band policy. `Reference/` is what turns any admissible policy into a
circuit family. The distinction matters because `referenceProgramAt_success`
is *generic* in the policy, so passing the side conditions is a complete
acceptance test with no per-submission proof. See
`ShorVerification/Submission/README.md`.

The work splits into three independently-verified subroutines
(`PhaseProduct/`, `QFT/`, `ModularExponentiation/`), the assembly folder that composes the
subroutines into the full order-finding circuit and proves Shor's algorithm
correct (`Shor/`), the resource-estimation layers (`GateCount/` for gates,
`QubitCount/` for qubits), and the
folder that makes every remaining choice concrete and turns a table into a
`ShorImplementation` (`Reference/`).

```
PhaseProduct, QFT, ModularExponentiation  <  Shor  <  Reference
                                 GateCount (consumes Shor + PhaseProduct + QFT)
                                QubitCount (consumes Shor + Compiler + Reference)
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

## Lemma libraries over Framework vocabulary

Derived laws of the Framework definitions live in the proofs of the lowest
folder that uses them, and later folders import them from there:

| File | Laws of |
|---|---|
| `PhaseProduct/Proofs/Registers.lean` | `Reg`, `RegEncoding`, `ExtReg`, two's complement |
| `PhaseProduct/Proofs/States.lean` | `QSemantics` evaluation: zero, injectivity, adjoints, norms, freshness |
| `PhaseProduct/Proofs/GateLaws.lean` | the per-gate semantic classes of `Framework/Semantics/GateSemantics.lean` |
| `PhaseProduct/Proofs/LowGateEval.lean` | `LowerGateClass.evalL` and its bridge to `Gate` |
| `QFT/Proofs/Hadamard.lean` | `H_reg`: uniform superposition and span closure |
| `QFT/Proofs/QftPhase.lean` | `qftPhase`: grid-exponential form, periodicity, unit norm |
| `Shor/Proofs/Measurement.lean` | `MeasureClass`: projector sums and distance bounds on outcome distributions |

A Statement never imports these. `CleanClosure` is a definition, so it sits in
`PhaseProduct/Statement.lean`, and the spare-qubit lemmas behind the
modular-multiplication workspaces sit in `ModularExponentiation/Statement.lean`.

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
  `K` independent of the modulus, precision, or instance. The per-step
  precision `η` is left free here, and the lower bound it states is
  informative only once `η` is chosen as a function of `N`.
* `Shor_correct_approx_lowered` — the same circuit at a precision schedule
  tied to `N`. At any `η ≤ shorPrecision N x` the approximation loss is at
  most half of the ideal bound, so the circuit certifiably keeps the other
  half, `κ / (2 · log(log₂ N + 1))`. This is the lowered statement to cite.
* `Shor_correct_approx_lowered_2048` — the uniform bound with its constant
  named, `K = 2048`, at any precision. `Reference/` consumes this one, which
  is why nothing outside `Shor/` needs to import `Shor/Proofs/`.
* `Shor_ready_workspace_sufficient` — a readiness package gives the circuit
  the workspace its lowering needs. The lowered statements take that
  workspace proof as an argument; this says it can always be supplied.

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

## `QubitCount/` — the qubit count

**Tackles:** how many qubits the lowered circuit needs at once. A lowered
circuit is walked in time order with a set of live qubits: gates and
extensions make qubits live, deallocations release them, and waiting qubits
stay live. The phase product's recursion runs its children one after another,
so only one child's reserve is live at a time.

**Final theorem:** `Policy.orderFinding_peak_formula` — from its five
registers' active qubits, the lowered order-finding circuit returns to that
set, and its peak is that set's size plus `Policy.orderFindingPeak`, an
explicit function of the register widths and the policy.
`Policy.reference_peak_formula` gives the same for the reference circuit and
bounds its qubit count from an empty start.
`Policy.orderFinding_peak_formula_balanced` is the same formula for the
circuit lowered after `Reference/Balanced/`'s balancing pass, each phase
product costed as its balanced split; at 2048 bits it gives 17,291 qubits
(`reference_2048_peak_balanced`), against 19,319 unbalanced.

## `Reference/` — table ↦ circuit family

**Tackles:** making every choice the folders above leave abstract (which
physical register layout, which precision schedule as a function of the
framework's natural-number precision level `m`) into one deterministic,
fully computable construction, discharging the implementation-specific
readiness obligations against it, and packaging the result as a value of the
framework's `ShorImplementation` structure.

One choice it does not make: the interpolation tables. Those are the
*input* — a `ShorLoweringPolicy`, i.e. a submission — and
`standardLoweringSetup` is merely this folder's own default table, the
canonical ladder `0, -1, 1, -2, 2, …`, not a constant baked into anything's
type.

**Final theorem/definition:** `referenceProgramAt_success`, which is where
the genericity lives: it holds for *every* admissible `ShorLoweringPolicy`,
so a submitted table or policy needs no correctness proof of its own.
`referenceShorImplementation lowering` packages a table into the framework's
structure. Everything else here (`ReferenceLayout.lean`,
`ReferenceReadiness.lean`, `ReferencePrecision.lean`, `ShorProgram.lean`,
`Reference2048Headline.lean`) exists to construct those fields and discharge
their obligations. `Reference2048Headline.lean` fixes the explicit precision
`m2048` (`η = 2⁻¹⁵⁰`) and proves the single-run bound at it retains at
least 99% of the ideal `κ / log(log₂ N + 1)` baseline — which is what
`Submission/Score.lean` turns into the trial count the score multiplies by.

## Reading order for newcomers

Start at `Reference/ReferenceShorImplementation.lean`'s
`referenceShorImplementation` and follow imports *backwards*: `Shor/Main.lean`
for what "Shor's algorithm is correct" means at the circuit level,
`ModularExponentiation/Main.lean` for the implementation error bound
`Shor/` transfers across, and `QFT/Main.lean` /
`PhaseProduct/Main.lean` for the two subroutines the circuit is built from.
`GateCount/` and the lemma libraries above are consumed along the way rather
than sitting on this main spine.
