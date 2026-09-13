# `Spec/`

The public specification surface: precision and validity predicates,
compact configuration records bundling them with the circuit, and the final
named claim proved in `Main.lean`. `Precision.lean` and `Validity.lean` are
independent siblings; `Config.lean` builds on both plus `Circuit/`;
`Assertions.lean` builds on `Config.lean`.

## `Precision.lean`

- **`stepErr`** — `√(2Kη)`, the per-core norm error scale used by the
  modular-exponentiation hybrid bound.
- **`algorithm1ExtraBits`** — the extra work-register bits the paper's
  precision schedule prescribes: `⌈2·log₂(2 + 1/(2η))⌉`.
- **`Algorithm1Precision`** — the sufficient precision condition on the
  data/work register widths this development actually uses (`0 < η < 1/2`
  and `regSize work = regSize data + algorithm1ExtraBits η`), which implies
  the paper's `2^(m-n) ≥ (2 + 1/(2η))²` bound.

## `Validity.lean`

- **`GoodModMulBasisInput`** — a computational-basis input Algorithm 1 is
  allowed to run on: the data register holds a canonical residue below `N`,
  the two data reserve bits and the work register are clean, and the
  comparator flag is clean. The control/exponent registers are unconstrained.
- **`ValidModMulState`** — the linear span of all basis kets satisfying
  `GoodModMulBasisInput`: arbitrary superpositions over the control/exponent
  registers and valid data residues.
- **`GoodAlgorithm1BasisInput`** / **`ValidAlgorithm1State`** — the same pair,
  extended with a clean `scratch` register (Step 4's comparator workspace).
- **`ConstArithmeticCleanBasis`** — basis-level cleanliness consumed by both
  Step-3 lowerers: `data` fresh, `scratch` at zero and fresh.
- **`CSubConstCleanBasis`** — the same predicate under controlled
  subtraction's name; the concrete lowerer is total (fixed-width modular
  subtraction), so no extra no-underflow premise is needed.
- **`CmpGeConstCleanState`** / **`CSubConstCleanState`** — the linear closure
  (`CleanClosure`) of the two basis predicates above, so they apply to
  arbitrary quantum states rather than just basis kets.

## `Config.lean`

Compact records so the bound files don't have to keep threading the modulus,
registers, precision proof, workspace proof, layout proof, and coprimality
hypotheses individually.

- **`Algorithm1Env`** — the common environment for one Algorithm-1 analysis:
  modulus `N`, `data`/`work`/`scratch` registers, `N ≤ ASize data.active`, a
  proof of `Algorithm1Precision`, and a proof of `ModMulCircuitWorkspaceOK`.
- **`ModMulConfig`** (+ namespace) — one controlled modular-multiplication
  core's configuration: an `Algorithm1Env`, multiplier `c` coprime to `N`,
  `flag`/`ctrl` qubits with a valid `ModMulCoreLayout`, and a Step-4
  `CmpLtNWWorkspace`. `approxGate`/`idealGate` package the concrete
  `CmodMulInPlaceCore` circuit and `Gate.idealCtrlModMul` for this config;
  `ValidState`/`ValidUnitState` package `ValidAlgorithm1State` membership
  (with unit norm, for the latter).
- **`ModExpConfig`** (+ namespace) — the same idea one level up, for the full
  modular-exponentiation recursion: adds the exponent register `x`, a
  `ModExpLayout`, and a `ModExpArithmeticOK` proof. `approxGate`/`idealGate`
  package `modExpApproxValid`/`modExpIdeal'`; `ValidUnitState` packages
  `ValidAlgorithm1State` membership with unit norm.

## `Assertions.lean`

- **`ModExpApproxValidDistUniform`** — the final claim: there is a single
  constant `K ≥ 0`, independent of `η`, the configuration, or the input
  state, such that on every valid unit state the approximate
  modular-exponentiation gate is within `tbits x · stepErr K η` of the ideal
  gate. Proved in `Main.lean` from `Proofs/ModExp.lean`'s
  `modExpApprox_valid_dist_uniform`.
