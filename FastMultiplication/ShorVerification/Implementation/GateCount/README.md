# GateCount

This folder proves the asymptotic gate-count bound for the lowered Shor
implementation. It starts with a concrete cost model for `LowGate`, proves bounds for PhaseProduct and QFT lowering, then assembles those bounds into the final Shor order-finding estimate.

The final results are the `O(n^(2 + epsilon))` gate-count theorems:

```lean
shorGateCountBound_of_setup
exists_shorGateCountBound
exists_k_shorGateCountBound_of_programOK
```


## Final Approach

The proof is organized around one comparison rate for PhaseProduct and one
coarser comparison rate for the full Shor circuit.

PhaseProduct uses

```text
n^(log_k(q k))
```

where `q k` is the number of recursive PhaseProduct calls(`2k-1`) produced by the
Toom-Cook interpolation program.

The complete Shor circuit uses

```text
n^(2 + epsilon)
```

The main strategy is:

1. Define a concrete cost model for lowered gates.
2. Prove unsigned and controlled PhaseProduct bounds at rate
   `n^(log_k(q k))`.
3. Prove exact QFT lowering via the Cooley-Tuckey Decomposition is bounded by the same PhaseProduct rate.
4. Prove one controlled modular-multiplication core is bounded by the
   PhaseProduct rate.
5. Sum that core bound over modular exponentiation, adding one factor of `n`.
6. Add the order-finding QFT and initialization costs.
7. Choose `k` large enough that `log_k(q k) <= 1 + epsilon`, converting the
   full exponent to `2 + epsilon`.

## Main Theorems

The PhaseProduct endpoint is:

```lean
phaseProductGateCountBound_of_programOK
```

This proves `PhaseProductGateCountBound` for any interpolation program
satisfying `PhaseProductProgramOK`, which is C1-C4: the conditions that make a
Toom-Cook table admissible. The recurrence is solved against the number of
recursive leaves, `phaseProductCount ops = q k`, which C3 and `hpts` supply
through `ProgConsumesPts.phaseProductCount_eq` in
`PhaseProduct/Proofs/Compiler/Support.lean`: ordered point consumption peels one
point per `phaseProduct` operation and passes the list through every other
operation, so leaves and interpolation points are in bijection.

The controlled PhaseProduct endpoint is:

```lean
CPhaseProductReduction.cPhaseProductGateCountBound_of_programOK
```

This proves `CPhaseProductGateCountBound`, using the unsigned PhaseProduct
bound plus a constant-factor controlled overhead.

The QFT endpoint is:

```lean
qftGateCountBound_of_programOK
```

This proves `QFTGateCountBound` for the standard exact-QFT lowering plan, using
the PhaseProduct theorem for the split interaction at each QFT recursion node.

The Shor component assembly endpoint is:

```lean
shorGateCountBound_of_programOK
```

This proves `ShorGateCountBound` once the chosen `k` has
`phaseProductExponent k <= 1 + epsilon`.

`ShorGateCountBound` is parametric in the per-step precision `eta`, under a
work-width budget: fix any `cWork >= 1`, and one constant `C` serves every
`eta` whose `algorithm1ExtraBits` fit `(cWork - 1) * n`. Shor's own schedule
`eta = delta/n^2` is one such choice; `shorGateCountBoundShorEta_of_bound`
and `shorGateCountBoundShorEta_of_setup` specialise to it, and are the only
public statements here that mention `delta`.

The per-submission endpoint is:

```lean
shorGateCountBound_of_setup
```

This proves `ShorGateCountBound` for an arbitrary `ShorLoweringSetup` - any
admissible table, not only the generated one. A setup's `good`, `consumes` and
`returns` fields are `PhaseProductProgramOK`, which is what
`ShorLoweringSetup.programOK` (`Definitions.lean`) records, so the submission
conditions are the only hypotheses. Here `epsilon` is a hypothesis rather than
a choice: a table fixes its own arity `k`, and with it its exponent
`phaseProductExponent k = log (2k - 1) / log k`, so a `k = 2` table runs at
roughly `n^2.585` and supports no smaller `epsilon`.

The fully existential endpoint is:

```lean
exists_shorGateCountBound
```

This chooses both a suitable `k` and a generated PhaseProduct program. Driving
`epsilon` towards `0` means letting `k` grow, which is why this form quantifies
over `k` existentially where `shorGateCountBound_of_setup` takes the exponent
bound as a hypothesis.

## Folder Layout

```text
GateCount/
  Definitions.lean
  PhaseProduct/
    Lemmas.lean
    Main.lean
  QFT_GateCount.lean
  Shor_GateCount.lean
```