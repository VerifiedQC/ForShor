# GateCount

This folder proves the asymptotic gate-count bound for the lowered Shor
implementation. It starts with a concrete cost model for `LowGate`, proves bounds for PhaseProduct and QFT lowering, then assembles those bounds into the final Shor order-finding estimate.

The final results are the two `O(n^(2 + epsilon))` gate-count theorem:

```lean
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
satisfying `PhaseProductProgramOK`.

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

The fully existential endpoint is:

```lean
exists_shorGateCountBound
```

This chooses both a suitable `k` and a generated PhaseProduct program.

## Folder Layout

```text
GateCount/
  Definitions.lean
  PhaseProduct/
    Lemmas.lean
    Main.lean
  QFT_GateCount.lean
  Shor_GateCount.lean
  Lemmas/
    LowGateCount.lean
```