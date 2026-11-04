# `Table_Generation/Programs/`

Concrete synthesis programs assembled from the `Builders/` fragments, plus
their end-to-end certification.

## `WithProduct.lean`

Defines no new declarations of its own; it certifies `genOpsWithProduct`
(from `Builders/Fragments.lean`) end to end. It proves the per-point fragment
`opsForPointWithProduct` returns to `State.start_state`
(`opsForPointWithProduct_returns_to_original`) and lifts that across a whole
point list to `genOpsWithProduct_returns_to_original`. It then proves the
stronger, *ordered* consumption property `ProgConsumesPts` for one point
block (`opsForPointWithProduct_ProgConsumesPts`) and for the full generator
(`genOpsWithProduct_ProgConsumesPts`), and finally derives the unordered
`genOpsWithProduct_PhaseProductCoverage` — the statement that
`genOpsWithProduct hk pts`, run from `start_state`, covers exactly `pts` at
its `phaseProduct` checkpoints.
