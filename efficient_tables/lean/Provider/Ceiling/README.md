# `Ceiling/`

The ceiling on the charge of a literal baseline source table, built up from dyadic coefficient and point bounds through grouped scans.

## `GroupedCharge.lean` (added after the reorganization)

Exact charge of the grouped literal baseline `Paper.F3ChargeCeiling.groupedLiteralBaseline` (the "C1"
construction: every nonzero finite point is built in register 0 from the basis rows, checkpointed and undone):

| Lean theorem | Statement |
|---|---|
| `Paper.F3ChargeCeiling.groupedLiteralBaseline_charge` | for `2 ≤ k ≤ K`: `charge = 4·(k−1)·(2k−3)` (exact) |
| `Paper.F3ChargeCeiling.groupedLiteralBaseline_charge_le` | `charge ≤ 8·k·k` |

The baseline's legality and its `8k²` scan peaks are checked in `Grouped.lean` and `GroupedPeak.lean`. This is a
different construction from the paper's *paired* constructor (charge `≤ 6k²`), whose legality is a paper proof; see
`../../Foundations/PairedCharge/` for the counting of that skeleton. Axioms: `scripts/AxiomAudit.lean`.
