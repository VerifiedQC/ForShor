# `Foundations/`

Pure arithmetic about weighted words, branch counts and budgets, and four self-contained developments added after the reorganization (small integer points in a polyhedron, composition of stage costs, separation of signed sums of powers of two, charge counting of the paired constructor). Nothing here mentions the table model's definitions; the first group is consumed by the budget and encoding bounds in `ILPEncoding/`. Each of the four folders has its own README and an `Audit.lean`.

| file | formerly |
| --- | --- |
| `MachineResource.lean` | `MachineResource.Bounds` |
| `Counting/` | word, branch and budget counting (formerly several flat folders) |
| `SmallPoint/` | the small-integer-point bound `(t+1)·t!·B^t` (new) |
| `RuntimeComposition/` | arithmetic composition of stage-wise cost bounds (new; not a runtime theorem) |
| `SeparationLemmas/` | zero and anchored-integrality criteria for signed sums of powers of two (new) |
| `PairedCharge/` | charge counting of the paired constructor's instruction skeleton (new; counting only) |
