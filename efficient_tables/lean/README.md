# `lean/` — layered proof library

The Lean modules are grouped into eight dependency layers, listed here from bottom to top. A file may import only from its own layer or from a layer above it in this list; `scripts/gen_docs_graph.py` asserts that on every run. `Helpers/` is a separate, standalone library.

| layer | what it holds |
| --- | --- |
| `Foundations/` | Word-counting and budget arithmetic with no dependence on the table model. |
| `Source/` | The source-level program model and the contracts for the best-known tables. |
| `Model/` | The exact model: instruction language, width scanner, interpreter, and the profile algebra. |
| `Planner/` | The recursive planner, its optimality theorems, and the exact integer rotation price. |
| `PhaseProduct/` | The phase identity and the finite-catalogue end-to-end optimum (`PhaseProduct.Catalog.EndToEnd`). |
| `Provider/` | Raw ladders, profile intervals, the baseline ceiling, shift-block compression, interpolation weights, and the finite effective provider with its exhaustive optimizer. |
| `ILPEncoding/` | The affine cost encoding of the shared-ladder objective and the bit-size bounds on it. |
| `Alignment/` | Alignment of the Fortran solver's search with the Lean model, and the sparse-threshold census. |

**What is and is not claimed** is stated in the [top-level README](../README.md); nothing here proves polynomial-time synthesis of optimal tables.

The main end-to-end theorem is `Paper.PPEndToEnd.pp_through_arity_K`, now in `PhaseProduct/Catalog/EndToEnd.lean`. Lean namespaces were not changed by the reorganization, only file paths and module names; `MODULE_MAP.md` maps every old module name to its new one.

**Added after the reorganization.** Four self-contained developments live in `Foundations/` (`SmallPoint/`, `RuntimeComposition/`, `SeparationLemmas/`, `PairedCharge/`) and the exact charge of the grouped baseline in `Provider/Ceiling/GroupedCharge.lean`. They have no old flat names; they are listed at the end of `MODULE_MAP.md`. The axiom audit of the declarations named in `LEAN_MAP.md` is `scripts/AxiomAudit.lean`.
