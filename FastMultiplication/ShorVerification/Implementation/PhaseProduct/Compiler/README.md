# `Compiler/`

Definitions for the recursive phase-product compiler: turning a pair of
registers `x`, `z` and a source arithmetic program into a concrete `Gate`
circuit. Internal order: `Layout → Widths → Coefficients → Compile →
Workspace` (each file may use anything from the ones before it).

## `Layout.lean`

- **`LayoutState k`** — the current chunk-to-register assignment: an `xslot`/`zslot`
  function from `Fin k` to `ExtReg`, i.e. where each of the `k` chunks of `x`
  and `z` currently live.
- **`WidthState k`** / **`NeededWidths k`** — plain width bookkeeping (no
  registers): the current logical width of each chunk, and the maximum width
  each chunk will need once the whole source program has run.
- **`ValidPhaseSplit`**, **`PhaseSplitLayout parent k W`** — the abstract
  interface for splitting one extendable register into `k` "top-heavy" active
  chunks (the last chunk absorbs the remainder) plus a disjoint reserve
  partition.
- **`Gate.PhaseProductLayout x z k`** — a pair of compatible `PhaseSplitLayout`s
  for `x` and `z`, with a proof that no chunk of `x` overlaps any chunk of `z`.
- **`ExtReg.CanGrowTo`**, **`growExtRegTo`** — whether/how a register can be
  widened in place to a target width using its reserve.
- **`initSignedLayoutState`** — the starting `LayoutState` built directly from
  a `PhaseProductLayout`'s split chunks.
- **`targetSignedLayoutState`** — the same layout after every slot has been
  grown to the common width the source program will need.
- **`ReserveBudget parent k`** — a partition of a parent register's reserve
  into `k` child reserve sizes that sum to the parent's total capacity.

## `Widths.lean`

- **`scanNeededWidths`** — walks the source program once, tracking how wide
  each chunk's logical value grows (shifts, negation, scaled addition), and
  returns the resulting `NeededWidths`.
- **`phaseInputSize`** — `max x.width z.width`, the size used to decide
  whether a phase product should recurse again.
- **`nextSignedWidth`** — the width the *next* recursion level will actually
  need, i.e. `commonNeededWidth (scanNeededWidths x z ops)`.

## `Coefficients.lean`

- **`q k`** — the number of interpolation points needed for a radix-`k`
  decomposition, `2k - 1`.
- **`interpMatrix`**, **`phaseCoeffFromPts`**, **`cramerCoeffFromPts`** — build
  the interpolation matrix from a chosen point set and solve for the phase
  coefficients (two equivalent formulations: matrix inverse and Cramer's
  rule, the latter computable).
- **`alternatingPoint`**, **`genInterpolationPoints`** — the canonical point
  set actually used everywhere: `0, ∞, 1, -1, 2, -2, …` (`2k-1` points).
- **`GoodToomCookPoints`**, **`toMathPoint`** — the bridge from this compiler's
  own `Point`/interpolation-row representation to the pure Toom-Cook algebra
  in `Math/ToomCook.lean`.

## `Compile.lean`

- **`AnnotatedOp k`** — a source operation tagged with which interpolation
  point (if any) its phase-product leaf corresponds to.
- **`compileOpsToSignedGate`** — the full signed compiler: allocate widened
  chunks, emit the annotated-body circuit (arithmetic gates plus one
  `SignedPhaseProd` per phase-product leaf, phased by the matching
  coefficient), then deallocate back down.
- **`controlPhaseLeaves`**, **`compileOpsToCSignedGate`** — wraps only the
  phase-product leaves of a compiled circuit with a shared control qubit,
  giving the controlled compiler.
- **`Gate.PhaseProductLayout.ControlDisjoint`** — the control qubit must sit
  outside every child register the layout touches.

## `Workspace.lean`

- **`RecursivePhaseWorkspace.reserveNeed`** — the conservative reserve (on
  each side) that a complete recursive compilation needs: growth room for the
  current level plus one full descendant reserve per chunk.
- **`SignedRecursiveWorkspaceOK`** / **`CSignedRecursiveWorkspaceOK`** — the
  static (non-quantum) precondition packaging register disjointness plus
  "the reserve is big enough for the whole recursion" for the uncontrolled
  and controlled cases.
- **`PhaseSplitLayout.ofBudget`**, **`ReserveBudget.ofRequirements`** —
  construct a concrete split layout / reserve budget from per-child
  requirements, given that they fit in the parent's capacity.
- **`CanonicalSignedStep`**, **`canonicalSignedStep`** — the canonical,
  deterministic choice of layout for one recursive step: builds the layout,
  and proves it has enough capacity for the next level and that every child's
  recursive input size is exactly `nextSignedWidth`.
