# `Lowering/`

Turns a compiled circuit into a finite, structurally-checked *plan* for
lowering it to primitive `LowGate`s, and provides the public entry points that
build such a plan automatically from a workspace assumption.

## `Plan.lean`

- **`compiledSignedPhaseGate`** / **`compiledCSignedPhaseGate`** — the
  specific `Gate` a recursive step's child call must lower (i.e.
  `compileOpsToSignedGate`/`compileOpsToCSignedGate` applied at the next
  recursion width), named up front because the plan type below refers to them.
- **`PhaseLoweringPlan k hk pts hpts ops initSize U`** — an inductive,
  finite certificate that gate `U` can be lowered: one constructor per
  primitive gate (`id`, `seq`, `H`, `X`, shifts, `AddScaled`, extend/dealloc,
  `RadixReverse`), plus `signedBase`/`signedStep` and
  `cSignedBase`/`cSignedStep` for signed phase products — either "stop here,
  use the naive base gate" or "recurse, carrying a concrete layout, capacity
  proof, and child plan".
- **`lowerGateRec`** — the interpreter: erases a plan's proof data and returns
  the `LowGate` it certifies (structural recursion on the plan).
- **`StandardPhaseLoweringPlan`**, **`lowerPhasePlan`** — the plan type
  specialized to the canonical interpolation points, and its interpreter.
- **`lowerSignedPhaseProd`** / **`lowerCSignedPhaseProd`** — the public
  entry points: given a plan whose initial size is the actual operand
  `phaseInputSize`, produce the lowered `LowGate`.

## `PlanBuilders.lean`

Constructs plans (rather than just interpreting them), mirroring the compiler
one gate at a time:

- **`planAllocChunkGate`/`planDeallocChunkGate`** and their `*Aux`/whole-layout
  versions — plans for the per-chunk (de)allocation gates and their
  sequential composition.
- **`planCompileAnnotatedOpsToSignedGateAux`** (and the controlled
  `...CSignedGateAux`) — a plan for the annotated-body circuit, taking a
  `recurse` callback used at each phase-product leaf.
- **`planCompiledSignedPhaseGate`** / **`planCompiledCSignedPhaseGate`** —
  assembles allocation + body + deallocation plans for one full recursive
  level.
- **`standardSignedPhaseLoweringPlan`** / **`standardCSignedPhaseLoweringPlan`**
  — the canonical planners: given the static workspace precondition
  (`SignedRecursiveWorkspaceOK`/`CSignedRecursiveWorkspaceOK`), recursively
  choose either the naive base case or one compiled recursive step (via
  `canonicalSignedStep`), all the way down. These are what everything else in
  the codebase actually calls to get a plan.

## `Lower.lean`

- **`lowerSignedPhaseProdWithWorkspace`** / **`lowerCSignedPhaseProdWithWorkspace`**
  — the two public top-level constructors: build the canonical standard plan
  from a root workspace assumption and lower it. These are the functions
  `Spec/Assertions.lean`'s claims are about, and what the rest of the
  codebase (`QFT`, `Shor`, …) actually imports to get a lowered
  phase-product circuit.
