# `Lowering/`

Turns a compiled circuit into a finite, structurally-checked *plan* for
lowering it to primitive `LowGate`s, and provides the public entry points that
build such a plan automatically from a workspace assumption.

## Plans are indexed by a policy

A plan is parameterised by a **`ShorLoweringPolicy`** — a width-indexed
choice of Toom-Cook table, so that a deep recursion may use a wide table
while the operands are wide and narrower ones as it descends. The policy is
fixed for a whole plan and threaded unchanged through every constructor; what
varies with depth is which table `P.choose initSize` hands back at that
level.

**The old names are the constant policy.** `StandardPhaseLoweringPlan k hk
pts hpts ops` is now an `abbrev` for
`PhaseLoweringPlan (constPolicy ⟨k, hk, pts, hpts, ops⟩)`, and
`standardSignedPhaseLoweringPlan` and friends are wrappers that build at that
policy. Fixed-table statements elsewhere in the codebase are therefore
byte-identical to what they were before policies existed — they are the
one-band case, not a separate mechanism.

## `Plan.lean`

- **`compiledSignedPhaseGate`** / **`compiledCSignedPhaseGate`** — the
  specific `Gate` a recursive step's child call must lower (i.e.
  `compileOpsToSignedGate`/`compileOpsToCSignedGate` applied at the next
  recursion width), named up front because the plan type below refers to them.
- **`PhaseLoweringPlan P initSize U`** — an inductive, finite certificate
  that gate `U` can be lowered under policy `P`: one constructor per
  primitive gate (`id`, `seq`, `H`, `X`, shifts, `AddScaled`, extend/dealloc,
  `RadixReverse`), plus `signedBase`/`signedStep` and
  `cSignedBase`/`cSignedStep` for signed phase products — either "stop here,
  use the naive base gate" or "recurse, carrying a concrete layout, capacity
  proof, and child plan".

  The recursive constructors carry the table they used and the evidence that
  the policy chose it: `signedStep` takes `(T : ToomCookTable)` together with
  `hT : P.choose initSize = some T`, and its child is a plan *at the same
  policy* for the next width. So a plan records not just that each level
  recursed but which table that level was entitled to. Correspondingly
  `signedBase` carries `∀ T, P.choose initSize ≠ some T` — stopping is only
  licensed where the policy offers nothing.
- **`lowerGateRec`** — the interpreter: erases a plan's proof data and returns
  the `LowGate` it certifies (structural recursion on the plan).
- **`StandardPhaseLoweringPlan`**, **`lowerPhasePlan`** — the plan type at
  the constant policy on one table (see above), and its interpreter.
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
- **`Policy.stepPlan`** / **`Policy.cStepPlan`** — one compiled recursive
  *step* at an explicitly given table: allocation + body + deallocation, with
  the child supplied by a `recurse` callback. The step knows nothing about
  where its table came from.
- **`Policy.signedPlanOf`** / **`Policy.cSignedPlanOf`** — the *dispatcher*:
  given the policy's answer at this width, either take a step at the table it
  named or stop at the base case. Note the shape — the lookup result is an
  explicit argument,

  ```lean
  ∀ (o : Option ToomCookTable), P.choose (phaseInputSize x z) = o → PhaseLoweringPlan P …
  ```

  rather than a `match h : P.choose … with` inside the body. Written the
  latter way the definition unfolds to an `Option.casesOn` under an `Eq.ndrec`
  motive, which `split` and `cases` cannot see through, and every downstream
  proof about the dispatcher becomes unworkable. Passing the result in keeps
  both branches reachable by `cases o`.
- **`Policy.signedPlan`** / **`Policy.cSignedPlan`** — the dispatcher applied
  to its own lookup (`… _ rfl`). These are the general planners.
- **`standardSignedPhaseLoweringPlan`** / **`standardCSignedPhaseLoweringPlan`**
  — the canonical planners at a single fixed table: `Policy.signedPlan` at
  the constant policy, with the workspace precondition converted by
  `Policy.workspaceOK_of_const` from the familiar
  `SignedRecursiveWorkspaceOK`/`CSignedRecursiveWorkspaceOK`. These are what
  everything else in the codebase actually calls to get a plan, and
  `Policy.signedPlan_constPolicy` identifies them with the dispatcher's
  `some` branch by `rfl`.

## `Lower.lean`

- **`lowerSignedPhaseProdWithWorkspace`** / **`lowerCSignedPhaseProdWithWorkspace`**
  — the two public top-level constructors: build the canonical standard plan
  from a root workspace assumption and lower it. These are the functions
  `Spec/Assertions.lean`'s claims are about, and what the rest of the
  codebase (`QFT`, `Shor`, …) actually imports to get a lowered
  phase-product circuit.
