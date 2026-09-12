# `Table_Generation/Core/`

The register/state model, the op language and its partial execution
semantics, the phase-product coverage predicates, a small set of proof
tactics, and the reusable lemma layer built on top of all of that.

## `Registers.lean`

- **`Register k`** — a linear combination of `x₀,…,x_{k-1}` with integer
  coefficients, represented as `Fin k → ℤ`.
- **`State k`** — `k` registers, i.e. `Fin k → Register k`.
- **`Register.zero`, `Register.negate`, `Register.shiftL`, `Register.shiftR?`,
  `Register.addScaled`** — the primitive register-level operations: the zero
  register, coefficient negation, left shift by `n` (multiply by `2^n`),
  right shift by `n` (returns `none` unless every coefficient is divisible by
  `2^n`), and `dst ← dst + (±1)·src·2^shift`.
- **`State.start_state`** — the basis state: register `i` holds exactly the
  unit vector `x_i`. The canonical starting/ending state for every synthesis
  proof in this subtree.
- **`State.setReg`, `State.negateReg`, `State.shiftLReg`, `State.shiftRReg?`,
  `State.addScaledReg`** — the state-level lifts of the register operations
  above, each touching only the named register index.
- **`Operations.Point`** — an interpolation point: `.int z` or `.frac m`
  (read as `1/m`).
- **`Operations.valid_ops k`** — the primitive instruction set every
  table-generation program is built from: `shiftL`, `shiftR`, `negate`,
  `addScaled`, `phaseProduct`.
- **`Operations.inv`** — the syntactic inverse of one operation (`shiftL` ↔
  `shiftR`, flips `negSrc` on `addScaled`, `negate`/`phaseProduct` are
  self-inverse).

## `Language.lean`

- **`Prog k`** — a program: `List (valid_ops k)`.
- **`applyOp?`** — executes one operation against a state; only `shiftR` can
  fail (returns `none` on inexact division).
- **`apply_Op_inverse`** — reverses a program and inverts each op, giving a
  candidate "undo" program.
- **`run?`** — executes a program left to right, short-circuiting to `none`
  on any failing step.
- **`Prog.OpOK`, `Prog.WellFormed`** — an op (resp. whole program) is
  well-formed if no `addScaled` writes a register into itself
  (`dst ≠ src`).
- **`Prog.SHL`, `Prog.SHR`, `Prog.NEG`, `Prog.ADD`, `Prog.SUB`** —
  singleton-program constructors for each primitive, backing the infix
  notation `<<s=`, `>>s=`, `neg`, `+:= … <<`, `-:= … <<`, `;;`.
- **`Prog.runAtStep?`** — executes just the first `t` steps of a program.
- **`MatchesAt`, `MatchesAtState`** — matcher-function shapes: does a given
  register (resp. a state at a given index) encode the row expected for an
  interpolation `Point`.
- **`expectedRow`** — the canonical row a register should hold for a point:
  `z^j` for `.int z`, the rescaled reciprocal powers `m^(k-1-j)` for
  `.frac m`.
- **`regEqExpected`, `matchesAt_pointRow`, `matchesAt_pointRow_state`** —
  Boolean matchers comparing an actual register/state against
  `expectedRow`.
- **`finZero`, `finLast`, `pointAnchor`** — the distinguished `0`/`k-1`
  register indices, and which one a point's row is anchored at
  (`.int` → `finZero`, `.frac` → `finLast`).
- **`expectedRow2`, `matchesAt_pointRow_state2`** — a variant expected-row and
  matcher that forces the anchor coordinate to `1` regardless of what
  `expectedRow` says there (proved to agree with `expectedRow`/
  `matchesAt_pointRow_state` at the correct anchor).
- **`List.eraseFirstMatch?`** — removes the first list element satisfying a
  predicate, or returns `none` if nothing matches.
- **`phaseCoverageFrom?`, `phaseProduct_coverage_check`** — Boolean check
  that running a program consumes every point in a target list, in any
  order, exactly at its `phaseProduct` checkpoints.
- **`ProgEq`** (notation `≃ₚ`) — two programs are equivalent if they agree on
  every input state.
- **`PhaseProductCoverageM`, `PhaseProductCoverage`** — the propositional
  (inductive) version of phase-product coverage, parameterized by an
  arbitrary state-matcher `M`; `PhaseProductCoverage` instantiates `M` to
  `matchesAt_pointRow_state`.
- **`ProgConsumesPts`** — a stronger, *ordered* coverage predicate: the
  program's `phaseProduct` checkpoints must consume the given points in
  exactly that left-to-right order.

## `ListHelpers.lean`

Three trivial named restatements of existing `List` facts
(`List.mem_cons`, `List.nodup_cons`, `List.mem_finRange`) used as a shared
vocabulary by the later coverage proofs; it introduces no new definitions.

## `RegisterLemmas.lean`

Basic algebraic facts about the model in `Language.lean`/`Registers.lean`:
`run?` simp lemmas (including how `run?` distributes over `++`), commutation
and cancellation identities for `setReg`/`shiftLReg`/`negateReg` (e.g. double
negation is the identity, same-register shifts add exponents,
shift-then-negate commutes), the `ProgEq` equivalence relation's `refl`/
`symm`/`trans`/congruence lemmas, and the final "well-formed undo" theorem
(`run?_inverse_undoes_WF`) showing that running `apply_Op_inverse p` after a
successful, well-formed run of `p` restores the original state.

## `RunLemmas.lean`

- **`NoPhase`** — a program contains no `phaseProduct` operation at all; used
  to mark purely-arithmetic build/uncompute fragments that structurally
  cannot consume any point.

Otherwise this file is proof-only: it establishes how `PhaseProductCoverage`
composes across program concatenation (`phaseProduct_coverage_check_append*`,
plus helpers to extract the intermediate state a coverage proof runs to), and
proves that `NoPhase` is preserved by append, `reverse`, and `map inv`, and
that the `computeLocal` build program and its inverse are both `NoPhase`.

## `Coverage.lean`

- **`SafeProg`** — every `addScaled` operation appearing anywhere in the
  program has a distinct source and destination register (a safety condition
  close to `Prog.WellFormed`, stated directly on arbitrary splits of the
  program).
- **`ProgConsumesPtsSafe`** — structure bundling a `ProgConsumesPts` proof
  together with a `SafeProg` proof for the same program.
- **`PhaseBlock`** — one phase block: an arithmetic prefix (`arith`, proved
  `NoPhase`) that runs to a state whose register `i` matches a target
  `Point`, packaged together with the run and match proofs.
- **`PhaseBlock.toProg`** — the concrete program of one phase block: the
  arithmetic prefix followed by a single `phaseProduct i`.
- **`BlockDecomposition`** — inductive: a program decomposes into a sequence
  of phase blocks (one per point consumed, in order) plus a trailing
  phase-free tail once all points are exhausted.

## `Tactics.lean`

- **`example_prog_1`** — a hand-written 3-register example program used to
  exercise the coverage machinery.
- **`example_prog_2`** — a larger 3-register example program (also certified
  in `Table_Generation/Examples.lean`).
- **`example_prog_3`** — a 4-register example program.
- **`prove_coverage n`** — a custom `elab`-defined tactic that discharges
  `phaseProduct_coverage_check` goals by unfolding the relevant definitions
  and case-splitting on the helper lemma `x_fin_checker n`.
- **`returns_to_original?`** — a custom `elab`-defined tactic that discharges
  "this program returns to `start_state`" goals via `simp` plus
  case-splitting on register indices.
