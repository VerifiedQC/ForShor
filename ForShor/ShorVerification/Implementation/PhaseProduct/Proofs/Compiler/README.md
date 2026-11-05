# `Proofs/Compiler/`

Correctness of the `Compiler/` and `Gates/` definitions: proves the compiled
circuits actually compute the phase products they're supposed to. Internal
order: `Support`/`WidthSoundness` → `Allocation`/`Body/*`/`Interpolation` →
`Compilation` → `Correctness` (each may use anything from the ones before
it).

The folder's two headline results, in **`Correctness.lean`**:

- **`eval_compileOpsToSignedGate_correct`** — on any *clean* workspace state
  (not just a basis ket), the compiled signed circuit evaluates exactly like
  the high-level `Gate.SignedPhaseProd phi x z`.
- **`eval_compileOpsToCSignedGate_correct`** — the same for the controlled
  circuit against `Gate.CSignedPhaseProd`.

These are what `Proofs/Lowering/` builds on to prove the lowered (`LowGate`)
circuit correct. Everything else in this folder — allocation correctness,
the Toom-Cook interpolation identity, and the whole `Body/` subfolder proving
the annotated body evaluates to the right phase scalar — assembles into these
two theorems via `Compilation.lean`. See `Body/README.md` for the body proof
in particular.
