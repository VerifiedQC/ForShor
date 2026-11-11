# PhaseProduct

This folder builds the phase-product circuit, which applies the phase `exp(i·φ·x·z)` to two registers `x` and `z`, and proves it correct. There is a signed version and a controlled signed version.

The circuit is a Toom-Cook recursion. Each operand is cut into `k` chunks, the product phase is rebuilt from `2k - 1` smaller phase products plus some classical arithmetic, and the recursion bottoms out in a schoolbook circuit. Which Toom-Cook table is used at each width comes from a `ShorLoweringPolicy`. A single fixed table is just the policy with one band.

## Files

- `Statement.lean` has the definitions (the compiler, the lowering plans, the workspace model) and the statements of the theorems. It doesn't import anything else from this folder, so you can check the claims against it alone.
- `Proofs/` has all the lemmas, the gate-count proofs, and the table generator in `Proofs/Math/`. `Proofs/README.md` describes it in more detail.
- `Main.lean` proves the final theorems:
  - `lowerSignedPhaseProduct_correct` and `lowerCSignedPhaseProduct_correct`, with their `Policy.` versions: on a state whose workspace is big enough and clean, the lowered circuit does exactly what `Gate.SignedPhaseProd` (or `CSignedPhaseProd`) does.
  - `signedPhaseProductGateCountBound_of_programOK` and `cSignedPhaseProductGateCountBound_of_programOK`: the gate count grows like `n^(log_k(2k-1))` for any table that satisfies C1–C4.
  - `Policy.signedPhaseProductGateCountBound` and `Policy.cSignedPhaseProductGateCountBound`: for any admissible policy the gate count grows like `n^P.gateExponent`, which is `n^(log_k(2k-1))` for the arity `k` of the policy's first band.

If you're new here, read `Main.lean` first to see what's proved, then `Statement.lean` for what the claims mean.

## One thing to know

The interpolation weights are defined by Cramer's rule (`cramerCoeffFromPts`), because that's easy to prove things about. Evaluating it directly costs a sum over `(2k-1)!` permutations, which gets very slow from `k = 5` on. So `Statement.lean` also has a Gauss-Jordan version (`gjCoeffFromPts`) that checks its own inverse and falls back to Cramer if the check fails, and a `@[csimp]` lemma that makes compiled code use it. Proofs still only see Cramer's rule.

A `@[csimp]` lemma only affects code compiled after it, so it has to stay above everything in `Statement.lean` that calls `cramerCoeffFromPts`.
