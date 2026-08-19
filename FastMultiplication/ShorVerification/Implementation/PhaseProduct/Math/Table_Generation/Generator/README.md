# Table Generation Submission

This branch is the template for table-generation submissions. A submission
provides Lean definitions for the generated points and program, then proves the
two required correctness theorems.

Edit only:

- `Defs.lean`
- `Correctness.lean`

`Defs.lean` should define:

- `generatedPoints`
- `generatePointsInOrder`
- `generate`

`generatedPoints` must be the protected canonical point list from `Spec.lean`.
`generatePointsInOrder` may choose a different consumption order, but it must be
a permutation of that canonical list.

`Correctness.lean` should prove:

- `generatedPoints_valid`
- `generate_ProgConsumesPtsSafe`

Do not change the theorem statements. The verifier checks that the statements
match this template, rejects `sorry`, `admit`, new `axiom`/`constant`
declarations, and checks the final theorem axiom dependencies.

The current scoring target is `k = 4`, `PhaseTripleProduct`. The reported score
is:

- arithmetic operation count
- parallel phase-product layer count

The current reference result to beat is `46` arithmetic operations with `4`
parallel phase-product layers.

## Pull Request Submission

Create your submission branch from:

```text
submission/table-generation/template
```

Open a pull request with:

```text
base:    submission/table-generation/template
compare: your submission branch
```

For example, a branch named `submission/table-generation/alice` should open a PR
from `submission/table-generation/alice` into
`submission/table-generation/template`, not into `main`.

GitHub Actions runs the verifier when the PR is opened or updated. The workflow
posts a PR comment and uploads a JSON result artifact. Successful submissions
are closed automatically after the result is produced.
