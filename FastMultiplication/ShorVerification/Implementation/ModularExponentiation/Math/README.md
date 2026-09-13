# `Math/`

Pure mathematics, no framework/register dependencies: the numerical core of
Algorithm 1's Step-1 QPE tail-mass bound, extracted from `Proofs/Step1QPE.lean`
into a semantics-free module. Everything here is stated in terms of `M : ℕ`,
real phases, and finite sums — nothing refers to the project's
state-semantics/register-encoding layer.

## `QPETail.lean`

- **`qpeKernel M θ t`** — the normalized Fourier kernel for phase `θ` sampled
  on an `M`-point inverse-QFT grid.
- **`qpeCircularDistance`** — distance from `θ` to grid point `t/M` on the
  unit circle (wraps around).
- **`qpeCircularTail`** — the set of labels whose circular distance to `θ` is
  at least `δ`.

The file's sections, in order:

- **Zero-phase exactness** — the degenerate case `θ = 0`: the kernel is then
  a geometric sum over a nontrivial root of unity, so it vanishes at every
  nonzero label. Apex: **`qpeKernel_zero_phase_bad_mass_zero`** — at zero
  phase, all bad mass is exactly 0, not just small.
- **Kernel chord bound** — the pointwise estimate driving everything: writes
  the kernel as a geometric sum via a root of unity `qpeRoot`, bounds the
  numerator by 2, and bounds the chord `‖qpeRoot - 1‖` below by
  `4 · (circular distance)` using the Jordan-type inequality
  `2·min(u, 1-u) ≤ |sin(πu)|`. Apex: **`qpeKernel_norm_sq_le_circular_majorant`**
  — `‖qpeKernel‖² ≤ 1/(4·(M·dist)²)`.
- **Reciprocal-square tails** — two elementary real estimates: `∑ 1/n²` over
  `Icc L M` telescopes to `≤ 1/(L-1)`; starting the sum at `⌊a⌋₊` for `a ≥ 4`
  gives `≤ 128/a`. Apex: **`reciprocal_square_floor_tail_le`**.
- **Floor-shell geometry** — how many labels can share one value of
  `⌊M·dist⌋₊` (a "floor shell"). Resolves the circular distance into 4 cases
  (direct/wrapped × left/right of `θ`, tagged by **`qpeShellTag`**); shows two
  labels in the same shell and tag must coincide
  (**`qpe_same_floor_shell_same_tag`**), capping each shell at 4 tags × 2
  sides = 8 labels.
- **Tail majorant summation** — reindexes the tail sum by floor shell
  (**`qpeCircular_tail_floor_shell_partition`**) and combines it with the
  per-shell cap and the reciprocal-square tail sum. Apex:
  **`qpeKernel_circular_tail_le`** — `∑_{tail} ‖qpeKernel‖² ≤ 128/(M·δ)`; this
  is the analytic heart of the file.
- **Ordinary-fraction tail bound** — specializes to `θ = r/N` (`0 < r < N`),
  the phase Algorithm 1 actually produces, switching from circular distance
  to ordinary absolute-value windows. Final apex theorem of the whole file:
  **`qpeKernel_bad_mass_le_grid_ratio`** — given the standard precision
  hypothesis `(2 + 1/(2η))² ≤ M/D`, the ordinary-window bad mass is
  `≤ 128 · (D / (M·η))`.

`Proofs/Step1QPE.lean` (Step 1 of the Algorithm 1 proof outline, see
`Proofs/README.md`) supplies the `alg1*`-semantics glue around
`qpeKernel_bad_mass_le_grid_ratio` to turn this pure-math estimate into the
actual Step-1 QPE tail bound for Algorithm 1.
