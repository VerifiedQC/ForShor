import FastMultiplication.ShorVerification.Framework.Semantics.GateSemantics
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Modular-Exponentiation Precision

The concrete precision schedule for Algorithm 1 (`algorithm1ExtraBits`,
`Algorithm1Precision`) and the per-core norm error scale used by the
modular-exponentiation hybrid bound (`stepErr`).
-/

namespace Shor

/-- Per-core norm error scale used by the modular-exponentiation hybrid bound. -/
noncomputable def stepErr (K η : ℝ) : ℝ :=
  Real.sqrt (2 * (K * η))

/-- Extra work-register bits prescribed by the Algorithm 1 precision parameter. -/
noncomputable def algorithm1ExtraBits (η : ℝ) : ℕ :=
  ⌈2 * Real.logb 2 (2 + 1 / (2 * η))⌉₊

/--
The precision condition on the work register: the paper's width, pinned
exactly rather than bounded below.

With `n = regSize data` and `m = regSize work`, this fixes

  m = n + ⌈2 · log₂ (2 + 1 / (2η))⌉

which implies the paper's inequality `2^(m - n) ≥ (2 + 1 / (2η))^2`
(`Proofs/Core.lean`'s `pow_bound`) but is strictly stronger. The width is
pinned because both directions are load-bearing, in different proofs:

* `≥` — *enough* bits. `pow_bound` feeds the QPE/Fourier contraction estimate
  in `Proofs/Step1QPE.lean`. This is the direction the paper states, and the
  only one a correctness argument needs.
* `≤` — *not too many* bits. `Algorithm1Precision.work_width_le_mul`
  (`GateCount/Shor_GateCount.lean`) rewrites with this equality to bound
  `regSize work ≤ cWork * regSize data`, which the `O(n^(2+ε))` gate count
  depends on. A work register merely *at least* wide enough could be
  arbitrarily wide, and the resource estimate would not hold of it.

Relaxing this to `algorithm1ExtraBits η ≤ regSize work - regSize data` would
keep correctness and cost the gate-count theorem.
-/
def Algorithm1Precision (η : ℝ) (data work : Reg) : Prop :=
  0 < η ∧ η < (1 / 2 : ℝ) ∧ regSize work = regSize data + algorithm1ExtraBits η

end Shor
