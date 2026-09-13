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
A sufficient precision condition for the work register.

If `n = regSize data` and `m = regSize work`, this says

  2^(m - n) ≥ (2 + 1 / (2η))^2,

which is implied by the paper's choice
`m = n + ceil (2 * log₂ (2 + 1 / (2η)))`.
-/
def Algorithm1Precision (η : ℝ) (data work : Reg) : Prop :=
  0 < η ∧ η < (1 / 2 : ℝ) ∧ regSize work = regSize data + algorithm1ExtraBits η

end Shor
