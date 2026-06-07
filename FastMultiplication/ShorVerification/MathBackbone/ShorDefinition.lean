import FastMultiplication.ShorVerification.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Shor

/-!
# Classical Shor Algorithm Math

This file collects the classical number-theoretic and postprocessing material
needed by the top-level Shor correctness statement.  It deliberately stays
away from circuit semantics, so `ShorDefinition` can focus on the quantum
circuit and measurement interfaces.
-/

/-! =========================================================
    Section 1: Order-finding parameters

    These definitions describe the multiplicative order being recovered and
    the standard size assumptions on the control and work registers.
========================================================= -/

/-- `r` is the multiplicative order of `a` modulo `N`. -/
def Order (a N r : ℕ) : Prop :=
  ∃ h : Nat.Coprime a N, r = orderOf (ZMod.unitOfCoprime a h)

noncomputable def ord (a N : ℕ) (hgcd : Nat.gcd a N = 1) : ℕ :=
  orderOf (ZMod.unitOfCoprime a ((Nat.coprime_iff_gcd_eq_one).2 hgcd))

/-- Classical size and coprimality conditions used in the correctness proof. -/
def BasicSetting (a r N m n : ℕ) : Prop :=
  0 < a ∧ a < N ∧
  Order a r N ∧
  N^2 < 2^m ∧ 2^m ≤ 2 * N^2 ∧
  N < 2^n ∧ 2^n ≤ 2 * N

/-! =========================================================
    Section 2: Good outcomes and continued fractions

    This section isolates the rational-approximation condition that a measured
    outcome must satisfy and the abstract continued-fraction recovery interface.
========================================================= -/

noncomputable def GoodOutcome (j m N r : ℕ) : Prop :=
  ∃ k, Nat.Coprime k r ∧
    |((j:ℝ)/(2^m:ℝ)) - ((k:ℝ)/(r:ℝ))| < (1 / (2*(N:ℝ)^2))

structure CFOut where
  num : ℕ
  den : ℕ
deriving DecidableEq

def approxRat (o Q k r : ℕ) (δ : ℝ) : Prop :=
  (Q > 0) ∧
  abs ((o : ℝ)/(Q : ℝ) - (k : ℝ)/(r : ℝ)) ≤ δ

/-- Abstract continued-fraction / rational-approximation postprocessing. -/
class ContinuedFractionPost where
  step : ℕ → ℕ → ℕ → CFOut
  denom : ℕ → ℕ → ℕ → ℕ := fun t o Q => (step t o Q).den

lemma CF_recovers_denominator [ContinuedFractionPost]
  (T : ℕ → ℕ)
  {o Q k r : ℕ}
  (happrox : approxRat o Q k r (1 / (2 * (Q : ℝ))))
  (hgcd : Nat.gcd k r = 1) :
  ∃ t, t < T Q ∧ ContinuedFractionPost.denom t o Q = r := by
  sorry

/-! =========================================================
    Section 3: Classical postprocessing success indicator

    The quantum proof produces a distribution on measurement outcomes; these
    definitions express the classical scan over continued-fraction candidates.
========================================================= -/

abbrev OrderVerifier := ℕ → Bool

variable [ContinuedFractionPost]

noncomputable def OF_post
  (T : ℕ → ℕ) (verify : OrderVerifier) (o Q : ℕ) : ℕ :=
  let Tmax := T Q
  let rec go : ℕ → ℕ
    | 0      => 0
    | t + 1  =>
        let d := ContinuedFractionPost.denom t o Q
        if verify d then d else go t
  go Tmax

noncomputable def r_found (T : ℕ → ℕ) (verify : OrderVerifier) (o Q r : ℕ) : ℝ :=
  if OF_post (T := T) verify o Q = r then (1 : ℝ) else 0

/-- The asymptotic success-probability constant appearing in the final bound. -/
noncomputable def κ : ℝ := (4 * Real.exp (-2)) / (Real.pi ^ 2)

end Shor
