import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Classical

/-!
# Factoring reduction definitions

This file contains the classical predicates used by the factoring-to-order
finding reduction: periods, Shor's success conditions, nontrivial factors, and
the finite choice sets used for probability statements.
-/

/-! =========================================================
    Section 1: Periods and multiplicative order
========================================================= -/

def is_period (a r N : ℕ) : Prop :=
  orderOf (a : ZMod N) = r

noncomputable def ord (a N : ℕ) (hgcd : Nat.gcd a N = 1) : ℕ :=
  orderOf (ZMod.unitOfCoprime a ((Nat.coprime_iff_gcd_eq_one).2 hgcd))

/-! =========================================================
    Section 2: Success conditions and factors
========================================================= -/

-- Two conditions:
-- (1) r is even
-- (2) a^(r/2) ≡ -1 (mod N) does not hold.
def shor_success_conditions (a r N : ℕ) : Prop :=
  (Even r) ∧ ((a : ZMod N) ^ (r / 2) ≠ -1)

-- A non-trivial factor is a divisor d, where 1 < d < N and d divides N
def is_nontrivial_factor (d N : ℕ) : Prop :=
  1 < d ∧ d < N ∧ d ∣ N

/-! =========================================================
    Section 3: Choice sets for success probabilities
========================================================= -/

-- a is a successful choice if there exists a period r that satisfies the success conditions
def is_successful_choice (a N : ℕ) : Prop :=
  ∃ r, is_period a r N ∧ shor_success_conditions a r N

-- the set of valid a's; 1 < a < N and a coprime to N
noncomputable def valid_choices (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun a => 1 < a ∧ Nat.gcd a N = 1)

/-- The subset of valid 'a's that will successfully yield a factor. -/
noncomputable def successful_choices (N : ℕ) : Finset ℕ :=
  (valid_choices N).filter (fun a => is_successful_choice a N)
