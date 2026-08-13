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
  Order a N r ∧
  N^2 < 2^m ∧ 2^m ≤ 2 * N^2 ∧
  N < 2^n ∧ 2^n ≤ 2 * N

/-! =========================================================
    Section 2: Good outcomes and continued fractions

    This section isolates the rational-approximation condition that a measured
    outcome must satisfy and the abstract continued-fraction recovery interface.
========================================================= -/
structure CFOut where
  num : ℕ
  den : ℕ
deriving DecidableEq

def approxRat
    (o Q k r : ℕ)
    (δ : ℝ) : Prop :=
  0 < Q ∧ 0 < r ∧
  abs ((o : ℝ) / (Q : ℝ) - (k : ℝ) / (r : ℝ)) ≤ δ

noncomputable def GoodOutcome
    (o Q r : ℕ) : Prop :=
  ∃ k : ℕ, k < r ∧
    Nat.Coprime k r ∧
    r ^ 2 ≤ Q ∧
    approxRat o Q k r (1 / (2 * (Q : ℝ)))

/-- Abstract continued-fraction/rational-approximation postprocessing.

`searchBound Q` is a uniform number of convergent candidates sufficient for
inputs with denominator bounded by `Q`. The correctness field states that a
sufficiently accurate reduced fraction is found within that bound.
-/
class ContinuedFractionPost where
  step : ℕ → ℕ → ℕ → CFOut
  denom : ℕ → ℕ → ℕ → ℕ := fun t o Q => (step t o Q).den
  searchBound : ℕ → ℕ
  recovers_denominator :
    ∀ {o Q k r : ℕ},
      k < r → r ^ 2 ≤ Q →
      approxRat o Q k r (1 / (2 * (Q : ℝ))) →
      Nat.Coprime k r →
        ∃ t : ℕ, t < searchBound Q ∧ denom t o Q = r
  -- recovers_denominator :
  --   ∀ {o Q k r : ℕ},
  --     0 < r → k < r →  r ^ 2 ≤ Q →
  --     approxRat o Q k r (1 / (2 * (Q : ℝ))) →
  --     Nat.Coprime k r →
  --     ∃ t : ℕ, t < searchBound Q ∧ denom t o Q = r

def ContinuedFractionSearchComplete
    [ContinuedFractionPost]
    (T : ℕ → ℕ) : Prop :=
  ∀ Q : ℕ,
    ContinuedFractionPost.searchBound Q ≤ T Q

lemma CF_recovers_denominator
    [ContinuedFractionPost]
    (T : ℕ → ℕ)
    (hT : ContinuedFractionSearchComplete T)
    {o Q k r : ℕ}
    (hkr : k < r)
    (hrQ : r ^ 2 ≤ Q)
    (happrox :
      approxRat o Q k r
        (1 / (2 * (Q : ℝ))))
    (hgcd : Nat.Coprime k r) :
    ∃ t : ℕ,
      t < T Q ∧
      ContinuedFractionPost.denom t o Q = r := by
  rcases
      ContinuedFractionPost.recovers_denominator
        hkr hrQ happrox hgcd with
    ⟨t, ht, hdenom⟩

  exact
    ⟨t,
      lt_of_lt_of_le ht (hT Q),
      hdenom⟩

lemma GoodOutcome.exists_denominator_candidate
    [ContinuedFractionPost]
    (T : ℕ → ℕ)
    (hT : ContinuedFractionSearchComplete T)
    {o Q r : ℕ}
    (hgood : GoodOutcome o Q r) :
    ∃ t : ℕ,
      t < T Q ∧
      ContinuedFractionPost.denom t o Q = r := by
  rcases hgood with
    ⟨k, hkr, hgcd, hrQ, happrox⟩

  exact CF_recovers_denominator
    T hT hkr hrQ happrox hgcd

abbrev OrderVerifier := ℕ → Bool

variable [ContinuedFractionPost]

noncomputable def orderCandidates
    (T : ℕ → ℕ)
    (o Q : ℕ) : Finset ℕ :=
  (Finset.range (T Q)).image
    (fun t =>
      ContinuedFractionPost.denom t o Q)

noncomputable def verifiedOrderCandidates
    (T : ℕ → ℕ)
    (verify : OrderVerifier)
    (o Q : ℕ) : Finset ℕ :=
  (orderCandidates T o Q).filter
    (fun d => 0 < d ∧ verify d = true)

noncomputable def OF_post
    (T : ℕ → ℕ)
    (verify : OrderVerifier)
    (o Q : ℕ) : ℕ :=
  let candidates :=
    verifiedOrderCandidates T verify o Q

  if h : candidates.Nonempty then
    candidates.min' h
  else
    0

lemma denominator_mem_orderCandidates
    (T : ℕ → ℕ)
    {o Q r : ℕ}
    (h :
      ∃ t : ℕ,
        t < T Q ∧
        ContinuedFractionPost.denom t o Q = r) :
    r ∈ orderCandidates T o Q := by
  rcases h with ⟨t, ht, hdenom⟩
  rw [orderCandidates, Finset.mem_image]
  exact ⟨t, Finset.mem_range.mpr ht, hdenom⟩

lemma GoodOutcome.order_mem_candidates
    (T : ℕ → ℕ)
    (hT : ContinuedFractionSearchComplete T)
    {o Q r : ℕ}
    (hgood : GoodOutcome o Q r) :
    r ∈ orderCandidates T o Q := by
  apply denominator_mem_orderCandidates
  exact hgood.exists_denominator_candidate T hT

lemma mem_verifiedOrderCandidates
    (T : ℕ → ℕ)
    (verify : OrderVerifier)
    {o Q d : ℕ}
    (hcandidate : d ∈ orderCandidates T o Q)
    (hdpos : 0 < d)
    (hverify : verify d = true) :
    d ∈ verifiedOrderCandidates T verify o Q := by
  simp [
    verifiedOrderCandidates,
    hcandidate,
    hdpos,
    hverify
  ]

lemma OF_post_eq_of_mem_of_least
    (T : ℕ → ℕ)
    (verify : OrderVerifier)
    {o Q r : ℕ}
    (hr :
      r ∈ verifiedOrderCandidates T verify o Q)
    (hleast :
      ∀ d ∈ verifiedOrderCandidates T verify o Q,
        r ≤ d) :
    OF_post T verify o Q = r := by
  classical

  let candidates :=
    verifiedOrderCandidates T verify o Q

  have hr' : r ∈ candidates := by
    simpa [candidates] using hr

  have hnonempty : candidates.Nonempty :=
    ⟨r, hr'⟩

  unfold OF_post
  dsimp only

  rw [dif_pos hnonempty]

  apply Nat.le_antisymm

  · exact Finset.min'_le candidates r hr'

  · exact hleast
      (candidates.min' hnonempty)
      (by
        simpa [candidates] using
          Finset.min'_mem candidates hnonempty)
/-! =========================================================
    Section 3: Classical postprocessing success indicator

    The quantum proof produces a distribution on measurement outcomes; these
    definitions express the classical scan over continued-fraction candidates.
========================================================= -/


noncomputable def r_found (T : ℕ → ℕ) (verify : OrderVerifier) (o Q r : ℕ) : ℝ :=
  if OF_post (T := T) verify o Q = r then (1 : ℝ) else 0

/-- The asymptotic success-probability constant appearing in the final bound. -/
noncomputable def κ : ℝ := (4 * Real.exp (-2)) / (Real.pi ^ 2)
