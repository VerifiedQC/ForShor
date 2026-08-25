import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.DiophantineApproximation.ContinuedFractions
import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat

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
    outcome must satisfy and the continued-fraction recovery algorithm.
========================================================= -/
def approxRat
    (o Q k r : ℕ)
    (δ : ℝ) : Prop :=
  0 < Q ∧ 0 < r ∧
  abs ((o : ℝ) / (Q : ℝ) - (k : ℝ) / (r : ℝ)) ≤ δ

noncomputable def GoodOutcome
    (o Q r : ℕ) : Prop :=
  o < Q ∧
  ∃ k : ℕ, k < r ∧
    Nat.Coprime k r ∧
    r ^ 2 < Q ∧
    approxRat o Q k r (1 / (2 * (Q : ℝ)))

/--
The `t`th regular continued-fraction convergent of the measured ratio `o / Q`,
computed by Mathlib's recursive convergent algorithm.
-/
noncomputable def continuedFractionConvergent
    (t o Q : ℕ) : ℚ :=
  Real.convergent ((o : ℝ) / (Q : ℝ)) t

/-- The denominator tested by classical postprocessing at step `t`. -/
noncomputable def continuedFractionDenom
    (t o Q : ℕ) : ℕ :=
  (continuedFractionConvergent t o Q).den

private lemma continuedFraction_terminates (o Q : ℕ) :
    (GenContFract.of ((o : ℝ) / (Q : ℝ))).Terminates := by
  rw [GenContFract.terminates_iff_rat]
  exact ⟨(o : ℚ) / (Q : ℚ), by simp⟩

/-- The first index after the finite continued fraction for `o / Q` terminates. -/
noncomputable def continuedFractionTerminationIndex
    (o Q : ℕ) : ℕ :=
  Nat.find (continuedFraction_terminates o Q)

private lemma continuedFraction_terminatedAt (o Q : ℕ) :
    (GenContFract.of ((o : ℝ) / (Q : ℝ))).TerminatedAt
      (continuedFractionTerminationIndex o Q) :=
  Nat.find_spec (continuedFraction_terminates o Q)

/--
A proof-oriented uniform number of convergents sufficient for every outcome
`o < Q`. Callers may scan any larger bound.
-/
noncomputable def continuedFractionSearchBound (Q : ℕ) : ℕ :=
  (Finset.range Q).sup (fun o => continuedFractionTerminationIndex o Q) + 1

private lemma continuedFractionTerminationIndex_lt_searchBound
    {o Q : ℕ}
    (ho : o < Q) :
    continuedFractionTerminationIndex o Q < continuedFractionSearchBound Q := by
  apply Nat.lt_succ_of_le
  exact Finset.le_sup
    (f := fun o => continuedFractionTerminationIndex o Q)
    (Finset.mem_range.mpr ho)

private lemma reducedFraction_denominator
    {k r : ℕ}
    (hr : 0 < r)
    (hcop : Nat.Coprime k r) :
    (((k : ℤ) : ℚ) / ((r : ℤ) : ℚ)).den = r := by
  have h := Rat.den_div_eq_of_coprime
    (a := (k : ℤ)) (b := (r : ℤ))
    (by exact_mod_cast hr) (by simpa using hcop)
  exact_mod_cast h

def ContinuedFractionSearchComplete
    (T : ℕ → ℕ) : Prop :=
  ∀ Q : ℕ,
    continuedFractionSearchBound Q ≤ T Q

lemma CF_recovers_denominator
    (T : ℕ → ℕ)
    (hT : ContinuedFractionSearchComplete T)
    {o Q k r : ℕ}
    (ho : o < Q)
    (hrQ : r ^ 2 < Q)
    (happrox :
      approxRat o Q k r
        (1 / (2 * (Q : ℝ))))
    (hgcd : Nat.Coprime k r) :
    ∃ t : ℕ,
      t < T Q ∧
      continuedFractionDenom t o Q = r := by
  let q : ℚ := ((k : ℤ) : ℚ) / ((r : ℤ) : ℚ)

  have hqden : q.den = r := by
    simpa [q] using reducedFraction_denominator happrox.2.1 hgcd

  have hstrict :
      |(o : ℝ) / (Q : ℝ) - (q : ℝ)| <
        1 / (2 * (q.den : ℝ) ^ 2) := by
    rw [hqden]
    have hrQ' : (r : ℝ) ^ 2 < (Q : ℝ) := by
      exact_mod_cast hrQ
    have hr' : 0 < (r : ℝ) := by
      exact_mod_cast happrox.2.1
    have hbound :
        1 / (2 * (Q : ℝ)) < 1 / (2 * (r : ℝ) ^ 2) := by
      exact one_div_lt_one_div_of_lt (by positivity) (by nlinarith)
    exact lt_of_le_of_lt (by simpa [q] using happrox.2.2) hbound

  obtain ⟨n, hn⟩ := Real.exists_rat_eq_convergent hstrict
  let u := continuedFractionTerminationIndex o Q

  by_cases hnu : n ≤ u
  · refine ⟨n, lt_of_le_of_lt hnu ?_, ?_⟩
    · exact lt_of_lt_of_le
        (continuedFractionTerminationIndex_lt_searchBound ho) (hT Q)
    · rw [continuedFractionDenom, continuedFractionConvergent, ← hqden, hn]

  · have hun : u ≤ n := Nat.le_of_lt (Nat.lt_of_not_ge hnu)
    have hconv :
        Real.convergent ((o : ℝ) / (Q : ℝ)) u =
          Real.convergent ((o : ℝ) / (Q : ℝ)) n := by
      apply (Rat.cast_injective : Function.Injective (Rat.cast : ℚ → ℝ))
      rw [← Real.convs_eq_convergent, ← Real.convs_eq_convergent]
      exact (GenContFract.convs_stable_of_terminated hun
        (continuedFraction_terminatedAt o Q)).symm

    refine ⟨u, lt_of_lt_of_le ?_ (hT Q), ?_⟩
    · exact continuedFractionTerminationIndex_lt_searchBound ho
    · rw [continuedFractionDenom, continuedFractionConvergent,
        ← hqden, hn, ← hconv]

lemma GoodOutcome.exists_denominator_candidate
    (T : ℕ → ℕ)
    (hT : ContinuedFractionSearchComplete T)
    {o Q r : ℕ}
    (hgood : GoodOutcome o Q r) :
    ∃ t : ℕ,
      t < T Q ∧
      continuedFractionDenom t o Q = r := by
  rcases hgood with
    ⟨ho, k, _hkr, hgcd, hrQ, happrox⟩

  exact CF_recovers_denominator
    T hT ho hrQ happrox hgcd

abbrev OrderVerifier := ℕ → Bool

noncomputable def orderCandidates
    (T : ℕ → ℕ)
    (o Q : ℕ) : Finset ℕ :=
  (Finset.range (T Q)).image
    (fun t =>
      continuedFractionDenom t o Q)

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
        continuedFractionDenom t o Q = r) :
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
