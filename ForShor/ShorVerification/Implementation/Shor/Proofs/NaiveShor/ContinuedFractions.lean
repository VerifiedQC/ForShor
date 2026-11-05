import ForShor.ShorVerification.Implementation.Shor.Statement
import ForShor.ShorVerification.Implementation.Shor.Proofs.Math.Factoring_Reduction.Defs

/-!
# NaiveShor — continued fractions and the order

`GoodOutcome`, the proof that continued fractions recover the order from a good
outcome, the facts about the candidates `OF_post` chooses from, and
`is_period_ord`, which relates `ord` to the classical reduction's `is_period`.
-/

namespace Shor

/-- `r` is the multiplicative order of `a` modulo `N`. -/
def Order (a N r : ℕ) : Prop :=
  ∃ h : Nat.Coprime a N, r = orderOf (ZMod.unitOfCoprime a h)

/-- Classical size and coprimality conditions used in the correctness proof. -/
def BasicSetting (a r N m n : ℕ) : Prop :=
  0 < a ∧ a < N ∧
  Order a N r ∧
  N^2 < 2^m ∧ 2^m ≤ 2 * N^2 ∧
  N < 2^n ∧ 2^n ≤ 2 * N

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

private lemma reducedFraction_denominator
    {k r : ℕ}
    (hr : 0 < r)
    (hcop : Nat.Coprime k r) :
    (((k : ℤ) : ℚ) / ((r : ℤ) : ℚ)).den = r := by
  have h := Rat.den_div_eq_of_coprime
    (a := (k : ℤ)) (b := (r : ℤ))
    (by exact_mod_cast hr) (by simpa using hcop)
  exact_mod_cast h

lemma CF_recovers_denominator (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T)
    {o Q k r : ℕ} (ho : o < Q) (hrQ : r ^ 2 < Q)
    (happrox : approxRat o Q k r (1 / (2 * (Q : ℝ)))) (hgcd : Nat.Coprime k r) :
    ∃ t < T Q, (Real.convergent ((o : ℝ) / (Q : ℝ)) t).den = r := by
  let q : ℚ := ((k : ℤ) : ℚ) / ((r : ℤ) : ℚ)
  have hqden : q.den = r := by
    simpa [q] using reducedFraction_denominator happrox.2.1 hgcd
  have hstrict : |(o : ℝ) / (Q : ℝ) - (q : ℝ)| < 1 / (2 * (q.den : ℝ) ^ 2) := by
    rw [hqden]
    have hrQ' : (r : ℝ) ^ 2 < (Q : ℝ) := by exact_mod_cast hrQ
    have hr' : 0 < (r : ℝ) := by exact_mod_cast happrox.2.1
    have hbound : 1 / (2 * (Q : ℝ)) < 1 / (2 * (r : ℝ) ^ 2) := by
      exact one_div_lt_one_div_of_lt (by positivity) (by nlinarith)
    exact lt_of_le_of_lt (by simpa [q] using happrox.2.2) hbound
  obtain ⟨n, hn⟩ := Real.exists_rat_eq_convergent hstrict
  obtain ⟨u, hu, hterm⟩ := hT Q o ho
  by_cases hnu : n ≤ u
  · exact ⟨n, lt_of_le_of_lt hnu hu, by rw [← hqden, hn]⟩
  · have hun : u ≤ n := Nat.le_of_lt (Nat.lt_of_not_ge hnu)
    have hconv :
        Real.convergent ((o : ℝ) / (Q : ℝ)) u = Real.convergent ((o : ℝ) / (Q : ℝ)) n := by
      apply (Rat.cast_injective : Function.Injective (Rat.cast : ℚ → ℝ))
      rw [← Real.convs_eq_convergent, ← Real.convs_eq_convergent]
      exact (GenContFract.convs_stable_of_terminated hun hterm).symm
    exact ⟨u, hu, by rw [← hqden, hn, ← hconv]⟩

lemma GoodOutcome.exists_denominator_candidate (T : ℕ → ℕ)
    (hT : ContinuedFractionSearchComplete T) {o Q r : ℕ} (hgood : GoodOutcome o Q r) :
    ∃ t < T Q, (Real.convergent ((o : ℝ) / (Q : ℝ)) t).den = r := by
  rcases hgood with ⟨ho, k, _hkr, hgcd, hrQ, happrox⟩
  exact CF_recovers_denominator T hT ho hrQ happrox hgcd

/-- For a good outcome, the order is a candidate if it is positive and passes `verify`. -/
lemma GoodOutcome.order_mem_candidates (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T)
    (verify : ℕ → Bool) {o Q r : ℕ} (hgood : GoodOutcome o Q r) (hrpos : 0 < r)
    (hverify : verify r = true) : r ∈ orderCandidates T verify o Q := by
  obtain ⟨t, ht, hden⟩ := hgood.exists_denominator_candidate T hT
  simp only [orderCandidates, Finset.mem_filter, Finset.mem_image, Finset.mem_range]
  exact ⟨⟨t, ht, hden⟩, hrpos, hverify⟩

lemma OF_post_eq_of_mem_of_least (T : ℕ → ℕ) (verify : ℕ → Bool) {o Q r : ℕ}
    (hr : r ∈ orderCandidates T verify o Q)
    (hleast : ∀ d ∈ orderCandidates T verify o Q, r ≤ d) : OF_post T verify o Q = r := by
  have hne : (orderCandidates T verify o Q).Nonempty := ⟨r, hr⟩
  rw [OF_post, dite_eq_left hne]
  exact Nat.le_antisymm (Finset.min'_le _ r hr) (hleast _ (Finset.min'_mem _ hne))

end Shor

/-- Show equivalence between two period definitions -/
lemma is_period_ord (a N : ℕ) (hgcd : Nat.gcd a N = 1) :
  is_period a (Shor.ord a N hgcd) N := by
  let u : (ZMod N)ˣ := ZMod.unitOfCoprime a ((Nat.coprime_iff_gcd_eq_one).mpr hgcd)
  exact orderOf_injective (Units.coeHom (ZMod N)) Units.val_injective u
