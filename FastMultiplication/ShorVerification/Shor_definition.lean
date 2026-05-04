import FastMultiplication.ShorVerification.QFT_decomposition
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Shor
open Gate


def initY1 (y : Reg) : Gate :=
  Gate.X y.lo

/-- Approximate (in-place) quantum order-finding circuit. -/
noncomputable def orderFindingApprox
  (qs : QSemantics) [RegEncoding qs.Basis] [Spec] [ExtRegEncoding QSemantics.Basis] [ModMul qs]
  (a N : ℕ) (x y w_reg : Reg) (flag : ℕ) : Gate :=
  (H_reg x) ;;
  (initY1 y) ;;
  (modExpApprox' (qs := qs) a N x y w_reg flag) ;;
  (Gate.QFT x)

/-- Approximate (in-place) quantum order-finding circuit. -/
noncomputable def orderFindingIdeal
  (qs : QSemantics) [RegEncoding qs.Basis] [Spec]
  (a N : ℕ) (x y : Reg) : Gate :=
  (H_reg x) ;;
  (initY1 y) ;;
  (modExpIdeal' (qs := qs) a N x y) ;;
  (Gate.QFT x)


variable {qs : QSemantics}
variable [RegEncoding qs.Basis]


/--r is the multiplicative order of a mod N-/
def Order (a N r : ℕ) : Prop :=
  ∃ h : Nat.Coprime a N, r = orderOf (ZMod.unitOfCoprime a h)

noncomputable def ord (a N : ℕ) (hgcd : Nat.gcd a N = 1) : ℕ :=
  orderOf (ZMod.unitOfCoprime a ((Nat.coprime_iff_gcd_eq_one).2 hgcd))

/--These are the classical conditions that will be used in the correctness proof-/
def BasicSetting (a r N m n : ℕ) : Prop :=
  0 < a ∧ a < N ∧
  Order a r N ∧
  N^2 < 2^m ∧ 2^m ≤ 2 * N^2 ∧
  N < 2^n ∧ 2^n ≤ 2 * N

/--Modelling “measurement”-/
class MeasureClass (qs : QSemantics) [RegEncoding qs.Basis] where
  probMeas : (r : Reg) → (o : ℕ) → qs.State → ℝ

  probMeas_nonneg : ∀ r o ψ, 0 ≤ probMeas r o ψ

  probMeas_outOfRange : ∀ r o ψ, (2^(regSize r) ≤ o) → probMeas r o ψ = 0

  probMeas_total :
    ∀ r (ψ : qs.State),
      ‖ψ‖ = 1 →
      (∑ o : Fin (2^(regSize r)), probMeas r o.1 ψ) = 1



variable [MeasureClass qs]

/-- Run the circuit G on input state ψ, then measure register r, and ask for probability of outcome o -/
noncomputable def measProbAfter (r : Reg) (o : ℕ) (G : Gate) (ψ : qs.State) : ℝ :=
  MeasureClass.probMeas (qs := qs) r o (qs.eval G ψ)

/-- Given a finite set Good of outcomes that are “successful,” sum the measurement probability over those outcomes. -/
noncomputable def successProbAfterFinset
  (r : Reg) (Good : Finset ℕ) (G : Gate) (ψ : qs.State) : ℝ :=
  ∑ o ∈ Good, measProbAfter (qs := qs) r o G ψ

/--Success probability is nonnegative.-/
lemma successProbAfterFinset_nonneg
  (r : Reg) (Good : Finset ℕ) (G : Gate) (ψ : qs.State) :
  0 ≤ successProbAfterFinset (qs := qs) r Good G ψ := by
  unfold successProbAfterFinset measProbAfter
  refine Finset.sum_nonneg ?_
  intro o ho
  have : 0 ≤ MeasureClass.probMeas (qs := qs) r o (qs.eval G ψ) := by
    simpa using (MeasureClass.probMeas_nonneg (qs := qs) r o (qs.eval G ψ))
  simpa using this

/-- If the “good outcomes” set is enlargened, success probability can only go up -/
lemma successProbAfterFinset_mono
  (r : Reg) {Good Good' : Finset ℕ} (hsub : Good ⊆ Good')
  (G : Gate) (ψ : qs.State) :
  successProbAfterFinset (qs := qs) r Good G ψ
    ≤
  successProbAfterFinset (qs := qs) r Good' G ψ := by
  unfold successProbAfterFinset
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
  intro o ho hnot
  unfold measProbAfter
  simpa using (MeasureClass.probMeas_nonneg (qs := qs) r o (qs.eval G ψ))

lemma successProbAfterFinset_inter_range_eq
  (r : Reg) (Good : Finset ℕ) (G : Gate) (ψ : qs.State) :
  successProbAfterFinset (qs := qs) r (Good ∩ Finset.range (2^(regSize r))) G ψ
    =
  successProbAfterFinset (qs := qs) r Good G ψ := by
  classical
  unfold successProbAfterFinset measProbAfter
  have :
      (∑ o ∈ Good ∩ Finset.range (2^(regSize r)),
          MeasureClass.probMeas (qs := qs) r o (qs.eval G ψ))
      =
      ∑ o ∈ Good,
        MeasureClass.probMeas (qs := qs) r o (qs.eval G ψ) := by
    have hdecomp :
        (∑ o ∈ Good,
            MeasureClass.probMeas (qs := qs) r o (qs.eval G ψ))
        =
        (∑ o ∈ (Good ∩ Finset.range (2^(regSize r))),
            MeasureClass.probMeas (qs := qs) r o (qs.eval G ψ))
        +
        (∑ o ∈ (Good \ Finset.range (2^(regSize r))),
            MeasureClass.probMeas (qs := qs) r o (qs.eval G ψ)) := by

      have:=(Finset.sum_inter_add_sum_diff (s := Good) (t := Finset.range (2^(regSize r)))
              (f := fun o => MeasureClass.probMeas (qs := qs) r o (qs.eval G ψ)))
      simp at *
      rw[← this]

    have hdiff0 :
        (∑ o ∈ (Good \ Finset.range (2^(regSize r))),
            MeasureClass.probMeas (qs := qs) r o (qs.eval G ψ)) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro o ho
      have ho_not_range : o ∉ Finset.range (2^(regSize r)) := by
        exact (Finset.mem_sdiff.mp ho).2
      have ho_ge : 2^(regSize r) ≤ o := by
        exact Nat.le_of_not_gt (by
          intro ho_lt
          exact ho_not_range (Finset.mem_range.mpr ho_lt))
      simpa using (MeasureClass.probMeas_outOfRange (qs := qs) r o (qs.eval G ψ) ho_ge)


    have := congrArg (fun t => t - (∑ o ∈ (Good \ Finset.range (2^(regSize r))),
        MeasureClass.probMeas (qs := qs) r o (qs.eval G ψ))) hdecomp
    calc
      (∑ o ∈ Good ∩ Finset.range (2^(regSize r)),
          MeasureClass.probMeas (qs := qs) r o (qs.eval G ψ))
          =
      (∑ o ∈ Good ∩ Finset.range (2^(regSize r)),
          MeasureClass.probMeas (qs := qs) r o (qs.eval G ψ)) + 0 := by simp
      _ =
      (∑ o ∈ Good ∩ Finset.range (2^(regSize r)),
          MeasureClass.probMeas (qs := qs) r o (qs.eval G ψ))
        +
      (∑ o ∈ (Good \ Finset.range (2^(regSize r))),
          MeasureClass.probMeas (qs := qs) r o (qs.eval G ψ)) := by simp [hdiff0]
      _ =
      (∑ o ∈ Good,
          MeasureClass.probMeas (qs := qs) r o (qs.eval G ψ)) := by
          symm
          exact hdecomp
  simp[this]

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



variable [ContinuedFractionPost] [Spec]


abbrev OrderVerifier := ℕ → Bool

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

noncomputable def probability_of_success
  (T : ℕ → ℕ) (verify : OrderVerifier)
  (x : Reg) (r Q : ℕ) (G : Gate) (ψ : qs.State) : ℝ :=
  ∑ o : Fin Q,
    (r_found (T := T) verify o.1 Q r) *
      (measProbAfter (qs := qs) x o.1 G ψ)

noncomputable def κ : ℝ := (4 * Real.exp (-2)) / (Real.pi ^ 2)

/-- Shor/order-finding correctness statement -/
theorem Shor_correct
  (T : ℕ → ℕ)
  (a N : ℕ)
  (ha : 0 < a ∧ a < N)
  (hgcd : Nat.gcd a N = 1)
  (x y w : Reg) (flag : ℕ)
  (ψ0 : qs.State)
  (hm : regSize x = Nat.log2 (2 * N^2))
  (hn : regSize y = Nat.log2 (2 * N))
  (hset : BasicSetting a (ord a N hgcd) N (regSize x) (regSize y)) :
  probability_of_success (qs := qs) (T := T)
    (verify := fun d => decide ((a ^ d) % N = 1))
    (x := x) (r := ord a N hgcd) (Q := 2^(regSize x))
    (G := orderFindingIdeal (qs := qs) a N x y)
    (ψ := ψ0)
  ≥ κ / (Nat.log2 N : ℝ)^4 := by

  sorry
