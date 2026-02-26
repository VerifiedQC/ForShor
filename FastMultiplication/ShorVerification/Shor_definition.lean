import FastMultiplication.ShorVerification.LowGate_compilation
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Shor
open Gate


def initY1 (y : Reg) : Gate :=
  Gate.X y.lo

/-- Approximate (in-place) quantum order-finding circuit. -/
noncomputable def orderFindingApprox
  (qs : QSemantics) [RegEncoding qs.Basis] [Spec qs] [ModMul qs]
  (a N : ℕ) (x y w_reg : Reg) (flag : ℕ) : Gate :=
  (H_reg x) ;;
  (initY1 y) ;;
  (modExpApprox' (qs := qs) a N x y w_reg flag) ;;
  (Gate.QFT x)













open scoped BigOperators


def Order (a r N : ℕ) : Prop :=
  ∃ h : Nat.Coprime a N, orderOf (ZMod.unitOfCoprime a h) = r
def BasicSetting (a r N m n : ℕ) : Prop :=
  0 < a ∧ a < N ∧
  Order a r N ∧
  N^2 < 2^m ∧ 2^m ≤ 2 * N^2 ∧
  N < 2^n ∧ 2^n ≤ 2 * N

class MeasureClass (qs : QSemantics) where
  prob : Reg → qs.State → ℕ → ℝ
  prob_nonneg : ∀ (r : Reg) (ψ : qs.State) (k : ℕ), 0 ≤ prob r ψ k

def PrEvent {qs : QSemantics} [MeasureClass qs]
    (r : Reg) (S : Finset ℕ) (ψ : qs.State) : ℝ :=
  ∑ k ∈ S, MeasureClass.prob (qs := qs) r ψ k

class OFPost where
  OF_post : (a N o m : ℕ) → ℕ

def r_found [OFPost] (o m r a N : ℕ) : ℝ :=
  if OFPost.OF_post a N o m = r then 1 else 0

noncomputable def probability_of_success
  (qs : QSemantics)
  [RegEncoding qs.Basis] [Spec qs] [ModMul qs]
  [MeasureClass qs] [OFPost]
  (a r N : ℕ) (x y w_reg : Reg) (flag : ℕ) (ψ : qs.State) : ℝ :=
  Finset.sum (Finset.range (2 ^ (tbits x))) (fun o =>
    (r_found (o := o) (m := tbits x) (r := r) (a := a) (N := N))
      * MeasureClass.prob (qs := qs) x
          (qs.eval (orderFindingApprox (qs := qs) a N x y w_reg flag) ψ) o)

lemma r_found_nonneg [OFPost] (o m r a N : ℕ) : 0 ≤ r_found (o:=o) (m:=m) (r:=r) (a:=a) (N:=N) := by
  unfold r_found
  by_cases h : OFPost.OF_post a N o m = r <;> simp [h]

lemma probability_of_success_nonneg
  (qs : QSemantics)
  [RegEncoding qs.Basis] [Spec qs] [ModMul qs]
  [MeasureClass qs] [OFPost] :
  ∀ (a r N : ℕ) (x y w_reg : Reg) (flag : ℕ) (ψ : qs.State),
    0 ≤ probability_of_success (qs := qs) a r N x y w_reg flag ψ := by
  intro a r N x y w_reg flag ψ
  unfold probability_of_success
  refine Finset.sum_nonneg ?_
  intro o ho
  have h1 : 0 ≤ r_found (o:=o) (m:=tbits x) (r:=r) (a:=a) (N:=N) := r_found_nonneg (o:=o) (m:=tbits x) (r:=r) (a:=a) (N:=N)
  have h2 : 0 ≤ MeasureClass.prob (qs := qs) x
      (qs.eval (orderFindingApprox (qs := qs) a N x y w_reg flag) ψ) o :=
    MeasureClass.prob_nonneg (qs := qs) x _ o
  nlinarith

lemma sum_image_le_sum_univ
  {α : Type} [DecidableEq α]
  (S : Finset α) (T : Finset α) (f : α → ℝ)
  (hf : ∀ a, 0 ≤ f a)
  (hST : S ⊆ T) :
  (∑ a∈S, f a) ≤ (∑ a ∈ T, f a) := by
  refine Finset.sum_le_sum_of_subset_of_nonneg hST ?_
  intro a haT haS
  exact hf a

class OrderTheory where
  ord : ℕ → ℕ → ℕ
  ord_Order : ∀ {a N : ℕ}, 0 < a → a < N → Nat.gcd a N = 1 → Order a (ord a N) N
