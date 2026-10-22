import FastMultiplication.ShorVerification.Model.Standard.Basis
import FastMultiplication.ShorVerification.Framework.Quantum.QSemantics
import FastMultiplication.ShorVerification.Framework.Quantum.Measurement
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The state space, `QSemantics` and `MeasureClass`

Items 2 and 3 of the original construction plan.

`QSemantics.state_induction` says every state is a *finite* linear combination
of kets, so the state space is the algebraic span of the basis, not its
completion: `State := ModelBasis →₀ ℂ` with the ℓ² inner product. Kets are then
literally `Finsupp.single`, orthonormality is `Finsupp.single_apply`, and
`state_induction` is `Finsupp.induction`.

Measurement of a register is `Finsupp.filter`: keep the kets whose register
value is the observed outcome.
-/

namespace Shor
namespace Model

open scoped ComplexConjugate

/-- States: finite complex combinations of computational basis kets. -/
abbrev State : Type := ModelBasis →₀ ℂ

/-! ## The ℓ² inner product -/

/-- The ℓ² inner product, conjugate-linear in the first argument (Mathlib's
convention). -/
noncomputable def innerS (f g : State) : ℂ := f.sum fun b a => conj a * g b

noncomputable instance instInnerState : Inner ℂ State := ⟨innerS⟩

theorem inner_eq_innerS (f g : State) : inner ℂ f g = innerS f g := rfl

/-- Any finite set containing the support of the *first* argument computes the
inner product. This single lemma is what makes all five `Core` fields routine. -/
theorem innerS_eq_sum (f g : State) {s : Finset ModelBasis} (hs : f.support ⊆ s) :
    innerS f g = ∑ b ∈ s, conj (f b) * g b :=
  Finsupp.sum_of_support_subset f hs _ (by intro i _; simp)

theorem innerS_self (f : State) :
    innerS f f = ((∑ b ∈ f.support, Complex.normSq (f b) : ℝ) : ℂ) := by
  rw [innerS_eq_sum f f (subset_refl _)]
  push_cast
  exact Finset.sum_congr rfl fun b _ => Complex.normSq_eq_conj_mul_self.symm

theorem re_innerS_self (f : State) :
    RCLike.re (K := ℂ) (innerS f f) = ∑ b ∈ f.support, Complex.normSq (f b) := by
  rw [innerS_self]; simp

/-! ### The five `InnerProductSpace.Core` laws -/

theorem innerS_conj_symm (x y : State) : conj (innerS y x) = innerS x y := by
  classical
  rw [innerS_eq_sum y x Finset.subset_union_right,
      innerS_eq_sum x y (Finset.subset_union_left (s₂ := y.support)), map_sum]
  exact Finset.sum_congr rfl fun b _ => by simp [mul_comm]

theorem re_innerS_self_nonneg (x : State) : 0 ≤ RCLike.re (K := ℂ) (innerS x x) := by
  rw [re_innerS_self]
  exact Finset.sum_nonneg fun b _ => Complex.normSq_nonneg _

theorem innerS_add_left (x y z : State) : innerS (x + y) z = innerS x z + innerS y z := by
  classical
  rw [innerS_eq_sum (x + y) z Finsupp.support_add,
      innerS_eq_sum x z Finset.subset_union_left,
      innerS_eq_sum y z Finset.subset_union_right, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun b _ => by simp [add_mul]

theorem innerS_smul_left (x y : State) (r : ℂ) : innerS (r • x) y = conj r * innerS x y := by
  rw [innerS_eq_sum (r • x) y Finsupp.support_smul,
      innerS_eq_sum x y (subset_refl _), Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by simp [mul_assoc]

theorem innerS_definite (x : State) (hx : innerS x x = 0) : x = 0 := by
  have hx' : ∑ b ∈ x.support, Complex.normSq (x b) = 0 := by
    have h : RCLike.re (K := ℂ) (innerS x x) = 0 := by rw [hx]; simp
    rwa [re_innerS_self] at h
  have hzero : ∀ b ∈ x.support, Complex.normSq (x b) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun b _ => Complex.normSq_nonneg _).mp hx'
  have hsupp : x.support = ∅ := by
    by_contra h
    obtain ⟨b, hb⟩ := Finset.nonempty_of_ne_empty h
    exact (Finsupp.mem_support_iff.mp hb) (Complex.normSq_eq_zero.mp (hzero b hb))
  exact Finsupp.support_eq_empty.mp hsupp

/-! ### The normed and inner-product structures -/

noncomputable instance instNormedState : NormedAddCommGroup State :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ State _ _ _
    { toInner := instInnerState
      conj_inner_symm := innerS_conj_symm
      re_inner_nonneg := re_innerS_self_nonneg
      definite := innerS_definite
      add_left := innerS_add_left
      smul_left := innerS_smul_left }

noncomputable instance instIPState : InnerProductSpace ℂ State :=
  InnerProductSpace.ofCore _

theorem norm_sq_eq_sum (f : State) :
    ‖f‖ ^ 2 = ∑ b ∈ f.support, Complex.normSq (f b) := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ) f, inner_eq_innerS, re_innerS_self]

/-! ## Kets -/

/-- The computational basis ket: literally a standard basis vector. -/
noncomputable def ket (b : ModelBasis) : State := Finsupp.single b 1

theorem innerS_ket_self (b : ModelBasis) : innerS (ket b) (ket b) = 1 := by
  rw [ket, innerS, Finsupp.sum_single_index (by simp)]
  simp

theorem innerS_ket_of_ne {b₁ b₂ : ModelBasis} (h : b₁ ≠ b₂) :
    innerS (ket b₁) (ket b₂) = 0 := by
  classical
  rw [ket, ket, innerS, Finsupp.sum_single_index (by simp)]
  simp [h]

/-! ## `QSemantics` -/

/-- **The model.** A concrete `QSemantics` over `ModelBasis`. -/
noncomputable def qs : QSemantics where
  Basis := ModelBasis
  State := State
  instNormed := instNormedState
  instIP := instIPState
  ket := ket
  state_induction := by
    intro P h0 hadd hsmul hket ψ
    refine Finsupp.induction ψ h0 ?_
    intro a c f _ _ ih
    refine hadd _ _ ?_ ih
    have hc : Finsupp.single a c = c • ket a := by rw [ket, Finsupp.smul_single]; simp
    rw [hc]
    exact hsmul c _ (hket a)
  ket_inner_eq_of_eq := by
    intro b₁ b₂ h; subst h; exact innerS_ket_self b₁
  ket_inner_eq_zero_of_ne := by
    intro b₁ b₂ h; exact innerS_ket_of_ne h

@[simp] theorem qs_Basis : qs.Basis = ModelBasis := rfl
@[simp] theorem qs_State : qs.State = State := rfl
@[simp] theorem qs_ket (b : ModelBasis) : qs.ket b = ket b := rfl

/-- The register encoding, at the type the rest of the development names it. -/
instance instRegEncodingQs : RegEncoding qs.Basis := instRegEncoding

/-! ## Measurement -/

/-- Measuring register `r` and seeing `o` keeps exactly the kets on which `r`
reads as `o`. -/
noncomputable def measFilter (r : Reg) (o : ℕ) : State →ₗ[ℂ] State where
  toFun f := Finsupp.filter (fun b => mToNat r b = o) f
  map_add' _ _ := Finsupp.filter_add
  map_smul' _ _ := Finsupp.filter_smul

@[simp] theorem measFilter_apply (r : Reg) (o : ℕ) (f : State) (b : ModelBasis) :
    measFilter r o f b = if mToNat r b = o then f b else 0 :=
  Finsupp.filter_apply _ _ _

theorem measFilter_support (r : Reg) (o : ℕ) (f : State) :
    (measFilter r o f).support ⊆ f.support := by
  intro b hb
  rw [Finsupp.mem_support_iff] at hb ⊢
  rw [measFilter_apply] at hb
  by_contra hc
  exact hb (by simp [hc])

theorem measFilter_norm_le (r : Reg) (o : ℕ) (f : State) :
    ‖measFilter r o f‖ ≤ 1 * ‖f‖ := by
  have hsq : ‖measFilter r o f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [norm_sq_eq_sum, norm_sq_eq_sum]
    refine le_trans (le_of_eq (Finset.sum_congr rfl ?_))
      (Finset.sum_le_sum_of_subset_of_nonneg (measFilter_support r o f)
        fun b _ _ => Complex.normSq_nonneg _)
    intro b hb
    have hb' : mToNat r b = o := by
      by_contra hc
      exact (Finsupp.mem_support_iff.mp hb) (by simp [hc])
    simp [hb']
  nlinarith [norm_nonneg (measFilter r o f), norm_nonneg f]

theorem measFilter_ket (r : Reg) (o : ℕ) (b : ModelBasis) :
    measFilter r o (ket b) = if mToNat r b = o then ket b else 0 := by
  classical
  refine Finsupp.ext fun b' => ?_
  by_cases h : mToNat r b = o
  · rw [if_pos h, measFilter_apply]
    by_cases hb : b' = b
    · subst hb; simp [h]
    · simp [ket, hb]
  · rw [if_neg h, measFilter_apply]
    by_cases hb : b' = b
    · subst hb; simp [h]
    · simp [ket, hb]

/-- The Born-rule projectors. -/
noncomputable instance instMeasureClass : MeasureClass qs where
  measProj r o := LinearMap.mkContinuous (measFilter r o) 1 (measFilter_norm_le r o)
  measProj_ket := by
    intro r o b
    exact measFilter_ket r o b
  measProj_zero_outOfRange := by
    intro r o ψ ho
    show measFilter r o ψ = 0
    refine Finsupp.ext fun b => ?_
    have hlt : mToNat r b < 2 ^ regSize r := by
      simpa [ASize] using RegEncoding.toNat_lt_ASize (Basis := ModelBasis) r b
    have : mToNat r b ≠ o := by omega
    simp [this]
  measProj_selfAdjoint := by
    classical
    intro r o ψ φ
    show innerS (measFilter r o ψ) φ = innerS ψ (measFilter r o φ)
    have h1 : (measFilter r o ψ).support ⊆ ψ.support ∪ φ.support :=
      subset_trans (measFilter_support r o ψ) Finset.subset_union_left
    rw [innerS_eq_sum _ _ h1,
        innerS_eq_sum ψ _ (Finset.subset_union_left (s₂ := φ.support))]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases h : mToNat r b = o <;> simp [h]
  measProj_orthogonal := by
    intro r o o' ψ hne
    show measFilter r o (measFilter r o' ψ) = 0
    refine Finsupp.ext fun b => ?_
    by_cases h : mToNat r b = o <;> by_cases h' : mToNat r b = o' <;> simp_all
  measProj_complete := by
    classical
    intro r ψ
    show (∑ o : Fin (2 ^ regSize r), measFilter r o.1 ψ) = ψ
    refine Finsupp.ext fun b => ?_
    rw [Finsupp.finset_sum_apply]
    have hlt : mToNat r b < 2 ^ regSize r := by
      simpa [ASize] using RegEncoding.toNat_lt_ASize (Basis := ModelBasis) r b
    rw [Finset.sum_eq_single (⟨mToNat r b, hlt⟩ : Fin (2 ^ regSize r))]
    · simp
    · intro o _ hne
      have h : mToNat r b ≠ o.1 := fun h => hne (Fin.ext h.symm)
      simp [h]
    · intro h; exact absurd (Finset.mem_univ _) h

/-! ## Sanity checks -/

section Sanity

example : qs.Basis = ModelBasis := rfl
example : qs.State = State := rfl
example (b : ModelBasis) : qs.ket b = Finsupp.single b 1 := rfl
example (b : ModelBasis) : ‖qs.ket b‖ = 1 := ket_norm_one qs b

end Sanity

end Model
end Shor
