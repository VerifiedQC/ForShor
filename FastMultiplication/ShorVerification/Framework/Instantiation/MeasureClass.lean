import FastMultiplication.ShorVerification.Framework.Quantum.Measurement
import FastMultiplication.ShorVerification.Framework.Instantiation.RegEncoding

import Mathlib.Data.Finsupp.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

namespace Shor

namespace ConcreteQSemantics

open scoped BigOperators

def outcomePred (r : Reg) (o : ℕ) (b : Basis) : Prop :=
  RegEncoding.toNat r b = o

instance instDecidableOutcomePred (r : Reg) (o : ℕ) :
    DecidablePred (outcomePred r o) := by
  intro b
  unfold outcomePred
  infer_instance

noncomputable def measFilter
    (r : Reg)
    (o : ℕ)
    (ψ : State) :
    State :=
  ψ.filter (outcomePred r o)

@[simp]
lemma measFilter_apply
    (r : Reg)
    (o : ℕ)
    (ψ : State)
    (b : Basis) :
    measFilter r o ψ b =
      if RegEncoding.toNat r b = o then ψ b else 0 := by
  rfl

lemma norm_sq_eq_sum_normSq
    (ψ : State) :
    ‖ψ‖ ^ 2 =
      ∑ b ∈ ψ.support, Complex.normSq (ψ b) := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  change
    (finsuppInner ψ ψ).re =
      ∑ b ∈ ψ.support, Complex.normSq (ψ b)
  unfold finsuppInner Finsupp.sum
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [← Complex.normSq_eq_conj_mul_self]
  simp

lemma norm_sq_measFilter_le
    (r : Reg)
    (o : ℕ)
    (ψ : State) :
    ‖measFilter r o ψ‖ ^ 2 ≤ ‖ψ‖ ^ 2 := by
  rw [norm_sq_eq_sum_normSq, norm_sq_eq_sum_normSq]

  have h :
      (∑ b ∈ (measFilter r o ψ).support,
          Complex.normSq (measFilter r o ψ b))
        =
      ∑ b ∈ ψ.support.filter (outcomePred r o),
          Complex.normSq (ψ b) := by
    rw [measFilter, Finsupp.support_filter]
    apply Finset.sum_congr rfl
    intro b hb
    have hp :
        outcomePred r o b :=
      (Finset.mem_filter.mp hb).2
    rw [Finsupp.filter_apply_pos _ _ hp]

  rw [h]

  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset _ _)
    (fun b hb₁ hb₂ => Complex.normSq_nonneg (ψ b))

lemma norm_measFilter_le
    (r : Reg)
    (o : ℕ)
    (ψ : State) :
    ‖measFilter r o ψ‖ ≤ ‖ψ‖ := by
  have h := norm_sq_measFilter_le r o ψ
  nlinarith [norm_nonneg (measFilter r o ψ), norm_nonneg ψ]

noncomputable def measLinearMap
    (r : Reg)
    (o : ℕ) :
    State →ₗ[ℂ] State where
  toFun := measFilter r o

  map_add' := by
    intro ψ φ
    apply Finsupp.ext
    intro b
    by_cases h : RegEncoding.toNat r b = o <;>
      simp [measFilter_apply, h]

  map_smul' := by
    intro a ψ
    apply Finsupp.ext
    intro b
    by_cases h : RegEncoding.toNat r b = o <;>
      simp [measFilter_apply, h]

noncomputable def measProjCLM
    (r : Reg)
    (o : ℕ) :
    State →L[ℂ] State :=
  (measLinearMap r o).mkContinuous 1
    (fun ψ => by
      simpa using norm_measFilter_le r o ψ)

@[simp]
lemma measProjCLM_apply
    (r : Reg)
    (o : ℕ)
    (ψ : State) :
    measProjCLM r o ψ = measFilter r o ψ := by
  rfl

lemma measProjCLM_ket
    (r : Reg)
    (o : ℕ)
    (b : Basis) :
    measProjCLM r o (ket b) =
      if RegEncoding.toNat r b = o then ket b else 0 := by
  by_cases h : RegEncoding.toNat r b = o
  · simp [measProjCLM_apply, measFilter, ket, outcomePred, h]
  · simp [measProjCLM_apply, measFilter, ket, outcomePred, h]

lemma measProjCLM_zero_outOfRange
    (r : Reg)
    (o : ℕ)
    (ψ : State)
    (ho : 2 ^ regSize r ≤ o) :
    measProjCLM r o ψ = 0 := by
  apply Finsupp.ext
  intro b

  have hb :
      RegEncoding.toNat r b < 2 ^ regSize r := by
    have h :=
      RegEncoding.toNat_lt_ASize
        (Basis := Basis) r b
    simpa [ASize] using h

  have hne :
      RegEncoding.toNat r b ≠ o := by
    omega

  simp [measProjCLM_apply, measFilter_apply, hne]

lemma inner_measFilter
    (r : Reg)
    (o : ℕ)
    (ψ φ : State) :
    inner ℂ (measFilter r o ψ) φ =
      inner ℂ ψ (measFilter r o φ) := by
  classical

  change
    finsuppInner (measFilter r o ψ) φ =
      finsuppInner ψ (measFilter r o φ)

  unfold finsuppInner Finsupp.sum measFilter

  rw [Finsupp.support_filter]
  rw [Finset.sum_filter]

  apply Finset.sum_congr rfl
  intro b hb

  by_cases h : RegEncoding.toNat r b = o
  · simp [outcomePred, h]
  · simp [outcomePred, h]

lemma measProjCLM_selfAdjoint
    (r : Reg)
    (o : ℕ)
    (ψ φ : State) :
    inner ℂ (measProjCLM r o ψ) φ =
      inner ℂ ψ (measProjCLM r o φ) := by
  simpa [measProjCLM_apply] using
    inner_measFilter r o ψ φ

lemma measFilter_orthogonal
    (r : Reg)
    (o o' : ℕ)
    (ψ : State)
    (h : o ≠ o') :
    measFilter r o (measFilter r o' ψ) = 0 := by
  apply Finsupp.ext
  intro b

  by_cases ho' : RegEncoding.toNat r b = o'
  · have ho : RegEncoding.toNat r b ≠ o := by
      intro ho
      apply h
      exact ho.symm.trans ho'

    simp [measFilter_apply, ho']
    intro ho
    subst ho
    subst ho'
    simp_all only [ne_eq, not_true_eq_false]
  · simp [measFilter_apply, ho']

lemma measProjCLM_orthogonal
    (r : Reg)
    (o o' : ℕ)
    (ψ : State)
    (h : o ≠ o') :
    measProjCLM r o (measProjCLM r o' ψ) = 0 := by
  simpa [measProjCLM_apply] using
    measFilter_orthogonal r o o' ψ h

lemma measProjCLM_complete
    (r : Reg)
    (ψ : State) :
    (∑ o : Fin (2 ^ regSize r),
        measProjCLM r o.1 ψ) = ψ := by
  classical

  apply Finsupp.ext
  intro b

  have hb :
      RegEncoding.toNat r b < 2 ^ regSize r := by
    have h :=
      RegEncoding.toNat_lt_ASize
        (Basis := Basis) r b
    simpa [ASize] using h

  let i : Fin (2 ^ regSize r) :=
    ⟨RegEncoding.toNat r b, hb⟩

  simp only [measProjCLM_apply]
  change
    (Finsupp.applyAddHom b)
      (∑ o : Fin (2 ^ regSize r), measFilter r o.1 ψ) = ψ b
  rw [map_sum]
  change
    (∑ o : Fin (2 ^ regSize r), measFilter r o.1 ψ b) = ψ b

  calc
    (∑ o : Fin (2 ^ regSize r), measFilter r o.1 ψ b)
        = measFilter r i.1 ψ b := by
            apply Fintype.sum_eq_single i
            · intro j hji
              have hne :
                  RegEncoding.toNat r b ≠ j.1 := by
                intro h
                apply hji
                apply Fin.ext
                simpa [i] using h.symm
              simp [measFilter_apply, hne]
    _ = ψ b := by
            simp [measFilter_apply, i]

noncomputable instance instMeasureClass :
    MeasureClass concreteQSemantics where

  measProj := fun r o =>
    measProjCLM r o

  measProj_ket := by
    intro r o b
    exact measProjCLM_ket r o b

  measProj_zero_outOfRange := by
    intro r o ψ ho
    exact measProjCLM_zero_outOfRange r o ψ ho

  measProj_selfAdjoint := by
    intro r o ψ φ
    exact measProjCLM_selfAdjoint r o ψ φ

  measProj_orthogonal := by
    intro r o o' ψ h
    exact measProjCLM_orthogonal r o o' ψ h

  measProj_complete := by
    intro r ψ
    exact measProjCLM_complete r ψ

end ConcreteQSemantics

end Shor
