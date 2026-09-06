import FastMultiplication.ShorVerification.Framework.Quantum.QSemantics
import Mathlib.Algebra.BigOperators.Finsupp.Basic

namespace Shor

namespace ConcreteQSemantics

open ComplexConjugate

abbrev Basis := ℕ

abbrev State := Basis →₀ ℂ

noncomputable def ket (b : Basis) : State :=
  Finsupp.single b 1

noncomputable def finsuppInner (ψ φ : State) : ℂ :=
  ψ.sum fun b a => (starRingEnd ℂ) a * φ b

private lemma finsuppInner_eq_sum_union (ψ φ : State) :
    finsuppInner ψ φ =
      ∑ b ∈ ψ.support ∪ φ.support,
        (starRingEnd ℂ) (ψ b) * φ b := by
  classical
  unfold finsuppInner Finsupp.sum
  apply Finset.sum_subset Finset.subset_union_left
  intro b hb hψ
  rw [Finsupp.notMem_support_iff.mp hψ]
  simp

private lemma finsuppInner_conj_symm (ψ φ : State) :
    (starRingEnd ℂ) (finsuppInner φ ψ) =
      finsuppInner ψ φ := by
  classical
  rw [finsuppInner_eq_sum_union, finsuppInner_eq_sum_union]
  rw [Finset.union_comm φ.support ψ.support]
  simp only [map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro b hb
  simp [mul_comm]

private lemma finsuppInner_add_left (ψ φ χ : State) :
    finsuppInner (ψ + φ) χ =
      finsuppInner ψ χ + finsuppInner φ χ := by
  classical
  unfold finsuppInner
  apply Finsupp.sum_add_index
  · intro b
    simp
  · intro b a₁ a₂
    simp [add_mul]

private lemma support_smul_eq
    (r : ℂ) (ψ : State) (hr : r ≠ 0) :
    (r • ψ).support = ψ.support := by
  classical
  ext b
  simp [Finsupp.mem_support_iff, hr]

private lemma finsuppInner_smul_left (ψ φ : State) (r : ℂ) :
    finsuppInner (r • ψ) φ =
      (starRingEnd ℂ) r * finsuppInner ψ φ := by
  classical
  by_cases hr : r = 0
  · subst r
    simp [finsuppInner]
  · unfold finsuppInner Finsupp.sum
    rw [support_smul_eq r ψ hr]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    simp [mul_assoc]

private lemma finsuppInner_self_eq_sum_normSq (ψ : State) :
    finsuppInner ψ ψ =
      ((∑ b ∈ ψ.support, Complex.normSq (ψ b) : ℝ) : ℂ) := by
  classical
  unfold finsuppInner Finsupp.sum
  push_cast
  apply Finset.sum_congr rfl
  intro b hb
  simpa using
    (Complex.normSq_eq_conj_mul_self (z := ψ b)).symm

private lemma finsuppInner_re_nonneg (ψ : State) :
    0 ≤ (finsuppInner ψ ψ).re := by
  rw [finsuppInner_self_eq_sum_normSq]
  simp only [Complex.ofReal_re]
  exact Finset.sum_nonneg fun b hb =>
    Complex.normSq_nonneg (ψ b)

private lemma finsuppInner_definite
    (ψ : State)
    (h : finsuppInner ψ ψ = 0) :
    ψ = 0 := by
  classical
  have hsum :
      ∑ b ∈ ψ.support, Complex.normSq (ψ b) = 0 := by
    have hre := congrArg Complex.re h
    rw [finsuppInner_self_eq_sum_normSq] at hre
    simpa using hre

  apply Finsupp.ext
  intro b
  by_cases hb : b ∈ ψ.support
  · have hz : Complex.normSq (ψ b) = 0 := by
      have hall :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun b hb => Complex.normSq_nonneg (ψ b))).mp hsum
      exact hall b hb
    simpa using Complex.normSq_eq_zero.mp hz
  · simpa using Finsupp.notMem_support_iff.mp hb

noncomputable def stateCore :
    InnerProductSpace.Core ℂ State where
  inner := finsuppInner
  conj_inner_symm := by
    intro ψ φ
    exact finsuppInner_conj_symm ψ φ
  re_inner_nonneg := by
    intro ψ
    exact finsuppInner_re_nonneg ψ
  add_left := by
    intro ψ φ χ
    exact finsuppInner_add_left ψ φ χ
  smul_left := by
    intro ψ φ r
    exact finsuppInner_smul_left ψ φ r
  definite := by
    intro ψ h
    exact finsuppInner_definite ψ h

noncomputable local instance stateCoreInst :
    InnerProductSpace.Core ℂ State :=
  stateCore

noncomputable instance stateNormedAddCommGroup :
    NormedAddCommGroup State :=
  InnerProductSpace.Core.toNormedAddCommGroup
    (𝕜 := ℂ) (F := State)

noncomputable instance stateInnerProductSpace :
    InnerProductSpace ℂ State :=
  InnerProductSpace.ofCore
    (𝕜 := ℂ) (F := State)
    (show PreInnerProductSpace.Core ℂ State from inferInstance)

noncomputable def concreteQSemantics : QSemantics where
  Basis := Basis
  State := State
  instNormed := stateNormedAddCommGroup
  instIP := stateInnerProductSpace

  ket := ket

  state_induction := by
    intro P hzero hadd hsmul hket ψ
    classical

    have hsum :
        P (∑ b ∈ ψ.support, ψ b • ket b) := by
      induction ψ.support using Finset.induction with
      | empty =>
          simpa using hzero
      | @insert b s hb ih =>
          rw [Finset.sum_insert hb]
          exact hadd _ _
            (hsmul (ψ b) (ket b) (hket b))
            ih

    have hrepr :
        (∑ b ∈ ψ.support, ψ b • ket b) = ψ := by
      calc
        (∑ b ∈ ψ.support, ψ b • ket b)
            = ∑ b ∈ ψ.support, Finsupp.single b (ψ b) := by
                apply Finset.sum_congr rfl
                intro b hb
                simp [ket]
        _ = ψ := by
                simpa [Finsupp.sum] using Finsupp.sum_single ψ

    rw [← hrepr]
    exact hsum

  ket_inner_eq_of_eq := by
    intro b₁ b₂ h
    subst b₂
    change finsuppInner (ket b₁) (ket b₁) = 1
    simp [finsuppInner, ket]

  ket_inner_eq_zero_of_ne := by
    intro b₁ b₂ h
    change finsuppInner (ket b₁) (ket b₂) = 0
    simp [finsuppInner, ket, h]

end ConcreteQSemantics

end Shor
