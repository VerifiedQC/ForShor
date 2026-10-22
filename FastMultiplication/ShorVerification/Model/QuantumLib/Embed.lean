import FastMultiplication.ShorVerification.Model.Standard.State
import FastMultiplication.ShorVerification.Model.QuantumLib.Vendored

/-!
# Embedding `dim`-qubit vectors into the standard model

`Model/`'s state space is `ModelBasis →₀ ℂ` over the *infinite* basis
`ModelBasis = ℕ → Bool`, because `RegEncoding` admits registers on arbitrarily
large qubit names. A `dim`-qubit `CVector (2 ^ dim)` sits inside it as the span
of the basis states supported on qubits `0, …, dim-1`.

**Bit order**: index `k : Fin (2 ^ dim)` is the basis state
whose qubit `i` is `Nat.testBit k i`. Qubit `0` is the *least* significant bit
of the index, so in a `kron` chain the high qubits are on the left.
-/

namespace Shor
namespace Model
namespace QuantumLib

open scoped ComplexConjugate

/-! ## The register of the `dim` lowest qubits -/

/-- Qubits `0, …, dim-1`, in order. -/
def fullReg (dim : ℕ) : Reg := Reg.interval 0 dim

@[simp] theorem fullReg_qubits (dim : ℕ) : (fullReg dim).qubits = List.range dim := by
  simp [fullReg, Reg.interval]

@[simp] theorem mem_fullReg (dim q : ℕ) : q ∈ (fullReg dim).qubits ↔ q < dim := by simp

@[simp] theorem regSize_fullReg (dim : ℕ) : regSize (fullReg dim) = dim := by
  simp [regSize, Reg.width]

@[simp] theorem ASize_fullReg (dim : ℕ) : ASize (fullReg dim) = 2 ^ dim := by
  simp [ASize]

theorem fullReg_get (dim : ℕ) (i : Fin (regSize (fullReg dim))) : (fullReg dim).get i = i.1 := by
  simp [Reg.get]

/-! ## Supported below `dim` -/

/-- A basis state uses only qubits `< dim`. -/
def Below (dim : ℕ) (b : ModelBasis) : Prop := ∀ i, dim ≤ i → b i = false

theorem Below.eq_false {dim : ℕ} {b : ModelBasis} (h : Below dim b) {i : ℕ} (hi : dim ≤ i) :
    b i = false := h i hi

/-! ## Index ↔ basis state -/

/-- The basis state named by an index: qubit `i` is bit `i` of `k`. -/
def idxBasis (dim : ℕ) (k : Fin (2 ^ dim)) : ModelBasis := fun i => Nat.testBit k.1 i

theorem idxBasis_apply (dim : ℕ) (k : Fin (2 ^ dim)) (i : ℕ) :
    idxBasis dim k i = Nat.testBit k.1 i := rfl

theorem idxBasis_below (dim : ℕ) (k : Fin (2 ^ dim)) : Below dim (idxBasis dim k) := by
  intro i hi
  exact Nat.testBit_eq_false_of_lt
    (lt_of_lt_of_le k.2 (Nat.pow_le_pow_right (by norm_num) hi))

/-- The index named by a basis state: read qubits `0, …, dim-1`. -/
def basisIdx (dim : ℕ) (b : ModelBasis) : Fin (2 ^ dim) :=
  ⟨mToNat (fullReg dim) b, by simpa using mToNat_lt (fullReg dim) b⟩

@[simp] theorem basisIdx_val (dim : ℕ) (b : ModelBasis) :
    (basisIdx dim b).1 = mToNat (fullReg dim) b := rfl

@[simp] theorem basisIdx_idxBasis (dim : ℕ) (k : Fin (2 ^ dim)) :
    basisIdx dim (idxBasis dim k) = k := by
  refine Fin.ext (Nat.eq_of_testBit_eq fun i => ?_)
  by_cases hi : i < dim
  · have h := testBit_mToNat (fullReg dim) (idxBasis dim k) ⟨i, by simpa using hi⟩
    rw [fullReg_get] at h
    simpa [idxBasis_apply] using h
  · push_neg at hi
    have h1 : Nat.testBit (mToNat (fullReg dim) (idxBasis dim k)) i = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by simpa using mToNat_lt (fullReg dim) _)
        (Nat.pow_le_pow_right (by norm_num) hi))
    have h2 : Nat.testBit k.1 i = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le k.2 (Nat.pow_le_pow_right (by norm_num) hi))
    simpa [h2] using h1

theorem idxBasis_basisIdx {dim : ℕ} {b : ModelBasis} (hb : Below dim b) :
    idxBasis dim (basisIdx dim b) = b := by
  refine eq_of_agree_off (r := fullReg dim) (fun q hq => ?_) ?_
  · have hq' : dim ≤ q := by simpa using hq
    rw [hb.eq_false hq']
    exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by simpa using mToNat_lt (fullReg dim) b)
      (Nat.pow_le_pow_right (by norm_num) hq'))
  · exact congrArg Fin.val (basisIdx_idxBasis dim (basisIdx dim b))

theorem idxBasis_injective (dim : ℕ) : Function.Injective (idxBasis dim) := by
  intro k k' h
  rw [← basisIdx_idxBasis dim k, ← basisIdx_idxBasis dim k', h]

/-! ## The embedding -/

/-- A `dim`-qubit column vector, read as a state of the standard model. -/
noncomputable def ι (dim : ℕ) : CVector (2 ^ dim) →ₗ[ℂ] State where
  toFun v := ∑ k : Fin (2 ^ dim), v k 0 • ket (idxBasis dim k)
  map_add' u v := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.smul_sum, smul_smul]

theorem ι_apply (dim : ℕ) (v : CVector (2 ^ dim)) :
    ι dim v = ∑ k : Fin (2 ^ dim), v k 0 • ket (idxBasis dim k) := rfl

/-- The standard basis vector of `CVector (2 ^ dim)`. -/
def e (dim : ℕ) (k : Fin (2 ^ dim)) : CVector (2 ^ dim) := fun k' _ => if k' = k then 1 else 0

@[simp] theorem e_apply (dim : ℕ) (k k' : Fin (2 ^ dim)) (j : Fin 1) :
    e dim k k' j = if k' = k then 1 else 0 := rfl

@[simp] theorem ι_e (dim : ℕ) (k : Fin (2 ^ dim)) : ι dim (e dim k) = ket (idxBasis dim k) := by
  rw [ι_apply, Finset.sum_eq_single k]
  · simp
  · intro k' _ hk'; simp [hk']
  · intro h; exact absurd (Finset.mem_univ k) h

theorem mul_eq_sum_e (dim : ℕ) (M : CSquare (2 ^ dim)) (v : CVector (2 ^ dim)) :
    M * v = ∑ k, v k 0 • (M * e dim k) := by
  ext k' j
  have hj : j = 0 := Subsingleton.elim j 0
  subst hj
  rw [Finset.sum_apply, Finset.sum_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Finset.sum_eq_single i]
  · simp [mul_comm]
  · intro j' _ hj'; simp [hj']
  · intro h; exact absurd (Finset.mem_univ i) h

theorem eq_sum_e (dim : ℕ) (v : CVector (2 ^ dim)) : v = ∑ k, v k 0 • e dim k := by
  ext k' j
  rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_eq_single k']
  · simp [Subsingleton.elim j 0]
  · intro k _ hk; simp [Ne.symm hk]
  · intro h; exact absurd (Finset.mem_univ k') h

theorem ι_mul_e (dim : ℕ) (M : CSquare (2 ^ dim)) (k : Fin (2 ^ dim)) :
    ι dim (M * e dim k) = ∑ k' : Fin (2 ^ dim), M k' k • ket (idxBasis dim k') := by
  rw [ι_apply]
  refine Finset.sum_congr rfl fun k' _ => ?_
  congr 1
  rw [Matrix.mul_apply, Finset.sum_eq_single k]
  · simp
  · intro j _ hj; simp [hj]
  · intro h; exact absurd (Finset.mem_univ k) h

/-- **The transfer principle.** A unitary of the standard model agrees with a
matrix on the whole embedded subspace as soon as it agrees on every ket. -/
theorem transfer_of_ket {dim : ℕ} (T : State ≃ₗᵢ[ℂ] State) (M : CSquare (2 ^ dim))
    (h : ∀ k, T (ket (idxBasis dim k)) = ι dim (M * e dim k)) (v : CVector (2 ^ dim)) :
    T (ι dim v) = ι dim (M * v) := by
  calc T (ι dim v)
      = ∑ k : Fin (2 ^ dim), v k 0 • T (ket (idxBasis dim k)) := by
        rw [ι_apply, map_sum]
        exact Finset.sum_congr rfl fun k _ => map_smul _ _ _
    _ = ∑ k : Fin (2 ^ dim), v k 0 • ι dim (M * e dim k) := by
        exact Finset.sum_congr rfl fun k _ => by rw [h k]
    _ = ι dim (∑ k : Fin (2 ^ dim), v k 0 • (M * e dim k)) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun k _ => (map_smul _ _ _).symm
    _ = ι dim (M * v) := by
        rw [mul_eq_sum_e dim M v]

/-! ## Norms and inner products -/

/-- The squared ℓ² norm of a column vector. `Matrix`'s own norm instance is the
sup norm, so the ℓ² quantity is named explicitly here and never left implicit. -/
noncomputable def cnorm2 {n : ℕ} (v : CVector n) : ℝ := ∑ k : Fin n, ‖v k 0‖ ^ 2

theorem inner_ι (dim : ℕ) (u v : CVector (2 ^ dim)) :
    inner ℂ (ι dim u) (ι dim v) = ∑ k : Fin (2 ^ dim), conj (u k 0) * v k 0 := by
  rw [ι_apply, ι_apply, sum_inner]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_sum, Finset.sum_eq_single k]
  · rw [inner_smul_left, inner_smul_right, inner_eq_innerS, innerS_ket_self]
    ring
  · intro k' _ hk'
    rw [inner_smul_left, inner_smul_right, inner_eq_innerS,
      innerS_ket_of_ne (fun hc => hk' (idxBasis_injective dim hc).symm)]
    ring
  · intro h; exact absurd (Finset.mem_univ k) h

theorem norm_sq_ι (dim : ℕ) (v : CVector (2 ^ dim)) : ‖ι dim v‖ ^ 2 = cnorm2 v := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ) (ι dim v), inner_ι, cnorm2, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Complex.normSq_eq_conj_mul_self]
  simp [Complex.normSq_eq_norm_sq, -Complex.ofReal_pow]

end QuantumLib
end Model
end Shor
