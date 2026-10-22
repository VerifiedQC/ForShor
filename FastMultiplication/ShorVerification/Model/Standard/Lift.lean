import FastMultiplication.ShorVerification.Model.Standard.State
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Lifting basis-level data to unitaries on `State`

Item 4 of the original construction plan, and the heart of the model.

Every primitive gate law in `Framework/Semantics/` gives the image of a ket
explicitly, and the right-hand sides come in exactly three shapes: a relabelling
of the basis, a diagonal phase, and a `2^w × 2^w` block acting on one register.
Each is `Finsupp.linearCombination` of a family `v : ModelBasis → State` that is
orthonormal, and each has an explicit inverse of the same shape, so all three
are built by one construction, `liftIso`.

`blockLift` is where the usual finite matrices live. The `kron`/`pad` with
identity on every other qubit that a fixed-dimension development writes out is
what `mWriteNat` touching only `r`'s bits does implicitly here.
-/

namespace Shor
namespace Model

open scoped ComplexConjugate

/-! ## The generic lift -/

/-- The linear extension of `v` along the basis. -/
noncomputable def liftMap (v : ModelBasis → State) : State →ₗ[ℂ] State :=
  Finsupp.linearCombination ℂ v

@[simp] theorem liftMap_ket (v : ModelBasis → State) (b : ModelBasis) :
    liftMap v (ket b) = v b := by
  rw [liftMap, ket, Finsupp.linearCombination_single, one_smul]

theorem liftMap_eq_sum (v : ModelBasis → State) (f : State) :
    liftMap v f = ∑ b ∈ f.support, f b • v b := by
  rw [liftMap, Finsupp.linearCombination_apply, Finsupp.sum]

/-- Two linear maps agreeing on every ket are equal. -/
theorem lift_ext {F G : State →ₗ[ℂ] State} (h : ∀ b, F (ket b) = G (ket b)) : F = G := by
  refine Finsupp.lhom_ext (φ := F) (ψ := G) fun a c => ?_
  have hc : (Finsupp.single a c : State) = c • ket a := by
    rw [ket, Finsupp.smul_single]; simp
  rw [hc, map_smul, map_smul, h a]

/-- If `v` is orthonormal, its linear extension preserves the inner product. -/
theorem inner_liftMap (v : ModelBasis → State)
    (hself : ∀ b, innerS (v b) (v b) = 1)
    (hne : ∀ b b', b ≠ b' → innerS (v b) (v b') = 0)
    (f g : State) :
    innerS (liftMap v f) (liftMap v g) = innerS f g := by
  classical
  rw [← inner_eq_innerS, liftMap_eq_sum v f, liftMap_eq_sum v g, sum_inner,
    innerS_eq_sum f g (subset_refl _)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [inner_sum]
  have key : ∀ b' ∈ g.support,
      (inner ℂ (f b • v b) (g b' • v b') : ℂ)
        = if b' = b then conj (f b) * g b else 0 := by
    intro b' _
    rw [inner_smul_left, inner_smul_right]
    by_cases h : b' = b
    · subst h
      rw [if_pos rfl, inner_eq_innerS, hself b']
      ring
    · rw [if_neg h, inner_eq_innerS, hne b b' (Ne.symm h)]
      ring
  rw [Finset.sum_congr rfl key, Finset.sum_ite_eq' g.support b]
  by_cases hbg : b ∈ g.support
  · rw [if_pos hbg]
  · rw [if_neg hbg, Finsupp.notMem_support_iff.mp hbg]
    ring

/-- A pair of mutually inverse orthonormal families gives a linear isometry
equivalence. All three lifts below are instances of this. -/
noncomputable def liftIso (v w : ModelBasis → State)
    (hvw : ∀ b, liftMap w (v b) = ket b)
    (hwv : ∀ b, liftMap v (w b) = ket b)
    (hself : ∀ b, innerS (v b) (v b) = 1)
    (hne : ∀ b b', b ≠ b' → innerS (v b) (v b') = 0) :
    State ≃ₗᵢ[ℂ] State :=
  LinearEquiv.isometryOfInner
    (LinearEquiv.ofLinear (liftMap v) (liftMap w)
      (lift_ext (by intro b; simp [hwv b]))
      (lift_ext (by intro b; simp [hvw b])))
    (fun x y => inner_liftMap v hself hne x y)

@[simp] theorem liftIso_ket (v w : ModelBasis → State) (hvw hwv hself hne) (b : ModelBasis) :
    liftIso v w hvw hwv hself hne (ket b) = v b := by
  simp [liftIso]

/-! ## 1. Basis relabelling -/

/-- A permutation of the computational basis, lifted to a unitary. -/
noncomputable def permLift (σ : Equiv.Perm ModelBasis) : State ≃ₗᵢ[ℂ] State :=
  liftIso (fun b => ket (σ b)) (fun b => ket (σ.symm b))
    (by intro b; simp)
    (by intro b; simp)
    (by intro b; exact innerS_ket_self _)
    (by intro b b' h; exact innerS_ket_of_ne (fun hc => h (σ.injective hc)))

@[simp] theorem permLift_ket (σ : Equiv.Perm ModelBasis) (b : ModelBasis) :
    permLift σ (ket b) = ket (σ b) := by simp [permLift]

/-! ## 2. Diagonal phases -/

/-- Pointwise multiplication by a unit-modulus function of the basis state. -/
noncomputable def diagLift (φ : ModelBasis → ℂ) (hφ : ∀ b, ‖φ b‖ = 1) :
    State ≃ₗᵢ[ℂ] State := by
  have hmul : ∀ b, conj (φ b) * φ b = 1 := by
    intro b; rw [RCLike.conj_mul]; norm_cast; rw [hφ b]; norm_num
  refine liftIso (fun b => φ b • ket b) (fun b => conj (φ b) • ket b) ?_ ?_ ?_ ?_
  · intro b
    rw [map_smul, liftMap_ket, smul_smul, mul_comm, hmul b, one_smul]
  · intro b
    rw [map_smul, liftMap_ket, smul_smul, hmul b, one_smul]
  · intro b
    rw [innerS_smul_left, ← inner_eq_innerS, inner_smul_right, inner_eq_innerS,
      innerS_ket_self, mul_one, hmul b]
  · intro b b' h
    rw [innerS_smul_left, ← inner_eq_innerS, inner_smul_right, inner_eq_innerS,
      innerS_ket_of_ne h, mul_zero, mul_zero]

@[simp] theorem diagLift_ket (φ : ModelBasis → ℂ) (hφ : ∀ b, ‖φ b‖ = 1) (b : ModelBasis) :
    diagLift φ hφ (ket b) = φ b • ket b := by simp [diagLift]

/-! ## 3. A unitary block on one register

This is the SQIR-style part of the model: the matrices are the usual finite
`2^w × 2^w` ones. What a fixed-dimension development writes as an explicit
`kron` with the identity on every other qubit is here exactly the fact that
`mWriteNat r` touches only `r`'s bits.
-/

/-- The value register `r` holds, as an index into the block. -/
def blockIdx (r : Reg) (b : ModelBasis) : Fin (ASize r) := ⟨mToNat r b, mToNat_lt r b⟩

@[simp] theorem blockIdx_val (r : Reg) (b : ModelBasis) :
    (blockIdx r b).1 = mToNat r b := rfl

@[simp] theorem blockIdx_mWriteNat (r : Reg) (y : Fin (ASize r)) (b : ModelBasis) :
    blockIdx r (mWriteNat r y.1 b) = y :=
  Fin.ext (mToNat_mWriteNat b y.2)

@[simp] theorem mWriteNat_blockIdx (r : Reg) (b : ModelBasis) :
    mWriteNat r (blockIdx r b).1 b = b := mWriteNat_mToNat r b

/-- The image of `ket b` under the block `M` acting on register `r`. -/
noncomputable def blockVec (r : Reg) (M : Matrix (Fin (ASize r)) (Fin (ASize r)) ℂ)
    (b : ModelBasis) : State :=
  ∑ y : Fin (ASize r), M y (blockIdx r b) • ket (mWriteNat r y.1 b)

theorem blockVec_eq (r : Reg) (M : Matrix (Fin (ASize r)) (Fin (ASize r)) ℂ) (b : ModelBasis) :
    blockVec r M b = ∑ y : Fin (ASize r), M y (blockIdx r b) • ket (mWriteNat r y.1 b) := rfl

theorem sum_one_smul_ket (r : Reg) (x : Fin (ASize r)) (u : Fin (ASize r) → ModelBasis) :
    ∑ y : Fin (ASize r),
        ((1 : Matrix (Fin (ASize r)) (Fin (ASize r)) ℂ) y x) • ket (u y) = ket (u x) := by
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy; simp [hy]
  · intro h; exact absurd (Finset.mem_univ x) h

/-- Composing two blocks on the same register multiplies the matrices. -/
theorem liftMap_blockVec (r : Reg) (M N : Matrix (Fin (ASize r)) (Fin (ASize r)) ℂ)
    (b : ModelBasis) :
    liftMap (blockVec r N) (blockVec r M b)
      = ∑ y' : Fin (ASize r), (N * M) y' (blockIdx r b) • ket (mWriteNat r y'.1 b) := by
  rw [blockVec_eq r M b, map_sum]
  have step : ∀ y : Fin (ASize r),
      liftMap (blockVec r N) (M y (blockIdx r b) • ket (mWriteNat r y.1 b))
        = ∑ y' : Fin (ASize r), (N y' y * M y (blockIdx r b)) • ket (mWriteNat r y'.1 b) := by
    intro y
    rw [map_smul, liftMap_ket, blockVec_eq, blockIdx_mWriteNat, Finset.smul_sum]
    refine Finset.sum_congr rfl fun y' _ => ?_
    rw [smul_smul, mWriteNat_mWriteNat, mul_comm]
  rw [Finset.sum_congr rfl (fun y _ => step y), Finset.sum_comm]
  refine Finset.sum_congr rfl fun y' _ => ?_
  rw [Matrix.mul_apply, Finset.sum_smul]

/-- Sesquilinear expansion of the inner product of two block images. -/
theorem innerS_blockVec (r : Reg) (M : Matrix (Fin (ASize r)) (Fin (ASize r)) ℂ)
    (b b' : ModelBasis) :
    innerS (blockVec r M b) (blockVec r M b')
      = ∑ y : Fin (ASize r), ∑ y' : Fin (ASize r),
          conj (M y (blockIdx r b)) * M y' (blockIdx r b') *
            innerS (ket (mWriteNat r y.1 b)) (ket (mWriteNat r y'.1 b')) := by
  rw [blockVec_eq, blockVec_eq, ← inner_eq_innerS, sum_inner]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun y' _ => ?_
  rw [inner_smul_left, inner_smul_right, inner_eq_innerS]
  ring

/-- `star M * M = 1`, read entrywise. -/
theorem star_mul_apply (r : Reg) (M : Matrix (Fin (ASize r)) (Fin (ASize r)) ℂ)
    (x x' : Fin (ASize r)) :
    (star M * M) x x' = ∑ y : Fin (ASize r), conj (M y x) * M y x' := by
  rw [Matrix.mul_apply]
  exact Finset.sum_congr rfl fun y _ => by rw [Matrix.star_apply]; rfl

theorem innerS_blockVec_of_agree (r : Reg) (M : Matrix (Fin (ASize r)) (Fin (ASize r)) ℂ)
    (hM : star M * M = 1) (b b' : ModelBasis)
    (hoff : ∀ q, q ∉ r.qubits → b q = b' q) :
    innerS (blockVec r M b) (blockVec r M b')
      = if blockIdx r b = blockIdx r b' then 1 else 0 := by
  have key : ∀ y y' : Fin (ASize r),
      innerS (ket (mWriteNat r y.1 b)) (ket (mWriteNat r y'.1 b'))
        = if y = y' then 1 else 0 := by
    intro y y'
    by_cases h : y = y'
    · subst h
      rw [if_pos rfl, (mWriteNat_eq_iff y.2 y.2).mpr ⟨rfl, hoff⟩]
      exact innerS_ket_self _
    · rw [if_neg h]
      exact innerS_ket_of_ne fun hc => h (Fin.ext ((mWriteNat_eq_iff y.2 y'.2).mp hc).1)
  rw [innerS_blockVec]
  have collapse : ∀ y : Fin (ASize r),
      (∑ y' : Fin (ASize r), conj (M y (blockIdx r b)) * M y' (blockIdx r b') *
          innerS (ket (mWriteNat r y.1 b)) (ket (mWriteNat r y'.1 b')))
        = conj (M y (blockIdx r b)) * M y (blockIdx r b') := by
    intro y
    rw [Finset.sum_congr rfl (fun y' (_ : y' ∈ Finset.univ) =>
      show conj (M y (blockIdx r b)) * M y' (blockIdx r b') *
            innerS (ket (mWriteNat r y.1 b)) (ket (mWriteNat r y'.1 b'))
          = if y = y' then conj (M y (blockIdx r b)) * M y' (blockIdx r b') else 0 by
        rw [key y y']; by_cases h : y = y' <;> simp [h]),
      Finset.sum_ite_eq Finset.univ y
        (fun y' => conj (M y (blockIdx r b)) * M y' (blockIdx r b')), if_pos (Finset.mem_univ y)]
  rw [Finset.sum_congr rfl (fun y _ => collapse y), ← star_mul_apply, hM, Matrix.one_apply]

theorem innerS_blockVec_of_disagree (r : Reg) (M : Matrix (Fin (ASize r)) (Fin (ASize r)) ℂ)
    (b b' : ModelBasis) (hoff : ¬ ∀ q, q ∉ r.qubits → b q = b' q) :
    innerS (blockVec r M b) (blockVec r M b') = 0 := by
  rw [innerS_blockVec]
  refine Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun y' _ => ?_
  have : innerS (ket (mWriteNat r y.1 b)) (ket (mWriteNat r y'.1 b')) = 0 :=
    innerS_ket_of_ne fun hc => hoff ((mWriteNat_eq_iff y.2 y'.2).mp hc).2
  rw [this, mul_zero]

theorem innerS_blockVec_self (r : Reg) (M : Matrix (Fin (ASize r)) (Fin (ASize r)) ℂ)
    (hM : star M * M = 1) (b : ModelBasis) :
    innerS (blockVec r M b) (blockVec r M b) = 1 := by
  rw [innerS_blockVec_of_agree r M hM b b (fun _ _ => rfl), if_pos rfl]

theorem innerS_blockVec_of_ne (r : Reg) (M : Matrix (Fin (ASize r)) (Fin (ASize r)) ℂ)
    (hM : star M * M = 1) (b b' : ModelBasis) (hb : b ≠ b') :
    innerS (blockVec r M b) (blockVec r M b') = 0 := by
  by_cases hoff : ∀ q, q ∉ r.qubits → b q = b' q
  · rw [innerS_blockVec_of_agree r M hM b b' hoff, if_neg]
    intro hc
    exact hb (eq_of_agree_off hoff (congrArg Fin.val hc))
  · exact innerS_blockVec_of_disagree r M b b' hoff

/-- A `2^w × 2^w` unitary acting on register `r` and trivially elsewhere. -/
noncomputable def blockLift (r : Reg) (M : Matrix (Fin (ASize r)) (Fin (ASize r)) ℂ)
    (hM : M ∈ Matrix.unitaryGroup (Fin (ASize r)) ℂ) : State ≃ₗᵢ[ℂ] State := by
  have h1 : star M * M = 1 := Matrix.mem_unitaryGroup_iff'.mp hM
  have h2 : M * star M = 1 := Matrix.mem_unitaryGroup_iff.mp hM
  refine liftIso (blockVec r M) (blockVec r (star M)) ?_ ?_ ?_ ?_
  · intro b
    rw [liftMap_blockVec, h1, sum_one_smul_ket, mWriteNat_blockIdx]
  · intro b
    rw [liftMap_blockVec, h2, sum_one_smul_ket, mWriteNat_blockIdx]
  · exact innerS_blockVec_self r M h1
  · exact innerS_blockVec_of_ne r M h1

@[simp] theorem blockLift_ket (r : Reg) (M : Matrix (Fin (ASize r)) (Fin (ASize r)) ℂ)
    (hM : M ∈ Matrix.unitaryGroup (Fin (ASize r)) ℂ) (b : ModelBasis) :
    blockLift r M hM (ket b)
      = ∑ y : Fin (ASize r), M y (blockIdx r b) • ket (mWriteNat r y.1 b) := by
  simp [blockLift, blockVec]

end Model
end Shor
