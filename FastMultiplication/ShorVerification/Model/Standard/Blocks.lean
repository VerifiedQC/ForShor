import FastMultiplication.ShorVerification.Model.Standard.Lift
import FastMultiplication.ShorVerification.Model.Standard.BasisMaps
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# The two matrix blocks, and the diagonal phases

Item 6 of the original construction plan. `H` and `QFT` are the only gates whose laws are not
a relabelling of the basis or a diagonal phase: each is a `2^w × 2^w` unitary
acting on one register. Those matrices are the ordinary finite ones, and
`blockLift` is what puts them on an infinite basis.
-/

namespace Shor
namespace Model

open scoped ComplexConjugate

/-! ## Hadamard -/

/-- The one-qubit Hadamard matrix. -/
noncomputable def hadamardMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1 / (Real.sqrt 2 : ℝ), 1 / (Real.sqrt 2 : ℝ);
     1 / (Real.sqrt 2 : ℝ), -(1 / (Real.sqrt 2 : ℝ))]

theorem sqrt_two_sq : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
  have h : (Real.sqrt 2 : ℝ) * (Real.sqrt 2 : ℝ) = 2 := Real.mul_self_sqrt (by norm_num)
  exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) h

theorem sqrt_two_ne_zero : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
  intro h
  have := sqrt_two_sq
  rw [h, mul_zero] at this
  norm_num at this

theorem hadamardMatrix_unitary : hadamardMatrix ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by rw [sq]; exact sqrt_two_sq
  have hne := sqrt_two_ne_zero
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, hadamardMatrix, Fin.sum_univ_two,
      Matrix.star_apply, Complex.conj_ofReal] <;>
    field_simp <;>
    first
      | linear_combination hs2
      | linear_combination (2 : ℂ) * hs2
      | linear_combination (-2 : ℂ) * hs2
      | linear_combination (-1 : ℂ) * hs2

/-- Hadamard on qubit `q`, as a unitary on the whole state space. -/
noncomputable def hadamardLift (q : ℕ) : State ≃ₗᵢ[ℂ] State :=
  blockLift (qubitReg q) hadamardMatrix hadamardMatrix_unitary

theorem blockIdx_qubitReg (q : ℕ) (b : ModelBasis) :
    blockIdx (qubitReg q) b = if b q then (1 : Fin 2) else 0 := by
  refine Fin.ext ?_
  rw [blockIdx_val, mToNat_qubitReg]
  cases b q <;> rfl

/-- The Hadamard law, in exactly the form `HadamardSemantics` states it. -/
theorem hadamardLift_ket (q : ℕ) (b : ModelBasis) :
    hadamardLift q (ket b)
      = ((1 / Real.sqrt (2 : ℝ) : ℂ)) •
          (ket (mWriteNat (qubitReg q) 0 b)
            + (if b q then (-1 : ℂ) else 1) • ket (mWriteNat (qubitReg q) 1 b)) := by
  show blockLift (qubitReg q) hadamardMatrix hadamardMatrix_unitary (ket b) = _
  refine (blockLift_ket _ _ _ b).trans ?_
  have hidx := blockIdx_qubitReg q b
  show (∑ y : Fin 2, hadamardMatrix y (blockIdx (qubitReg q) b)
      • ket (mWriteNat (qubitReg q) y.1 b)) = _
  rw [Fin.sum_univ_two]
  simp only [hidx]
  cases hq : b q <;>
    simp [hadamardMatrix, smul_add]

/-! ## The quantum Fourier transform -/

/-- The `2 ^ w × 2 ^ w` QFT matrix. -/
noncomputable def qftMatrix (w : ℕ) : Matrix (Fin (2 ^ w)) (Fin (2 ^ w)) ℂ :=
  fun y x => (1 / (Real.sqrt ((2 ^ w : ℕ) : ℝ) : ℂ)) * qftPhase (2 ^ w) x.1 y.1

theorem qftMatrix_apply (w : ℕ) (y x : Fin (2 ^ w)) :
    qftMatrix w y x
      = (1 / ((Real.sqrt ((2 ^ w : ℕ) : ℝ) : ℝ) : ℂ)) * (ω (2 ^ w)) ^ (x.1 * y.1) := rfl

theorem two_pow_ne_zero_nat (w : ℕ) : (2 ^ w : ℕ) ≠ 0 := by positivity

theorem omega_primitive (w : ℕ) : IsPrimitiveRoot (ω (2 ^ w)) (2 ^ w) := by
  rw [ω]
  exact Complex.isPrimitiveRoot_exp _ (by exact_mod_cast two_pow_ne_zero_nat w)

theorem omega_pow_card (w : ℕ) : (ω (2 ^ w)) ^ (2 ^ w) = 1 :=
  (omega_primitive w).pow_eq_one

theorem omega_ne_zero (N : ℕ) : ω N ≠ 0 := Complex.exp_ne_zero _

theorem omega_eq (N : ℕ) : ω N = Complex.exp (((2 * Real.pi / N : ℝ) : ℂ) * Complex.I) := by
  rw [ω]; push_cast; ring_nf

theorem conj_omega (N : ℕ) : conj (ω N) = (ω N)⁻¹ := by
  rw [omega_eq, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem conj_omega_pow (N k : ℕ) : conj ((ω N) ^ k) = ((ω N) ^ k)⁻¹ := by
  rw [map_pow, conj_omega, inv_pow]

theorem sqrt_two_pow_sq (w : ℕ) :
    ((Real.sqrt ((2 ^ w : ℕ) : ℝ) : ℝ) : ℂ) * ((Real.sqrt ((2 ^ w : ℕ) : ℝ) : ℝ) : ℂ)
      = ((2 ^ w : ℕ) : ℂ) := by
  have h : (Real.sqrt ((2 ^ w : ℕ) : ℝ)) * (Real.sqrt ((2 ^ w : ℕ) : ℝ)) = ((2 ^ w : ℕ) : ℝ) :=
    Real.mul_self_sqrt (by positivity)
  exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) h

theorem sqrt_two_pow_ne_zero (w : ℕ) : ((Real.sqrt ((2 ^ w : ℕ) : ℝ) : ℝ) : ℂ) ≠ 0 := by
  intro h
  have := sqrt_two_pow_sq w
  rw [h, mul_zero] at this
  exact (two_pow_ne_zero_nat w) (by exact_mod_cast this.symm)

theorem qftMatrix_unitary (w : ℕ) : qftMatrix w ∈ Matrix.unitaryGroup (Fin (2 ^ w)) ℂ := by
  classical
  have hsne : ((Real.sqrt ((2 ^ w : ℕ) : ℝ) : ℝ) : ℂ) ≠ 0 := sqrt_two_pow_ne_zero w
  have hNne : ((2 ^ w : ℕ) : ℂ) ≠ 0 := by exact_mod_cast two_pow_ne_zero_nat w
  obtain ⟨sv, hsv⟩ : ∃ z : ℂ, z = 1 / ((Real.sqrt ((2 ^ w : ℕ) : ℝ) : ℝ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨zt, hzt⟩ : ∃ z : ℂ, z = ω (2 ^ w) := ⟨_, rfl⟩
  have hz0 : zt ≠ 0 := by rw [hzt]; exact omega_ne_zero _
  have hz1 : zt ^ (2 ^ w) = 1 := by rw [hzt]; exact omega_pow_card w
  have hconj : ∀ k : ℕ, conj (zt ^ k) = (zt ^ k)⁻¹ := by
    intro k; rw [hzt]; exact conj_omega_pow _ k
  have hss : conj sv * sv = 1 / ((2 ^ w : ℕ) : ℂ) := by
    rw [hsv, map_div₀, Complex.conj_ofReal, map_one, div_mul_div_comm, one_mul,
      sqrt_two_pow_sq w]
  rw [Matrix.mem_unitaryGroup_iff']
  ext x x'
  have hM : ∀ y u : Fin (2 ^ w), qftMatrix w y u = sv * zt ^ (u.1 * y.1) := by
    intro y u; rw [qftMatrix_apply, hsv, hzt]
  have hterm : ∀ y : Fin (2 ^ w),
      conj (qftMatrix w y x) * qftMatrix w y x'
        = (conj sv * sv) * (zt ^ x'.1 * (zt ^ x.1)⁻¹) ^ y.1 := by
    intro y
    rw [hM y x, hM y x', map_mul, hconj]
    simp only [pow_mul, mul_pow, inv_pow]
    ring
  have hsum : (star (qftMatrix w) * qftMatrix w) x x'
      = (conj sv * sv) * ∑ y : Fin (2 ^ w), (zt ^ x'.1 * (zt ^ x.1)⁻¹) ^ y.1 := by
    rw [Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Matrix.star_apply]
    exact hterm y
  rw [hsum, hss, Matrix.one_apply]
  by_cases hxx : x = x'
  · subst hxx
    rw [mul_inv_cancel₀ (pow_ne_zero _ hz0), ite_eq_left rfl]
    simp only [one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one]
    field_simp
  · have htne : zt ^ x'.1 * (zt ^ x.1)⁻¹ ≠ 1 := by
      intro hc
      have hpx : zt ^ x.1 ≠ 0 := pow_ne_zero _ hz0
      have he : zt ^ x'.1 = zt ^ x.1 := by field_simp at hc; exact hc
      rw [hzt] at he
      exact hxx (Fin.ext ((omega_primitive w).pow_inj x.2 x'.2 he.symm))
    have htN : (zt ^ x'.1 * (zt ^ x.1)⁻¹) ^ (2 ^ w) = 1 := by
      rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm x'.1 (2 ^ w),
        mul_comm x.1 (2 ^ w), pow_mul, pow_mul, hz1, one_pow, one_pow, inv_one, mul_one]
    have hgeom : ∑ y : Fin (2 ^ w), (zt ^ x'.1 * (zt ^ x.1)⁻¹) ^ y.1 = 0 := by
      rw [Fin.sum_univ_eq_sum_range (fun i => (zt ^ x'.1 * (zt ^ x.1)⁻¹) ^ i) (2 ^ w),
        geom_sum_eq htne, htN]
      simp
    rw [hgeom, ite_eq_right hxx, mul_zero]

/-- The QFT on an extendable register's active part. -/
noncomputable def qftLift (e : ExtReg) : State ≃ₗᵢ[ℂ] State :=
  blockLift e.active (qftMatrix e.width) (qftMatrix_unitary e.width)

/-- The QFT law, in exactly the form `QFTSemantics` states it. -/
theorem qftLift_ket (e : ExtReg) (b : ModelBasis) :
    qftLift e (ket b)
      = ((1 / Real.sqrt ((2 ^ e.width : ℕ) : ℝ) : ℂ)) •
          ∑ y : Fin (2 ^ e.width),
            (qftPhase (2 ^ e.width) (mToNat e.active b) y.1) •
              ket (mWriteNat e.active y.1 b) := by
  show blockLift e.active (qftMatrix e.width) (qftMatrix_unitary e.width) (ket b) = _
  refine (blockLift_ket _ _ _ b).trans ?_
  simp only [Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [smul_smul, qftMatrix, blockIdx_val]

/-! ## Diagonal phases -/

theorem norm_exp_real_mul_I (r : ℝ) : ‖Complex.exp ((r : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp_ofReal_mul_I]

/-- Every exponent appearing in a phase law is a real multiple of `I`. -/
theorem norm_phase (t : ℝ) (z : ℂ) (hz : ∃ r : ℝ, z = (r : ℂ)) :
    ‖Complex.exp ((t : ℂ) * Complex.I * z)‖ = 1 := by
  obtain ⟨r, rfl⟩ := hz
  rw [show ((t : ℂ) * Complex.I * (r : ℂ)) = (((t * r : ℝ)) : ℂ) * Complex.I from by
    push_cast; ring]
  exact norm_exp_real_mul_I _

/-- The diagonal of `SignedPhaseProd`. -/
noncomputable def phaseProdDiag (phi : Angle) (x z : ExtReg) (b : ModelBasis) : ℂ :=
  Complex.exp (((Angle.toReal phi : ℝ) : ℂ) * Complex.I *
    (((extToInt x b : ℤ) : ℂ) * (((extToInt z b : ℤ) : ℂ))))

theorem phaseProdDiag_norm (phi : Angle) (x z : ExtReg) (b : ModelBasis) :
    ‖phaseProdDiag phi x z b‖ = 1 :=
  norm_phase _ _ ⟨((extToInt x b : ℤ) : ℝ) * ((extToInt z b : ℤ) : ℝ), by push_cast; ring⟩

/-- The diagonal of `CSignedPhaseProd`. -/
noncomputable def cPhaseProdDiag (ctrl : ℕ) (phi : Angle) (x z : ExtReg) (b : ModelBasis) : ℂ :=
  if b ctrl then phaseProdDiag phi x z b else 1

theorem cPhaseProdDiag_norm (ctrl : ℕ) (phi : Angle) (x z : ExtReg) (b : ModelBasis) :
    ‖cPhaseProdDiag ctrl phi x z b‖ = 1 := by
  rw [cPhaseProdDiag]
  split
  · exact phaseProdDiag_norm phi x z b
  · simp

/-- The diagonal of `LowGate.Phase`. -/
noncomputable def lowPhaseDiag (q : ℕ) (θ : Angle) (b : ModelBasis) : ℂ :=
  if b q then Complex.exp (((Angle.toReal θ : ℝ) : ℂ) * Complex.I) else 1

theorem lowPhaseDiag_norm (q : ℕ) (θ : Angle) (b : ModelBasis) : ‖lowPhaseDiag q θ b‖ = 1 := by
  rw [lowPhaseDiag]
  split
  · exact norm_exp_real_mul_I _
  · simp

end Model
end Shor
