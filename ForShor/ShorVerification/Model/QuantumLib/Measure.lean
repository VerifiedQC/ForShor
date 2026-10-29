import ForShor.ShorVerification.Model.QuantumLib.Transfer
import ForShor.ShorVerification.Implementation.Shor.Main
import ForShor.ShorVerification.Implementation.Reference.Contract

/-!
# Measurement as a projector matrix

`MeasureClass.measProj` of the standard model is `Finsupp.filter`: keep the kets
whose register reads the observed outcome. On the embedded subspace that is a
diagonal `0/1` matrix, and the Born probability is the ℓ² norm of the projected
column vector.
-/

namespace Shor
namespace Model
namespace QuantumLib

open Matrix

/-- The index of the all-zeros basis state. -/
def zeroIdx (dim : ℕ) : Fin (2 ^ dim) := ⟨0, by positivity⟩

@[simp] theorem idxBasis_zeroIdx (dim : ℕ) : idxBasis dim (zeroIdx dim) = fun _ => false := by
  funext i
  simp [idxBasis, zeroIdx]

/-- The development's all-zeros input, as an embedded vector. -/
theorem ket_zero_eq (dim : ℕ) :
    qs.ket (RegEncoding.zero (Basis := qs.Basis)) = ι dim (e dim (zeroIdx dim)) := by
  rw [ι_e, idxBasis_zeroIdx]
  rfl

/-- The outcome-`o` projector on register `r`, as a diagonal matrix. -/
noncomputable def proj (dim : ℕ) (r : Reg) (o : ℕ) : CSquare (2 ^ dim) :=
  fun y x => if y = x then (if mToNat r (idxBasis dim x) = o then 1 else 0) else 0

theorem proj_mul_apply (dim : ℕ) (r : Reg) (o : ℕ) (v : CVector (2 ^ dim))
    (k : Fin (2 ^ dim)) :
    (proj dim r o * v) k 0 = (if mToNat r (idxBasis dim k) = o then 1 else 0) * v k 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single k]
  · rw [proj, ite_eq_left rfl]
  · intro k' _ hk'; rw [proj, ite_eq_right (Ne.symm hk'), zero_mul]
  · intro hc; exact absurd (Finset.mem_univ _) hc

theorem measProj_ι (dim : ℕ) (r : Reg) (o : ℕ) (v : CVector (2 ^ dim)) :
    MeasureClass.measProj (qs := qs) r o (ι dim v) = ι dim (proj dim r o * v) := by
  show measFilter r o (ι dim v) = _
  rw [ι_apply, map_sum, ι_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, measFilter_ket, proj_mul_apply]
  by_cases h : mToNat r (idxBasis dim k) = o
  · rw [ite_eq_left h, ite_eq_left h, one_mul]
  · rw [ite_eq_right h, ite_eq_right h, zero_mul, smul_zero, zero_smul]

/-- **The Born rule, as a matrix statement.** -/
theorem probMeas_ι (dim : ℕ) (r : Reg) (o : ℕ) (v : CVector (2 ^ dim)) :
    MeasureClass.probMeas (qs := qs) r o (ι dim v) = cnorm2 (proj dim r o * v) := by
  rw [MeasureClass.probMeas, measProj_ι, norm_sq_ι]

/-- Any `Below` basis state is an embedded standard basis vector. -/
theorem ket_eq_ι {dim : ℕ} {b : ModelBasis} (hb : Below dim b) :
    ket b = ι dim (e dim (basisIdx dim b)) := by
  rw [ι_e, idxBasis_basisIdx hb]

/-! ## The success probability over matrices -/

/-- The development's `probability_of_success`, read entirely in
`CSquare`/`CVector`: run the circuit matrix on the input column vector, project
onto each outcome of the output register, and weight the squared ℓ² norms by the
continued-fraction post-processing indicator. -/
noncomputable def qlSuccessOn (dim : ℕ) (C : LowGate) (x : Reg) (T : ℕ → ℕ)
    (verify : ℕ → Bool) (r Q : ℕ) (w : CVector (2 ^ dim)) : ℝ :=
  ∑ o : Fin Q,
    r_found (T := T) verify o.1 Q r * cnorm2 (proj dim x o.1 * (denote dim C * w))

/-- **The bridge.** On any embedded input, the abstract success probability and
the matrix one are the same number. -/
theorem probability_of_success_ι {dim : ℕ} (C : LowGate) (h : maxQubit C ≤ dim)
    (T : ℕ → ℕ) (verify : ℕ → Bool) (x : Reg) (r Q : ℕ) (w : CVector (2 ^ dim)) :
    probability_of_success (qs := qs) (evalC := LowerGateClass.evalL (qs := qs))
        (T := T) (verify := verify) (x := x) (r := r) (Q := Q) (C := C) (ψ := ι dim w)
      = qlSuccessOn dim C x T verify r Q w := by
  rw [probability_of_success, qlSuccessOn]
  refine Finset.sum_congr rfl fun o _ => ?_
  congr 1
  rw [evalL_ι C h, probMeas_ι]

/-- The all-zeros-input specialisation: the input of every headline theorem
stated over `qs.ket RegEncoding.zero`. -/
noncomputable def qlSuccess (dim : ℕ) (C : LowGate) (x : Reg) (T : ℕ → ℕ)
    (verify : ℕ → Bool) (r Q : ℕ) : ℝ :=
  qlSuccessOn dim C x T verify r Q (e dim (zeroIdx dim))

theorem probability_of_success_eq {dim : ℕ} (C : LowGate) (h : maxQubit C ≤ dim)
    (T : ℕ → ℕ) (verify : ℕ → Bool) (x : Reg) (r Q : ℕ) :
    probability_of_success (qs := qs) (evalC := LowerGateClass.evalL (qs := qs))
        (T := T) (verify := verify) (x := x) (r := r) (Q := Q) (C := C)
        (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis)))
      = qlSuccess dim C x T verify r Q := by
  rw [ket_zero_eq dim, probability_of_success_ι C h, qlSuccess]

theorem probability_of_success_ket {dim : ℕ} (C : LowGate) (h : maxQubit C ≤ dim)
    (T : ℕ → ℕ) (verify : ℕ → Bool) (x : Reg) (r Q : ℕ)
    {b : qs.Basis} (hb : Below dim b) :
    probability_of_success (qs := qs) (evalC := LowerGateClass.evalL (qs := qs))
        (T := T) (verify := verify) (x := x) (r := r) (Q := Q) (C := C) (ψ := qs.ket b)
      = qlSuccessOn dim C x T verify r Q (e dim (basisIdx dim b)) := by
  rw [show qs.ket b = ket b from rfl, ket_eq_ι hb, probability_of_success_ι C h]

end QuantumLib
end Model
end Shor
