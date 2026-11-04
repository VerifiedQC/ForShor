import Model.Defs

/-!
# The phase-product identity

Expands the pair and triple phase products (`pair_expansion`,
`triple_expansion`) and shows a certificate on the weights gives the identity
(`pair_identity_of_certificate`, `triple_identity_of_certificate`), with
`pair_certificate_iff` and `triple_certificate_iff` as characterizations. It
instantiates these for the concrete C11 and PTP2 weights
(`c11_phase_product_identity`, `ptp2_phase_triple_product_identity`).
-/

namespace Paper.PhaseIdentity

theorem pair_expansion {k q : Nat} (weight : Fin q → ℚ)
    (row : Fin q → Fin k → ℚ) (x z : Fin k → ℚ) :
    (∑ l, weight l * linearForm (row l) x * linearForm (row l) z) =
      ∑ i, ∑ j, (∑ l, weight l * row l i * row l j) * x i * z j := by
  conv_rhs => rw [Finset.sum_comm]
  simp only [linearForm, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem triple_expansion {k q : Nat} (weight : Fin q → ℚ)
    (row : Fin q → Fin k → ℚ) (x y z : Fin k → ℚ) :
    (∑ l, weight l * linearForm (row l) x * linearForm (row l) y *
      linearForm (row l) z) =
      ∑ i, ∑ j, ∑ t, (∑ l, weight l * row l i * row l j * row l t) *
        x i * y j * z t := by
  conv_rhs =>
    rw [Finset.sum_comm]
    arg 2
    ext j
    rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  simp only [linearForm, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem pair_identity_of_certificate {k q : Nat} (weight : Fin q → ℚ)
    (row : Fin q → Fin k → ℚ) (base : Fin k → ℚ)
    (h : PairCertificate weight row base) (x z : Fin k → ℚ) :
    (∑ l, weight l * linearForm (row l) x * linearForm (row l) z) =
      linearForm base x * linearForm base z := by
  rw [pair_expansion]
  dsimp only [PairCertificate] at h
  simp_rw [h]
  simp only [linearForm, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem triple_identity_of_certificate {k q : Nat} (weight : Fin q → ℚ)
    (row : Fin q → Fin k → ℚ) (base : Fin k → ℚ)
    (h : TripleCertificate weight row base) (x y z : Fin k → ℚ) :
    (∑ l, weight l * linearForm (row l) x * linearForm (row l) y * linearForm (row l) z) =
      linearForm base x * linearForm base y * linearForm base z := by
  rw [triple_expansion]
  dsimp only [TripleCertificate] at h
  simp_rw [h]
  simp only [linearForm, Finset.sum_mul, Finset.mul_sum]
  conv_rhs =>
    rw [Finset.sum_comm]
    arg 2
    ext j
    rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem pair_certificate_iff {k q : Nat} (weight : Fin q → ℚ)
    (row : Fin q → Fin k → ℚ) (base : Fin k → ℚ) :
    PairCertificate weight row base ↔
      ∀ x z, (∑ l, weight l * linearForm (row l) x * linearForm (row l) z) =
        linearForm base x * linearForm base z := by
  constructor
  · exact pair_identity_of_certificate weight row base
  · intro h i j
    simpa [linearForm] using h (fun t => if t = i then 1 else 0)
      (fun t => if t = j then 1 else 0)

theorem triple_certificate_iff {k q : Nat} (weight : Fin q → ℚ)
    (row : Fin q → Fin k → ℚ) (base : Fin k → ℚ) :
    TripleCertificate weight row base ↔
      ∀ x y z, (∑ l, weight l * linearForm (row l) x * linearForm (row l) y * linearForm (row l) z) =
        linearForm base x * linearForm base y * linearForm base z := by
  constructor
  · exact triple_identity_of_certificate weight row base
  · intro h i j t
    simpa [linearForm] using h (fun s => if s = i then 1 else 0)
      (fun s => if s = j then 1 else 0) (fun s => if s = t then 1 else 0)

theorem c11_pair_certificate (b : ℚ) : PairCertificate (c11Weights b) c11Rows (c11Base b) := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [c11Weights, c11Rows, c11Base, Fin.sum_univ_succ] <;> ring

theorem c11_phase_product_identity (b : ℚ) (x z : Fin 3 → ℚ) :
    (∑ l, c11Weights b l * linearForm (c11Rows l) x * linearForm (c11Rows l) z) =
      (x 0 + b*x 1 + b^2*x 2) * (z 0 + b*z 1 + b^2*z 2) := by
  simpa [linearForm, c11Base, Fin.sum_univ_succ, add_assoc] using
    pair_identity_of_certificate _ _ _ (c11_pair_certificate b) x z

theorem ptp2_triple_certificate (b : ℚ) :
    TripleCertificate (ptp2Weights b) ptp2Rows (ptp2Base b) := by
  intro i j t
  fin_cases i <;> fin_cases j <;> fin_cases t <;>
    simp [ptp2Weights, ptp2Rows, ptp2Base, Fin.sum_univ_succ] <;> ring

theorem ptp2_phase_triple_product_identity (b : ℚ) (x y z : Fin 2 → ℚ) :
    (∑ l, ptp2Weights b l * linearForm (ptp2Rows l) x * linearForm (ptp2Rows l) y *
      linearForm (ptp2Rows l) z) =
      (x 0 + b*x 1) * (y 0 + b*y 1) * (z 0 + b*z 1) := by
  simpa [linearForm, ptp2Base, Fin.sum_univ_succ] using
    triple_identity_of_certificate _ _ _ (ptp2_triple_certificate b) x y z

end Paper.PhaseIdentity
