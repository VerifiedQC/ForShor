import Model.Defs

/-!
# Interpolation moments and uniqueness

Moment identities for finite interpolation weights over rational nodes: the
moment property `moment` and its low-degree form `finite_moment_of_lt`.
The theorem `weights_unique` shows the weights are determined by the moment
conditions.
-/

namespace Paper.Interpolation

theorem finite_moment_of_lt {d : Nat} (v : Fin d → ℚ)
    (hv : Function.Injective v) (b : ℚ) (m : Nat) (hm : m < d) :
    (∑ i, finiteWeight v b i * v i ^ m) = b ^ m := by
  have hdeg : ((Polynomial.X : Polynomial ℚ) ^ m).degree <
      (Finset.univ : Finset (Fin d)).card := by
    simpa [Polynomial.degree_X_pow] using hm
  have hp := Lagrange.eq_interpolate (v := v) (s := Finset.univ)
    (f := (Polynomial.X : Polynomial ℚ) ^ m) hv.injOn hdeg
  have heval := congrArg (Polynomial.eval b) hp
  simpa [Lagrange.interpolate_apply, finiteWeight, Polynomial.eval_finset_sum,
    Polynomial.eval_mul, Polynomial.eval_pow, mul_comm] using heval.symm

theorem moment {d : Nat} (v : Fin d → ℚ)
    (hv : Function.Injective v) (b : ℚ) (m : Nat) (hm : m ≤ d) :
    (∑ i, finiteWeight v b i * v i ^ m) +
      infinityWeight v b * (if m = d then 1 else 0) = b ^ m := by
  rcases lt_or_eq_of_le hm with hlt | rfl
  · simpa [infinityWeight, hlt.ne] using finite_moment_of_lt v hv b m hlt
  · simp [infinityWeight]

theorem weights_unique {d : Nat} (v : Fin d → ℚ)
    (hv : Function.Injective v) (b : ℚ) (w : Fin d → ℚ) (z : ℚ)
    (h : ∀ m : Nat, m ≤ d →
      (∑ i, w i * v i ^ m) + z * (if m = d then 1 else 0) = b ^ m) :
    w = finiteWeight v b ∧ z = infinityWeight v b := by
  have hdiff (m : Fin d) :
      (∑ i, (w i - finiteWeight v b i) * v i ^ (m : Nat)) = 0 := by
    have hne : (m : Nat) ≠ d := Nat.ne_of_lt m.isLt
    have hw := h (m : Nat) (Nat.le_of_lt m.isLt)
    simp [hne] at hw
    have hf := finite_moment_of_lt v hv b (m : Nat) m.isLt
    calc
      (∑ i, (w i - finiteWeight v b i) * v i ^ (m : Nat)) =
          (∑ i, w i * v i ^ (m : Nat)) -
          (∑ i, finiteWeight v b i * v i ^ (m : Nat)) := by
        simp [sub_mul, Finset.sum_sub_distrib]
      _ = 0 := by rw [hw, hf]; ring
  have hzero : (fun i => w i - finiteWeight v b i) = 0 :=
    Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hv hdiff
  have hw : w = finiteWeight v b := by
    funext i
    have hi := congrFun hzero i
    exact sub_eq_zero.mp (by simpa using hi)
  constructor
  · exact hw
  · have htop := h d le_rfl
    rw [hw] at htop
    simp only [↓reduceIte, mul_one] at htop
    dsimp [infinityWeight]
    linarith

theorem zero_degree_moment (v : Fin 0 → ℚ) (b : ℚ) :
    infinityWeight v b = 1 := by
  have hv : Function.Injective v := by
    intro i
    exact Fin.elim0 i
  have h := moment v hv b 0 le_rfl
  simpa using h

end Paper.Interpolation
