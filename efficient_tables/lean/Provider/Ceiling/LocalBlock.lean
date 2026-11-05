import Provider.Ceiling.Coefficients

/-! # Local Blocks
Proves fixed-length statements for the local blocks: `computeLocal_fixed_length` and `computeFracLocal_fixed_length`, via the auxiliaries `computeLocalAux_fixed_length` and `computeFracLocalAux_fixed_length`. Also states the coefficient bound `coeffDyadic_pow_bound`.
-/

namespace Paper.F3ChargeCeiling

open TableGeneration

theorem coeffDyadic_pow_bound {k E : Nat} (z : Int) (e j : Nat)
    (he : e ≤ k) (hj : j ≤ k - 1) (hE : k * (k - 1) ≤ E)
    (hz : z.natAbs = 2^e) : CoeffDyadic E (z^j) := by
  apply coeffDyadic_pow z e j
  · calc
      e * j ≤ k * j := Nat.mul_le_mul_right j he
      _ ≤ k * (k - 1) := Nat.mul_le_mul_left k hj
      _ ≤ E := hE
  · exact hz

theorem computeLocalAux_fixed_length {k E : Nat} (hk : 0 < k)
    (z : Int) (hz : ∃ e, e ≤ k ∧ (z = 0 ∨ z.natAbs = 2^e))
    (hE : k * (k - 1) ≤ E) (js : List (Fin k))
    (hjs : ∀ j ∈ js, j ≠ finZero hk) :
    SourceFixed (finZero hk) E (computeLocalAux hk z js) ∧
      (computeLocalAux hk z js).length ≤ js.length := by
  induction js with
  | nil => simp [computeLocalAux, SourceFixed]
  | cons j rest ih =>
    have hj : j ≠ finZero hk := hjs j (by simp)
    have hrest : ∀ x ∈ rest, x ≠ finZero hk := by
      intro x hx
      exact hjs x (by simp [hx])
    have hi := ih hrest
    have hpow : CoeffDyadic E (z ^ j.val) := by
      rcases hz with ⟨e, he, hz | hz⟩
      · subst z
        exact coeffDyadic_zero_pow E j.val
      · exact coeffDyadic_pow_bound z e j.val he (by omega) hE hz
    have hadd := addConstFrom_coeff_fixed (finZero hk) j E hj (z^j.val) hpow
    constructor
    · simpa only [computeLocalAux] using sourceFixed_append hadd.1 hi.1
    · simp only [computeLocalAux, List.length_append, List.length_cons]
      omega

theorem computeLocal_fixed_length {k E : Nat} (hk : 0 < k)
    (z : Int) (hz : ∃ e, e ≤ k ∧ (z = 0 ∨ z.natAbs = 2^e))
    (hE : k * (k - 1) ≤ E) :
    SourceFixed (finZero hk) E (computeLocal hk z) ∧
      (computeLocal hk z).length ≤ (nonzeroFins hk).length := by
  apply computeLocalAux_fixed_length hk z hz hE
  intro j hj
  simp only [nonzeroFins, List.mem_filter] at hj
  simpa using hj.2

theorem computeFracLocalAux_fixed_length {k E : Nat} (hk : 0 < k)
    (c : Int) (hc : ∃ e, e ≤ k ∧ (c = 0 ∨ c.natAbs = 2^e))
    (hE : k * (k - 1) ≤ E) (js : List (Fin k))
    (hjs : ∀ j ∈ js, j ≠ finLast hk) :
    SourceFixed (finLast hk) E (computeFracLocalAux hk c js) ∧
      (computeFracLocalAux hk c js).length ≤ js.length := by
  induction js with
  | nil => simp [computeFracLocalAux, SourceFixed]
  | cons j rest ih =>
    have hj : j ≠ finLast hk := hjs j (by simp)
    have hrest : ∀ x ∈ rest, x ≠ finLast hk := by
      intro x hx
      exact hjs x (by simp [hx])
    have hi := ih hrest
    have hpow : CoeffDyadic E (fracCoeff (k := k) c j) := by
      rcases hc with ⟨e, he, hc | hc⟩
      · subst c
        exact coeffDyadic_zero_pow E (k - 1 - j.val)
      · exact coeffDyadic_pow_bound c e (k - 1 - j.val) he (by omega) hE hc
    have hadd := addConstFrom_coeff_fixed (finLast hk) j E hj
      (fracCoeff (k := k) c j) hpow
    constructor
    · simpa only [computeFracLocalAux] using sourceFixed_append hadd.1 hi.1
    · simp only [computeFracLocalAux, List.length_append, List.length_cons]
      omega

theorem computeFracLocal_fixed_length {k E : Nat} (hk : 0 < k)
    (c : Int) (hc : ∃ e, e ≤ k ∧ (c = 0 ∨ c.natAbs = 2^e))
    (hE : k * (k - 1) ≤ E) :
    SourceFixed (finLast hk) E (computeFracLocal hk c) ∧
      (computeFracLocal hk c).length ≤ (nonlastFins hk).length := by
  apply computeFracLocalAux_fixed_length hk c hc hE
  intro j hj
  simp only [nonlastFins, List.mem_filter] at hj
  simpa using hj.2

end Paper.F3ChargeCeiling
