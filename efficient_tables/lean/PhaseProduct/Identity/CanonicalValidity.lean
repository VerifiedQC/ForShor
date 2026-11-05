import PhaseProduct.Identity.CanonicalNodes

/-!
# Validity of the canonical points

Shows the Boolean point checker accepts the canonical points: the power-of-two
tests (`powerOfTwo_accepts`, `signedPowerOfTwo_accepts`), a single point
(`canonicalPoint_valid`) and the whole list (`canonicalPoints_valid`).
-/

namespace Paper.CanonicalValidity
open TableGeneration TableGeneration.Operations

theorem powerOfTwoFuel_accepts (e fuel : Nat) (hf : e ≤ fuel) :
    natPowerOfTwoFuel fuel (2^e) = true := by
  induction e generalizing fuel with
  | zero => cases fuel <;> simp [natPowerOfTwoFuel]
  | succ e ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hpos : 0 < 2^e := Nat.pow_pos (by decide)
      have hne0 : 2^(e+1) ≠ 0 := by positivity
      have hne1 : 2^(e+1) ≠ 1 := by rw [pow_succ]; omega
      have hmod : 2^(e+1) % 2 = 0 := by simp [pow_succ]
      have hdiv : 2^(e+1) / 2 = 2^e := by simp [pow_succ]
      simp only [natPowerOfTwoFuel, hne0, hne1, beq_iff_eq, ↓reduceIte, hmod, hdiv]
      exact ih fuel (by omega)

theorem powerOfTwo_accepts (e : Nat) : natPowerOfTwo? (2^e) = true := by
  exact powerOfTwoFuel_accepts e (2^e) (Nat.le_of_lt e.lt_two_pow_self)

theorem signedPowerOfTwo_accepts (e : Nat) :
    signedPowerOfTwo? ((2 : Int)^e) = true ∧
      signedPowerOfTwo? (-((2 : Int)^e)) = true := by
  have hp : (2 : Int)^e ≠ 0 := pow_ne_zero _ (by decide)
  simp [signedPowerOfTwo?, hp, Int.natAbs_pow, powerOfTwo_accepts]

theorem canonicalPoint_valid (n : Nat) : validPoint? (canonicalPoint n) = true := by
  by_cases hn : n < 4
  · interval_cases n <;> decide
  · have he : n = (n-4)+4 := by omega
    rw [he]
    have hb : (n-4) % 4 < 4 := Nat.mod_lt _ (by decide)
    have hp := signedPowerOfTwo_accepts (1+(n-4)/4)
    interval_cases hm : (n-4) % 4 <;> simp [canonicalPoint, hm, validPoint?, hp.1, hp.2]

theorem canonicalPoints_valid (mode : ProductMode) (k : Nat) :
    ValidPointList mode k (canonicalPoints mode k) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [canonicalPoints]
  · rw [CanonicalNodes.canonicalPoints_eq_ofFn, List.map_ofFn, List.nodup_ofFn]
    intro i j he
    apply Fin.ext
    apply CanonicalNodes.canonicalPoint_injective
    simpa only [Function.comp_def, CanonicalNodes.normalize_canonicalPoint] using he
  · apply List.all_eq_true.mpr
    intro pt hpt
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hpt
    exact canonicalPoint_valid i

end Paper.CanonicalValidity
