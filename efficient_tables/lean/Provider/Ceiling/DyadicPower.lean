import Provider.Ceiling.Grouped

/-! # Dyadic Power Bounds
Proves `addConstAuxFuel_two_pow`, a power-of-two statement about the fueled constant-addition auxiliary, and the elementary bound `exponent_le_two_pow`. Combines them into `addConstFrom_dyadic`, the dyadic property of `addConstFrom`.
-/

namespace Paper.F3ChargeCeiling

open TableGeneration

theorem addConstAuxFuel_two_pow {k : Nat} (dst src : Fin k) (neg : Bool)
    (e sh fuel : Nat) (hf : e + 1 ≤ fuel) :
    addConstAuxFuel dst src neg fuel (2^e) sh =
      [.addScaled dst src neg (sh + e)] := by
  induction e generalizing sh fuel with
  | zero =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp [addConstAuxFuel]
      cases fuel <;> simp [addConstAuxFuel]
  | succ e ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hf' : e + 1 ≤ fuel := by omega
      have hp : 0 < 2^(e+1) := by positivity
      have hsucc : 2^(e+1) = (2^(e+1)-1)+1 := by omega
      have hdiv : 2^(e+1)/2 = 2^e := by rw [pow_succ]; omega
      have hmod : 2^(e+1)%2 = 0 := by rw [pow_succ]; omega
      rw [hsucc]
      simp only [addConstAuxFuel]
      rw [← hsucc, hdiv, hmod]
      simp [ih sh.succ fuel hf', Nat.add_comm, Nat.add_left_comm]

theorem exponent_le_two_pow (e : Nat) : e ≤ 2^e := by
  induction e with
  | zero => simp
  | succ e ih =>
    have hpos : 0 < 2^e := by positivity
    rw [pow_succ]
    omega

theorem addConstFrom_dyadic {k : Nat} (dst src : Fin k)
    (c : Int) (e : Nat) (habs : c.natAbs = 2^e) :
    addConstFrom dst src c = [.addScaled dst src (decide (c < 0)) e] := by
  have hc : c ≠ 0 := by
    intro h
    subst c
    have hp : 0 < 2^e := by positivity
    omega
  unfold addConstFrom
  rw [if_neg hc, habs]
  simpa only [Nat.zero_add] using addConstAuxFuel_two_pow dst src (decide (c < 0)) e 0 (2^e+1)
    (Nat.add_le_add_right (exponent_le_two_pow e) 1)

end Paper.F3ChargeCeiling
