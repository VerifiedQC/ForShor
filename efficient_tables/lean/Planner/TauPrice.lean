import Planner.PolicyOptimality

/-!
# Exact integer form of the rotation price

Defines `tauExact`, an executable integer form of the stipulated rounded real rotation price. Proves it agrees with the accepted real-valued price at every input (`tauRS_eq_tauExact`), that substituting it leaves the formal recursive problem unchanged (`ppProblem_tauRS_eq_tauExact`), and defines the concrete selector `selectExactPP` at this price.
-/

namespace Paper.PPEndToEnd

/-- Executable integer form of the stipulated rounded real rotation price. -/
def tauExact (R : Nat) : Nat :=
  if R = 0 then 1 else (Nat.log2 ((100 * R) ^ 615) + 272) / 200

theorem logb_pow_bracket (n : Nat) (hn : 0 < n) :
    (Nat.log2 (n ^ 615) : Real) ≤ Real.logb 2 ((n : Real) ^ 615) ∧
      Real.logb 2 ((n : Real) ^ 615) < (Nat.log2 (n ^ 615) : Real) + 1 := by
  have hp : 0 < n ^ 615 := Nat.pow_pos hn
  have hn0 : n ^ 615 ≠ 0 := Nat.ne_of_gt hp
  have hlo : 2 ^ Nat.log2 (n ^ 615) ≤ n ^ 615 := by
    rw [Nat.log2_eq_log_two]
    exact Nat.pow_log_le_self 2 hn0
  have hhi : n ^ 615 < 2 ^ (Nat.log2 (n ^ 615) + 1) := by
    rw [Nat.log2_eq_log_two]
    exact Nat.lt_pow_succ_log_self Nat.one_lt_two (n ^ 615)
  have hloR : (2 : Real) ^ Nat.log2 (n ^ 615) ≤ ((n ^ 615 : Nat) : Real) := by exact_mod_cast hlo
  have hhiR : ((n ^ 615 : Nat) : Real) < (2 : Real) ^ (Nat.log2 (n ^ 615) + 1) := by exact_mod_cast hhi
  have hpow : ((n ^ 615 : Nat) : Real) = (n : Real) ^ 615 := by norm_cast
  have hlowLog := (Real.logb_le_logb (by norm_num : (1 : Real) < 2)
      (by positivity : 0 < (2 : Real) ^ Nat.log2 (n ^ 615))
      (by positivity : 0 < (n : Real) ^ 615)).2 (by simpa [hpow] using hloR)
  have hhighLog := (Real.logb_lt_logb_iff (by norm_num : (1 : Real) < 2)
      (by positivity : 0 < (n : Real) ^ 615)
      (by positivity : 0 < (2 : Real) ^ (Nat.log2 (n ^ 615) + 1))).2
      (by simpa [hpow] using hhiR)
  have heq : Real.logb 2 ((2 : Real) ^ Nat.log2 (n ^ 615)) = (Nat.log2 (n ^ 615) : Real) := by
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : Real) < 2)]
    simp
  have heq' : Real.logb 2 ((2 : Real) ^ (Nat.log2 (n ^ 615) + 1)) = (Nat.log2 (n ^ 615) : Real) + 1 := by
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : Real) < 2)]
    simp
  constructor
  · rw [← heq]
    exact hlowLog
  · rw [heq'] at hhighLog
    exact hhighLog

/-- The accepted real-valued price equals its exact integer implementation at every input. -/
theorem tauRS_eq_tauExact (R : Nat) : tauRS R = tauExact R := by
  by_cases hR : R = 0
  · subst R
    norm_num [tauRS, tauExact, Real.logb_zero, round]
  · have hRpos : 0 < R := Nat.pos_of_ne_zero hR
    let n := 100 * R
    let e := Nat.log2 (n ^ 615)
    let m := (e + 272) / 200
    have hn : 0 < n := Nat.mul_pos (by decide) hRpos
    have harg : (R : Real) / (1 / 100) = (n : Real) := by
      dsimp [n]
      push_cast
      norm_num [div_eq_mul_inv]
      ring
    have hshift : (3.075 : Real) * Real.logb 2 ((R : Real) / (1 / 100)) + 0.86 + 1 / 2 =
        (Real.logb 2 ((n : Real) ^ 615) + 272) / 200 := by
      rw [harg, Real.logb_pow]
      norm_num
      ring
    have hlog := logb_pow_bracket n hn
    have hlogL : (e : Real) ≤ Real.logb 2 ((n : Real) ^ 615) := by simpa [e] using hlog.1
    have hlogU : Real.logb 2 ((n : Real) ^ 615) < (e : Real) + 1 := by simpa [e] using hlog.2
    have hloN : m * 200 ≤ e + 272 := by
      dsimp [m]
      exact Nat.div_mul_le_self _ _
    have hquot : (e + 272) / 200 < (m + 1) := by
      dsimp [m]
      exact Nat.lt_succ_self _
    have hhiN : e + 272 < (m + 1) * 200 := by
      have hh := (Nat.div_lt_iff_lt_mul (by decide : 0 < 200)).mp hquot
      simpa [Nat.mul_comm] using hh
    have hloR : (m : Real) ≤ (Real.logb 2 ((n : Real) ^ 615) + 272) / 200 := by
      apply (le_div_iff₀ (by norm_num : (0 : Real) < 200)).2
      have hh : (m : Real) * 200 ≤ (e : Real) + 272 := by exact_mod_cast hloN
      linarith
    have hhiR : (Real.logb 2 ((n : Real) ^ 615) + 272) / 200 < (m : Real) + 1 := by
      apply (div_lt_iff₀ (by norm_num : (0 : Real) < 200)).2
      have hhN : e + 273 ≤ (m + 1) * 200 := by omega
      have hhR : (e : Real) + 273 ≤ ((m : Real) + 1) * 200 := by
        push_cast
        exact_mod_cast hhN
      linarith
    have hfloor : Int.floor ((Real.logb 2 ((n : Real) ^ 615) + 272) / 200) = (m : Int) := by
      apply Int.floor_eq_iff.mpr
      exact ⟨by exact_mod_cast hloR, by exact_mod_cast hhiR⟩
    have hround : round ((3.075 : Real) * Real.logb 2 ((R : Real) / (1 / 100)) + 0.86) = (m : Int) := by
      rw [round_eq, hshift, hfloor]
    rw [tauRS, hround, tauExact, if_neg hR]
    rw [Int.toNat_natCast]


/-- Function equality for substitution into higher-order cost and optimizer APIs. -/
theorem tauRS_eq_tauExact_fun : tauRS = tauExact := funext tauRS_eq_tauExact

theorem tauExact_eq_tauRS_fun : tauExact = tauRS := tauRS_eq_tauExact_fun.symm

/-- The formal recursive problem is unchanged by the exact-price replacement. -/
theorem ppProblem_tauRS_eq_tauExact {K : Nat} {ι : Type}
    (entry : ι → VerifiedPPCandidate K) :
    ppProblem tauRS entry = ppProblem tauExact entry := by
  rw [tauRS_eq_tauExact_fun]

/-- Concrete computable finite selector instantiated at the exact integer price. -/
def selectExactPP {ι : Type} [DecidableEq ι] {K : Nat}
    (entry : ι → VerifiedPPCandidate K) (catalog : List ι)
    (width N : Nat) :=
  PolicyOptimality.select (ppProblem tauExact entry) catalog
    (fun c => (entry c).arity) K width N

/-- Expose definitionally that the concrete selector uses its entries' own arities. -/
theorem selectExactPP_eq_select {ι : Type} [DecidableEq ι] {K : Nat}
    (entry : ι → VerifiedPPCandidate K) (catalog : List ι)
    (width N : Nat) :
    selectExactPP entry catalog width N =
      PolicyOptimality.select (ppProblem tauExact entry) catalog
        (fun c => (entry c).arity) K width N := rfl
theorem chosenTrace_tauRS_eq_tauExact {ι : Type} [DecidableEq ι] {K : Nat}
    (entry : ι → VerifiedPPCandidate K) (catalog : List ι)
    (arity : ι → Nat) (width N : Nat) :
    PolicyOptimality.chosenTrace (ppProblem tauRS entry) catalog arity K width N =
      PolicyOptimality.chosenTrace (ppProblem tauExact entry) catalog arity K width N := by
  rw [ppProblem_tauRS_eq_tauExact]

theorem chosenCost_tauRS_eq_tauExact {ι : Type} [DecidableEq ι] {K : Nat}
    (entry : ι → VerifiedPPCandidate K) (catalog : List ι)
    (arity : ι → Nat) (width N : Nat) :
    PolicyOptimality.chosenCost (ppProblem tauRS entry) catalog arity K width N =
      PolicyOptimality.chosenCost (ppProblem tauExact entry) catalog arity K width N := by
  rw [ppProblem_tauRS_eq_tauExact]

theorem benchmarkCost_tauExact_eq_tauRS {K W : Nat}
    (policy : PPPolicy K W) (N : Nat) :
    policy.benchmarkCost tauExact N = policy.benchmarkCost tauRS N := by
  rw [tauExact_eq_tauRS_fun]

end Paper.PPEndToEnd

