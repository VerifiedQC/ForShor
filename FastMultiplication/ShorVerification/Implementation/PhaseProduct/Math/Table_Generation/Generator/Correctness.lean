import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Generator.WellFormed
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Core.Coverage

open Operations

namespace Table_Generation

private lemma start_matches_int_zero {k : ℕ} (hk : k > 0) :
    matchesAt_pointRow_state (k := k) hk State.start_state
      (finZero hk) (.int 0) = true := by
  unfold matchesAt_pointRow_state regEqExpected
  apply List.all_eq_true.mpr
  intro j _
  apply decide_eq_true_iff.mpr
  by_cases hj : j = finZero hk
  · subst j
    change (if finZero hk = finZero hk then 1 else 0) = (0 : ℤ) ^ 0
    simp
  · have hjval : j.val ≠ 0 := by
      intro hzero
      apply hj
      apply Fin.ext
      simpa [finZero] using hzero
    have hjpos : 0 < j.val := Nat.pos_of_ne_zero hjval
    change (if j = finZero hk then 1 else 0) = (0 : ℤ) ^ j.val
    rw [if_neg hj, zero_pow (Nat.ne_of_gt hjpos)]

private lemma replicate_phaseProduct_consumes_int_zero
    {k : ℕ} (hk : k > 0) (n : ℕ) :
    ProgConsumesPts hk State.start_state
      (List.replicate n (valid_ops.phaseProduct (finZero hk)))
      (List.replicate n (.int 0)) := by
  induction n with
  | zero =>
      simp [ProgConsumesPts]
  | succ n ih =>
      simp [List.replicate_succ, ProgConsumesPts, start_matches_int_zero, ih]

/- The generated point list has the expected length and allowed point shapes. -/
theorem generatedPoints_valid (mode : ProductMode) (k : ℕ) (_ : k ≥ 2) :
    ValidPointList mode k (generatedPoints mode k) := by
  constructor
  · simp [generatedPoints]
  · intro p hp
    have hpzero : p = .int 0 := List.eq_of_mem_replicate hp
    subst p
    simp [AllowedPoint]

/- The generated program safely consumes the expected points in order. -/
theorem generate_ProgConsumesPtsSafe (mode : ProductMode) (k : ℕ) (hk : k ≥ 2) :
    ProgConsumesPtsSafe (by omega) State.start_state
      (generate mode k hk) (generatePointsInOrder mode k hk) := by
  constructor
  · simpa [generate, generatePointsInOrder, generatedPoints] using
      replicate_phaseProduct_consumes_int_zero
        (k := k) (by omega) (ProductMode.pointCount mode k)
  · intro pre rest d s negSrc sh hops
    have hmem : valid_ops.addScaled d s negSrc sh ∈ generate mode k hk := by
      rw [hops]
      simp
    simp [generate] at hmem

end Table_Generation
