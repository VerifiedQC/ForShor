import FastMultiplication.ShorVerification.Submission.Correct

/-!
# The scored quantities, fixed once for every submission

`SUBMISSION_PLAN.md` S3. Decision P4 makes the leaderboard score
`trialCount N × (Qualtran's gate count for the emitted IR)`. The gate count
is measured outside Lean, on the IR `Emit/` produces. The *trial count* is
not measured at all: it follows from the declared single-run success bound,
which by P3 is fixed at one precision `submissionPrecision` for everybody.
So both factors of the score are settled here, once, and neither is something
a submitter can influence:

- `submissionSuccessBound N` is `referenceSuccessProbabilityAt` at the fixed
  precision. Its definition takes a modulus and nothing else — there is no
  submission argument to pass — so every accepted table declares the same
  bound at the same `N`.
- `submissionTrialCount N` is a computable `ℕ`, not the `Nat.find` witness
  `Reference/Reference2048Headline.lean` uses: a submissions repo has to be
  able to *evaluate* it, and `Nat.find` only proves a number exists.

Scope of the trial-count theorem: 2048-bit moduli, the case P3's precision
was chosen for. `submissionTrialCount` is total, but its correctness proof
needs `Is2048Bit N` — that is where the rational lower bound on the success
probability comes from.
-/

namespace Shor

open Reference

/-! =========================================================
    S3.1: the declared single-run success bound
========================================================= -/

/-- The single-run success probability every submission declares, at the one
precision the organiser fixed (P3).

**Independent of the submission**, in the strongest sense available: the
right-hand side mentions no `ShorSubmission`, so there is nothing for a
submitter to vary. `submissionSuccessBound_le_success` below is
`submission_correct` with this name in place of the expanded expression,
which is the form a leaderboard should cite. -/
noncomputable def submissionSuccessBound (N : ℕ) : ℝ :=
  referenceSuccessProbabilityAt submissionPrecision N

theorem submissionSuccessBound_bounds (N : ℕ) :
    0 ≤ submissionSuccessBound N ∧ submissionSuccessBound N ≤ 1 :=
  referenceSuccessProbabilityAt_bounds submissionPrecision N

theorem submissionSuccessBound_nonneg (N : ℕ) : 0 ≤ submissionSuccessBound N :=
  (submissionSuccessBound_bounds N).1

theorem submissionSuccessBound_le_one (N : ℕ) : submissionSuccessBound N ≤ 1 :=
  (submissionSuccessBound_bounds N).2

section Certificate

variable {qs : QSemantics}
variable [RegEncoding qs.Basis]
variable [MeasureClass qs]
variable [GateSemanticsFacts qs]
variable [LowerGateClass qs]
variable [IdealCtrlModMulExactSemantics qs]

/-- `submission_correct` (S2.2) with the declared bound named. Note where `s`
occurs: only on the right. Whatever table a submitter hands in, the number it
is held to is `submissionSuccessBound inst.N`. -/
theorem submissionSuccessBound_le_success (s : ShorSubmission) :
    ∀ (T : ℕ → ℕ), ContinuedFractionSearchComplete T →
    ∀ inst : ShorOrderFindingInstance,
      submissionSuccessBound inst.N ≤
        probability_of_success
          (qs := qs)
          (evalC := LowerGateClass.evalL (qs := qs))
          (T := T)
          (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
          (x := (referenceProgramAt s submissionPrecision inst).output)
          (r := ord inst.a inst.N inst.coprime)
          (Q := ASize (referenceProgramAt s submissionPrecision inst).output)
          (C := (referenceProgramAt s submissionPrecision inst).circuit)
          (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis))) :=
  submission_correct (qs := qs) s

end Certificate

/-! =========================================================
    S3.2: a computable trial count
========================================================= -/

/-- A rational lower bound on `submissionSuccessBound N` for 2048-bit `N`
(`pLower_le_bound`), obtained by composing the two facts
`Reference/Reference2048Headline.lean` already proves: at
`submissionPrecision` the declared bound retains at least 99% of the ideal
`κ / (log₂ N)⁴ = κ / 2047⁴` baseline (`headline_success_bound`), and
`1/25 ≤ κ` (`kappa_ge_one_div_25`).

Rational, not real, so that `submissionTrialCount` below is a number the
submissions repo can evaluate rather than a `Nat.find` witness. It takes `N`
because that is the shape the rest of the scoring API has and because a
sharper, genuinely `N`-dependent bound could replace it later; at present the
value is the same for every 2048-bit modulus, since `log₂ N = 2047`
throughout that range. -/
def pLower (_N : ℕ) : ℚ := 99 / (2500 * 2047 ^ 4)

theorem pLower_pos (N : ℕ) : 0 < pLower N := by
  unfold pLower; norm_num

theorem pLower_lt_one (N : ℕ) : pLower N < 1 := by
  unfold pLower; norm_num

theorem pLower_le_bound {N : ℕ} (hN : Is2048Bit N) :
    (pLower N : ℝ) ≤ submissionSuccessBound N := by
  have hbase : (99 / 100 : ℝ) * (κ / (2047 : ℝ) ^ 4) ≤ submissionSuccessBound N :=
    headline_success_bound hN
  have hpow : (0 : ℝ) < (2047 : ℝ) ^ 4 := by positivity
  have hκ : (1 : ℝ) / 25 ≤ κ := kappa_ge_one_div_25
  have hstep : (99 / 100 : ℝ) * (((1 : ℝ) / 25) / (2047 : ℝ) ^ 4)
      ≤ (99 / 100 : ℝ) * (κ / (2047 : ℝ) ^ 4) := by
    gcongr
  have hcast : ((pLower N : ℚ) : ℝ) = (99 / 100 : ℝ) * (((1 : ℝ) / 25) / (2047 : ℝ) ^ 4) := by
    unfold pLower; push_cast; ring
  rw [hcast]
  linarith

/-- The 2048-bit benchmark predicate is spelled twice in this repository —
`Reference.Is2048Bit` (used by `headline_success_bound`, and so by everything
in this file) and `Shor.Is2048Bit` (used by
`ShorImplementation.trialCount_correct`, `Framework/Contract.lean`). They are
the same `2 ^ 2047 ≤ N ∧ N < 2 ^ 2048`, definitionally, so either theorem
feeds the other without a transport. Recorded here rather than left for a
reader of the scoring API to rediscover. -/
theorem reference_is2048Bit_eq (N : ℕ) : Reference.Is2048Bit N = Is2048Bit N := rfl

/-- The number of independent runs the score is computed over: the smallest
`t` with `pLower N * t ≥ 5`, and `5 > log 100`, so `t` runs amplify the
declared single-run bound past 99% overall (`submissionTrialCount_correct`).

Computable, unlike `Reference.headlineTrialCount` (a `Nat.find` witness), and
the same number for every submission at a given `N` — published once, not
recomputed per pull request. It is large (`≈ 2.2 · 10¹⁵` at 2048 bits)
because the single-run baseline `κ / (log₂ N)⁴` it amplifies is itself weak;
that is a property of the correctness bound this repository proves, not of
any particular table. -/
def submissionTrialCount (N : ℕ) : ℕ := ⌈(5 : ℚ) / pLower N⌉₊

theorem five_le_pLower_mul_trialCount (N : ℕ) :
    (5 : ℝ) ≤ (pLower N : ℝ) * submissionTrialCount N := by
  have hpos : (0 : ℚ) < pLower N := pLower_pos N
  have hceil : (5 : ℚ) / pLower N ≤ (submissionTrialCount N : ℚ) := Nat.le_ceil _
  have hq : (5 : ℚ) ≤ pLower N * submissionTrialCount N := by
    rw [mul_comm]
    exact (div_le_iff₀ hpos).mp hceil
  exact_mod_cast hq

/-- `100 ≤ e⁵`, i.e. `log 100 < 5` — the only analytic input to the trial
count, and the reason `5` is the constant in `submissionTrialCount`. -/
theorem hundred_le_exp_five : (100 : ℝ) ≤ Real.exp 5 := by
  have h27 : (2.7 : ℝ) ≤ Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  have hpow : (2.7 : ℝ) ^ (5 : ℕ) ≤ Real.exp 1 ^ (5 : ℕ) := by
    gcongr
  have hexp : Real.exp 1 ^ (5 : ℕ) = Real.exp 5 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [← hexp]
  calc (100 : ℝ) ≤ (2.7 : ℝ) ^ (5 : ℕ) := by norm_num
    _ ≤ Real.exp 1 ^ (5 : ℕ) := hpow

theorem exp_neg_five_le : Real.exp (-5) ≤ 1 / 100 := by
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 5) (by norm_num)]
  simpa using hundred_le_exp_five

/-- **The trial count is enough.** Running an accepted submission's circuit
`submissionTrialCount N` times independently succeeds with probability at
least 99%, for every 2048-bit modulus.

The argument is the standard one, with no slack worth tightening: the
declared bound `p` is at least the rational `c = pLower N`, so the failure
probability per run is at most `1 - c ≤ exp (-c)`; over `t` runs that is
`exp (-c·t) ≤ exp (-5) ≤ 1/100`, because `t = ⌈5/c⌉₊` gives `c·t ≥ 5` and
`5 > log 100`. -/
theorem submissionTrialCount_correct {N : ℕ} (hN : Is2048Bit N) :
    (99 / 100 : ℝ) ≤ 1 - (1 - submissionSuccessBound N) ^ submissionTrialCount N := by
  set c : ℝ := (pLower N : ℝ) with hc
  set p : ℝ := submissionSuccessBound N with hp
  set t : ℕ := submissionTrialCount N with ht
  have hc_pos : 0 < c := by rw [hc]; exact_mod_cast pLower_pos N
  have hc_lt_one : c < 1 := by rw [hc]; exact_mod_cast pLower_lt_one N
  have hcp : c ≤ p := pLower_le_bound hN
  have hp1 : p ≤ 1 := submissionSuccessBound_le_one N
  -- `(1 - p) ^ t ≤ (1 - c) ^ t`
  have hfail_nonneg : (0 : ℝ) ≤ 1 - p := by linarith
  have hstep1 : (1 - p) ^ t ≤ (1 - c) ^ t := by gcongr
  -- `(1 - c) ^ t ≤ exp (-c) ^ t = exp (-(c * t))`
  have hc_nonneg : (0 : ℝ) ≤ 1 - c := by linarith
  have hexp1 : 1 - c ≤ Real.exp (-c) := by
    have := Real.add_one_le_exp (-c)
    linarith
  have hstep2 : (1 - c) ^ t ≤ Real.exp (-c) ^ t := by gcongr
  have hpow : Real.exp (-c) ^ t = Real.exp (-(c * t)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  -- `exp (-(c * t)) ≤ exp (-5) ≤ 1/100`
  have hct : (5 : ℝ) ≤ c * t := five_le_pLower_mul_trialCount N
  have hstep3 : Real.exp (-(c * t)) ≤ Real.exp (-5) :=
    Real.exp_le_exp.mpr (by linarith)
  have hfinal : (1 - p) ^ t ≤ 1 / 100 := by
    calc (1 - p) ^ t ≤ (1 - c) ^ t := hstep1
      _ ≤ Real.exp (-c) ^ t := hstep2
      _ = Real.exp (-(c * t)) := hpow
      _ ≤ Real.exp (-5) := hstep3
      _ ≤ 1 / 100 := exp_neg_five_le
  linarith

end Shor
