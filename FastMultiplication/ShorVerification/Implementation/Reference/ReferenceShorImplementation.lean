import FastMultiplication.ShorVerification.Implementation.Reference.ShorProgram
import FastMultiplication.ShorVerification.Implementation.Shor.Main
import FastMultiplication.ShorVerification.Framework.Submission

namespace Shor

namespace Reference

noncomputable section

/-!
# Reference `ShorImplementation`

This file packages the reference approximate Shor construction into the
framework's `ShorImplementation` interface.

For each approximation level `m`, we first define the corresponding program,
certified single-run success lower bound, and gate count. The final submission
then chooses `m` internally as a function of the modulus.
-/

variable {qs : QSemantics}

variable [RegEncoding qs.Basis]
variable [MeasureClass qs]
variable [GateSemanticsFacts qs]
variable [LowerGateClass qs]
variable [IdealCtrlModMulExactSemantics qs]


/-! =========================================================
    Section 1: Uniform approximation constant
========================================================= -/

/--
Uniform constant controlling the modular-exponentiation approximation error.

Unlike an arbitrary `Classical.choose` witness, this is a concrete numeral:
`modExpApprox_valid_dist_uniform` proves a uniform constant `K ≤ 2048` works
(traced from `Cpe = 512` and `Cstep2 = 2π + 2π²` in the Algorithm-1 error
bounds), so `2048` itself is a valid, and clean, choice of constant. -/
noncomputable def referenceK : ℝ := 2048

omit [MeasureClass qs] [LowerGateClass qs] in
theorem referenceK_nonneg :
    0 ≤ referenceK := by
  norm_num [referenceK]

omit [MeasureClass qs] [LowerGateClass qs] in
theorem referenceK_modExp_bound :
    ∀ (η : ℝ) (cfg : ModExpConfig η) (ψ : qs.State),
      ModExpConfig.ValidUnitState qs cfg ψ →
      ‖qs.eval (ModExpConfig.approxGate (Basis := qs.Basis) cfg) ψ -
          qs.eval (ModExpConfig.idealGate qs cfg) ψ‖
        ≤ (tbits cfg.x : ℝ) * stepErr (referenceK) η := by
  obtain ⟨K, hK_nonneg, hK_le, hbound⟩ :=
    modExpApprox_valid_dist_uniform (qs := qs)
  intro η cfg ψ hψ
  have hη : 0 ≤ η := le_of_lt cfg.env.precision.1
  have hstep_mono : stepErr K η ≤ stepErr (referenceK) η := by
    unfold stepErr referenceK
    apply Real.sqrt_le_sqrt
    nlinarith [hK_le, hη]
  calc
    ‖qs.eval (ModExpConfig.approxGate (Basis := qs.Basis) cfg) ψ -
        qs.eval (ModExpConfig.idealGate qs cfg) ψ‖
      ≤ (tbits cfg.x : ℝ) * stepErr K η := hbound η cfg ψ hψ
    _ ≤ (tbits cfg.x : ℝ) * stepErr (referenceK) η :=
      mul_le_mul_of_nonneg_left hstep_mono (by positivity)


/-! =========================================================
    Section 2: Reference program at fixed approximation `m`
========================================================= -/

/-- Reference order-finding program at approximation level `m`. -/
noncomputable def referenceProgramAt
    (lowering : ShorLoweringSetup) (m : ℕ) (inst : ShorOrderFindingInstance) :
    ShorOrderFindingProgram :=
  referenceShorProg (qs := qs) lowering inst m

/-- Approximation error appearing in the reference correctness bound. -/
noncomputable def referenceApproximationErrorAt (m N : ℕ) : ℝ :=
  2 *
    (tbits (Reg.interval 0 (Nat.log2 (2 * N ^ 2))) : ℝ) *
    Real.sqrt (2 * (referenceK * referencePrecision m))

/-- Raw analytical single-run success lower bound at approximation level `m`. -/
noncomputable def referenceRawSuccessProbabilityAt (m N : ℕ) : ℝ :=
  κ / (Nat.log2 N : ℝ) ^ 4 -
    referenceApproximationErrorAt m N

/-- Declared probability bound at `m`, clamped to `[0,1]`. -/
noncomputable def referenceSuccessProbabilityAt (m N : ℕ) : ℝ :=
  max 0 (min 1 (referenceRawSuccessProbabilityAt m N))

omit [MeasureClass qs] [LowerGateClass qs] in
theorem referenceSuccessProbabilityAt_bounds (m N : ℕ) :
    0 ≤ referenceSuccessProbabilityAt m N ∧
      referenceSuccessProbabilityAt m N ≤ 1 := by
  simp [referenceSuccessProbabilityAt]

/-- Every fixed-`m` reference program achieves its declared success bound. -/
theorem referenceProgramAt_success
    (lowering : ShorLoweringSetup) (m : ℕ) :
    ∀ (T : ℕ → ℕ), ContinuedFractionSearchComplete T →
    ∀ inst : ShorOrderFindingInstance,
      referenceSuccessProbabilityAt m inst.N ≤
        probability_of_success
          (qs := qs)
          (evalC := LowerGateClass.evalL (qs := qs))
          (T := T)
          (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
          (x := (referenceProgramAt (qs := qs) lowering m inst).output)
          (r := ord inst.a inst.N inst.coprime)
          (Q := ASize (referenceProgramAt (qs := qs) lowering m inst).output)
          (C := (referenceProgramAt (qs := qs) lowering m inst).circuit)
          (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis))) := by
  intro T hT inst

  let η : ℝ := referencePrecision m
  let layout := allocateReferenceLayout lowering.ops inst η

  have hηpos : 0 < η := by
    simpa [η] using referencePrecision_pos m

  have hηhalf : η < (1 / 2 : ℝ) := by
    simpa [η] using referencePrecision_lt_half m

  let hready :=
    referenceLayout_ready (qs := qs) lowering inst η hηpos hηhalf

  have hxwidth :
      regSize layout.x.active = Nat.log2 (2 * inst.N^2) := by
    simpa [layout] using
      allocateReferenceLayout_x_width lowering.ops inst η

  have hywidth :
      regSize layout.data.active = Nat.log2 (2 * inst.N) := by
    simp[layout]

  have hb :=
    Shor_correct_approx_lowered_of_modExp_bound
      (qs := qs)
      (referenceK)
      (referenceK_modExp_bound (qs := qs))
      T hT
      inst lowering
      layout.x layout.data layout.work layout.scratch layout.flag
      (RegEncoding.zero (Basis := qs.Basis))
      hxwidth hywidth η hready

  have hraw :
      referenceRawSuccessProbabilityAt m inst.N ≤
        probability_of_success
          (qs := qs)
          (evalC := LowerGateClass.evalL (qs := qs))
          (T := T)
          (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
          (x := (referenceProgramAt (qs := qs) lowering m inst).output)
          (r := ord inst.a inst.N inst.coprime)
          (Q := ASize (referenceProgramAt (qs := qs) lowering m inst).output)
          (C := (referenceProgramAt (qs := qs) lowering m inst).circuit)
          (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis))) := by
    simpa [
      referenceProgramAt,
      referenceShorProg,
      referenceShorCircuit,
      referenceRawSuccessProbabilityAt,
      referenceApproximationErrorAt,
      referenceXActive,
      referenceXWidth,
      layout,
      η,
      hready,
      referenceLowerWorkspace,
      referenceApproxSetup,
      referenceMinimalSetup,
      referenceLayout_ready
    ] using hb

  have hprob_nonneg :
      0 ≤
        probability_of_success
          (qs := qs)
          (evalC := LowerGateClass.evalL (qs := qs))
          (T := T)
          (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
          (x := (referenceProgramAt (qs := qs) lowering m inst).output)
          (r := ord inst.a inst.N inst.coprime)
          (Q := ASize (referenceProgramAt (qs := qs) lowering m inst).output)
          (C := (referenceProgramAt (qs := qs) lowering m inst).circuit)
          (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis))) := by
    unfold probability_of_success
    apply Finset.sum_nonneg
    intro o _
    by_cases h :
        OF_post
            (T := T)
            (fun d => decide ((inst.a ^ d) % inst.N = 1))
            o.1
            (ASize (referenceProgramAt (qs := qs) lowering m inst).output)
          =
        ord inst.a inst.N inst.coprime
    · simp [r_found, h, MeasureClass.probMeas]
    · simp [r_found, h]

  rw [referenceSuccessProbabilityAt]
  exact max_le hprob_nonneg
    (le_trans (min_le_right 1 _) hraw)


/-! =========================================================
    Section 3: Internal approximation choice
========================================================= -/

theorem exists_precision_error_le
    (t : ℕ) (K : ℝ) (_hK : 0 ≤ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ,
      2 * (t : ℝ) *
        Real.sqrt (2 * (K * referencePrecision m)) ≤ ε := by
  have hden : (0 : ℝ) < 2 * (t : ℝ) + 1 := by
    positivity

  let D : ℝ := ε / (2 * (t : ℝ) + 1)

  have hD : 0 < D := by
    dsimp [D]
    positivity

  have hDsq : 0 < D ^ 2 := by
    positivity

  obtain ⟨m, hm⟩ := exists_nat_ge (2 * K / D ^ 2)

  refine ⟨m, ?_⟩

  have hm3 : (0 : ℝ) < (m : ℝ) + 3 := by
    positivity

  have herror :
      2 * (K * referencePrecision m) ≤ D ^ 2 := by
    have hrewrite :
        2 * (K * referencePrecision m) =
          2 * K / ((m : ℝ) + 3) := by
      unfold referencePrecision
      field_simp

    rw [hrewrite, div_le_iff₀ hm3]

    have hle :
        2 * K / D ^ 2 ≤ (m : ℝ) + 3 := by
      calc
        2 * K / D ^ 2 ≤ (m : ℝ) := hm
        _ ≤ (m : ℝ) + 3 := by linarith

    rw [div_le_iff₀ hDsq] at hle
    nlinarith

  have hsqrt :
      Real.sqrt (2 * (K * referencePrecision m)) ≤ D := by
    calc
      Real.sqrt (2 * (K * referencePrecision m))
          ≤ Real.sqrt (D ^ 2) :=
        Real.sqrt_le_sqrt herror
      _ = D := Real.sqrt_sq hD.le

  calc
    2 * (t : ℝ) *
          Real.sqrt (2 * (K * referencePrecision m))
        ≤ 2 * (t : ℝ) * D := by
          exact mul_le_mul_of_nonneg_left hsqrt (by positivity)

    _ ≤ ε := by
      dsimp [D]
      rw [mul_div_assoc', div_le_iff₀ hden]
      nlinarith [hε]

omit [MeasureClass qs] [LowerGateClass qs] in
/-- Some approximation level has strictly positive certified success. -/
theorem exists_reference_positive_precision
    (N : ℕ) (hN : 2 ≤ N) :
    ∃ m : ℕ, 0 < referenceSuccessProbabilityAt m N := by
  have hlogNat : 0 < Nat.log2 N := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_pos Nat.one_lt_two hN

  have hlog : (0 : ℝ) < Nat.log2 N := by
    exact_mod_cast hlogNat

  have hκ : 0 < κ := by
    unfold κ
    positivity

  have hideal : 0 < κ / (Nat.log2 N : ℝ) ^ 4 := by
    positivity

  obtain ⟨m, hm⟩ :=
    exists_precision_error_le
      (tbits (Reg.interval 0 (Nat.log2 (2 * N ^ 2))))
      (referenceK)
      referenceK_nonneg
      (ε := κ / (Nat.log2 N : ℝ) ^ 4 / 2)
      (by positivity)

  refine ⟨m, ?_⟩

  have herr :
      referenceApproximationErrorAt m N ≤
        κ / (Nat.log2 N : ℝ) ^ 4 / 2 := by
    simpa [referenceApproximationErrorAt] using hm

  have hraw :
      0 < referenceRawSuccessProbabilityAt m N := by
    rw [referenceRawSuccessProbabilityAt]
    linarith

  have hmin :
      0 < min 1 (referenceRawSuccessProbabilityAt m N) := by
    exact lt_min (by norm_num) hraw

  rw [referenceSuccessProbabilityAt, max_eq_right hmin.le]
  exact hmin
/-- Approximation level chosen internally by the reference submission. -/
noncomputable def referenceChosenPrecision (N : ℕ) : ℕ :=
  if hN : 2 ≤ N then
    Nat.find (exists_reference_positive_precision N hN)
  else
    0

omit [MeasureClass qs] [LowerGateClass qs] in
theorem referenceChosenPrecision_positive
    (N : ℕ) (hN : 2 ≤ N) :
    0 <
      referenceSuccessProbabilityAt
        (referenceChosenPrecision N) N := by
  rw [referenceChosenPrecision, dif_pos hN]
  exact Nat.find_spec
    (exists_reference_positive_precision N hN)


/-! =========================================================
    Section 4: Framework-facing program and success bound
========================================================= -/

/-- Final submitted program, with approximation precision chosen internally. -/
noncomputable def referenceSubmittedProgram
    (lowering : ShorLoweringSetup) (inst : ShorOrderFindingInstance) :
    ShorOrderFindingProgram :=
  referenceProgramAt (qs := qs) lowering
    (referenceChosenPrecision inst.N) inst

/-- Final single-run success probability declared by the reference submission. -/
noncomputable def referenceSuccessProbability (N : ℕ) : ℝ :=
  if 2 ≤ N then
    referenceSuccessProbabilityAt
      (referenceChosenPrecision N) N
  else
    1

omit [MeasureClass qs] [LowerGateClass qs] in
theorem referenceSuccessProbability_bounds (N : ℕ) :
    0 ≤ referenceSuccessProbability N ∧
      referenceSuccessProbability N ≤ 1 := by
  by_cases hN : 2 ≤ N
  · simpa [referenceSuccessProbability, hN] using
      referenceSuccessProbabilityAt_bounds
        (referenceChosenPrecision N)
        N
  · simp [referenceSuccessProbability, hN]

omit [MeasureClass qs] [LowerGateClass qs] in
theorem referenceSuccessProbability_pos (N : ℕ) :
    0 < referenceSuccessProbability N := by
  by_cases hN : 2 ≤ N
  · simpa [referenceSuccessProbability, hN] using
      referenceChosenPrecision_positive N hN
  · simp [referenceSuccessProbability, hN]

/-- The final submitted program satisfies its declared single-run success bound. -/
theorem referenceSubmittedProgram_correct
    (lowering : ShorLoweringSetup) :
    ∀ (T : ℕ → ℕ), ContinuedFractionSearchComplete T →
    ∀ inst : ShorOrderFindingInstance,
      0 ≤ referenceSuccessProbability inst.N ∧
      referenceSuccessProbability inst.N ≤ 1 ∧
      referenceSuccessProbability inst.N ≤
        probability_of_success
          (qs := qs)
          (evalC := LowerGateClass.evalL (qs := qs))
          (T := T)
          (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
          (x := (referenceSubmittedProgram (qs := qs) lowering inst).output)
          (r := ord inst.a inst.N inst.coprime)
          (Q := ASize (referenceSubmittedProgram (qs := qs) lowering inst).output)
          (C := (referenceSubmittedProgram (qs := qs) lowering inst).circuit)
          (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis))) := by
  intro T hT inst

  have hN : 2 ≤ inst.N := by
    have hr:=inst.range
    omega

  have hbounds :=
    referenceSuccessProbability_bounds inst.N

  refine ⟨hbounds.1, hbounds.2, ?_⟩

  simpa [referenceSuccessProbability, hN, referenceSubmittedProgram] using
    (referenceProgramAt_success
      (qs := qs)
      lowering
      (referenceChosenPrecision inst.N)
      T hT inst)


/-! =========================================================
    Section 5: Trial amplification
========================================================= -/

omit [MeasureClass qs] [LowerGateClass qs] in
theorem exists_reference_trialCount (N : ℕ) :
    ∃ k : ℕ,
      (99 / 100 : ℝ) ≤
        1 - (1 - referenceSuccessProbability N) ^ k := by
  let p := referenceSuccessProbability N

  have hp : 0 < p := by
    simpa [p] using referenceSuccessProbability_pos N

  have hlt : 1 - p < (1 : ℝ) := by
    linarith

  obtain ⟨k, hk⟩ :=
    exists_pow_lt_of_lt_one
      (K := ℝ)
      (x := (1 / 100 : ℝ))
      (y := 1 - p)
      (by norm_num)
      hlt

  refine ⟨k, ?_⟩
  change (99 / 100 : ℝ) ≤ 1 - (1 - p) ^ k
  linarith

/-- Number of independent trials declared by the reference submission. -/
noncomputable def referenceTrialCount (N : ℕ) : ℕ :=
  Nat.find (exists_reference_trialCount N)

omit [MeasureClass qs] [LowerGateClass qs] in
theorem referenceTrialCount_correct (N : ℕ) :
    (99 / 100 : ℝ) ≤
      1 -
        (1 - referenceSuccessProbability N) ^
          referenceTrialCount N := by
  simpa [referenceTrialCount] using
    Nat.find_spec (exists_reference_trialCount N)


/-! =========================================================
    Section 6: Concrete `ShorImplementation`
========================================================= -/

/--
Declared logical gate count of the submitted single-run circuit.

The codebase's gate-count layer (`Shor_GateCount.lean`) currently only proves
*asymptotic* bounds on `LowGate.gateCount shorGateCostModel (...)` with
unnamed existential constants (`ShorGateCountBound` and friends) — there is no
closed-form formula for this quantity in terms of `η`/register widths/`k`
anywhere in the codebase. The framework's `gateCount_correct` obligation only
asks that the *declared* value equal the *actual* count of the *submitted*
circuit, so the honest and provable choice is to declare exactly that count.
-/
noncomputable def referenceGateCount
    (lowering : ShorLoweringSetup) (inst : ShorOrderFindingInstance) : ℕ :=
  LowGate.gateCount shorGateCostModel
    (referenceSubmittedProgram (qs := qs) lowering inst).circuit

omit [MeasureClass qs] [GateSemanticsFacts qs] [LowerGateClass qs]
  [IdealCtrlModMulExactSemantics qs] in
theorem referenceGateCount_correct
    (lowering : ShorLoweringSetup) (inst : ShorOrderFindingInstance) :
    LowGate.gateCount shorGateCostModel
        (referenceSubmittedProgram (qs := qs) lowering inst).circuit =
      referenceGateCount (qs := qs) lowering inst :=
  rfl

/-- Reference implementation packaged into the public submission interface. -/
noncomputable def referenceShorImplementation
    (lowering : ShorLoweringSetup) :
    ShorImplementation (qs := qs) where
  program := referenceSubmittedProgram (qs := qs) lowering
  successProbability := referenceSuccessProbability
  correct := referenceSubmittedProgram_correct (qs := qs) lowering
  trialCount := referenceTrialCount
  trialCount_correct := by
    intro N h
    apply referenceTrialCount_correct

end

end Reference

end Shor
