import ForShor.ShorVerification.Implementation.Reference.ShorProgram
import ForShor.ShorVerification.Implementation.Reference.Contract
import ForShor.ShorVerification.Implementation.Shor.Main
import ForShor.ShorVerification.Implementation.ModularExponentiation.Main
import ForShor.ShorVerification.Implementation.ModularExponentiation.Spec.Config

namespace Shor

namespace Reference

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


/-! =========================================================
    Section 1: Uniform approximation constant
========================================================= -/

/--
Uniform constant controlling the modular-exponentiation approximation error.

Unlike an arbitrary `Classical.choose` witness, this is a concrete numeral:
`Shor_correct_approx_lowered_uniform` proves the lowered bound for a constant
`K ≤ 1600` (traced from `Cpe ≤ 512` and `Cstep2 ≤ 2π + 2π²` in the Algorithm-1
error bounds, which give `K ≤ 1536 + 3π + 3π² ≈ 1575.03`), so by monotonicity
it holds at `1600` itself.

The bound at this constant is `modExpApprox_correct_1600`
(`ModularExponentiation/Main.lean`). This definition exists because the error
schedule below and `Reference2048Headline.lean` compute with the numeral by
name. -/
noncomputable def referenceK : ℝ := 1600

omit [MeasureClass qs] [LowerGateClass qs] in
theorem referenceK_nonneg :
    0 ≤ referenceK := by
  norm_num [referenceK]

/-! =========================================================
    Section 2: Reference program at fixed approximation `m`
========================================================= -/

/-- Reference order-finding program at approximation level `m`. -/
def referenceProgramAt
    (P : ShorLoweringPolicy) (_hP : P.Admissible) (m : ℕ) (inst : ShorOrderFindingInstance) :
    ShorOrderFindingProgram :=
  referenceShorProg P inst m

/-- Approximation error appearing in the reference correctness bound. -/
noncomputable def referenceApproximationErrorAt (m N : ℕ) : ℝ :=
  2 *
    (regSize (Reg.interval 0 (Nat.log2 (2 * N ^ 2))) : ℝ) *
    Real.sqrt (2 * (referenceK * referencePrecision m))

/-- Raw analytical single-run success lower bound at approximation level `m`. -/
noncomputable def referenceRawSuccessProbabilityAt (m N : ℕ) : ℝ :=
  κ / Real.log ((Nat.log2 N : ℝ) + 1) -
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
    (P : ShorLoweringPolicy) (hP : P.Admissible) (m : ℕ) :
    ∀ (T : ℕ → ℕ), ContinuedFractionSearchComplete T →
    ∀ inst : ShorOrderFindingInstance,
      referenceSuccessProbabilityAt m inst.N ≤
        probability_of_success
          (qs := qs)
          (evalC := LowerGateClass.evalL (qs := qs))
          (T := T)
          (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
          (x := (referenceProgramAt P hP m inst).output)
          (r := ord inst.a inst.N inst.coprime)
          (Q := ASize (referenceProgramAt P hP m inst).output)
          (C := (referenceProgramAt P hP m inst).circuit)
          (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis))) := by
  intro T hT inst

  let η : ℝ := referencePrecision m
  let layout := allocateReferenceLayout P inst m

  let hready :=
    referenceLayout_ready (qs := qs) P inst m

  have hxwidth :
      regSize layout.x.active = Nat.log2 (2 * inst.N^2) := by
    simpa [layout] using
      allocateReferenceLayout_x_width P inst m

  have hywidth :
      regSize layout.data.active = Nat.log2 (2 * inst.N) := by
    simp[layout]

  -- The lowered bound holds at some `K ≤ 1600`; the loss is monotone in `K`.
  obtain ⟨K, _, hK, hunif⟩ := Shor_correct_approx_lowered_uniform (qs := qs) T hT
  have hb0 :=
    hunif inst P hP
      layout.x layout.data layout.work layout.scratch layout.flag
      (RegEncoding.zero (Basis := qs.Basis))
      hxwidth hywidth η hready
      hready.workspace
  have hη : 0 ≤ η := (referencePrecision_pos m).le
  have hloss :
      2 * (regSize layout.x.active : ℝ) * Real.sqrt (2 * (K * η)) ≤
        2 * (regSize layout.x.active : ℝ) * Real.sqrt (2 * (referenceK * η)) := by
    have : K * η ≤ referenceK * η := mul_le_mul_of_nonneg_right hK hη
    gcongr
  have hb := (sub_le_sub_left hloss _).trans hb0

  have hraw :
      referenceRawSuccessProbabilityAt m inst.N ≤
        probability_of_success
          (qs := qs)
          (evalC := LowerGateClass.evalL (qs := qs))
          (T := T)
          (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
          (x := (referenceProgramAt P hP m inst).output)
          (r := ord inst.a inst.N inst.coprime)
          (Q := ASize (referenceProgramAt P hP m inst).output)
          (C := (referenceProgramAt P hP m inst).circuit)
          (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis))) := by
    simpa [
      referenceProgramAt,
      referenceShorProg,
      referenceShorCircuit,
      referenceRawSuccessProbabilityAt,
      referenceApproximationErrorAt,
      referenceK,
      LoweredShorReady.circuit,
      referenceXActive,
      referenceXWidth,
      layout,
      η,
      hready,
      referenceLowerWorkspace,
      referenceApproxSetup,
      referenceMinimalSetup,
      referenceLayout_ready
    ] using! hb

  have hprob_nonneg :
      0 ≤
        probability_of_success
          (qs := qs)
          (evalC := LowerGateClass.evalL (qs := qs))
          (T := T)
          (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
          (x := (referenceProgramAt P hP m inst).output)
          (r := ord inst.a inst.N inst.coprime)
          (Q := ASize (referenceProgramAt P hP m inst).output)
          (C := (referenceProgramAt P hP m inst).circuit)
          (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis))) := by
    unfold probability_of_success
    apply Finset.sum_nonneg
    intro o _
    by_cases h :
        OF_post
            (T := T)
            (fun d => decide ((inst.a ^ d) % inst.N = 1))
            o.1
            (ASize (referenceProgramAt P hP m inst).output)
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

  have hκ : 0 < κ := κ_pos

  have hD : 0 < Real.log ((Nat.log2 N : ℝ) + 1) :=
    Real.log_pos (by linarith)

  have hideal : 0 < κ / Real.log ((Nat.log2 N : ℝ) + 1) := div_pos hκ hD

  obtain ⟨m, hm⟩ :=
    exists_precision_error_le
      (regSize (Reg.interval 0 (Nat.log2 (2 * N ^ 2))))
      (referenceK)
      referenceK_nonneg
      (ε := κ / Real.log ((Nat.log2 N : ℝ) + 1) / 2)
      (div_pos hideal two_pos)

  refine ⟨m, ?_⟩

  have herr :
      referenceApproximationErrorAt m N ≤
        κ / Real.log ((Nat.log2 N : ℝ) + 1) / 2 := by
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
  rw [referenceChosenPrecision, dite_eq_left hN]
  exact Nat.find_spec
    (exists_reference_positive_precision N hN)


/-! =========================================================
    Section 4: Framework-facing program and success bound
========================================================= -/

/-- Final submitted program, with approximation precision chosen internally. -/
noncomputable def referenceSubmittedProgram
    (P : ShorLoweringPolicy) (hP : P.Admissible) (inst : ShorOrderFindingInstance) :
    ShorOrderFindingProgram :=
  referenceProgramAt P hP
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
    (P : ShorLoweringPolicy) (hP : P.Admissible) :
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
          (x := (referenceSubmittedProgram P hP inst).output)
          (r := ord inst.a inst.N inst.coprime)
          (Q := ASize (referenceSubmittedProgram P hP inst).output)
          (C := (referenceSubmittedProgram P hP inst).circuit)
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
      P
      hP
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
    (P : ShorLoweringPolicy) (hP : P.Admissible) (inst : ShorOrderFindingInstance) : ℕ :=
  LowGate.gateCount shorGateCostModel
    (referenceSubmittedProgram P hP inst).circuit

omit [MeasureClass qs] [GateSemanticsFacts qs] [LowerGateClass qs] in
theorem referenceGateCount_correct
    (P : ShorLoweringPolicy) (hP : P.Admissible) (inst : ShorOrderFindingInstance) :
    LowGate.gateCount shorGateCostModel
        (referenceSubmittedProgram P hP inst).circuit =
      referenceGateCount P hP inst :=
  rfl

/-- Reference implementation packaged into the public submission interface. -/
noncomputable def referenceShorImplementation
    (P : ShorLoweringPolicy) (hP : P.Admissible) :
    ShorImplementation (qs := qs) where
  program := referenceSubmittedProgram P hP
  successProbability := referenceSuccessProbability
  correct := referenceSubmittedProgram_correct (qs := qs) P hP
  trialCount := referenceTrialCount
  trialCount_correct := by
    intro N h
    apply referenceTrialCount_correct

end Reference

end Shor
