import ForShor.ShorVerification.Implementation.Reference.Standard.Proofs.Readiness

/-!
# Reference: the success bound

The reference program at precision level `m` meets `referenceSuccessProbabilityAt m`
(`programOf_success`); a positive bound exists at every modulus, so the chosen
precision and the trial count are the least such (`referenceChosenPrecision_positive`,
`referenceTrialCount_correct`); and the submitted program meets the contract
(`submittedProgramOf_correct`).
-/

namespace Shor
namespace Reference

variable {qs : QSemantics}
variable [RegEncoding qs.Basis]
variable [MeasureClass qs]
variable [GateSemanticsFacts qs]
variable [LowerGateClass qs]

omit [MeasureClass qs] [LowerGateClass qs] in
theorem referenceK_nonneg : 0 ≤ referenceK := by
  norm_num [referenceK]

omit [MeasureClass qs] [LowerGateClass qs] in
theorem referenceSuccessProbabilityAt_bounds (m N : ℕ) :
    0 ≤ referenceSuccessProbabilityAt m N ∧ referenceSuccessProbabilityAt m N ≤ 1 := by
  simp [referenceSuccessProbabilityAt]

/-! ## The bound at a fixed level -/

/-- The reference program at level `m` achieves its declared bound. -/
theorem programOf_success (P : ShorLoweringPolicy) (hP : P.Admissible) (m : ℕ) :
    ∀ (T : ℕ → ℕ), ContinuedFractionSearchComplete T →
    ∀ inst : ShorOrderFindingInstance,
      referenceSuccessProbabilityAt m inst.N ≤
        probability_of_success
          (qs := qs)
          (evalC := LowerGateClass.evalL (qs := qs))
          (T := T)
          (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
          (x := (referenceProgramOf (reference_ready P inst m)).output)
          (r := ord inst.a inst.N inst.coprime)
          (Q := ASize (referenceProgramOf (reference_ready P inst m)).output)
          (C := (referenceProgramOf (reference_ready P inst m)).circuit)
          (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis))) := by
  intro T hT inst
  let η : ℝ := referencePrecision m
  let layout := allocateReferenceLayout P inst m
  let hready := referenceLayout_ready (qs := qs) P inst m
  have hxwidth : regSize layout.x.active = Nat.log2 (2 * inst.N^2) := by
    simpa [layout] using allocateReferenceLayout_x_width P inst m
  have hywidth : regSize layout.data.active = Nat.log2 (2 * inst.N) := by
    simp [layout]
  have hxw : regSize (referenceX P inst m).active = Nat.log2 (2 * inst.N ^ 2) :=
    allocateReferenceLayout_x_width P inst m
  -- The lowered bound holds at some `K ≤ 1600`; the loss is monotone in `K`.
  obtain ⟨K, _, hK, hunif⟩ := Shor_correct_approx_lowered_uniform (qs := qs) T hT
  have hb0 :=
    hunif inst P hP layout.x layout.data layout.work layout.scratch layout.flag
      (RegEncoding.zero (Basis := qs.Basis)) hxwidth hywidth η hready hready.workspace
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
          (x := (referenceProgramOf (reference_ready P inst m)).output)
          (r := ord inst.a inst.N inst.coprime)
          (Q := ASize (referenceProgramOf (reference_ready P inst m)).output)
          (C := (referenceProgramOf (reference_ready P inst m)).circuit)
          (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis))) := by
    simpa [referenceProgramOf, referenceShorCircuitOf, orderFindingApproxLow,
      referenceRawSuccessProbabilityAt, referenceApproximationErrorAt, referenceK,
      LoweredShorReady.circuit, referenceXActive, referenceXWidth, layout, η, hready,
      referenceLayout_ready, allocatedReferenceApproxSetupMinimal, referenceApproxSetupMinimal,
      reference_step4Workspace, allocateReferenceLayout, hxw] using! hb
  have hprob_nonneg :
      0 ≤
        probability_of_success
          (qs := qs)
          (evalC := LowerGateClass.evalL (qs := qs))
          (T := T)
          (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
          (x := (referenceProgramOf (reference_ready P inst m)).output)
          (r := ord inst.a inst.N inst.coprime)
          (Q := ASize (referenceProgramOf (reference_ready P inst m)).output)
          (C := (referenceProgramOf (reference_ready P inst m)).circuit)
          (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis))) := by
    unfold probability_of_success
    apply Finset.sum_nonneg
    intro o _
    by_cases h :
        OF_post (T := T) (fun d => decide ((inst.a ^ d) % inst.N = 1)) o.1
            (ASize (referenceProgramOf (reference_ready P inst m)).output)
          = ord inst.a inst.N inst.coprime
    · simp [r_found, h, MeasureClass.probMeas]
    · simp [r_found, h]
  rw [referenceSuccessProbabilityAt]
  exact max_le hprob_nonneg (le_trans (min_le_right 1 _) hraw)

/-! ## The chosen precision -/

theorem exists_precision_error_le (t : ℕ) (K : ℝ) (_hK : 0 ≤ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 2 * (t : ℝ) * Real.sqrt (2 * (K * referencePrecision m)) ≤ ε := by
  have hden : (0 : ℝ) < 2 * (t : ℝ) + 1 := by positivity
  let D : ℝ := ε / (2 * (t : ℝ) + 1)
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hDsq : 0 < D ^ 2 := by positivity
  obtain ⟨m, hm⟩ := exists_nat_ge (2 * K / D ^ 2)
  refine ⟨m, ?_⟩
  have hm3 : (0 : ℝ) < (m : ℝ) + 3 := by positivity
  have herror : 2 * (K * referencePrecision m) ≤ D ^ 2 := by
    have hrewrite : 2 * (K * referencePrecision m) = 2 * K / ((m : ℝ) + 3) := by
      unfold referencePrecision
      field_simp
    rw [hrewrite, div_le_iff₀ hm3]
    have hle : 2 * K / D ^ 2 ≤ (m : ℝ) + 3 := by
      calc
        2 * K / D ^ 2 ≤ (m : ℝ) := hm
        _ ≤ (m : ℝ) + 3 := by linarith
    rw [div_le_iff₀ hDsq] at hle
    nlinarith
  have hsqrt : Real.sqrt (2 * (K * referencePrecision m)) ≤ D := by
    calc
      Real.sqrt (2 * (K * referencePrecision m)) ≤ Real.sqrt (D ^ 2) := Real.sqrt_le_sqrt herror
      _ = D := Real.sqrt_sq hD.le
  calc
    2 * (t : ℝ) * Real.sqrt (2 * (K * referencePrecision m)) ≤ 2 * (t : ℝ) * D := by
      exact mul_le_mul_of_nonneg_left hsqrt (by positivity)
    _ ≤ ε := by
      dsimp [D]
      rw [mul_div_assoc', div_le_iff₀ hden]
      nlinarith [hε]

omit [MeasureClass qs] [LowerGateClass qs] in
/-- Some precision level has a positive declared bound. -/
theorem exists_reference_positive_precision (N : ℕ) (hN : 2 ≤ N) :
    ∃ m : ℕ, 0 < referenceSuccessProbabilityAt m N := by
  have hlogNat : 0 < Nat.log2 N := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_pos Nat.one_lt_two hN
  have hlog : (0 : ℝ) < Nat.log2 N := by exact_mod_cast hlogNat
  have hκ : 0 < κ := κ_pos
  have hD : 0 < Real.log ((Nat.log2 N : ℝ) + 1) := Real.log_pos (by linarith)
  have hideal : 0 < κ / Real.log ((Nat.log2 N : ℝ) + 1) := div_pos hκ hD
  obtain ⟨m, hm⟩ :=
    exists_precision_error_le (regSize (Reg.interval 0 (Nat.log2 (2 * N ^ 2)))) referenceK
      referenceK_nonneg (ε := κ / Real.log ((Nat.log2 N : ℝ) + 1) / 2) (div_pos hideal two_pos)
  refine ⟨m, ?_⟩
  have herr : referenceApproximationErrorAt m N ≤ κ / Real.log ((Nat.log2 N : ℝ) + 1) / 2 := by
    simpa [referenceApproximationErrorAt] using hm
  have hraw : 0 < referenceRawSuccessProbabilityAt m N := by
    rw [referenceRawSuccessProbabilityAt]
    linarith
  have hmin : 0 < min 1 (referenceRawSuccessProbabilityAt m N) := lt_min (by norm_num) hraw
  rw [referenceSuccessProbabilityAt, max_eq_right hmin.le]
  exact hmin

omit [MeasureClass qs] [LowerGateClass qs] in
theorem referenceChosenPrecision_positive (N : ℕ) (hN : 2 ≤ N) :
    0 < referenceSuccessProbabilityAt (referenceChosenPrecision N) N := by
  have hex := exists_reference_positive_precision N hN
  rw [referenceChosenPrecision, dite_eq_left hex]
  exact Nat.find_spec hex

omit [MeasureClass qs] [LowerGateClass qs] in
theorem referenceSuccessProbability_bounds (N : ℕ) :
    0 ≤ referenceSuccessProbability N ∧ referenceSuccessProbability N ≤ 1 := by
  by_cases hN : 2 ≤ N
  · simpa [referenceSuccessProbability, hN] using
      referenceSuccessProbabilityAt_bounds (referenceChosenPrecision N) N
  · simp [referenceSuccessProbability, hN]

omit [MeasureClass qs] [LowerGateClass qs] in
theorem referenceSuccessProbability_pos (N : ℕ) : 0 < referenceSuccessProbability N := by
  by_cases hN : 2 ≤ N
  · simpa [referenceSuccessProbability, hN] using referenceChosenPrecision_positive N hN
  · simp [referenceSuccessProbability, hN]

/-! ## The submitted program -/

/-- The program at the chosen precision meets the contract's `correct`. -/
theorem submittedProgramOf_correct (P : ShorLoweringPolicy) (hP : P.Admissible) :
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
          (x := (referenceProgramOf (reference_ready P inst (referenceChosenPrecision inst.N))).output)
          (r := ord inst.a inst.N inst.coprime)
          (Q := ASize (referenceProgramOf (reference_ready P inst (referenceChosenPrecision inst.N))).output)
          (C := (referenceProgramOf (reference_ready P inst (referenceChosenPrecision inst.N))).circuit)
          (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis))) := by
  intro T hT inst
  have hN : 2 ≤ inst.N := by
    have hr := inst.range
    omega
  have hbounds := referenceSuccessProbability_bounds inst.N
  refine ⟨hbounds.1, hbounds.2, ?_⟩
  simpa [referenceSuccessProbability, hN] using
    programOf_success (qs := qs) P hP (referenceChosenPrecision inst.N) T hT inst

/-! ## The trial count -/

omit [MeasureClass qs] [LowerGateClass qs] in
theorem exists_reference_trialCount (N : ℕ) :
    ∃ k : ℕ, (99 / 100 : ℝ) ≤ 1 - (1 - referenceSuccessProbability N) ^ k := by
  let p := referenceSuccessProbability N
  have hp : 0 < p := by simpa [p] using referenceSuccessProbability_pos N
  have hlt : 1 - p < (1 : ℝ) := by linarith
  obtain ⟨k, hk⟩ :=
    exists_pow_lt_of_lt_one (K := ℝ) (x := (1 / 100 : ℝ)) (y := 1 - p) (by norm_num) hlt
  refine ⟨k, ?_⟩
  change (99 / 100 : ℝ) ≤ 1 - (1 - p) ^ k
  linarith

omit [MeasureClass qs] [LowerGateClass qs] in
theorem referenceTrialCount_correct (N : ℕ) :
    (99 / 100 : ℝ) ≤ 1 - (1 - referenceSuccessProbability N) ^ referenceTrialCount N := by
  have hex := exists_reference_trialCount N
  rw [referenceTrialCount, dite_eq_left hex]
  exact Nat.find_spec hex

end Reference
end Shor
