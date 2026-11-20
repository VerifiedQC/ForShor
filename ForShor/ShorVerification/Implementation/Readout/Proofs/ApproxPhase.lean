import ForShor.ShorVerification.Implementation.Readout.Proofs.Approx

/-!
# Readout: the approximate-gate bound up to global phases

`semiclassical_dist_le_sum_errors` asks each implemented rotation `R j r` to be
`ρ j`-close to the EXACT phase `Phase c (ffAngle j r)`. Synthesis error bounds
(Ross-Selinger) are stated up to a global phase. Here each `R j r` may differ by
a global phase `exp(iα)` that may depend on the round `j` and the record `r`
(not on the state):

  `∃ α : ℝ, ∀ φ, ‖exp(iα) • R j r φ - Phase c (ffAngle j r) φ‖ ≤ ρ j · ‖φ‖`.

Route: put `R' j r = exp(iα_{j,r}) • R j r` (`phaseCorrect`). In every round a
child branch is computed LINEARLY from its parent branch alone (the round's gates,
the record-indexed rotation, the measurement projector and reset), so the run with
`R'` is the run with `R` multiplied branch by branch by a unit complex number
(`MGate.eval_phaseEquiv`, `semiclassicalImpl_phaseEquiv`), and every record has the
same probability (`recordProb_phaseCorrect`). `R'` satisfies the exact-phase
hypothesis, so the existing bound applies to it
(`semiclassical_dist_le_sum_errors_up_to_phase`).
-/

namespace Shor
namespace Readout

open MeasureClass

section Phase

variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsCore qs] [LowerGateClass qs]
  [MeasureClass qs]

/-- Two branching states agree up to a unit complex factor on every branch. -/
def PhaseEquiv (ψ ψ' : MState qs) : Prop :=
  ∃ z : Record → ℂ, (∀ r, ‖z r‖ = 1) ∧ ∀ r, ψ' r = z r • ψ r

omit [RegEncoding qs.Basis] [GateSemanticsCore qs] [LowerGateClass qs] [MeasureClass qs] in
/-- Branchwise unit factors do not change record probabilities. -/
theorem PhaseEquiv.recordProb_eq {ψ ψ' : MState qs} (h : PhaseEquiv ψ ψ') (r : Record) :
    recordProb ψ' r = recordProb ψ r := by
  obtain ⟨z, hz, h⟩ := h
  rw [recordProb, recordProb, h, norm_smul, hz, one_mul]

omit [LowerGateClass qs] in
/-- The measure-and-reset child is linear in its parent branch. -/
theorem measureResetBranch_smul (q : ℕ) (b : Bool) (a : ℂ) (φ : qs.State) :
    measureResetBranch q b (a • φ) = a • measureResetBranch q b φ := by
  cases b <;> simp [measureResetBranch, map_smul, gate_eval_smul]

/-- **Every `MGate` program preserves branchwise unit factors.** -/
theorem MGate.eval_phaseEquiv (P : MGate) {ψ ψ' : MState qs} (h : PhaseEquiv ψ ψ') :
    PhaseEquiv (P.eval ψ) (P.eval ψ') := by
  induction P generalizing ψ ψ' with
  | unitary g =>
    obtain ⟨z, hz, h⟩ := h
    exact ⟨z, hz, fun r => by simp only [MGate.eval_unitary, h, gate_eval_smul]⟩
  | ffPhase q j =>
    obtain ⟨z, hz, h⟩ := h
    exact ⟨z, hz, fun r => by
      simp only [MGate.eval_ffPhase, h]
      exact (lowL (LowGate.Phase q (ffAngle j r))).map_smul (z r) (ψ r)⟩
  | seq a b iha ihb => exact ihb (iha h)
  | measureReset q =>
    obtain ⟨z, hz, h⟩ := h
    refine ⟨fun r => z r.dropLast, fun r => hz _, fun r => ?_⟩
    rcases List.eq_nil_or_concat r with rfl | ⟨r₀, b, rfl⟩
    · simp
    · simp only [List.concat_eq_append, MGate.eval_measureReset_append, h,
        measureResetBranch_smul, List.dropLast_concat]

/-- The phase-corrected rotations `R' j r = exp(i α j r) • R j r`. -/
noncomputable def phaseCorrect (α : ℕ → Record → ℝ) (R : ℕ → Record → qs.State →ₗ[ℂ] qs.State) :
    ℕ → Record → qs.State →ₗ[ℂ] qs.State :=
  fun j r => Complex.exp ((α j r : ℂ) * Complex.I) • R j r

theorem norm_exp_mul_I (t : ℝ) : ‖Complex.exp ((t : ℂ) * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I t

/-- **The implemented readout with phase-corrected rotations is the same run up
to branchwise unit factors.** -/
theorem semiclassicalImpl_phaseEquiv (c : ℕ) (Ũ : ℕ → Gate)
    (R : ℕ → Record → qs.State →ₗ[ℂ] qs.State) (α : ℕ → Record → ℝ) (m : ℕ) (ψ : MState qs) :
    PhaseEquiv (semiclassicalImpl c Ũ R m ψ) (semiclassicalImpl c Ũ (phaseCorrect α R) m ψ) := by
  induction m with
  | zero => exact ⟨fun _ => 1, fun _ => by simp, fun r => by simp [semiclassicalImpl]⟩
  | succ k ih =>
    obtain ⟨z, hz, h⟩ := ih
    simp only [semiclassicalImpl, implRound]
    refine MGate.eval_phaseEquiv _ ⟨fun r => Complex.exp ((α k r : ℂ) * Complex.I) * z r,
      fun r => by rw [norm_mul, norm_exp_mul_I, hz, one_mul], fun r => ?_⟩
    simp only [phaseCorrect, h, LinearMap.smul_apply, gate_eval_smul, map_smul, smul_smul, mul_comm]

/-- **Global phases do not change record probabilities.** -/
theorem recordProb_phaseCorrect (c : ℕ) (Ũ : ℕ → Gate)
    (R : ℕ → Record → qs.State →ₗ[ℂ] qs.State) (α : ℕ → Record → ℝ) (m : ℕ) (ψ : MState qs)
    (r : Record) :
    recordProb (semiclassicalImpl c Ũ (phaseCorrect α R) m ψ) r
      = recordProb (semiclassicalImpl c Ũ R m ψ) r :=
  (semiclassicalImpl_phaseEquiv c Ũ R α m ψ).recordProb_eq r

omit [GateSemanticsCore qs] [MeasureClass qs] in
/-- From the up-to-phase hypothesis, a choice of phases `α` for which the
corrected rotations satisfy the exact-phase hypotheses `hR`, `hRc` of
`semiclassical_dist_le_sum_errors`. -/
theorem exists_phaseCorrection (c m : ℕ) (R : ℕ → Record → qs.State →ₗ[ℂ] qs.State)
    (ρ : ℕ → ℝ)
    (hRg : ∀ j < m, ∀ r : Record, r.length = j → ∃ α : ℝ, ∀ φ : qs.State,
      ‖Complex.exp ((α : ℂ) * Complex.I) • R j r φ
          - LowerGateClass.evalL (LowGate.Phase c (ffAngle j r)) φ‖ ≤ ρ j * ‖φ‖)
    (hRc : ∀ j < m, ∀ r : Record, r.length = j → ∀ φ : qs.State, ‖R j r φ‖ ≤ ‖φ‖) :
    ∃ α : ℕ → Record → ℝ,
      (∀ j < m, ∀ r : Record, r.length = j → ∀ φ : qs.State,
        ‖phaseCorrect α R j r φ - LowerGateClass.evalL (LowGate.Phase c (ffAngle j r)) φ‖
          ≤ ρ j * ‖φ‖) ∧
      (∀ j < m, ∀ r : Record, r.length = j → ∀ φ : qs.State, ‖phaseCorrect α R j r φ‖ ≤ ‖φ‖) := by
  classical
  let α : ℕ → Record → ℝ := fun j r =>
    if h : j < m ∧ r.length = j then Classical.choose (hRg j h.1 r h.2) else 0
  refine ⟨α, fun j hj r hr φ => ?_, fun j hj r hr φ => ?_⟩
  · have hspec := Classical.choose_spec (hRg j hj r hr)
    simp only [phaseCorrect, LinearMap.smul_apply, α, hj, hr, and_self, ↓reduceDIte]
    exact hspec φ
  · simp only [phaseCorrect, LinearMap.smul_apply, norm_smul, norm_exp_mul_I, one_mul]
    exact hRc j hj r hr φ

end Phase

section Bound

variable {qs : QSemantics.{0}} [RegEncoding qs.Basis]
  [GateSemanticsCore qs] [LowerGateClass qs] [MeasureClass qs]
  [HadamardSemantics qs] [PauliXSemantics qs] [IdealCtrlModMulExactSemantics qs]

/-- **Approximate-gate bound, rotations exact only up to global phase.** The
hypotheses of `semiclassical_dist_le_sum_errors`, except that `hR` is replaced
by `hRg`: for every round `j < m` and record `r` of length `j` there is a phase
`α` (depending on `j` and `r`, not on the state) with
`‖exp(iα) • R j r φ - Phase c (ffAngle j r) φ‖ ≤ ρ j · ‖φ‖` for every `φ`; and
`‖R j r φ‖ ≤ ‖φ‖`. The Hadamards and measure-and-reset steps are exact.

Conclusion: the `ℓ¹` distance `∑_r |P_impl(r) - P_ideal(r)|` of the record
distributions is at most `2 ∑_{j<m} (ε j + ρ j)` (in `TV = ½ · ℓ¹` terms:
`TV ≤ ∑_{j<m} (ε j + ρ j)`), exactly as with exact-phase closeness. -/
theorem semiclassical_dist_le_sum_errors_up_to_phase
    (a N m : ℕ) (data : Reg) (c : ℕ) (P : qs.Basis → Prop)
    (hN : 1 < N) (hNdata : N ≤ ASize data) (ha : Nat.Coprime a N) (hc : c ∉ data.qubits)
    (hPc : ∀ x v, P x → P (RegEncoding.writeNat (qubitReg c) v x))
    (hPdata : ∀ x v, P x → P (RegEncoding.writeNat data v x))
    (ψ₀ : qs.State) (hψ₀ : InRangeOn c data N P ψ₀) (hnorm : ‖ψ₀‖ = 1)
    (Ũ : ℕ → Gate) (R : ℕ → Record → qs.State →ₗ[ℂ] qs.State) (ε ρ : ℕ → ℝ)
    (hU : ∀ j < m, ∀ φ ∈ ValidSpan data N P,
      ‖qs.eval (Ũ j) φ
          - qs.eval (Gate.idealCtrlModMul ((a ^ (2 ^ (m - 1 - j))) % N) N data c) φ‖
        ≤ ε j * ‖φ‖)
    (hRg : ∀ j < m, ∀ r : Record, r.length = j → ∃ α : ℝ, ∀ φ : qs.State,
      ‖Complex.exp ((α : ℂ) * Complex.I) • R j r φ
          - LowerGateClass.evalL (LowGate.Phase c (ffAngle j r)) φ‖ ≤ ρ j * ‖φ‖)
    (hRc : ∀ j < m, ∀ r : Record, r.length = j → ∀ φ : qs.State, ‖R j r φ‖ ≤ ‖φ‖) :
    ∑' r : Record, |recordProb (semiclassicalImpl c Ũ R m (MState.init ψ₀)) r
        - recordProb ((semiclassicalIdeal a N m data c).eval (MState.init ψ₀)) r|
      ≤ 2 * ∑ j ∈ Finset.range m, (ε j + ρ j) := by
  obtain ⟨α, hR', hRc'⟩ := exists_phaseCorrection c m R ρ hRg hRc
  have h := semiclassical_dist_le_sum_errors a N m data c P hN hNdata ha hc hPc hPdata ψ₀ hψ₀
    hnorm Ũ (phaseCorrect α R) ε ρ hU hR' hRc'
  simpa only [recordProb_phaseCorrect] using h

end Bound

end Readout
end Shor
