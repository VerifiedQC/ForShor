import ForShor.ShorVerification.Implementation.Readout.Proofs.Approx
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Readout: tests of the approximate-gate bound

Non-vacuity checks for `Readout/Proofs/Approx.lean`, for an arbitrary quantum
semantics with the classes named in each statement:

* `bound_at_zero_is_equality`: with the exact gates (`Ũ = U`, `R j r` the exact
  phase) every error hypothesis of `semiclassical_dist_le_sum_errors` is
  discharged here with `ε = ρ = 0`; the bound then says the `ℓ¹` distance
  `∑|p - q|` of the record distributions is `≤ 0`, the zero-error corollary gives equal record probabilities, and indeed
  the implemented run IS the ideal run.
* `phase_shift_dist_le`: shifting a phase angle by `δ` moves every state by at
  most `‖exp(iπδ) - 1‖ · ‖φ‖` (the per-rotation error of a mis-synthesized
  rotation).
* `semiclassical_shifted_phase_bound`: the theorem instantiated with a real
  perturbation: every feed-forward phase replaced by `Phase c (ffAngle j r + δ)`
  (multipliers exact). All hypotheses are discharged; the bound is
  `2 · m · ‖exp(iπδ) - 1‖ ≤ 2 m π |δ|`.
* `semiclassical_shifted_phase_bound_m1`: at `m = 1`, `δ = 1/8` the bound is
  `≤ π/4 < 2`, below the trivial `ℓ¹` bound `2` (`∑|p - q| ≤ ∑p + ∑q = 2`), so the
  conclusion is not automatic. (Whether the bound is tight is not checked.)

The instance of these hypotheses at the concrete model `Model.qs` is in
`Model/Standard/MSemanticsModel.lean`.
-/

namespace Shor
namespace Readout
namespace ApproxTests

open MeasureClass

variable {qs : QSemantics} [RegEncoding qs.Basis]
  [GateSemanticsCore qs] [LowerGateClass qs] [MeasureClass qs]
  [HadamardSemantics qs] [PauliXSemantics qs] [IdealCtrlModMulExactSemantics qs]

/-- **Bound at zero error is equality.** Exact gates: `Ũ j = U j` (the ideal
multipliers) and `R j r = Phase c (ffAngle j r)`. The hypotheses of
`semiclassical_dist_le_sum_errors` hold with `ε = ρ = 0` (proved here), the
bound gives `ℓ¹` distance `∑|p - q| ≤ 0`, `semiclassical_dist_zero` gives equal record
probabilities, and the implemented run equals the ideal run. -/
theorem bound_at_zero_is_equality
    (a N m : ℕ) (data : Reg) (c : ℕ) (P : qs.Basis → Prop)
    (hN : 1 < N) (hNdata : N ≤ ASize data) (ha : Nat.Coprime a N) (hc : c ∉ data.qubits)
    (hPc : ∀ x v, P x → P (RegEncoding.writeNat (qubitReg c) v x))
    (hPdata : ∀ x v, P x → P (RegEncoding.writeNat data v x))
    (ψ₀ : qs.State) (hψ₀ : InRangeOn c data N P ψ₀) (hnorm : ‖ψ₀‖ = 1) :
    (∑' r : Record,
        |recordProb (semiclassicalImpl c (schedule a N m data c) (fun j => exactPhase c j) m
            (MState.init ψ₀)) r
          - recordProb ((semiclassicalIdeal a N m data c).eval (MState.init ψ₀)) r| ≤ 0) ∧
    (∀ r : Record,
      recordProb (semiclassicalImpl c (schedule a N m data c) (fun j => exactPhase c j) m
          (MState.init ψ₀)) r
        = recordProb ((semiclassicalIdeal a N m data c).eval (MState.init ψ₀)) r) ∧
    semiclassicalImpl c (schedule a N m data c) (fun j => exactPhase c j) m (MState.init ψ₀)
      = (semiclassicalIdeal a N m data c).eval (MState.init ψ₀) := by
  have hU : ∀ j < m, ∀ φ ∈ ValidSpan data N P,
      ‖qs.eval (schedule a N m data c j) φ
          - qs.eval (Gate.idealCtrlModMul ((a ^ (2 ^ (m - 1 - j))) % N) N data c) φ‖
        ≤ (fun _ => (0 : ℝ)) j * ‖φ‖ := fun j _ φ _ => by
    simp [schedule]
  have hR : ∀ j < m, ∀ r : Record, r.length = j → ∀ φ : qs.State,
      ‖exactPhase c j r φ - LowerGateClass.evalL (LowGate.Phase c (ffAngle j r)) φ‖
        ≤ (fun _ => (0 : ℝ)) j * ‖φ‖ := fun j _ r _ φ => by
    simp [exactPhase]
  have hRc : ∀ j < m, ∀ r : Record, r.length = j → ∀ φ : qs.State,
      ‖exactPhase c j r φ‖ ≤ ‖φ‖ := fun j _ r _ φ => by
    simp only [exactPhase, lowL_apply]
    rw [norm_evalL_phase]
  refine ⟨?_, fun r => semiclassical_dist_zero a N m data c P hN hNdata ha hc hPc hPdata ψ₀ hψ₀
    hnorm _ _ _ _ hU hR hRc (fun _ _ => rfl) (fun _ _ => rfl) r, ?_⟩
  · have := semiclassical_dist_le_sum_errors a N m data c P hN hNdata ha hc hPc hPdata ψ₀ hψ₀
      hnorm _ _ _ _ hU hR hRc
    simpa using this
  · rw [semiclassicalIdeal_eq_impl]

omit [GateSemanticsCore qs] [HadamardSemantics qs] [PauliXSemantics qs]
  [IdealCtrlModMulExactSemantics qs] in
/-- **Phase-angle perturbation.** `‖Phase c (θ + δ) φ - Phase c θ φ‖ ≤ ‖exp(iπδ) - 1‖ · ‖φ‖`. -/
theorem phase_shift_dist_le (c : ℕ) (θ δ : Angle) (φ : qs.State) :
    ‖LowerGateClass.evalL (LowGate.Phase c (θ + δ)) φ - LowerGateClass.evalL (LowGate.Phase c θ) φ‖
      ≤ ‖Complex.exp (((Angle.toReal δ : ℝ) : ℂ) * Complex.I) - 1‖ * ‖φ‖ := by
  -- split `φ` along qubit `c`
  have hsum : measProj (qubitReg c) 0 φ + measProj (qubitReg c) 1 φ = φ := by
    have h := MeasureClass.measProj_complete (qs := qs) (qubitReg c) φ
    rw [regSize_qubitReg] at h
    simpa [Fin.sum_univ_two] using h
  have hL : ∀ α : Angle, LowerGateClass.evalL (LowGate.Phase c α) φ
      = measProj (qubitReg c) 0 φ
        + Complex.exp (((Angle.toReal α : ℝ) : ℂ) * Complex.I) • measProj (qubitReg c) 1 φ :=
    fun α => by
      conv_lhs => rw [← hsum]
      rw [LowerGateClass.evalL_add, phase_measProj_zero, phase_measProj_one]
  have hexp : Complex.exp (((Angle.toReal (θ + δ) : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((Angle.toReal θ : ℝ) : ℂ) * Complex.I)
        * Complex.exp (((Angle.toReal δ : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [Angle.toReal]
    push_cast
    ring
  have hdiff : LowerGateClass.evalL (LowGate.Phase c (θ + δ)) φ
      - LowerGateClass.evalL (LowGate.Phase c θ) φ
      = (Complex.exp (((Angle.toReal θ : ℝ) : ℂ) * Complex.I)
          * (Complex.exp (((Angle.toReal δ : ℝ) : ℂ) * Complex.I) - 1))
        • measProj (qubitReg c) 1 φ := by
    rw [hL, hL, hexp]
    module
  have hP1 : ‖measProj (qubitReg c) 1 φ‖ ≤ ‖φ‖ := by
    have h := probMeas_qubitReg_zero_add_one (qs := qs) c φ
    simp only [probMeas] at h
    have h0 := sq_nonneg ‖measProj (qubitReg c) 0 φ‖
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (by linarith)
  rw [hdiff, norm_smul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  exact mul_le_mul_of_nonneg_left hP1 (norm_nonneg _)

/-- The perturbed feed-forward rotation: `Phase c (ffAngle j r + δ)`. -/
noncomputable def shiftedPhase (c : ℕ) (δ : Angle) : ℕ → Record → qs.State →ₗ[ℂ] qs.State :=
  fun j r => lowL (LowGate.Phase c (ffAngle j r + δ))

/-- **A non-trivial instance.** Every feed-forward phase replaced by
`Phase c (ffAngle j r + δ)`, multipliers exact. All hypotheses of
`semiclassical_dist_le_sum_errors` are discharged (`ε j = 0`,
`ρ j = ‖exp(iπδ) - 1‖`), giving the `ℓ¹` distance `∑|p - q| ≤ 2 m ‖exp(iπδ) - 1‖ ≤ 2 m π |δ|` (in standard
`TV = ½ · ℓ¹` terms: `TV ≤ m ‖exp(iπδ) - 1‖`). -/
theorem semiclassical_shifted_phase_bound
    (a N m : ℕ) (data : Reg) (c : ℕ) (P : qs.Basis → Prop)
    (hN : 1 < N) (hNdata : N ≤ ASize data) (ha : Nat.Coprime a N) (hc : c ∉ data.qubits)
    (hPc : ∀ x v, P x → P (RegEncoding.writeNat (qubitReg c) v x))
    (hPdata : ∀ x v, P x → P (RegEncoding.writeNat data v x))
    (ψ₀ : qs.State) (hψ₀ : InRangeOn c data N P ψ₀) (hnorm : ‖ψ₀‖ = 1) (δ : Angle) :
    ∑' r : Record,
        |recordProb (semiclassicalImpl c (schedule a N m data c) (shiftedPhase c δ) m
            (MState.init ψ₀)) r
          - recordProb ((semiclassicalIdeal a N m data c).eval (MState.init ψ₀)) r|
      ≤ 2 * m * ‖Complex.exp (((Angle.toReal δ : ℝ) : ℂ) * Complex.I) - 1‖ ∧
    2 * m * ‖Complex.exp (((Angle.toReal δ : ℝ) : ℂ) * Complex.I) - 1‖
      ≤ 2 * m * (Real.pi * |(δ : ℝ)|) := by
  set ρ : ℝ := ‖Complex.exp (((Angle.toReal δ : ℝ) : ℂ) * Complex.I) - 1‖ with hρ
  have hU : ∀ j < m, ∀ φ ∈ ValidSpan data N P,
      ‖qs.eval (schedule a N m data c j) φ
          - qs.eval (Gate.idealCtrlModMul ((a ^ (2 ^ (m - 1 - j))) % N) N data c) φ‖
        ≤ (fun _ => (0 : ℝ)) j * ‖φ‖ := fun j _ φ _ => by
    simp [schedule]
  have hR : ∀ j < m, ∀ r : Record, r.length = j → ∀ φ : qs.State,
      ‖shiftedPhase c δ j r φ - LowerGateClass.evalL (LowGate.Phase c (ffAngle j r)) φ‖
        ≤ (fun _ => ρ) j * ‖φ‖ := fun j _ r _ φ => by
    simp only [shiftedPhase, lowL_apply]
    exact phase_shift_dist_le c (ffAngle j r) δ φ
  have hRc : ∀ j < m, ∀ r : Record, r.length = j → ∀ φ : qs.State,
      ‖shiftedPhase c δ j r φ‖ ≤ ‖φ‖ := fun j _ r _ φ => by
    simp only [shiftedPhase, lowL_apply]
    rw [norm_evalL_phase]
  refine ⟨?_, ?_⟩
  · have := semiclassical_dist_le_sum_errors a N m data c P hN hNdata ha hc hPc hPdata ψ₀ hψ₀
      hnorm _ _ _ _ hU hR hRc
    simp only [zero_add, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    linarith
  · have hle : ρ ≤ Real.pi * |(δ : ℝ)| := by
      rw [hρ, mul_comm _ Complex.I]
      refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans_eq ?_
      rw [Angle.toReal, Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos, mul_comm]
    have hm : (0 : ℝ) ≤ 2 * m := by positivity
    exact mul_le_mul_of_nonneg_left hle hm

/-- **The bound is below the trivial one.** At `m = 1` (one round) and
`δ = 1/8` (a phase error of `π/8`), the `ℓ¹` distance `∑|p - q|` is at most
`π/4 < 2` (the trivial `ℓ¹` bound); in `TV = ½ · ℓ¹` terms `TV ≤ π/8`. -/
theorem semiclassical_shifted_phase_bound_m1
    (a N : ℕ) (data : Reg) (c : ℕ) (P : qs.Basis → Prop)
    (hN : 1 < N) (hNdata : N ≤ ASize data) (ha : Nat.Coprime a N) (hc : c ∉ data.qubits)
    (hPc : ∀ x v, P x → P (RegEncoding.writeNat (qubitReg c) v x))
    (hPdata : ∀ x v, P x → P (RegEncoding.writeNat data v x))
    (ψ₀ : qs.State) (hψ₀ : InRangeOn c data N P ψ₀) (hnorm : ‖ψ₀‖ = 1) :
    ∑' r : Record,
        |recordProb (semiclassicalImpl c (schedule a N 1 data c) (shiftedPhase c (1 / 8)) 1
            (MState.init ψ₀)) r
          - recordProb ((semiclassicalIdeal a N 1 data c).eval (MState.init ψ₀)) r|
      ≤ Real.pi / 4 ∧ Real.pi / 4 < 2 := by
  obtain ⟨h1, h2⟩ := semiclassical_shifted_phase_bound a N 1 data c P hN hNdata ha hc hPc hPdata
    ψ₀ hψ₀ hnorm (1 / 8)
  have h8 : ((1 / 8 : Angle) : ℝ) = 1 / 8 := by norm_num
  rw [h8] at h2
  refine ⟨?_, by linarith [Real.pi_le_four]⟩
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ = Real.pi / 4 := by norm_num; ring

end ApproxTests
end Readout
end Shor
