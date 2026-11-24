import ForShor.ShorVerification.Implementation.Readout.GhostFree

/-!
# Readout: tests of the ghost-free success theorems

* `ghostfree_implies_ghost_at_shorPrecision`: the ghost-free theorem implies the ghost
  theorem `Shor_correct_semiclassical_at_shorPrecision` (same hypotheses, `x` used only to
  rewrite `m = regSize x.active` and `Q = ASize x.active`): the new statement is at least
  as strong.
* `ghostfree_lowered_implies_ghost`: the same for the lowered statement; likewise for every
  other variant: `…_impl_of_modMul_bound`, `…_of_modMul_bound`, `…_uniform`,
  `…_impl_at_shorPrecision`, both `…_up_to_phase`, `ghostfree_lowered_balanced_implies_ghost`,
  `ghostfree_lowered_balancedU_implies_ghost` (each instantiates the ghost-free theorem with
  `.of_ghost`, `shorPrecision_eq_rounds` and `hm`).
* `outcomeMass_two_three_one_zero` (`a = 2`, `N = 3`, one round: outcome `0` has mass `1/2`)
  and `successMass_pos` (`successMass > 0` at `m = log₂(2N²) ≥ 1` for every instance).
* `shorPrecision_reference_eq`: `shorPrecision N x = shorPrecisionRounds N m` whenever
  `regSize x = m`.
* `outcomeMass_zero_rounds`: with `0` rounds the only outcome `0` has mass `1` (the
  data value `a^0 mod N = 1`, one term of modulus `1`), so `outcomeMass` is not a
  degenerate constant `0`.
-/

namespace Shor
namespace Readout
namespace GhostFreeTests

variable {qs : QSemantics.{0}} [RegEncoding qs.Basis] [MeasureClass qs]
  [GateSemanticsFacts qs] [LowerGateClass qs]

/-- The ghost-free theorem gives the ghost one's conclusion under the ghost hypotheses. -/
theorem ghostfree_implies_ghost_at_shorPrecision
    (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T)
    (inst : ShorOrderFindingInstance) (c : ℕ) (x y work scratch : ExtReg) (flag : ℕ)
    (b0 : qs.Basis)
    (hm : regSize x.active = Nat.log2 (2 * inst.N ^ 2))
    (hn : regSize y.active = Nat.log2 (2 * inst.N)) (η : ℝ)
    (hη : η ≤ shorPrecision inst.N x.active)
    (hsetup : SemiclassicalShorSetup qs η inst.N c x y work scratch flag b0) :
    probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
        (regSize x.active) (ord inst.a inst.N inst.coprime) (ASize x.active)
        ((orderFindingSemiclassical inst.a inst.N c (regSize x.active) y work scratch flag
            hsetup.circuit_workspace hsetup.step4_workspace).eval (MState.init (qs.ket b0)))
      ≥ κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1)) := by
  rw [shorPrecision_eq_rounds, hm] at hη
  have h := Shor_correct_semiclassical_ghostfree_at_shorPrecision T hT inst c y work scratch flag
    b0 hn η hη (SemiclassicalGhostFreeSetup.of_ghost hsetup)
  simp only [ASize, hm]
  exact h

/-- The ghost-free lowered statement gives the ghost lowered statement. -/
theorem ghostfree_lowered_implies_ghost (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T) :
    ShorCorrectSemiclassicalLowered (qs := qs) T hT := by
  intro inst P hP c x y work scratch flag b0 hm hn η hη hsetup hzero
  rw [shorPrecision_eq_rounds, hm] at hη
  simp only [ASize]
  rw [hm]
  intro hws
  exact Shor_correct_semiclassical_lowered_ghostfree_at_shorPrecision (qs := qs) T hT inst P hP
    c y work scratch flag b0 hn η hη (SemiclassicalGhostFreeSetup.of_ghost hsetup) hzero hws

/-- `shorPrecision` at a register of `m` qubits is `shorPrecisionRounds` at `m`. -/
theorem shorPrecision_reference_eq (N m : ℕ) (x : Reg) (hx : regSize x = m) :
    shorPrecision N x = shorPrecisionRounds N m := by
  rw [shorPrecision_eq_rounds, hx]

/-- With `0` rounds, outcome `0` has mass `1`. -/
theorem outcomeMass_zero_rounds (a N : ℕ) (hN : 1 < N) : outcomeMass a N 0 0 = 1 := by
  have h1 : 1 % N = 1 := Nat.mod_eq_of_lt hN
  unfold outcomeMass massAmp
  rw [Finset.sum_eq_single 1]
  · simp [Finset.filter_singleton, h1]
  · intro v _ hv
    simp [Finset.filter_singleton, h1, Ne.symm hv]
  · intro h; exact absurd (Finset.mem_range.2 hN) h

/-! ## Every ghost-free variant implies its ghost counterpart -/

/-- `_impl_of_modMul_bound`: ghost-free ⟹ ghost. -/
theorem ghostfree_implies_ghost_impl_of_modMul_bound (K : ℝ)
    (hmodMul : ∀ (η : ℝ) (cfg : ModMulConfig η) (ψ : qs.State),
      ModMulConfig.ValidUnitState qs cfg ψ →
      ‖qs.eval (ModMulConfig.approxGate cfg) ψ - qs.eval (ModMulConfig.idealGate cfg) ψ‖
        ≤ stepErr K η)
    (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T)
    (inst : ShorOrderFindingInstance) (c : ℕ) (x y work scratch : ExtReg) (flag : ℕ)
    (b0 : qs.Basis)
    (hm : regSize x.active = Nat.log2 (2 * inst.N ^ 2))
    (hn : regSize y.active = Nat.log2 (2 * inst.N)) (η : ℝ)
    (hsetup : SemiclassicalShorSetup qs η inst.N c x y work scratch flag b0)
    (R : ℕ → Record → qs.State →ₗ[ℂ] qs.State) (ρ : ℕ → ℝ)
    (hR : ∀ j < regSize x.active, ∀ r : Record, r.length = j → ∀ φ : qs.State,
      ‖R j r φ - LowerGateClass.evalL (LowGate.Phase c (ffAngle j r)) φ‖ ≤ ρ j * ‖φ‖)
    (hRc : ∀ j < regSize x.active, ∀ r : Record, r.length = j → ∀ φ : qs.State,
      ‖R j r φ‖ ≤ ‖φ‖) :
    probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
        (regSize x.active) (ord inst.a inst.N inst.coprime) (ASize x.active)
        (semiclassicalImpl c
          (semiclassicalMultipliers inst.a inst.N c (regSize x.active) y work scratch flag
            hsetup.circuit_workspace hsetup.step4_workspace)
          R (regSize x.active) (MState.init (qs.eval (initY1 y.active) (qs.ket b0))))
      ≥ κ / Real.log ((Nat.log2 inst.N : ℝ) + 1)
        - 2 * ∑ j ∈ Finset.range (regSize x.active), (stepErr K η + ρ j) := by
  rw [hm] at hR hRc
  simp only [ASize]
  rw [hm]
  exact Shor_correct_semiclassical_impl_ghostfree_of_modMul_bound K hmodMul T hT inst c y work
    scratch flag b0 hn η (SemiclassicalGhostFreeSetup.of_ghost hsetup) R ρ hR hRc

/-- `_of_modMul_bound` (the `MGate`): ghost-free ⟹ ghost. -/
theorem ghostfree_implies_ghost_of_modMul_bound (K : ℝ)
    (hmodMul : ∀ (η : ℝ) (cfg : ModMulConfig η) (ψ : qs.State),
      ModMulConfig.ValidUnitState qs cfg ψ →
      ‖qs.eval (ModMulConfig.approxGate cfg) ψ - qs.eval (ModMulConfig.idealGate cfg) ψ‖
        ≤ stepErr K η)
    (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T)
    (inst : ShorOrderFindingInstance) (c : ℕ) (x y work scratch : ExtReg) (flag : ℕ)
    (b0 : qs.Basis)
    (hm : regSize x.active = Nat.log2 (2 * inst.N ^ 2))
    (hn : regSize y.active = Nat.log2 (2 * inst.N)) (η : ℝ)
    (hsetup : SemiclassicalShorSetup qs η inst.N c x y work scratch flag b0) :
    probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
        (regSize x.active) (ord inst.a inst.N inst.coprime) (ASize x.active)
        ((orderFindingSemiclassical inst.a inst.N c (regSize x.active) y work scratch flag
            hsetup.circuit_workspace hsetup.step4_workspace).eval (MState.init (qs.ket b0)))
      ≥ κ / Real.log ((Nat.log2 inst.N : ℝ) + 1)
        - 2 * (regSize x.active : ℝ) * Real.sqrt (2 * (K * η)) := by
  simp only [ASize]
  rw [hm]
  exact Shor_correct_semiclassical_ghostfree_of_modMul_bound K hmodMul T hT inst c y work
    scratch flag b0 hn η (SemiclassicalGhostFreeSetup.of_ghost hsetup)

/-- The uniform-`K` theorem: the ghost-free one implies the ghost one's statement (same `K`). -/
theorem ghostfree_implies_ghost_uniform (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T) :
    ∃ K : ℝ, 0 ≤ K ∧ K ≤ 1600 ∧
      ∀ (inst : ShorOrderFindingInstance) (c : ℕ) (x y work scratch : ExtReg) (flag : ℕ)
        (b0 : qs.Basis)
        (_hm : regSize x.active = Nat.log2 (2 * inst.N ^ 2))
        (_hn : regSize y.active = Nat.log2 (2 * inst.N)) (η : ℝ)
        (hsetup : SemiclassicalShorSetup qs η inst.N c x y work scratch flag b0),
    probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
        (regSize x.active) (ord inst.a inst.N inst.coprime) (ASize x.active)
        ((orderFindingSemiclassical inst.a inst.N c (regSize x.active) y work scratch flag
            hsetup.circuit_workspace hsetup.step4_workspace).eval (MState.init (qs.ket b0)))
          ≥ κ / Real.log ((Nat.log2 inst.N : ℝ) + 1)
            - 2 * (regSize x.active : ℝ) * Real.sqrt (2 * (K * η)) := by
  obtain ⟨K, hK0, hK, h⟩ := Shor_correct_semiclassical_ghostfree (qs := qs) T hT
  refine ⟨K, hK0, hK, fun inst c x y work scratch flag b0 hm hn η hsetup => ?_⟩
  simp only [ASize]
  rw [hm]
  exact h inst c y work scratch flag b0 hn η (SemiclassicalGhostFreeSetup.of_ghost hsetup)

/-- `_impl_at_shorPrecision`: ghost-free ⟹ ghost. -/
theorem ghostfree_implies_ghost_impl_at_shorPrecision
    (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T)
    (inst : ShorOrderFindingInstance) (c : ℕ) (x y work scratch : ExtReg) (flag : ℕ)
    (b0 : qs.Basis)
    (hm : regSize x.active = Nat.log2 (2 * inst.N ^ 2))
    (hn : regSize y.active = Nat.log2 (2 * inst.N)) (η : ℝ)
    (hη : η ≤ shorPrecision inst.N x.active)
    (hsetup : SemiclassicalShorSetup qs η inst.N c x y work scratch flag b0)
    (R : ℕ → Record → qs.State →ₗ[ℂ] qs.State) (ρ : ℕ → ℝ)
    (hR : ∀ j < regSize x.active, ∀ r : Record, r.length = j → ∀ φ : qs.State,
      ‖R j r φ - LowerGateClass.evalL (LowGate.Phase c (ffAngle j r)) φ‖ ≤ ρ j * ‖φ‖)
    (hRc : ∀ j < regSize x.active, ∀ r : Record, r.length = j → ∀ φ : qs.State,
      ‖R j r φ‖ ≤ ‖φ‖) :
    probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
        (regSize x.active) (ord inst.a inst.N inst.coprime) (ASize x.active)
        (semiclassicalImpl c
          (semiclassicalMultipliers inst.a inst.N c (regSize x.active) y work scratch flag
            hsetup.circuit_workspace hsetup.step4_workspace)
          R (regSize x.active) (MState.init (qs.eval (initY1 y.active) (qs.ket b0))))
      ≥ κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1))
        - 2 * ∑ j ∈ Finset.range (regSize x.active), ρ j := by
  rw [shorPrecision_eq_rounds, hm] at hη
  rw [hm] at hR hRc
  simp only [ASize]
  rw [hm]
  exact Shor_correct_semiclassical_impl_ghostfree_at_shorPrecision T hT inst c y work scratch flag
    b0 hn η hη (SemiclassicalGhostFreeSetup.of_ghost hsetup) R ρ hR hRc

/-- `_impl_of_modMul_bound_up_to_phase`: ghost-free ⟹ ghost. -/
theorem ghostfree_implies_ghost_impl_of_modMul_bound_up_to_phase (K : ℝ)
    (hmodMul : ∀ (η : ℝ) (cfg : ModMulConfig η) (ψ : qs.State),
      ModMulConfig.ValidUnitState qs cfg ψ →
      ‖qs.eval (ModMulConfig.approxGate cfg) ψ - qs.eval (ModMulConfig.idealGate cfg) ψ‖
        ≤ stepErr K η)
    (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T)
    (inst : ShorOrderFindingInstance) (c : ℕ) (x y work scratch : ExtReg) (flag : ℕ)
    (b0 : qs.Basis)
    (hm : regSize x.active = Nat.log2 (2 * inst.N ^ 2))
    (hn : regSize y.active = Nat.log2 (2 * inst.N)) (η : ℝ)
    (hsetup : SemiclassicalShorSetup qs η inst.N c x y work scratch flag b0)
    (R : ℕ → Record → qs.State →ₗ[ℂ] qs.State) (ρ : ℕ → ℝ)
    (hRg : ∀ j < regSize x.active, ∀ r : Record, r.length = j → ∃ α : ℝ, ∀ φ : qs.State,
      ‖Complex.exp ((α : ℂ) * Complex.I) • R j r φ
          - LowerGateClass.evalL (LowGate.Phase c (ffAngle j r)) φ‖ ≤ ρ j * ‖φ‖)
    (hRc : ∀ j < regSize x.active, ∀ r : Record, r.length = j → ∀ φ : qs.State,
      ‖R j r φ‖ ≤ ‖φ‖) :
    probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
        (regSize x.active) (ord inst.a inst.N inst.coprime) (ASize x.active)
        (semiclassicalImpl c
          (semiclassicalMultipliers inst.a inst.N c (regSize x.active) y work scratch flag
            hsetup.circuit_workspace hsetup.step4_workspace)
          R (regSize x.active) (MState.init (qs.eval (initY1 y.active) (qs.ket b0))))
      ≥ κ / Real.log ((Nat.log2 inst.N : ℝ) + 1)
        - 2 * ∑ j ∈ Finset.range (regSize x.active), (stepErr K η + ρ j) := by
  rw [hm] at hRg hRc
  simp only [ASize]
  rw [hm]
  exact Shor_correct_semiclassical_impl_ghostfree_of_modMul_bound_up_to_phase K hmodMul T hT inst
    c y work scratch flag b0 hn η (SemiclassicalGhostFreeSetup.of_ghost hsetup) R ρ hRg hRc

/-- `_impl_at_shorPrecision_up_to_phase`: ghost-free ⟹ ghost. -/
theorem ghostfree_implies_ghost_impl_at_shorPrecision_up_to_phase
    (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T)
    (inst : ShorOrderFindingInstance) (c : ℕ) (x y work scratch : ExtReg) (flag : ℕ)
    (b0 : qs.Basis)
    (hm : regSize x.active = Nat.log2 (2 * inst.N ^ 2))
    (hn : regSize y.active = Nat.log2 (2 * inst.N)) (η : ℝ)
    (hη : η ≤ shorPrecision inst.N x.active)
    (hsetup : SemiclassicalShorSetup qs η inst.N c x y work scratch flag b0)
    (R : ℕ → Record → qs.State →ₗ[ℂ] qs.State) (ρ : ℕ → ℝ)
    (hRg : ∀ j < regSize x.active, ∀ r : Record, r.length = j → ∃ α : ℝ, ∀ φ : qs.State,
      ‖Complex.exp ((α : ℂ) * Complex.I) • R j r φ
          - LowerGateClass.evalL (LowGate.Phase c (ffAngle j r)) φ‖ ≤ ρ j * ‖φ‖)
    (hRc : ∀ j < regSize x.active, ∀ r : Record, r.length = j → ∀ φ : qs.State,
      ‖R j r φ‖ ≤ ‖φ‖) :
    probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
        (regSize x.active) (ord inst.a inst.N inst.coprime) (ASize x.active)
        (semiclassicalImpl c
          (semiclassicalMultipliers inst.a inst.N c (regSize x.active) y work scratch flag
            hsetup.circuit_workspace hsetup.step4_workspace)
          R (regSize x.active) (MState.init (qs.eval (initY1 y.active) (qs.ket b0))))
      ≥ κ / (2 * Real.log ((Nat.log2 inst.N : ℝ) + 1))
        - 2 * ∑ j ∈ Finset.range (regSize x.active), ρ j := by
  rw [shorPrecision_eq_rounds, hm] at hη
  rw [hm] at hRg hRc
  simp only [ASize]
  rw [hm]
  exact Shor_correct_semiclassical_impl_ghostfree_at_shorPrecision_up_to_phase T hT inst c y work
    scratch flag b0 hn η hη (SemiclassicalGhostFreeSetup.of_ghost hsetup) R ρ hRg hRc

/-- Balanced lowering: ghost-free ⟹ ghost (every rule `R`). -/
theorem ghostfree_lowered_balanced_implies_ghost (R : Balanced.Rule) (T : ℕ → ℕ)
    (hT : ContinuedFractionSearchComplete T) :
    ShorCorrectSemiclassicalLoweredBalanced (qs := qs) R T hT := by
  intro inst P hP c x y work scratch flag b0 hm hn η hη hsetup hzero
  rw [shorPrecision_eq_rounds, hm] at hη
  simp only [ASize]
  rw [hm]
  intro hws
  exact Shor_correct_semiclassical_lowered_balanced_ghostfree_at_shorPrecision (qs := qs) R T hT
    inst P hP c y work scratch flag b0 hn η hη (SemiclassicalGhostFreeSetup.of_ghost hsetup) hzero
    hws

/-- Every site split (with its `Fits` hypothesis): ghost-free ⟹ ghost (every rule `R`). -/
theorem ghostfree_lowered_balancedU_implies_ghost (R : Balanced.Rule) (T : ℕ → ℕ)
    (hT : ContinuedFractionSearchComplete T) :
    ShorCorrectSemiclassicalLoweredBalancedU (qs := qs) R T hT := by
  intro inst P hP c x y work scratch flag b0 hm hn η hη hsetup hzero
  rw [shorPrecision_eq_rounds, hm] at hη
  simp only [ASize]
  rw [hm]
  intro hws hf
  exact Shor_correct_semiclassical_lowered_balancedU_ghostfree_at_shorPrecision (qs := qs) R T hT
    inst P hP c y work scratch flag b0 hn η hη (SemiclassicalGhostFreeSetup.of_ghost hsetup) hzero
    hws hf

/-! ## `successMass` at a positive number of rounds -/

/-- With `1` round, `a = 2`, `N = 3`: outcome `0` has mass `1/2` (data values `1` and `2`,
one term each, amplitude `1/2`). -/
theorem outcomeMass_two_three_one_zero : outcomeMass 2 3 1 0 = 1 / 2 := by
  have h0 : ((Finset.range 2).filter (fun κ => 2 ^ κ % 3 = 0)).card = 0 := by decide
  have h1 : ((Finset.range 2).filter (fun κ => 2 ^ κ % 3 = 1)).card = 1 := by decide
  have h2 : ((Finset.range 2).filter (fun κ => 2 ^ κ % 3 = 2)).card = 1 := by decide
  unfold outcomeMass massAmp
  simp [Finset.sum_range_succ, h0, h1, h2]
  norm_num

/-- `successMass` is positive at `m = log₂(2N²) ≥ 1` for every instance (from
`successMass_ge_of_semantics` and `κ > 0`; any model `qs'` witnesses it). -/
theorem successMass_pos (qs' : QSemantics.{0}) [RegEncoding qs'.Basis]
    [GateSemanticsFacts qs'] [MeasureClass qs'] (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T)
    (inst : ShorOrderFindingInstance) :
    0 < successMass T (fun d => decide ((inst.a ^ d) % inst.N = 1)) inst.a inst.N
        (Nat.log2 (2 * inst.N ^ 2)) (ord inst.a inst.N inst.coprime) := by
  have h := successMass_ge_of_semantics qs' T hT inst
  have hN : 2 ≤ inst.N := by have := inst.range; omega
  have hlog : 0 < Nat.log2 inst.N := by
    rw [Nat.log2_eq_log_two]; exact Nat.log_pos Nat.one_lt_two hN
  have hL : (0 : ℝ) < Real.log ((Nat.log2 inst.N : ℝ) + 1) := by
    apply Real.log_pos
    have : (0 : ℝ) < (Nat.log2 inst.N : ℝ) := by exact_mod_cast hlog
    linarith
  have := κ_pos
  have : 0 < κ / Real.log ((Nat.log2 inst.N : ℝ) + 1) := by positivity
  linarith

end GhostFreeTests
end Readout
end Shor
