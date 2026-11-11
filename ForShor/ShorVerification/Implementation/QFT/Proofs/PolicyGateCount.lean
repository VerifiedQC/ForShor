import ForShor.ShorVerification.Implementation.QFT.Proofs.GateCount
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.GateCount.Policy

/-!
# QFT gate count under a policy

The gate count of `Policy.lowerQFT P`: `O(n ^ P.gateExponent)`, the rate of the phase product at
its splits. A split of width `n` runs one phase product on its two halves and recurses on each
half, and for any exponent above one the two half-width powers contract
(`rpow_half_contraction`), so the phase-product rate at the root dominates.
-/

namespace Shor

open Operations

section PolicyQFTGateCount

variable (nm : NegationMethod)
variable (P : ShorLoweringPolicy)

/-- Gate count of the policy QFT plan on explicit workspace pools. -/
noncomputable def Policy.qftPlanGateCountFor (r xWork zWork : Reg)
    (hworkspace : Policy.QFTWorkspaceOK P r xWork zWork) : ℕ :=
  LowGate.gateCount (shorGateCostModelFor nm)
    (lowerQFTPlan (Policy.qftPlan P r xWork zWork hworkspace))

/-- Gate count of the phase-product node at a QFT split. -/
noncomputable def Policy.qftPhaseGateCountFor (r xWork zWork : Reg)
    (hworkspace : Policy.QFTWorkspaceOK P r xWork zWork) (hsize : 2 ≤ regSize r) : ℕ :=
  LowGate.gateCount (shorGateCostModelFor nm)
    (lowerGateRec
      (Policy.phaseProdUsingPlan P (qftPhi (regSize r)) (hworkspace.phaseWorkspace hsize)))

/-! ## One split -/

/-- The phase-product node of a split costs the signed product on the two halves, each grown by
one qubit. -/
lemma Policy.qftPhaseGateCountFor_eq_signed (r xWork zWork : Reg)
    (hworkspace : Policy.QFTWorkspaceOK P r xWork zWork) (hsize : 2 ≤ regSize r) :
    Policy.qftPhaseGateCountFor nm P r xWork zWork hworkspace hsize
      = Policy.signedPhaseProductGateCountFor nm P (qftPhi (regSize r))
          ((hworkspace.phaseWorkspace hsize).xExt.grow 1)
          ((hworkspace.phaseWorkspace hsize).zExt.grow 1) := by
  set ws := hworkspace.phaseWorkspace hsize
  have hplan :
      lowerGateRec (Policy.phaseProdUsingPlan P (qftPhi (regSize r)) ws)
        = LowGate.seq (LowGate.zeroExtend ws.xExt 1)
            (LowGate.seq (LowGate.zeroExtend ws.zExt 1)
              (LowGate.seq
                (Policy.lowerSignedPhaseProd P (qftPhi (regSize r)) (ws.xExt.grow 1)
                  (ws.zExt.grow 1))
                (LowGate.seq (LowGate.zeroDealloc ws.zExt 1) (LowGate.zeroDealloc ws.xExt 1)))) :=
    rfl
  simp only [Policy.qftPhaseGateCountFor, Policy.signedPhaseProductGateCountFor]
  rw [hplan]
  simp [LowGate.gateCount]

/-- A split costs its right child, its phase product, its left child and the radix reversal. -/
lemma Policy.qftPlanGateCountFor_split (r xWork zWork : Reg)
    (hworkspace : Policy.QFTWorkspaceOK P r xWork zWork) (hsize : 2 ≤ regSize r) :
    Policy.qftPlanGateCountFor nm P r xWork zWork hworkspace
      = Policy.qftPlanGateCountFor nm P (rightReg r) xWork zWork (hworkspace.right hsize)
        + Policy.qftPhaseGateCountFor nm P r xWork zWork hworkspace hsize
        + Policy.qftPlanGateCountFor nm P (leftReg r) xWork zWork (hworkspace.left hsize)
        + qftSplitRadixGateCount r := by
  have hplan :
      Policy.qftPlan P r xWork zWork hworkspace =
        QFTLoweringPlan.split r hsize
          (hworkspace.phaseWorkspace hsize)
          (phaseInputSize ((hworkspace.phaseWorkspace hsize).xExt.grow 1)
            ((hworkspace.phaseWorkspace hsize).zExt.grow 1))
          (Policy.phaseProdUsingPlan P (qftPhi (regSize r)) (hworkspace.phaseWorkspace hsize))
          (Policy.qftPlan P (rightReg r) xWork zWork (hworkspace.right hsize))
          (Policy.qftPlan P (leftReg r) xWork zWork (hworkspace.left hsize)) := by
    rw [Policy.qftPlan]
    simp only [show regSize r ≠ 0 by omega, show regSize r ≠ 1 by omega,
      dite_eq_right, not_false_eq_true]
  unfold Policy.qftPlanGateCountFor
  rw [hplan]
  simp only [lowerQFTPlan, LowGate.gateCount_seq_eq]
  have hrad := gateCount_radixReverse_for nm r
  unfold Policy.qftPhaseGateCountFor
  unfold qftHalfWidth at hrad
  omega

/-- The empty register costs nothing. -/
lemma Policy.qftPlanGateCountFor_zero (r xWork zWork : Reg)
    (hworkspace : Policy.QFTWorkspaceOK P r xWork zWork) (hzero : regSize r = 0) :
    Policy.qftPlanGateCountFor nm P r xWork zWork hworkspace = 0 := by
  have hplan : Policy.qftPlan P r xWork zWork hworkspace = QFTLoweringPlan.empty r hzero := by
    rw [Policy.qftPlan]
    simp [hzero]
  simp [Policy.qftPlanGateCountFor, hplan, lowerQFTPlan]

/-- A one-qubit register costs one gate. -/
lemma Policy.qftPlanGateCountFor_one (r xWork zWork : Reg)
    (hworkspace : Policy.QFTWorkspaceOK P r xWork zWork) (hone : regSize r = 1) :
    Policy.qftPlanGateCountFor nm P r xWork zWork hworkspace = 1 := by
  have hplan : Policy.qftPlan P r xWork zWork hworkspace = QFTLoweringPlan.singleton r hone := by
    rw [Policy.qftPlan]
    simp [hone]
  simp [Policy.qftPlanGateCountFor, hplan, lowerQFTPlan]

/-- The operands of a split's phase product are at most as wide as the split. -/
lemma Policy.qftPhase_inputSize_le (r xWork zWork : Reg)
    (hworkspace : Policy.QFTWorkspaceOK P r xWork zWork) (hsize : 2 ≤ regSize r) :
    phaseInputSize ((hworkspace.phaseWorkspace hsize).xExt.grow 1)
        ((hworkspace.phaseWorkspace hsize).zExt.grow 1) ≤ regSize r := by
  rw [phaseInputSize_phaseProdUsing, regSize_leftReg, regSize_rightReg]
  omega

/-- The operands of a split's phase product are at least half as wide as the split. -/
lemma Policy.qftPhase_half_le_inputSize (r xWork zWork : Reg)
    (hworkspace : Policy.QFTWorkspaceOK P r xWork zWork) (hsize : 2 ≤ regSize r) :
    regSize r / 2 ≤ phaseInputSize ((hworkspace.phaseWorkspace hsize).xExt.grow 1)
        ((hworkspace.phaseWorkspace hsize).zExt.grow 1) := by
  rw [phaseInputSize_phaseProdUsing, regSize_leftReg, regSize_rightReg]
  omega

/-! ## Bounded widths -/

/-- Registers of bounded width cost a bounded number of gates. -/
lemma Policy.qftPlanGateCountFor_bounded (N : ℕ) :
    ∃ D : ℕ, ∀ (r xWork zWork : Reg) (hworkspace : Policy.QFTWorkspaceOK P r xWork zWork),
      regSize r ≤ N → Policy.qftPlanGateCountFor nm P r xWork zWork hworkspace ≤ D := by
  induction N with
  | zero =>
      refine ⟨0, fun r xWork zWork hworkspace hsize => ?_⟩
      rw [Policy.qftPlanGateCountFor_zero nm P r xWork zWork hworkspace (by omega)]
  | succ N ih =>
      obtain ⟨D, hD⟩ := ih
      obtain ⟨Q, hQ⟩ := Policy.signedPhaseProductGateCountFor_bounded nm P (N + 1)
      refine ⟨D + (2 * D + Q + 3 * (N + 1)) + 1, fun r xWork zWork hworkspace hsize => ?_⟩
      by_cases hprevious : regSize r ≤ N
      · exact (hD r xWork zWork hworkspace hprevious).trans (by omega)
      by_cases htwo : 2 ≤ regSize r
      · have hleft : regSize (leftReg r) ≤ N := by rw [regSize_leftReg]; omega
        have hright : regSize (rightReg r) ≤ N := by rw [regSize_rightReg]; omega
        have hleftCost := hD (leftReg r) xWork zWork (hworkspace.left htwo) hleft
        have hrightCost := hD (rightReg r) xWork zWork (hworkspace.right htwo) hright
        have hphaseCost :
            Policy.qftPhaseGateCountFor nm P r xWork zWork hworkspace htwo ≤ Q := by
          rw [Policy.qftPhaseGateCountFor_eq_signed]
          exact hQ _ _ _ (hworkspace.policySignedWorkspaceOK htwo)
            ((Policy.qftPhase_inputSize_le P r xWork zWork hworkspace htwo).trans hsize)
        have hradixCost : qftSplitRadixGateCount r ≤ 3 * (N + 1) :=
          (qftSplitRadixGateCount_le r).trans (Nat.mul_le_mul_left 3 hsize)
        rw [Policy.qftPlanGateCountFor_split nm P r xWork zWork hworkspace htwo]
        omega
      · rw [Policy.qftPlanGateCountFor_one nm P r xWork zWork hworkspace (by omega)]
        omega

/-! ## The binary recurrence -/

/-- The QFT plan costs `O(n ^ α)` whenever the phase product does, for any exponent `α` above
one. -/
theorem Policy.qftPlanGateCountFor_bound (α : ℝ) (hα : 1 < α)
    (hPhase : ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 1 ≤ n₀ ∧
      ∀ (φ : Angle) (x z : ExtReg), Policy.WorkspaceOK P x z →
        n₀ ≤ max (ExtReg.width x) (ExtReg.width z) →
        (Policy.signedPhaseProductGateCountFor nm P φ x z : ℝ)
          ≤ C * Real.rpow ((max (ExtReg.width x) (ExtReg.width z) : ℕ) : ℝ) α) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (r xWork zWork : Reg) (hworkspace : Policy.QFTWorkspaceOK P r xWork zWork),
        1 ≤ regSize r →
        (Policy.qftPlanGateCountFor nm P r xWork zWork hworkspace : ℝ)
          ≤ C * Real.rpow (regSize r : ℝ) α := by
  have hα0 : 0 ≤ α := le_of_lt (lt_trans zero_lt_one hα)
  obtain ⟨ρ, hρ0, hρ1, hcontract⟩ := rpow_half_contraction α hα
  obtain ⟨Cφ, hCφ, n₀, hn₀, hPh⟩ := hPhase
  obtain ⟨D, hD⟩ := Policy.qftPlanGateCountFor_bounded nm P (max 2 (2 * n₀))
  have hdelta : 0 < 1 - ρ := sub_pos.mpr hρ1
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = max (D : ℝ) ((Cφ + 3) / (1 - ρ)) + 1 := ⟨_, rfl⟩
  have hDleC : (D : ℝ) ≤ C := by
    have := le_max_left (D : ℝ) ((Cφ + 3) / (1 - ρ)); rw [hCdef]; linarith
  have hC : 0 < C := by
    have hD0 : (0 : ℝ) ≤ (D : ℝ) := by positivity
    have := le_max_left (D : ℝ) ((Cφ + 3) / (1 - ρ)); rw [hCdef]; linarith
  have hfrac : (Cφ + 3) / (1 - ρ) ≤ C := by
    have := le_max_right (D : ℝ) ((Cφ + 3) / (1 - ρ)); rw [hCdef]; linarith
  have habsorb : ρ * C + (Cφ + 3) ≤ C := by
    have := (div_le_iff₀ hdelta).1 hfrac
    nlinarith
  refine ⟨C, hC, ?_⟩
  suffices hall : ∀ n : ℕ, 1 ≤ n →
      ∀ (r xWork zWork : Reg) (hworkspace : Policy.QFTWorkspaceOK P r xWork zWork),
        regSize r = n →
        (Policy.qftPlanGateCountFor nm P r xWork zWork hworkspace : ℝ)
          ≤ C * Real.rpow (n : ℝ) α from
    fun r xWork zWork hworkspace hn => hall (regSize r) hn r xWork zWork hworkspace rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn r xWork zWork hworkspace hrSize
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hp1 : 1 ≤ Real.rpow (n : ℝ) α := Real.one_le_rpow hnR hα0
    have hpn : (n : ℝ) ≤ Real.rpow (n : ℝ) α := Real.self_le_rpow_of_one_le hnR hα.le
    by_cases hsmall : n < max 2 (2 * n₀)
    · have hcost : (Policy.qftPlanGateCountFor nm P r xWork zWork hworkspace : ℝ) ≤ (D : ℝ) := by
        exact_mod_cast hD r xWork zWork hworkspace (by omega)
      nlinarith [hcost, hDleC, hp1, hC]
    · have htwo : 2 ≤ regSize r := by omega
      have hleftSize : regSize (leftReg r) = n / 2 := by rw [regSize_leftReg, hrSize]
      have hrightSize : regSize (rightReg r) = n - n / 2 := by rw [regSize_rightReg, hrSize]
      have hleftBound := ih (n / 2) (by omega) (by omega) (leftReg r) xWork zWork
        (hworkspace.left htwo) hleftSize
      have hrightBound := ih (n - n / 2) (by omega) (by omega) (rightReg r) xWork zWork
        (hworkspace.right htwo) hrightSize
      have hphase : (Policy.qftPhaseGateCountFor nm P r xWork zWork hworkspace htwo : ℝ)
          ≤ Cφ * Real.rpow (n : ℝ) α := by
        rw [Policy.qftPhaseGateCountFor_eq_signed]
        have hlow := Policy.qftPhase_half_le_inputSize P r xWork zWork hworkspace htwo
        have hhigh := Policy.qftPhase_inputSize_le P r xWork zWork hworkspace htwo
        have hb := hPh (qftPhi (regSize r)) _ _ (hworkspace.policySignedWorkspaceOK htwo)
          (show n₀ ≤ phaseInputSize _ _ by omega)
        refine hb.trans (mul_le_mul_of_nonneg_left ?_ hCφ.le)
        exact Real.rpow_le_rpow (by positivity)
          (by exact_mod_cast (show phaseInputSize _ _ ≤ n by omega)) hα0
      have hradix : (qftSplitRadixGateCount r : ℝ) ≤ 3 * Real.rpow (n : ℝ) α := by
        have h := qftSplitRadixGateCount_le r
        rw [hrSize] at h
        have hR : (qftSplitRadixGateCount r : ℝ) ≤ 3 * (n : ℝ) := by exact_mod_cast h
        linarith
      have hsplit := Policy.qftPlanGateCountFor_split nm P r xWork zWork hworkspace htwo
      have hsplitR : (Policy.qftPlanGateCountFor nm P r xWork zWork hworkspace : ℝ)
          = (Policy.qftPlanGateCountFor nm P (rightReg r) xWork zWork (hworkspace.right htwo) : ℝ)
            + (Policy.qftPhaseGateCountFor nm P r xWork zWork hworkspace htwo : ℝ)
            + (Policy.qftPlanGateCountFor nm P (leftReg r) xWork zWork (hworkspace.left htwo) : ℝ)
            + (qftSplitRadixGateCount r : ℝ) := by
        exact_mod_cast hsplit
      have hchildren := mul_le_mul_of_nonneg_left (hcontract n (by omega)) hC.le
      have hfinal := mul_le_mul_of_nonneg_right habsorb (le_trans zero_le_one hp1)
      rw [hsplitR]
      linarith

/-! ## The lowered QFT -/

/-- **The QFT gate count under a policy**: at most a constant times `n ^ P.gateExponent`. -/
theorem Policy.lowerQFT_gateCountFor_bound (hP : P.Admissible) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 1 ≤ n₀ ∧
      ∀ (r : ExtReg) (hworkspace : Policy.QFTReserveOK P r), n₀ ≤ r.width →
        (LowGate.gateCount (shorGateCostModelFor nm) (Policy.lowerQFT P r hworkspace) : ℝ)
          ≤ C * Real.rpow (r.width : ℝ) P.gateExponent := by
  obtain ⟨C, hC, hbound⟩ := Policy.qftPlanGateCountFor_bound nm P P.gateExponent
    P.one_lt_gateExponent (Policy.signedPhaseProductGateCountFor_gateExponent_bound nm P hP)
  exact ⟨C, hC, 1, le_rfl, fun r hworkspace hn =>
    hbound r.active (Policy.qftXWork P r) (Policy.qftZWork P r) hworkspace.explicitWorkspace hn⟩

end PolicyQFTGateCount

end Shor
