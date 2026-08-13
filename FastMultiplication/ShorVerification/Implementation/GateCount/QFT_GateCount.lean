import FastMultiplication.ShorVerification.Implementation.GateCount.PhaseProduct.Main
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.GateConstructions
import FastMultiplication.ShorVerification.Implementation.GateCount.Lemmas.LowGateCount

open Shor

namespace Shor

/-! =========================================================
    QFT Gate-Count Bound

This file proves the asymptotic gate-count bound for the plan-directed exact-QFT
lowering. The proof reduces the QFT recurrence to the already established
PhaseProduct bound, controls the split/radix overhead, and solves the resulting
binary divide-and-conquer recurrence.
========================================================= -/

/-! ---------------------------------------------------------
    QFT split geometry

The exact QFT lowering recursively splits the active register in half. These
lemmas collect the register-size and disjointness facts needed by both the
structural recurrence and the phase-product bridge.
--------------------------------------------------------- -/

section SplitGeometry

/-- The left recursive QFT register has floor-half of the input width. -/
@[simp] lemma regSize_qftLeftReg (r : Reg) :
    regSize (qftLeftReg r) = regSize r / 2 := by
  simp [qftLeftReg]

/-- The right recursive QFT register contains the remaining high half. -/
@[simp] lemma regSize_qftRightReg (r : Reg) :
    regSize (qftRightReg r) = regSize r - regSize r / 2 := by
  simp [qftRightReg]

/-- The two recursive halves of a QFT split occupy disjoint qubits. -/
lemma qftSplit_disjoint (r : Reg) :
    Disjoint (qftLeftReg r) (qftRightReg r) := by
  simpa [qftLeftReg, qftRightReg] using disjoint_left_right r

/-- When the input has at least two qubits, both recursive QFT children are strictly smaller. -/
lemma qftSplit_strictly_smaller
    (r : Reg)
    (hsize : 2 ≤ regSize r) :
    regSize (qftLeftReg r) < regSize r ∧
    regSize (qftRightReg r) < regSize r := by
  rw [regSize_qftLeftReg, regSize_qftRightReg]
  constructor
  · exact Nat.div_lt_self (by omega) (by omega)
  · have hpos : 0 < regSize r / 2 := Nat.div_pos hsize (by omega)
    omega

/-- The PhaseProduct call spawned by a split has input size between half and the full QFT width. -/
lemma qftSplit_phase_size_bounds (r : Reg) :
    regSize r / 2
        ≤ max (regSize (qftLeftReg r)) (regSize (qftRightReg r))
    ∧
      max (regSize (qftLeftReg r)) (regSize (qftRightReg r))
        ≤ regSize r := by
  rw [regSize_qftLeftReg, regSize_qftRightReg]
  constructor
  · exact Nat.le_max_left _ _
  · apply max_le
    · exact Nat.div_le_self _ _
    · exact Nat.sub_le _ _

end SplitGeometry

/-! ---------------------------------------------------------
    Explicit cost functions and exact unfoldings

The recursive QFT plan is easier to estimate through concrete natural-valued
cost functions. This section records the exact equations for base cases, split
nodes, and the PhaseProduct gate embedded at each split.
--------------------------------------------------------- -/

section ExplicitCosts

/-- Concrete low-gate count of the standard exact-QFT lowering plan. -/
noncomputable def explicitQFTGateCount
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ) (hk : 1 < k) (ops : Prog k)
    (r xWork zWork : Reg)
    (hworkspace : QFTWorkspaceOK ops r xWork zWork) : ℕ :=
  LowGate.gateCount shorGateCostModel
    (lowerQFTPlan (standardQFTLoweringPlan k hk ops r xWork zWork hworkspace))

/-- Concrete low-gate count of the PhaseProduct node used at a nontrivial QFT split. -/
noncomputable def explicitQFTPhaseGateCount
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ) (hk : 1 < k) (ops : Prog k)
    (r xWork zWork : Reg)
    (hworkspace : QFTWorkspaceOK ops r xWork zWork)
    (hsize : 2 ≤ regSize r) : ℕ :=
  LowGate.gateCount shorGateCostModel
    (lowerGateRec
      (standardPhaseProdUsingPlan k hk ops (qftPhi (regSize r))
        (hworkspace.phaseWorkspace hsize)
        (hworkspace.signedWorkspaceOK hsize)))

/-- Reidentifies the planned PhaseProduct node with the public `lowerGate` entry point. -/
lemma explicitQFTPhaseGateCount_eq_lowerGate
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ) (hk : 1 < k) (ops : Prog k)
    (φ : ℝ) (x z : Reg)
    (ws : Gate.PhaseProdWorkspace x z)
    (hsigned : SignedRecursiveWorkspaceOK ops (ws.xExt.grow 1) (ws.zExt.grow 1)) :
    LowGate.gateCount shorGateCostModel
        (lowerGateRec (standardPhaseProdUsingPlan k hk ops φ ws hsigned))
      =
    LowGate.gateCount shorGateCostModel
        (lowerGate (Basis := Basis) k hk ops
          (Gate.PhaseProdUsing φ x z ws)
          (by simpa [GateWorkspaceOK, Gate.PhaseProdUsing] using hsigned)) := by
  simp [standardPhaseProdUsingPlan, Gate.PhaseProdUsing, lowerGate,
    lowerGateRec, lowerSignedPhaseProdWithWorkspace]
  congr

/-- Rewrites the split PhaseProduct node as the signed PhaseProduct recurrence cost. -/
lemma explicitQFTPhaseGateCount_eq_signed
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ) (hk : 1 < k) (ops : Prog k)
    (r xWork zWork : Reg)
    (hworkspace : QFTWorkspaceOK ops r xWork zWork)
    (hsize : 2 ≤ regSize r) :
    explicitQFTPhaseGateCount (Basis := Basis) k hk ops r xWork zWork hworkspace hsize
      =
    signedPhaseProductGateCount (Basis := Basis) k hk ops (qftPhi (regSize r))
      ((hworkspace.phaseWorkspace hsize).xExt.grow 1)
      ((hworkspace.phaseWorkspace hsize).zExt.grow 1)
      (hworkspace.signedWorkspaceOK hsize) := by
  let ws := hworkspace.phaseWorkspace hsize
  let hsigned : SignedRecursiveWorkspaceOK ops (ws.xExt.grow 1) (ws.zExt.grow 1) :=
    hworkspace.signedWorkspaceOK hsize
  let hgate :
      GateWorkspaceOK ops
        (Gate.PhaseProdUsing (qftPhi (regSize r)) (leftReg r) (rightReg r) ws) := by
    simpa [GateWorkspaceOK, Gate.PhaseProdUsing] using hsigned
  calc
    explicitQFTPhaseGateCount (Basis := Basis) k hk ops r xWork zWork hworkspace hsize
        =
      LowGate.gateCount shorGateCostModel
        (lowerGate (Basis := Basis) k hk ops
          (Gate.PhaseProdUsing (qftPhi (regSize r)) (leftReg r) (rightReg r) ws)
          hgate) := by
            simpa [explicitQFTPhaseGateCount, ws, hsigned, hgate] using
              explicitQFTPhaseGateCount_eq_lowerGate
                (Basis := Basis) k hk ops (qftPhi (regSize r))
                (leftReg r) (rightReg r) ws hsigned
    _ =
      signedPhaseProductGateCount (Basis := Basis) k hk ops (qftPhi (regSize r))
        (ws.xExt.grow 1) (ws.zExt.grow 1)
        (phaseProdUsing_signedWorkspace ops (qftPhi (regSize r))
          (leftReg r) (rightReg r) ws hgate) :=
      lowerGate_PhaseProdUsing_gateCount_eq_signed
        (Basis := Basis) k hk ops (qftPhi (regSize r))
        (leftReg r) (rightReg r) ws hgate
    _ =
      signedPhaseProductGateCount (Basis := Basis) k hk ops (qftPhi (regSize r))
        ((hworkspace.phaseWorkspace hsize).xExt.grow 1)
        ((hworkspace.phaseWorkspace hsize).zExt.grow 1)
        (hworkspace.signedWorkspaceOK hsize) := by
          congr

/-- Exact cost decomposition for a nontrivial QFT split: right child, PhaseProduct, left child, then radix overhead. -/
lemma explicitQFTGateCount_split
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ) (hk : 1 < k) (ops : Prog k)
    (r xWork zWork : Reg)
    (hworkspace : QFTWorkspaceOK ops r xWork zWork)
    (hsize : 2 ≤ regSize r) :
    explicitQFTGateCount (Basis := Basis) k hk ops r xWork zWork hworkspace
      =
    explicitQFTGateCount (Basis := Basis) k hk ops (rightReg r) xWork zWork
        (hworkspace.right hsize)
      +
    explicitQFTPhaseGateCount (Basis := Basis) k hk ops r xWork zWork hworkspace hsize
      +
    explicitQFTGateCount (Basis := Basis) k hk ops (leftReg r) xWork zWork
        (hworkspace.left hsize)
      +
    qftSplitRadixGateCount r := by
  have hplan :
      standardQFTLoweringPlan k hk ops r xWork zWork hworkspace =
        QFTLoweringPlan.split r hsize
          (hworkspace.phaseWorkspace hsize)
          (phaseProdUsingInputSize (hworkspace.phaseWorkspace hsize))
          (standardPhaseProdUsingPlan k hk ops (qftPhi (regSize r))
            (hworkspace.phaseWorkspace hsize)
            (hworkspace.signedWorkspaceOK hsize))
          (standardQFTLoweringPlan k hk ops (rightReg r) xWork zWork
            (hworkspace.right hsize))
          (standardQFTLoweringPlan k hk ops (leftReg r) xWork zWork
            (hworkspace.left hsize)) := by
    rw [standardQFTLoweringPlan]
    simp [show regSize r ≠ 0 by omega, show regSize r ≠ 1 by omega]
  unfold explicitQFTGateCount
  rw [hplan]
  simp only [lowerQFTPlan, LowGate.gateCount_seq_eq]
  unfold explicitQFTPhaseGateCount qftSplitRadixGateCount qftHalfWidth
  omega

/-- The empty-register QFT plan has zero cost. -/
lemma explicitQFTGateCount_zero
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ) (hk : 1 < k) (ops : Prog k)
    (r xWork zWork : Reg)
    (hworkspace : QFTWorkspaceOK ops r xWork zWork)
    (hzero : regSize r = 0) :
    explicitQFTGateCount (Basis := Basis) k hk ops r xWork zWork hworkspace = 0 := by
  have hplan :
      standardQFTLoweringPlan k hk ops r xWork zWork hworkspace =
        QFTLoweringPlan.empty r hzero := by
    rw [standardQFTLoweringPlan]
    simp [hzero]
  simp [explicitQFTGateCount, hplan, lowerQFTPlan]

/-- A one-qubit QFT plan is exactly one Hadamard-cost gate. -/
lemma explicitQFTGateCount_one
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ) (hk : 1 < k) (ops : Prog k)
    (r xWork zWork : Reg)
    (hworkspace : QFTWorkspaceOK ops r xWork zWork)
    (hone : regSize r = 1) :
    explicitQFTGateCount (Basis := Basis) k hk ops r xWork zWork hworkspace = 1 := by
  have hplan :
      standardQFTLoweringPlan k hk ops r xWork zWork hworkspace =
        QFTLoweringPlan.singleton r hone := by
    rw [standardQFTLoweringPlan]
    simp [hone]
  simp [explicitQFTGateCount, hplan, lowerQFTPlan,
    shorGateCostModel, phaseProductCostModel]

end ExplicitCosts

/-! ---------------------------------------------------------
    Phase and radix overhead estimates

This section bounds the two nonrecursive costs at each QFT split: the embedded
PhaseProduct call and the fixed split/radix bookkeeping. Both are measured
against the PhaseProduct comparison rate.
--------------------------------------------------------- -/

section SplitOverheadBounds

/-- The PhaseProduct comparison rate is monotone in the register width. -/
lemma phaseProductGateRate_mono
    (k : ℕ)
    (hk : 1 < k)
    {m n : ℕ}
    (hmn : m ≤ n) :
    phaseProductGateRate k m ≤ phaseProductGateRate k n := by
  have hα : 0 ≤ phaseProductExponent k := by
    linarith [one_lt_phaseProductExponent k hk]
  unfold phaseProductGateRate
  exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hmn) hα

/-- Eventually, the embedded PhaseProduct node is bounded by the PhaseProduct rate at the parent QFT width. -/
lemma explicitQFTPhaseGateCount_eventually_le
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (hPhase : PhaseProductGateCountBound (Basis := Basis) k hk ops) :
    ∃ Cφ : ℝ, 0 < Cφ ∧
    ∃ Nφ : ℕ, 2 ≤ Nφ ∧
      ∀ (r xWork zWork : Reg)
        (hworkspace : QFTWorkspaceOK ops r xWork zWork)
        (hsize : 2 ≤ regSize r),
        Nφ ≤ regSize r →
        (explicitQFTPhaseGateCount (Basis := Basis)
          k hk ops r xWork zWork hworkspace hsize : ℝ)
          ≤ Cφ * phaseProductGateRate k (regSize r) := by
  rcases hPhase with ⟨Cφ, hCφ, n₀, hn₀, hPhase⟩
  refine ⟨Cφ, hCφ, max 2 (2 * n₀), by omega, ?_⟩
  intro r xWork zWork hworkspace hsize hn
  let ws := hworkspace.phaseWorkspace hsize
  let hsigned : SignedRecursiveWorkspaceOK ops (ws.xExt.grow 1) (ws.zExt.grow 1) :=
    hworkspace.signedWorkspaceOK hsize
  let hgate :
      GateWorkspaceOK ops
        (Gate.PhaseProdUsing (qftPhi (regSize r)) (leftReg r) (rightReg r) ws) := by
    simpa [GateWorkspaceOK, Gate.PhaseProdUsing] using hsigned
  have hleftLarge : n₀ ≤ regSize r / 2 := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
    omega
  have hchildLarge :
      n₀ ≤ max (regSize (leftReg r)) (regSize (rightReg r)) := by
    rw [regSize_leftReg]
    exact hleftLarge.trans (Nat.le_max_left _ _)
  have hnode :=
    hPhase (qftPhi (regSize r)) (leftReg r) (rightReg r) ws hgate hchildLarge
  have hsizeLe :
      max (regSize (leftReg r)) (regSize (rightReg r)) ≤ regSize r := by
    simpa [qftLeftReg, qftRightReg] using (qftSplit_phase_size_bounds r).2
  have hrate := phaseProductGateRate_mono k hk hsizeLe
  have hplanEq :
      explicitQFTPhaseGateCount (Basis := Basis)
          k hk ops r xWork zWork hworkspace hsize
        =
      LowGate.gateCount shorGateCostModel
        (lowerGate (Basis := Basis) k hk ops
          (Gate.PhaseProdUsing (qftPhi (regSize r)) (leftReg r) (rightReg r) ws)
          hgate) := by
    simpa [explicitQFTPhaseGateCount, ws, hsigned, hgate] using
      explicitQFTPhaseGateCount_eq_lowerGate
        (Basis := Basis) k hk ops (qftPhi (regSize r))
        (leftReg r) (rightReg r) ws hsigned
  rw [hplanEq]
  exact hnode.trans (mul_le_mul_of_nonneg_left hrate (le_of_lt hCφ))

/-- The fixed radix-reversal and split bookkeeping cost is linear in the QFT width. -/
lemma qftSplitRadixGateCount_le
    (r : Reg) :
    qftSplitRadixGateCount r ≤ 3 * regSize r := by
  unfold qftSplitRadixGateCount qftHalfWidth
  simp [LowGate.gateCount, shorGateCostModel, phaseProductCostModel,
    radixReverseGateCount]
  have hdiv : regSize r / 2 / 2 ≤ regSize r :=
    (Nat.div_le_self _ _).trans (Nat.div_le_self _ _)
  exact hdiv

/-- The linear split/radix overhead is eventually absorbed by the PhaseProduct comparison rate. -/
lemma qftSplitRadixGateCount_eventually_le
    (k : ℕ)
    (hk : 1 < k) :
    ∃ Cr : ℝ, 0 < Cr ∧
    ∃ Nr : ℕ, 1 ≤ Nr ∧
      ∀ r : Reg,
        Nr ≤ regSize r →
        (qftSplitRadixGateCount r : ℝ)
          ≤ Cr * phaseProductGateRate k (regSize r) := by
  refine ⟨3, by norm_num, 1, by omega, ?_⟩
  intro r hn
  have hcost := qftSplitRadixGateCount_le r
  have hn' : (regSize r : ℝ) ≤ phaseProductGateRate k (regSize r) := by
    simpa [phaseProductGateRate] using natCast_le_phaseProduct_rpow k hk hn
  have hcostR :
      (qftSplitRadixGateCount r : ℝ) ≤ ((3 * regSize r : ℕ) : ℝ) := by
    exact_mod_cast hcost
  calc
    (qftSplitRadixGateCount r : ℝ)
        ≤ ((3 * regSize r : ℕ) : ℝ) := hcostR
    _ = 3 * (regSize r : ℝ) := by norm_num
    _ ≤ 3 * phaseProductGateRate k (regSize r) :=
      mul_le_mul_of_nonneg_left hn' (by norm_num)

end SplitOverheadBounds

/-! ---------------------------------------------------------
    Bounded base cases and the one-level QFT recurrence

The recurrence solver needs finite boundedness below a cutoff and a one-step
estimate above the cutoff. These lemmas extract exactly those two hypotheses
from the explicit QFT equations and the PhaseProduct bound.
--------------------------------------------------------- -/

section FiniteBasesAndOneStep

/-- PhaseProduct costs appearing in QFT splits are uniformly bounded on bounded parent sizes. -/
lemma explicitQFTPhaseGateCount_bounded_on_bounded_sizes
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (N : ℕ) :
    ∃ P : ℕ,
      ∀ (r xWork zWork : Reg)
        (hworkspace : QFTWorkspaceOK ops r xWork zWork)
        (hsize : 2 ≤ regSize r),
        regSize r ≤ N →
        explicitQFTPhaseGateCount (Basis := Basis)
          k hk ops r xWork zWork hworkspace hsize ≤ P := by
  rcases signedPhaseProductGateCount_bounded_on_bounded_inputs
      (Basis := Basis) k hk ops (N + 1) with ⟨P, hP⟩
  refine ⟨P, ?_⟩
  intro r xWork zWork hworkspace hsize hr
  rw [explicitQFTPhaseGateCount_eq_signed]
  apply hP
  rw [phaseInputSize_phaseProdUsing]
  have hmax :
      max (regSize (leftReg r)) (regSize (rightReg r)) ≤ N := by
    have := (qftSplit_phase_size_bounds r).2.trans hr
    simpa [qftLeftReg, qftRightReg] using this
  omega

/-- Explicit QFT costs are uniformly bounded on every finite range of input widths. -/
lemma explicitQFTGateCount_bounded_on_bounded_sizes
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (N : ℕ) :
    ∃ D : ℕ,
      ∀ (r xWork zWork : Reg)
        (hworkspace : QFTWorkspaceOK ops r xWork zWork),
        regSize r ≤ N →
        explicitQFTGateCount (Basis := Basis)
          k hk ops r xWork zWork hworkspace ≤ D := by
  induction N with
  | zero =>
      refine ⟨0, ?_⟩
      intro r xWork zWork hworkspace hsize
      rw [explicitQFTGateCount_zero
        (Basis := Basis) k hk ops r xWork zWork hworkspace (by omega)]
  | succ N ih =>
      rcases ih with ⟨D, hD⟩
      rcases explicitQFTPhaseGateCount_bounded_on_bounded_sizes
          (Basis := Basis) k hk ops (N + 1) with ⟨P, hP⟩
      let B : ℕ := max D (2 * D + P + 3 * (N + 1))
      refine ⟨B, ?_⟩
      intro r xWork zWork hworkspace hsize
      by_cases hprevious : regSize r ≤ N
      · exact (hD r xWork zWork hworkspace hprevious).trans (Nat.le_max_left _ _)
      · have hrSize : regSize r = N + 1 := by omega
        by_cases htwo : 2 ≤ regSize r
        · have hsmaller := qftSplit_strictly_smaller r htwo
          have hleftN : regSize (leftReg r) ≤ N := by
            have hleftLt : regSize (leftReg r) < regSize r := by
              simpa [qftLeftReg] using hsmaller.1
            omega
          have hrightN : regSize (rightReg r) ≤ N := by
            have hrightLt : regSize (rightReg r) < regSize r := by
              simpa [qftRightReg] using hsmaller.2
            omega
          have hleftCost :=
            hD (leftReg r) xWork zWork (hworkspace.left htwo) hleftN
          have hrightCost :=
            hD (rightReg r) xWork zWork (hworkspace.right htwo) hrightN
          have hphaseCost := hP r xWork zWork hworkspace htwo hsize
          have hradixCost :
              qftSplitRadixGateCount r ≤ 3 * (N + 1) := by
            exact (qftSplitRadixGateCount_le r).trans
              (Nat.mul_le_mul_left 3 hsize)
          rw [explicitQFTGateCount_split
            (Basis := Basis) k hk ops r xWork zWork hworkspace htwo]
          dsimp [B]
          apply le_trans (show
              explicitQFTGateCount (Basis := Basis) k hk ops
                    (rightReg r) xWork zWork (hworkspace.right htwo)
                + explicitQFTPhaseGateCount (Basis := Basis) k hk ops
                    r xWork zWork hworkspace htwo
                + explicitQFTGateCount (Basis := Basis) k hk ops
                    (leftReg r) xWork zWork (hworkspace.left htwo)
                + qftSplitRadixGateCount r
              ≤ 2 * D + P + 3 * (N + 1) by omega)
          exact Nat.le_max_right _ _
        · have hrOne : regSize r = 1 := by omega
          rw [explicitQFTGateCount_one
            (Basis := Basis) k hk ops r xWork zWork hworkspace hrOne]
          dsimp [B]
          apply le_trans (show 1 ≤ 2 * D + P + 3 * (N + 1) by omega)
          exact Nat.le_max_right _ _

/-- One QFT split costs its two recursive children plus one PhaseProduct-rate overhead term. -/
lemma explicitQFTGateCount_one_level_recurrence
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (hPhase : PhaseProductGateCountBound (Basis := Basis) k hk ops) :
    ∃ A : ℝ, 0 < A ∧
    ∃ N : ℕ, 2 ≤ N ∧
      ∀ (r xWork zWork : Reg)
        (hworkspace : QFTWorkspaceOK ops r xWork zWork)
        (hsize : 2 ≤ regSize r),
        N ≤ regSize r →
        (explicitQFTGateCount (Basis := Basis)
          k hk ops r xWork zWork hworkspace : ℝ)
          ≤
        (explicitQFTGateCount (Basis := Basis)
          k hk ops (rightReg r) xWork zWork
          (hworkspace.right hsize) : ℝ)
          +
        (explicitQFTGateCount (Basis := Basis)
          k hk ops (leftReg r) xWork zWork
          (hworkspace.left hsize) : ℝ)
          +
        A * phaseProductGateRate k (regSize r) := by
  rcases explicitQFTPhaseGateCount_eventually_le
      (Basis := Basis) k hk ops hPhase with
    ⟨Cφ, hCφ, Nφ, hNφ, hPhaseNode⟩
  rcases qftSplitRadixGateCount_eventually_le k hk with
    ⟨Cr, hCr, Nr, hNr, hRadixNode⟩
  refine ⟨Cφ + Cr, by linarith, max Nφ Nr, by omega, ?_⟩
  intro r xWork zWork hworkspace htwo hn
  have hnφ : Nφ ≤ regSize r :=
    le_trans (Nat.le_max_left Nφ Nr) hn
  have hnr : Nr ≤ regSize r :=
    le_trans (Nat.le_max_right Nφ Nr) hn
  have hsplit := explicitQFTGateCount_split
    (Basis := Basis) k hk ops r xWork zWork hworkspace htwo
  have hphase := hPhaseNode r xWork zWork hworkspace htwo hnφ
  have hradix := hRadixNode r hnr
  rw [hsplit]
  push_cast
  linarith

end FiniteBasesAndOneStep

/-! ---------------------------------------------------------
    Binary recurrence solution

This section proves that the two half-size recursive calls contract under the
PhaseProduct exponent and then solves the explicit QFT recurrence by strong
induction.
--------------------------------------------------------- -/

section BinaryRecurrenceSolution

/-- The two half-size PhaseProduct rates sum to a strict contraction of the parent rate. -/
lemma qft_half_rate_contraction
    (k : ℕ)
    (_hk : 1 < k)
    (hα : 1 < phaseProductExponent k) :
    ∃ ρ : ℝ,
      0 ≤ ρ ∧ ρ < 1 ∧
      ∀ n : ℕ,
        2 ≤ n →
        phaseProductGateRate k (n / 2)
          + phaseProductGateRate k (n - n / 2)
          ≤ ρ * phaseProductGateRate k n := by
  let α : ℝ := phaseProductExponent k
  let ρ : ℝ :=
    Real.rpow (1 / 3 : ℝ) α + Real.rpow (2 / 3 : ℝ) α
  have hα' : 1 < α := by simpa [α] using hα
  have hρnonneg : 0 ≤ ρ := by
    dsimp [ρ]
    positivity
  have hthird :
      Real.rpow (1 / 3 : ℝ) α < (1 / 3 : ℝ) := by
    exact Real.rpow_lt_self_of_lt_one (by norm_num) (by norm_num) hα'
  have htwoThirds :
      Real.rpow (2 / 3 : ℝ) α < (2 / 3 : ℝ) := by
    exact Real.rpow_lt_self_of_lt_one (by norm_num) (by norm_num) hα'
  have hρlt : ρ < 1 := by
    have hsum :
        Real.rpow (1 / 3 : ℝ) α + Real.rpow (2 / 3 : ℝ) α
          < (1 / 3 : ℝ) + (2 / 3 : ℝ) :=
      add_lt_add hthird htwoThirds
    norm_num at hsum
    simpa [ρ] using hsum
  refine ⟨ρ, hρnonneg, hρlt, ?_⟩
  intro n hn
  let a : ℕ := n / 2
  let b : ℕ := n - a
  have hnpos : 0 < n := by omega
  have haPos : 0 < a := by
    dsimp [a]
    exact Nat.div_pos hn (by omega)
  have haLe : a ≤ n := by
    dsimp [a]
    exact Nat.div_le_self _ _
  have hbPos : 0 < b := by
    dsimp [b]
    omega
  have hab : a + b = n := by
    dsimp [b]
    omega
  have htwoA : 2 * a ≤ n := by
    dsimp [a]
    simpa using Nat.mul_div_le n 2
  have hmod : n % 2 < 2 := Nat.mod_lt n (by omega)
  have hdecomp : n % 2 + 2 * a = n := by
    dsimp [a]
    simpa using Nat.mod_add_div n 2
  have hnLeThreeA : n ≤ 3 * a := by omega
  have hthreeALeTwoN : 3 * a ≤ 2 * n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  let t : ℝ := (a : ℝ) / (n : ℝ)
  have htLower : (1 / 3 : ℝ) ≤ t := by
    dsimp [t]
    have hcast : (n : ℝ) ≤ 3 * (a : ℝ) := by
      exact_mod_cast hnLeThreeA
    rw [le_div_iff₀ hnR]
    nlinarith
  have htUpper : t ≤ (2 / 3 : ℝ) := by
    dsimp [t]
    apply (div_le_iff₀ hnR).2
    have hcast : 3 * (a : ℝ) ≤ 2 * (n : ℝ) := by
      exact_mod_cast hthreeALeTwoN
    linarith
  let lam : ℝ := 2 - 3 * t
  let μ : ℝ := 3 * t - 1
  have hlam : 0 ≤ lam := by
    dsimp [lam]
    linarith
  have hμ : 0 ≤ μ := by
    dsimp [μ]
    linarith
  have hlamμ : lam + μ = 1 := by
    dsimp [lam, μ]
    ring
  have hμlam : μ + lam = 1 := by linarith [hlamμ]
  have htCombination :
      lam * (1 / 3 : ℝ) + μ * (2 / 3 : ℝ) = t := by
    dsimp [lam, μ]
    ring
  have honeMinusCombination :
      μ * (1 / 3 : ℝ) + lam * (2 / 3 : ℝ) = 1 - t := by
    dsimp [lam, μ]
    ring
  have hconvex := convexOn_rpow (p := α) (le_of_lt hα')
  have htPow :
      Real.rpow t α
        ≤ lam * Real.rpow (1 / 3 : ℝ) α
          + μ * Real.rpow (2 / 3 : ℝ) α := by
    have hc :=
      hconvex.right
        (show (1 / 3 : ℝ) ∈ Set.Ici (0 : ℝ) by norm_num)
        (show (2 / 3 : ℝ) ∈ Set.Ici (0 : ℝ) by norm_num)
        hlam hμ hlamμ
    rw [← htCombination]
    simpa [smul_eq_mul] using hc
  have honeMinusPow :
      Real.rpow (1 - t) α
        ≤ μ * Real.rpow (1 / 3 : ℝ) α
          + lam * Real.rpow (2 / 3 : ℝ) α := by
    have hc :=
      hconvex.right
        (show (1 / 3 : ℝ) ∈ Set.Ici (0 : ℝ) by norm_num)
        (show (2 / 3 : ℝ) ∈ Set.Ici (0 : ℝ) by norm_num)
        hμ hlam hμlam
    rw [← honeMinusCombination]
    simpa [smul_eq_mul] using hc
  have hnormalized :
      Real.rpow t α + Real.rpow (1 - t) α ≤ ρ := by
    calc
      Real.rpow t α + Real.rpow (1 - t) α
          ≤
        (lam * Real.rpow (1 / 3 : ℝ) α
            + μ * Real.rpow (2 / 3 : ℝ) α)
          +
        (μ * Real.rpow (1 / 3 : ℝ) α
            + lam * Real.rpow (2 / 3 : ℝ) α) :=
        add_le_add htPow honeMinusPow
      _ =
        (lam + μ) *
          (Real.rpow (1 / 3 : ℝ) α + Real.rpow (2 / 3 : ℝ) α) := by
        ring
      _ = ρ := by
        rw [hlamμ, one_mul]
  have hbCast : (b : ℝ) = (n : ℝ) - (a : ℝ) := by
    dsimp [b]
    rw [Nat.cast_sub haLe]
  have hbRatio : (b : ℝ) / (n : ℝ) = 1 - t := by
    dsimp [t]
    rw [hbCast]
    field_simp [ne_of_gt hnR]
  have htMul : t * (n : ℝ) = (a : ℝ) := by
    dsimp [t]
    field_simp [ne_of_gt hnR]
  have honeMinusMul : (1 - t) * (n : ℝ) = (b : ℝ) := by
    rw [← hbRatio]
    field_simp [ne_of_gt hnR]
  have htNonneg : 0 ≤ t := by linarith [htLower]
  have honeMinusNonneg : 0 ≤ 1 - t := by linarith [htUpper]
  have haPow :
      Real.rpow (a : ℝ) α =
        Real.rpow t α * Real.rpow (n : ℝ) α := by
    have hmul := Real.mul_rpow htNonneg (le_of_lt hnR) (z := α)
    rw [htMul] at hmul
    exact hmul
  have hbPow :
      Real.rpow (b : ℝ) α =
        Real.rpow (1 - t) α * Real.rpow (n : ℝ) α := by
    have hmul :=
      Real.mul_rpow honeMinusNonneg (le_of_lt hnR) (z := α)
    rw [honeMinusMul] at hmul
    exact hmul
  change
    Real.rpow (a : ℝ) α + Real.rpow (b : ℝ) α
      ≤ ρ * Real.rpow (n : ℝ) α
  rw [haPow, hbPow]
  calc
    Real.rpow t α * Real.rpow (n : ℝ) α
        + Real.rpow (1 - t) α * Real.rpow (n : ℝ) α
        =
      (Real.rpow t α + Real.rpow (1 - t) α) *
        Real.rpow (n : ℝ) α := by ring
    _ ≤ ρ * Real.rpow (n : ℝ) α :=
      mul_le_mul_of_nonneg_right hnormalized
        (Real.rpow_nonneg (by positivity : 0 ≤ (n : ℝ)) _)

/-- Solves the explicit QFT divide-and-conquer recurrence using the contraction factor. -/
lemma explicitQFT_binary_recurrence_solution
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (hcontract :
      ∃ ρ : ℝ,
        0 ≤ ρ ∧ ρ < 1 ∧
        ∀ n : ℕ,
          2 ≤ n →
          phaseProductGateRate k (n / 2)
            + phaseProductGateRate k (n - n / 2)
            ≤ ρ * phaseProductGateRate k n)
    (hbase :
      ∀ N : ℕ,
        ∃ D : ℕ,
          ∀ (r xWork zWork : Reg)
            (hworkspace : QFTWorkspaceOK ops r xWork zWork),
            regSize r ≤ N →
            explicitQFTGateCount (Basis := Basis)
              k hk ops r xWork zWork hworkspace ≤ D)
    (hstep :
      ∃ A : ℝ, 0 < A ∧
      ∃ N : ℕ, 2 ≤ N ∧
        ∀ (r xWork zWork : Reg)
          (hworkspace : QFTWorkspaceOK ops r xWork zWork)
          (hsize : 2 ≤ regSize r),
          N ≤ regSize r →
          (explicitQFTGateCount (Basis := Basis)
            k hk ops r xWork zWork hworkspace : ℝ)
            ≤
          (explicitQFTGateCount (Basis := Basis)
            k hk ops (rightReg r) xWork zWork
            (hworkspace.right hsize) : ℝ)
            +
          (explicitQFTGateCount (Basis := Basis)
            k hk ops (leftReg r) xWork zWork
            (hworkspace.left hsize) : ℝ)
            +
          A * phaseProductGateRate k (regSize r)) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (r xWork zWork : Reg)
      (hworkspace : QFTWorkspaceOK ops r xWork zWork),
      1 ≤ regSize r →
      (explicitQFTGateCount (Basis := Basis)
        k hk ops r xWork zWork hworkspace : ℝ)
        ≤ C * phaseProductGateRate k (regSize r) := by
  rcases hcontract with ⟨ρ, hρnonneg, hρlt, hcontractBound⟩
  rcases hstep with ⟨A, hA, N, hN, hstepBound⟩
  rcases hbase N with ⟨D, hD⟩
  have hdelta : 0 < 1 - ρ := sub_pos.mpr hρlt
  let C : ℝ := max (D : ℝ) (A / (1 - ρ)) + 1
  have hC : 0 < C := by
    have hDnonneg : 0 ≤ (D : ℝ) := by positivity
    have hmaxNonneg :
        0 ≤ max (D : ℝ) (A / (1 - ρ)) :=
      hDnonneg.trans (le_max_left _ _)
    dsimp [C]
    linarith
  have hDleC : (D : ℝ) ≤ C := by
    have hmax := le_max_left (D : ℝ) (A / (1 - ρ))
    dsimp [C]
    linarith
  have hfracLeC : A / (1 - ρ) ≤ C := by
    have hmax := le_max_right (D : ℝ) (A / (1 - ρ))
    dsimp [C]
    linarith
  have hAle : A ≤ (1 - ρ) * C := by
    have hdiv := (div_le_iff₀ hdelta).1 hfracLeC
    nlinarith
  have habsorb : ρ * C + A ≤ C := by
    nlinarith [hAle]
  have hall :
      ∀ n : ℕ,
        1 ≤ n →
        ∀ (r xWork zWork : Reg)
          (hworkspace : QFTWorkspaceOK ops r xWork zWork),
          regSize r = n →
          (explicitQFTGateCount (Basis := Basis)
            k hk ops r xWork zWork hworkspace : ℝ)
            ≤ C * phaseProductGateRate k n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro hn r xWork zWork hworkspace hrSize
        by_cases hsmall : n < N
        · have hcostNat :
              explicitQFTGateCount (Basis := Basis)
                  k hk ops r xWork zWork hworkspace ≤ D :=
            hD r xWork zWork hworkspace (by omega)
          have hcost :
              (explicitQFTGateCount (Basis := Basis)
                k hk ops r xWork zWork hworkspace : ℝ) ≤ (D : ℝ) := by
            exact_mod_cast hcostNat
          have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          have hnRate :
              (n : ℝ) ≤ phaseProductGateRate k n := by
            simpa [phaseProductGateRate] using
              natCast_le_phaseProduct_rpow k hk hn
          have hrate : (1 : ℝ) ≤ phaseProductGateRate k n :=
            hnR.trans hnRate
          calc
            (explicitQFTGateCount (Basis := Basis)
                k hk ops r xWork zWork hworkspace : ℝ)
                ≤ (D : ℝ) := hcost
            _ ≤ C := hDleC
            _ ≤ C * phaseProductGateRate k n := by
              nlinarith [le_of_lt hC, hrate]
        · have hNn : N ≤ n := Nat.le_of_not_gt hsmall
          have htwo : 2 ≤ n := hN.trans hNn
          have htwoR : 2 ≤ regSize r := by simpa [hrSize] using htwo
          have hsmaller := qftSplit_strictly_smaller r htwoR
          have hleftPos : 1 ≤ regSize (leftReg r) := by
            rw [regSize_leftReg, hrSize]
            exact Nat.div_pos htwo (by omega)
          have hrightPos : 1 ≤ regSize (rightReg r) := by
            rw [regSize_rightReg, hrSize]
            have hhalfPos : 0 < n / 2 := Nat.div_pos htwo (by omega)
            omega
          have hleftLt : regSize (leftReg r) < n := by
            simpa [qftLeftReg, hrSize] using hsmaller.1
          have hrightLt : regSize (rightReg r) < n := by
            simpa [qftRightReg, hrSize] using hsmaller.2
          have hleftBound :=
            ih (regSize (leftReg r)) hleftLt hleftPos
              (leftReg r) xWork zWork (hworkspace.left htwoR) rfl
          have hrightBound :=
            ih (regSize (rightReg r)) hrightLt hrightPos
              (rightReg r) xWork zWork (hworkspace.right htwoR) rfl
          have hnode :
              (explicitQFTGateCount (Basis := Basis)
                k hk ops r xWork zWork hworkspace : ℝ)
                ≤
              (explicitQFTGateCount (Basis := Basis)
                k hk ops (rightReg r) xWork zWork
                (hworkspace.right htwoR) : ℝ)
                +
              (explicitQFTGateCount (Basis := Basis)
                k hk ops (leftReg r) xWork zWork
                (hworkspace.left htwoR) : ℝ)
                +
              A * phaseProductGateRate k n := by
            simpa [hrSize] using
              hstepBound r xWork zWork hworkspace htwoR
                (by simpa [hrSize] using hNn)
          have hcontractChildren :
              phaseProductGateRate k (regSize (leftReg r))
                + phaseProductGateRate k (regSize (rightReg r))
                ≤ ρ * phaseProductGateRate k n := by
            simpa [regSize_leftReg, regSize_rightReg, hrSize] using
              hcontractBound n htwo
          have hcontractScaled :
              C *
                (phaseProductGateRate k (regSize (leftReg r))
                  + phaseProductGateRate k (regSize (rightReg r)))
                ≤ C * (ρ * phaseProductGateRate k n) :=
            mul_le_mul_of_nonneg_left hcontractChildren (le_of_lt hC)
          calc
            (explicitQFTGateCount (Basis := Basis)
                k hk ops r xWork zWork hworkspace : ℝ)
                ≤
              (explicitQFTGateCount (Basis := Basis)
                k hk ops (rightReg r) xWork zWork
                (hworkspace.right htwoR) : ℝ)
                +
              (explicitQFTGateCount (Basis := Basis)
                k hk ops (leftReg r) xWork zWork
                (hworkspace.left htwoR) : ℝ)
                +
              A * phaseProductGateRate k n := hnode
            _ ≤
              C * phaseProductGateRate k (regSize (rightReg r))
                + C * phaseProductGateRate k (regSize (leftReg r))
                + A * phaseProductGateRate k n := by
              linarith
            _ =
              C *
                (phaseProductGateRate k (regSize (leftReg r))
                  + phaseProductGateRate k (regSize (rightReg r)))
                + A * phaseProductGateRate k n := by ring
            _ ≤
              C * (ρ * phaseProductGateRate k n)
                + A * phaseProductGateRate k n := by
              linarith
            _ = (ρ * C + A) * phaseProductGateRate k n := by ring
            _ ≤ C * phaseProductGateRate k n :=
              mul_le_mul_of_nonneg_right habsorb
                (Real.rpow_nonneg (by positivity : 0 ≤ (n : ℝ)) _)
  exact ⟨C, hC, fun r xWork zWork hworkspace hn =>
    hall (regSize r) hn r xWork zWork hworkspace rfl⟩

end BinaryRecurrenceSolution

/-! ---------------------------------------------------------
    Public QFT gate-count theorems

The final section transports the explicit-plan bound back to the public `lowerQFT`
API and packages the result first from a PhaseProduct bound, then from the
standard generated-program correctness hypothesis.
--------------------------------------------------------- -/

section PublicTheorems

/-- The public `lowerQFT` cost is definitionally the explicit standard-plan cost. -/
lemma lowerQFT_gateCount_eq_explicit
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (r : ExtReg)
    (hworkspace : QFTReserveOK ops r) :
    LowGate.gateCount shorGateCostModel (lowerQFT k hk ops r hworkspace)
      =
    explicitQFTGateCount (Basis := Basis) k hk ops r.active
      (qftXWork ops r) (qftZWork ops r) hworkspace.explicitWorkspace := by
  rfl

/-- Main QFT gate-count theorem assuming the corresponding PhaseProduct gate-count bound. -/
theorem qftGateCountBound_of_phaseProduct
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (hPhase : PhaseProductGateCountBound (Basis := Basis) k hk ops) :
    QFTGateCountBound (Basis := Basis) k hk ops := by
  have hα : 1 < phaseProductExponent k := one_lt_phaseProductExponent k hk
  have hcontract := qft_half_rate_contraction k hk hα
  have hbase :=
    explicitQFTGateCount_bounded_on_bounded_sizes (Basis := Basis) k hk ops
  have hstep :=
    explicitQFTGateCount_one_level_recurrence (Basis := Basis) k hk ops hPhase
  rcases explicitQFT_binary_recurrence_solution
      (Basis := Basis) k hk ops hcontract hbase hstep with
    ⟨C, hC, hbound⟩
  refine ⟨C, hC, 1, by omega, ?_⟩
  intro r hworkspace hn
  have hactiveSize : regSize r.active = r.width := by rfl
  have hgate :=
    hbound r.active (qftXWork ops r) (qftZWork ops r)
      hworkspace.explicitWorkspace (by simpa [hactiveSize] using hn)
  rw [lowerQFT_gateCount_eq_explicit
    (Basis := Basis) k hk ops r hworkspace]
  simpa [hactiveSize, phaseProductSafeRate, phaseProductGateRate,
    max_eq_right hn] using hgate

/-- Main generated-program QFT gate-count theorem, using the PhaseProduct theorem from `PhaseProduct.Main`. -/
theorem qftGateCountBound_of_programOK
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (hops : PhaseProductProgramOK k hk ops) :
    QFTGateCountBound (Basis := Basis) k hk ops := by
  exact qftGateCountBound_of_phaseProduct (Basis := Basis) k hk ops
    (phaseProductGateCountBound_of_programOK (Basis := Basis) k hk ops hops)

end PublicTheorems

end Shor
