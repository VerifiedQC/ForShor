import FastMultiplication.ShorVerification.Implementation.GateCount.QFT_GateCount
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.GateConstructions

namespace Shor

open Filter

/-! =========================================================
    Complete Shor Gate-Count Bound

This file assembles the component bounds for PhaseProduct, controlled
PhaseProduct, QFT, controlled modular multiplication, modular exponentiation,
and the full order-finding circuit. The final theorems package the asymptotic
`O(n^(2+ε))` gate-count bound and show that a suitable interpolation program
exists for every positive `ε`.
========================================================= -/

/-! ---------------------------------------------------------
    Public counting interface

These definitions fix the Shor precision schedule, record the register-layout
conditions used by the asymptotic proof, and expose the final lowered circuit
count as a proof-independent natural number.
--------------------------------------------------------- -/

section CountingInterface

/-- The per-modular-multiplication precision used by Shor. -/
noncomputable def shorEta (δ : ℝ) (n : ℕ) : ℝ :=
  δ / (n : ℝ) ^ 2

/--
Width and register-layout assumptions used internally by the counting proof.
All public registers are extended registers; only their active widths enter
the asymptotic estimate.
-/
def ShorGateCountLayout
    (cWork n : ℕ)
    (x y work : ExtReg)
    (flag : ℕ) : Prop :=
  regSize y.active = n ∧
  n ≤ regSize x.active ∧
  regSize x.active ≤ 2 * n ∧
  n ≤ regSize work.active ∧
  regSize work.active ≤ cWork * n ∧
  ModExpLayout x.active y work flag

/-- Gate count of a fully lowered approximate order-finding circuit. -/
noncomputable def shorOrderFindingGateCount
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (a N : ℕ)
    (x y work : ExtReg)
    (flag : ℕ)
    (hmodWorkspace : ModMulCircuitWorkspaceOK y work)
    (hLowerWorkspace :
      GateWorkspaceOK ops
        (orderFindingApprox qs a N x y work flag hmodWorkspace)) : ℕ :=
  LowGate.gateCount shorGateCostModel
    (orderFindingApproxLow qs k hk ops a N x y work flag
      hmodWorkspace hLowerWorkspace)

/--
The complete lowered Shor order-finding circuit has gate count
`O(n^(2+ε))`.  The static lowering-workspace proof is explicit because it is
the precondition required by `lowerGate`; the count is proof-independent.
-/
def ShorGateCountBound
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (ε δ : ℝ)
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k) : Prop :=
  ∃ C : ℝ, 0 < C ∧
  ∃ n₀ : ℕ, 1 ≤ n₀ ∧
    ∀ (inst : ShorOrderFindingInstance)
      (work : ExtReg) (flag : ℕ) (b0 : qs.Basis)
      (hsetup :
        ShorApproxSetup qs (shorEta δ inst.y.width) inst.x inst.y work flag b0),
      let n := inst.y.width
      n₀ ≤ n →
      ∀ hLowerWorkspace :
        GateWorkspaceOK ops
          (orderFindingApprox qs inst.a inst.N
            inst.x inst.y work flag hsetup.circuit_workspace),
      (shorOrderFindingGateCount qs k hk ops inst.a inst.N
          inst.x inst.y work flag hsetup.circuit_workspace
          hLowerWorkspace : ℝ)
        ≤ C * shorGateRate ε n

end CountingInterface

/-! ---------------------------------------------------------
    Lowered-gate utility lemmas

The proof estimates high-level gates through `lowerGate`. This section provides
small exact cost equations for sequencing, adjoints, Hadamard registers, Shor's
modular-multiplication steps, primitive arithmetic substeps, and uniform power
rescaling.
--------------------------------------------------------- -/

section LoweredGateUtilities

/-- Concrete low-gate count of one high-level gate after PhaseProduct-aware lowering. -/
noncomputable def loweredGateCount
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ) (hk : 1 < k) (ops : Prog k)
    (G : Gate) (hworkspace : GateWorkspaceOK ops G) : ℕ :=
  LowGate.gateCount shorGateCostModel
    (lowerGate (Basis := Basis) k hk ops G hworkspace)

/-- Lowered costs add across sequential composition. -/
@[simp] lemma loweredGateCount_seq
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ) (hk : 1 < k) (ops : Prog k)
    (U V : Gate)
    (hworkspace : GateWorkspaceOK ops (U ;; V)) :
    loweredGateCount (Basis := Basis) k hk ops (U ;; V) hworkspace =
      loweredGateCount (Basis := Basis) k hk ops U hworkspace.1 +
      loweredGateCount (Basis := Basis) k hk ops V hworkspace.2 := by
  rfl

/-- Taking an adjoint does not change the lowered gate count in this cost model. -/
@[simp] lemma loweredGateCount_adj
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ) (hk : 1 < k) (ops : Prog k)
    (U : Gate)
    (hworkspace : GateWorkspaceOK ops (†U)) :
    loweredGateCount (Basis := Basis) k hk ops (†U) hworkspace =
      loweredGateCount (Basis := Basis) k hk ops U hworkspace := by
  simp [loweredGateCount, lowerGate]

/-- Applying Hadamards to every qubit in a register costs exactly the register width. -/
lemma lowered_H_reg_gateCount
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ) (hk : 1 < k) (ops : Prog k)
    (r : Reg)
    (hworkspace : GateWorkspaceOK ops (H_reg r)) :
    loweredGateCount (Basis := Basis) k hk ops (H_reg r) hworkspace =
      regSize r := by
  have hfold :
      ∀ (l : List ℕ) (U : Gate)
        (hU : GateWorkspaceOK ops U)
        (hws : GateWorkspaceOK ops
          (l.foldl (fun acc q => Gate.H q ;; acc) U)),
        loweredGateCount (Basis := Basis) k hk ops
          (l.foldl (fun acc q => Gate.H q ;; acc) U) hws =
        l.length + loweredGateCount (Basis := Basis) k hk ops U hU := by
    intro l
    induction l with
    | nil =>
        intro U hU hws
        simp
    | cons q l ih =>
        intro U hU hws
        simp only [List.foldl_cons]
        rw [ih (Gate.H q ;; U) (by exact ⟨trivial, hU⟩)]
        simp [loweredGateCount, lowerGate, LowGate.gateCount]
        omega
  simpa [H_reg, regQubits, regSize] using
    hfold (regQubits r) Gate.id trivial hworkspace

/-- Expands controlled modular multiplication into the five Algorithm 1 core steps. -/
lemma test_core_expand
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ) (hk : 1 < k) (ops : Prog k)
    (c N ctrl : ℕ) (data work : ExtReg) (flag : ℕ)
    (hmod : ModMulCircuitWorkspaceOK data work)
    (hworkspace :
      GateWorkspaceOK ops
        (CmodMulInPlaceCore (Basis := Basis) c N ctrl data work flag hmod)) :
    loweredGateCount (Basis := Basis) k hk ops
        (CmodMulInPlaceCore (Basis := Basis) c N ctrl data work flag hmod)
        hworkspace
      =
    loweredGateCount (Basis := Basis) k hk ops
        (step1 (Basis := Basis) c N ctrl data work hmod)
        hworkspace.1
      +
    loweredGateCount (Basis := Basis) k hk ops
        (step2 (Basis := Basis) N data work hmod)
        hworkspace.2.1
      +
    loweredGateCount (Basis := Basis) k hk ops
        (step3 N (data.grow 1).active flag)
        (by simp [step3, GateWorkspaceOK])
      +
    loweredGateCount (Basis := Basis) k hk ops
        (step4 N (data.grow 1).active work.active flag)
        (by simp [step4, GateWorkspaceOK])
      +
    loweredGateCount (Basis := Basis) k hk ops
        (step5 (Basis := Basis) (step5Constant c N) N ctrl data work hmod)
        hworkspace.2.2.2.2 := by
  simp [CmodMulInPlaceCore]
  omega

/-- Decomposes Step 1 into work Hadamards, controlled PhaseProduct, and QFT. -/
lemma step1_gateCount_decompose
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ) (hk : 1 < k) (ops : Prog k)
    (c N ctrl : ℕ) (data work : ExtReg)
    (hmod : ModMulCircuitWorkspaceOK data work)
    (hworkspace :
      GateWorkspaceOK ops (step1 (Basis := Basis) c N ctrl data work hmod)) :
    loweredGateCount (Basis := Basis) k hk ops
        (step1 (Basis := Basis) c N ctrl data work hmod) hworkspace
      =
    loweredGateCount (Basis := Basis) k hk ops (H_reg work.active) hworkspace.1
      +
    loweredGateCount (Basis := Basis) k hk ops
        (Gate.CPhaseProdUsing ctrl
          ((2 * Real.pi * (((c + N - 1) % N : ℕ) : ℝ)) / (N : ℝ))
          data.active work.active hmod.step1Workspace)
        hworkspace.2.1
      +
    loweredGateCount (Basis := Basis) k hk ops
        (Gate.QFT hmod.step1Workspace.zExt) hworkspace.2.2 := by
  simp [step1, IQFT]
  omega

/-- Decomposes Step 2 into QFT, PhaseProduct, and inverse-QFT. -/
lemma step2_gateCount_decompose
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ) (hk : 1 < k) (ops : Prog k)
    (N : ℕ) (data work : ExtReg)
    (hmod : ModMulCircuitWorkspaceOK data work)
    (hworkspace :
      GateWorkspaceOK ops (step2 (Basis := Basis) N data work hmod)) :
    loweredGateCount (Basis := Basis) k hk ops
        (step2 (Basis := Basis) N data work hmod) hworkspace
      =
    loweredGateCount (Basis := Basis) k hk ops
        (Gate.QFT hmod.step2Workspace.zExt) hworkspace.1
      +
    loweredGateCount (Basis := Basis) k hk ops
        (Gate.PhaseProdUsing
          ((2 * Real.pi * (N : ℝ)) /
            ((2 : ℝ) ^ (regSize work.active + regSize (data.grow 1).active)))
          work.active (data.grow 1).active hmod.step2Workspace)
        hworkspace.2.1
      +
    loweredGateCount (Basis := Basis) k hk ops
        (Gate.QFT hmod.step2Workspace.zExt) hworkspace.2.2 := by
  simp [step2, IQFT]
  omega

/-- Decomposes Step 5 into work Hadamards, controlled PhaseProduct, and QFT. -/
lemma step5_gateCount_decompose
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ) (hk : 1 < k) (ops : Prog k)
    (k5 N ctrl : ℕ) (data work : ExtReg)
    (hmod : ModMulCircuitWorkspaceOK data work)
    (hworkspace :
      GateWorkspaceOK ops
        (step5 (Basis := Basis) k5 N ctrl data work hmod)) :
    loweredGateCount (Basis := Basis) k hk ops
        (step5 (Basis := Basis) k5 N ctrl data work hmod) hworkspace
      =
    loweredGateCount (Basis := Basis) k hk ops (H_reg work.active) hworkspace.1
      +
    loweredGateCount (Basis := Basis) k hk ops
        (Gate.CPhaseProdUsing ctrl
          ((2 * Real.pi * ((k5 % N : ℕ) : ℝ)) / (N : ℝ))
          (data.grow 1).active work.active hmod.step5Workspace)
        hworkspace.2.1
      +
    loweredGateCount (Basis := Basis) k hk ops
        (Gate.QFT hmod.step5Workspace.zExt) hworkspace.2.2 := by
  simp [step5, IQFT]
  omega

/-- Step 3 is a primitive arithmetic block with linear cost in the data-carry width. -/
lemma step3_gateCount_le
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ) (hk : 1 < k) (ops : Prog k)
    (N : ℕ) (dataCarry : Reg) (flag : ℕ)
    (hworkspace : GateWorkspaceOK ops (step3 N dataCarry flag)) :
    loweredGateCount (Basis := Basis) k hk ops
        (step3 N dataCarry flag) hworkspace
      ≤ 40 * regSize dataCarry + 20 := by
  simp [step3, loweredGateCount, lowerGate, LowGate.gateCount,
    shorGateCostModel, phaseProductCostModel, shorPrimCost,
    linearPrimitiveGateBound, regSize, Reg.width]
  omega

/-- Step 4 is a primitive arithmetic block with linear cost in data-carry plus work widths. -/
lemma step4_gateCount_le
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ) (hk : 1 < k) (ops : Prog k)
    (N : ℕ) (dataCarry work : Reg) (flag : ℕ)
    (hworkspace : GateWorkspaceOK ops (step4 N dataCarry work flag)) :
    loweredGateCount (Basis := Basis) k hk ops
        (step4 N dataCarry work flag) hworkspace
      ≤ 20 * (regSize dataCarry + regSize work) + 10 := by
  simp [step4, loweredGateCount, lowerGate, LowGate.gateCount,
    shorGateCostModel, phaseProductCostModel, shorPrimCost,
    linearPrimitiveGateBound, regSize, Reg.width]

/-- Step 1's PhaseProduct target workspace has the same width as the work register. -/
@[simp] lemma width_step1Workspace_zExt
    {data work : ExtReg}
    (hmod : ModMulCircuitWorkspaceOK data work) :
    (hmod.step1Workspace.zExt).width = work.width := by
  rfl

/-- Step 2's PhaseProduct target workspace is the one-bit-grown data register. -/
@[simp] lemma width_step2Workspace_zExt
    {data work : ExtReg}
    (hmod : ModMulCircuitWorkspaceOK data work) :
    (hmod.step2Workspace.zExt).width = data.width + 1 := by
  simpa [ModMulCircuitWorkspaceOK.step2Workspace,
    Gate.PhaseProdWorkspace.ofExtRegs, Gate.PhaseProdWorkspace.zExt] using
    ExtReg.width_grow data 1 hmod.data_canGrow_one

/-- Step 5's PhaseProduct target workspace has the same width as the work register. -/
@[simp] lemma width_step5Workspace_zExt
    {data work : ExtReg}
    (hmod : ModMulCircuitWorkspaceOK data work) :
    (hmod.step5Workspace.zExt).width = work.width := by
  rfl

/-- If `W ≤ c*n`, then the PhaseProduct comparison power at `W` is absorbed by a constant times the power at `n`. -/
lemma rpow_le_constPow_mul_rpow
    (k c W n : ℕ)
    (hk : 1 < k)
    (hW : W ≤ c * n) :
    Real.rpow (W : ℝ) (phaseProductExponent k)
      ≤
    Real.rpow (c : ℝ) (phaseProductExponent k) *
      Real.rpow (n : ℝ) (phaseProductExponent k) := by
  have hα : 0 ≤ phaseProductExponent k := by
    linarith [one_lt_phaseProductExponent k hk]
  have hWR : (W : ℝ) ≤ ((c * n : ℕ) : ℝ) := by
    exact_mod_cast hW
  calc
    Real.rpow (W : ℝ) (phaseProductExponent k)
        ≤ Real.rpow ((c * n : ℕ) : ℝ) (phaseProductExponent k) :=
      Real.rpow_le_rpow (by positivity) hWR hα
    _ =
      Real.rpow ((c : ℕ) : ℝ) (phaseProductExponent k) *
        Real.rpow ((n : ℕ) : ℝ) (phaseProductExponent k) := by
      rw [Nat.cast_mul]
      exact Real.mul_rpow (by positivity) (by positivity)

end LoweredGateUtilities

/-! ---------------------------------------------------------
    Controlled modular-multiplication core

This section combines the component bounds for PhaseProduct, controlled
PhaseProduct, QFT, Hadamards, and primitive arithmetic into one bound for a
single controlled modular-multiplication core.
--------------------------------------------------------- -/

section ModMulCoreBound

set_option maxHeartbeats 800000 in
/-- A full controlled modular-multiplication core costs one PhaseProduct-rate term at the data width. -/
lemma cmodMulInPlaceCore_gateCount_phase_bound
    {Basis : Type u}
    [RegEncoding Basis]
    (cWork : ℕ)
    (hcWork : 1 ≤ cWork)
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (hPhase : PhaseProductGateCountBound (Basis := Basis) k hk ops)
    (hCPhase : CPhaseProductGateCountBound (Basis := Basis) k hk ops)
    (hQFT : QFTGateCountBound (Basis := Basis) k hk ops) :
    ∃ A : ℝ, 0 < A ∧
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧
      ∀ (n c N ctrl : ℕ)
        (data work : ExtReg)
        (flag : ℕ)
        (hmod : ModMulCircuitWorkspaceOK data work)
        (hworkspace :
          GateWorkspaceOK ops
            (CmodMulInPlaceCore (Basis := Basis)
              c N ctrl data work flag hmod)),
        n₀ ≤ n →
        data.width = n →
        n ≤ work.width →
        work.width ≤ cWork * n →
        (loweredGateCount (Basis := Basis) k hk ops
          (CmodMulInPlaceCore (Basis := Basis)
            c N ctrl data work flag hmod) hworkspace : ℝ)
          ≤ A * Real.rpow (n : ℝ) (phaseProductExponent k) := by
  rcases hPhase with ⟨Cp, hCp, np, hnp, hPhase⟩
  rcases hCPhase with ⟨Cc, hCc, nc, hnc, hCPhase⟩
  rcases hQFT with ⟨Cq, hCq, nq, hnq, hQFT⟩
  let cMax : ℕ := max 2 cWork
  let α : ℝ := phaseProductExponent k
  let S : ℝ := Real.rpow (cMax : ℝ) α
  let L : ℝ := 22 * cWork + 150
  let A : ℝ := (Cp + 2 * Cc + 4 * Cq) * S + L + 1
  have hS : 0 < S := by
    dsimp [S, cMax]
    positivity
  have hL : 0 ≤ L := by
    dsimp [L]
    positivity
  have hA : 0 < A := by
    dsimp [A]
    positivity
  refine ⟨A, hA, max np (max nc nq), by omega, ?_⟩
  intro n c N ctrl data work flag hmod hworkspace hn hdata hworkLower hworkUpper
  have hn1 : 1 ≤ n := le_trans hnp (le_trans (Nat.le_max_left _ _) hn)
  have hnp' : np ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hnc' : nc ≤ n :=
    le_trans (Nat.le_max_left nc nq)
      (le_trans (Nat.le_max_right np (max nc nq)) hn)
  have hnq' : nq ≤ n :=
    le_trans (Nat.le_max_right nc nq)
      (le_trans (Nat.le_max_right np (max nc nq)) hn)
  have hcarry :
      (data.grow 1).width = n + 1 := by
    rw [ExtReg.width_grow data 1 hmod.data_canGrow_one, hdata]
  have hcMaxTwo : 2 ≤ cMax := Nat.le_max_left _ _
  have hcMaxWork : cWork ≤ cMax := Nat.le_max_right _ _
  have hnCarry : n + 1 ≤ 2 * n := by omega
  have hworkMax : work.width ≤ cMax * n := by
    exact hworkUpper.trans (Nat.mul_le_mul_right n hcMaxWork)
  have hcarryMax : (data.grow 1).width ≤ cMax * n := by
    rw [hcarry]
    exact hnCarry.trans (Nat.mul_le_mul_right n hcMaxTwo)
  have hdataMax : data.width ≤ cMax * n := by
    rw [hdata]
    have : 1 ≤ cMax := by omega
    nlinarith
  have hmaxDataWork :
      max (regSize data.active) (regSize work.active) ≤ cMax * n := by
    simpa [ExtReg.width] using max_le hdataMax hworkMax
  have hmaxCarryWork :
      max (regSize (data.grow 1).active) (regSize work.active) ≤ cMax * n := by
    simpa [ExtReg.width] using max_le hcarryMax hworkMax
  have hmaxWorkCarry :
      max (regSize work.active) (regSize (data.grow 1).active) ≤ cMax * n := by
    simpa [ExtReg.width] using max_le hworkMax hcarryMax
  let hws1 := hworkspace.1
  let hws2 := hworkspace.2.1
  let hws3 := hworkspace.2.2.1
  let hws4 := hworkspace.2.2.2.1
  let hws5 := hworkspace.2.2.2.2
  have hC1 := hCPhase ctrl
    ((2 * Real.pi * (((c + N - 1) % N : ℕ) : ℝ)) / (N : ℝ))
    data.active work.active hmod.step1Workspace hws1.2.1
  have hC1' := hC1 (by
    have : n ≤ max (regSize data.active) (regSize work.active) := by
      rw [← hdata]
      simp[ExtReg.width]
    exact hnc'.trans this)
  have hC5 := hCPhase ctrl
    ((2 * Real.pi * (((step5Constant c N) % N : ℕ) : ℝ)) / (N : ℝ))
    (data.grow 1).active work.active hmod.step5Workspace hws5.2.1
  have hC5' := hC5 (by
    have : n ≤ max (regSize (data.grow 1).active) (regSize work.active) := by
      have : n ≤ (data.grow 1).width := by rw [hcarry]; omega
      have hle :
          (data.grow 1).width ≤
            max (regSize (data.grow 1).active) (regSize work.active) := by
        simp [ExtReg.width]
      exact this.trans hle
    exact hnc'.trans this)
  have hP2 := hPhase
    ((2 * Real.pi * (N : ℝ)) /
      ((2 : ℝ) ^ (regSize work.active + regSize (data.grow 1).active)))
    work.active (data.grow 1).active hmod.step2Workspace hws2.2.1
  have hP2' := hP2 (by
    have : n ≤ max (regSize work.active) (regSize (data.grow 1).active) := by
      have : n ≤ (data.grow 1).width := by rw [hcarry]; omega
      have hle :
          (data.grow 1).width ≤
            max (regSize work.active) (regSize (data.grow 1).active) := by
        simp [ExtReg.width]
      exact this.trans hle
    exact hnp'.trans this)
  have hQ1 := hQFT hmod.step1Workspace.zExt hws1.2.2 (by
    simpa using hnq'.trans hworkLower)
  have hQ2a := hQFT hmod.step2Workspace.zExt hws2.1 (by
    rw [width_step2Workspace_zExt]
    omega)
  have hQ2b := hQFT hmod.step2Workspace.zExt hws2.2.2 (by
    rw [width_step2Workspace_zExt]
    omega)
  have hQ5 := hQFT hmod.step5Workspace.zExt hws5.2.2 (by
    simpa using hnq'.trans hworkLower)
  have hscaleDataWork :=
    rpow_le_constPow_mul_rpow k cMax
      (max (regSize data.active) (regSize work.active)) n hk hmaxDataWork
  have hscaleCarryWork :=
    rpow_le_constPow_mul_rpow k cMax
      (max (regSize (data.grow 1).active) (regSize work.active)) n hk hmaxCarryWork
  have hscaleWorkCarry :=
    rpow_le_constPow_mul_rpow k cMax
      (max (regSize work.active) (regSize (data.grow 1).active)) n hk hmaxWorkCarry
  have hscaleWork :=
    rpow_le_constPow_mul_rpow k cMax work.width n hk hworkMax
  have hscaleCarry :=
    rpow_le_constPow_mul_rpow k cMax (data.grow 1).width n hk hcarryMax
  have hC1b :
      (loweredGateCount (Basis := Basis) k hk ops
        (Gate.CPhaseProdUsing ctrl
          ((2 * Real.pi * (((c + N - 1) % N : ℕ) : ℝ)) / (N : ℝ))
          data.active work.active hmod.step1Workspace) hws1.2.1 : ℝ)
        ≤ Cc * S * Real.rpow (n : ℝ) α := by
    have hmaxPos :
        1 ≤ max (regSize data.active) (regSize work.active) := by
      have hnMax :
          n ≤ max (regSize data.active) (regSize work.active) := by
        rw [← hdata]
        simp [ExtReg.width]
      exact hn1.trans hnMax
    have hsafe :
        phaseProductSafeRate k
            (max (regSize data.active) (regSize work.active)) =
          Real.rpow
            ((max (regSize data.active) (regSize work.active) : ℕ) : ℝ)
            (phaseProductExponent k) := by
      simp [phaseProductSafeRate, max_eq_right hmaxPos]
    rw [hsafe] at hC1'
    have hb :=
      hC1'.trans
        (mul_le_mul_of_nonneg_left hscaleDataWork (le_of_lt hCc))
    simpa [loweredGateCount, S, α, mul_assoc] using hb
  have hC5b :
      (loweredGateCount (Basis := Basis) k hk ops
        (Gate.CPhaseProdUsing ctrl
          ((2 * Real.pi * (((step5Constant c N) % N : ℕ) : ℝ)) / (N : ℝ))
          (data.grow 1).active work.active hmod.step5Workspace) hws5.2.1 : ℝ)
        ≤ Cc * S * Real.rpow (n : ℝ) α := by
    have hmaxPos :
        1 ≤
          max (regSize (data.grow 1).active) (regSize work.active) := by
      have hnCarry' : n ≤ (data.grow 1).width := by
        rw [hcarry]
        omega
      have hcarryMax' :
          (data.grow 1).width ≤
            max (regSize (data.grow 1).active) (regSize work.active) := by
        simp [ExtReg.width]
      exact hn1.trans (hnCarry'.trans hcarryMax')
    have hsafe :
        phaseProductSafeRate k
            (max (regSize (data.grow 1).active) (regSize work.active)) =
          Real.rpow
            ((max (regSize (data.grow 1).active)
              (regSize work.active) : ℕ) : ℝ)
            (phaseProductExponent k) := by
      simp [phaseProductSafeRate, max_eq_right hmaxPos]
    rw [hsafe] at hC5'
    have hb :=
      hC5'.trans
        (mul_le_mul_of_nonneg_left hscaleCarryWork (le_of_lt hCc))
    simpa [loweredGateCount, S, α, mul_assoc] using hb
  have hP2b :
      (loweredGateCount (Basis := Basis) k hk ops
        (Gate.PhaseProdUsing
          ((2 * Real.pi * (N : ℝ)) /
            ((2 : ℝ) ^ (regSize work.active + regSize (data.grow 1).active)))
          work.active (data.grow 1).active hmod.step2Workspace) hws2.2.1 : ℝ)
        ≤ Cp * S * Real.rpow (n : ℝ) α := by
    have hb :=
      hP2'.trans
        (mul_le_mul_of_nonneg_left hscaleWorkCarry (le_of_lt hCp))
    simpa [loweredGateCount, S, α, mul_assoc] using hb
  have hQ1b :
      (loweredGateCount (Basis := Basis) k hk ops
        (Gate.QFT hmod.step1Workspace.zExt) hws1.2.2 : ℝ)
        ≤ Cq * S * Real.rpow (n : ℝ) α := by
    rw [width_step1Workspace_zExt] at hQ1
    have hsafe : phaseProductSafeRate k work.width =
        Real.rpow (work.width : ℝ) (phaseProductExponent k) := by
      simp [phaseProductSafeRate, max_eq_right (hworkLower.trans' hn1)]
    rw [hsafe] at hQ1
    have hb :=
      hQ1.trans (mul_le_mul_of_nonneg_left hscaleWork (le_of_lt hCq))
    simpa [loweredGateCount, lowerGate, S, α, mul_assoc] using hb
  have hQ2ab :
      (loweredGateCount (Basis := Basis) k hk ops
        (Gate.QFT hmod.step2Workspace.zExt) hws2.1 : ℝ)
        ≤ Cq * S * Real.rpow (n : ℝ) α := by
    rw [width_step2Workspace_zExt] at hQ2a
    rw [← ExtReg.width_grow data 1 hmod.data_canGrow_one] at hQ2a
    have hcarryPos : 1 ≤ (data.grow 1).width := by rw [hcarry]; omega
    have hsafe : phaseProductSafeRate k (data.grow 1).width =
        Real.rpow ((data.grow 1).width : ℝ) (phaseProductExponent k) := by
      simp [phaseProductSafeRate, max_eq_right hcarryPos]
    rw [hsafe] at hQ2a
    have hb :=
      hQ2a.trans (mul_le_mul_of_nonneg_left hscaleCarry (le_of_lt hCq))
    simpa [loweredGateCount, lowerGate, S, α, mul_assoc] using hb
  have hQ2bb :
      (loweredGateCount (Basis := Basis) k hk ops
        (Gate.QFT hmod.step2Workspace.zExt) hws2.2.2 : ℝ)
        ≤ Cq * S * Real.rpow (n : ℝ) α := by
    rw [width_step2Workspace_zExt] at hQ2b
    rw [← ExtReg.width_grow data 1 hmod.data_canGrow_one] at hQ2b
    have hcarryPos : 1 ≤ (data.grow 1).width := by rw [hcarry]; omega
    have hsafe : phaseProductSafeRate k (data.grow 1).width =
        Real.rpow ((data.grow 1).width : ℝ) (phaseProductExponent k) := by
      simp [phaseProductSafeRate, max_eq_right hcarryPos]
    rw [hsafe] at hQ2b
    have hb :=
      hQ2b.trans (mul_le_mul_of_nonneg_left hscaleCarry (le_of_lt hCq))
    simpa [loweredGateCount, lowerGate, S, α, mul_assoc] using hb
  have hQ5b :
      (loweredGateCount (Basis := Basis) k hk ops
        (Gate.QFT hmod.step5Workspace.zExt) hws5.2.2 : ℝ)
        ≤ Cq * S * Real.rpow (n : ℝ) α := by
    rw [width_step5Workspace_zExt] at hQ5
    have hsafe : phaseProductSafeRate k work.width =
        Real.rpow (work.width : ℝ) (phaseProductExponent k) := by
      simp [phaseProductSafeRate, max_eq_right (hworkLower.trans' hn1)]
    rw [hsafe] at hQ5
    have hb :=
      hQ5.trans (mul_le_mul_of_nonneg_left hscaleWork (le_of_lt hCq))
    simpa [loweredGateCount, lowerGate, S, α, mul_assoc] using hb
  have hH1 :
      (loweredGateCount (Basis := Basis) k hk ops
        (H_reg work.active) hws1.1 : ℝ) ≤ cWork * n := by
    rw [lowered_H_reg_gateCount]
    exact_mod_cast hworkUpper
  have hH5 :
      (loweredGateCount (Basis := Basis) k hk ops
        (H_reg work.active) hws5.1 : ℝ) ≤ cWork * n := by
    rw [lowered_H_reg_gateCount]
    exact_mod_cast hworkUpper
  have hS3Nat := step3_gateCount_le (Basis := Basis) k hk ops
    N (data.grow 1).active flag hws3
  have hS4Nat := step4_gateCount_le (Basis := Basis) k hk ops
    N (data.grow 1).active work.active flag hws4
  have hS3 :
      (loweredGateCount (Basis := Basis) k hk ops
        (step3 N (data.grow 1).active flag) hws3 : ℝ)
        ≤ 100 * n := by
    have hS3R :
        (loweredGateCount (Basis := Basis) k hk ops
          (step3 N (data.grow 1).active flag) hws3 : ℝ)
          ≤ (40 * regSize (data.grow 1).active + 20 : ℕ) := by
      exact_mod_cast hS3Nat
    have hcarryReg :
        regSize (data.grow 1).active = n + 1 := by
      simpa [ExtReg.width] using hcarry
    rw [hcarryReg] at hS3R
    push_cast at hS3R
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    linarith
  have hS4 :
      (loweredGateCount (Basis := Basis) k hk ops
        (step4 N (data.grow 1).active work.active flag) hws4 : ℝ)
        ≤ (20 * (cWork + 2) + 10) * n := by
    have hS4R :
        (loweredGateCount (Basis := Basis) k hk ops
          (step4 N (data.grow 1).active work.active flag) hws4 : ℝ)
          ≤ (20 * (regSize (data.grow 1).active + regSize work.active) + 10 : ℕ) := by
      exact_mod_cast hS4Nat
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hwR : (work.width : ℝ) ≤ cWork * n := by exact_mod_cast hworkUpper
    have hcarryReg :
        regSize (data.grow 1).active = n + 1 := by
      simpa [ExtReg.width] using hcarry
    have hworkReg : regSize work.active = work.width := by
      rfl
    rw [hcarryReg, hworkReg] at hS4R
    push_cast at hS4R ⊢
    nlinarith
  have hnRate : (n : ℝ) ≤ Real.rpow (n : ℝ) α := by
    simpa [α] using natCast_le_phaseProduct_rpow k hk hn1
  have hrateNonneg : 0 ≤ Real.rpow (n : ℝ) α := by
    exact Real.rpow_nonneg (by positivity) α
  have hlinearRate :
      (22 * cWork + 150 : ℝ) * n ≤
        (22 * cWork + 150 : ℝ) * Real.rpow (n : ℝ) α :=
    mul_le_mul_of_nonneg_left hnRate (by positivity)
  rw [test_core_expand (Basis := Basis) k hk ops c N ctrl data work flag hmod hworkspace]
  rw [step1_gateCount_decompose, step2_gateCount_decompose, step5_gateCount_decompose]
  push_cast
  dsimp [A, L, α] at hC1b hC5b hP2b
  dsimp [A, L, α] at hQ1b hQ2ab hQ2bb hQ5b
  dsimp [A, L, α] at hlinearRate hrateNonneg ⊢
  calc
    _ ≤
        ((cWork : ℝ) * n +
            Cc * S * Real.rpow (n : ℝ) (phaseProductExponent k) +
            Cq * S * Real.rpow (n : ℝ) (phaseProductExponent k)) +
          (Cq * S * Real.rpow (n : ℝ) (phaseProductExponent k) +
            Cp * S * Real.rpow (n : ℝ) (phaseProductExponent k) +
            Cq * S * Real.rpow (n : ℝ) (phaseProductExponent k)) +
          100 * n +
          (20 * ((cWork : ℝ) + 2) + 10) * n +
          ((cWork : ℝ) * n +
            Cc * S * Real.rpow (n : ℝ) (phaseProductExponent k) +
            Cq * S * Real.rpow (n : ℝ) (phaseProductExponent k)) := by
      gcongr <;> assumption
    _ =
        (Cp + 2 * Cc + 4 * Cq) * S *
            Real.rpow (n : ℝ) (phaseProductExponent k) +
          (22 * (cWork : ℝ) + 150) * n := by
      ring
    _ ≤
        (Cp + 2 * Cc + 4 * Cq) * S *
            Real.rpow (n : ℝ) (phaseProductExponent k) +
          (22 * (cWork : ℝ) + 150) *
            Real.rpow (n : ℝ) (phaseProductExponent k) :=
      add_le_add_right hlinearRate _
    _ =
        ((Cp + 2 * Cc + 4 * Cq) * S +
            (22 * (cWork : ℝ) + 150)) *
          Real.rpow (n : ℝ) (phaseProductExponent k) := by
      ring
    _ =
        ((Cp + 2 * Cc + 4 * Cq) * S +
            (22 * (cWork : ℝ) + 150)) *
            Real.rpow (n : ℝ) (phaseProductExponent k) + 0 := by
      ring
    _ ≤
        ((Cp + 2 * Cc + 4 * Cq) * S +
            (22 * (cWork : ℝ) + 150)) *
            Real.rpow (n : ℝ) (phaseProductExponent k) +
          Real.rpow (n : ℝ) (phaseProductExponent k) :=
      add_le_add_right hrateNonneg _
    _ =
        ((Cp + 2 * Cc + 4 * Cq) * S +
            (22 * (cWork : ℝ) + 150) + 1) *
          Real.rpow (n : ℝ) (phaseProductExponent k) := by
      ring

end ModMulCoreBound

/-! ---------------------------------------------------------
    Modular exponentiation

A modular exponentiation circuit is a list recursion over controlled
modular-multiplication cores. This section turns the one-core estimate into the
loop estimate by summing over the control register.
--------------------------------------------------------- -/

section ModExpBound

set_option maxHeartbeats 800000 in
/--
If one controlled modular multiplication costs at most
`A * n^(phaseProductExponent k)`, the loop over at most `2*n` controls costs
at most `2*A*n*n^(phaseProductExponent k)`.
-/
lemma modExpApproxValid_gateCount_phase_bound_of_core
    {Basis : Type u}
    [RegEncoding Basis]
    (cWork : ℕ)
    (_hcWork : 1 ≤ cWork)
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (A : ℝ)
    (hA : 0 < A)
    (nCore : ℕ)
    (hnCore : 1 ≤ nCore)
    (hCore :
      ∀ (n c N ctrl : ℕ)
        (data work : ExtReg)
        (flag : ℕ)
        (hmod : ModMulCircuitWorkspaceOK data work)
        (hworkspace :
          GateWorkspaceOK ops
            (CmodMulInPlaceCore (Basis := Basis)
              c N ctrl data work flag hmod)),
        nCore ≤ n →
        data.width = n →
        n ≤ work.width →
        work.width ≤ cWork * n →
        (loweredGateCount (Basis := Basis) k hk ops
          (CmodMulInPlaceCore (Basis := Basis)
            c N ctrl data work flag hmod) hworkspace : ℝ)
          ≤ A * Real.rpow (n : ℝ) (phaseProductExponent k)) :
    ∃ B : ℝ, 0 < B ∧
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧
      ∀ (n a N : ℕ)
        (x data work : ExtReg)
        (flag : ℕ)
        (hmod : ModMulCircuitWorkspaceOK data work)
        (hworkspace :
          GateWorkspaceOK ops
            (modExpApproxValid (Basis := Basis)
              a N x.active data work flag hmod)),
        n₀ ≤ n →
        ShorGateCountLayout cWork n
          x data work flag →
        (loweredGateCount (Basis := Basis) k hk ops
          (modExpApproxValid (Basis := Basis)
            a N x.active data work flag hmod) hworkspace : ℝ)
          ≤ B * (n : ℝ) *
            Real.rpow (n : ℝ) (phaseProductExponent k) := by
  refine ⟨2 * A, by positivity, nCore, hnCore, ?_⟩
  intro n a N x data work flag hmod hworkspace hn hLayout
  rcases hLayout with
    ⟨hDataSize, _hxLower, hxUpper,
      hworkLower, hworkUpper, _hRegisterLayout⟩
  let R : ℝ :=
    Real.rpow (n : ℝ) (phaseProductExponent k)
  have hRNonneg : 0 ≤ R := by
    exact Real.rpow_nonneg (by positivity) _
  have hARNonneg : 0 ≤ A * R :=
    mul_nonneg (le_of_lt hA) hRNonneg
  have hSteps :
      ∀ (e : ℕ) (ctrls : List ℕ)
        (hws :
          GateWorkspaceOK ops
            (modExpApproxStepsValid (Basis := Basis)
              a N data work flag hmod e ctrls)),
        (loweredGateCount (Basis := Basis) k hk ops
          (modExpApproxStepsValid (Basis := Basis)
            a N data work flag hmod e ctrls) hws : ℝ)
          ≤ (ctrls.length : ℝ) * (A * R) := by
    intro e ctrls
    induction ctrls generalizing e with
    | nil =>
        intro hws
        simp [modExpApproxStepsValid, loweredGateCount]
    | cons ctrl ctrls ih =>
        intro hws
        let c : ℕ := (a ^ (2 ^ e)) % N
        have hHead :
            (loweredGateCount (Basis := Basis) k hk ops
              (CmodMulInPlaceCore (Basis := Basis)
                c N ctrl data work flag hmod) hws.1 : ℝ)
              ≤ A * R := by
          simpa [c, R] using
            hCore n c N ctrl data work flag hmod hws.1
              hn hDataSize hworkLower hworkUpper
        have hTail :
            (loweredGateCount (Basis := Basis) k hk ops
              (modExpApproxStepsValid (Basis := Basis)
                a N data work flag hmod (e + 1) ctrls) hws.2 : ℝ)
              ≤ (ctrls.length : ℝ) * (A * R) :=
          ih (e + 1) hws.2
        simp only [modExpApproxStepsValid, loweredGateCount_seq,
          List.length_cons]
        push_cast
        calc
          _ ≤ A * R + (ctrls.length : ℝ) * (A * R) :=
            add_le_add hHead hTail
          _ = ((ctrls.length : ℝ) + 1) * (A * R) := by
            ring
  have hAllSteps :=
    hSteps 0 x.active.qubits hworkspace
  have hxUpper' : x.active.qubits.length ≤ 2 * n := by
    simpa [regSize, Reg.width] using hxUpper
  have hxUpperR : (x.active.qubits.length : ℝ) ≤ 2 * (n : ℝ) := by
    exact_mod_cast hxUpper'
  calc
    (loweredGateCount (Basis := Basis) k hk ops
        (modExpApproxValid (Basis := Basis)
          a N x.active data work flag hmod) hworkspace : ℝ)
        ≤ (x.active.qubits.length : ℝ) * (A * R) := by
          simpa [modExpApproxValid] using hAllSteps
    _ ≤ (2 * (n : ℝ)) * (A * R) :=
      mul_le_mul_of_nonneg_right hxUpperR hARNonneg
    _ =
        (2 * A) * (n : ℝ) *
          Real.rpow (n : ℝ) (phaseProductExponent k) := by
      dsimp [R]
      ring

end ModExpBound

/-! ---------------------------------------------------------
    Order finding

The full approximate order-finding circuit wraps modular exponentiation with
input Hadamards, initialization of `y` to one, and the final inverse QFT. The
lemmas below add those costs to the modular-exponentiation estimate.
--------------------------------------------------------- -/

section OrderFindingBound

/-- Initializing the output register to `1` costs at most one primitive gate. -/
lemma lowered_initY1_gateCount_le
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ) (hk : 1 < k) (ops : Prog k)
    (y : Reg)
    (hworkspace : GateWorkspaceOK ops (initY1 y)) :
    loweredGateCount (Basis := Basis) k hk ops
      (initY1 y) hworkspace ≤ 1 := by
  by_cases hnil : y.qubits = []
  · simp [initY1, hnil, loweredGateCount]
  · obtain ⟨q, tail, hcons⟩ := List.exists_cons_of_ne_nil hnil
    simp [initY1, hcons, loweredGateCount, lowerGate]

/-- Decomposes the order-finding circuit into Hadamards, initialization, modular exponentiation, and inverse-QFT. -/
lemma orderFindingApprox_gateCount_decompose
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (k : ℕ) (hk : 1 < k) (ops : Prog k)
    (a N : ℕ)
    (x y work : ExtReg)
    (flag : ℕ)
    (hmod : ModMulCircuitWorkspaceOK y work)
    (hworkspace :
      GateWorkspaceOK ops
        (orderFindingApprox qs a N x y work flag hmod)) :
    loweredGateCount (Basis := qs.Basis) k hk ops
        (orderFindingApprox qs a N x y work flag hmod) hworkspace
      =
    loweredGateCount (Basis := qs.Basis) k hk ops
        (H_reg x.active) hworkspace.1
      +
    loweredGateCount (Basis := qs.Basis) k hk ops
        (initY1 y.active) hworkspace.2.1
      +
    loweredGateCount (Basis := qs.Basis) k hk ops
        (modExpApproxValid (Basis := qs.Basis)
          a N x.active y work flag hmod) hworkspace.2.2.1
      +
    loweredGateCount (Basis := qs.Basis) k hk ops
        (IQFT x) hworkspace.2.2.2 := by
  simp [orderFindingApprox, IQFT]
  omega

set_option maxHeartbeats 800000 in
/--
Add the initial Hadamards, initialization `X`, and final inverse QFT to the
modular-exponentiation estimate.
-/
lemma orderFindingApproxLow_gateCount_phase_bound
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (cWork : ℕ)
    (_hcWork : 1 ≤ cWork)
    (hQFT : QFTGateCountBound (Basis := qs.Basis) k hk ops)
    (B : ℝ)
    (hB : 0 < B)
    (nModExp : ℕ)
    (hnModExp : 1 ≤ nModExp)
    (hModExp :
      ∀ (n a N : ℕ)
        (x y work : ExtReg)
        (flag : ℕ)
        (hmod : ModMulCircuitWorkspaceOK y work)
        (hworkspace :
          GateWorkspaceOK ops
            (modExpApproxValid (Basis := qs.Basis)
              a N x.active y work flag hmod)),
        nModExp ≤ n →
        ShorGateCountLayout cWork n x y work flag →
        (loweredGateCount (Basis := qs.Basis) k hk ops
          (modExpApproxValid (Basis := qs.Basis)
            a N x.active y work flag hmod) hworkspace : ℝ)
          ≤ B * (n : ℝ) *
            Real.rpow (n : ℝ) (phaseProductExponent k)) :
    ∃ C : ℝ, 0 < C ∧
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧
      ∀ (n a N : ℕ)
        (x y work : ExtReg)
        (flag : ℕ)
        (hmod : ModMulCircuitWorkspaceOK y work)
        (hworkspace :
          GateWorkspaceOK ops
            (orderFindingApprox qs a N x y work flag hmod)),
        n₀ ≤ n →
        ShorGateCountLayout cWork n x y work flag →
        (shorOrderFindingGateCount qs k hk ops
          a N x y work flag hmod hworkspace : ℝ)
          ≤ C *
            Real.rpow (n : ℝ)
              (1 + phaseProductExponent k) := by
  rcases hQFT with ⟨Cq, hCq, nq, hnq, hQFT⟩
  let α : ℝ := phaseProductExponent k
  let S : ℝ := Real.rpow (2 : ℝ) α
  let C : ℝ := B + Cq * S + 4
  have hC : 0 < C := by
    dsimp [C, S]
    positivity
  refine ⟨C, hC, max nModExp nq, by omega, ?_⟩
  intro n a N x y work flag hmod hworkspace hn hLayout
  rcases hLayout with
    ⟨hySize, hxLower, hxUpper,
      hworkLower, hworkUpper, hRegisterLayout⟩
  have hn1 : 1 ≤ n :=
    hnModExp.trans ((Nat.le_max_left _ _).trans hn)
  have hnModExp' : nModExp ≤ n :=
    (Nat.le_max_left _ _).trans hn
  have hnq' : nq ≤ n :=
    (Nat.le_max_right _ _).trans hn
  have hLayout' :
      ShorGateCountLayout cWork n x y work flag :=
    ⟨hySize, hxLower, hxUpper,
      hworkLower, hworkUpper, hRegisterLayout⟩
  have hM :=
    hModExp n a N x y work flag hmod hworkspace.2.2.1
      hnModExp' hLayout'
  have hHNat :=
    lowered_H_reg_gateCount (Basis := qs.Basis)
      k hk ops x.active hworkspace.1
  have hH :
      (loweredGateCount (Basis := qs.Basis) k hk ops
        (H_reg x.active) hworkspace.1 : ℝ) ≤ 2 * n := by
    rw [hHNat]
    exact_mod_cast hxUpper
  have hInitNat :=
    lowered_initY1_gateCount_le (Basis := qs.Basis)
      k hk ops y.active hworkspace.2.1
  have hInit :
      (loweredGateCount (Basis := qs.Basis) k hk ops
        (initY1 y.active) hworkspace.2.1 : ℝ) ≤ 1 := by
    exact_mod_cast hInitNat
  have hQ := hQFT x hworkspace.2.2.2 (hnq'.trans hxLower)
  have hsafeX :
      phaseProductSafeRate k x.width =
        Real.rpow (x.width : ℝ) (phaseProductExponent k) := by
    have hxPos : 1 ≤ x.width := by
      exact hn1.trans hxLower
    simp [phaseProductSafeRate, max_eq_right hxPos]
  rw [hsafeX] at hQ
  have hscaleX :=
    rpow_le_constPow_mul_rpow k 2 x.width n hk hxUpper
  have hQScaled :=
    hQ.trans (mul_le_mul_of_nonneg_left hscaleX (le_of_lt hCq))
  have hQ' :
      (loweredGateCount (Basis := qs.Basis) k hk ops
        (IQFT x) hworkspace.2.2.2 : ℝ)
        ≤ Cq * S * Real.rpow (n : ℝ) α := by
    simpa [loweredGateCount, lowerGate, IQFT, S, α,
      LowGate.gateCount, mul_assoc] using hQScaled
  have hrateNonneg :
      0 ≤ Real.rpow (n : ℝ) α :=
    Real.rpow_nonneg (by positivity) _
  have hrateOne :
      1 ≤ Real.rpow (n : ℝ) α := by
    have hα : 0 ≤ α := by
      dsimp [α]
      linarith [one_lt_phaseProductExponent k hk]
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    simpa using Real.one_rpow α ▸
      Real.rpow_le_rpow (by norm_num) hnR hα
  have hBigRate :
      (n : ℝ) ^ (1 + α) =
        (n : ℝ) * ((n : ℝ) ^ α) := by
    calc
      (n : ℝ) ^ (1 + α) =
          (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ α :=
        Real.rpow_add (by positivity) 1 α
      _ = (n : ℝ) * ((n : ℝ) ^ α) := by
        congr 1
        exact Real.rpow_one (n : ℝ)
  change
    (loweredGateCount (Basis := qs.Basis) k hk ops
      (orderFindingApprox qs a N x y work flag hmod) hworkspace : ℝ)
      ≤ C * Real.rpow (n : ℝ) (1 + phaseProductExponent k)
  rw [orderFindingApprox_gateCount_decompose]
  push_cast
  dsimp [C]
  change
    _ ≤ (B + Cq * S + 4) * ((n : ℝ) ^ (1 + α))
  rw [hBigRate]
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hH' : (2 : ℝ) * n ≤ 2 * (n * Real.rpow (n : ℝ) α) := by
    nlinarith
  have hInit' : (1 : ℝ) ≤ n * Real.rpow (n : ℝ) α := by
    nlinarith
  calc
    _ ≤
        2 * n + 1 +
          B * n * Real.rpow (n : ℝ) α +
          Cq * S * Real.rpow (n : ℝ) α := by
      gcongr
    _ ≤
        2 * (n * Real.rpow (n : ℝ) α) +
          n * Real.rpow (n : ℝ) α +
          B * n * Real.rpow (n : ℝ) α +
          Cq * S * (n * Real.rpow (n : ℝ) α) := by
      gcongr
      · exact mul_nonneg (le_of_lt hCq) (by
          dsimp [S]
          positivity)
      · simpa using
          (mul_le_mul_of_nonneg_right hnR hrateNonneg)
    _ =
        (B + Cq * S + 3) *
          (n * Real.rpow (n : ℝ) α) := by
      ring
    _ ≤
        (B + Cq * S + 4) *
          (n * Real.rpow (n : ℝ) α) := by
      have hbigNonneg :
          0 ≤ (n : ℝ) * Real.rpow (n : ℝ) α :=
        mul_nonneg (by positivity) hrateNonneg
      gcongr
      norm_num

end OrderFindingBound

/-! ---------------------------------------------------------
    Exponent and register-width conversions

The component bound is expressed with the PhaseProduct exponent and concrete
register widths from Shor's setup. These lemmas convert that form to
`shorGateRate ε n` and show the work-register precision overhead is eventually
linear.
--------------------------------------------------------- -/

section ExponentAndWidthConversions

/-- Converts the PhaseProduct exponent bound into the final Shor comparison rate. -/
lemma phaseProduct_succ_rate_le_shorGateRate
    (ε : ℝ)
    (k n : ℕ)
    (hn : 1 ≤ n)
    (hExponent : phaseProductExponent k ≤ 1 + ε) :
    Real.rpow (n : ℝ) (1 + phaseProductExponent k)
      ≤ shorGateRate ε n := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hExp :
      1 + phaseProductExponent k ≤ 2 + ε := by
    linarith
  have hpow :=
    Real.rpow_le_rpow_of_exponent_le hnR hExp
  simpa [shorGateRate, max_eq_right hn] using hpow

/-- Shor's exponent register is at least as wide as the data register. -/
lemma shor_y_width_le_x_width
    (N : ℕ)
    (x y : ExtReg)
    (hN : 1 < N)
    (hx : regSize x.active = Nat.log2 (2 * N^2))
    (hy : regSize y.active = Nat.log2 (2 * N)) :
    regSize y.active ≤ regSize x.active := by
  rw [hx, hy]
  have harg : 2 * N ≤ 2 * N^2 := by
    nlinarith
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  exact Nat.log_mono_right harg

/-- Shor's exponent register is at most twice as wide as the data register. -/
lemma shor_x_width_le_two_y_width
    (N : ℕ)
    (x y : ExtReg)
    (hN : 1 < N)
    (hx : regSize x.active = Nat.log2 (2 * N^2))
    (hy : regSize y.active = Nat.log2 (2 * N)) :
    regSize x.active ≤ 2 * regSize y.active := by
  have hNne : N ≠ 0 := by omega
  have hNsqne : N ^ 2 ≠ 0 := by positivity
  have hN_lt_pow :
      N < 2 ^ (Nat.log2 N + 1) :=
    (Nat.log2_lt hNne).mp (by omega)
  have hsq :
      N ^ 2 < (2 ^ (Nat.log2 N + 1)) ^ 2 := by
    nlinarith
  have hpow_eq :
      (2 ^ (Nat.log2 N + 1)) ^ 2 =
        2 ^ (2 * Nat.log2 N + 2) := by
    rw [← pow_mul]
    congr 1
    omega
  have hsq' :
      N ^ 2 < 2 ^ (2 * Nat.log2 N + 2) := by
    calc
      N ^ 2 < (2 ^ (Nat.log2 N + 1)) ^ 2 := hsq
      _ = 2 ^ (2 * Nat.log2 N + 2) := hpow_eq
  have hlogSq :
      Nat.log2 (N ^ 2) < 2 * Nat.log2 N + 2 :=
    (Nat.log2_lt hNsqne).mpr hsq'
  rw [hx, hy]
  rw [Nat.log2_two_mul hNsqne]
  rw [Nat.log2_two_mul hNne]
  omega

/-- Algorithm 1 precision gives a linear work-width bound once the extra bits fit the chosen constant. -/
lemma Algorithm1Precision.work_width_le_mul
    {η : ℝ}
    {data work : Reg}
    {cWork : ℕ}
    (hcWork : 1 ≤ cWork)
    (h : Algorithm1Precision η data work)
    (hExtra :
      algorithm1ExtraBits η ≤
        (cWork - 1) * regSize data) :
    regSize work ≤ cWork * regSize data := by
  rw [work_width h]
  calc
    regSize data + algorithm1ExtraBits η
        ≤ regSize data + (cWork - 1) * regSize data :=
      Nat.add_le_add_left hExtra _
    _ = cWork * regSize data := by
      calc
        regSize data + (cWork - 1) * regSize data =
            (1 + (cWork - 1)) * regSize data := by
          rw [Nat.add_mul, one_mul]
        _ = cWork * regSize data := by
          rw [Nat.add_comm, Nat.sub_add_cancel hcWork]

/-- Rewrites the inverse precision scale for the Shor precision schedule. -/
lemma shorEta_inv_two_mul
    (δ : ℝ)
    (hδ : 0 < δ)
    (n : ℕ)
    (hn : 1 ≤ n) :
    1 / (2 * shorEta δ n) =
      (n : ℝ)^2 / (2 * δ) := by
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hn)
  dsimp [shorEta]
  field_simp [hδ.ne', hn0]

/-- The extra precision bits required by `shorEta` are eventually linear in the data width. -/
lemma algorithm1ExtraBits_shorEta_eventually_linear
    (δ : ℝ)
    (hδ : 0 < δ) :
    ∃ cWork : ℕ, 1 ≤ cWork ∧
    ∃ nExtra : ℕ, 1 ≤ nExtra ∧
      ∀ n : ℕ,
        nExtra ≤ n →
        algorithm1ExtraBits (shorEta δ n)
          ≤ (cWork - 1) * n := by
  have hconst :
      Tendsto
        (fun n : ℕ => (2 : ℝ) / (2 : ℝ)^n)
        atTop (nhds 0) := by
    simpa using
      (tendsto_pow_const_div_const_pow_of_one_lt
        0
        (show (1 : ℝ) < 2 by norm_num)).const_mul (2 : ℝ)
  have hquad0 :
      Tendsto
        (fun n : ℕ => ((n : ℝ)^2 / (2 : ℝ)^n))
        atTop (nhds 0) := by
    simpa using
      (tendsto_pow_const_div_const_pow_of_one_lt
        2
        (show (1 : ℝ) < 2 by norm_num))
  have hquad :
      Tendsto
        (fun n : ℕ =>
          ((n : ℝ)^2 / (2 * δ)) / (2 : ℝ)^n)
        atTop (nhds 0) := by
    have h :=
      hquad0.const_mul ((2 * δ)⁻¹)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  have hsum :
      Tendsto
        (fun n : ℕ =>
          (2 + (n : ℝ)^2 / (2 * δ)) / (2 : ℝ)^n)
        atTop (nhds 0) := by
    have h := hconst.add hquad
    simpa [zero_add] using
      h.congr' (by
        filter_upwards with n
        field_simp [
          pow_ne_zero _
            (show (2 : ℝ) ≠ 0 by norm_num)])
  have hlt :
      ∀ᶠ n : ℕ in atTop,
        (2 + (n : ℝ)^2 / (2 * δ)) / (2 : ℝ)^n < 1 :=
    hsum.eventually
      (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  rw [eventually_atTop] at hlt
  rcases hlt with ⟨N, hN⟩
  refine ⟨3, by omega, max 1 N, by omega, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := by omega
  have hratio :
      (2 + (n : ℝ)^2 / (2 * δ)) / (2 : ℝ)^n < 1 :=
    hN n (by omega)
  have hdenpos : 0 < (2 : ℝ)^n :=
    pow_pos (by norm_num) _
  have harg_le_pow :
      2 + (n : ℝ)^2 / (2 * δ) ≤ (2 : ℝ)^n := by
    have hmul :=
      mul_lt_mul_of_pos_right hratio hdenpos
    exact le_of_lt <| by
      calc
        2 + (n : ℝ)^2 / (2 * δ) =
            ((2 + (n : ℝ)^2 / (2 * δ)) / (2 : ℝ)^n) *
              (2 : ℝ)^n := by
          field_simp [
            pow_ne_zero _
              (show (2 : ℝ) ≠ 0 by norm_num)]
        _ < (1 : ℝ) * (2 : ℝ)^n := hmul
        _ = (2 : ℝ)^n := by ring
  have hargpos :
      0 < 2 + (n : ℝ)^2 / (2 * δ) := by
    positivity
  have hlog :
      Real.logb 2 (2 + (n : ℝ)^2 / (2 * δ))
        ≤ (n : ℝ) := by
    have hp :
        2 + (n : ℝ)^2 / (2 * δ)
          ≤ (2 : ℝ) ^ (n : ℝ) := by
      simpa [Real.rpow_natCast] using harg_le_pow
    exact
      (Real.logb_le_iff_le_rpow
        (show (1 : ℝ) < 2 by norm_num)
        hargpos).2 hp
  have heta :
      1 / (2 * shorEta δ n) =
        (n : ℝ)^2 / (2 * δ) :=
    shorEta_inv_two_mul δ hδ n hn1
  have hceil :
      algorithm1ExtraBits (shorEta δ n) ≤ 2 * n := by
    dsimp [algorithm1ExtraBits]
    rw [heta]
    exact
      Nat.ceil_le.mpr (by
        norm_num
        nlinarith)
  simpa using hceil

end ExponentAndWidthConversions

/-! ---------------------------------------------------------
    Public setup to counting layout

This section extracts the compact counting layout from the richer correctness
setup used by the approximate Shor circuit.
--------------------------------------------------------- -/

section SetupLayout

/-- A correctness setup satisfying the extra-bit bound also satisfies the counting layout. -/
lemma ShorApproxSetup.toShorGateCountLayout
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    {η : ℝ}
    (cWork : ℕ)
    (hcWork : 1 ≤ cWork)
    (inst : ShorOrderFindingInstance)
    (work : ExtReg)
    (flag : ℕ)
    (b0 : qs.Basis)
    (hsetup : ShorApproxSetup qs η inst.x inst.y work flag b0)
    (hExtra :
      algorithm1ExtraBits η
        ≤ (cWork - 1) * regSize inst.y.active) :
    ShorGateCountLayout cWork (regSize inst.y.active)
      inst.x inst.y work flag := by
  have hN : 1 < inst.N := by
    rcases inst.range with ⟨ha0, haN⟩
    omega
  have hxLower :
      regSize inst.y.active ≤ regSize inst.x.active :=
    shor_y_width_le_x_width
      inst.N inst.x inst.y hN inst.x_width inst.y_width
  have hxUpper :
      regSize inst.x.active ≤ 2 * regSize inst.y.active :=
    shor_x_width_le_two_y_width
      inst.N inst.x inst.y hN inst.x_width inst.y_width
  have hworkLower :
      regSize inst.y.active ≤ regSize work.active :=
    data_width_le_work_width hsetup.work_precision
  have hworkUpper :
      regSize work.active ≤ cWork * regSize inst.y.active :=
    Algorithm1Precision.work_width_le_mul
      hcWork hsetup.work_precision hExtra
  exact
    ⟨rfl, hxLower, hxUpper,
      hworkLower, hworkUpper, hsetup.register_layout⟩

end SetupLayout

/-! ---------------------------------------------------------
    Final component assembly

The final assembly theorem threads the modular-multiplication, modular
exponentiation, order-finding, QFT, and PhaseProduct component bounds together
and converts the resulting exponent to `2 + ε`.
--------------------------------------------------------- -/

section ComponentAssembly

/-- Complete Shor gate-count bound from the PhaseProduct, controlled PhaseProduct, and QFT component bounds. -/
theorem shorGateCountBound_of_components
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (ε δ : ℝ)
    (hδ : 0 < δ)
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (hExponent : phaseProductExponent k ≤ 1 + ε)
    (hPhase :
      PhaseProductGateCountBound (Basis := qs.Basis) k hk ops)
    (hCPhase :
      CPhaseProductGateCountBound (Basis := qs.Basis) k hk ops)
    (hQFT :
      QFTGateCountBound (Basis := qs.Basis) k hk ops) :
    ShorGateCountBound qs ε δ k hk ops := by
  rcases algorithm1ExtraBits_shorEta_eventually_linear δ hδ with
    ⟨cWork, hcWork, nExtra, hnExtra, hExtraFits⟩
  rcases cmodMulInPlaceCore_gateCount_phase_bound
      (Basis := qs.Basis)
      cWork hcWork k hk ops hPhase hCPhase hQFT with
    ⟨A, hA, nCore, hnCore, hCore⟩
  rcases modExpApproxValid_gateCount_phase_bound_of_core
      (Basis := qs.Basis)
      cWork hcWork k hk ops A hA nCore hnCore hCore with
    ⟨B, hB, nModExp, hnModExp, hModExp⟩
  rcases orderFindingApproxLow_gateCount_phase_bound
      qs k hk ops cWork hcWork hQFT
      B hB nModExp hnModExp hModExp with
    ⟨C, hC, nOrder, hnOrder, hOrderFinding⟩
  let nFinal : ℕ := max nOrder nExtra
  have hnFinal : 1 ≤ nFinal := by
    dsimp [nFinal]
    omega
  refine ⟨C, hC, nFinal, hnFinal, ?_⟩
  intro inst work flag b0 hsetup
  dsimp
  intro hn hLowerWorkspace
  let n : ℕ := inst.y.width
  have hnOrder' : nOrder ≤ n := by
    dsimp [nFinal, n] at hn
    omega
  have hnExtra' : nExtra ≤ n := by
    dsimp [nFinal, n] at hn
    omega
  have hnOne : 1 ≤ n :=
    hnOrder.trans hnOrder'
  have hExtra :
      algorithm1ExtraBits
          (shorEta δ inst.y.width)
        ≤ (cWork - 1) * regSize inst.y.active := by
    have :=
      hExtraFits inst.y.width (by simpa [n] using hnExtra')
    simpa [ExtReg.width] using this
  have hLayout :
      ShorGateCountLayout cWork n
        inst.x inst.y work flag := by
    dsimp [n]
    simpa [ExtReg.width] using
      ShorApproxSetup.toShorGateCountLayout
        cWork hcWork inst work flag b0 hsetup hExtra
  have hPreliminary :
      (shorOrderFindingGateCount qs k hk ops
          inst.a inst.N inst.x inst.y work flag
          hsetup.circuit_workspace hLowerWorkspace : ℝ)
        ≤ C *
          Real.rpow (n : ℝ)
            (1 + phaseProductExponent k) :=
    hOrderFinding n inst.a inst.N
      inst.x inst.y work flag hsetup.circuit_workspace
      hLowerWorkspace hnOrder' hLayout
  have hRate :
      Real.rpow (n : ℝ) (1 + phaseProductExponent k)
        ≤ shorGateRate ε n :=
    phaseProduct_succ_rate_le_shorGateRate
      ε k n hnOne hExponent
  exact
    hPreliminary.trans
      (mul_le_mul_of_nonneg_left hRate (le_of_lt hC))

/-- Complete Shor gate-count bound for any PhaseProduct program satisfying the generated-program contract. -/
theorem shorGateCountBound_of_programOK
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (ε δ : ℝ)
    (hδ : 0 < δ)
    (k : ℕ)
    (hk : 1 < k)
    (hExponent : phaseProductExponent k ≤ 1 + ε) :
    ∀ ops : Prog k,
      PhaseProductProgramOK k hk ops →
      ShorGateCountBound qs ε δ k hk ops := by
  intro ops hops
  exact
    shorGateCountBound_of_components
      qs ε δ hδ k hk ops hExponent
      (phaseProductGateCountBound_of_programOK
        (Basis := qs.Basis) k hk ops hops)
      (CPhaseProductReduction.cPhaseProductGateCountBound_of_programOK
        (Basis := qs.Basis) k hk ops hops)
      (qftGateCountBound_of_programOK
        (Basis := qs.Basis) k hk ops hops)

end ComponentAssembly

/-! ---------------------------------------------------------
    Existence of a suitable recursion parameter and program

These final theorems choose a large enough interpolation arity `k`, instantiate
the generated interpolation program, and package the existential version of the
complete Shor gate-count bound.
--------------------------------------------------------- -/

section ExistenceResults

/-- For every positive `ε`, some arity `k` makes the PhaseProduct exponent at most `1 + ε`. -/
lemma exists_k_phaseProductExponent_le
    (ε : ℝ)
    (hε : 0 < ε) :
    ∃ k : ℕ,
      1 < k ∧
      phaseProductExponent k ≤ 1 + ε := by
  obtain ⟨m : ℕ, hm⟩ :=
    exists_nat_gt (1 / ε)
  let k : ℕ := 2 ^ (m + 1)
  have hpowpos : 0 < 2 ^ m := by positivity
  have hk : 1 < k := by
    dsimp [k]
    rw [pow_succ]
    omega
  have hkR : (1 : ℝ) < (k : ℝ) := by
    exact_mod_cast hk
  have hlogk_pos : 0 < Real.log (k : ℝ) :=
    Real.log_pos hkR
  have hm_succ :
      1 / ε < ((m + 1 : ℕ) : ℝ) := by
    calc
      1 / ε < (m : ℝ) := hm
      _ < ((m + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.lt_succ_self m
  have hmε :
      1 < ((m + 1 : ℕ) : ℝ) * ε :=
    (div_lt_iff₀ hε).mp hm_succ
  have hk_cast :
      (k : ℝ) = (2 : ℝ) ^ (m + 1) := by
    simp [k]
  have hlogk :
      Real.log (k : ℝ) =
        ((m + 1 : ℕ) : ℝ) * Real.log 2 := by
    rw [hk_cast, Real.log_pow]
  have hlog2_pos :
      0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hlog2_le :
      Real.log 2 ≤ ε * Real.log (k : ℝ) := by
    have hmε_le :
        (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * ε :=
      le_of_lt hmε
    calc
      Real.log 2 = 1 * Real.log 2 := by ring
      _ ≤ (((m + 1 : ℕ) : ℝ) * ε) * Real.log 2 :=
        mul_le_mul_of_nonneg_right hmε_le (le_of_lt hlog2_pos)
      _ = ε * Real.log (k : ℝ) := by
        rw [hlogk]
        ring
  have hq_pos_nat : 0 < q k := by
    unfold q
    omega
  have hq_lt_nat : q k < 2 * k := by
    unfold q
    omega
  have hq_pos : 0 < (q k : ℝ) := by
    exact_mod_cast hq_pos_nat
  have hq_lt : (q k : ℝ) < 2 * (k : ℝ) := by
    exact_mod_cast hq_lt_nat
  have hlogq_le :
      Real.log (q k : ℝ) ≤
        Real.log (2 * (k : ℝ)) :=
    le_of_lt (Real.log_lt_log hq_pos hq_lt)
  refine ⟨k, hk, ?_⟩
  unfold phaseProductExponent
  rw [div_le_iff₀ hlogk_pos]
  calc
    Real.log (q k : ℝ)
        ≤ Real.log (2 * (k : ℝ)) := hlogq_le
    _ = Real.log 2 + Real.log (k : ℝ) := by
      rw [Real.log_mul
        (by norm_num : (2 : ℝ) ≠ 0)
        (by positivity : (k : ℝ) ≠ 0)]
    _ ≤ (1 + ε) * Real.log (k : ℝ) := by
      nlinarith [hlog2_le]

/-- The generated interpolation program satisfies the PhaseProduct program contract for every valid arity. -/
theorem exists_phaseProductProgramOK
    (k : ℕ)
    (hk : 1 < k) :
    ∃ ops : Prog k,
      PhaseProductProgramOK k hk ops := by
  have hk0 : 0 < k := by omega
  refine
    ⟨genOpsWithProduct (k := k) hk0
      (genInterpolationPoints k), ?_⟩
  unfold PhaseProductProgramOK
  dsimp
  exact
    ⟨by simpa using genInterpolationPoints_good k,
      genOpsWithProduct_ProgConsumesPtsSafe
        (k := k) hk0 (genInterpolationPoints k),
      genOpsWithProduct_returns_to_original
        (k := k) hk0 (genInterpolationPoints k),
      by
        simpa [genInterpolationPoints, q] using
          phaseProductCount_genOpsWithProduct
            (k := k) hk0 (genInterpolationPoints k)⟩

/-- Existential complete Shor gate-count theorem: choose both `k` and the generated PhaseProduct program. -/
theorem exists_shorGateCountBound
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (ε δ : ℝ)
    (hδ : 0 < δ)
    (hε : 0 < ε) :
    ∃ k : ℕ,
    ∃ hk : 1 < k,
    ∃ ops : Prog k,
      PhaseProductProgramOK k hk ops ∧
      ShorGateCountBound qs ε δ k hk ops := by
  rcases exists_k_phaseProductExponent_le ε hε with
    ⟨k, hk, hExponent⟩
  rcases exists_phaseProductProgramOK k hk with
    ⟨ops, hops⟩
  exact
    ⟨k, hk, ops, hops,
      shorGateCountBound_of_programOK
        qs ε δ hδ k hk hExponent ops hops⟩

/-- Chooses only `k`; any program satisfying the PhaseProduct contract then yields the Shor bound. -/
theorem exists_k_shorGateCountBound_of_programOK
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (ε δ : ℝ)
    (hε : 0 < ε)
    (hδ : 0 < δ) :
    ∃ (k : ℕ) (hk : 1 < k),
      ∀ ops : Prog k,
        PhaseProductProgramOK k hk ops →
        ShorGateCountBound qs ε δ k hk ops := by
  rcases exists_k_phaseProductExponent_le ε hε with
    ⟨k, hk, hExponent⟩
  exact
    ⟨k, hk,
      shorGateCountBound_of_programOK
        qs ε δ hδ k hk hExponent⟩

end ExistenceResults

end Shor
