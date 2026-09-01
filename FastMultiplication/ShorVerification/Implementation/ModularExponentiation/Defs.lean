import FastMultiplication.ShorVerification.Framework.Semantics.GateSemantics
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Defs
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.GateLevelCorrectness.GateSemanticsLemmas
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.CmpLtNW
import Mathlib.Data.Int.GCD
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Modular-Exponentiation Definitions

The minimal definitional vocabulary needed to state the modular-exponentiation
correctness assertion (`Assertions.lean`): the gate constructions, configs, and
validity predicates.  All proofs live under `ModularExponentiation.Proofs`.
-/

universe u v

namespace Shor

/-! =========================================================
    Modular Multiplication Bounds Core

This file contains the shared definitions for the modular-multiplication and
modular-exponentiation approximation proofs: ideal specifications, Algorithm 1
gates, layout and validity predicates, precision side conditions, reusable
configuration records, and the reference packets used by the Step 1/2/3/4/5
bound files.
========================================================= -/

/-! ---------------------------------------------------------
    Shared circuit syntax and workspace

This section defines the reusable high-level gates for Algorithm 1, together
with the concrete workspace predicate that provides the phase-product reserves
needed by Steps 1, 2, and 5.
--------------------------------------------------------- -/

section CircuitSyntaxAndWorkspace

/-- Inverse QFT. -/
def IQFT (r : ExtReg) : Gate :=
  †(Gate.QFT r)

/-- Apply Hadamards across all qubits of a register. -/
def H_reg (r : Reg) : Gate :=
  (regQubits r).foldl (fun acc q => (Gate.H q) ;; acc) Gate.id

/-- Build an unsigned PhaseProduct workspace from two growable, owned-disjoint extended registers. -/
def Gate.PhaseProdWorkspace.ofExtRegs
    (x z : ExtReg)
    (hx : x.CanGrow 1)
    (hz : z.CanGrow 1)
    (howned : ExtReg.OwnedDisjoint x z) :
    Gate.PhaseProdWorkspace x.active z.active := by
  have hOwned :
      ∀ q,
        q ∈ x.ownedQubits →
        q ∈ z.ownedQubits →
        False := by
    simpa [ExtReg.OwnedDisjoint, List.disjoint_left] using howned

  refine
    {
      xReserve := x.reserve
      zReserve := z.reserve

      x_can_grow := ?_
      z_can_grow := ?_

      xz_disjoint := ?_
      x_reserve_disjoint := x.active_reserve_disjoint
      z_reserve_disjoint := z.active_reserve_disjoint
      xReserve_not_z := ?_
      zReserve_not_x := ?_
      reserve_disjoint := ?_
    }

  · simpa [ExtReg.CanGrow, ExtReg.capacity] using hx
  · simpa [ExtReg.CanGrow, ExtReg.capacity] using hz

  · rw [Disjoint, List.disjoint_left]
    intro q hqx hqz
    exact hOwned q
      (by simp [ExtReg.ownedQubits, hqx])
      (by simp [ExtReg.ownedQubits, hqz])

  · rw [Disjoint, List.disjoint_left]
    intro q hqx hqz
    exact hOwned q
      (by simp [ExtReg.ownedQubits, hqx])
      (by simp [ExtReg.ownedQubits, hqz])

  · rw [Disjoint, List.disjoint_left]
    intro q hqz hqx
    exact hOwned q
      (by simp [ExtReg.ownedQubits, hqx])
      (by simp [ExtReg.ownedQubits, hqz])

  · rw [Disjoint, List.disjoint_left]
    intro q hqx hqz
    exact hOwned q
      (by simp [ExtReg.ownedQubits, hqx])
      (by simp [ExtReg.ownedQubits, hqz])

/-- Static workspace condition for one controlled modular-multiplication core. -/
def ModMulCircuitWorkspaceOK
    (data work : ExtReg) : Prop :=
  data.CanGrow 2 ∧
  work.CanGrow 1 ∧
  ExtReg.OwnedDisjoint data work

lemma ModMulCircuitWorkspaceOK.data_canGrow_one
    {data work : ExtReg}
    (h : ModMulCircuitWorkspaceOK data work) :
    data.CanGrow 1 := by
  unfold ModMulCircuitWorkspaceOK at h
  unfold ExtReg.CanGrow ExtReg.capacity at *
  omega

lemma ModMulCircuitWorkspaceOK.dataCarry_canGrow_one
    {data work : ExtReg}
    (h : ModMulCircuitWorkspaceOK data work) :
    (data.grow 1).CanGrow 1 := by
  have h1 : data.CanGrow 1 :=
    h.data_canGrow_one

  unfold ModMulCircuitWorkspaceOK at h
  rw [ExtReg.CanGrow, ExtReg.capacity_grow data 1 h1]
  unfold ExtReg.CanGrow ExtReg.capacity at h
  simp[ExtReg.CanGrow, ExtReg.capacity] at *
  omega

lemma ModMulCircuitWorkspaceOK.work_canGrow_one
    {data work : ExtReg}
    (h : ModMulCircuitWorkspaceOK data work) :
    work.CanGrow 1 :=
  h.2.1

lemma ModMulCircuitWorkspaceOK.dataCarry_work_disjoint
    {data work : ExtReg}
    (h : ModMulCircuitWorkspaceOK data work) :
    ExtReg.OwnedDisjoint (data.grow 1) work := by
  unfold ModMulCircuitWorkspaceOK at h
  unfold ExtReg.OwnedDisjoint at h ⊢
  rw [List.disjoint_left]
  intro q hqGrow hqWork
  simp [ExtReg.ownedQubits, ExtReg.grow, Reg.append,
    ExtReg.newBits, ExtReg.remainingReserve, Reg.take, Reg.drop,
    List.mem_append] at hqGrow
  have hqData : q ∈ data.ownedQubits := by
    rw [ExtReg.ownedQubits, List.mem_append]
    rcases hqGrow with hqActive | hqReserve
    · exact Or.inl hqActive
    · rcases hqReserve with hqNew | hqRemaining
      · exact Or.inr (List.mem_of_mem_take hqNew)
      · exact Or.inr (List.tail_subset _ hqRemaining)
  exact h.2.2 hqData hqWork

lemma ModMulCircuitWorkspaceOK.work_dataCarry_disjoint
    {data work : ExtReg}
    (h : ModMulCircuitWorkspaceOK data work) :
    ExtReg.OwnedDisjoint work (data.grow 1) := by
  exact List.Disjoint.symm h.dataCarry_work_disjoint

/-- The PhaseProduct workspace used by Step 1. -/
def ModMulCircuitWorkspaceOK.step1Workspace
    {data work : ExtReg}
    (h : ModMulCircuitWorkspaceOK data work) :
    Gate.PhaseProdWorkspace data.active work.active :=
  let dataNoCarry : ExtReg :=
    ExtReg.withReserve
      data.active
      (data.reserve.drop 1)
      (by
        rw [Disjoint, List.disjoint_left]
        intro q hqActive hqReserve
        have hdisj := data.active_reserve_disjoint
        rw [Disjoint, List.disjoint_left] at hdisj
        exact hdisj hqActive (List.mem_of_mem_drop hqReserve))
  Gate.PhaseProdWorkspace.ofExtRegs
    dataNoCarry work
    (by
      dsimp [dataNoCarry]
      unfold ExtReg.CanGrow ExtReg.capacity
      change 1 ≤ regSize (data.reserve.drop 1)
      simp [Reg.drop, regSize, Reg.width]
      change 1 ≤ regSize data.reserve - 1
      have hdata2 : 2 ≤ regSize data.reserve := by
        simpa [ExtReg.CanGrow, ExtReg.capacity] using h.1
      omega)
    h.work_canGrow_one
    (by
      unfold ExtReg.OwnedDisjoint
      rw [List.disjoint_left]
      intro q hqData hqWork
      apply h.2.2
      · rw [ExtReg.ownedQubits, List.mem_append] at hqData ⊢
        rcases hqData with hqActive | hqReserve
        · exact Or.inl hqActive
        · exact Or.inr (List.mem_of_mem_drop hqReserve)
      · exact hqWork)

/-- The PhaseProduct workspace used by Step 2, after growing the data register by one carry bit. -/
def ModMulCircuitWorkspaceOK.step2Workspace
    {data work : ExtReg}
    (h : ModMulCircuitWorkspaceOK data work) :
    Gate.PhaseProdWorkspace
      work.active
      (data.grow 1).active :=
  Gate.PhaseProdWorkspace.ofExtRegs
    work
    (data.grow 1)
    h.work_canGrow_one
    h.dataCarry_canGrow_one
    h.work_dataCarry_disjoint

/-- The PhaseProduct workspace used by Step 5. -/
def ModMulCircuitWorkspaceOK.step5Workspace
    {data work : ExtReg}
    (h : ModMulCircuitWorkspaceOK data work) :
    Gate.PhaseProdWorkspace
      (data.grow 1).active
      work.active :=
  Gate.PhaseProdWorkspace.ofExtRegs
    (data.grow 1)
    work
    h.dataCarry_canGrow_one
    h.work_canGrow_one
    h.dataCarry_work_disjoint

/-- Algorithm 1 Step 1: prepare the work Fourier packet and apply the first controlled phase load. -/
noncomputable def step1
    {Basis : Type v}
    [RegEncoding Basis]
    (c N ctrl : ℕ)
    (data work : ExtReg)
    (hworkspace : ModMulCircuitWorkspaceOK data work) :
    Gate :=
  let phi : ℝ := (2 * Real.pi * (((c + N - 1) % N : ℕ) : ℝ)) / (N : ℝ)

  H_reg work.active ;;
  Gate.CPhaseProdUsing
    ctrl phi
    data.active
    work.active
    hworkspace.step1Workspace ;;
  IQFT hworkspace.step1Workspace.zExt

/-- Algorithm 1 Step 2: use a PhaseProduct to transfer the work-label phase into the data-carry register. -/
noncomputable def step2
    {Basis : Type v}
    [RegEncoding Basis]
    (N : ℕ)
    (data work : ExtReg)
    (hworkspace : ModMulCircuitWorkspaceOK data work) :
    Gate :=
  let dataCarry : ExtReg := data.grow 1
  let phi : ℝ := (2 * Real.pi * (N : ℝ)) / ((2 : ℝ) ^ (regSize work.active + regSize dataCarry.active))

  Gate.QFT hworkspace.step2Workspace.zExt ;;
  Gate.PhaseProdUsing
    phi
    work.active
    dataCarry.active
    hworkspace.step2Workspace ;;
  IQFT hworkspace.step2Workspace.zExt

/-- Algorithm 1 Step 3: compare against `N` and conditionally subtract it from the data-carry register. -/
def step3 (N : ℕ) (dataCarry : Reg) (flag : ℕ) : Gate :=
  Gate.CmpGeConst N dataCarry flag ;;
  Gate.CSubConst N dataCarry flag

/-- Algorithm 1 Step 4: clear the comparator flag using the data-carry/work relation. -/
noncomputable def step4
    (N : ℕ) (dataCarry work scratch : ExtReg)
    (flag : ℕ)
    (hworkspace : CmpLtNWWorkspace N dataCarry work scratch flag) :
    Gate :=
  cmpLtNW N dataCarry work scratch flag hworkspace

/-- Algorithm 1 Step 5: adjoint cleanup for the forward fractional load using the inverse constant. -/
noncomputable def step5
    {Basis : Type v} [RegEncoding Basis]
    (k5val N : ℕ) (ctrl : ℕ) (data work : ExtReg)
    (hworkspace : ModMulCircuitWorkspaceOK data work)
    : Gate :=
  let phi : ℝ := (2 * Real.pi * ((k5val % N : ℕ) : ℝ)) / (N : ℝ)
  †((H_reg work.active) ;;
    (Gate.CPhaseProdUsing ctrl phi (data.grow 1).active work.active hworkspace.step5Workspace) ;;
    (IQFT hworkspace.step5Workspace.zExt))

/--
The Step-5 cleanup constant `1 - c⁻¹ mod N`, with the inverse chosen from
the finite modular-inverse existence theorem when it applies.
-/
noncomputable def step5Constant (c N : ℕ) : ℕ :=
  if h : ∃ cinv : ℕ, cinv < N ∧ (c * cinv) % N = 1 then
    (1 + N - Nat.find h) % N
  else
    0

/-- The five-step controlled in-place modular-multiplication core. -/
noncomputable def CmodMulInPlaceCore
    {Basis : Type v} [RegEncoding Basis]
    (c N : ℕ) (ctrl : ℕ) (data work scratch : ExtReg) (flag : ℕ)
    (hworkspace : ModMulCircuitWorkspaceOK data work)
    (hstep4 : CmpLtNWWorkspace N (data.grow 1) work scratch flag) : Gate :=
  let U1 : Gate := step1 (Basis := Basis) c N ctrl data work hworkspace
  let U2 : Gate := step2 (Basis := Basis) N data work hworkspace
  let U3 : Gate := step3 N (data.grow 1).active flag
  let U4 : Gate := step4 N (data.grow 1) work scratch flag hstep4
  let U5 : Gate := step5 (Basis := Basis)
      (step5Constant c N) N ctrl data work hworkspace
  U1 ;; U2 ;; U3 ;; U4 ;; U5

/-- Number of exponent/control bits used by modular exponentiation. -/
def tbits (x : Reg) : ℕ :=
  regSize x

/-- Ideal modular-exponentiation recursion over a list of control qubits. -/
def modExpIdealSteps (qs : QSemantics) [RegEncoding qs.Basis] [Spec]
    (a N : ℕ) (data : Reg) :
    ℕ → List ℕ → Gate
  | _, [] => Gate.id

  | e, ctrl :: ctrls =>
      Spec.idealCtrlModMul ((a ^ (2 ^ e)) % N) N data ctrl ;;
      modExpIdealSteps qs a N data (e + 1) ctrls

/-- Ideal modular exponentiation over all qubits in the exponent register. -/
def modExpIdeal'
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [Spec]
    (a N : ℕ)
    (x data : Reg) :
    Gate :=
  modExpIdealSteps qs a N data 0 x.qubits

/-- Per-core norm error scale used by the modular-exponentiation hybrid bound. -/
noncomputable def stepErr (K η : ℝ) : ℝ :=
  Real.sqrt (2 * (K * η))

end CircuitSyntaxAndWorkspace

/-! ---------------------------------------------------------
    Valid inputs and ideal controlled multiplication

The later approximation theorems work on a valid-input subspace. This section
defines the layout and clean-input predicates for that subspace, specifies the
ideal controlled modular multiplier on good basis states, and proves that the
ideal gate preserves the whole valid subspace.
--------------------------------------------------------- -/

section ValidInputsAndIdealSemantics

/--
The full valid-input subspace.

This is the span of *all* computational-basis states satisfying
`GoodModMulBasisInput`; hence it includes arbitrary superpositions over
the control register, exponent register, and valid modular data values.
-/
def ValidModMulState
    (qs : QSemantics) [RegEncoding qs.Basis]
    (N : ℕ) (data work : ExtReg) (flag : ℕ) :
    Submodule ℂ qs.State :=
  Submodule.span ℂ
    ({ ψ : qs.State |
        ∃ b : qs.Basis,
          GoodModMulBasisInput qs N data work flag b ∧
          ψ = qs.ket b } : Set qs.State)

def GoodAlgorithm1BasisInput
    (qs : QSemantics) [RegEncoding qs.Basis]
    (N : ℕ)
    (data work scratch : ExtReg)
    (flag : ℕ)
    (b : qs.Basis) : Prop :=
  GoodModMulBasisInput qs N data work flag b ∧
  RegEncoding.toNat scratch.active b = 0 ∧
  scratch.FreshFor 1 b

def ValidAlgorithm1State
    (qs : QSemantics) [RegEncoding qs.Basis]
    (N : ℕ)
    (data work scratch : ExtReg)
    (flag : ℕ) :
    Submodule ℂ qs.State :=
  Submodule.span ℂ
    ({ ψ : qs.State |
        ∃ b : qs.Basis,
          GoodAlgorithm1BasisInput
            qs N data work scratch flag b ∧
          ψ = qs.ket b } : Set qs.State)

end ValidInputsAndIdealSemantics

/-! ---------------------------------------------------------
    Algorithm 1 precision and arithmetic constants

This section packages the concrete precision schedule for Algorithm 1 and the
Step-5 inverse constant used by the cleanup phase.
--------------------------------------------------------- -/

section Algorithm1PrecisionAndConstants

/-- Extra work-register bits prescribed by the Algorithm 1 precision parameter. -/
noncomputable def algorithm1ExtraBits (η : ℝ) : ℕ :=
  ⌈2 * Real.logb 2 (2 + 1 / (2 * η))⌉₊

/--
A sufficient precision condition for the work register.

If `n = regSize data` and `m = regSize work`, this says

  2^(m - n) ≥ (2 + 1 / (2η))^2,

which is implied by the paper's choice
`m = n + ceil (2 * log₂ (2 + 1 / (2η)))`.
-/
def Algorithm1Precision
    (η : ℝ) (data work : Reg) : Prop :=
  0 < η ∧
  η < (1 / 2 : ℝ) ∧
  regSize work =
    regSize data + algorithm1ExtraBits η
end Algorithm1PrecisionAndConstants

/-! ---------------------------------------------------------
    Modular-exponentiation layout and gates

The current modular-exponentiation API recurses over a list of control qubits.
These predicates and gates express the layout and coprimality side conditions
for that list-based recursion.
--------------------------------------------------------- -/

section ModExpLayoutAndGates

/-- Every exponent/control qubit has a valid modular-multiplication core layout. -/
def ModExpLayout
    (x : Reg)
    (data work : ExtReg)
    (flag : ℕ) :
    Prop :=
  ∀ i : Fin (regSize x),
    ModMulCoreLayout data work flag (x.get i)

/-- Every multiplier used by modular exponentiation is coprime to the modulus. -/
def ModExpArithmeticOK
    (a N : ℕ)
    (x : Reg) :
    Prop :=
  ∀ i : Fin (regSize x),
    Nat.Coprime ((a ^ (2 ^ i.1)) % N) N

/-- Approximate modular-exponentiation recursion over a list of controls, using valid Algorithm 1 cores. -/
noncomputable def modExpApproxStepsValid
    {Basis : Type u}
    [RegEncoding Basis]
    (a N : ℕ)
    (data work scratch : ExtReg)
    (flag : ℕ)
    (hworkspace : ModMulCircuitWorkspaceOK data work)
    (hstep4 : CmpLtNWWorkspace N (data.grow 1) work scratch flag) :
    ℕ → List ℕ → Gate
  | _, [] =>
      Gate.id
  | e, ctrl :: ctrls =>
      let c := (a ^ (2 ^ e)) % N
      CmodMulInPlaceCore (Basis := Basis) c N ctrl data work scratch flag hworkspace hstep4
      ;;
      modExpApproxStepsValid (Basis := Basis) a N data work scratch flag hworkspace hstep4 (e + 1) ctrls

/-- Approximate modular exponentiation over all qubits in the exponent register. -/
noncomputable def modExpApproxValid
    {Basis : Type u}
    [RegEncoding Basis]
    (a N : ℕ)
    (x : Reg)
    (data work scratch : ExtReg)
    (flag : ℕ)
    (hworkspace : ModMulCircuitWorkspaceOK data work)
    (hstep4 : CmpLtNWWorkspace N (data.grow 1) work scratch flag) :
    Gate :=
  modExpApproxStepsValid (Basis := Basis) a N data work scratch flag hworkspace hstep4 0 x.qubits
end ModExpLayoutAndGates

/-! ---------------------------------------------------------
    Shared configurations

The bound files pass around compact records rather than repeatedly threading the
modulus, registers, precision proof, workspace proof, layout proof, and
coprimality hypotheses.
--------------------------------------------------------- -/

section SharedConfigurations

/-- Common environment for one Algorithm 1 modular-multiplication analysis. -/
structure Algorithm1Env (η : ℝ) where
  N : ℕ
  data : ExtReg
  work : ExtReg
  scratch : ExtReg
  modulus_gt_one : 1 < N
  data_capacity  : N ≤ ASize data.active
  precision      : Algorithm1Precision η data.active work.active
  circuit_workspace : ModMulCircuitWorkspaceOK data work

/-- Configuration for approximate modular exponentiation. -/
structure ModExpConfig (η : ℝ) where
  env : Algorithm1Env η
  a : ℕ
  x : Reg
  flag : ℕ

  layout : ModExpLayout x env.data env.work flag

  arithmetic : ModExpArithmeticOK a env.N x

  step4_workspace : CmpLtNWWorkspace env.N (env.data.grow 1) env.work env.scratch flag

namespace ModExpConfig

/-- Concrete approximate modular-exponentiation gate for this configuration. -/
noncomputable def approxGate
    {η : ℝ}
    {Basis : Type u} [RegEncoding Basis] (cfg : ModExpConfig η) : Gate :=
  modExpApproxValid
    (Basis := Basis)
    cfg.a cfg.env.N cfg.x cfg.env.data cfg.env.work cfg.env.scratch cfg.flag cfg.env.circuit_workspace cfg.step4_workspace

/-- Ideal modular-exponentiation gate for this configuration. -/
def idealGate
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [Spec]
    {η : ℝ}
    (cfg : ModExpConfig η) : Gate :=
  modExpIdeal' qs cfg.a cfg.env.N cfg.x cfg.env.data.active

/-- Valid modular-multiplication state with unit norm for modular exponentiation. -/
def ValidUnitState
    (qs : QSemantics) [RegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModExpConfig η) (ψ : qs.State) : Prop :=
  ψ ∈ ValidAlgorithm1State
      qs cfg.env.N cfg.env.data cfg.env.work
        cfg.env.scratch cfg.flag
    ∧ ‖ψ‖ = 1

end ModExpConfig

/-! ---------------------------------------------------------
    One controlled modular multiplication
--------------------------------------------------------- -/

/-- Configuration for one controlled modular-multiplication core. -/
structure ModMulConfig (η : ℝ) where
  env : Algorithm1Env η
  c : ℕ
  flag : ℕ
  ctrl : ℕ
  coprime  : Nat.Coprime c env.N
  layout   : ModMulCoreLayout env.data env.work flag ctrl
  step4_workspace : CmpLtNWWorkspace env.N (env.data.grow 1) env.work env.scratch flag

namespace ModMulConfig

/-- Concrete five-step approximate modular-multiplication gate for this configuration. -/
noncomputable def approxGate
    {η : ℝ}
    {Basis : Type u} [RegEncoding Basis]
    (cfg : ModMulConfig η) : Gate :=
  CmodMulInPlaceCore (Basis := Basis) cfg.c cfg.env.N
    cfg.ctrl cfg.env.data cfg.env.work cfg.env.scratch cfg.flag
    cfg.env.circuit_workspace cfg.step4_workspace

/-- Ideal controlled modular-multiplication gate for this configuration. -/
def idealGate
    {η : ℝ}
    [Spec]
    (cfg : ModMulConfig η) : Gate :=
  Spec.idealCtrlModMul cfg.c cfg.env.N cfg.env.data.active cfg.ctrl

/-- Valid-state predicate for one modular-multiplication configuration. -/
def ValidState
    (qs : QSemantics) [RegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η) (ψ : qs.State) : Prop :=
  ψ ∈ ValidAlgorithm1State
    qs cfg.env.N cfg.env.data cfg.env.work cfg.env.scratch cfg.flag

/-- Valid modular-multiplication state with unit norm. -/
def ValidUnitState
    (qs : QSemantics) [RegEncoding qs.Basis]
    {η : ℝ}
    (cfg : ModMulConfig η) (ψ : qs.State) : Prop :=
  cfg.ValidState qs ψ ∧ ‖ψ‖ = 1

end ModMulConfig

end SharedConfigurations

end Shor
