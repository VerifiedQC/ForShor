import FastMultiplication.ShorVerification.Framework.Semantics.GateSemantics
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Gates.Macros
import FastMultiplication.ShorVerification.Implementation.Semantics.GateSemanticsLemmas
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.CmpLtNW
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Spec.Precision
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Spec.Validity
import Mathlib.Data.Int.GCD

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
def step1
    (c N ctrl : ℕ)
    (data work : ExtReg)
    (hworkspace : ModMulCircuitWorkspaceOK data work) :
    Gate :=
  let phi : Angle := (2 * (((c + N - 1) % N : ℕ) : ℚ)) / (N : ℚ)

  H_reg work.active ;;
  Gate.CPhaseProdUsing
    ctrl phi
    data.active
    work.active
    hworkspace.step1Workspace ;;
  IQFT hworkspace.step1Workspace.zExt

/-- Algorithm 1 Step 2: use a PhaseProduct to transfer the work-label phase into the data-carry register. -/
def step2
    (N : ℕ)
    (data work : ExtReg)
    (hworkspace : ModMulCircuitWorkspaceOK data work) :
    Gate :=
  let dataCarry : ExtReg := data.grow 1
  let phi : Angle := (2 * (N : ℚ)) / (2 : ℚ) ^ (regSize work.active + regSize dataCarry.active)

  Gate.QFT hworkspace.step2Workspace.zExt ;;
  Gate.PhaseProdUsing
    phi
    work.active
    dataCarry.active
    hworkspace.step2Workspace ;;
  IQFT hworkspace.step2Workspace.zExt

/-- Algorithm 1 Step 3: compare against `N` and conditionally subtract it from the data-carry register. -/
def step3 (N : ℕ) (dataCarry scratch : ExtReg) (flag : ℕ) : Gate :=
  Gate.CmpGeConst N dataCarry scratch flag ;;
  Gate.CSubConst N dataCarry scratch flag

/-- Algorithm 1 Step 4: clear the comparator flag using the data-carry/work relation. -/
def step4
    (N : ℕ) (dataCarry work scratch : ExtReg)
    (flag : ℕ)
    (hworkspace : CmpLtNWWorkspace N dataCarry work scratch flag) :
    Gate :=
  cmpLtNW N dataCarry work scratch flag hworkspace

/-- Algorithm 1 Step 5: adjoint cleanup for the forward fractional load using the inverse constant. -/
def step5
    (k5val N : ℕ) (ctrl : ℕ) (data work : ExtReg)
    (hworkspace : ModMulCircuitWorkspaceOK data work)
    : Gate :=
  let phi : Angle := (2 * ((k5val % N : ℕ) : ℚ)) / (N : ℚ)
  †((H_reg work.active) ;;
    (Gate.CPhaseProdUsing ctrl phi (data.grow 1).active work.active hworkspace.step5Workspace) ;;
    (IQFT hworkspace.step5Workspace.zExt))

/--
The Step-5 cleanup constant `1 - c⁻¹ mod N`, with the inverse chosen from
the finite modular-inverse existence theorem when it applies.
-/
def step5Constant (c N : ℕ) : ℕ :=
  if h : ∃ cinv : ℕ, cinv < N ∧ (c * cinv) % N = 1 then
    (1 + N - Nat.find h) % N
  else
    0

/-- The five-step controlled in-place modular-multiplication core. -/
def CmodMulInPlaceCore
    (c N : ℕ) (ctrl : ℕ) (data work scratch : ExtReg) (flag : ℕ)
    (hworkspace : ModMulCircuitWorkspaceOK data work)
    (hstep4 : CmpLtNWWorkspace N (data.grow 1) work scratch flag) : Gate :=
  let U1 : Gate := step1 c N ctrl data work hworkspace
  let U2 : Gate := step2 N data work hworkspace
  let U3 : Gate := step3 N (data.grow 1) scratch flag
  let U4 : Gate := step4 N (data.grow 1) work scratch flag hstep4
  let U5 : Gate := step5
      (step5Constant c N) N ctrl data work hworkspace
  U1 ;; U2 ;; U3 ;; U4 ;; U5

/-- Number of exponent/control bits used by modular exponentiation. -/
def tbits (x : Reg) : ℕ :=
  regSize x

/-- Ideal modular-exponentiation recursion over a list of control qubits. -/
def modExpIdealSteps (qs : QSemantics) [RegEncoding qs.Basis]
    (a N : ℕ) (data : Reg) :
    ℕ → List ℕ → Gate
  | _, [] => Gate.id

  | e, ctrl :: ctrls =>
      Gate.idealCtrlModMul ((a ^ (2 ^ e)) % N) N data ctrl ;;
      modExpIdealSteps qs a N data (e + 1) ctrls

/-- Ideal modular exponentiation over all qubits in the exponent register. -/
def modExpIdeal'
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (a N : ℕ)
    (x data : Reg) :
    Gate :=
  modExpIdealSteps qs a N data 0 x.qubits

end CircuitSyntaxAndWorkspace

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
def modExpApproxStepsValid
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
      CmodMulInPlaceCore c N ctrl data work scratch flag hworkspace hstep4
      ;;
      modExpApproxStepsValid a N data work scratch flag hworkspace hstep4 (e + 1) ctrls

/-- Approximate modular exponentiation over all qubits in the exponent register. -/
def modExpApproxValid
    (a N : ℕ)
    (x : Reg)
    (data work scratch : ExtReg)
    (flag : ℕ)
    (hworkspace : ModMulCircuitWorkspaceOK data work)
    (hstep4 : CmpLtNWWorkspace N (data.grow 1) work scratch flag) :
    Gate :=
  modExpApproxStepsValid a N data work scratch flag hworkspace hstep4 0 x.qubits
end ModExpLayoutAndGates

end Shor
