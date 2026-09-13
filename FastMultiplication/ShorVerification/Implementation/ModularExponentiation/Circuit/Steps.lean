import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.Workspace
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.CmpLtNW

/-!
# Modular-Exponentiation Circuit: Algorithm-1 Steps

The reusable high-level gates for Algorithm 1 (`IQFT`, `H_reg`), the five
circuit steps (`step1`…`step5`, `step5Constant`), and the five-step controlled
in-place modular-multiplication core they assemble (`CmodMulInPlaceCore`).
-/

namespace Shor

open Gate

/-- Inverse QFT. -/
def IQFT (r : ExtReg) : Gate :=
  †(Gate.QFT r)

/-- Apply Hadamards across all qubits of a register. -/
def H_reg (r : Reg) : Gate :=
  (regQubits r).foldl (fun acc q => (Gate.H q) ;; acc) Gate.id

/-- Algorithm 1 Step 1: prepare the work Fourier packet and apply the first controlled phase load. -/
def step1
    (c N ctrl : ℕ) (data work : ExtReg) (hworkspace : ModMulCircuitWorkspaceOK data work) : Gate :=
  let phi : Angle := (2 * (((c + N - 1) % N : ℕ) : ℚ)) / (N : ℚ)
  H_reg work.active ;;
  Gate.CPhaseProdUsing ctrl phi data.active work.active hworkspace.step1Workspace ;;
  IQFT hworkspace.step1Workspace.zExt

/-- Algorithm 1 Step 2: use a PhaseProduct to transfer the work-label phase into the data-carry register. -/
def step2 (N : ℕ) (data work : ExtReg) (hworkspace : ModMulCircuitWorkspaceOK data work) : Gate :=
  let dataCarry : ExtReg := data.grow 1
  let phi : Angle := (2 * (N : ℚ)) / (2 : ℚ) ^ (regSize work.active + regSize dataCarry.active)
  Gate.QFT hworkspace.step2Workspace.zExt ;;
  Gate.PhaseProdUsing phi work.active dataCarry.active hworkspace.step2Workspace ;;
  IQFT hworkspace.step2Workspace.zExt

/-- Algorithm 1 Step 3: compare against `N` and conditionally subtract it from the data-carry register. -/
def step3 (N : ℕ) (dataCarry scratch : ExtReg) (flag : ℕ) : Gate :=
  Gate.CmpGeConst N dataCarry scratch flag ;;
  Gate.CSubConst N dataCarry scratch flag

/-- Algorithm 1 Step 4: clear the comparator flag using the data-carry/work relation. -/
def step4
    (N : ℕ) (dataCarry work scratch : ExtReg) (flag : ℕ)
    (hworkspace : CmpLtNWWorkspace N dataCarry work scratch flag) :
    Gate :=
  cmpLtNW N dataCarry work scratch flag hworkspace

/-- Algorithm 1 Step 5: adjoint cleanup for the forward fractional load using the inverse constant. -/
def step5
    (k5val N : ℕ) (ctrl : ℕ) (data work : ExtReg) (hworkspace : ModMulCircuitWorkspaceOK data work) :
    Gate :=
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
  let U5 : Gate := step5 (step5Constant c N) N ctrl data work hworkspace
  U1 ;; U2 ;; U3 ;; U4 ;; U5

end Shor
