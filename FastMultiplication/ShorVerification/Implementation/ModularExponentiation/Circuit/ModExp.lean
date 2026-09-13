import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.Workspace
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.Steps

/-!
# Modular-Exponentiation Circuit: Exponentiation Layer

The ideal specification (`tbits`, `modExpIdealSteps`, `modExpIdeal'`) and the
approximate modular-exponentiation recursion over a list of control qubits
(`ModExpLayout`, `ModExpArithmeticOK`, `modExpApproxStepsValid`,
`modExpApproxValid`), built from the per-core `CmodMulInPlaceCore` circuit.
-/

namespace Shor

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
    (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsCore qs] (a N : ℕ) (x data : Reg) :
    Gate :=
  modExpIdealSteps qs a N data 0 x.qubits

/-- Every exponent/control qubit has a valid modular-multiplication core layout. -/
def ModExpLayout (x : Reg) (data work : ExtReg) (flag : ℕ) : Prop :=
  ∀ i : Fin (regSize x), ModMulCoreLayout data work flag (x.get i)

/-- Every multiplier used by modular exponentiation is coprime to the modulus. -/
def ModExpArithmeticOK (a N : ℕ) (x : Reg) : Prop :=
  ∀ i : Fin (regSize x), Nat.Coprime ((a ^ (2 ^ i.1)) % N) N

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
      CmodMulInPlaceCore c N ctrl data work scratch flag hworkspace hstep4 ;;
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

end Shor
