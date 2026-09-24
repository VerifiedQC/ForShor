import FastMultiplication.ShorVerification.Implementation.Shor.Lowering.LowerGate
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.Steps
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.ModExp

/-!
# Order-Finding Circuits

The approximate circuit uses the verified modular-exponentiation implementation;
the ideal circuit swaps in the abstract exact modular exponentiation gate.
-/
namespace Shor
open Operations

/-- Initialize the data register to the computational basis value `1`. -/
def initY1 (y : Reg) : Gate :=
  match y.qubits with
  | [] => Gate.id
  | q :: _ => Gate.X q

/-- Approximate order finding using the proved valid-input ModExp circuit. -/
def orderFindingApprox
    (a N : ℕ)
    (x y work scratch : ExtReg)
    (flag : ℕ)
    (hworkspace : ModMulCircuitWorkspaceOK y work)
    (hstep4 :
      CmpLtNWWorkspace N (y.grow 1) work scratch flag) :
    Gate :=
  (H_reg x.active) ;;
  (initY1 y.active) ;;
  (modExpApproxValid
    a N x.active y work scratch flag
    hworkspace hstep4) ;;
  (IQFT x)


/-- The lowered implementation of approximate order finding. -/
def orderFindingApproxLow
    (k : ℕ) (hk : 1 < k)
    (ops : Prog k)
    (pts : List Point) (hpts : pts.length = q k)
    (a N : ℕ)
    (x y work scratch : ExtReg)
    (flag : ℕ)
    (hmodWorkspace : ModMulCircuitWorkspaceOK y work)
    (hstep4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hLowerWorkspace : GateWorkspaceOK ops (orderFindingApprox a N x y work scratch flag
          hmodWorkspace hstep4)) :=
  lowerGate k hk ops pts hpts (orderFindingApprox a N x y work scratch flag hmodWorkspace hstep4)
    hLowerWorkspace

/-- Ideal order-finding circuit using exact modular exponentiation. -/
noncomputable def orderFindingIdeal
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (a N : ℕ)
    (x y : ExtReg) : Gate :=
  (H_reg x.active) ;;
  (initY1 y.active) ;;
  (modExpIdeal' qs a N x.active y.active) ;;
  (IQFT x)

end Shor
