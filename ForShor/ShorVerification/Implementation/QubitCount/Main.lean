import ForShor.ShorVerification.Implementation.QubitCount.Statement
import ForShor.ShorVerification.Implementation.QubitCount.Proofs.Formula
import ForShor.ShorVerification.Implementation.QubitCount.Proofs.BalancedU
import ForShor.ShorVerification.Implementation.QubitCount.Proofs.Numerals
import ForShor.ShorVerification.Implementation.QubitCount.Proofs.BalancedNumerals

/-!
# Qubit count: main theorems

The three formulas of `Statement.lean`, proved: the lowered order-finding
circuit, the circuit after the balanced split, and the circuit after the
unconditional balanced split. The 2048-bit numbers are in `Proofs/Numerals.lean`
and `Proofs/BalancedNumerals.lean`.
-/

namespace Shor

open QubitCount

/-- **The qubit-count formula for the lowered order-finding circuit.** -/
theorem Policy.orderFinding_peak_formula (P : ShorLoweringPolicy) :
    Policy.OrderFindingPeakFormula P :=
  QubitCount.orderFindingPeakFormula P

/-- **The qubit-count formula for the balanced order-finding circuit.** Each
phase-product site costs what it runs: its split where the operands' spare
qubits fit the plan, the product itself otherwise. -/
theorem Policy.orderFinding_peak_formula_balanced (P : ShorLoweringPolicy) (R : Balanced.Rule) :
    Policy.OrderFindingPeakFormulaBalanced P R :=
  QubitCount.orderFindingPeakFormulaBalanced P R

/-- **The qubit-count formula for the unconditionally balanced order-finding
circuit.** Every site is split, so the count is a function of the register
widths alone. -/
theorem Policy.orderFinding_peak_formula_balanced_u (P : ShorLoweringPolicy) (R : Balanced.Rule) :
    Policy.OrderFindingPeakFormulaBalancedU P R :=
  QubitCount.orderFindingPeakFormulaBalancedU P R

end Shor
