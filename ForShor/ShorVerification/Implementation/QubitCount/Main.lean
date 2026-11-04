import ForShor.ShorVerification.Implementation.QubitCount.Statement
import ForShor.ShorVerification.Implementation.QubitCount.Proofs.Numerals
import ForShor.ShorVerification.Implementation.QubitCount.Proofs.BalancedNumerals

/-!
# Qubit count: main theorems

Each claim of `Statement.lean`, proved. The supporting lemmas are in
`Proofs/`.
-/

namespace Shor

open QubitCount

/-- **The qubit-count formula for the lowered order-finding circuit.** -/
theorem Policy.orderFinding_peak_formula (P : ShorLoweringPolicy) :
    Policy.OrderFindingPeakFormula P :=
  QubitCount.orderFindingPeakFormula P

/-- The formula for the reference circuit, in the reference register widths. -/
theorem Policy.reference_peak_formula (P : ShorLoweringPolicy) :
    Policy.ReferencePeakFormula P :=
  QubitCount.referencePeakFormula P

/-- **The 2048-bit count.** For every 2048-bit modulus, the reference circuit
from the standard `k = 2` table at `m2048` peaks, scratch included, at exactly
19,319 qubits when its exponent register has 4096 qubits and 19,318 when it
has 4095. -/
theorem reference_2048_peak : Reference2048Peak :=
  QubitCount.reference2048Peak

/-- **For `N = 2²⁰⁴⁸ − 1`, the peak, scratch included, is exactly 19,319
qubits.** -/
theorem reference_2048_peak_example : Reference2048PeakExample :=
  QubitCount.reference2048PeakExample

/-- **The qubit-count formula for the balanced order-finding circuit.** Each
phase-product site costs what it runs: its split where the operands' spare
qubits fit the plan, the product itself otherwise. -/
theorem Policy.orderFinding_peak_formula_balanced (P : ShorLoweringPolicy) (R : Balanced.Rule) :
    Policy.OrderFindingPeakFormulaBalanced P R :=
  QubitCount.orderFindingPeakFormulaBalanced P R

/-- **The 2048-bit count, balanced.** For every 2048-bit modulus, the
reference circuit lowered after balancing with `Balanced.defaultRule` peaks,
scratch included, at exactly 17,291 qubits when its exponent register has 4096
qubits and 17,290 when it has 4095. -/
theorem reference_2048_peak_balanced : Reference2048PeakBalanced :=
  QubitCount.reference2048PeakBalanced

end Shor
