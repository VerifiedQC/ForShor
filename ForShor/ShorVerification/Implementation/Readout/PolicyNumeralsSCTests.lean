import ForShor.ShorVerification.Implementation.Readout.Proofs.PolicyNumeralsSC.Board

/-!
# Semiclassical readout: tests of the board numerals

* `#print axioms` of the conjunction `board_semiclassical_saving` and of each row's kernel
  numerals: only `propext`, `Classical.choice`, `Quot.sound` (no `sorryAx`, no
  `Lean.ofReduceBool`: the numerals are `decide +kernel`, not `native_decide`).
* `new_below_old` (negative sanity): on every row the new count is strictly below the old one.
* `saving_le_xW_sub_one` (negative sanity): on every row the saving is not larger than
  `xW - 1 = 4094` (the inverse QFT never set the old peak, so nothing beyond the exponent
  register is saved), and `saving_ne_xW`: it is not `xW = 4095` (one control qubit remains).
* `peak_sc_ge_old_qft`: `N_SC` is at least the old inverse-QFT peak at `xW = 4095` (the
  hypothesis that makes the saving exact).
-/

namespace Shor
namespace Readout
namespace PolicyNumeralsSC
namespace Tests

/-- **Negative sanity: the new count is below the old one on every row.** -/
theorem new_below_old :
    Policy.orderFindingQubitsUSC Row6f036362302e.under Balanced.defaultRule 2048 2347 4398 < Policy.orderFindingQubitsU Row6f036362302e.under Balanced.defaultRule 4095 2048 2347 4398 ∧
    Policy.orderFindingQubitsUSC Rowea01254c45f8.under Balanced.defaultRule 2048 2347 4398 < Policy.orderFindingQubitsU Rowea01254c45f8.under Balanced.defaultRule 4095 2048 2347 4398 ∧
    Policy.orderFindingQubitsUSC Row7df40770c0b6.under Balanced.defaultRule 2048 2347 4398 < Policy.orderFindingQubitsU Row7df40770c0b6.under Balanced.defaultRule 4095 2048 2347 4398 ∧
    Policy.orderFindingQubitsUSC Rowa3972b965049.under Balanced.defaultRule 2048 2347 4398 < Policy.orderFindingQubitsU Rowa3972b965049.under Balanced.defaultRule 4095 2048 2347 4398 ∧
    Policy.orderFindingQubitsUSC Row6f7d25984ff8K6.under Balanced.defaultRule 2048 2347 4398 < Policy.orderFindingQubitsU Row6f7d25984ff8K6.under Balanced.defaultRule 4095 2048 2347 4398 ∧
    Policy.orderFindingQubitsUSC Rowc7f81cb40081.under Balanced.defaultRule 2048 2347 4398 < Policy.orderFindingQubitsU Rowc7f81cb40081.under Balanced.defaultRule 4095 2048 2347 4398 ∧
    Policy.orderFindingQubitsUSC Row6f7d25984ff8K8.under Balanced.defaultRule 2048 2347 4398 < Policy.orderFindingQubitsU Row6f7d25984ff8K8.under Balanced.defaultRule 4095 2048 2347 4398 ∧
    Policy.orderFindingQubitsUSC Rowf4aff955f16b.under Balanced.defaultRule 2048 2347 4398 < Policy.orderFindingQubitsU Rowf4aff955f16b.under Balanced.defaultRule 4095 2048 2347 4398 ∧
    Policy.orderFindingQubitsUSC Rowf0f15fefe959.under Balanced.defaultRule 2048 2347 4398 < Policy.orderFindingQubitsU Rowf0f15fefe959.under Balanced.defaultRule 4095 2048 2347 4398 ∧
    Policy.orderFindingQubitsUSC RefPp2048.under Balanced.defaultRule 2048 2347 4398 < Policy.orderFindingQubitsU RefPp2048.under Balanced.defaultRule 4095 2048 2347 4398 :=
  ⟨by have := Row6f036362302e.qubits_sc; have := Row6f036362302e.qubits_old; omega,
   by have := Rowea01254c45f8.qubits_sc; have := Rowea01254c45f8.qubits_old; omega,
   by have := Row7df40770c0b6.qubits_sc; have := Row7df40770c0b6.qubits_old; omega,
   by have := Rowa3972b965049.qubits_sc; have := Rowa3972b965049.qubits_old; omega,
   by have := Row6f7d25984ff8K6.qubits_sc; have := Row6f7d25984ff8K6.qubits_old; omega,
   by have := Rowc7f81cb40081.qubits_sc; have := Rowc7f81cb40081.qubits_old; omega,
   by have := Row6f7d25984ff8K8.qubits_sc; have := Row6f7d25984ff8K8.qubits_old; omega,
   by have := Rowf4aff955f16b.qubits_sc; have := Rowf4aff955f16b.qubits_old; omega,
   by have := Rowf0f15fefe959.qubits_sc; have := Rowf0f15fefe959.qubits_old; omega,
   by have := RefPp2048.qubits_sc; have := RefPp2048.qubits_old; omega⟩

/-- **Negative sanity: the saving is not larger than `xW - 1` on every row.** -/
theorem saving_le_xW_sub_one :
    Policy.orderFindingQubitsU Row6f036362302e.under Balanced.defaultRule 4095 2048 2347 4398 - Policy.orderFindingQubitsUSC Row6f036362302e.under Balanced.defaultRule 2048 2347 4398 ≤ 4095 - 1 ∧
    Policy.orderFindingQubitsU Rowea01254c45f8.under Balanced.defaultRule 4095 2048 2347 4398 - Policy.orderFindingQubitsUSC Rowea01254c45f8.under Balanced.defaultRule 2048 2347 4398 ≤ 4095 - 1 ∧
    Policy.orderFindingQubitsU Row7df40770c0b6.under Balanced.defaultRule 4095 2048 2347 4398 - Policy.orderFindingQubitsUSC Row7df40770c0b6.under Balanced.defaultRule 2048 2347 4398 ≤ 4095 - 1 ∧
    Policy.orderFindingQubitsU Rowa3972b965049.under Balanced.defaultRule 4095 2048 2347 4398 - Policy.orderFindingQubitsUSC Rowa3972b965049.under Balanced.defaultRule 2048 2347 4398 ≤ 4095 - 1 ∧
    Policy.orderFindingQubitsU Row6f7d25984ff8K6.under Balanced.defaultRule 4095 2048 2347 4398 - Policy.orderFindingQubitsUSC Row6f7d25984ff8K6.under Balanced.defaultRule 2048 2347 4398 ≤ 4095 - 1 ∧
    Policy.orderFindingQubitsU Rowc7f81cb40081.under Balanced.defaultRule 4095 2048 2347 4398 - Policy.orderFindingQubitsUSC Rowc7f81cb40081.under Balanced.defaultRule 2048 2347 4398 ≤ 4095 - 1 ∧
    Policy.orderFindingQubitsU Row6f7d25984ff8K8.under Balanced.defaultRule 4095 2048 2347 4398 - Policy.orderFindingQubitsUSC Row6f7d25984ff8K8.under Balanced.defaultRule 2048 2347 4398 ≤ 4095 - 1 ∧
    Policy.orderFindingQubitsU Rowf4aff955f16b.under Balanced.defaultRule 4095 2048 2347 4398 - Policy.orderFindingQubitsUSC Rowf4aff955f16b.under Balanced.defaultRule 2048 2347 4398 ≤ 4095 - 1 ∧
    Policy.orderFindingQubitsU Rowf0f15fefe959.under Balanced.defaultRule 4095 2048 2347 4398 - Policy.orderFindingQubitsUSC Rowf0f15fefe959.under Balanced.defaultRule 2048 2347 4398 ≤ 4095 - 1 ∧
    Policy.orderFindingQubitsU RefPp2048.under Balanced.defaultRule 4095 2048 2347 4398 - Policy.orderFindingQubitsUSC RefPp2048.under Balanced.defaultRule 2048 2347 4398 ≤ 4095 - 1 :=
  ⟨by have := Row6f036362302e.saving; omega,
   by have := Rowea01254c45f8.saving; omega,
   by have := Row7df40770c0b6.saving; omega,
   by have := Rowa3972b965049.saving; omega,
   by have := Row6f7d25984ff8K6.saving; omega,
   by have := Rowc7f81cb40081.saving; omega,
   by have := Row6f7d25984ff8K8.saving; omega,
   by have := Rowf4aff955f16b.saving; omega,
   by have := Rowf0f15fefe959.saving; omega,
   by have := RefPp2048.saving; omega⟩

/-- **Negative sanity: the saving is not `xW`** (the control qubit `c` stays). -/
theorem saving_ne_xW :
    Policy.orderFindingQubitsU Row6f036362302e.under Balanced.defaultRule 4095 2048 2347 4398 - Policy.orderFindingQubitsUSC Row6f036362302e.under Balanced.defaultRule 2048 2347 4398 ≠ 4095 ∧
    Policy.orderFindingQubitsU Rowea01254c45f8.under Balanced.defaultRule 4095 2048 2347 4398 - Policy.orderFindingQubitsUSC Rowea01254c45f8.under Balanced.defaultRule 2048 2347 4398 ≠ 4095 ∧
    Policy.orderFindingQubitsU Row7df40770c0b6.under Balanced.defaultRule 4095 2048 2347 4398 - Policy.orderFindingQubitsUSC Row7df40770c0b6.under Balanced.defaultRule 2048 2347 4398 ≠ 4095 ∧
    Policy.orderFindingQubitsU Rowa3972b965049.under Balanced.defaultRule 4095 2048 2347 4398 - Policy.orderFindingQubitsUSC Rowa3972b965049.under Balanced.defaultRule 2048 2347 4398 ≠ 4095 ∧
    Policy.orderFindingQubitsU Row6f7d25984ff8K6.under Balanced.defaultRule 4095 2048 2347 4398 - Policy.orderFindingQubitsUSC Row6f7d25984ff8K6.under Balanced.defaultRule 2048 2347 4398 ≠ 4095 ∧
    Policy.orderFindingQubitsU Rowc7f81cb40081.under Balanced.defaultRule 4095 2048 2347 4398 - Policy.orderFindingQubitsUSC Rowc7f81cb40081.under Balanced.defaultRule 2048 2347 4398 ≠ 4095 ∧
    Policy.orderFindingQubitsU Row6f7d25984ff8K8.under Balanced.defaultRule 4095 2048 2347 4398 - Policy.orderFindingQubitsUSC Row6f7d25984ff8K8.under Balanced.defaultRule 2048 2347 4398 ≠ 4095 ∧
    Policy.orderFindingQubitsU Rowf4aff955f16b.under Balanced.defaultRule 4095 2048 2347 4398 - Policy.orderFindingQubitsUSC Rowf4aff955f16b.under Balanced.defaultRule 2048 2347 4398 ≠ 4095 ∧
    Policy.orderFindingQubitsU Rowf0f15fefe959.under Balanced.defaultRule 4095 2048 2347 4398 - Policy.orderFindingQubitsUSC Rowf0f15fefe959.under Balanced.defaultRule 2048 2347 4398 ≠ 4095 ∧
    Policy.orderFindingQubitsU RefPp2048.under Balanced.defaultRule 4095 2048 2347 4398 - Policy.orderFindingQubitsUSC RefPp2048.under Balanced.defaultRule 2048 2347 4398 ≠ 4095 :=
  ⟨by have := Row6f036362302e.saving; omega,
   by have := Rowea01254c45f8.saving; omega,
   by have := Row7df40770c0b6.saving; omega,
   by have := Rowa3972b965049.saving; omega,
   by have := Row6f7d25984ff8K6.saving; omega,
   by have := Rowc7f81cb40081.saving; omega,
   by have := Row6f7d25984ff8K8.saving; omega,
   by have := Rowf4aff955f16b.saving; omega,
   by have := Rowf0f15fefe959.saving; omega,
   by have := RefPp2048.saving; omega⟩

/-- `qftPeakD 4095 ≤ N_SC` on every row (the old peak was set by the multiplication). -/
theorem peak_sc_ge_old_qft :
    qftPeakD Row6f036362302e.under.negation Row6f036362302e.under.widthRule (Policy.compile Row6f036362302e.under) 4095 ≤ Policy.orderFindingPeakUSC Row6f036362302e.under Balanced.defaultRule 2048 2347 4398 ∧
    qftPeakD Rowea01254c45f8.under.negation Rowea01254c45f8.under.widthRule (Policy.compile Rowea01254c45f8.under) 4095 ≤ Policy.orderFindingPeakUSC Rowea01254c45f8.under Balanced.defaultRule 2048 2347 4398 ∧
    qftPeakD Row7df40770c0b6.under.negation Row7df40770c0b6.under.widthRule (Policy.compile Row7df40770c0b6.under) 4095 ≤ Policy.orderFindingPeakUSC Row7df40770c0b6.under Balanced.defaultRule 2048 2347 4398 ∧
    qftPeakD Rowa3972b965049.under.negation Rowa3972b965049.under.widthRule (Policy.compile Rowa3972b965049.under) 4095 ≤ Policy.orderFindingPeakUSC Rowa3972b965049.under Balanced.defaultRule 2048 2347 4398 ∧
    qftPeakD Row6f7d25984ff8K6.under.negation Row6f7d25984ff8K6.under.widthRule (Policy.compile Row6f7d25984ff8K6.under) 4095 ≤ Policy.orderFindingPeakUSC Row6f7d25984ff8K6.under Balanced.defaultRule 2048 2347 4398 ∧
    qftPeakD Rowc7f81cb40081.under.negation Rowc7f81cb40081.under.widthRule (Policy.compile Rowc7f81cb40081.under) 4095 ≤ Policy.orderFindingPeakUSC Rowc7f81cb40081.under Balanced.defaultRule 2048 2347 4398 ∧
    qftPeakD Row6f7d25984ff8K8.under.negation Row6f7d25984ff8K8.under.widthRule (Policy.compile Row6f7d25984ff8K8.under) 4095 ≤ Policy.orderFindingPeakUSC Row6f7d25984ff8K8.under Balanced.defaultRule 2048 2347 4398 ∧
    qftPeakD Rowf4aff955f16b.under.negation Rowf4aff955f16b.under.widthRule (Policy.compile Rowf4aff955f16b.under) 4095 ≤ Policy.orderFindingPeakUSC Rowf4aff955f16b.under Balanced.defaultRule 2048 2347 4398 ∧
    qftPeakD Rowf0f15fefe959.under.negation Rowf0f15fefe959.under.widthRule (Policy.compile Rowf0f15fefe959.under) 4095 ≤ Policy.orderFindingPeakUSC Rowf0f15fefe959.under Balanced.defaultRule 2048 2347 4398 ∧
    qftPeakD RefPp2048.under.negation RefPp2048.under.widthRule (Policy.compile RefPp2048.under) 4095 ≤ Policy.orderFindingPeakUSC RefPp2048.under Balanced.defaultRule 2048 2347 4398 :=
  ⟨by have := Row6f036362302e.numerals.1; have := Row6f036362302e.qft_le; omega,
   by have := Rowea01254c45f8.numerals.1; have := Rowea01254c45f8.qft_le; omega,
   by have := Row7df40770c0b6.numerals.1; have := Row7df40770c0b6.qft_le; omega,
   by have := Rowa3972b965049.numerals.1; have := Rowa3972b965049.qft_le; omega,
   by have := Row6f7d25984ff8K6.numerals.1; have := Row6f7d25984ff8K6.qft_le; omega,
   by have := Rowc7f81cb40081.numerals.1; have := Rowc7f81cb40081.qft_le; omega,
   by have := Row6f7d25984ff8K8.numerals.1; have := Row6f7d25984ff8K8.qft_le; omega,
   by have := Rowf4aff955f16b.numerals.1; have := Rowf4aff955f16b.qft_le; omega,
   by have := Rowf0f15fefe959.numerals.1; have := Rowf0f15fefe959.qft_le; omega,
   by have := RefPp2048.numerals.1; have := RefPp2048.qft_le; omega⟩

#print axioms board_semiclassical_saving
#print axioms Row6f036362302e.numerals
#print axioms Rowea01254c45f8.numerals
#print axioms Row7df40770c0b6.numerals
#print axioms Rowa3972b965049.numerals
#print axioms Row6f7d25984ff8K6.numerals
#print axioms Rowc7f81cb40081.numerals
#print axioms Row6f7d25984ff8K8.numerals
#print axioms Rowf4aff955f16b.numerals
#print axioms Rowf0f15fefe959.numerals
#print axioms RefPp2048.numerals
#print axioms new_below_old
#print axioms saving_le_xW_sub_one
#print axioms saving_ne_xW
#print axioms peak_sc_ge_old_qft

#assert_axioms _root_.Shor.Readout.PolicyNumeralsSC.Tests.new_below_old
#assert_axioms _root_.Shor.Readout.PolicyNumeralsSC.Tests.saving_le_xW_sub_one
#assert_axioms _root_.Shor.Readout.PolicyNumeralsSC.Tests.saving_ne_xW
#assert_axioms _root_.Shor.Readout.PolicyNumeralsSC.Tests.peak_sc_ge_old_qft

end Tests
end PolicyNumeralsSC
end Readout
end Shor
