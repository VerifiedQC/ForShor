import ForShor.ShorVerification.Implementation.Readout.Proofs.PolicyNumeralsSC.Basic
import ForShor.ShorVerification.Submission.Policies.BoardPP.Rowc7f81cb40081
import ForShor.ShorVerification.Implementation.Readout.Proofs.PolicyNumeralsSC.Row6f7d25984ff8K6  -- import chain: Lake evaluates the rows one at a time

/-!
# Semiclassical readout: kernel-evaluated numerals of board row `c7f81cb40081`

The 2048-bit reference circuit with the semiclassical readout, lowered by
`PolicySubmission.Policies.BoardPP.Rowc7f81cb40081.policy` under the width rule `exact` (the board's rule), negation `oneQubit`,
balanced with `Balanced.defaultRule` (the board's configuration):

* `numerals` (one `decide +kernel`, re-checked by `#guard`): the modular multiplication's
  peak `N_SC = Policy.orderFindingPeakUSC … 2048 2347 4398 = 606` and the inverse QFT's peak
  at the board's exponent width, `qftPeakD … 4095 = 308` (so `qftPeakD 4095 ≤ N_SC`: the old
  peak was set by the multiplication).
* `qubits_sc`: `Q_SC = Policy.orderFindingQubitsUSC … = 1 + 8795 + 606 = 9402`.
* `qubits_old` / `peakU_4095`: the OLD balanced count at `xW = 4095` re-derived from the two
  numerals (`peakU_eq_of`, the algebra of `max`): `4095 + 8795 + 606 = 13496`, the same `N` as
  the old kernel numeral `PolicyNumeralsBoard.Rowc7f81cb40081Exact.balanced_exact_oneQubit` (`QubitCount/Proofs/PolicyNumeralsBoard/Rowc7f81cb40081Exact.lean`), which is NOT imported or re-evaluated here.
* `saving`: `Q_old - Q_SC = 4094 = xW - 1`.
* `peak_lowered`: the lowered balanced and every-site-split semiclassical circuits at the
  2048-bit reference layout peak at exactly `9402` qubits (`ReferenceSemiclassicalPeakIs`).

Provenance: the same numbers were first obtained by the compiled interpreter (`#eval`); here
they are kernel-checked.

Memory: the kernel evaluation of each row module of this folder peaks at 3 to 6.4 GB; the
modules form an import chain (`Row6f036362302e` → … → `RefPp2048`), so Lake evaluates them one
at a time.
-/

namespace Shor
namespace Readout
namespace PolicyNumeralsSC
namespace Rowc7f81cb40081

/-- The policy under the board's configuration: width rule `exact`, negation `oneQubit`. -/
abbrev under : ShorLoweringPolicy :=
  (PolicySubmission.Policies.BoardPP.Rowc7f81cb40081.policy.policy.withRule .exact).withNegation .oneQubit

theorem under_admissible : under.Admissible :=
  ShorLoweringPolicy.withNegation_admissible
    (ShorLoweringPolicy.withRule_admissible PolicySubmission.Policies.BoardPP.Rowc7f81cb40081.admissible .exact) .oneQubit

/-- The two kernel-evaluated numerals: `N_SC` and the inverse QFT's peak at `xW = 4095`. -/
theorem numerals :
    Policy.orderFindingPeakUSC under Balanced.defaultRule 2048 2347 4398 = 606 ∧
    qftPeakD under.negation under.widthRule (Policy.compile under) 4095 = 308 := by
  decide +kernel

-- the same two numerals, by the compiled interpreter (independent of the kernel run above)
#guard Policy.orderFindingPeakUSC under Balanced.defaultRule 2048 2347 4398 == 606
#guard qftPeakD under.negation under.widthRule (Policy.compile under) 4095 == 308

/-- `N_SC`: the semiclassical (modular-multiplication) peak. -/
theorem peak_sc : Policy.orderFindingPeakUSC under Balanced.defaultRule 2048 2347 4398 = 606 :=
  numerals.1

/-- The inverse QFT at `xW = 4095` does not set the old peak. -/
theorem qft_le : qftPeakD under.negation under.widthRule (Policy.compile under) 4095 ≤ 606 := by
  rw [numerals.2]; decide

/-- The old balanced peak at `xW = 4095`, re-derived (not re-evaluated). -/
theorem peakU_4095 : Policy.orderFindingPeakU under Balanced.defaultRule 4095 2048 2347 4398 = 606 :=
  peakU_eq_of under Balanced.defaultRule (by norm_num) 2048 2347 4398 numerals.1 numerals.2
    (by decide)

/-- **`Q_SC`**: the semiclassical qubit count. -/
theorem qubits_sc : Policy.orderFindingQubitsUSC under Balanced.defaultRule 2048 2347 4398 = 9402 :=
  (qubitsUSC_eq_of under numerals.1).trans (by norm_num)

/-- The old count at `xW = 4095` (the board's Q). -/
theorem qubits_old :
    Policy.orderFindingQubitsU under Balanced.defaultRule 4095 2048 2347 4398 = 13496 :=
  (qubitsU_eq_of under numerals.1 numerals.2 (by decide)).trans (by norm_num)

/-- **The saving**: `Q_old - Q_SC = 4094 = xW - 1`. -/
theorem saving :
    Policy.orderFindingQubitsU under Balanced.defaultRule 4095 2048 2347 4398
      - Policy.orderFindingQubitsUSC under Balanced.defaultRule 2048 2347 4398 = 4094 :=
  saving_eq_of under numerals.1 numerals.2 (by decide)

/-- **The lowered semiclassical circuit peaks at `Q_SC = 9402`** (balanced and every site
split, 2048-bit reference layout). -/
theorem peak_lowered : ReferenceSemiclassicalPeakIs under 606 :=
  referenceSemiclassicalPeakIs_of under under_admissible numerals.1

#assert_axioms _root_.Shor.Readout.PolicyNumeralsSC.Rowc7f81cb40081.numerals
#assert_axioms _root_.Shor.Readout.PolicyNumeralsSC.Rowc7f81cb40081.peak_sc
#assert_axioms _root_.Shor.Readout.PolicyNumeralsSC.Rowc7f81cb40081.qft_le
#assert_axioms _root_.Shor.Readout.PolicyNumeralsSC.Rowc7f81cb40081.peakU_4095
#assert_axioms _root_.Shor.Readout.PolicyNumeralsSC.Rowc7f81cb40081.qubits_sc
#assert_axioms _root_.Shor.Readout.PolicyNumeralsSC.Rowc7f81cb40081.qubits_old
#assert_axioms _root_.Shor.Readout.PolicyNumeralsSC.Rowc7f81cb40081.saving
#assert_axioms _root_.Shor.Readout.PolicyNumeralsSC.Rowc7f81cb40081.peak_lowered

end Rowc7f81cb40081
end PolicyNumeralsSC
end Readout
end Shor
