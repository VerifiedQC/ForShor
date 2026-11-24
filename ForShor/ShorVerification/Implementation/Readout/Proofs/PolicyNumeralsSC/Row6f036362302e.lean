import ForShor.ShorVerification.Implementation.Readout.Proofs.PolicyNumeralsSC.Basic
import ForShor.ShorVerification.Submission.Policies.BoardPP.Row6f036362302e

/-!
# Semiclassical readout: kernel-evaluated numerals of board row `6f036362302e`

The 2048-bit reference circuit with the semiclassical readout, lowered by
`PolicySubmission.Policies.BoardPP.Row6f036362302e.policy` under the width rule `exact` (the board's rule), negation `oneQubit`,
balanced with `Balanced.defaultRule` (the board's configuration):

* `numerals` (one `decide +kernel`, re-checked by `#guard`): the modular multiplication's
  peak `N_SC = Policy.orderFindingPeakUSC … 2048 2347 4398 = 346` and the inverse QFT's peak
  at the board's exponent width, `qftPeakD … 4095 = 42` (so `qftPeakD 4095 ≤ N_SC`: the old
  peak was set by the multiplication).
* `qubits_sc`: `Q_SC = Policy.orderFindingQubitsUSC … = 1 + 8795 + 346 = 9142`.
* `qubits_old` / `peakU_4095`: the OLD balanced count at `xW = 4095` re-derived from the two
  numerals (`peakU_eq_of`, the algebra of `max`): `4095 + 8795 + 346 = 13236`, the same `N` as
  the old kernel numeral `PolicyNumeralsBoard.Row6f036362302eExact.balanced_exact_oneQubit` (`QubitCount/Proofs/PolicyNumeralsBoard/Row6f036362302eExact.lean`), which is NOT imported or re-evaluated here.
* `saving`: `Q_old - Q_SC = 4094 = xW - 1`.
* `peak_lowered`: the lowered balanced and every-site-split semiclassical circuits at the
  2048-bit reference layout peak at exactly `9142` qubits (`ReferenceSemiclassicalPeakIs`).

Provenance: the same numbers were first obtained by the compiled interpreter (`#eval`); here
they are kernel-checked.

Memory: the kernel evaluation of each row module of this folder peaks at 3 to 6.4 GB; the
modules form an import chain (`Row6f036362302e` → … → `RefPp2048`), so Lake evaluates them one
at a time.
-/

namespace Shor
namespace Readout
namespace PolicyNumeralsSC
namespace Row6f036362302e

/-- The policy under the board's configuration: width rule `exact`, negation `oneQubit`. -/
abbrev under : ShorLoweringPolicy :=
  (PolicySubmission.Policies.BoardPP.Row6f036362302e.policy.policy.withRule .exact).withNegation .oneQubit

theorem under_admissible : under.Admissible :=
  ShorLoweringPolicy.withNegation_admissible
    (ShorLoweringPolicy.withRule_admissible PolicySubmission.Policies.BoardPP.Row6f036362302e.admissible .exact) .oneQubit

/-- The two kernel-evaluated numerals: `N_SC` and the inverse QFT's peak at `xW = 4095`. -/
theorem numerals :
    Policy.orderFindingPeakUSC under Balanced.defaultRule 2048 2347 4398 = 346 ∧
    qftPeakD under.negation under.widthRule (Policy.compile under) 4095 = 42 := by
  decide +kernel

-- the same two numerals, by the compiled interpreter (independent of the kernel run above)
#guard Policy.orderFindingPeakUSC under Balanced.defaultRule 2048 2347 4398 == 346
#guard qftPeakD under.negation under.widthRule (Policy.compile under) 4095 == 42

/-- `N_SC`: the semiclassical (modular-multiplication) peak. -/
theorem peak_sc : Policy.orderFindingPeakUSC under Balanced.defaultRule 2048 2347 4398 = 346 :=
  numerals.1

/-- The inverse QFT at `xW = 4095` does not set the old peak. -/
theorem qft_le : qftPeakD under.negation under.widthRule (Policy.compile under) 4095 ≤ 346 := by
  rw [numerals.2]; decide

/-- The old balanced peak at `xW = 4095`, re-derived (not re-evaluated). -/
theorem peakU_4095 : Policy.orderFindingPeakU under Balanced.defaultRule 4095 2048 2347 4398 = 346 :=
  peakU_eq_of under Balanced.defaultRule (by norm_num) 2048 2347 4398 numerals.1 numerals.2
    (by decide)

/-- **`Q_SC`**: the semiclassical qubit count. -/
theorem qubits_sc : Policy.orderFindingQubitsUSC under Balanced.defaultRule 2048 2347 4398 = 9142 :=
  (qubitsUSC_eq_of under numerals.1).trans (by norm_num)

/-- The old count at `xW = 4095` (the board's Q). -/
theorem qubits_old :
    Policy.orderFindingQubitsU under Balanced.defaultRule 4095 2048 2347 4398 = 13236 :=
  (qubitsU_eq_of under numerals.1 numerals.2 (by decide)).trans (by norm_num)

/-- **The saving**: `Q_old - Q_SC = 4094 = xW - 1`. -/
theorem saving :
    Policy.orderFindingQubitsU under Balanced.defaultRule 4095 2048 2347 4398
      - Policy.orderFindingQubitsUSC under Balanced.defaultRule 2048 2347 4398 = 4094 :=
  saving_eq_of under numerals.1 numerals.2 (by decide)

/-- **The lowered semiclassical circuit peaks at `Q_SC = 9142`** (balanced and every site
split, 2048-bit reference layout). -/
theorem peak_lowered : ReferenceSemiclassicalPeakIs under 346 :=
  referenceSemiclassicalPeakIs_of under under_admissible numerals.1

#assert_axioms _root_.Shor.Readout.PolicyNumeralsSC.Row6f036362302e.numerals
#assert_axioms _root_.Shor.Readout.PolicyNumeralsSC.Row6f036362302e.peak_sc
#assert_axioms _root_.Shor.Readout.PolicyNumeralsSC.Row6f036362302e.qft_le
#assert_axioms _root_.Shor.Readout.PolicyNumeralsSC.Row6f036362302e.peakU_4095
#assert_axioms _root_.Shor.Readout.PolicyNumeralsSC.Row6f036362302e.qubits_sc
#assert_axioms _root_.Shor.Readout.PolicyNumeralsSC.Row6f036362302e.qubits_old
#assert_axioms _root_.Shor.Readout.PolicyNumeralsSC.Row6f036362302e.saving
#assert_axioms _root_.Shor.Readout.PolicyNumeralsSC.Row6f036362302e.peak_lowered

end Row6f036362302e
end PolicyNumeralsSC
end Readout
end Shor
