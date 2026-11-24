import ForShor.ShorVerification.Implementation.Readout.Proofs.PolicyNumeralsSC.Row6f036362302e
import ForShor.ShorVerification.Implementation.Readout.Proofs.PolicyNumeralsSC.Rowea01254c45f8
import ForShor.ShorVerification.Implementation.Readout.Proofs.PolicyNumeralsSC.Row7df40770c0b6
import ForShor.ShorVerification.Implementation.Readout.Proofs.PolicyNumeralsSC.Rowa3972b965049
import ForShor.ShorVerification.Implementation.Readout.Proofs.PolicyNumeralsSC.Row6f7d25984ff8K6
import ForShor.ShorVerification.Implementation.Readout.Proofs.PolicyNumeralsSC.Rowc7f81cb40081
import ForShor.ShorVerification.Implementation.Readout.Proofs.PolicyNumeralsSC.Row6f7d25984ff8K8
import ForShor.ShorVerification.Implementation.Readout.Proofs.PolicyNumeralsSC.Rowf4aff955f16b
import ForShor.ShorVerification.Implementation.Readout.Proofs.PolicyNumeralsSC.Rowf0f15fefe959
import ForShor.ShorVerification.Implementation.Readout.Proofs.PolicyNumeralsSC.RefPp2048

/-!
# Semiclassical readout: the board table, kernel-checked

Root of `PolicyNumeralsSC/*.lean`: for the nine distinct PhaseProduct policies of the results
board and `policies/ref_pp_2048.json`, at n = 2048, width rule `exact`, negation `oneQubit`,
balanced with `Balanced.defaultRule`, exponent width `xW = 4095`:

| policy | N_SC | qftPeakD 4095 | old Q | Q_SC | saving |
|---|---|---|---|---|---|
| 6f036362302e | 346 | 42 | 13,236 | 9,142 | 4,094 |
| ea01254c45f8 | 394 | 104 | 13,284 | 9,190 | 4,094 |
| 7df40770c0b6 | 420 | 124 | 13,310 | 9,216 | 4,094 |
| a3972b965049 | 514 | 232 | 13,404 | 9,310 | 4,094 |
| 6f7d25984ff8K6 | 516 | 242 | 13,406 | 9,312 | 4,094 |
| c7f81cb40081 | 606 | 308 | 13,496 | 9,402 | 4,094 |
| 6f7d25984ff8K8 | 786 | 442 | 13,676 | 9,582 | 4,094 |
| f4aff955f16b | 770 | 430 | 13,660 | 9,566 | 4,094 |
| f0f15fefe959 | 770 | 430 | 13,660 | 9,566 | 4,094 |
| ref_pp_2048 | 606 | 314 | 13,496 | 9,402 | 4,094 |

`N_SC` and `qftPeakD 4095` are kernel-evaluated (`decide +kernel`, one per row module); every
other column is derived from them by proved algebra (`PolicyNumeralsSC/Basic.lean`). The old
Q column is re-derived (`qubits_old`) and agrees with the old kernel numerals
(`QubitCount/Proofs/PolicyNumeralsBoard/*Exact.lean`, `PolicyNumerals/RefPp2048Exact.lean`),
which are not imported. Provenance: these numbers were first `#eval`-ed by the compiled
interpreter; here they are kernel-checked.

Memory and CI: every row module's kernel evaluation peaks at 3.1 to 6.4 GB (measured locally,
2026-11-19; the old exact-rule numerals need 5 to 15.4 GB because they also evaluate the plain
circuit and both negation methods), so no row is local-only: the ten form the
`PolicyNumeralsSC` library (root `Readout/PolicyNumeralsSCTests.lean`), outside the `ForShor` umbrella and built
in a CI step of its own. They form an import chain so Lake evaluates one at a time.

`board_semiclassical_saving`: on every row, `Q_SC` is the stated numeral, the saving
`Q_old - Q_SC` is `4094`, and the lowered semiclassical circuit at the 2048-bit reference layout
peaks at `Q_SC` (`ReferenceSemiclassicalPeakIs`).
-/

namespace Shor
namespace Readout
namespace PolicyNumeralsSC

/-- One row: `Q_SC = q`, `Q_old - Q_SC = 4094`, and the lowered circuit peaks at `1 + 8795 + N_SC`. -/
def RowHolds (P : ShorLoweringPolicy) (Nsc q : ℕ) : Prop :=
  Policy.orderFindingQubitsUSC P Balanced.defaultRule 2048 2347 4398 = q ∧
  Policy.orderFindingQubitsU P Balanced.defaultRule 4095 2048 2347 4398
    - Policy.orderFindingQubitsUSC P Balanced.defaultRule 2048 2347 4398 = 4094 ∧
  ReferenceSemiclassicalPeakIs P Nsc

/-- **The board table of the semiclassical readout, every row.** -/
theorem board_semiclassical_saving :
    RowHolds Row6f036362302e.under 346 9142 ∧
    RowHolds Rowea01254c45f8.under 394 9190 ∧
    RowHolds Row7df40770c0b6.under 420 9216 ∧
    RowHolds Rowa3972b965049.under 514 9310 ∧
    RowHolds Row6f7d25984ff8K6.under 516 9312 ∧
    RowHolds Rowc7f81cb40081.under 606 9402 ∧
    RowHolds Row6f7d25984ff8K8.under 786 9582 ∧
    RowHolds Rowf4aff955f16b.under 770 9566 ∧
    RowHolds Rowf0f15fefe959.under 770 9566 ∧
    RowHolds RefPp2048.under 606 9402 :=
  ⟨⟨Row6f036362302e.qubits_sc, Row6f036362302e.saving, Row6f036362302e.peak_lowered⟩,
   ⟨Rowea01254c45f8.qubits_sc, Rowea01254c45f8.saving, Rowea01254c45f8.peak_lowered⟩,
   ⟨Row7df40770c0b6.qubits_sc, Row7df40770c0b6.saving, Row7df40770c0b6.peak_lowered⟩,
   ⟨Rowa3972b965049.qubits_sc, Rowa3972b965049.saving, Rowa3972b965049.peak_lowered⟩,
   ⟨Row6f7d25984ff8K6.qubits_sc, Row6f7d25984ff8K6.saving, Row6f7d25984ff8K6.peak_lowered⟩,
   ⟨Rowc7f81cb40081.qubits_sc, Rowc7f81cb40081.saving, Rowc7f81cb40081.peak_lowered⟩,
   ⟨Row6f7d25984ff8K8.qubits_sc, Row6f7d25984ff8K8.saving, Row6f7d25984ff8K8.peak_lowered⟩,
   ⟨Rowf4aff955f16b.qubits_sc, Rowf4aff955f16b.saving, Rowf4aff955f16b.peak_lowered⟩,
   ⟨Rowf0f15fefe959.qubits_sc, Rowf0f15fefe959.saving, Rowf0f15fefe959.peak_lowered⟩,
   ⟨RefPp2048.qubits_sc, RefPp2048.saving, RefPp2048.peak_lowered⟩⟩

#assert_axioms _root_.Shor.Readout.PolicyNumeralsSC.board_semiclassical_saving

end PolicyNumeralsSC
end Readout
end Shor
