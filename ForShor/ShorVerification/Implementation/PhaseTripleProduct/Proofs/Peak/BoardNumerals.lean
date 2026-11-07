import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Peak.BoardNumerals.Row82eaf805f71c
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Peak.BoardNumerals.Row6f7d25984ff8
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Peak.BoardNumerals.Row85fbe1296fbd
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Peak.BoardNumerals.Row265a0f53acbc
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Peak.BoardNumerals.Row2ed7dc90d130
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Peak.BoardNumerals.Rowc733baf3cd08

/-!
# The six PhaseTripleProduct board policies: kernel-checked single-product peaks (`n = 2048`)

One file per board row under `BoardNumerals/`; each states, for `oneQubit` and `scratch` and for the scan and exact width rules,
`ptpWsTD`, `ptpCleanAncD` and `ptpPeakQubits = 3 n + ptpWsTD + ptpCleanAncD` (all by `decide +kernel`), and the headline instances
of `ptp_peak_qubits_exact` / `ptp_peak_qubits_scan`. The board's width rule is `exact`. No table of these policies negates, so the
two methods coincide. Peak (exact rule), the board's `qubits` (a live-qubit peak formula, one less everywhere: it lets the single
clean scratch share a qubit with the leaf's two ancillas, the Lean count adds it):

| row | policy | ladder | Lean peak (exact) | board Q | Lean peak (scan) |
|---|---|---|---|---|---|
| 82eaf805f71c | forshor_sub1 | 2048:4 -> 522:4 -> 142:leaf | 6405 | 6404 | 6660 |
| 6f7d25984ff8 | forshor_sub2 | 2048:8 -> 292:4 -> 80:leaf | 7095 | 7094 | 12351 |
| 85fbe1296fbd | forshor_sub27 | 2048:3 -> 687:3 -> 233:3 -> 82:leaf | 6261 | 6260 | 6540 |
| 265a0f53acbc | forshor_sub28 | 2048:4 -> 519:4 -> 139:leaf | 6342 | 6341 | 6852 |
| 2ed7dc90d130 | forshor_sub29 | 2048:5 -> 425:5 -> 98:leaf | 6573 | 6572 | 8238 |
| c733baf3cd08 | forshor_sub30 | 2048:6 -> 359:6 -> 80:leaf | 6828 | 6827 | 9750 |
-/

namespace Shor.PTP.Peak.Board

/-- The exact-rule peaks of the six board rows (`oneQubit`; the `scratch` values are the same, `methods_agree`), in board order. -/
theorem exact_peaks_oneQubit :
    ptpPeakQubits PolicySubmission.Policies.Board.Row82eaf805f71c.policy exactRule 2048 = 6405 ∧
    ptpPeakQubits PolicySubmission.Policies.Board.Row6f7d25984ff8.policy exactRule 2048 = 7095 ∧
    ptpPeakQubits PolicySubmission.Policies.Board.Row85fbe1296fbd.policy exactRule 2048 = 6261 ∧
    ptpPeakQubits PolicySubmission.Policies.Board.Row265a0f53acbc.policy exactRule 2048 = 6342 ∧
    ptpPeakQubits PolicySubmission.Policies.Board.Row2ed7dc90d130.policy exactRule 2048 = 6573 ∧
    ptpPeakQubits PolicySubmission.Policies.Board.Rowc733baf3cd08.policy exactRule 2048 = 6828 :=
  ⟨Row82eaf805f71c.oneQubit_exact.2.2.2, Row6f7d25984ff8.oneQubit_exact.2.2.2, Row85fbe1296fbd.oneQubit_exact.2.2.2, Row265a0f53acbc.oneQubit_exact.2.2.2, Row2ed7dc90d130.oneQubit_exact.2.2.2, Rowc733baf3cd08.oneQubit_exact.2.2.2⟩

/-- The same for `scratch`. -/
theorem exact_peaks_scratch :
    ptpPeakQubits (PolicySubmission.Policies.Board.Row82eaf805f71c.policy.withNegation .scratch) exactRule 2048 = 6405 ∧
    ptpPeakQubits (PolicySubmission.Policies.Board.Row6f7d25984ff8.policy.withNegation .scratch) exactRule 2048 = 7095 ∧
    ptpPeakQubits (PolicySubmission.Policies.Board.Row85fbe1296fbd.policy.withNegation .scratch) exactRule 2048 = 6261 ∧
    ptpPeakQubits (PolicySubmission.Policies.Board.Row265a0f53acbc.policy.withNegation .scratch) exactRule 2048 = 6342 ∧
    ptpPeakQubits (PolicySubmission.Policies.Board.Row2ed7dc90d130.policy.withNegation .scratch) exactRule 2048 = 6573 ∧
    ptpPeakQubits (PolicySubmission.Policies.Board.Rowc733baf3cd08.policy.withNegation .scratch) exactRule 2048 = 6828 :=
  ⟨Row82eaf805f71c.scratch_exact.2.2.2, Row6f7d25984ff8.scratch_exact.2.2.2, Row85fbe1296fbd.scratch_exact.2.2.2, Row265a0f53acbc.scratch_exact.2.2.2, Row2ed7dc90d130.scratch_exact.2.2.2, Rowc733baf3cd08.scratch_exact.2.2.2⟩

end Shor.PTP.Peak.Board

open Shor.Audit

#assert_axioms _root_.Shor.PTP.Peak.Board.exact_peaks_oneQubit
#assert_axioms _root_.Shor.PTP.Peak.Board.exact_peaks_scratch
