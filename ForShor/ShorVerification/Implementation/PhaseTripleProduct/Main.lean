import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Statement
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Threshold
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Surface
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Controlled
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Unbalanced
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Asymptotic
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.QubitsTight

/-!
# PhaseTripleProduct Main Theorems

This module proves the public claims stated in `Statement.lean`. All supporting lemmas are
kept under `PhaseTripleProduct.Proofs`.

Read `Statement.lean` for what each claim means; building this file is the guarantee that every
one of them is proved. Each theorem below has the same name as the claim it proves, in lower case.
-/

namespace Shor
namespace PTP

/-- **State level, exact board.** For every checked policy there is a circuit following it at exact
widths that equals the PTP phase operator on every clean state, with the exact gate census in the
policy's own resource model (its negation method). (`PTPLowerExactCorrect`.) -/
theorem ptp_lowerExact_correct (qs : QSemantics) [RegEncoding qs.Basis] [LowerGateClass qs]
    (P : PTPPolicy) (n : ℕ) (X : Fin 3 → ExtReg) (base : ℕ) :
    PTPLowerExactCorrect qs P n X base := by
  intro hP hG
  obtain ⟨W, G, hI, hB, _, hR⟩ := ptp_gate_full_exact (qs := qs) P hP n X base hG
  exact ⟨W, G, hI, hB,
    fun φ U ψ hψ => evalL_policyImplD_state hP (admissible_exact P) hI φ U hψ, hR⟩

/-- **Controlled PTP by operand masking**, exact board, with the census. (`PTPCtlLowerExactCorrect`.) -/
theorem ptp_ctl_lowerExact_correct (qs : QSemantics) [RegEncoding qs.Basis] [LowerGateClass qs]
    (P : PTPPolicy) (n : ℕ) (X : Fin 3 → ExtReg) (Y : ExtReg) (c base : ℕ) :
    PTPCtlLowerExactCorrect qs P n X Y c base :=
  ptp_ctl_lowerExact_correct_core P n X Y c base

/-- **Unequal operand widths**, by in-place sign-extension padding. (`PTPPadLowerExactCorrect`.) -/
theorem ptp_pad_lowerExact_correct (qs : QSemantics) [RegEncoding qs.Basis] [LowerGateClass qs]
    (P : PTPPolicy) (n : ℕ) (X : Fin 3 → ExtReg) (d : Fin 3 → ℕ) (base : ℕ) :
    PTPPadLowerExactCorrect qs P n X d base :=
  ptp_pad_lowerExact_correct_core P n X d base

/-- **Gate count of the width-rule census** for a constant policy, under either negation method:
`O(n ^ log_k (3k - 2))`. (`PTPGateTotalBound`.) -/
theorem ptp_gateTotal_bound (t : ℕ) (T : PTPTable) (wd : WidthRule) :
    PTPGateTotalBound t T wd :=
  fun hT hwd m => ptp_gateTotal_bound_core m t T hT wd hwd

/-- **Gate count of the constructed circuit** for a constant policy, under either negation method:
`O(n ^ log_k (3k - 2))`. (`PTPCircuitGateCountBound`.) -/
theorem ptp_circuit_gateCount_bound (qs : QSemantics) [RegEncoding qs.Basis] [LowerGateClass qs]
    (t : ℕ) (T : PTPTable) :
    PTPCircuitGateCountBound qs t T :=
  fun hT hP m => ptp_circuit_gateCount_bound_core (qs := qs) m t T hT hP

/-- **Tight qubit count** for any admissible width rule. (`PTPQubitsTight`.) -/
theorem ptp_qubits_tight (P : PTPPolicy) (wd : WidthRule) (n : ℕ) (X : Fin 3 → ExtReg) (base : ℕ) :
    PTPQubitsTight P wd n X base :=
  fun hP hwd hG => ptp_qubits_tight_core P hP wd hwd n X base hG

/-- **Tight qubit count on the exact board.** (`PTPQubitsTightExact`.) -/
theorem ptp_qubits_tight_exact (P : PTPPolicy) (n : ℕ) (X : Fin 3 → ExtReg) (base : ℕ) :
    PTPQubitsTightExact P n X base :=
  fun hP hG => ptp_qubits_tight_exact_core P hP n X base hG

/-- **`ptpQubits` is an upper bound** at the scan rule. (`PTPQubitsLePtpQubits`.) -/
theorem ptp_qubits_le_ptpQubits (P : PTPPolicy) (n : ℕ) (X : Fin 3 → ExtReg) (base : ℕ) :
    PTPQubitsLePtpQubits P n X base :=
  fun hP hG => ptp_qubits_le_ptpQubits_core P hP n X base hG

/-- **The acceptance rule, without the ladder.** (`PTPChainContractsTightIffReach`.) -/
theorem ptp_chainContractsTight_iff_reach (P : PTPPolicy) (n : ℕ) :
    PTPChainContractsTightIffReach P n :=
  PTPPolicy.chainContractsTight_iff_reach P n

end PTP
end Shor
