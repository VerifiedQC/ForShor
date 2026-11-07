import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Statement
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.QubitsTight
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.ExactBoard.ExactRecursion

/-!
# The single-product peak: the framework's qubit count of the constructed circuit

`ptp_qubits_tight_core` bounds the qubits the constructed circuit *names* (`LowGate.usedQubits`) by
`3 n + ptpWsTD P wd n`. `PolicyImplD.cleanAnc_le` bounds the clean scratch the policy's resource model holds
on top of them (`cleanAnc` of `P.resourceModel`, so under the policy's negation method) by `ptpCleanAncD P wd n`.
The framework's own measure is the sum, `LowGate.qubitCount M g = (usedQubits g).card + (resources M g).cleanAnc`,
so for the circuit `ptp_qubits_tight_core` constructs

    qubitCount P.resourceModel (G φ) ≤ 3 n + ptpWsTD P wd n + ptpCleanAncD P wd n.

The two lemmas are applied to the same `PolicyImplD` witness: `cleanAnc_le` holds for every witness, the used-qubit
bound is a property of the construction (`exists_policyImplD_tight`), and `ptp_qubits_tight_core` returns the
witness it bounds. The sum, not a `max`, is right: the scratch is by definition extra to the named qubits.

This is an upper bound for the constructed circuit, not an equality: neither summand is shown attained (the used
bound is by cardinality of a pool that the circuit may not all touch, and `ptpCleanAncD` is the max over the ladder
of per-node charges, an upper bound of the `max` the circuit's `seq` composition computes).
-/

namespace Shor
namespace PTP

open Shor Operations

/-- Every table the policy chooses has `1 ≤ k` (from `check`). -/
theorem ptp_hk_of_check (P : PTPPolicy) (hP : P.check = true) :
    ∀ m T, P.choose m = some T → 1 ≤ T.k := by
  intro m T hc
  obtain ⟨b, hb, rfl⟩ := PTPPolicy.choose_mem hc
  have hT := PTPPolicy.check_tables hP b hb
  have := ((PTPTable.contract_iff b.table).mp hT).1
  omega

/-- **The single-product peak** (any admissible width rule): the constructed circuit's framework qubit count in
the policy's own resource model is at most `3 n + ptpWsTD + ptpCleanAncD`. -/
theorem ptp_peak_core (P : PTPPolicy) (hP : P.check = true) (wd : WidthRule)
    (hwd : Admissible P wd) (n : ℕ) (X : Fin 3 → ExtReg) (base : ℕ) (hG : Good X n base) :
    ∃ (W : List ℕ) (G : Angle → LowGate), PolicyImplD P wd X n W G ∧
      ∀ φ, (LowGate.usedQubits (G φ)).card ≤ 3 * n + ptpWsTD P wd n ∧
        (LowGate.resources P.resourceModel (G φ)).cleanAnc ≤ ptpCleanAncD P wd n ∧
        LowGate.qubitCount P.resourceModel (G φ) ≤ ptpPeakQubits P wd n := by
  obtain ⟨W, G, hI, h⟩ := ptp_qubits_tight_core P hP wd hwd n X base hG
  refine ⟨W, G, hI, fun φ => ⟨(h φ).1, hI.cleanAnc_le φ, ?_⟩⟩
  have h1 := (h φ).1
  have h2 := hI.cleanAnc_le φ
  unfold LowGate.qubitCount ptpPeakQubits
  omega

/-- The single-product peak on the exact board. -/
theorem ptp_peak_exact_core (P : PTPPolicy) (hP : P.check = true) (n : ℕ)
    (X : Fin 3 → ExtReg) (base : ℕ) (hG : Good X n base) :
    ∃ (W : List ℕ) (G : Angle → LowGate), PolicyImplX P X n W G ∧
      ∀ φ, (LowGate.usedQubits (G φ)).card ≤ 3 * n + ptpWsTD P exactRule n ∧
        (LowGate.resources P.resourceModel (G φ)).cleanAnc ≤ ptpCleanAncD P exactRule n ∧
        LowGate.qubitCount P.resourceModel (G φ) ≤ ptpPeakQubits P exactRule n :=
  ptp_peak_core P hP exactRule (admissible_exact P) n X base hG

/-- The single-product peak on the scan board. -/
theorem ptp_peak_scan_core (P : PTPPolicy) (hP : P.check = true) (n : ℕ)
    (X : Fin 3 → ExtReg) (base : ℕ) (hG : Good X n base) :
    ∃ (W : List ℕ) (G : Angle → LowGate), PolicyImpl P X n W G ∧
      ∀ φ, (LowGate.usedQubits (G φ)).card ≤ 3 * n + ptpWsTD P ptpScanWidth n ∧
        (LowGate.resources P.resourceModel (G φ)).cleanAnc ≤ ptpCleanAnc P n ∧
        LowGate.qubitCount P.resourceModel (G φ) ≤ ptpPeakQubits P ptpScanWidth n := by
  obtain ⟨W, G, hI, h⟩ := ptp_peak_core P hP scanRule (admissible_scan P hP) n X base hG
  refine ⟨W, G, hI.toScan, fun φ => ⟨(h φ).1, ?_, (h φ).2.2⟩⟩
  have := (h φ).2.1
  rwa [ptpCleanAncD_scan] at this

/-- The peak against the `ptpQubits` formula: at most the scratch more. -/
theorem ptp_peak_le_ptpQubits_add_core (P : PTPPolicy) (hP : P.check = true) (n : ℕ) :
    ptpPeakQubits P ptpScanWidth n ≤ ptpQubits P n + ptpCleanAnc P n := by
  have h : ptpWsTD P ptpScanWidth n ≤
      3 * ptpReserveNeedD P ptpScanWidth n + max (ptpCleanAncD P ptpScanWidth n) 2 :=
    ptpWsTD_le_formula P scanRule (ptp_hk_of_check P hP) n
  have h1 : ptpReserveNeedD P ptpScanWidth n = ptpReserveNeed P n := ptpReserveNeedD_scan P n
  rw [h1] at h
  have h2 : ptpCleanAncD P ptpScanWidth n = ptpCleanAnc P n := ptpCleanAncD_scan P n
  rw [h2] at h
  unfold ptpPeakQubits ptpQubits
  omega

end PTP
end Shor
