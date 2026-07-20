import FastMultiplication.ShorVerification.GateCount.Definitions

namespace Shor

/-! =========================================================
    Generic low-gate counting lemmas
========================================================= -/

namespace LowGate

/-- The identity gate contributes no cost. -/
@[simp]
theorem gateCount_id_eq (M : LowGateCostModel) :
    gateCount M .id = 0 := rfl

/-- Sequential composition contributes the sum of the component costs. -/
@[simp]
theorem gateCount_seq_eq (M : LowGateCostModel) (U V : LowGate) :
    gateCount M (U ;; V) = gateCount M U + gateCount M V := rfl

/-- Taking adjoints preserves the gate count. -/
@[simp]
theorem gateCount_adj_eq (M : LowGateCostModel) (U : LowGate) :
    gateCount M (†U) = gateCount M U := rfl

/-- A Hadamard is counted as one primitive low-level gate. -/
@[simp]
theorem gateCount_H_eq (M : LowGateCostModel) (q : ℕ) :
    gateCount M (.H q) = 1 := rfl

/-- An `X` gate is counted as one primitive low-level gate. -/
@[simp]
theorem gateCount_X_eq (M : LowGateCostModel) (q : ℕ) :
    gateCount M (.X q) = 1 := rfl

end LowGate

end Shor
