import FastMultiplication.ShorVerification.Framework.AbstractMachine.LowGate

/-!
# Framework — LowGate cost model

The abstract cost model for lowered circuits, the `LowGate → ℕ` evaluator,
and the concrete Shor cost instance. Program-independent: it depends only on
the `LowGate` language, not on any lowering or construction.
-/

namespace Shor

/-! =========================================================
    Low-gate cost interface

This section defines the abstract cost model for lowered circuits and the
single evaluator that interprets a `LowGate` syntax tree as a natural-number
cost.  Later sections instantiate the model with the concrete Shor costs used
in the asymptotic bounds.
========================================================= -/

section LowGateCostModel

/-- A table of costs for each primitive low-level gate family.  Sequencing,
adjoint, and elementary one-qubit gates are handled uniformly by `gateCount`; the
fields here are exactly the operations whose costs depend on registers, payloads,
or the concrete arithmetic model. -/
structure LowGateCostModel where
  shiftL : ExtReg → ℕ → ℕ
  shiftR : ExtReg → ℕ → ℕ
  negate : ExtReg → ℕ
  addScaled : ExtReg → ExtReg → Bool → ℕ → ℕ
  zeroExtend : ExtReg → ℕ → ℕ
  signExtend : ExtReg → ℕ → ℕ
  zeroDealloc : ExtReg → ℕ → ℕ
  signDealloc : ExtReg → ℕ → ℕ
  radixReverse : Reg → ℕ → ℕ

namespace LowGate

/-- Evaluate a lowered gate tree against a cost model.  Structural gates add or
preserve cost, elementary `H`/`X` gates cost one, and model-dependent operations
are delegated to `LowGateCostModel`. -/
def gateCount (M : LowGateCostModel) : LowGate → ℕ
  | .id => 0
  | .seq U V => gateCount M U + gateCount M V
  | .adj U => gateCount M U
  | .H _ => 1
  | .X _ => 1
  | .ShiftL r n => M.shiftL r n
  | .ShiftR r n => M.shiftR r n
  | .Negate r => M.negate r
  | .AddScaled dst src negSrc shift => M.addScaled dst src negSrc shift
  | .Phase _ _ => 1
  | .CNOT _ _ => 1
  | .Toffoli _ _ _ => 1
  | .zeroExtend r n => M.zeroExtend r n
  | .signExtend r n => M.signExtend r n
  | .zeroDealloc r n => M.zeroDealloc r n
  | .signDealloc r n => M.signDealloc r n
  | .RadixReverse r m => M.radixReverse r m

end LowGate
end LowGateCostModel
