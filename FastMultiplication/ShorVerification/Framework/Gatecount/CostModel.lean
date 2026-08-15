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
  prim : String → List ℕ → ℕ
  shiftL : ExtReg → ℕ → ℕ
  shiftR : ExtReg → ℕ → ℕ
  negate : ExtReg → ℕ
  addScaled : ExtReg → ExtReg → Bool → ℕ → ℕ
  naiveSignedPhaseProd : ℝ → ExtReg → ExtReg → ℕ
  naiveCSignedPhaseProd : ℕ → ℝ → ExtReg → ExtReg → ℕ
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
  | .Prim tag qs => M.prim tag qs
  | .ShiftL r n => M.shiftL r n
  | .ShiftR r n => M.shiftR r n
  | .Negate r => M.negate r
  | .AddScaled dst src negSrc shift => M.addScaled dst src negSrc shift
  | .Naive_SignedPhaseProd phi x z => M.naiveSignedPhaseProd phi x z
  | .Naive_CSignedPhaseProd ctrl phi x z => M.naiveCSignedPhaseProd ctrl phi x z
  | .zeroExtend r n => M.zeroExtend r n
  | .signExtend r n => M.signExtend r n
  | .zeroDealloc r n => M.zeroDealloc r n
  | .signDealloc r n => M.signDealloc r n
  | .RadixReverse r m => M.radixReverse r m

end LowGate
end LowGateCostModel

/-! =========================================================
    Concrete Shor cost model

This section gives the numerical costs assigned to arithmetic primitives and
packages them into the concrete model used throughout the gate-count proofs.
The constants are intentionally conservative; the later asymptotic results only
need linear arithmetic costs and quadratic direct PhaseProduct base cases.
========================================================= -/

section ConcreteCostModel

/-- Conservative linear bound for one ripple-adder on `w` qubits. -/
def rippleAdderGateBound (w : ℕ) : ℕ := 9 * w + 2

/-- Negation is bounded by sign-width handling plus one ripple-adder. -/
def negateGateBound (r : ExtReg) : ℕ := ExtReg.width r + rippleAdderGateBound (ExtReg.width r)

/-- Direct signed PhaseProduct base-case cost, quadratic in the operand widths. -/
def directSignedPhaseProductGateCount (x z : ExtReg) : ℕ := ExtReg.width x * ExtReg.width z

/-- Direct controlled signed PhaseProduct base-case cost, with a constant-factor
controlled overhead over the signed direct implementation. -/
def directCSignedPhaseProductGateCount (x z : ExtReg) : ℕ := 5 * ExtReg.width x * ExtReg.width z

/-- Cost assigned to the final radix-reversal swaps for a register split. -/
def radixReverseGateCount (_r : Reg) (m : ℕ) : ℕ := 3 * (m / 2)

/-- Build a PhaseProduct-oriented cost model from a primitive-cost table. Shifts
and register-view bookkeeping default to zero under this model, arithmetic
operations are linear, and direct signed PhaseProduct gates are quadratic base
cases. A zero model cost records the chosen accounting convention; it is not a
claim that the corresponding physical operation is universally free. -/
def phaseProductCostModel
    (primCost : String → List ℕ → ℕ)
    (shiftLCost : ExtReg → ℕ → ℕ := fun _ _ => 0)
    (shiftRCost : ExtReg → ℕ → ℕ := fun _ _ => 0) : LowGateCostModel where
  prim := primCost
  shiftL := shiftLCost
  shiftR := shiftRCost
  negate := negateGateBound
  addScaled := fun dst _src _negSrc _shift => rippleAdderGateBound (ExtReg.width dst)
  naiveSignedPhaseProd := fun _phi x z => directSignedPhaseProductGateCount x z
  naiveCSignedPhaseProd := fun _ctrl _phi x z => directCSignedPhaseProductGateCount x z
  zeroExtend := fun _r _n => 0
  signExtend := fun _r _n => 0
  zeroDealloc := fun _r _n => 0
  signDealloc := fun _r _n => 0
  radixReverse := radixReverseGateCount

/-- Conservative linear elementary-gate bound for an opaque reversible arithmetic
primitive acting on `w` qubits. -/
def linearPrimitiveGateBound (w : ℕ) : ℕ := 20 * w + 10

/-- Concrete costs for the opaque arithmetic primitives used by the Shor circuit.
Recognized payloads use their register widths; malformed or unknown payloads are
assigned cost one as a defensive fallback. -/
def shorPrimCost (tag : String) (args : List ℕ) : ℕ :=
  if tag = "CMP_GE_CONST" ∨
      tag = "CSUB_CONST" ∨
      tag = "CMP_LT_NW" then
    linearPrimitiveGateBound (args.length - 2)
  else
    1

/-- Concrete gate-cost model used by all Shor gate-count developments. -/
def shorGateCostModel : LowGateCostModel := phaseProductCostModel shorPrimCost

end ConcreteCostModel


end Shor
