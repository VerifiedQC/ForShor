import FastMultiplication.ShorVerification.ShorCorrectness
namespace Shor

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

def gateCount (M : LowGateCostModel) : LowGate → ℕ
  | .id =>
      0
  | .seq U V =>
      gateCount M U + gateCount M V
  | .adj U =>
      gateCount M U
  | .H _ =>
      1
  | .X _ =>
      1
  | .Prim tag qs =>
      M.prim tag qs
  | .ShiftL r n =>
      M.shiftL r n
  | .ShiftR r n =>
      M.shiftR r n
  | .Negate r =>
      M.negate r
  | .AddScaled dst src negSrc shift =>
      M.addScaled dst src negSrc shift
  | .Naive_SignedPhaseProd phi x z =>
      M.naiveSignedPhaseProd phi x z
  | .Naive_CSignedPhaseProd ctrl phi x z =>
      M.naiveCSignedPhaseProd ctrl phi x z
  | .zeroExtend r n =>
      M.zeroExtend r n
  | .signExtend r n =>
      M.signExtend r n
  | .zeroDealloc r n =>
      M.zeroDealloc r n
  | .signDealloc r n =>
      M.signDealloc r n
  | .RadixReverse r m =>
      M.radixReverse r m

@[simp]
theorem gateCount_id (M : LowGateCostModel) :
    gateCount M .id = 0 := rfl

@[simp]
theorem gateCount_seq (M : LowGateCostModel) (U V : LowGate) :
    gateCount M (U ;; V) = gateCount M U + gateCount M V := rfl

@[simp]
theorem gateCount_adj (M : LowGateCostModel) (U : LowGate) :
    gateCount M (†U) = gateCount M U := rfl

@[simp]
theorem gateCount_H (M : LowGateCostModel) (q : ℕ) :
    gateCount M (.H q) = 1 := rfl

@[simp]
theorem gateCount_X (M : LowGateCostModel) (q : ℕ) :
    gateCount M (.X q) = 1 := rfl

end LowGate

def rippleAdderGateBound (w : ℕ) : ℕ :=
  9 * w + 2

def negateGateBound (r : ExtReg) : ℕ :=
  ExtReg.width r + rippleAdderGateBound (ExtReg.width r)

def directSignedPhaseProductGateCount (x z : ExtReg) : ℕ :=
  ExtReg.width x * ExtReg.width z

def directCSignedPhaseProductGateCount (x z : ExtReg) : ℕ :=
  ExtReg.width x * ExtReg.width z

def radixReverseGateCount (_r : Reg) (m : ℕ) : ℕ :=
  3 * (m / 2)

def phaseProductCostModel
    (primCost : String → List ℕ → ℕ)
    (shiftLCost : ExtReg → ℕ → ℕ := fun _ _ => 0)
    (shiftRCost : ExtReg → ℕ → ℕ := fun _ _ => 0) :
    LowGateCostModel where
  prim := primCost

  shiftL := shiftLCost
  shiftR := shiftRCost

  negate := negateGateBound

  addScaled := fun dst _src _negSrc _shift =>
    rippleAdderGateBound (ExtReg.width dst)

  naiveSignedPhaseProd := fun _phi x z =>
    directSignedPhaseProductGateCount x z

  naiveCSignedPhaseProd := fun _ctrl _phi x z =>
    directCSignedPhaseProductGateCount x z

  zeroExtend := fun _r _n => 0
  signExtend := fun _r _n => 0
  zeroDealloc := fun _r _n => 0
  signDealloc := fun _r _n => 0

  radixReverse := radixReverseGateCount

def phaseProductGateCount
    (primCost : String → List ℕ → ℕ)
    (U : LowGate) : ℕ :=
  LowGate.gateCount (phaseProductCostModel primCost) U
