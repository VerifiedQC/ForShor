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
  | .id => 0
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
    (shiftLCost : ExtReg → ℕ → ℕ := fun _ _ => 0)
    (shiftRCost : ExtReg → ℕ → ℕ := fun _ _ => 0) :
    LowGateCostModel where
  prim := 0

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
    (U : LowGate) : ℕ :=
  LowGate.gateCount (phaseProductCostModel) U


/--
 log_k (2k - 1).
-/
noncomputable def phaseProductExponent (k : ℕ) : ℝ :=
  Real.log (q k : ℝ) / Real.log (k : ℝ)

/-- The comparison function `n ↦ n^(log_k (2k - 1))`. -/
noncomputable def phaseProductGateRate (k n : ℕ) : ℝ :=
  Real.rpow (n : ℝ) (phaseProductExponent k)

def phaseProductInputSize (x z : Reg) : ℕ :=
  max (regSize x) (regSize z)

#check lowerGate

/--
For fixed `k` and `ops`, every sufficiently large PhaseProduct instance
has gate count bounded by C * n^(log_k (2k - 1)),
where `n` is the maximum width of its two input registers.
-/
def PhaseProductGateCountBound
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k) : Prop :=
  ∃ C : ℝ, 0 < C ∧
  ∃ n₀ : ℕ, 1 ≤ n₀ ∧
    ∀ (φ : ℝ) (x z : Reg),
      let n := max (regSize x) (regSize z)
      WellFormedReg x → WellFormedReg z → Disjoint x z →
      n₀ ≤ n →
      (LowGate.gateCount
          (phaseProductCostModel)
          (lowerGate (Basis := Basis) k hk ops (Gate.PhaseProd φ x z)) : ℝ)
        ≤  C * Real.rpow n (phaseProductExponent k)

-- Correctness of the table
def PhaseProductProgramOK
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k) : Prop :=
  let pts := genInterpolationPoints k
  let hpts : pts.length = q k := by
    simp [pts, genInterpolationPoints, q]
  GoodToomCookPoints k pts hpts ∧
  ProgConsumesPtsSafe
    (k := k) (by omega)
    State.start_state ops pts ∧
  run? ops State.start_state = some State.start_state ∧
  phaseProductCount ops = 2*k - 1

theorem exists_phaseProduct_gateCount_fixed_k
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (k : ℕ)
    (hk : 1 < k) :
    ∃ ops : Prog k,
      PhaseProductProgramOK k hk ops ∧
      PhaseProductGateCountBound (Basis := Basis) k hk ops := by
  -- The table that we get from computing one value at a time allows for the bound
  use (genOpsWithProduct (k:=k) (by linarith) (genInterpolationPoints k))
  constructor
  · simp[PhaseProductProgramOK]
    sorry

  sorry
