import FastMultiplication.ShorVerification.ShorCorrectness

namespace Shor

/-! =========================================================
    Shared gate-count definitions
========================================================= -/

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

end LowGate

def rippleAdderGateBound (w : ℕ) : ℕ :=
  9 * w + 2

/-- Negation is bounded by sign-width handling plus one ripple-adder. -/

def negateGateBound (r : ExtReg) : ℕ :=
  ExtReg.width r + rippleAdderGateBound (ExtReg.width r)

/-- Direct signed PhaseProduct base case, quadratic in the operand widths. -/

def directSignedPhaseProductGateCount (x z : ExtReg) : ℕ :=
  ExtReg.width x * ExtReg.width z

/-- Direct controlled signed PhaseProduct base case, also quadratic in width. -/

def directCSignedPhaseProductGateCount (x z : ExtReg) : ℕ :=
  5 * ExtReg.width x * ExtReg.width z

/-- Radix reversal is counted by the number of pairwise swaps up to constants. -/

def radixReverseGateCount (_r : Reg) (m : ℕ) : ℕ :=
  3 * (m / 2)

/-- The concrete cost model used in the final theorem: shifts and extension
bookkeeping are free, arithmetic is linear, and direct PhaseProduct is
quadratic. -/

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

/--
A conservative linear elementary-gate bound for a reversible arithmetic
primitive acting on `w` qubits.
-/

def linearPrimitiveGateBound (w : ℕ) : ℕ :=
  20 * w + 10

/--
Concrete costs for every opaque primitive used by the Shor circuit.

The payload formats come from:

* `CMP_GE_CONST [x.lo, x.hi, N, flag]`
* `CSUB_CONST   [flag, x.lo, x.hi, N]`
* `CMP_LT_NW    [x.lo, x.hi, w.lo, w.hi, N, flag]`

Malformed or unknown primitives are counted as one gate. That fallback should
not be reached by the current Shor circuit.
-/

def shorPrimCost (tag : String) (args : List ℕ) : ℕ :=
  if tag = "CMP_GE_CONST" then
    match args with
    | [lo, hi, _N, _flag] =>
        linearPrimitiveGateBound (hi - lo)
    | _ => 1
  else if tag = "CSUB_CONST" then
    match args with
    | [_flag, lo, hi, _N] =>
        linearPrimitiveGateBound (hi - lo)
    | _ => 1
  else if tag = "CMP_LT_NW" then
    match args with
    | [xlo, xhi, wlo, whi, _N, _flag] =>
        linearPrimitiveGateBound
          ((xhi - xlo) + (whi - wlo))
    | _ => 1
  else
    1

/-- Concrete gate-cost model used by all paper-level bounds. -/

def shorGateCostModel : LowGateCostModel :=
  phaseProductCostModel shorPrimCost

/-- Gate count of a lowered gate under the PhaseProduct-specialized cost
model. -/

def phaseProductGateCount
    (U : LowGate) : ℕ :=
  LowGate.gateCount shorGateCostModel U


/--
 log_k (2k - 1).
-/

noncomputable def phaseProductExponent (k : ℕ) : ℝ :=
  Real.log (q k : ℝ) / Real.log (k : ℝ)

/-- The comparison function `n ↦ n^(log_k (2k - 1))`. -/

noncomputable def phaseProductGateRate (k n : ℕ) : ℝ :=
  Real.rpow (n : ℝ) (phaseProductExponent k)

/-- The input size used in the final unsigned theorem: the larger register
width. -/

def phaseProductInputSize (x z : Reg) : ℕ :=
  max (regSize x) (regSize z)

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
      (LowGate.gateCount shorGateCostModel
          (lowerGate (Basis := Basis) k hk ops (Gate.PhaseProd φ x z)) : ℝ)
        ≤  C * Real.rpow n (phaseProductExponent k)


def PhaseProductProgramOK
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k) : Prop :=
  let pts := genInterpolationPoints k
  let hpts : pts.length = q k  := by
    simp [pts, genInterpolationPoints, q]
  GoodToomCookPoints k pts hpts ∧
  ProgConsumesPtsSafe
    (k := k) (by omega)
    State.start_state ops pts ∧
  run? ops State.start_state = some State.start_state ∧
  phaseProductCount ops = q k


/-- Well-formed generated programs are safe for point-consumption, giving the
table correctness predicate its safety component. -/

def QubitOutsideReg (q : ℕ) (r : Reg) : Prop :=
  q < r.lo ∨ r.hi ≤ q



/-! =========================================================
    PhaseProduct proof data
========================================================= -/

noncomputable def phaseProductSafeRate (k n : ℕ) : ℝ :=
  Real.rpow
    (((max 1 n : ℕ) : ℝ))
    (phaseProductExponent k)

/-- Gate count of the recursively lowered signed PhaseProduct. -/

noncomputable def signedPhaseProductGateCount
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (φ : ℝ)
    (x z : ExtReg) : ℕ :=
  LowGate.gateCount
    shorGateCostModel
    (lowerSignedPhaseProd
      (Basis := Basis) k hk φ x z ops)

/--
The balanced-input statement
-/

noncomputable def BalancedSignedPhaseProductBound
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (C : ℝ) : Prop :=
  ∀ (φ : ℝ) (x z : ExtReg),
    ExtReg.width x = ExtReg.width z →
    (signedPhaseProductGateCount
        (Basis := Basis) k hk ops φ x z : ℝ)
      ≤
    C * phaseProductSafeRate k (ExtReg.width x)


open Operations

def phaseArithmeticOpCost {k : ℕ}
    (W : ℕ) : valid_ops k → ℕ
  | .shiftL _ _ => 0
  | .shiftR _ _ => 0
  | .negate _ => 2 * (W + rippleAdderGateBound W)
  | .addScaled _ _ _ _ => 2 * rippleAdderGateBound W
  | .phaseProduct _ => 0

/-- Total nonrecursive work at one PhaseProduct recursion node. -/

def phaseProgramOverhead {k : ℕ}
    (W : ℕ)
    (ops : Prog k) : ℕ :=
  ops.foldr (fun op total => phaseArithmeticOpCost W op + total) 0

/--
A fixed source program performs only linearly many gates in the common working
width.  The constants depend on the fixed program, hence ultimately on `k`.
-/

def phaseOpWidthGrowth {k : ℕ} : valid_ops k → ℕ
  | .shiftL _ n              => n
  | .shiftR _ _              => 0
  | .negate _                => 1
  | .addScaled _ _ _ shift   => shift + 1
  | .phaseProduct _          => 0

/-- Sum of the additive width increases of a fixed program. -/

def phaseProgramWidthGrowth {k : ℕ} :
    List (valid_ops k) → ℕ
  | [] => 0
  | op :: ops =>
      phaseOpWidthGrowth op + phaseProgramWidthGrowth ops

/-- Every `x`- and `z`-slot in a width state is at most `B`. -/

def WidthStateBounded {k : ℕ}
    (st : WidthState k) (B : ℕ) : Prop :=
  ∀ i : Fin k, st.xw i ≤ B ∧ st.zw i ≤ B

/-- Every recorded needed width is at most `B`. -/

def NeededWidthsBounded {k : ℕ}
    (need : NeededWidths k) (B : ℕ) : Prop :=
  ∀ i : Fin k,
    need.xneed i ≤ B ∧ need.zneed i ≤ B

structure BalancedPhaseProductInstance where
  φ : ℝ
  x : ExtReg
  z : ExtReg
  hwidth : ExtReg.width x = ExtReg.width z

/-! =========================================================
    Shor-level and controlled PhaseProduct bounds
========================================================= -/

noncomputable def shorGateRate (ε : ℝ) (n : ℕ) : ℝ :=
  Real.rpow
    (((max 1 n : ℕ) : ℝ)) (2 + ε)



def CPhaseProductGateCountBound
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k) : Prop :=
  ∃ C : ℝ, 0 < C ∧
  ∃ n₀ : ℕ, 1 ≤ n₀ ∧
    ∀ (ctrl : ℕ) (φ : ℝ) (x z : Reg),
      let n := max (regSize x) (regSize z)
      WellFormedReg x →
      WellFormedReg z →
      Disjoint x z →
      (ctrl < x.lo ∨ x.hi ≤ ctrl) →
      (ctrl < z.lo ∨ z.hi ≤ ctrl) →
      n₀ ≤ n →
      (LowGate.gateCount shorGateCostModel
          (lowerGate
            (Basis := Basis)
            k hk ops
            (Gate.CPhaseProd ctrl φ x z)) : ℝ)
        ≤
      C * phaseProductSafeRate k n

end Shor

open Shor

/-! =========================================================
    Exact-QFT gate-count definitions
========================================================= -/

def QFTGateCountBound
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k) : Prop :=
  ∃ C : ℝ, 0 < C ∧
  ∃ n₀ : ℕ, 1 ≤ n₀ ∧
    ∀ r : Reg,
      WellFormedReg r →
      n₀ ≤ regSize r →
      (LowGate.gateCount shorGateCostModel
          (lowerGate
            (Basis := Basis)
            k hk ops
            (Gate.QFT r)) : ℝ)
        ≤
      C * phaseProductSafeRate k (regSize r)


/-- The paper chooses the split point `m = n / 2`. -/
def qftHalfWidth (r : Reg) : ℕ :=
  regSize r / 2

/-- The first half of the QFT register. -/

def qftLeftReg (r : Reg) : Reg :=
  { lo := r.lo
    size := qftHalfWidth r }

/-- The second half of the QFT register. -/

def qftRightReg (r : Reg) : Reg :=
  { lo := r.lo + qftHalfWidth r
    size := regSize r - qftHalfWidth r }

/-- Gate count of the recursively lowered exact QFT. -/

noncomputable def loweredQFTGateCount
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (r : Reg) : ℕ :=
  LowGate.gateCount
    shorGateCostModel
    (lowerGate
      (Basis := Basis)
      k hk ops
      (Gate.QFT r))

/--
Gate count of the PhaseProduct joining the two halves of one QFT recursion
node.
-/

noncomputable def qftSplitPhaseGateCount
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (r : Reg) : ℕ :=
  LowGate.gateCount
    shorGateCostModel
    (lowerGate
      (Basis := Basis)
      k hk ops
      (Gate.PhaseProd
        (qftPhi (regSize r))
        (qftLeftReg r)
        (qftRightReg r)))

/-- Gate count of the final radix reversal at one QFT recursion node. -/

def qftSplitRadixGateCount (r : Reg) : ℕ :=
  LowGate.gateCount
    shorGateCostModel
    (LowGate.RadixReverse r (qftHalfWidth r))
