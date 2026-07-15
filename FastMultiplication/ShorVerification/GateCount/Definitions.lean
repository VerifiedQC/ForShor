import FastMultiplication.ShorVerification.ShorCorrectness
import FastMultiplication.ShorVerification.GateCount.MasterTheoremProof
namespace Shor

/-! =========================================================
    Low-gate cost model and basic counting facts
========================================================= -/

/-- Cost hooks for each low-level gate family used after lowering.  The final
bound specializes this interface to the PhaseProduct cost model below. -/
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

/-- Interprets a lowered gate as a natural-number gate count by recursively
adding sequential costs and delegating primitive families to the cost model. -/
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

/-- The identity gate contributes no cost. -/
@[simp]
theorem gateCount_id (M : LowGateCostModel) :
    gateCount M .id = 0 := rfl

/-- Sequential composition contributes the sum of the two component costs. -/
@[simp]
theorem gateCount_seq (M : LowGateCostModel) (U V : LowGate) :
    gateCount M (U ;; V) = gateCount M U + gateCount M V := rfl

/-- Taking adjoints preserves the gate count, used when inverse table code is
compiled in the final PhaseProduct program. -/
@[simp]
theorem gateCount_adj (M : LowGateCostModel) (U : LowGate) :
    gateCount M (†U) = gateCount M U := rfl

/-- A Hadamard is counted as one primitive low-level gate. -/
@[simp]
theorem gateCount_H (M : LowGateCostModel) (q : ℕ) :
    gateCount M (.H q) = 1 := rfl

/-- An `X` gate is counted as one primitive low-level gate. -/
@[simp]
theorem gateCount_X (M : LowGateCostModel) (q : ℕ) :
    gateCount M (.X q) = 1 := rfl

end LowGate

/-! ---------------------------------------------------------
    Concrete costs for the PhaseProduct lowering
--------------------------------------------------------- -/

/-- Linear ripple-adder bound used as the scalar arithmetic cost throughout
the recurrence. -/
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
  ExtReg.width x * ExtReg.width z

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

/-! ---------------------------------------------------------
    Correctness and size facts for the generated interpolation table
--------------------------------------------------------- -/

/-- Semantic and counting requirements for the generated Toom-Cook table used
by the final existence theorem. -/
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
lemma SafeProg_of_WellFormed {k : ℕ} {ops : Prog k}
    (hWF : Prog.WellFormed ops) :
    SafeProg ops := by
  intro pre rest d s negSrc sh hops
  have hmem : Operations.valid_ops.addScaled d s negSrc sh ∈ ops := by
    rw [hops]
    simp
  simpa [Prog.OpOK] using hWF (Operations.valid_ops.addScaled d s negSrc sh) hmem

/-- A singleton PhaseProduct operation is well formed, serving as the leaf in
each generated interpolation-point block. -/
lemma phaseProduct_singleton_WellFormed {k : ℕ} (i : Fin k) :
    Prog.WellFormed ([Operations.valid_ops.phaseProduct i] : Prog k) := by
  intro op hop
  simp at hop
  subst op
  simp [Prog.OpOK]

/-- The program emitted for one interpolation point is well formed: compute the
local value, emit one PhaseProduct, then uncompute. -/
lemma opsForPointWithProduct_WellFormed {k : ℕ} (hk : 0 < k) (pt : Operations.Point) :
    Prog.WellFormed (opsForPointWithProduct (k := k) hk pt) := by
  cases pt with
  | int z =>
      have hBuild : Prog.WellFormed (computeLocal2 (k := k) hk z) :=
        computeLocal2_Valid (k := k) (z := z) hk
      have hPhase : Prog.WellFormed ([Operations.valid_ops.phaseProduct (finZero hk)] : Prog k) :=
        phaseProduct_singleton_WellFormed (k := k) (finZero hk)
      have hInv : Prog.WellFormed (apply_Op_inverse (computeLocal2 (k := k) hk z)) :=
        Prog.apply_Op_inverse_preserves_WF hBuild
      simpa [opsForPointWithProduct] using
        WellFormed_append (k := k) hBuild
          (WellFormed_append (k := k) hPhase hInv)
  | frac c =>
      by_cases hc : c = 0
      · have hPhase : Prog.WellFormed ([Operations.valid_ops.phaseProduct (finLast hk)] : Prog k) :=
          phaseProduct_singleton_WellFormed (k := k) (finLast hk)
        simpa [opsForPointWithProduct, hc] using hPhase
      · have hBuild : Prog.WellFormed (computeFracLocal2 (k := k) hk c) :=
          computeFracLocal2_Valid (k := k) (c := c) hk
        have hPhase : Prog.WellFormed ([Operations.valid_ops.phaseProduct (finLast hk)] : Prog k) :=
          phaseProduct_singleton_WellFormed (k := k) (finLast hk)
        have hInv : Prog.WellFormed (apply_Op_inverse (computeFracLocal2 (k := k) hk c)) :=
          Prog.apply_Op_inverse_preserves_WF hBuild
        simpa [opsForPointWithProduct, hc] using
          WellFormed_append (k := k) hBuild
            (WellFormed_append (k := k) hPhase hInv)

/-- A list of generated point blocks is well formed by appending the
well-formed block for each interpolation point. -/
lemma genOpsWithProduct_WellFormed {k : ℕ} (hk : 0 < k) :
    ∀ pts : List Operations.Point, Prog.WellFormed (genOpsWithProduct (k := k) hk pts)
  | [] => by
      intro op hop
      simp [genOpsWithProduct] at hop
  | pt :: pts => by
      simpa [genOpsWithProduct] using
        WellFormed_append (k := k)
          (opsForPointWithProduct_WellFormed (k := k) hk pt)
          (genOpsWithProduct_WellFormed (k := k) hk pts)

/-- The generated table safely consumes exactly the interpolation points while
using only well-formed arithmetic operations. -/
lemma genOpsWithProduct_ProgConsumesPtsSafe {k : ℕ} (hk : 0 < k)
    (pts : List Operations.Point) :
    ProgConsumesPtsSafe (k := k) hk State.start_state
      (genOpsWithProduct (k := k) hk pts) pts where
  consumes := genOpsWithProduct_ProgConsumesPts (k := k) hk pts
  safe_add := SafeProg_of_WellFormed
    (genOpsWithProduct_WellFormed (k := k) hk pts)

/-- Integer local-computation blocks contain no PhaseProduct leaves, so they
contribute zero to the PhaseProduct leaf count. -/
lemma computeLocal2_NoPhase {k : ℕ} (hk : 0 < k) (z : ℤ) :
    NoPhase (computeLocal2 (k := k) hk z) := by
  exact NoPhase_of_onlyAddScaled (onlyAddScaled_computeLocal2 (k := k) hk z)

/-- The inverse of an integer local-computation block also contains no
PhaseProduct leaves, keeping uncomputation out of the branching factor. -/
lemma computeLocal2_inverse_NoPhase {k : ℕ} (hk : 0 < k) (z : ℤ) :
    NoPhase (apply_Op_inverse (computeLocal2 (k := k) hk z)) := by
  rw [computeLocal_eq (k := k) (z := z) hk]
  exact (computeLocal_NoPhase_2 (k := k) hk z).2

/-- Each interpolation-point block contributes exactly one recursive
PhaseProduct leaf. -/
lemma phaseProductCount_opsForPointWithProduct {k : ℕ} (hk : 0 < k)
    (pt : Operations.Point) :
    phaseProductCount (opsForPointWithProduct (k := k) hk pt) = 1 := by
  cases pt with
  | int z =>
      have hBuild :
          phaseProductCount (computeLocal2 (k := k) hk z) = 0 :=
        phaseProductCount_eq_zero_of_NoPhase
          (computeLocal2_NoPhase (k := k) hk z)
      have hInv :
          phaseProductCount (apply_Op_inverse (computeLocal2 (k := k) hk z)) = 0 :=
        phaseProductCount_eq_zero_of_NoPhase
          (computeLocal2_inverse_NoPhase (k := k) hk z)
      simp [opsForPointWithProduct, phaseProductCount_append,
        phaseProductCount, hBuild, hInv]
  | frac c =>
      by_cases hc : c = 0
      · simp [opsForPointWithProduct, hc, phaseProductCount]
      · have hBuild :
            phaseProductCount (computeFracLocal2 (k := k) hk c) = 0 :=
          phaseProductCount_eq_zero_of_NoPhase
            (computeFracLocal2_NoPhase (k := k) hk c)
        have hInv :
            phaseProductCount (apply_Op_inverse (computeFracLocal2 (k := k) hk c)) = 0 :=
          phaseProductCount_eq_zero_of_NoPhase
            ((computeFracLocal2_NoPhase_2 (k := k) hk c).2)
        simp [opsForPointWithProduct, hc, phaseProductCount_append,
          phaseProductCount, hBuild, hInv]

/-- The generated program has one PhaseProduct leaf per interpolation point,
giving the final branching factor `q k `. -/
lemma phaseProductCount_genOpsWithProduct {k : ℕ} (hk : 0 < k) :
    ∀ pts : List Operations.Point,
      phaseProductCount (genOpsWithProduct (k := k) hk pts) = pts.length
  | [] => by
      simp [genOpsWithProduct, phaseProductCount]
  | pt :: pts => by
      simp [genOpsWithProduct, phaseProductCount_append,
        phaseProductCount_opsForPointWithProduct (k := k) hk pt,
        phaseProductCount_genOpsWithProduct (k := k) hk pts, Nat.add_comm]

/--
The qubit `q` lies outside the half-open interval represented by `r`.
-/
def QubitOutsideReg (q : ℕ) (r : Reg) : Prop :=
  q < r.lo ∨ r.hi ≤ q


/-! =========================================================
    Paper-style PhaseProduct gate-count proof
========================================================= -/

/--
Use `max 1 n` internally so that the recursive bound also covers the finitely
many width-zero/base cases.  Above width zero this is the paper's rate.
-/
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

/-! ---------------------------------------------------------
    Step 2: scalar cost of the nonrecursive arithmetic
--------------------------------------------------------- -/

/--
Cost contributed at one recursion node by one source-language operation,
excluding its recursive PhaseProduct child.

Each arithmetic operation is performed once on the `x` slots and once on the
`z` slots.  Shifts cost zero in `phaseProductCostModel`.
-/
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
lemma phaseProgramOverhead_linear
    {k : ℕ}
    (ops : Prog k) :
    ∃ A B : ℕ, ∀ W : ℕ,
      phaseProgramOverhead W ops ≤ A * W + B := by
  induction ops with
  | nil =>
      refine ⟨0, 0, ?_⟩
      intro W
      simp [phaseProgramOverhead]
  | cons op ops ih =>
      rcases ih with ⟨A, B, htail⟩
      refine ⟨A + 20, B + 4, ?_⟩
      intro W
      have hop :
          phaseArithmeticOpCost (k := k) W op ≤ 20 * W + 4 := by
        cases op <;> simp [phaseArithmeticOpCost, rippleAdderGateBound] <;> omega
      calc
        phaseProgramOverhead W (op :: ops)
            = phaseArithmeticOpCost (k := k) W op + phaseProgramOverhead W ops := rfl
        _ ≤ (20 * W + 4) + (A * W + B) :=
            Nat.add_le_add hop (htail W)
        _ ≤ (A + 20) * W + (B + 4) := by
            nlinarith [Nat.zero_le A, Nat.zero_le B, Nat.zero_le W]

/-! =========================================================
    Additive width growth of a fixed source program
========================================================= -/

/--
An upper bound on how much one source operation can increase a
uniform bound on all slot widths.
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

/-- Updating widths by one operation preserves boundedness, up to that
operation's declared additive growth. -/
lemma updateWidthState_bounded
    {k : ℕ}
    {st : WidthState k}
    {B : ℕ}
    (hst : WidthStateBounded st B)
    (op : valid_ops k) :
    WidthStateBounded
      (updateWidthState st op)
      (B + phaseOpWidthGrowth op) := by
  classical
  intro i

  cases op with
  | shiftL j n =>
      by_cases hij : i = j
      · subst i
        rcases hst j with ⟨hx, hz⟩
        have hpair :
            st.xw j + n ≤ B + n ∧
            st.zw j + n ≤ B + n := by
          omega
        simpa [updateWidthState, phaseOpWidthGrowth] using hpair
      ·
        rcases hst i with ⟨hx, hz⟩
        have hpair :
            st.xw i ≤ B + n ∧
            st.zw i ≤ B + n := by
          omega
        simpa [updateWidthState, phaseOpWidthGrowth,
          hij, Ne.symm hij] using hpair

  | shiftR j n =>
      by_cases hij : i = j
      · subst i
        rcases hst j with ⟨hx, hz⟩
        have hpair :
            st.xw j - n ≤ B ∧
            st.zw j - n ≤ B := by
          omega
        simpa [updateWidthState, phaseOpWidthGrowth] using hpair
      ·
        rcases hst i with ⟨hx, hz⟩
        have hpair :
            st.xw i ≤ B ∧
            st.zw i ≤ B :=
          ⟨hx, hz⟩
        simpa [updateWidthState, phaseOpWidthGrowth,
          hij, Ne.symm hij] using hpair

  | negate j =>
      by_cases hij : i = j
      · subst i
        rcases hst j with ⟨hx, hz⟩
        have hpair :
            st.xw j + 1 ≤ B + 1 ∧
            st.zw j + 1 ≤ B + 1 := by
          omega
        simpa [updateWidthState, phaseOpWidthGrowth] using hpair
      ·
        rcases hst i with ⟨hx, hz⟩
        have hpair :
            st.xw i ≤ B + 1 ∧
            st.zw i ≤ B + 1 := by
          omega
        simpa [updateWidthState, phaseOpWidthGrowth,
          hij, Ne.symm hij] using hpair

  | addScaled dst src negSrc shift =>
      by_cases hidst : i = dst
      · subst i
        rcases hst dst with ⟨hxdst, hzdst⟩
        rcases hst src with ⟨hxsrc, hzsrc⟩

        have hxmax :
            max (st.xw dst) (st.xw src + shift)
              ≤ B + shift := by
          apply max_le
          · omega
          · omega

        have hzmax :
            max (st.zw dst) (st.zw src + shift)
              ≤ B + shift := by
          apply max_le
          · omega
          · omega

        have hpair :
            1 + max (st.xw dst) (st.xw src + shift)
                ≤ B + (shift + 1) ∧
            1 + max (st.zw dst) (st.zw src + shift)
                ≤ B + (shift + 1) := by
          constructor <;> omega

        simpa [updateWidthState, phaseOpWidthGrowth] using hpair
      ·
        rcases hst i with ⟨hx, hz⟩
        have hpair :
            st.xw i ≤ B + (shift + 1) ∧
            st.zw i ≤ B + (shift + 1) := by
          omega
        simpa [updateWidthState, phaseOpWidthGrowth,
          hidst, Ne.symm hidst] using hpair

  | phaseProduct j =>
      simpa [updateWidthState, phaseOpWidthGrowth] using hst i

/-- The current width state is also a valid bound on the recorded needed
widths, used to initialize the scan invariant. -/
lemma widthsOfState_bounded
    {k : ℕ}
    {st : WidthState k}
    {B : ℕ}
    (hst : WidthStateBounded st B) :
    NeededWidthsBounded (widthsOfState st) B := by
  intro i
  simpa [widthsOfState] using hst i

/-- Needed-width bounds can be weakened, letting later scan steps absorb more
additive growth. -/
lemma neededWidthsBounded_mono
    {k : ℕ}
    {need : NeededWidths k}
    {A B : ℕ}
    (hneed : NeededWidthsBounded need A)
    (hAB : A ≤ B) :
    NeededWidthsBounded need B := by
  intro i
  rcases hneed i with ⟨hx, hz⟩
  exact ⟨hx.trans hAB, hz.trans hAB⟩

/-- Merging two needed-width summaries preserves a common upper bound. -/
lemma mergeNeededWidths_bounded
    {k : ℕ}
    {a b : NeededWidths k}
    {B : ℕ}
    (ha : NeededWidthsBounded a B)
    (hb : NeededWidthsBounded b B) :
    NeededWidthsBounded (mergeNeededWidths a b) B := by
  intro i
  rcases ha i with ⟨hax, haz⟩
  rcases hb i with ⟨hbx, hbz⟩
  change
    max (a.xneed i) (b.xneed i) ≤ B ∧
    max (a.zneed i) (b.zneed i) ≤ B
  exact ⟨max_le hax hbx, max_le haz hbz⟩

/-- Scanning a full program accumulates only the sum of per-operation width
growth, a key input to the recursive-size bound. -/
lemma scanNeededWidthsAux_bounded
    {k : ℕ}
    (cur : WidthState k)
    (mx : NeededWidths k)
    (ops : List (valid_ops k))
    (B : ℕ)
    (hcur : WidthStateBounded cur B)
    (hmx : NeededWidthsBounded mx B) :
    NeededWidthsBounded
      (scanNeededWidthsAux cur mx ops)
      (B + phaseProgramWidthGrowth ops) := by
  induction ops generalizing cur mx B with
  | nil =>
      simpa [scanNeededWidthsAux, phaseProgramWidthGrowth] using hmx

  | cons op rest ih =>
      have hcur' :
          WidthStateBounded
            (updateWidthState cur op)
            (B + phaseOpWidthGrowth op) :=
        updateWidthState_bounded hcur op

      have hmxOld :
          NeededWidthsBounded
            mx
            (B + phaseOpWidthGrowth op) := by
        apply neededWidthsBounded_mono hmx
        omega

      have hcurNeed :
          NeededWidthsBounded
            (widthsOfState (updateWidthState cur op))
            (B + phaseOpWidthGrowth op) :=
        widthsOfState_bounded hcur'

      have hmx' :
          NeededWidthsBounded
            (mergeNeededWidths
              mx
              (widthsOfState (updateWidthState cur op)))
            (B + phaseOpWidthGrowth op) :=
        mergeNeededWidths_bounded hmxOld hcurNeed

      have htail :=
        ih
          (cur := updateWidthState cur op)
          (mx :=
            mergeNeededWidths
              mx
              (widthsOfState (updateWidthState cur op)))
          (B := B + phaseOpWidthGrowth op)
          hcur'
          hmx'

      simpa [scanNeededWidthsAux, phaseProgramWidthGrowth,
        Nat.add_assoc] using htail

/-- A bound on every recorded needed width bounds the common target width
chosen for recursive children. -/
lemma commonNeededWidth_le_of_bounded
    {k : ℕ}
    {need : NeededWidths k}
    {B : ℕ}
    (hneed : NeededWidthsBounded need B) :
    commonNeededWidth need ≤ B + 1 := by
  unfold commonNeededWidth

  have hsup :
      Finset.univ.sup
          (fun i : Fin k =>
            max (need.xneed i) (need.zneed i))
        ≤ B := by
    apply Finset.sup_le
    intro i hi
    exact max_le (hneed i).1 (hneed i).2

  omega

/-- The top-heavy split leaves every limb no larger than the top chunk, which
is the initial width before fixed program growth is added. -/
lemma phaseSplitLogicalWidth_le_topHeavy
    (k W w n : ℕ)
    (hk : 0 < k)
    (hw : w ≤ n)
    (hkW : k * W ≤ n)
    (i : Fin k) :
    phaseSplitLogicalWidth w W k i
      ≤ n - (k - 1) * W := by
  by_cases htop : isTopChunk i
  ·
    have hiSucc : i.val + 1 = k := by
      simpa [isTopChunk] using htop

    have hi : i.val = k - 1 := by
      omega

    simp only [phaseSplitLogicalWidth, if_pos htop, hi]
    omega

  ·
    have hkDecomp : k - 1 + 1 = k := by
      omega

    have hsum :
        W + (k - 1) * W ≤ n := by
      calc
        W + (k - 1) * W
            = (k - 1) * W + W := Nat.add_comm _ _
        _ = ((k - 1) + 1) * W := by
              simp [Nat.add_mul]
        _ = k * W := by
              rw [hkDecomp]
        _ ≤ n := hkW

    have hW :
        W ≤ n - (k - 1) * W := by
      omega

    simpa [phaseSplitLogicalWidth, htop] using hW

/-- The initial layout created from the two input registers is bounded by the
top-heavy chunk width. -/
lemma initWidthState_bounded_topHeavy
    (k : ℕ)
    (hk : 0 < k)
    (x z : ExtReg) :
    WidthStateBounded
      (initWidthState x z k)
      (phaseInputSize x z
        - (k - 1) * phaseLimbWidth x z k) := by
  intro i

  let W : ℕ := phaseLimbWidth x z k
  let n : ℕ := phaseInputSize x z

  have hxle : ExtReg.width x ≤ n := by
    simp [n, phaseInputSize]

  have hzle : ExtReg.width z ≤ n := by
    simp [n, phaseInputSize]

  have hWdiv :
      W ≤ ExtReg.width x / k := by
    simp [W, phaseLimbWidth, phaseLimbWidthOfWidth]

  have hWmul :
      W * k ≤ ExtReg.width x :=
    (Nat.le_div_iff_mul_le hk).mp hWdiv

  have hkW : k * W ≤ n := by
    have hWmax : W * k ≤ n :=
      hWmul.trans hxle
    simpa [Nat.mul_comm] using hWmax

  change
    phaseSplitLogicalWidth (ExtReg.width x) W k i
        ≤ n - (k - 1) * W ∧
    phaseSplitLogicalWidth (ExtReg.width z) W k i
        ≤ n - (k - 1) * W

  exact
    ⟨phaseSplitLogicalWidth_le_topHeavy
        k W (ExtReg.width x) n hk hxle hkW i,
      phaseSplitLogicalWidth_le_topHeavy
        k W (ExtReg.width z) n hk hzle hkW i⟩

/-- The recursive child width is at most the top-heavy chunk width plus the
fixed program's additive growth. -/
lemma nextSignedWidth_le_topHeavy_add_growth
    {k : ℕ}
    (hk : 0 < k)
    (ops : Prog k)
    (x z : ExtReg) :
    nextSignedWidth x z ops
      ≤
    phaseInputSize x z
      - (k - 1) * phaseLimbWidth x z k
      + (phaseProgramWidthGrowth ops + 1) := by
  have hinit :
      WidthStateBounded
        (initWidthState x z k)
        (phaseInputSize x z
          - (k - 1) * phaseLimbWidth x z k) :=
    initWidthState_bounded_topHeavy k hk x z

  have hscan :
      NeededWidthsBounded
        (scanNeededWidths x z ops)
        ((phaseInputSize x z
            - (k - 1) * phaseLimbWidth x z k)
          + phaseProgramWidthGrowth ops) := by
    simpa [scanNeededWidths] using
      scanNeededWidthsAux_bounded
        (cur := initWidthState x z k)
        (mx := widthsOfState (initWidthState x z k))
        (ops := ops)
        (B :=
          phaseInputSize x z
            - (k - 1) * phaseLimbWidth x z k)
        hinit
        (widthsOfState_bounded hinit)

  have hcommon :=
    commonNeededWidth_le_of_bounded hscan

  simpa [nextSignedWidth, Nat.add_assoc] using hcommon


/-! ---------------------------------------------------------
    Step 3: width bounds for the generated evaluation program
--------------------------------------------------------- -/

/--
General top-heavy width estimate.

The initial largest chunk has width

  phaseInputSize x z - (k - 1) * phaseLimbWidth x z k,

and a fixed finite program can increase this by only a fixed additive amount.
-/
lemma genOpsWithProduct_nextSignedWidth_topHeavy
    (k : ℕ)
    (hk : 0 < k)
    (pts : List Point) :
    ∃ c : ℕ, ∀ x z : ExtReg,
      nextSignedWidth
          x z
          (genOpsWithProduct (k := k) hk pts)
        ≤
      phaseInputSize x z
        - (k - 1) * phaseLimbWidth x z k
        + c := by
  refine
    ⟨phaseProgramWidthGrowth
        (genOpsWithProduct (k := k) hk pts) + 1,
      ?_⟩

  intro x z

  exact
    nextSignedWidth_le_topHeavy_add_growth
      hk
      (genOpsWithProduct (k := k) hk pts)
      x z
/--
For balanced inputs, every recursively compiled evaluation value has width

  ceil(n / k) + O_k(1).

This is the formal version of the paper's phrase “size roughly n/k”.
-/
lemma genOpsWithProduct_balanced_nextSignedWidth
    (k : ℕ)
    (hk : 1 < k)
    (hk0 : 0 < k)
    (pts : List Point) :
    ∃ c : ℕ, ∀ x z : ExtReg,
      ExtReg.width x = ExtReg.width z →
      nextSignedWidth
          x z
          (genOpsWithProduct (k := k) hk0 pts)
        ≤
      (ExtReg.width x + k - 1) / k + c := by
  rcases
      genOpsWithProduct_nextSignedWidth_topHeavy
        k hk0 pts with
    ⟨c, hc⟩
  refine ⟨c + (k - 1), ?_⟩
  intro x z hbalanced
  let n := ExtReg.width x
  have hsize : phaseInputSize x z = n := by
    simp [phaseInputSize, n, hbalanced]
  have hlimb : phaseLimbWidth x z k = n / k := by
    simp [phaseLimbWidth, phaseLimbWidthOfWidth, n, hbalanced]
  have hceil :
      n - (k - 1) * (n / k) ≤ (n + k - 1) / k + (k - 1) := by
    let q := n / k
    have hdiv : k * q ≤ n := by
      simpa [q] using Nat.mul_div_le n k
    have hmul : k * q = (k - 1) * q + q := by
      have hk_eq : k = (k - 1) + 1 := by omega
      calc
        k * q = ((k - 1) + 1) * q := by
          nth_rewrite 1 [hk_eq]
          rfl
        _ = (k - 1) * q + q := by rw [Nat.add_mul, one_mul]
    have hrem : n % k = n - k * q := by
      simpa [q] using (Nat.mod_eq_sub_mul_div : n % k = n - k * (n / k))
    have hsplit :
        n - (k - 1) * q =
          n % k + q := by
      omega
    have hmod : n % k ≤ k - 1 := by
      have hlt : n % k < k := Nat.mod_lt n hk0
      omega
    have hq_le_ceil : q ≤ (n + k - 1) / k := by
      apply Nat.div_le_div_right
      omega
    have hq :
        n - (k - 1) * q ≤ (n + k - 1) / k + (k - 1) := by
      rw [hsplit]
      omega
    simpa [q] using hq
  calc
    nextSignedWidth x z (genOpsWithProduct (k := k) hk0 pts)
        ≤ phaseInputSize x z - (k - 1) * phaseLimbWidth x z k + c :=
          hc x z
    _ = n - (k - 1) * (n / k) + c := by
          rw [hsize, hlimb]
    _ ≤ (n + k - 1) / k + (c + (k - 1)) := by
          omega

/--
For arbitrary unequal inputs, the first recursive working width is at most the
larger input width plus a constant depending only on the fixed table.
-/
lemma genOpsWithProduct_nextSignedWidth_le_input_add_const
    (k : ℕ)
    (hk : 0 < k)
    (pts : List Point) :
    ∃ c : ℕ, ∀ x z : ExtReg,
      nextSignedWidth
          x z
          (genOpsWithProduct (k := k) hk pts)
        ≤
      phaseInputSize x z + c := by
  rcases
      genOpsWithProduct_nextSignedWidth_topHeavy
        k hk pts with
    ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro x z
  exact
    le_trans
      (hc x z)
      (Nat.add_le_add_right
        (Nat.sub_le
          (phaseInputSize x z)
          ((k - 1) * phaseLimbWidth x z k))
        c)

/--
If the top-level unequal PhaseProduct does not recurse, then its smaller
operand has bounded width.

Indeed, failure to recurse means that the top-heavy split failed to remove a
positive fraction of the smaller operand.  The preceding top-heavy estimate
then forces that smaller width to be bounded by a constant.
-/
lemma genOpsWithProduct_no_recurse_implies_small_operand
    (k : ℕ)
    (hk : 1 < k)
    (hk0 : 0 < k)
    (pts : List Point) :
    ∃ d : ℕ, ∀ x z : ExtReg,
      (¬ nextSignedWidth x z (genOpsWithProduct (k := k) hk0 pts)
        < phaseInputSize x z)
        →
      (min (ExtReg.width x) (ExtReg.width z) ≤ d) := by
  rcases
      genOpsWithProduct_nextSignedWidth_topHeavy
        k hk0 pts with
    ⟨c, hc⟩
  refine ⟨k * c + k, ?_⟩
  intro x z hnot
  let n := phaseInputSize x z
  let m := min (ExtReg.width x) (ExtReg.width z)
  let W := phaseLimbWidth x z k
  have hn_le_next :
      n ≤ nextSignedWidth x z (genOpsWithProduct (k := k) hk0 pts) := by
    exact Nat.le_of_not_gt hnot
  have hnext :
      nextSignedWidth x z (genOpsWithProduct (k := k) hk0 pts)
        ≤ n - (k - 1) * W + c := by
    simpa [n, W] using hc x z
  have hn_le : n ≤ n - (k - 1) * W + c :=
    le_trans hn_le_next hnext
  have hW : W = m / k := by
    unfold W m phaseLimbWidth phaseLimbWidthOfWidth
    by_cases hxz : ExtReg.width x ≤ ExtReg.width z
    · have hdiv : ExtReg.width x / k ≤ ExtReg.width z / k :=
        Nat.div_le_div_right hxz
      simp [Nat.min_eq_left hxz, Nat.min_eq_left hdiv]
    · have hzx : ExtReg.width z ≤ ExtReg.width x := le_of_not_ge hxz
      have hdiv : ExtReg.width z / k ≤ ExtReg.width x / k :=
        Nat.div_le_div_right hzx
      simp [Nat.min_eq_right hzx, Nat.min_eq_right hdiv]
  by_cases hremove : (k - 1) * W ≤ n
  · have hremove_le_c : (k - 1) * W ≤ c := by
      omega
    have hW_le_c : W ≤ c := by
      have hkpred : 1 ≤ k - 1 := by omega
      nlinarith [hremove_le_c, hkpred, Nat.zero_le W]
    have hmod : m % k ≤ k - 1 := by
      have hlt : m % k < k := Nat.mod_lt m hk0
      omega
    have hsplit : m = k * (m / k) + m % k := by
      simpa [Nat.add_comm] using (Nat.mod_add_div m k).symm
    change m ≤ k * c + k
    rw [hW] at hW_le_c
    calc
      m = k * (m / k) + m % k := hsplit
      _ ≤ k * c + (k - 1) :=
          Nat.add_le_add (Nat.mul_le_mul_left k hW_le_c) hmod
      _ ≤ k * c + k :=
          Nat.add_le_add_left (Nat.sub_le k 1) (k * c)
  · have hn_le_c : n ≤ c := by
      omega
    have hm_le_n : m ≤ n := by
      simp [m, n, phaseInputSize]
    change m ≤ k * c + k
    exact le_trans hm_le_n (le_trans hn_le_c (by nlinarith [Nat.zero_le k, Nat.zero_le c]))


/-! ---------------------------------------------------------
    Step 4: exact one-recursion-level cost inequality
--------------------------------------------------------- -/

/-! Auxiliary lemmas computing the low-gate cost of the recursively lowered
    signed compilation.  Throughout, `COST g` abbreviates the gate count of
    `lowerGateRec` applied to `g` in `shorGateCostModel`. -/
section OneLevelCost
open Gate

variable {Basis : Type u}
  [RegEncoding Basis] [ExtRegEncoding Basis] [ExtRegSplitSemantics Basis]
variable (W k : ℕ) (hk : 1 < k) (pts : List Point) (hpts : pts.length = q k ) (ops : Prog k)

local notation "COST " g =>
  LowGate.gateCount shorGateCostModel
    (lowerGateRec (Basis := Basis) W k hk pts hpts ops g)

-- Structural reduction lemmas: `lowerGateRec` uses well-founded recursion, so we
-- unfold it one constructor at a time with its equation lemma.
/-- The lowered identity has zero cost inside the one-level cost calculation. -/
lemma lgc_id : (COST Gate.id) = 0 := by rw [lowerGateRec]; rfl

/-- Lowered sequencing splits into the sum of the component costs. -/
lemma lgc_seq (U V : Gate) :
    (COST (U ;; V)) = (COST U) + (COST V) := by
  rw [lowerGateRec]; rfl

/-- Left shifts are free in the PhaseProduct cost model. -/
lemma lgc_shiftL (r : ExtReg) (n : ℕ) : (COST (Gate.ShiftL r n)) = 0 := by
  rw [lowerGateRec]; rfl

/-- Right shifts are free in the PhaseProduct cost model. -/
lemma lgc_shiftR (r : ExtReg) (n : ℕ) : (COST (Gate.ShiftR r n)) = 0 := by
  rw [lowerGateRec]; rfl

/-- A lowered negation contributes the chosen linear negation bound. -/
lemma lgc_negate (r : ExtReg) :
    (COST (Gate.Negate r)) = negateGateBound r := by
  rw [lowerGateRec]; rfl

/-- A lowered scaled addition contributes one ripple-adder bound at the
destination width. -/
lemma lgc_addScaled (dst src : ExtReg) (b : Bool) (sh : ℕ) :
    (COST (Gate.AddScaled dst src b sh)) = rippleAdderGateBound (ExtReg.width dst) := by
  rw [lowerGateRec]; rfl

/-- Zero extension is treated as free bookkeeping in this model. -/
lemma lgc_zeroExtend (r : ExtReg) (n : ℕ) : (COST (Gate.zeroExtend r n)) = 0 := by
  rw [lowerGateRec]; rfl

/-- Sign extension is treated as free bookkeeping in this model. -/
lemma lgc_signExtend (r : ExtReg) (n : ℕ) : (COST (Gate.signExtend r n)) = 0 := by
  rw [lowerGateRec]; rfl

/-- Zero deallocation is treated as free bookkeeping in this model. -/
lemma lgc_zeroDealloc (r : ExtReg) (n : ℕ) : (COST (Gate.zeroDealloc r n)) = 0 := by
  rw [lowerGateRec]; rfl

/-- Sign deallocation is treated as free bookkeeping in this model. -/
lemma lgc_signDealloc (r : ExtReg) (n : ℕ) : (COST (Gate.signDealloc r n)) = 0 := by
  rw [lowerGateRec]; rfl

-- Allocation / deallocation of a single chunk costs zero: each is `id`,
-- `signExtend`/`signDealloc` or `zeroExtend`/`zeroDealloc`, all free.
/-- Allocating one signed chunk is free in the cost model, so allocation setup
does not affect the recurrence. -/
lemma lgc_allocChunk (i : Fin k) (src dst : ExtReg) :
    (COST (allocChunkGate i src dst)) = 0 := by
  simp only [allocChunkGate]
  split_ifs
  · exact lgc_id W k hk pts hpts ops
  · exact lgc_signExtend W k hk pts hpts ops _ _
  · exact lgc_zeroExtend W k hk pts hpts ops _ _

/-- Deallocating one signed chunk is free in the cost model, so uncomputation
bookkeeping does not affect the recurrence. -/
lemma lgc_deallocChunk (i : Fin k) (src dst : ExtReg) :
    (COST (deallocChunkGate i src dst)) = 0 := by
  simp only [deallocChunkGate]
  split_ifs
  · exact lgc_id W k hk pts hpts ops
  · exact lgc_signDealloc W k hk pts hpts ops _ _
  · exact lgc_zeroDealloc W k hk pts hpts ops _ _

-- Hence all allocations / deallocations together cost zero.
/-- All signed allocation gates together have zero cost, leaving only the
annotated arithmetic body in the one-level estimate. -/
lemma lgc_allocsAux (src dst : LayoutState k) :
    ∀ (n : ℕ) (hn : n ≤ k),
      (COST (compileSignedAllocationsAux src dst n hn)) = 0 := by
  intro n
  induction n with
  | zero => intro hn; rw [compileSignedAllocationsAux]; exact lgc_id W k hk pts hpts ops
  | succ m ih =>
      intro hn
      rw [compileSignedAllocationsAux]
      rw [lgc_seq, lgc_seq]
      rw [lgc_allocChunk, lgc_allocChunk]
      have := ih (Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self m)) hn)
      omega

/-- All signed deallocation gates together have zero cost, so the inverse
layout cleanup is omitted from the recurrence cost. -/
lemma lgc_deallocsAux (src dst : LayoutState k) :
    ∀ (n : ℕ) (hn : n ≤ k),
      (COST (compileSignedDeallocationsAux src dst n hn)) = 0 := by
  intro n
  induction n with
  | zero => intro hn; rw [compileSignedDeallocationsAux]; exact lgc_id W k hk pts hpts ops
  | succ m ih =>
      intro hn
      rw [compileSignedDeallocationsAux]
      rw [lgc_seq, lgc_seq]
      rw [lgc_deallocChunk, lgc_deallocChunk]
      have := ih (Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self m)) hn)
      omega

/-- A recursively lowered phase leaf whose operands already have the recursion's
target width is exactly one recursively lowered signed phase product: the
`lowerGateRec` cutoff `W` equals `phaseInputSize a b`, so the two branch the same
way. -/
lemma lgc_signedPhaseProd_child (a b : ExtReg) (ψ : ℝ)
    (hpe : pts = genInterpolationPoints k)
    (hab : phaseInputSize a b = W) :
    (COST (Gate.SignedPhaseProd ψ a b))
      = signedPhaseProductGateCount (Basis := Basis) k hk ops ψ a b := by
  subst hpe
  have h : lowerGateRec (Basis := Basis) W k hk (genInterpolationPoints k) hpts ops
        (Gate.SignedPhaseProd ψ a b)
      = lowerSignedPhaseProd (Basis := Basis) k hk ψ a b ops := by
    rw [lowerGateRec, lowerSignedPhaseProd, hab]
  rw [h]
  rfl

/-- Exposes the fold defining nonrecursive overhead on a cons cell, used by the
body-cost induction. -/
lemma phaseProgramOverhead_cons (op : valid_ops k) (rest : List (valid_ops k)) :
    phaseProgramOverhead W (op :: rest)
      = phaseArithmeticOpCost W op + phaseProgramOverhead W rest := rfl

/-- Induction on the annotated operations.  Each source operation contributes
its scalar `phaseArithmeticOpCost` (allocations/shifts free, negate and addScaled
run once per `x`/`z` slot at the common width `W`), and each annotated phase leaf
contributes one recursively lowered child, bounded by `R`. -/
lemma lgc_body_le
    (st : LayoutState k)
    (coeff : Fin (q k ) → ℚ)
    (φ : ℝ) (R : ℝ)
    (hR : 0 ≤ R)
    (hxw : ∀ i : Fin k, ExtReg.width (st.xslot i) = W)
    (hzw : ∀ i : Fin k, ExtReg.width (st.zslot i) = W)
    (hchild : ∀ (ψ : ℝ) (i : Fin k),
      ((COST (Gate.SignedPhaseProd ψ (st.xslot i) (st.zslot i))) : ℝ) ≤ R)
    (n : ℕ) (l : List (valid_ops k)) :
      ((COST (compileAnnotatedOpsToSignedGateAux k hk φ coeff st
            (annotatePhaseTermsAux k n l))) : ℝ)
      ≤ (phaseProgramOverhead W l : ℝ) + (phaseProductCount l : ℝ) * R := by
  induction l generalizing n with
  | nil =>
      simp only [annotatePhaseTermsAux, compileAnnotatedOpsToSignedGateAux,
        phaseProgramOverhead, phaseProductCount, List.foldr]
      rw [lgc_id]
      simp
  | cons op rest ih =>
      cases op with
      | shiftL i m =>
          simp only [annotatePhaseTermsAux, compileAnnotatedOpsToSignedGateAux]
          rw [lgc_seq, lgc_seq, lgc_shiftL, lgc_shiftL,
            phaseProgramOverhead_cons]
          simp only [phaseProductCount, phaseArithmeticOpCost]
          have := ih n
          push_cast at this ⊢
          linarith
      | shiftR i m =>
          simp only [annotatePhaseTermsAux, compileAnnotatedOpsToSignedGateAux]
          rw [lgc_seq, lgc_seq, lgc_shiftR, lgc_shiftR,
            phaseProgramOverhead_cons]
          simp only [phaseProductCount, phaseArithmeticOpCost]
          have := ih n
          push_cast at this ⊢
          linarith
      | negate i =>
          simp only [annotatePhaseTermsAux, compileAnnotatedOpsToSignedGateAux]
          rw [lgc_seq, lgc_seq, lgc_negate, lgc_negate,
            phaseProgramOverhead_cons]
          simp only [phaseProductCount, phaseArithmeticOpCost, negateGateBound]
          rw [hxw i, hzw i]
          have := ih n
          push_cast at this ⊢
          linarith
      | addScaled dst src negsrc sh =>
          simp only [annotatePhaseTermsAux, compileAnnotatedOpsToSignedGateAux]
          rw [lgc_seq, lgc_seq, lgc_addScaled, lgc_addScaled,
            phaseProgramOverhead_cons]
          simp only [phaseProductCount, phaseArithmeticOpCost]
          rw [hxw dst, hzw dst]
          have := ih n
          push_cast at this ⊢
          linarith
      | phaseProduct i =>
          simp only [annotatePhaseTermsAux]
          split_ifs with hn
          · -- annotation present: one recursively lowered child
            simp only [compileAnnotatedOpsToSignedGateAux]
            rw [lgc_seq, phaseProgramOverhead_cons]
            simp only [phaseProductCount, phaseArithmeticOpCost]
            have hc := hchild (φ * ((coeff ⟨n, hn⟩ : ℚ) : ℝ)) i
            have ht := ih (n + 1)
            push_cast at hc ht ⊢
            nlinarith [hc, ht, hR]
          · -- no annotation slot left: no gate emitted, but still counted
            simp only [compileAnnotatedOpsToSignedGateAux]
            rw [phaseProgramOverhead_cons]
            simp only [phaseProductCount, phaseArithmeticOpCost]
            have ht := ih (n + 1)
            push_cast at ht ⊢
            nlinarith [ht, hR]

end OneLevelCost

/--
One recursion node consists of:

* the arithmetic needed to form and unform the evaluations; and
* at most `phaseProductCount ops` recursively lowered PhaseProducts.

All recursive operands have the common target width `nextSignedWidth`.
-/
lemma lowerSignedPhaseProd_one_level_cost_le
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (φ : ℝ)
    (x z : ExtReg)
    (hrec :
      nextSignedWidth x z ops < phaseInputSize x z)
    (R : ℝ)
    (hchildren :
      ∀ (ψ : ℝ) (a b : ExtReg),
        ExtReg.width a = nextSignedWidth x z ops →
        ExtReg.width b = nextSignedWidth x z ops →
        (signedPhaseProductGateCount
            (Basis := Basis) k hk ops ψ a b : ℝ)
          ≤ R) :
    (signedPhaseProductGateCount
        (Basis := Basis) k hk ops φ x z : ℝ)
      ≤
    (phaseProgramOverhead
        (nextSignedWidth x z ops) ops : ℝ)
      +
    (phaseProductCount ops : ℝ) * R := by
  have hpts : (genInterpolationPoints k).length = q k  := by
    simp [genInterpolationPoints, q]
  -- every slot of the common target layout has width `nextSignedWidth x z ops`
  have hxw : ∀ i : Fin k,
      ExtReg.width
        ((targetSignedLayoutState (Basis := Basis) x z k (scanNeededWidths x z ops)).xslot i)
        = nextSignedWidth x z ops := by
    intro i
    exact targetSignedLayoutState_xslot_width_scan x z ops i
  have hzw : ∀ i : Fin k,
      ExtReg.width
        ((targetSignedLayoutState (Basis := Basis) x z k (scanNeededWidths x z ops)).zslot i)
        = nextSignedWidth x z ops := by
    intro i
    exact targetSignedLayoutState_zslot_width_scan x z ops i
  -- R is nonnegative (a gate count is a natural number)
  have hR : 0 ≤ R := by
    have hi : (0 : ℕ) < k := by omega
    have := hchildren φ
      ((targetSignedLayoutState (Basis := Basis) x z k (scanNeededWidths x z ops)).xslot ⟨0, hi⟩)
      ((targetSignedLayoutState (Basis := Basis) x z k (scanNeededWidths x z ops)).xslot ⟨0, hi⟩)
      (hxw ⟨0, hi⟩) (hxw ⟨0, hi⟩)
    exact le_trans (by positivity) this
  -- each recursive child costs at most R
  have hchild : ∀ (ψ : ℝ) (i : Fin k),
      ((LowGate.gateCount shorGateCostModel
        (lowerGateRec (Basis := Basis) (nextSignedWidth x z ops) k hk
          (genInterpolationPoints k) hpts ops
          (Gate.SignedPhaseProd ψ
            ((targetSignedLayoutState (Basis := Basis) x z k (scanNeededWidths x z ops)).xslot i)
            ((targetSignedLayoutState (Basis := Basis) x z k (scanNeededWidths x z ops)).zslot i)))) : ℝ)
        ≤ R := by
    intro ψ i
    have hab :
        phaseInputSize
          ((targetSignedLayoutState (Basis := Basis) x z k (scanNeededWidths x z ops)).xslot i)
          ((targetSignedLayoutState (Basis := Basis) x z k (scanNeededWidths x z ops)).zslot i)
          = nextSignedWidth x z ops := by
      simp only [phaseInputSize, hxw i, hzw i, max_self]
    rw [lgc_signedPhaseProd_child (nextSignedWidth x z ops) k hk (genInterpolationPoints k) hpts ops
      _ _ ψ rfl hab]
    exact hchildren ψ _ _ (hxw i) (hzw i)
  -- unfold the lowering along the recursion branch and split off the free
  -- allocations / deallocations, leaving only the annotated body
  unfold signedPhaseProductGateCount
  rw [lowerSignedPhaseProd, dif_pos hrec]
  unfold compileOpsToSignedGate compileSignedAllocations compileSignedDeallocations
  simp only [lgc_seq, lgc_allocsAux, lgc_deallocsAux, Nat.zero_add, Nat.add_zero]
  exact lgc_body_le (nextSignedWidth x z ops) k hk (genInterpolationPoints k) hpts ops
    (targetSignedLayoutState (Basis := Basis) x z k (scanNeededWidths x z ops))
    (phaseCoeffFromPtsWidth k (phaseLimbWidth x z k) (genInterpolationPoints k) hpts)
    φ R hR hxw hzw hchild 0 ops

/-- The per-operation overhead is monotone in the common working width. -/
lemma phaseArithmeticOpCost_mono
    {k : ℕ}
    {W₁ W₂ : ℕ}
    (hW : W₁ ≤ W₂)
    (op : valid_ops k) :
    phaseArithmeticOpCost W₁ op ≤
      phaseArithmeticOpCost W₂ op := by
  cases op <;>
    simp [phaseArithmeticOpCost, rippleAdderGateBound] <;>
    omega


/-- The nonrecursive overhead of a fixed program is monotone in width. -/
lemma phaseProgramOverhead_mono
    {k : ℕ}
    (ops : Prog k)
    {W₁ W₂ : ℕ}
    (hW : W₁ ≤ W₂) :
    phaseProgramOverhead W₁ ops ≤
      phaseProgramOverhead W₂ ops := by
  induction ops with
  | nil =>
      simp [phaseProgramOverhead]

  | cons op rest ih =>
      have hop :
          phaseArithmeticOpCost W₁ op ≤
            phaseArithmeticOpCost W₂ op :=
        phaseArithmeticOpCost_mono hW op

      simpa [phaseProgramOverhead] using
        Nat.add_le_add hop ih

/-- Natural-number form of the one-level recurrence, convenient for finite
base-case induction. -/
lemma lowerSignedPhaseProd_one_level_cost_le_nat
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (φ : ℝ)
    (x z : ExtReg)
    (hrec :
      nextSignedWidth x z ops < phaseInputSize x z)
    (D : ℕ)
    (hchildren :
      ∀ (ψ : ℝ) (a b : ExtReg),
        ExtReg.width a = nextSignedWidth x z ops →
        ExtReg.width b = nextSignedWidth x z ops →
        signedPhaseProductGateCount
            (Basis := Basis) k hk ops ψ a b
          ≤ D) :
    signedPhaseProductGateCount
        (Basis := Basis) k hk ops φ x z
      ≤
    phaseProgramOverhead
        (nextSignedWidth x z ops) ops
      +
    phaseProductCount ops * D := by

  have hchildrenR :
      ∀ (ψ : ℝ) (a b : ExtReg),
        ExtReg.width a = nextSignedWidth x z ops →
        ExtReg.width b = nextSignedWidth x z ops →
        (signedPhaseProductGateCount
            (Basis := Basis) k hk ops ψ a b : ℝ)
          ≤ (D : ℝ) := by
    intro ψ a b ha hb
    have h := hchildren ψ a b ha hb
    exact_mod_cast h

  have hreal :=
    lowerSignedPhaseProd_one_level_cost_le
      (Basis := Basis)
      k hk ops φ x z
      hrec
      (D : ℝ)
      hchildrenR

  have hcast :
      (signedPhaseProductGateCount
          (Basis := Basis) k hk ops φ x z : ℝ)
        ≤
      ((phaseProgramOverhead
          (nextSignedWidth x z ops) ops
          + phaseProductCount ops * D : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_mul] using hreal

  exact_mod_cast hcast

/--
Uniform boundedness on a finite range of input widths.

This supplies the finite base cases in the strong-induction proof of the
recurrence.
-/
lemma signedPhaseProductGateCount_bounded_on_bounded_inputs
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (N : ℕ) :
    ∃ D : ℕ, ∀ (φ : ℝ) (x z : ExtReg),
      phaseInputSize x z ≤ N →
      signedPhaseProductGateCount
          (Basis := Basis) k hk ops φ x z
        ≤ D := by
  classical

  induction N with
  | zero =>
      refine ⟨0, ?_⟩
      intro φ x z hsize

      have hsize0 : phaseInputSize x z = 0 :=
        Nat.eq_zero_of_le_zero hsize

      have hx : ExtReg.width x = 0 := by
        have hxle :
            ExtReg.width x ≤ phaseInputSize x z := by
          simp [phaseInputSize]
        omega

      have hz : ExtReg.width z = 0 := by
        have hzle :
            ExtReg.width z ≤ phaseInputSize x z := by
          simp [phaseInputSize]
        omega

      simp [
        signedPhaseProductGateCount,
        lowerSignedPhaseProd,
        hsize0,
        LowGate.gateCount,
        shorGateCostModel, phaseProductCostModel,
        directSignedPhaseProductGateCount,
        hx,
        hz
      ]

  | succ N ih =>
      rcases ih with ⟨D, hD⟩

      refine
        ⟨max
            (N.succ * N.succ)
            (phaseProgramOverhead N ops
              + phaseProductCount ops * D),
          ?_⟩

      intro φ x z hsize

      by_cases hrec :
          nextSignedWidth x z ops < phaseInputSize x z

      · -- Recursive case.
        have hW :
            nextSignedWidth x z ops ≤ N := by
          omega

        have hchildren :
            ∀ (ψ : ℝ) (a b : ExtReg),
              ExtReg.width a = nextSignedWidth x z ops →
              ExtReg.width b = nextSignedWidth x z ops →
              signedPhaseProductGateCount
                  (Basis := Basis) k hk ops ψ a b
                ≤ D := by
          intro ψ a b ha hb
          apply hD ψ a b

          have :
              phaseInputSize a b =
                nextSignedWidth x z ops := by
            simp [phaseInputSize, ha, hb]

          rw [this]
          exact hW

        have hnode :
            signedPhaseProductGateCount
                (Basis := Basis) k hk ops φ x z
              ≤
            phaseProgramOverhead
                (nextSignedWidth x z ops) ops
              +
            phaseProductCount ops * D :=
          lowerSignedPhaseProd_one_level_cost_le_nat
            (Basis := Basis)
            k hk ops φ x z
            hrec
            D
            hchildren

        have hoverhead :
            phaseProgramOverhead
                (nextSignedWidth x z ops) ops
              ≤
            phaseProgramOverhead N ops :=
          phaseProgramOverhead_mono ops hW

        have hnode' :
            signedPhaseProductGateCount
                (Basis := Basis) k hk ops φ x z
              ≤
            phaseProgramOverhead N ops
              + phaseProductCount ops * D :=
          hnode.trans
            (Nat.add_le_add_right
              hoverhead
              (phaseProductCount ops * D))

        exact hnode'.trans (Nat.le_max_right _ _)

      · -- Direct/base-case branch.
        have hbase :
            signedPhaseProductGateCount
                (Basis := Basis) k hk ops φ x z
              =
            ExtReg.width x * ExtReg.width z := by
          simp [
            signedPhaseProductGateCount,
            lowerSignedPhaseProd,
            hrec,
            LowGate.gateCount,
            shorGateCostModel, phaseProductCostModel,
            directSignedPhaseProductGateCount
          ]

        have hxmax :
            ExtReg.width x ≤ phaseInputSize x z := by
          simp [phaseInputSize]

        have hzmax :
            ExtReg.width z ≤ phaseInputSize x z := by
          simp[phaseInputSize]

        have hx : ExtReg.width x ≤ N.succ :=
          hxmax.trans hsize

        have hz : ExtReg.width z ≤ N.succ :=
          hzmax.trans hsize

        have hprod :
            ExtReg.width x * ExtReg.width z
              ≤ N.succ * N.succ :=
          Nat.mul_le_mul hx hz

        rw [hbase]
        exact hprod.trans (Nat.le_max_left _ _)


/-! ---------------------------------------------------------
    Step 5: real-exponent facts used by the recurrence
--------------------------------------------------------- -/

/-- Since `2k - 1 > k` for `k > 1`, the paper's exponent is greater than one. -/
lemma one_lt_phaseProductExponent
    (k : ℕ)
    (hk : 1 < k) :
    1 < phaseProductExponent k := by
  have hkR : 1 < (k : ℝ) := by exact_mod_cast hk
  have hkpos : 0 < (k : ℝ) := lt_trans zero_lt_one hkR
  have hlogpos : 0 < Real.log (k : ℝ) := Real.log_pos hkR
  have hkqNat : k < q k  := by
    unfold q
    omega
  have hkq : (k : ℝ) < (q k  : ℝ) := by exact_mod_cast hkqNat
  have hloglt : Real.log (k : ℝ) < Real.log (q k  : ℝ) :=
    Real.log_lt_log hkpos hkq
  unfold phaseProductExponent
  rw [lt_div_iff₀ hlogpos]
  simpa using hloglt

/--
The exponent was chosen so that one level's branching factor is exactly the
corresponding power of the shrink factor:

  k ^ log_k(2k - 1) = 2k - 1.
-/
lemma rpow_phaseProductExponent_eq_q
    (k : ℕ)
    (hk : 1 < k) :
    Real.rpow (k : ℝ) (phaseProductExponent k) = (q k : ℝ) := by
  have hkR : 1 < (k : ℝ) := by exact_mod_cast hk
  have hkpos : 0 < (k : ℝ) := lt_trans zero_lt_one hkR
  have hlogpos : 0 < Real.log (k : ℝ) := Real.log_pos hkR
  have hqposNat : 0 < q k  := by
    unfold q
    omega
  have hqpos : 0 < (q k  : ℝ) := by exact_mod_cast hqposNat
  unfold phaseProductExponent
  rw [Real.rpow_eq_pow, Real.rpow_def_of_pos hkpos]
  have hmul :
      Real.log (k : ℝ) * (Real.log (q k  : ℝ) / Real.log (k : ℝ))
        = Real.log (q k : ℝ) := by
    field_simp [hlogpos.ne']
  rw [hmul, Real.exp_log hqpos]


/-! ---------------------------------------------------------
    Step 6a: shift balanced child widths into Master-theorem form
--------------------------------------------------------- -/

/-- Converts the generated `ceil(n/k) + c` child-width bound into the shifted
shape required by the Master theorem helper. -/
lemma balanced_nextSignedWidth_shifted
    (k c n W : ℕ)
    (hk : 1 < k)
    (hM : k * (c + 1) + 1 ≤ n)
    (hW : W ≤ (n + k - 1) / k + c) :
    W ≤
      k * (c + 1) + 1 +
        (n - (k * (c + 1) + 1)) / k := by
  let M : ℕ := k * (c + 1) + 1
  let t : ℕ := n - M

  have hn : n = M + t := by
    dsimp [M, t]
    omega

  have hk0 : 0 < k := by omega
  have hk2 : 2 ≤ k := by omega

  have hnum :
      M + t + k - 1 =
        t + k * (c + 2) := by
    dsimp [M]
    have h₁ :
        k * (c + 1) + 1 + t + k - 1 =
          k * (c + 1) + t + k := by
      omega
    rw [h₁]
    ring

  have hdiv :
      (M + t + k - 1) / k + c
        =
      t / k + (c + 2) + c := by
    rw [hnum]
    rw [Nat.add_mul_div_left t (c + 2) hk0]

  have hkc :
      2 * (c + 1) ≤ k * (c + 1) :=
    Nat.mul_le_mul_right (c + 1) hk2

  have hsmall :
      t / k + (c + 2) + c
        ≤
      M + t / k := by
    dsimp [M]
    omega

  rw [hn] at hW
  rw [hdiv] at hW
  simpa [M, t, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    using hW.trans hsmall


/-! ---------------------------------------------------------
    Step 6b: solve the paper recurrence on balanced inputs
--------------------------------------------------------- -/

/--
A signed PhaseProduct instance whose two operand widths agree.
-/
structure BalancedPhaseProductInstance where
  φ : ℝ
  x : ExtReg
  z : ExtReg
  hwidth : ExtReg.width x = ExtReg.width z

/--
Strong-induction solution of

  T(n) ≤ q(k) * T(ceil(n/k) + c) + A*n + B.

The fixed additive `c` is handled by the shifted Master theorem. Since

  q(k) = k^(phaseProductExponent k)

and the exponent is greater than one, the resulting bound is

  T(n) = O(n^(phaseProductExponent k)).
-/
lemma balanced_phaseProduct_recurrence_solution
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (hcount :
      phaseProductCount ops = q k )
    (hwidth :
      ∃ c : ℕ, ∀ x z : ExtReg,
        ExtReg.width x = ExtReg.width z →
        nextSignedWidth x z ops
          ≤ (ExtReg.width x + k - 1) / k + c)
    (hoverhead :
      ∃ A B : ℕ, ∀ W : ℕ,
        phaseProgramOverhead W ops ≤ A * W + B) :
    ∃ C : ℝ, 0 < C ∧
      BalancedSignedPhaseProductBound
        (Basis := Basis) k hk ops C := by
  classical

  rcases hwidth with ⟨c, hwidth⟩
  rcases hoverhead with ⟨A, B, hoverhead⟩

  let size : BalancedPhaseProductInstance → ℕ :=
    fun i => ExtReg.width i.x

  let next : BalancedPhaseProductInstance → ℕ :=
    fun i => nextSignedWidth i.x i.z ops

  let cost : BalancedPhaseProductInstance → ℕ :=
    fun i =>
      signedPhaseProductGateCount
        (Basis := Basis)
        k hk ops i.φ i.x i.z

  /-
  The generated recursive width is at most

      ceil(n / k) + c

  on every balanced instance.
  -/
  have hnext :
      ∀ i : BalancedPhaseProductInstance,
        next i ≤
          (size i + k - 1) / k + c := by
    intro i

    simpa [next, size] using
      hwidth i.x i.z i.hwidth

  /-
  All instances whose widths lie below a fixed cutoff have a uniform
  gate-count bound.
  -/
  have hbounded :
      ∀ N : ℕ,
        ∃ D : ℕ, ∀ i : BalancedPhaseProductInstance,
          size i ≤ N →
          cost i ≤ D := by
    intro N

    obtain ⟨D, hD⟩ :=
      signedPhaseProductGateCount_bounded_on_bounded_inputs
        (Basis := Basis)
        k hk ops N

    refine ⟨D, ?_⟩
    intro i hi

    apply hD i.φ i.x i.z

    have hsize :
        phaseInputSize i.x i.z = size i := by
      simp [phaseInputSize, size, i.hwidth]

    rw [hsize]
    exact hi

  /-
  This is the compiler-specific one-level recurrence.

  If all balanced instances of the recursive width have cost at most `D`,
  then this instance has cost at most

      A * next + B + q(k) * D.
  -/
  have hstep :
      ∀ i : BalancedPhaseProductInstance,
        next i < size i →
        ∀ D : ℕ,
          (∀ j : BalancedPhaseProductInstance,
            size j = next i →
            cost j ≤ D) →
          cost i ≤
            A * next i + B + q k  * D := by
    intro i hrec D hchildrenBound

    have hrec' :
        nextSignedWidth i.x i.z ops
          < phaseInputSize i.x i.z := by
      simpa [next, size, phaseInputSize, i.hwidth] using hrec

    have hchildren :
        ∀ (ψ : ℝ) (a b : ExtReg),
          ExtReg.width a =
              nextSignedWidth i.x i.z ops →
          ExtReg.width b =
              nextSignedWidth i.x i.z ops →
          signedPhaseProductGateCount
              (Basis := Basis)
              k hk ops ψ a b
            ≤ D := by
      intro ψ a b ha hb

      let j : BalancedPhaseProductInstance :=
        {
          φ := ψ
          x := a
          z := b
          hwidth := ha.trans hb.symm
        }

      have hjsize :
          size j = next i := by
        simp [j, size, next, ha]

      exact hchildrenBound j hjsize

    have honeLevel :
        signedPhaseProductGateCount
            (Basis := Basis)
            k hk ops i.φ i.x i.z
          ≤
        phaseProgramOverhead
            (nextSignedWidth i.x i.z ops)
            ops
          +
        phaseProductCount ops * D :=
      lowerSignedPhaseProd_one_level_cost_le_nat
        (Basis := Basis)
        k hk ops
        i.φ i.x i.z
        hrec'
        D
        hchildren

    have hoverhead' :
        phaseProgramOverhead (next i) ops
          ≤ A * next i + B :=
      hoverhead (next i)

    calc
      cost i
          ≤
        phaseProgramOverhead (next i) ops
          + phaseProductCount ops * D := by
            simpa [cost, next] using honeLevel
      _ ≤
        (A * next i + B)
          + phaseProductCount ops * D :=
        Nat.add_le_add_right
          hoverhead'
          (phaseProductCount ops * D)
      _ =
        A * next i + B + q k  * D := by
          rw [hcount]

  obtain ⟨C, hC, hmaster⟩ :=
    shifted_master_theorem_exact_family
      (ι := BalancedPhaseProductInstance)
      (k := k)
      (q := q k )
      (c := c)
      (A := A)
      (B := B)
      (α := phaseProductExponent k)
      hk
      (one_lt_phaseProductExponent k hk)
      (rpow_phaseProductExponent_eq_q k  hk)
      size
      next
      cost
      hnext
      hbounded
      hstep

  refine ⟨C, hC, ?_⟩

  intro φ x z hxz

  let i : BalancedPhaseProductInstance :=
    {
      φ := φ
      x := x
      z := z
      hwidth := hxz
    }

  have hi := hmaster i

  simpa [
    i,
    size,
    cost,
    phaseProductSafeRate
  ] using hi

/-- Rewrites the public unsigned `PhaseProd` lowering as the signed recurrence
applied to unsigned views of the two input registers. -/
lemma lowerGate_PhaseProd_gateCount_eq_signed_unsignedView
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (φ : ℝ)
    (x z : Reg) :
    LowGate.gateCount shorGateCostModel
      (lowerGate (Basis := Basis) k hk ops (Gate.PhaseProd φ x z))
      =
    signedPhaseProductGateCount
      (Basis := Basis) k hk ops φ
      (Gate.unsignedView x) (Gate.unsignedView z) := by
  simp [lowerGate, Gate.PhaseProd, signedPhaseProductGateCount,
    lowerSignedPhaseProd, LowGate.gateCount, shorGateCostModel, phaseProductCostModel]

/-- Unsigned views add exactly one high extension bit to an ordinary register. -/
@[simp]
lemma width_unsignedView (r : Reg) :
    ExtReg.width (Gate.unsignedView r) = regSize r + 1 := by
  simp [Gate.unsignedView, ExtReg.width, ExtReg.ofReg, ExtReg.addExtra]

/-- The signed input size of two unsigned views is the original maximum
register width plus one. -/
@[simp]
lemma phaseInputSize_unsignedView (x z : Reg) :
    phaseInputSize (Gate.unsignedView x) (Gate.unsignedView z)
      =
    max (regSize x) (regSize z) + 1 := by
  simp only [phaseInputSize, width_unsignedView]
  by_cases h : regSize x ≤ regSize z
  · rw [
      max_eq_right h,
      max_eq_right (Nat.add_le_add_right h 1)
    ]
  · have h' : regSize z ≤ regSize x :=
      Nat.le_of_lt (Nat.lt_of_not_ge h)
    rw [
      max_eq_left h',
      max_eq_left (Nat.add_le_add_right h' 1)
    ]

/--
Absorb a fixed additive increase in the base of a real power.

For `1 ≤ n` and `W ≤ n + s`,

    max 1 W ≤ (s + 1) * n,

so raising both sides to a nonnegative exponent gives the result.
-/
lemma phaseProductSafeRate_le_scaled_rpow
    (k : ℕ)
    (hk : 1 < k)
    {W n s : ℕ}
    (hn : 1 ≤ n)
    (hW : W ≤ n + s) :
    phaseProductSafeRate k W
      ≤
    Real.rpow ((s + 1 : ℕ) : ℝ) (phaseProductExponent k) *
      Real.rpow (n : ℝ) (phaseProductExponent k) := by
  have hα :
      0 ≤ phaseProductExponent k := by
    have hα' := one_lt_phaseProductExponent k hk
    linarith

  have hmax :
      max 1 W ≤ n + s := by
    apply max_le
    · omega
    · exact hW

  have hs_mul :
      s ≤ s * n := by
    simpa using Nat.mul_le_mul_left s hn

  have hscale :
      n + s ≤ (s + 1) * n := by
    calc
      n + s ≤ n + s * n :=
        Nat.add_le_add_left hs_mul n
      _ = (s + 1) * n := by
        simp [Nat.add_mul, Nat.add_comm]

  have hpow₁ :
      Real.rpow ((max 1 W : ℕ) : ℝ)
          (phaseProductExponent k)
        ≤
      Real.rpow ((n + s : ℕ) : ℝ)
          (phaseProductExponent k) :=
    Real.rpow_le_rpow
      (by positivity)
      (by exact_mod_cast hmax)
      hα

  have hpow₂ :
      Real.rpow ((n + s : ℕ) : ℝ)
          (phaseProductExponent k)
        ≤
      Real.rpow (((s + 1) * n : ℕ) : ℝ)
          (phaseProductExponent k) :=
    Real.rpow_le_rpow
      (by positivity)
      (by exact_mod_cast hscale)
      hα

  calc
    phaseProductSafeRate k W
        =
      Real.rpow ((max 1 W : ℕ) : ℝ)
        (phaseProductExponent k) := rfl
    _ ≤
      Real.rpow ((n + s : ℕ) : ℝ)
        (phaseProductExponent k) := hpow₁
    _ ≤
      Real.rpow (((s + 1) * n : ℕ) : ℝ)
        (phaseProductExponent k) := hpow₂
    _ =
      Real.rpow ((s + 1 : ℕ) : ℝ)
          (phaseProductExponent k) *
        Real.rpow (n : ℝ)
          (phaseProductExponent k) := by
      simpa only [Nat.cast_mul] using
        (Real.mul_rpow
          (show 0 ≤ ((s + 1 : ℕ) : ℝ) by positivity)
          (show 0 ≤ (n : ℝ) by positivity)
          (z := phaseProductExponent k))

/--
For `n ≥ 1`, the linear function `n` is bounded by the
PhaseProduct comparison power because its exponent is greater than one.
-/
lemma natCast_le_phaseProduct_rpow
    (k : ℕ)
    (hk : 1 < k)
    {n : ℕ}
    (hn : 1 ≤ n) :
    (n : ℝ)
      ≤
    Real.rpow (n : ℝ) (phaseProductExponent k) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn

  exact
    Real.self_le_rpow_of_one_le
      hnR
      (le_of_lt (one_lt_phaseProductExponent k hk))

/--
In the nonrecursive branch, lowering is exactly the direct signed
PhaseProduct, whose cost is the product of the operand widths.
-/
lemma signedPhaseProductGateCount_eq_direct_of_not_recurse
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (φ : ℝ)
    (x z : ExtReg)
    (hno :
      ¬ nextSignedWidth x z ops < phaseInputSize x z) :
    signedPhaseProductGateCount
        (Basis := Basis) k hk ops φ x z
      =
    ExtReg.width x * ExtReg.width z := by
  simp [
    signedPhaseProductGateCount,
    lowerSignedPhaseProd,
    hno,
    LowGate.gateCount,
    shorGateCostModel, phaseProductCostModel,
    directSignedPhaseProductGateCount
  ]

/-- Bounds the public unsigned theorem's recursive branch by applying the
balanced signed bound to the equal-width recursive children. -/
lemma signedPhaseProductGateCount_unsignedView_recurse_case_bound
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (hcount :
      phaseProductCount ops = q k )
    (hoverhead :
      ∃ A B : ℕ, ∀ W : ℕ,
        phaseProgramOverhead W ops ≤ A * W + B)
    (hgrowth :
      ∃ c : ℕ, ∀ x z : ExtReg,
        nextSignedWidth x z ops ≤ phaseInputSize x z + c)
    (C : ℝ)
    (hC : 0 < C)
    (hbalanced :
      BalancedSignedPhaseProductBound
        (Basis := Basis) k hk ops C) :
    ∃ Cᵣ : ℝ, 0 < Cᵣ ∧
    ∃ nᵣ : ℕ, 1 ≤ nᵣ ∧
      ∀ (φ : ℝ) (x z : Reg),
        let n := max (regSize x) (regSize z)
        nextSignedWidth (Gate.unsignedView x) (Gate.unsignedView z) ops
          < phaseInputSize (Gate.unsignedView x) (Gate.unsignedView z) →
        nᵣ ≤ n →
        (signedPhaseProductGateCount
          (Basis := Basis) k hk ops φ
          (Gate.unsignedView x) (Gate.unsignedView z) : ℝ)
          ≤ Cᵣ * Real.rpow n (phaseProductExponent k) := by
  rcases hoverhead with ⟨A, B, hAB⟩
  rcases hgrowth with ⟨c, hc⟩

  let s : ℕ := c + 1

  let K : ℝ :=
    Real.rpow ((s + 1 : ℕ) : ℝ)
      (phaseProductExponent k)

  let L : ℝ :=
    (A : ℝ) * ((s + 1 : ℕ) : ℝ) + (B : ℝ)

  let Cᵣ : ℝ :=
    1 + L + (q k  : ℝ) * C * K

  have hKpos : 0 < K := by
    dsimp [K]
    positivity

  have hLnonneg : 0 ≤ L := by
    dsimp [L]
    positivity

  have hCᵣ : 0 < Cᵣ := by
    dsimp [Cᵣ]
    have hq : 0 ≤ (q k  : ℝ) := by positivity
    have hterm :
        0 ≤ (q k  : ℝ) * C * K := by
      positivity
    linarith

  refine ⟨Cᵣ, hCᵣ, 1, by omega, ?_⟩

  intro φ x z
  dsimp only
  intro hrec hn

  let ux : ExtReg := Gate.unsignedView x
  let uz : ExtReg := Gate.unsignedView z
  let n : ℕ := max (regSize x) (regSize z)
  let W : ℕ := nextSignedWidth ux uz ops

  have hn' : 1 ≤ n := by
    simpa [n] using hn

  have hinput :
      phaseInputSize ux uz = n + 1 := by
    simp [ux, uz, n]

  have hrec' :
      W < phaseInputSize ux uz := by
    simpa [W, ux, uz] using hrec

  have hW :
      W ≤ n + s := by
    have hg := hc ux uz
    rw [hinput] at hg
    dsimp [s]
    omega

  have hnPow :
      (n : ℝ)
        ≤
      Real.rpow (n : ℝ) (phaseProductExponent k) :=
    natCast_le_phaseProduct_rpow k hk hn'

  have hsafe :
      phaseProductSafeRate k W
        ≤
      K * Real.rpow (n : ℝ) (phaseProductExponent k) := by
    simpa [K] using
      phaseProductSafeRate_le_scaled_rpow
        k hk hn' hW

  have hWscaleNat :
      W ≤ (s + 1) * n := by
    exact hW.trans (by
      have hs_mul :
          s ≤ s * n := by
        simpa using Nat.mul_le_mul_left s hn'
      calc
        n + s ≤ n + s * n :=
          Nat.add_le_add_left hs_mul n
        _ = (s + 1) * n := by
          simp [Nat.add_mul, Nat.add_comm])

  have hWscale :
      (W : ℝ)
        ≤
      ((s + 1 : ℕ) : ℝ) * (n : ℝ) := by
    exact_mod_cast hWscaleNat

  have hoverheadR :
      (phaseProgramOverhead W ops : ℝ)
        ≤
      (A : ℝ) * (W : ℝ) + (B : ℝ) := by
    exact_mod_cast hAB W

  have hAW :
      (A : ℝ) * (W : ℝ)
        ≤
      (A : ℝ) * (((s + 1 : ℕ) : ℝ) * (n : ℝ)) :=
    mul_le_mul_of_nonneg_left
      hWscale
      (by positivity)

  have hnR :
      (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn'

  have hB :
      (B : ℝ) ≤ (B : ℝ) * (n : ℝ) := by
    have :=
      mul_le_mul_of_nonneg_left
        hnR
        (show 0 ≤ (B : ℝ) by positivity)
    simpa using this

  have hoverheadLinear :
      (phaseProgramOverhead W ops : ℝ)
        ≤
      L * (n : ℝ) := by
    calc
      (phaseProgramOverhead W ops : ℝ)
          ≤
        (A : ℝ) * (W : ℝ) + (B : ℝ) :=
        hoverheadR
      _ ≤
        (A : ℝ) *
            (((s + 1 : ℕ) : ℝ) * (n : ℝ)) +
          (B : ℝ) :=
        by nlinarith [hAW]
      _ ≤
        (A : ℝ) *
            (((s + 1 : ℕ) : ℝ) * (n : ℝ)) +
          (B : ℝ) * (n : ℝ) :=
        by nlinarith [hB]
      _ = L * (n : ℝ) := by
        dsimp [L]
        ring

  have hoverheadPow :
      (phaseProgramOverhead W ops : ℝ)
        ≤
      L * Real.rpow (n : ℝ) (phaseProductExponent k) :=
    hoverheadLinear.trans
      (mul_le_mul_of_nonneg_left hnPow hLnonneg)

  have hchildren :
      ∀ (ψ : ℝ) (a b : ExtReg),
        ExtReg.width a = W →
        ExtReg.width b = W →
        (signedPhaseProductGateCount
            (Basis := Basis) k hk ops ψ a b : ℝ)
          ≤
        C * phaseProductSafeRate k W := by
    intro ψ a b ha hb
    have hbnd := hbalanced ψ a b (ha.trans hb.symm)
    simpa [ha] using hbnd

  have hone :=
    lowerSignedPhaseProd_one_level_cost_le
      (Basis := Basis)
      k hk ops φ ux uz
      hrec'
      (C * phaseProductSafeRate k W)
      hchildren

  have hone' :
      (signedPhaseProductGateCount
          (Basis := Basis) k hk ops φ ux uz : ℝ)
        ≤
      (phaseProgramOverhead W ops : ℝ) +
        (q k  : ℝ) * (C * phaseProductSafeRate k W) := by
    simpa [W, hcount] using hone

  have hqC :
      0 ≤ (q k  : ℝ) * C := by
    positivity

  have hrecursiveTerm :
      (q k  : ℝ) * (C * phaseProductSafeRate k W)
        ≤
      ((q k  : ℝ) * C * K) *
        Real.rpow (n : ℝ) (phaseProductExponent k) := by
    calc
      (q k  : ℝ) * (C * phaseProductSafeRate k W)
          =
        ((q k  : ℝ) * C) * phaseProductSafeRate k W := by
        ring
      _ ≤
        ((q k  : ℝ) * C) *
          (K * Real.rpow (n : ℝ) (phaseProductExponent k)) :=
        mul_le_mul_of_nonneg_left hsafe hqC
      _ =
        ((q k  : ℝ) * C * K) *
          Real.rpow (n : ℝ) (phaseProductExponent k) := by
        ring

  have hpowNonneg :
      0 ≤ Real.rpow (n : ℝ) (phaseProductExponent k) :=
    Real.rpow_nonneg (by positivity) _

  change
    (signedPhaseProductGateCount
      (Basis := Basis) k hk ops φ ux uz : ℝ)
      ≤
    Cᵣ * Real.rpow (n : ℝ) (phaseProductExponent k)

  calc
    (signedPhaseProductGateCount
        (Basis := Basis) k hk ops φ ux uz : ℝ)
        ≤
      (phaseProgramOverhead W ops : ℝ) +
        (q k  : ℝ) * (C * phaseProductSafeRate k W) :=
      hone'
    _ ≤
      L * Real.rpow (n : ℝ) (phaseProductExponent k) +
        ((q k  : ℝ) * C * K) *
          Real.rpow (n : ℝ) (phaseProductExponent k) :=
      add_le_add hoverheadPow hrecursiveTerm
    _ =
      (L + (q k  : ℝ) * C * K) *
        Real.rpow (n : ℝ) (phaseProductExponent k) := by
      ring
    _ ≤
      Cᵣ * Real.rpow (n : ℝ) (phaseProductExponent k) := by
      apply mul_le_mul_of_nonneg_right _ hpowNonneg
      dsimp [Cᵣ]
      linarith

/-- Bounds the public unsigned theorem's nonrecursive branch: the direct
quadratic base case becomes linear because the smaller operand is bounded. -/
lemma signedPhaseProductGateCount_unsignedView_no_recurse_case_bound
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (hnarrow :
      ∃ d : ℕ, ∀ x z : ExtReg,
        ¬ nextSignedWidth x z ops < phaseInputSize x z →
        min (ExtReg.width x) (ExtReg.width z) ≤ d) :
    ∃ Cₙ : ℝ, 0 < Cₙ ∧
    ∃ nₙ : ℕ, 1 ≤ nₙ ∧
      ∀ (φ : ℝ) (x z : Reg),
        let n := max (regSize x) (regSize z)
        ¬ nextSignedWidth (Gate.unsignedView x) (Gate.unsignedView z) ops
          < phaseInputSize (Gate.unsignedView x) (Gate.unsignedView z) →
        nₙ ≤ n →
        (signedPhaseProductGateCount
          (Basis := Basis) k hk ops φ
          (Gate.unsignedView x) (Gate.unsignedView z) : ℝ)
          ≤ Cₙ * Real.rpow n (phaseProductExponent k) := by
  rcases hnarrow with ⟨d, hd⟩

  refine ⟨2 * (d : ℝ) + 1, by positivity, 1, by omega, ?_⟩

  intro φ x z
  dsimp only
  intro hno hn

  let ux : ExtReg := Gate.unsignedView x
  let uz : ExtReg := Gate.unsignedView z
  let n : ℕ := max (regSize x) (regSize z)

  have hn' : 1 ≤ n := by
    simpa [n] using hn

  have hno' :
      ¬ nextSignedWidth ux uz ops < phaseInputSize ux uz := by
    simpa [ux, uz] using hno

  have hsmall :
      min (regSize x + 1) (regSize z + 1) ≤ d := by
    simpa [ux, uz] using hd ux uz hno'

  have hprod :
      (regSize x + 1) * (regSize z + 1)
        ≤
      2 * d * n := by
    by_cases hxz : regSize x ≤ regSize z
    · have hnEq : n = regSize z := by
        simp [n, max_eq_right hxz]

      have hxz' :
          regSize x + 1 ≤ regSize z + 1 :=
        Nat.add_le_add_right hxz 1

      have hxsmall :
          regSize x + 1 ≤ d := by
        simpa [min_eq_left hxz'] using hsmall

      have hzpos : 1 ≤ regSize z := by
        simpa [hnEq] using hn'

      have hzdouble :
          regSize z + 1 ≤ 2 * regSize z := by
        omega

      calc
        (regSize x + 1) * (regSize z + 1)
            ≤
          d * (regSize z + 1) :=
          Nat.mul_le_mul hxsmall (le_refl _)
        _ ≤
          d * (2 * regSize z) :=
          Nat.mul_le_mul_left d hzdouble
        _ = 2 * d * n := by
          rw [hnEq]
          ring

    · have hzx : regSize z ≤ regSize x :=
        Nat.le_of_lt (Nat.lt_of_not_ge hxz)

      have hnEq : n = regSize x := by
        simp [n, max_eq_left hzx]

      have hzx' :
          regSize z + 1 ≤ regSize x + 1 :=
        Nat.add_le_add_right hzx 1

      have hzsmall :
          regSize z + 1 ≤ d := by
        simpa [min_eq_right hzx'] using hsmall

      have hxpos : 1 ≤ regSize x := by
        simpa [hnEq] using hn'

      have hxdouble :
          regSize x + 1 ≤ 2 * regSize x := by
        omega

      calc
        (regSize x + 1) * (regSize z + 1)
            =
          (regSize z + 1) * (regSize x + 1) := by
          ac_rfl
        _ ≤
          d * (regSize x + 1) :=
          Nat.mul_le_mul hzsmall (le_refl _)
        _ ≤
          d * (2 * regSize x) :=
          Nat.mul_le_mul_left d hxdouble
        _ = 2 * d * n := by
          rw [hnEq]
          ring

  have hdirect :
      signedPhaseProductGateCount
          (Basis := Basis) k hk ops φ ux uz
        =
      (regSize x + 1) * (regSize z + 1) := by
    calc
      signedPhaseProductGateCount
          (Basis := Basis) k hk ops φ ux uz
          =
        ExtReg.width ux * ExtReg.width uz :=
        signedPhaseProductGateCount_eq_direct_of_not_recurse
          (Basis := Basis)
          k hk ops φ ux uz hno'
      _ =
        (regSize x + 1) * (regSize z + 1) := by
        simp [ux, uz]

  have hlinear :
      (signedPhaseProductGateCount
          (Basis := Basis) k hk ops φ ux uz : ℝ)
        ≤
      (2 * (d : ℝ)) * (n : ℝ) := by
    rw [hdirect]
    exact_mod_cast hprod

  have hnPow :
      (n : ℝ)
        ≤
      Real.rpow (n : ℝ) (phaseProductExponent k) :=
    natCast_le_phaseProduct_rpow k hk hn'

  have hlinearPow :
      (2 * (d : ℝ)) * (n : ℝ)
        ≤
      (2 * (d : ℝ)) *
        Real.rpow (n : ℝ) (phaseProductExponent k) :=
    mul_le_mul_of_nonneg_left hnPow (by positivity)

  have hpowNonneg :
      0 ≤ Real.rpow (n : ℝ) (phaseProductExponent k) :=
    Real.rpow_nonneg (by positivity) _

  change
    (signedPhaseProductGateCount
      (Basis := Basis) k hk ops φ ux uz : ℝ)
      ≤
    (2 * (d : ℝ) + 1) *
      Real.rpow (n : ℝ) (phaseProductExponent k)

  calc
    (signedPhaseProductGateCount
        (Basis := Basis) k hk ops φ ux uz : ℝ)
        ≤
      (2 * (d : ℝ)) * (n : ℝ) :=
      hlinear
    _ ≤
      (2 * (d : ℝ)) *
        Real.rpow (n : ℝ) (phaseProductExponent k) :=
      hlinearPow
    _ ≤
      (2 * (d : ℝ) + 1) *
        Real.rpow (n : ℝ) (phaseProductExponent k) := by
      apply mul_le_mul_of_nonneg_right _ hpowNonneg
      linarith


/-! ---------------------------------------------------------
    Step 7: pass from balanced signed recursion to the
            theorem's arbitrary unsigned inputs
--------------------------------------------------------- -/

/--
Lift the paper's balanced recurrence bound to the current theorem, which
quantifies over arbitrary unequal ordinary registers.

This is implementation-specific rather than part of the paper:

* if the first level recurses, every child is balanced because all target slots
  have the common width `nextSignedWidth`;
* that common width is at most the original maximum width plus a constant;
* if the first level does not recurse, the smaller operand has bounded width,
  so the direct `width x * width z` base cost is only linear;
* the `unsignedView` wrapper adds one bit, absorbed into the constant.
-/
lemma phaseProductGateCountBound_of_balanced_signed_bound
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (hcount :
      phaseProductCount ops = q k )
    (hoverhead :
      ∃ A B : ℕ, ∀ W : ℕ,
        phaseProgramOverhead W ops ≤ A * W + B)
    (hgrowth :
      ∃ c : ℕ, ∀ x z : ExtReg,
        nextSignedWidth x z ops ≤ phaseInputSize x z + c)
    (hnarrow :
      ∃ d : ℕ, ∀ x z : ExtReg,
        ¬ nextSignedWidth x z ops < phaseInputSize x z →
        min (ExtReg.width x) (ExtReg.width z) ≤ d)
    (C : ℝ)
    (hC : 0 < C)
    (hbalanced :
      BalancedSignedPhaseProductBound
        (Basis := Basis) k hk ops C) :
    PhaseProductGateCountBound
      (Basis := Basis) k hk ops := by
  rcases
    signedPhaseProductGateCount_unsignedView_recurse_case_bound
      (Basis := Basis) k hk ops hcount hoverhead hgrowth C hC hbalanced
    with ⟨Cᵣ, hCᵣ, nᵣ, hnᵣ, hrecurse⟩
  rcases
    signedPhaseProductGateCount_unsignedView_no_recurse_case_bound
      (Basis := Basis) k hk ops hnarrow
    with ⟨Cₙ, hCₙ, nₙ, hnₙ, hnoRecurse⟩

  refine ⟨Cᵣ + Cₙ, by linarith, max nᵣ nₙ, ?_, ?_⟩
  · exact le_trans hnᵣ (Nat.le_max_left nᵣ nₙ)
  · intro φ x z
    dsimp
    intro _hWFx _hWFz _hdisj hnLarge
    let n := max (regSize x) (regSize z)
    have hnᵣ_le : nᵣ ≤ n := by
      exact le_trans (Nat.le_max_left nᵣ nₙ) hnLarge
    have hnₙ_le : nₙ ≤ n := by
      exact le_trans (Nat.le_max_right nᵣ nₙ) hnLarge
    have hn_pos_nat : 0 < n := by
      exact lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_one hnᵣ) hnᵣ_le
    have hrate_nonneg :
        0 ≤ Real.rpow (n : ℝ) (phaseProductExponent k) := by
      exact le_of_lt (Real.rpow_pos_of_pos (by exact_mod_cast hn_pos_nat) _)

    rw [lowerGate_PhaseProd_gateCount_eq_signed_unsignedView
      (Basis := Basis) k hk ops φ x z]

    by_cases hrec :
      nextSignedWidth (Gate.unsignedView x) (Gate.unsignedView z) ops
        < phaseInputSize (Gate.unsignedView x) (Gate.unsignedView z)
    · have hb :=
        hrecurse φ x z hrec hnᵣ_le
      dsimp [n] at hb ⊢
      nlinarith [hb, hrate_nonneg, le_of_lt hCₙ]
    · have hb :=
        hnoRecurse φ x z hrec hnₙ_le
      dsimp [n] at hb ⊢
      nlinarith [hb, hrate_nonneg, le_of_lt hCᵣ]


/-! ---------------------------------------------------------
    Concrete generated table
--------------------------------------------------------- -/

/-- The concrete generated interpolation table satisfies the asymptotic
PhaseProduct gate-count bound for this fixed `k`. -/
theorem genOpsWithProduct_phaseProduct_gateCount_fixed_k
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (k : ℕ)
    (hk : 1 < k) :
    PhaseProductGateCountBound (Basis := Basis) k hk
      (genOpsWithProduct (k := k) (by omega) (genInterpolationPoints k)) := by

  let hk0 : 0 < k := by omega
  let pts : List Point := genInterpolationPoints k
  let ops : Prog k :=
    genOpsWithProduct (k := k) hk0 pts

  have hcount : phaseProductCount ops = q k  := by
    calc
      phaseProductCount ops = pts.length := by
        simpa [ops] using
          phaseProductCount_genOpsWithProduct
            (k := k) hk0 pts
      _ = q k  := by
        simp [pts, genInterpolationPoints, q]

  have hbalancedWidth :
      ∃ c : ℕ, ∀ x z : ExtReg,
        ExtReg.width x = ExtReg.width z →
        nextSignedWidth x z ops
          ≤ (ExtReg.width x + k - 1) / k + c := by
    simpa [ops] using
      genOpsWithProduct_balanced_nextSignedWidth
        k hk hk0 pts

  have hoverhead :
      ∃ A B : ℕ, ∀ W : ℕ,
        phaseProgramOverhead W ops ≤ A * W + B :=
    phaseProgramOverhead_linear ops

  obtain ⟨C, hC, hbalanced⟩ :=
    balanced_phaseProduct_recurrence_solution
      (Basis := Basis)
      k hk ops
      hcount
      hbalancedWidth
      hoverhead

  have hgrowth :
      ∃ c : ℕ, ∀ x z : ExtReg,
        nextSignedWidth x z ops ≤ phaseInputSize x z + c := by
    simpa [ops] using
      genOpsWithProduct_nextSignedWidth_le_input_add_const
        k hk0 pts

  have hnarrow :
      ∃ d : ℕ, ∀ x z : ExtReg,
        ¬ nextSignedWidth x z ops < phaseInputSize x z →
        min (ExtReg.width x) (ExtReg.width z) ≤ d := by
    simpa [ops] using
      genOpsWithProduct_no_recurse_implies_small_operand
        k hk hk0 pts

  have hbound :
      PhaseProductGateCountBound
        (Basis := Basis) k hk ops :=
    phaseProductGateCountBound_of_balanced_signed_bound
      (Basis := Basis)
      k hk ops
      hcount
      hoverhead
      hgrowth
      hnarrow
      C hC hbalanced

  simpa [ops, pts, hk0] using hbound

/-- Final existence theorem: for every fixed `k > 1`, the generated table is
both program-correct and has the claimed PhaseProduct gate-count bound. -/
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
  let hk0 : 0 < k := by omega
  use (genOpsWithProduct (k:=k) hk0 (genInterpolationPoints k))
  constructor
  · unfold PhaseProductProgramOK
    dsimp
    constructor
    · simpa using genInterpolationPoints_good k
    constructor
    · exact genOpsWithProduct_ProgConsumesPtsSafe (k := k) hk0
        (genInterpolationPoints k)
    constructor
    · exact genOpsWithProduct_returns_to_original (k := k) hk0
        (genInterpolationPoints k)
    · simpa [genInterpolationPoints, q] using
        phaseProductCount_genOpsWithProduct (k := k) hk0
          (genInterpolationPoints k)
  · exact genOpsWithProduct_phaseProduct_gateCount_fixed_k (Basis := Basis) k hk

lemma prog_balanced_nextSignedWidth
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k) :
    ∃ c : ℕ, ∀ x z : ExtReg,
      ExtReg.width x = ExtReg.width z →
      nextSignedWidth x z ops
        ≤
      (ExtReg.width x + k - 1) / k + c := by
  let hk0 : 0 < k := by omega
  let c : ℕ := phaseProgramWidthGrowth ops + 1

  refine ⟨c + (k - 1), ?_⟩
  intro x z hbalanced

  let n := ExtReg.width x

  have hsize :
      phaseInputSize x z = n := by
    simp [phaseInputSize, n, hbalanced]

  have hlimb :
      phaseLimbWidth x z k = n / k := by
    simp [phaseLimbWidth, phaseLimbWidthOfWidth, n, hbalanced]

  have htop :
      nextSignedWidth x z ops
        ≤
      phaseInputSize x z
        - (k - 1) * phaseLimbWidth x z k
        + c := by
    simpa [c] using
      nextSignedWidth_le_topHeavy_add_growth
        hk0 ops x z

  have hceil :
      n - (k - 1) * (n / k)
        ≤
      (n + k - 1) / k + (k - 1) := by
    let d := n / k

    have hdiv :
        k * d ≤ n := by
      simpa [d] using Nat.mul_div_le n k

    have hrem :
        n % k = n - k * d := by
      simpa [d] using
        (Nat.mod_eq_sub_mul_div :
          n % k = n - k * (n / k))

    have hsplit :
        n - (k - 1) * d = n % k + d := by
      simp[hrem]
      simp[Nat.sub_mul];
      have hd_le_kd : d ≤ k * d := by
        nlinarith [hk0, Nat.zero_le d]
      rw [Nat.sub_sub_right n hd_le_kd]
      rw [Nat.sub_add_comm hdiv]



    have hmod :
        n % k ≤ k - 1 := by
      have hlt := Nat.mod_lt n hk0
      omega

    have hdceil :
        d ≤ (n + k - 1) / k := by
      apply Nat.div_le_div_right
      omega

    rw [show n / k = d by rfl, hsplit]
    omega

  calc
    nextSignedWidth x z ops
        ≤
      phaseInputSize x z
        - (k - 1) * phaseLimbWidth x z k
        + c :=
      htop
    _ =
      n - (k - 1) * (n / k) + c := by
      rw [hsize, hlimb]
    _ ≤
      (n + k - 1) / k + (c + (k - 1)) := by
      omega

lemma prog_nextSignedWidth_le_input_add_const
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k) :
    ∃ c : ℕ, ∀ x z : ExtReg,
      nextSignedWidth x z ops
        ≤ phaseInputSize x z + c := by
  let hk0 : 0 < k := by omega

  refine ⟨phaseProgramWidthGrowth ops + 1, ?_⟩
  intro x z

  exact
    le_trans
      (nextSignedWidth_le_topHeavy_add_growth
        hk0 ops x z)
      (Nat.add_le_add_right
        (Nat.sub_le
          (phaseInputSize x z)
          ((k - 1) * phaseLimbWidth x z k))
        (phaseProgramWidthGrowth ops + 1))

lemma prog_no_recurse_implies_small_operand
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k) :
    ∃ d : ℕ, ∀ x z : ExtReg,
      (¬ nextSignedWidth x z ops < phaseInputSize x z) →
      min (ExtReg.width x) (ExtReg.width z) ≤ d := by
  let hk0 : 0 < k := by omega
  let c : ℕ := phaseProgramWidthGrowth ops + 1

  refine ⟨k * c + k, ?_⟩
  intro x z hnot

  let n := phaseInputSize x z
  let m := min (ExtReg.width x) (ExtReg.width z)
  let W := phaseLimbWidth x z k

  have hn_le_next :
      n ≤ nextSignedWidth x z ops := by
    exact Nat.le_of_not_gt hnot

  have hnext :
      nextSignedWidth x z ops
        ≤ n - (k - 1) * W + c := by
    simpa [n, W, c] using
      nextSignedWidth_le_topHeavy_add_growth
        hk0 ops x z

  have hn_le :
      n ≤ n - (k - 1) * W + c :=
    hn_le_next.trans hnext

  have hW :
      W = m / k := by
    unfold W m phaseLimbWidth phaseLimbWidthOfWidth
    by_cases hxz : ExtReg.width x ≤ ExtReg.width z
    · have hdiv :
          ExtReg.width x / k ≤ ExtReg.width z / k :=
        Nat.div_le_div_right hxz
      simp [Nat.min_eq_left hxz, Nat.min_eq_left hdiv]
    · have hzx :
          ExtReg.width z ≤ ExtReg.width x :=
        le_of_not_ge hxz
      have hdiv :
          ExtReg.width z / k ≤ ExtReg.width x / k :=
        Nat.div_le_div_right hzx
      simp [Nat.min_eq_right hzx, Nat.min_eq_right hdiv]

  by_cases hremove : (k - 1) * W ≤ n
  · have hremove_le_c :
        (k - 1) * W ≤ c := by
      omega

    have hW_le_c : W ≤ c := by
      have hkpred : 1 ≤ k - 1 := by omega
      nlinarith [hremove_le_c, hkpred, Nat.zero_le W]

    have hmod :
        m % k ≤ k - 1 := by
      have hlt := Nat.mod_lt m hk0
      omega

    have hsplit :
        m = k * (m / k) + m % k := by
      simpa [Nat.add_comm] using
        (Nat.mod_add_div m k).symm

    change m ≤ k * c + k
    rw [hW] at hW_le_c

    calc
      m = k * (m / k) + m % k := hsplit
      _ ≤ k * c + (k - 1) :=
        Nat.add_le_add
          (Nat.mul_le_mul_left k hW_le_c)
          hmod
      _ ≤ k * c + k := by omega

  · have hn_le_c : n ≤ c := by
      omega

    have hm_le_n : m ≤ n := by
      simp [m, n, phaseInputSize]

    change m ≤ k * c + k
    exact hm_le_n.trans
      (hn_le_c.trans (by
        nlinarith [Nat.zero_le k, Nat.zero_le c]))

theorem phaseProductGateCountBound_of_programOK
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (hops : PhaseProductProgramOK k hk ops) :
    PhaseProductGateCountBound (Basis := Basis) k hk ops := by

  have hcount :
      phaseProductCount ops = q k := by
    unfold PhaseProductProgramOK at hops
    dsimp at hops
    exact hops.2.2.2

  have hbalancedWidth :
      ∃ c : ℕ, ∀ x z : ExtReg,
        ExtReg.width x = ExtReg.width z →
        nextSignedWidth x z ops
          ≤
        (ExtReg.width x + k - 1) / k + c :=
    prog_balanced_nextSignedWidth k hk ops

  have hoverhead :
      ∃ A B : ℕ, ∀ W : ℕ,
        phaseProgramOverhead W ops ≤ A * W + B :=
    phaseProgramOverhead_linear ops

  obtain ⟨C, hC, hbalanced⟩ :=
    balanced_phaseProduct_recurrence_solution
      (Basis := Basis)
      k hk ops
      hcount
      hbalancedWidth
      hoverhead

  have hgrowth :
      ∃ c : ℕ, ∀ x z : ExtReg,
        nextSignedWidth x z ops
          ≤ phaseInputSize x z + c :=
    prog_nextSignedWidth_le_input_add_const k hk ops

  have hnarrow :
      ∃ d : ℕ, ∀ x z : ExtReg,
        ¬ nextSignedWidth x z ops < phaseInputSize x z →
        min (ExtReg.width x) (ExtReg.width z) ≤ d :=
    prog_no_recurse_implies_small_operand k hk ops

  exact
    phaseProductGateCountBound_of_balanced_signed_bound
      (Basis := Basis)
      k hk ops
      hcount
      hoverhead
      hgrowth
      hnarrow
      C hC hbalanced

/-! =========================================================
    Paper-level bounds for CPhaseProduct, QFT, and Shor
========================================================= -/

/--
The paper's final comparison function for Shor:

  n ↦ n^(2 + ε).

The `max 1 n` wrapper makes the rate well behaved at `n = 0`; all asymptotic
statements below are eventually restricted to positive `n`.
-/
noncomputable def shorGateRate (ε : ℝ) (n : ℕ) : ℝ :=
  Real.rpow
    (((max 1 n : ℕ) : ℝ))
    (2 + ε)


/-! ---------------------------------------------------------
    Controlled PhaseProduct
--------------------------------------------------------- -/

/--
For fixed `k` and interpolation program `ops`, controlled PhaseProduct has the
same asymptotic exponent as ordinary PhaseProduct:

  O(n^(log_k(2k - 1))).

The control qubit is required to lie outside both operand registers.
-/
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

/--
Adding one external control does not change the PhaseProduct exponent.
-/
theorem cPhaseProductGateCountBound_of_phaseProduct
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (hPhase :
      PhaseProductGateCountBound
        (Basis := Basis) k hk ops) :
    CPhaseProductGateCountBound
      (Basis := Basis) k hk ops := by
  sorry

/--
Generated interpolation programs satisfy the controlled PhaseProduct bound.
-/
theorem cPhaseProductGateCountBound_of_programOK
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (hops : PhaseProductProgramOK k hk ops) :
    CPhaseProductGateCountBound
      (Basis := Basis) k hk ops := by
  sorry
