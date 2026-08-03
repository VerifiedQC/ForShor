import FastMultiplication.ShorVerification.ShorCorrectness

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

/-- Build a PhaseProduct-oriented cost model from a primitive-cost table.  Shifts
and allocation bookkeeping default to zero cost, arithmetic operations are
linear, and direct signed PhaseProduct gates are quadratic base cases. -/
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

/-! =========================================================
    PhaseProduct rates and public hypotheses

This section records the asymptotic comparison functions and the high-level
preconditions used by the final PhaseProduct bounds.  These definitions are
about theorem statements rather than local recursive proof bookkeeping.
========================================================= -/

section PhaseProductStatements

/-- The Toom-Cook PhaseProduct exponent `log_k (2k - 1)`. -/
noncomputable def phaseProductExponent (k : ℕ) : ℝ := Real.log (q k : ℝ) / Real.log (k : ℝ)

/-- The raw comparison function `n ↦ n^(log_k (2k - 1))`. -/
noncomputable def phaseProductGateRate (k n : ℕ) : ℝ := Real.rpow (n : ℝ) (phaseProductExponent k)

/-- The safe comparison function used in recursive estimates, with the input
clamped to at least one so small widths do not create degenerate powers. -/
noncomputable def phaseProductSafeRate (k n : ℕ) : ℝ := Real.rpow (((max 1 n : ℕ) : ℝ)) (phaseProductExponent k)

/-- The public unsigned PhaseProduct input size: the larger of the two source
register widths. -/
def phaseProductInputSize (x z : Reg) : ℕ := max (regSize x) (regSize z)

/-- Final unsigned PhaseProduct asymptotic statement for a fixed `k` and source
program `ops`: above some threshold, the lowered gate count is bounded by
`C * n^(log_k (2k - 1))`. -/
def PhaseProductGateCountBound {Basis : Type u} [RegEncoding Basis] (k : ℕ) (hk : 1 < k) (ops : Prog k) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 1 ≤ n₀ ∧
    ∀ (φ : ℝ) (x z : Reg) (ws : Gate.PhaseProdWorkspace x z)
      (hworkspace : GateWorkspaceOK ops (Gate.PhaseProdUsing φ x z ws)),
      let n := max (regSize x) (regSize z)
      n₀ ≤ n →
      (LowGate.gateCount shorGateCostModel
          (lowerGate (Basis := Basis) k hk ops (Gate.PhaseProdUsing φ x z ws) hworkspace) : ℝ)
        ≤ C * Real.rpow n (phaseProductExponent k)

/-- Static correctness assumptions on the fixed PhaseProduct program: the
interpolation points are good, point consumption is safe, the program preserves
the start state, and it contains exactly `q k` recursive PhaseProduct leaves. -/
def PhaseProductProgramOK (k : ℕ) (hk : 1 < k) (ops : Prog k) : Prop :=
  let pts := genInterpolationPoints k
  let hpts : pts.length = q k := by simp [pts, genInterpolationPoints, q]
  GoodToomCookPoints k pts hpts ∧
  ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops pts ∧
  run? ops State.start_state = some State.start_state ∧
  phaseProductCount ops = q k

end PhaseProductStatements

/-! =========================================================
    Signed PhaseProduct recursion data

The signed lowerer is the internal recursive object used to prove the public
unsigned theorem.  This section defines its measured gate count, its balanced
input bound, and the per-node costs that appear in the recurrence.
========================================================= -/

section SignedPhaseProductRecurrence

open Operations

/-- Gate count of the recursively lowered signed PhaseProduct. -/
noncomputable def signedPhaseProductGateCount
    {Basis : Type u} [RegEncoding Basis]
    (k : ℕ) (hk : 1 < k) (ops : Prog k) (φ : ℝ) (x z : ExtReg)
    (hworkspace : SignedRecursiveWorkspaceOK ops x z) : ℕ :=
  LowGate.gateCount shorGateCostModel (lowerSignedPhaseProdWithWorkspace k hk φ x z ops hworkspace)

/-- Gate count of the recursively lowered controlled signed PhaseProduct. -/
noncomputable def cSignedPhaseProductGateCount
    {Basis : Type u} [RegEncoding Basis]
    (k : ℕ) (hk : 1 < k) (ops : Prog k) (ctrl : ℕ) (φ : ℝ) (x z : ExtReg)
    (hworkspace : CSignedRecursiveWorkspaceOK ops ctrl x z) : ℕ :=
  LowGate.gateCount shorGateCostModel (lowerCSignedPhaseProdWithWorkspace k hk ctrl φ x z ops hworkspace)

/-- Balanced-input signed PhaseProduct bound: equal-width signed inputs are
bounded by a constant times the safe PhaseProduct comparison rate. -/
noncomputable def BalancedSignedPhaseProductBound
    {Basis : Type u} [RegEncoding Basis] (k : ℕ) (hk : 1 < k) (ops : Prog k) (C : ℝ) : Prop :=
  ∀ (φ : ℝ) (x z : ExtReg) (hworkspace : SignedRecursiveWorkspaceOK ops x z),
    ExtReg.width x = ExtReg.width z →
    (signedPhaseProductGateCount (Basis := Basis) k hk ops φ x z hworkspace : ℝ)
      ≤ C * phaseProductSafeRate k (ExtReg.width x)

/-- Nonrecursive arithmetic cost contributed by one annotated PhaseProduct-body
operation at common working width `W`; recursive PhaseProduct leaves are counted
separately in the recurrence. -/
def phaseArithmeticOpCost {k : ℕ} (W : ℕ) : valid_ops k → ℕ
  | .shiftL _ _ => 0
  | .shiftR _ _ => 0
  | .negate _ => 2 * (W + rippleAdderGateBound W)
  | .addScaled _ _ _ _ => 2 * rippleAdderGateBound W
  | .phaseProduct _ => 0

/-- Total nonrecursive arithmetic overhead of one PhaseProduct recursion node at
common working width `W`. -/
def phaseProgramOverhead {k : ℕ} (W : ℕ) (ops : Prog k) : ℕ :=
  ops.foldr (fun op total => phaseArithmeticOpCost W op + total) 0

/-- Additive width growth requested by one source operation while scanning a
fixed PhaseProduct body program. -/
def phaseOpWidthGrowth {k : ℕ} : valid_ops k → ℕ
  | .shiftL _ n => n
  | .shiftR _ _ => 0
  | .negate _ => 1
  | .addScaled _ _ _ shift => shift + 1
  | .phaseProduct _ => 0

/-- Total additive width growth requested by a fixed PhaseProduct body program. -/
def phaseProgramWidthGrowth {k : ℕ} : List (valid_ops k) → ℕ
  | [] => 0
  | op :: ops => phaseOpWidthGrowth op + phaseProgramWidthGrowth ops

/-- A concrete balanced signed PhaseProduct instance bundled with its phase,
registers, equal-width proof, and recursive workspace proof. -/
structure BalancedPhaseProductInstance {k : ℕ} (ops : Prog k) where
  φ : ℝ
  x : ExtReg
  z : ExtReg
  hwidth : ExtReg.width x = ExtReg.width z
  hworkspace : SignedRecursiveWorkspaceOK ops x z

end SignedPhaseProductRecurrence

/-! =========================================================
    Width bookkeeping predicates

This section contains small predicates used by width-soundness and allocation
proofs.  They state that all per-limb widths or all scanned needed widths are
bounded by a common natural number.
========================================================= -/

section WidthBookkeeping

/-- Every `x`- and `z`-slot in a width state is bounded by `B`. -/
def WidthStateBounded {k : ℕ} (st : WidthState k) (B : ℕ) : Prop :=
  ∀ i : Fin k, st.xw i ≤ B ∧ st.zw i ≤ B

/-- Every recorded needed width in a completed scan is bounded by `B`. -/
def NeededWidthsBounded {k : ℕ} (need : NeededWidths k) (B : ℕ) : Prop :=
  ∀ i : Fin k, need.xneed i ≤ B ∧ need.zneed i ≤ B

end WidthBookkeeping

/-! =========================================================
    Controlled PhaseProduct and Shor-level rates

Controlled PhaseProduct bounds share the signed recurrence but measure public
controlled gates.  The separate Shor rate is the coarser `n^(2+ε)` comparison
used when PhaseProduct is embedded in the full Shor circuit.
========================================================= -/

section ControlledAndShorBounds

/-- Coarser Shor-level comparison rate `n^(2 + ε)`, again clamped to nonzero
input width through `max 1 n`. -/
noncomputable def shorGateRate (ε : ℝ) (n : ℕ) : ℝ := Real.rpow (((max 1 n : ℕ) : ℝ)) (2 + ε)

/-- Public controlled PhaseProduct asymptotic statement, using the same
PhaseProduct safe rate but quantifying over the control qubit. -/
def CPhaseProductGateCountBound {Basis : Type u} [RegEncoding Basis] (k : ℕ) (hk : 1 < k) (ops : Prog k) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 1 ≤ n₀ ∧
    ∀ (ctrl : ℕ) (φ : ℝ) (x z : Reg) (ws : Gate.PhaseProdWorkspace x z)
      (hworkspace : GateWorkspaceOK ops (Gate.CPhaseProdUsing ctrl φ x z ws)),
      let n := max (regSize x) (regSize z)
      n₀ ≤ n →
      (LowGate.gateCount shorGateCostModel
          (lowerGate (Basis := Basis) k hk ops (Gate.CPhaseProdUsing ctrl φ x z ws) hworkspace) : ℝ)
        ≤ C * phaseProductSafeRate k n

end ControlledAndShorBounds

/-! =========================================================
    Exact-QFT gate-count definitions

The exact QFT recurrence uses PhaseProduct between the two halves of the register
plus a final radix reversal.  This section names the relevant sizes, subregisters,
and gate counts so the QFT gate-count proof can stay readable.
========================================================= -/

section QFTGateCounts

/-- Exact-QFT asymptotic statement for a fixed reserve program: sufficiently
large registers lower with cost bounded by the PhaseProduct safe rate. -/
def QFTGateCountBound {Basis : Type u} [RegEncoding Basis] (k : ℕ) (hk : 1 < k) (ops : Prog k) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 1 ≤ n₀ ∧
    ∀ (r : ExtReg) (hworkspace : QFTReserveOK ops r),
      n₀ ≤ r.width →
      (LowGate.gateCount shorGateCostModel (lowerQFT k hk ops r hworkspace) : ℝ)
        ≤ C * phaseProductSafeRate k r.width

/-- Width of the left half in a QFT split. -/
def qftHalfWidth (r : Reg) : ℕ := splitM r

/-- Left subregister used by one QFT recursion split. -/
def qftLeftReg (r : Reg) : Reg := leftReg r

/-- Right subregister used by one QFT recursion split. -/
def qftRightReg (r : Reg) : Reg := rightReg r

/-- Gate count of the recursively lowered exact QFT on an extended register. -/
noncomputable def loweredQFTGateCount
    {Basis : Type u} [RegEncoding Basis]
    (k : ℕ) (hk : 1 < k) (ops : Prog k) (r : ExtReg)
    (hworkspace : QFTReserveOK ops r) : ℕ :=
  LowGate.gateCount shorGateCostModel (lowerQFT k hk ops r hworkspace)

/-- Gate count of the PhaseProduct joining the two halves of one exact-QFT
recursion node. -/
noncomputable def qftSplitPhaseGateCount
    {Basis : Type u} [RegEncoding Basis]
    (k : ℕ) (hk : 1 < k) (ops : Prog k) (r : Reg)
    (ws : Gate.PhaseProdWorkspace (qftLeftReg r) (qftRightReg r))
    (hworkspace : GateWorkspaceOK ops (Gate.PhaseProdUsing (qftPhi (regSize r)) (qftLeftReg r) (qftRightReg r) ws)) : ℕ :=
  LowGate.gateCount shorGateCostModel
    (lowerGate (Basis := Basis) k hk ops
      (Gate.PhaseProdUsing (qftPhi (regSize r)) (qftLeftReg r) (qftRightReg r) ws) hworkspace)

/-- Gate count of the final radix reversal at one exact-QFT recursion node. -/
def qftSplitRadixGateCount (r : Reg) : ℕ :=
  LowGate.gateCount shorGateCostModel (LowGate.RadixReverse r (qftHalfWidth r))

end QFTGateCounts

end Shor
