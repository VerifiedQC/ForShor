import FastMultiplication.ShorVerification.ShorCorrectness
import FastMultiplication.ShorVerification.Framework.Semantics.CostModel

namespace Shor

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
