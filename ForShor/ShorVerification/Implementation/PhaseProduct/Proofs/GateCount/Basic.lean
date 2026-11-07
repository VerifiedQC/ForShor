import ForShor.ShorVerification.Implementation.PhaseProduct.Statement
import ForShor.ShorVerification.Framework.Gatecount.PolicyModel

/-!
# Phase-product gate count: the recursion data

The objects the gate-count proof is phrased in: the balanced-input bound the
recursion is solved for, the per-node arithmetic cost and width growth of a
table's program, and width-bookkeeping predicates. Also the bridges from a
`ShorLoweringSetup`, an admissible table and an admissible policy to
`PhaseProductProgramOK`.
-/

namespace Shor
open Operations

/-! ## Negation methods: the cost model and the width bound -/

/-- The bound `negateGateBoundFor nm` as a function of the width alone. -/
def negateWidthBoundFor : NegationMethod → ℕ → ℕ
  | .oneQubit, W => 34 * W + 1
  | .scratch, W => W + rippleAdderGateBound W

theorem negateGateBoundFor_eq (nm : NegationMethod) (r : ExtReg) :
    negateGateBoundFor nm r = negateWidthBoundFor nm (ExtReg.width r) := by
  cases nm <;> rfl

/-- The pre-swap width bound is the complement plus one ripple adder, verbatim. -/
theorem negateWidthBoundFor_scratch (W : ℕ) :
    negateWidthBoundFor .scratch W = W + rippleAdderGateBound W := rfl

/-- The cost model of the Shor lowering under a negation method: `shorGateCostModel` is the `oneQubit` one. -/
def shorGateCostModelFor (nm : NegationMethod) : LowGateCostModel :=
  (shorGateResourceModelFor nm).toCostModel

@[simp] theorem shorGateCostModelFor_oneQubit : shorGateCostModelFor .oneQubit = shorGateCostModel := rfl

/-- The cost model a policy is priced under, in terms of its negation method. -/
theorem ShorLoweringPolicy.resourceModel_toCostModel (P : ShorLoweringPolicy) :
    P.resourceModel.toCostModel = shorGateCostModelFor P.negation := rfl

/-! ## The comparison rates -/

/-- The Toom-Cook phase-product exponent `log_k (2k - 1)`, the exponent in
`SignedPhaseProductGateCountBound`. -/
noncomputable def phaseProductExponent (k : ℕ) : ℝ := Real.log (q k : ℝ) / Real.log (k : ℝ)

/-- The comparison function `n ↦ n^(log_k (2k - 1))`. -/
noncomputable def phaseProductGateRate (k n : ℕ) : ℝ := Real.rpow (n : ℝ) (phaseProductExponent k)

/-- The comparison function with its input clamped to at least one, so small
widths do not create degenerate powers. -/
noncomputable def phaseProductSafeRate (k n : ℕ) : ℝ :=
  Real.rpow (((max 1 n : ℕ) : ℝ)) (phaseProductExponent k)

/-! ## The program conditions -/

/-- Every submission satisfies the program conditions: a setup's `good`,
`consumes` and `returns` fields are C1–C4. -/
theorem ShorLoweringSetup.programOK (s : ShorLoweringSetup) :
    PhaseProductProgramOK s.k s.hk s.pts s.hpts s.ops :=
  ⟨s.good, s.consumes, s.returns⟩

/-- `ToomCookTable.Admissible` (`Framework/Policy.lean`) and
`PhaseProductProgramOK` are the same three conjuncts, stated twice so that the
specification does not import the resource estimate. The `k > 0` proofs the
two spellings feed to `ProgConsumesPtsSafe` differ only up to proof
irrelevance. -/
theorem ToomCookTable.admissible_iff_programOK (T : ToomCookTable) :
    T.Admissible ↔ PhaseProductProgramOK T.k T.hk T.pts T.hpts T.ops :=
  Iff.rfl

/-- An admissible policy hands each node the program conditions for whatever
table it chose. -/
theorem ShorLoweringPolicy.programOK_of_choose {P : ShorLoweringPolicy}
    (hP : P.Admissible) {n : ℕ} {T : ToomCookTable} (h : P.choose n = some T) :
    PhaseProductProgramOK T.k T.hk T.pts T.hpts T.ops :=
  (ToomCookTable.admissible_iff_programOK T).mp (hP.of_choose h)

/-! ## The signed recursion -/

section SignedPhaseProductRecurrence

/-- Gate count of the lowered signed phase product for a fixed table, under a negation method.
`signedPhaseProductGateCount` is the `oneQubit` one. -/
noncomputable def signedPhaseProductGateCountFor (nm : NegationMethod)
    {Basis : Type u} [RegEncoding Basis]
    (k : ℕ) (hk : 1 < k) (ops : Prog k) (pts : List Point) (hpts : pts.length = q k)
    (φ : Angle) (x z : ExtReg) : ℕ :=
  LowGate.gateCount (shorGateCostModelFor nm)
    (lowerSignedPhaseProd k hk φ x z ops pts hpts)

/-- Gate count of the lowered controlled signed phase product for a fixed table, under a negation method.
`cSignedPhaseProductGateCount` is the `oneQubit` one. -/
noncomputable def cSignedPhaseProductGateCountFor (nm : NegationMethod)
    {Basis : Type u} [RegEncoding Basis]
    (k : ℕ) (hk : 1 < k) (ops : Prog k) (pts : List Point) (hpts : pts.length = q k)
    (ctrl : ℕ) (φ : Angle) (x z : ExtReg) : ℕ :=
  LowGate.gateCount (shorGateCostModelFor nm)
    (lowerCSignedPhaseProd k hk ctrl φ x z ops pts hpts)

theorem signedPhaseProductGateCountFor_oneQubit
    {Basis : Type u} [RegEncoding Basis]
    (k : ℕ) (hk : 1 < k) (ops : Prog k) (pts : List Point) (hpts : pts.length = q k)
    (φ : Angle) (x z : ExtReg) :
    signedPhaseProductGateCountFor .oneQubit (Basis := Basis) k hk ops pts hpts φ x z
      = signedPhaseProductGateCount (Basis := Basis) k hk ops pts hpts φ x z := rfl

theorem cSignedPhaseProductGateCountFor_oneQubit
    {Basis : Type u} [RegEncoding Basis]
    (k : ℕ) (hk : 1 < k) (ops : Prog k) (pts : List Point) (hpts : pts.length = q k)
    (ctrl : ℕ) (φ : Angle) (x z : ExtReg) :
    cSignedPhaseProductGateCountFor .oneQubit (Basis := Basis) k hk ops pts hpts ctrl φ x z
      = cSignedPhaseProductGateCount (Basis := Basis) k hk ops pts hpts ctrl φ x z := rfl

/-- Balanced-input signed bound: equal-width signed inputs are bounded by a
constant times the safe comparison rate. -/
noncomputable def BalancedSignedPhaseProductBound
    {Basis : Type u} [RegEncoding Basis] (k : ℕ) (hk : 1 < k) (ops : Prog k)
    (pts : List Point) (hpts : pts.length = q k) (C : ℝ) : Prop :=
  ∀ (φ : Angle) (x z : ExtReg), SignedRecursiveWorkspaceOK ops x z →
    ExtReg.width x = ExtReg.width z →
    (signedPhaseProductGateCount (Basis := Basis) k hk ops pts hpts φ x z : ℝ)
      ≤ C * phaseProductSafeRate k (ExtReg.width x)

/-- Balanced-input signed bound under a negation method. -/
noncomputable def BalancedSignedPhaseProductBoundFor (nm : NegationMethod)
    {Basis : Type u} [RegEncoding Basis] (k : ℕ) (hk : 1 < k) (ops : Prog k)
    (pts : List Point) (hpts : pts.length = q k) (C : ℝ) : Prop :=
  ∀ (φ : Angle) (x z : ExtReg), SignedRecursiveWorkspaceOK ops x z →
    ExtReg.width x = ExtReg.width z →
    (signedPhaseProductGateCountFor nm (Basis := Basis) k hk ops pts hpts φ x z : ℝ)
      ≤ C * phaseProductSafeRate k (ExtReg.width x)

theorem BalancedSignedPhaseProductBoundFor_oneQubit
    {Basis : Type u} [RegEncoding Basis] (k : ℕ) (hk : 1 < k) (ops : Prog k)
    (pts : List Point) (hpts : pts.length = q k) (C : ℝ) :
    BalancedSignedPhaseProductBoundFor .oneQubit (Basis := Basis) k hk ops pts hpts C
      = BalancedSignedPhaseProductBound (Basis := Basis) k hk ops pts hpts C := rfl

/-- Nonrecursive arithmetic cost of one body operation at common working width
`W`; recursive leaves are counted separately in the recurrence. This is the `oneQubit` charge; see
`phaseArithmeticOpCostFor` for the other negation method. -/
def phaseArithmeticOpCost {k : ℕ} (W : ℕ) : valid_ops k → ℕ
  | .shiftL _ _ => 0
  | .shiftR _ _ => 0
  | .negate _ => 2 * (34 * W + 1)
  | .addScaled _ _ _ _ => 2 * rippleAdderGateBound W
  | .phaseProduct _ => 0

/-- Nonrecursive arithmetic cost of one body operation at common working width `W`, under a negation
method (a negation is charged twice, as the phase product negates both an `x` and a `z` slot). -/
def phaseArithmeticOpCostFor (nm : NegationMethod) {k : ℕ} (W : ℕ) : valid_ops k → ℕ
  | .shiftL _ _ => 0
  | .shiftR _ _ => 0
  | .negate _ => 2 * negateWidthBoundFor nm W
  | .addScaled _ _ _ _ => 2 * rippleAdderGateBound W
  | .phaseProduct _ => 0

/-- One body operation's nonrecursive cost has slope `phaseOpSlope nm` in the working width: `68` for
`oneQubit` (a negation is charged `2 (34 W + 1)`), `20` for `scratch` (the pre-swap value, a negation is
charged `2 (W + 9 W + 2)`). -/
def phaseOpSlope : NegationMethod → ℕ
  | .oneQubit => 68
  | .scratch => 20

theorem phaseArithmeticOpCostFor_le (nm : NegationMethod) {k : ℕ} (W : ℕ) (op : valid_ops k) :
    phaseArithmeticOpCostFor nm W op ≤ phaseOpSlope nm * W + 4 := by
  cases nm <;> cases op <;>
    simp [phaseArithmeticOpCostFor, negateWidthBoundFor, phaseOpSlope, rippleAdderGateBound] <;> omega

/-- Oracle: under `scratch` a negation node is charged exactly what it was before swap 001. -/
theorem phaseArithmeticOpCostFor_scratch_negate {k : ℕ} (W : ℕ) (j : Fin k) :
    phaseArithmeticOpCostFor .scratch W (.negate j) = 2 * (W + rippleAdderGateBound W) := rfl

theorem phaseArithmeticOpCostFor_oneQubit {k : ℕ} (W : ℕ) (op : valid_ops k) :
    phaseArithmeticOpCostFor .oneQubit W op = phaseArithmeticOpCost W op := by
  cases op <;> rfl

/-- Total nonrecursive arithmetic overhead of one recursion node at common
working width `W`. -/
def phaseProgramOverhead {k : ℕ} (W : ℕ) (ops : Prog k) : ℕ :=
  ops.foldr (fun op total => phaseArithmeticOpCost W op + total) 0

/-- Total nonrecursive arithmetic overhead of one recursion node at common working width `W`, under a
negation method. -/
def phaseProgramOverheadFor (nm : NegationMethod) {k : ℕ} (W : ℕ) (ops : Prog k) : ℕ :=
  ops.foldr (fun op total => phaseArithmeticOpCostFor nm W op + total) 0

theorem phaseProgramOverheadFor_oneQubit {k : ℕ} (W : ℕ) (ops : Prog k) :
    phaseProgramOverheadFor .oneQubit W ops = phaseProgramOverhead W ops := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
      simp only [phaseProgramOverheadFor, phaseProgramOverhead, List.foldr_cons] at ih ⊢
      rw [ih, phaseArithmeticOpCostFor_oneQubit]

/-- Additive width growth one source operation requests. -/
def phaseOpWidthGrowth {k : ℕ} : valid_ops k → ℕ
  | .shiftL _ n => n
  | .shiftR _ _ => 0
  | .negate _ => 1
  | .addScaled _ _ _ shift => shift + 1
  | .phaseProduct _ => 0

/-- Total additive width growth a program requests. -/
def phaseProgramWidthGrowth {k : ℕ} : List (valid_ops k) → ℕ
  | [] => 0
  | op :: ops => phaseOpWidthGrowth op + phaseProgramWidthGrowth ops

/-- A balanced signed instance: phase, equal-width registers, and their
recursive workspace. -/
structure BalancedPhaseProductInstance {k : ℕ} (ops : Prog k) where
  φ : Angle
  x : ExtReg
  z : ExtReg
  hwidth : ExtReg.width x = ExtReg.width z
  hworkspace : SignedRecursiveWorkspaceOK ops x z

end SignedPhaseProductRecurrence

/-! ## Width bookkeeping -/

section WidthBookkeeping

/-- Every `x`- and `z`-slot in a width state is bounded by `B`. -/
def WidthStateBounded {k : ℕ} (st : WidthState k) (B : ℕ) : Prop :=
  ∀ i : Fin k, st.xw i ≤ B ∧ st.zw i ≤ B

/-- Every recorded needed width in a completed scan is bounded by `B`. -/
def NeededWidthsBounded {k : ℕ} (need : NeededWidths k) (B : ℕ) : Prop :=
  ∀ i : Fin k, need.xneed i ≤ B ∧ need.zneed i ≤ B

end WidthBookkeeping

end Shor
