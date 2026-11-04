import ForShor.ShorVerification.Implementation.PhaseProduct.Statement

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

/-- Balanced-input signed bound: equal-width signed inputs are bounded by a
constant times the safe comparison rate. -/
noncomputable def BalancedSignedPhaseProductBound
    {Basis : Type u} [RegEncoding Basis] (k : ℕ) (hk : 1 < k) (ops : Prog k)
    (pts : List Point) (hpts : pts.length = q k) (C : ℝ) : Prop :=
  ∀ (φ : Angle) (x z : ExtReg), SignedRecursiveWorkspaceOK ops x z →
    ExtReg.width x = ExtReg.width z →
    (signedPhaseProductGateCount (Basis := Basis) k hk ops pts hpts φ x z : ℝ)
      ≤ C * phaseProductSafeRate k (ExtReg.width x)

/-- Nonrecursive arithmetic cost of one body operation at common working width
`W`; recursive leaves are counted separately in the recurrence. -/
def phaseArithmeticOpCost {k : ℕ} (W : ℕ) : valid_ops k → ℕ
  | .shiftL _ _ => 0
  | .shiftR _ _ => 0
  | .negate _ => 2 * (W + rippleAdderGateBound W)
  | .addScaled _ _ _ _ => 2 * rippleAdderGateBound W
  | .phaseProduct _ => 0

/-- Total nonrecursive arithmetic overhead of one recursion node at common
working width `W`. -/
def phaseProgramOverhead {k : ℕ} (W : ℕ) (ops : Prog k) : ℕ :=
  ops.foldr (fun op total => phaseArithmeticOpCost W op + total) 0

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
