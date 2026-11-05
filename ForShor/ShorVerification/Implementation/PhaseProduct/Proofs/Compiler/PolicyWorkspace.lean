import ForShor.ShorVerification.Implementation.PhaseProduct.Statement
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.Workspace
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.Widths
import ForShor.ShorVerification.Framework.Policy

/-!
# The workspace model under a policy

`Statement.lean`'s fixed-table model sizes the reserve for a recursion that uses **one**
table at every level: `RecursivePhaseWorkspace.reserveNeed ops wx wz` recurses
on `ops` alone. A policy picks a table by operand width, so the reserve
recurrence has to look the table up at each level, and the lookup is also what
supplies the base case — `choose n = none` is the leaf, alongside the shrink
test that was already there.

This file is separate from `Workspace.lean` because that file has many
direct importers and these definitions sit above it; `Plan.lean`,
`PlanBuilders.lean`, `Statement.lean` and `QFT/Statement.lean`
import this one.

The `const` bridges are the point of the file: each policy-level notion
reduces to the fixed-table notion at `constPolicy T`, so the single-table
statements keep their existing form.

| policy | fixed table | bridge |
|---|---|---|
| `Policy.reserveNeed P` | `RecursivePhaseWorkspace.reserveNeed ops` | `reserveNeed_const` |
| `Policy.WorkspaceOK P` | `SignedRecursiveWorkspaceOK ops` | `workspaceOK_const_iff` |
| `Policy.CWorkspaceOK P` | `CSignedRecursiveWorkspaceOK ops` | `cWorkspaceOK_const_iff` |

`Policy.canonicalStep` is the canonical recursive step; it is the only one,
and every lowering plan is built with it. It is plain data; `canonicalStep_spec`
proves the facts the correctness proofs need about it whenever the policy
picked its table, the table shrinks the operands, and the workspace fits.
-/

/-! ---------------------------------------------------------
    The workspace model under a policy (moved from `Statement.lean`)
--------------------------------------------------------- -/

namespace Shor.Policy

open Gate Operations ShorLoweringPolicy
open RecursivePhaseWorkspace
  (limbWidth nextWidth PhaseSide
   immediateNeed immediateXNeed immediateZNeed
   nextWidthBy immediateNeedBy immediateXNeedBy immediateZNeedBy)

/-! =========================================================
    The reserve recurrence
========================================================= -/

/-- First projection, exposing the recursive branch for simplification. -/
theorem reserveNeed_fst_of_choose {P : ShorLoweringPolicy} {wx wz : ℕ} {T : ToomCookTable}
    (hT : P.choose (max wx wz) = some T) :
    (reserveNeed P wx wz).1 =
      if _hrec : nextWidthBy P.widthRule T.ops wx wz < max wx wz then
        immediateXNeedBy P.widthRule T.ops wx wz
          + T.k * (reserveNeed P (nextWidthBy P.widthRule T.ops wx wz) (nextWidthBy P.widthRule T.ops wx wz)).1
      else 0 := by
  rw [reserveNeed, hT]
  dsimp only
  split_ifs with h <;> rfl

/-- Second projection, exposing the recursive branch for simplification. -/
theorem reserveNeed_snd_of_choose {P : ShorLoweringPolicy} {wx wz : ℕ} {T : ToomCookTable}
    (hT : P.choose (max wx wz) = some T) :
    (reserveNeed P wx wz).2 =
      if _hrec : nextWidthBy P.widthRule T.ops wx wz < max wx wz then
        immediateZNeedBy P.widthRule T.ops wx wz
          + T.k * (reserveNeed P (nextWidthBy P.widthRule T.ops wx wz) (nextWidthBy P.widthRule T.ops wx wz)).2
      else 0 := by
  rw [reserveNeed, hT]
  dsimp only
  split_ifs with h <;> rfl

/-! =========================================================
    Static workspace-sufficiency predicates
========================================================= -/

/-- Bridge: at the constant policy, the policy predicate *is* the fixed-table
predicate. This is what lets the existing single-table path keep its
statements. -/
theorem workspaceOK_const_iff {T : ToomCookTable} {x z : ExtReg} :
    WorkspaceOK (constPolicy T) x z ↔ SignedRecursiveWorkspaceOK T.ops x z := by
  -- `rw`, not `simp`: `RecursivePhaseWorkspace.reserveNeed_fst` is a `@[simp]`
  -- lemma that unfolds one level of the recurrence, so `simp` chases it down
  -- the whole recursion and hits the recursion-depth limit.
  constructor
  · intro h
    refine ⟨h.owned_disjoint, ?_, ?_⟩
    · have hx := h.x_reserve_sufficient; rwa [reserveNeed_const] at hx
    · have hz := h.z_reserve_sufficient; rwa [reserveNeed_const] at hz
  · intro h
    refine ⟨h.owned_disjoint, ?_, ?_⟩
    · have hx := h.x_reserve_sufficient; rwa [← reserveNeed_const] at hx
    · have hz := h.z_reserve_sufficient; rwa [← reserveNeed_const] at hz

/-- The controlled bridge. -/
theorem cWorkspaceOK_const_iff {T : ToomCookTable} {ctrl : ℕ} {x z : ExtReg} :
    CWorkspaceOK (constPolicy T) ctrl x z ↔ CSignedRecursiveWorkspaceOK T.ops ctrl x z := by
  constructor
  · intro h
    exact ⟨workspaceOK_const_iff.mp h.toWorkspaceOK, h.control_disjoint⟩
  · intro h
    exact ⟨workspaceOK_const_iff.mpr h.toSignedRecursiveWorkspaceOK, h.control_disjoint⟩

/-! =========================================================
    The width-model transfer, as a standalone lemma

Needed three times below, so it is stated once here.
========================================================= -/

/-- The `x` width model reproduces the operand's active width. -/
theorem widthModelX_width (x : ExtReg) : (ExtReg.ofReg (Reg.interval 0 x.width)).width = x.width := by
  simp [ExtReg.width, ExtReg.ofReg, regSize, Reg.width, Reg.interval]

/-- The `z` width model reproduces the operand's active width. -/
theorem widthModelZ_width (x z : ExtReg) : (ExtReg.ofReg (Reg.interval x.width z.width)).width = z.width := by
  simp [ExtReg.width, ExtReg.ofReg, regSize, Reg.width, Reg.interval]

/-- The width-only limb width agrees with the one computed on the real
operands. -/
theorem limbWidth_eq (k : ℕ) (x z : ExtReg) :
    limbWidth k x.width z.width = phaseLimbWidth x z k := by
  simp only [limbWidth, phaseLimbWidth, widthModelX_width, widthModelZ_width]

/-- The width-model registers reproduce the operands' active widths, so the
width-only recursion `nextWidth` agrees with `nextSignedWidth` on the real
operands. -/
theorem nextSignedWidth_eq_widthModel {k : ℕ} (ops : Prog k) (x z : ExtReg) :
    nextWidth ops x.width z.width = nextSignedWidth x z ops := by
  have hinit :
      initWidthState (ExtReg.ofReg (Reg.interval 0 x.width)) (ExtReg.ofReg (Reg.interval x.width z.width)) k
        = initWidthState x z k := by
    simp only [initWidthState, widthModelX_width, widthModelZ_width,
      show phaseLimbWidth (ExtReg.ofReg (Reg.interval 0 x.width)) (ExtReg.ofReg (Reg.interval x.width z.width)) k
        = phaseLimbWidth x z k from limbWidth_eq k x z]
  simp only [nextWidth, nextSignedWidth, scanNeededWidths, hinit]

/-! =========================================================
    Per-child reserve requirements
========================================================= -/

/-- `nextSignedWidth_eq_widthModel` under either width rule. -/
theorem nextSignedWidthBy_eq_widthModel (R : WidthRule) {k : ℕ} (ops : Prog k) (x z : ExtReg) :
    nextWidthBy R ops x.width z.width = nextSignedWidthBy R x z ops := by
  cases R
  · exact nextSignedWidth_eq_widthModel ops x z
  · simp only [nextWidthBy, nextSignedWidthBy, neededWidthsBy, widthModelX_width,
      widthModelZ_width]

/-- Summing child requirements gives immediate need plus one descendant
reserve for each child — the shape the `dite_eq_left` branch of `reserveNeed`
produces. -/
lemma requiredChildReserve_sum (P : ShorLoweringPolicy) (T : ToomCookTable)
    (side : PhaseSide) (wx wz : ℕ) :
    (List.ofFn (requiredChildReserve P T side wx wz)).sum =
      immediateNeedBy P.widthRule side T.ops wx wz
        + T.k * side.reserveComponent
            (reserveNeed P (nextWidthBy P.widthRule T.ops wx wz) (nextWidthBy P.widthRule T.ops wx wz)) := by
  rw [List.sum_ofFn]
  simp only [requiredChildReserve, immediateNeedBy]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

/-- Sum formula for `x` child reserve requirements. -/
lemma requiredXChildReserve_sum (P : ShorLoweringPolicy) (T : ToomCookTable) (wx wz : ℕ) :
    (List.ofFn (requiredChildReserve P T PhaseSide.x wx wz)).sum =
      immediateXNeedBy P.widthRule T.ops wx wz
        + T.k * (reserveNeed P (nextWidthBy P.widthRule T.ops wx wz) (nextWidthBy P.widthRule T.ops wx wz)).1 :=
  requiredChildReserve_sum P T PhaseSide.x wx wz

/-- Sum formula for `z` child reserve requirements. -/
lemma requiredZChildReserve_sum (P : ShorLoweringPolicy) (T : ToomCookTable) (wx wz : ℕ) :
    (List.ofFn (requiredChildReserve P T PhaseSide.z wx wz)).sum =
      immediateZNeedBy P.widthRule T.ops wx wz
        + T.k * (reserveNeed P (nextWidthBy P.widthRule T.ops wx wz) (nextWidthBy P.widthRule T.ops wx wz)).2 :=
  requiredChildReserve_sum P T PhaseSide.z wx wz

end Shor.Policy

namespace Shor.Policy

open Gate Operations ShorLoweringPolicy
open RecursivePhaseWorkspace
  (limbWidth nextWidth PhaseSide
   immediateNeed immediateXNeed immediateZNeed
   nextWidthBy immediateNeedBy immediateXNeedBy immediateZNeedBy)

/-! =========================================================
    The reserve recurrence
========================================================= -/

/-- Below the policy's last threshold there is no table, and no reserve. -/
@[simp] theorem reserveNeed_of_choose_none {P : ShorLoweringPolicy} {wx wz : ℕ}
    (hT : P.choose (max wx wz) = none) :
    reserveNeed P wx wz = (0, 0) := by
  rw [reserveNeed, hT]

/-! =========================================================
    The canonical step's invariants
========================================================= -/

/-- What the proofs need to know about one recursive step: its layout is valid,
every chunk can grow to the width this level needs, every child again has
enough workspace under the policy, and every child has the recursive width. -/
structure StepSpec (P : ShorLoweringPolicy) (T : ToomCookTable) (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z T.k) : Prop where
  /-- The layout's splits partition the operands' reserves and are disjoint. -/
  valid : layout.Valid
  /-- Every chunk can grow to the width this level needs. -/
  capacity : (initSignedLayoutState layout).CanGrowToNeeds (neededWidthsBy P.widthRule x z T.ops)
  /--
  After current-level growth, every paired child has enough remaining
  workspace for the complete descendant recursion **under the policy** — which
  is what lets the next level pick a different table.
  -/
  childWorkspace :
    let src := initSignedLayoutState layout
    let dst := targetSignedLayoutState src (neededWidthsBy P.widthRule x z T.ops)
    ∀ i : Fin T.k, WorkspaceOK P (dst.xslot i) (dst.zslot i)
  /--
  Every phase-product leaf emitted by this level has the recursive width
  `nextSignedWidthBy P.widthRule x z T.ops`, which is the width the policy is consulted at
  for the next level.
  -/
  childInputSize :
    let src := initSignedLayoutState layout
    let dst := targetSignedLayoutState src (neededWidthsBy P.widthRule x z T.ops)
    ∀ i : Fin T.k, phaseInputSize (dst.xslot i) (dst.zslot i) = nextSignedWidthBy P.widthRule x z T.ops

/-- The canonical step satisfies its spec whenever the policy chose `T` at
this width, `T` shrinks the operands, and the workspace fits. -/
theorem canonicalStep_spec
    {P : ShorLoweringPolicy}
    {T : ToomCookTable}
    {x z : ExtReg}
    (hT : P.choose (phaseInputSize x z) = some T)
    (hrec : nextSignedWidthBy P.widthRule x z T.ops < phaseInputSize x z)
    (hworkspace : WorkspaceOK P x z) :
    StepSpec P T x z (canonicalStep P T x z) := by
  let reqX : Fin T.k → ℕ := (requiredChildReserve P T PhaseSide.x x.width z.width)
  let reqZ : Fin T.k → ℕ := (requiredChildReserve P T PhaseSide.z x.width z.width)
  have hkpos : 0 < T.k := by have := T.hk; omega
  -- `phaseInputSize x z` is `max x.width z.width` by definition, which is the
  -- width the reserve recurrence consults the policy at.
  have hT' : P.choose (max x.width z.width) = some T := hT
  have hlimb : limbWidth T.k x.width z.width = phaseLimbWidth x z T.k := limbWidth_eq T.k x z
  have hnext : nextWidthBy P.widthRule T.ops x.width z.width = nextSignedWidthBy P.widthRule x z T.ops :=
    nextSignedWidthBy_eq_widthModel P.widthRule T.ops x z
  -- The recursion guard transfers to the width-model formulation.
  have hrec' : nextWidthBy P.widthRule T.ops x.width z.width < max x.width z.width := by
    rw [hnext]; exact hrec
  have hxfit : (List.ofFn reqX).sum ≤ x.capacity := by
    show (List.ofFn (requiredChildReserve P T PhaseSide.x x.width z.width)).sum ≤ x.capacity
    rw [requiredXChildReserve_sum]
    have hres := hworkspace.x_reserve_sufficient
    rw [reserveNeed_fst_of_choose hT', dite_eq_left hrec'] at hres
    exact hres
  have hzfit : (List.ofFn reqZ).sum ≤ z.capacity := by
    show (List.ofFn (requiredChildReserve P T PhaseSide.z x.width z.width)).sum ≤ z.capacity
    rw [requiredZChildReserve_sum]
    have hres := hworkspace.z_reserve_sufficient
    rw [reserveNeed_snd_of_choose hT', dite_eq_left hrec'] at hres
    exact hres
  let xBudget : ReserveBudget x T.k := ReserveBudget.ofRequirements hkpos reqX
  let zBudget : ReserveBudget z T.k := ReserveBudget.ofRequirements hkpos reqZ
  let xSplit : PhaseSplitLayout x T.k (phaseLimbWidth x z T.k) :=
    PhaseSplitLayout.ofBudget x T.k (phaseLimbWidth x z T.k) xBudget
  let zSplit : PhaseSplitLayout z T.k (phaseLimbWidth x z T.k) :=
    PhaseSplitLayout.ofBudget z T.k (phaseLimbWidth x z T.k) zBudget
  let layout : Gate.PhaseProductLayout x z T.k := canonicalStep P T x z
  have hxSplit : layout.xSplit = xSplit := rfl
  have hzSplit : layout.zSplit = zSplit := rfl
  have hvx : xSplit.Valid :=
    PhaseSplitLayout.ofBudget_valid (phaseLimbWidth_valid_left x z hkpos) xBudget
      (ReserveBudget.fillSlack_sum hkpos x.capacity reqX hxfit)
  have hvz : zSplit.Valid :=
    PhaseSplitLayout.ofBudget_valid (phaseLimbWidth_valid_right x z hkpos) zBudget
      (ReserveBudget.fillSlack_sum hkpos z.capacity reqZ hzfit)
  have hvalid : layout.Valid :=
    { xSplit := hvx
      zSplit := hvz
      cross_owned_disjoint := by
        intro i j; unfold ExtReg.OwnedDisjoint
        exact List.disjoint_of_subset_left
          (PhaseSplitLayout.child_owned_subset_parent hvx i)
          (List.disjoint_of_subset_right
            (PhaseSplitLayout.child_owned_subset_parent hvz j)
            hworkspace.owned_disjoint) }
  have hreqX_formula (i : Fin T.k) :
      reqX i = (nextSignedWidthBy P.widthRule x z T.ops - (xSplit.child i).width) +
        (reserveNeed P (nextSignedWidthBy P.widthRule x z T.ops) (nextSignedWidthBy P.widthRule x z T.ops)).1 := by
    dsimp [reqX, requiredChildReserve,
      RecursivePhaseWorkspace.PhaseSide.width,
      RecursivePhaseWorkspace.PhaseSide.reserveComponent]
    rw [hlimb, hnext, xSplit.child_width (phaseLimbWidth_valid_left x z hkpos)]
  have hreqZ_formula (i : Fin T.k) :
      reqZ i = (nextSignedWidthBy P.widthRule x z T.ops - (zSplit.child i).width) +
        (reserveNeed P (nextSignedWidthBy P.widthRule x z T.ops) (nextSignedWidthBy P.widthRule x z T.ops)).2 := by
    dsimp [reqZ, requiredChildReserve,
      RecursivePhaseWorkspace.PhaseSide.width,
      RecursivePhaseWorkspace.PhaseSide.reserveComponent]
    rw [hlimb, hnext, zSplit.child_width (phaseLimbWidth_valid_right x z hkpos)]
  have hxChildCapacity (i : Fin T.k) : reqX i ≤ (xSplit.child i).capacity := by
    have h := ReserveBudget.required_le_childReserve_size (parent := x) hkpos reqX hxfit i
    simpa [xSplit, xBudget, PhaseSplitLayout.ofBudget, PhaseSplitLayout.child,
      ExtReg.withReserve, ExtReg.capacity] using h
  have hzChildCapacity (i : Fin T.k) : reqZ i ≤ (zSplit.child i).capacity := by
    have h := ReserveBudget.required_le_childReserve_size (parent := z) hkpos reqZ hzfit i
    simpa [zSplit, zBudget, PhaseSplitLayout.ofBudget, PhaseSplitLayout.child,
      ExtReg.withReserve, ExtReg.capacity] using h
  have hcapacity :
      (initSignedLayoutState layout).CanGrowToNeeds (neededWidthsBy P.widthRule x z T.ops) := by
    change LayoutState.CanGrowTo (initSignedLayoutState layout) (nextSignedWidthBy P.widthRule x z T.ops)
    constructor
    · intro i
      change nextSignedWidthBy P.widthRule x z T.ops - (xSplit.child i).width ≤ (xSplit.child i).capacity
      have hsize := hxChildCapacity i
      rw [hreqX_formula i] at hsize
      omega
    · intro i
      change nextSignedWidthBy P.widthRule x z T.ops - (zSplit.child i).width ≤ (zSplit.child i).capacity
      have hsize := hzChildCapacity i
      rw [hreqZ_formula i] at hsize
      omega
  refine
    { valid := hvalid
      capacity := hcapacity
      childWorkspace := ?_
      childInputSize := ?_ }
  · dsimp only
    intro i
    let src : LayoutState T.k := initSignedLayoutState layout
    let dst : LayoutState T.k := targetSignedLayoutState src (neededWidthsBy P.widthRule x z T.ops)
    have howned : ExtReg.OwnedDisjoint (dst.xslot i) (dst.zslot i) := by
      have hpair := targetSignedLayoutState_owned_disjoint hvalid (neededWidthsBy P.widthRule x z T.ops)
      simpa [src, dst] using hpair.2.2 i i
    have hxgrow :
        (xSplit.child i).CanGrow (nextSignedWidthBy P.widthRule x z T.ops - (xSplit.child i).width) := by
      have h := hcapacity.1 i
      change (xSplit.child i).CanGrow (nextSignedWidthBy P.widthRule x z T.ops - (xSplit.child i).width) at h
      exact h
    have hzgrow :
        (zSplit.child i).CanGrow (nextSignedWidthBy P.widthRule x z T.ops - (zSplit.child i).width) := by
      have h := hcapacity.2 i
      change (zSplit.child i).CanGrow (nextSignedWidthBy P.widthRule x z T.ops - (zSplit.child i).width) at h
      exact h
    have hxcapacity :
        (dst.xslot i).capacity
          = (xSplit.child i).capacity - (nextSignedWidthBy P.widthRule x z T.ops - (xSplit.child i).width) := by
      change
        ((xSplit.child i).grow (nextSignedWidthBy P.widthRule x z T.ops - (xSplit.child i).width)).capacity
          = (xSplit.child i).capacity - (nextSignedWidthBy P.widthRule x z T.ops - (xSplit.child i).width)
      exact ExtReg.capacity_grow (xSplit.child i)
        (nextSignedWidthBy P.widthRule x z T.ops - (xSplit.child i).width) hxgrow
    have hzcapacity :
        (dst.zslot i).capacity
          = (zSplit.child i).capacity - (nextSignedWidthBy P.widthRule x z T.ops - (zSplit.child i).width) := by
      change
        ((zSplit.child i).grow (nextSignedWidthBy P.widthRule x z T.ops - (zSplit.child i).width)).capacity
          = (zSplit.child i).capacity - (nextSignedWidthBy P.widthRule x z T.ops - (zSplit.child i).width)
      exact ExtReg.capacity_grow (zSplit.child i)
        (nextSignedWidthBy P.widthRule x z T.ops - (zSplit.child i).width) hzgrow
    have hxwidth : (dst.xslot i).width = nextSignedWidthBy P.widthRule x z T.ops := by
      simpa [src, dst, nextSignedWidthBy] using
        targetSignedLayoutState_xslot_width_by P.widthRule layout T.ops i hcapacity
    have hzwidth : (dst.zslot i).width = nextSignedWidthBy P.widthRule x z T.ops := by
      simpa [src, dst, nextSignedWidthBy] using
        targetSignedLayoutState_zslot_width_by P.widthRule layout T.ops i hcapacity
    refine
      { owned_disjoint := howned
        x_reserve_sufficient := ?_
        z_reserve_sufficient := ?_ }
    · rw [hxwidth, hzwidth, hxcapacity]
      have hsize := hxChildCapacity i
      rw [hreqX_formula i] at hsize
      omega
    · rw [hxwidth, hzwidth, hzcapacity]
      have hsize := hzChildCapacity i
      rw [hreqZ_formula i] at hsize
      omega
  · dsimp only
    intro i
    let src : LayoutState T.k := initSignedLayoutState layout
    let dst : LayoutState T.k := targetSignedLayoutState src (neededWidthsBy P.widthRule x z T.ops)
    have hxwidth : (dst.xslot i).width = nextSignedWidthBy P.widthRule x z T.ops := by
      simpa [src, dst, nextSignedWidthBy] using
        targetSignedLayoutState_xslot_width_by P.widthRule layout T.ops i hcapacity
    have hzwidth : (dst.zslot i).width = nextSignedWidthBy P.widthRule x z T.ops := by
      simpa [src, dst, nextSignedWidthBy] using
        targetSignedLayoutState_zslot_width_by P.widthRule layout T.ops i hcapacity
    unfold phaseInputSize
    rw [hxwidth, hzwidth, max_self]

end Shor.Policy
