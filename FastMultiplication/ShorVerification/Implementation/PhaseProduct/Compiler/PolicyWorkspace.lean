import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Workspace
import FastMultiplication.ShorVerification.Framework.Policy

/-!
# The workspace model under a policy

`Compiler/Workspace.lean` sizes the reserve for a recursion that uses **one**
table at every level: `RecursivePhaseWorkspace.reserveNeed ops wx wz` recurses
on `ops` alone. A policy picks a table by operand width, so the reserve
recurrence has to look the table up at each level, and the lookup is also what
supplies the base case — `choose n = none` is the leaf, alongside the shrink
test that was already there.

Everything here is additive and lives in its own file. `Workspace.lean` has 19
direct importers, so appending to it would rebuild `PhaseProduct/`, `QFT/`,
`Shor/`, `GateCount/`, `Reference/`, `Submission/` and `Emit/` for definitions
nothing uses yet. Nothing in this file is imported by the existing tree; item 4
is where `Plan.lean` starts consuming it.

The four `const` bridges are the point of the file: each policy-level notion
reduces to the fixed-table notion at `constPolicy T`, so the single-table path
keeps its existing statements and proofs unchanged.

| policy | fixed table | bridge |
|---|---|---|
| `Policy.reserveNeed P` | `RecursivePhaseWorkspace.reserveNeed ops` | `reserveNeed_const` |
| `Policy.WorkspaceOK P` | `SignedRecursiveWorkspaceOK ops` | `workspaceOK_const_iff` |
| `Policy.CWorkspaceOK P` | `CSignedRecursiveWorkspaceOK ops` | `cWorkspaceOK_const_iff` |
| `Policy.canonicalStep` | `canonicalSignedStep` | shared lemmas, not a shared definition |

`canonicalStep` duplicates about two hundred lines of arithmetic from
`canonicalSignedStep`. That is deliberate and temporary: the old one has no
`pts` to build a `ToomCookTable` from, so it cannot be *defined* as the
constant-policy case, and it is still what the Shor side calls. Item 4 removes
the duplicate once the Shor side moves over.
-/

namespace Shor.Policy

open Gate Operations ShorLoweringPolicy
open RecursivePhaseWorkspace
  (widthModelX widthModelZ limbWidth nextWidth PhaseSide
   immediateNeed immediateXNeed immediateZNeed)

/-! =========================================================
    The reserve recurrence
========================================================= -/

/--
`RecursivePhaseWorkspace.reserveNeed`, switching tables by band.

Two things end the recursion now instead of one. `P.choose` returning `none`
is the policy's explicit leaf threshold; the shrink test
`Wnext < max wx wz` is the test that was already there, and keeping it is what
makes termination free and stops a non-shrinking band from being a side
condition a submitter has to discharge.
-/
def reserveNeed (P : ShorLoweringPolicy) (wx wz : ℕ) : ℕ × ℕ :=
  match P.choose (max wx wz) with
  | none => (0, 0)
  | some T =>
    let Wnext := nextWidth T.ops wx wz
    if _hrec : Wnext < max wx wz then
      let childNeed := reserveNeed P Wnext Wnext
      (immediateXNeed T.ops wx wz + T.k * childNeed.1,
       immediateZNeed T.ops wx wz + T.k * childNeed.2)
    else
      (0, 0)
termination_by max wx wz
decreasing_by simpa using _hrec

/-- Below the policy's last threshold there is no table, and no reserve. -/
@[simp] theorem reserveNeed_of_choose_none {P : ShorLoweringPolicy} {wx wz : ℕ}
    (hT : P.choose (max wx wz) = none) :
    reserveNeed P wx wz = (0, 0) := by
  rw [reserveNeed, hT]

/-- First projection, exposing the recursive branch for simplification. -/
theorem reserveNeed_fst_of_choose {P : ShorLoweringPolicy} {wx wz : ℕ} {T : ToomCookTable}
    (hT : P.choose (max wx wz) = some T) :
    (reserveNeed P wx wz).1 =
      if _hrec : nextWidth T.ops wx wz < max wx wz then
        immediateXNeed T.ops wx wz
          + T.k * (reserveNeed P (nextWidth T.ops wx wz) (nextWidth T.ops wx wz)).1
      else 0 := by
  rw [reserveNeed, hT]
  dsimp only
  split_ifs with h <;> rfl

/-- Second projection, exposing the recursive branch for simplification. -/
theorem reserveNeed_snd_of_choose {P : ShorLoweringPolicy} {wx wz : ℕ} {T : ToomCookTable}
    (hT : P.choose (max wx wz) = some T) :
    (reserveNeed P wx wz).2 =
      if _hrec : nextWidth T.ops wx wz < max wx wz then
        immediateZNeed T.ops wx wz
          + T.k * (reserveNeed P (nextWidth T.ops wx wz) (nextWidth T.ops wx wz)).2
      else 0 := by
  rw [reserveNeed, hT]
  dsimp only
  split_ifs with h <;> rfl

/-- The constant policy's reserve is the fixed-table reserve: the lookup
succeeds at every width with the same table, so the two recurrences take the
same branch at every level. -/
theorem reserveNeed_const (T : ToomCookTable) (wx wz : ℕ) :
    reserveNeed (constPolicy T) wx wz = RecursivePhaseWorkspace.reserveNeed T.ops wx wz := by
  -- Fuel induction on `max wx wz`, which is the measure both recurrences use.
  suffices h : ∀ n wx wz, max wx wz ≤ n →
      reserveNeed (constPolicy T) wx wz = RecursivePhaseWorkspace.reserveNeed T.ops wx wz from
    h (max wx wz) wx wz le_rfl
  intro n
  induction n with
  | zero =>
    intro wx wz hn
    rw [reserveNeed, constPolicy_choose, RecursivePhaseWorkspace.reserveNeed]
    have : ¬ nextWidth T.ops wx wz < max wx wz := by omega
    simp [this]
  | succ n ih =>
    intro wx wz hn
    rw [reserveNeed, constPolicy_choose, RecursivePhaseWorkspace.reserveNeed]
    by_cases hrec : nextWidth T.ops wx wz < max wx wz
    · have hchild : max (nextWidth T.ops wx wz) (nextWidth T.ops wx wz) ≤ n := by
        simp only [max_self]; omega
      simp only [dif_pos hrec]
      rw [ih _ _ hchild]
    · simp [hrec]

/-! =========================================================
    Static workspace-sufficiency predicates
========================================================= -/

/--
`SignedRecursiveWorkspaceOK` with the policy in place of the single table.
Identical in shape; only the reserve recurrence it quantifies over changes.
-/
structure WorkspaceOK (P : ShorLoweringPolicy) (x z : ExtReg) : Prop where
  /-- The complete owned regions of `x` and `z` do not overlap. -/
  owned_disjoint : ExtReg.OwnedDisjoint x z
  /-- `x.reserve` is large enough for the complete recursive compilation. -/
  x_reserve_sufficient : (reserveNeed P x.width z.width).1 ≤ x.capacity
  /-- `z.reserve` is large enough for the complete recursive compilation. -/
  z_reserve_sufficient : (reserveNeed P x.width z.width).2 ≤ z.capacity

/-- The controlled form: the control qubit must also sit outside both
operands' complete owned regions. -/
structure CWorkspaceOK (P : ShorLoweringPolicy) (ctrl : ℕ) (x z : ExtReg) : Prop
    extends WorkspaceOK P x z where
  /-- The control is outside both operands, workspace included. -/
  control_disjoint : ExtReg.CtrlDisjoint ctrl x z

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

`canonicalSignedStep` proves this inline (`Workspace.lean:623–640`). After this
plan it is needed three times, so it is stated once here. It belongs in
`Workspace.lean`; it is parked here for the same build-time reason the rest of
the file is, and can move home in item 4.
========================================================= -/

/-- The `x` width model reproduces the operand's active width. -/
theorem widthModelX_width (x : ExtReg) : (widthModelX x.width).width = x.width := by
  simp [widthModelX, ExtReg.width, ExtReg.ofReg, regSize, Reg.width, Reg.interval]

/-- The `z` width model reproduces the operand's active width. -/
theorem widthModelZ_width (x z : ExtReg) : (widthModelZ x.width z.width).width = z.width := by
  simp [widthModelZ, ExtReg.width, ExtReg.ofReg, regSize, Reg.width, Reg.interval]

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
      initWidthState (widthModelX x.width) (widthModelZ x.width z.width) k
        = initWidthState x z k := by
    simp only [initWidthState, widthModelX_width, widthModelZ_width,
      show phaseLimbWidth (widthModelX x.width) (widthModelZ x.width z.width) k
        = phaseLimbWidth x z k from limbWidth_eq k x z]
  simp only [nextWidth, nextSignedWidth, scanNeededWidths, hinit]

/-! =========================================================
    Per-child reserve requirements
========================================================= -/

/--
Reserve required by the `i`th child on one operand side, under a policy.
The first summand is consumed by the current compilation level; the second
remains available to the recursive child, and is sized by the *policy's*
recurrence rather than by one table's.
-/
def requiredChildReserve (P : ShorLoweringPolicy) (T : ToomCookTable)
    (side : PhaseSide) (wx wz : ℕ) (i : Fin T.k) : ℕ :=
  let Wphase := limbWidth T.k wx wz
  let Wnext := nextWidth T.ops wx wz
  let childNeed := side.reserveComponent (reserveNeed P Wnext Wnext)
  (Wnext - phaseSplitLogicalWidth (side.width wx wz) Wphase T.k i) + childNeed

/-- Reserve required by the `i`th `x` child. -/
abbrev requiredXChildReserve (P : ShorLoweringPolicy) (T : ToomCookTable)
    (wx wz : ℕ) (i : Fin T.k) : ℕ :=
  requiredChildReserve P T PhaseSide.x wx wz i

/-- Reserve required by the `i`th `z` child. -/
abbrev requiredZChildReserve (P : ShorLoweringPolicy) (T : ToomCookTable)
    (wx wz : ℕ) (i : Fin T.k) : ℕ :=
  requiredChildReserve P T PhaseSide.z wx wz i

/-- Summing child requirements gives immediate need plus one descendant
reserve for each child — the shape the `dif_pos` branch of `reserveNeed`
produces. -/
lemma requiredChildReserve_sum (P : ShorLoweringPolicy) (T : ToomCookTable)
    (side : PhaseSide) (wx wz : ℕ) :
    (List.ofFn (requiredChildReserve P T side wx wz)).sum =
      immediateNeed side T.ops wx wz
        + T.k * side.reserveComponent
            (reserveNeed P (nextWidth T.ops wx wz) (nextWidth T.ops wx wz)) := by
  rw [List.sum_ofFn]
  simp only [requiredChildReserve, immediateNeed]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

/-- Sum formula for `x` child reserve requirements. -/
lemma requiredXChildReserve_sum (P : ShorLoweringPolicy) (T : ToomCookTable) (wx wz : ℕ) :
    (List.ofFn (requiredXChildReserve P T wx wz)).sum =
      immediateXNeed T.ops wx wz
        + T.k * (reserveNeed P (nextWidth T.ops wx wz) (nextWidth T.ops wx wz)).1 :=
  requiredChildReserve_sum P T PhaseSide.x wx wz

/-- Sum formula for `z` child reserve requirements. -/
lemma requiredZChildReserve_sum (P : ShorLoweringPolicy) (T : ToomCookTable) (wx wz : ℕ) :
    (List.ofFn (requiredZChildReserve P T wx wz)).sum =
      immediateZNeed T.ops wx wz
        + T.k * (reserveNeed P (nextWidth T.ops wx wz) (nextWidth T.ops wx wz)).2 :=
  requiredChildReserve_sum P T PhaseSide.z wx wz

/-! =========================================================
    The canonical recursive step, parametrised by the chosen table

`canonicalSignedStep` (`Workspace.lean:607`) with three substitutions and no
new mathematics: the table comes from `hT` rather than from the ambient
parameter, `k`/`ops` become `T.k`/`T.ops`, and the two reserve-fit steps
rewrite with `reserveNeed_fst_of_choose`/`_snd_of_choose` instead of the
unconditional `reserveNeed_fst`/`_snd`. The width-model transfer, the budget
construction and the capacity arithmetic are unchanged.
========================================================= -/

/--
The information produced at one deterministic recursive signed phase-product
step under a policy. `T` is the table the policy chose at this node; the
children are sized by the policy, so they may be compiled with a different
table at the next level.
-/
structure CanonicalStep (P : ShorLoweringPolicy) (T : ToomCookTable) (x z : ExtReg) where
  /-- The chunk layout this level splits its operands into. -/
  layout : Gate.PhaseProductLayout x z T.k
  /-- Every chunk can grow to the width this level needs. -/
  capacity : (initSignedLayoutState layout).CanGrowToNeeds (scanNeededWidths x z T.ops)
  /--
  After current-level growth, every paired child has enough remaining
  workspace for the complete descendant recursion **under the policy** — which
  is what lets the next level pick a different table.
  -/
  childWorkspace :
    let src := initSignedLayoutState layout
    let dst := targetSignedLayoutState src (scanNeededWidths x z T.ops)
    ∀ i : Fin T.k, WorkspaceOK P (dst.xslot i) (dst.zslot i)
  /--
  Every phase-product leaf emitted by this level has the recursive width
  `nextSignedWidth x z T.ops`, which is the width the policy is consulted at
  for the next level.
  -/
  childInputSize :
    let src := initSignedLayoutState layout
    let dst := targetSignedLayoutState src (scanNeededWidths x z T.ops)
    ∀ i : Fin T.k, phaseInputSize (dst.xslot i) (dst.zslot i) = nextSignedWidth x z T.ops

/-- Canonical deterministic construction of one recursive signed
phase-product step under a policy. -/
def canonicalStep
    (P : ShorLoweringPolicy)
    (T : ToomCookTable)
    (x z : ExtReg)
    (hT : P.choose (phaseInputSize x z) = some T)
    (hrec : nextSignedWidth x z T.ops < phaseInputSize x z)
    (hworkspace : WorkspaceOK P x z) :
    CanonicalStep P T x z := by
  let reqX : Fin T.k → ℕ := requiredXChildReserve P T x.width z.width
  let reqZ : Fin T.k → ℕ := requiredZChildReserve P T x.width z.width
  have hkpos : 0 < T.k := by have := T.hk; omega
  -- `phaseInputSize x z` is `max x.width z.width` by definition, which is the
  -- width the reserve recurrence consults the policy at.
  have hT' : P.choose (max x.width z.width) = some T := hT
  have hlimb : limbWidth T.k x.width z.width = phaseLimbWidth x z T.k := limbWidth_eq T.k x z
  have hnext : nextWidth T.ops x.width z.width = nextSignedWidth x z T.ops :=
    nextSignedWidth_eq_widthModel T.ops x z
  -- The recursion guard transfers to the width-model formulation.
  have hrec' : nextWidth T.ops x.width z.width < max x.width z.width := by
    rw [hnext]; exact hrec
  have hxfit : (List.ofFn reqX).sum ≤ x.capacity := by
    show (List.ofFn (requiredXChildReserve P T x.width z.width)).sum ≤ x.capacity
    rw [requiredXChildReserve_sum]
    have hres := hworkspace.x_reserve_sufficient
    rw [reserveNeed_fst_of_choose hT', dif_pos hrec'] at hres
    exact hres
  have hzfit : (List.ofFn reqZ).sum ≤ z.capacity := by
    show (List.ofFn (requiredZChildReserve P T x.width z.width)).sum ≤ z.capacity
    rw [requiredZChildReserve_sum]
    have hres := hworkspace.z_reserve_sufficient
    rw [reserveNeed_snd_of_choose hT', dif_pos hrec'] at hres
    exact hres
  let xBudget : ReserveBudget x T.k := ReserveBudget.ofRequirements hkpos reqX hxfit
  let zBudget : ReserveBudget z T.k := ReserveBudget.ofRequirements hkpos reqZ hzfit
  let xSplit : PhaseSplitLayout x T.k (phaseLimbWidth x z T.k) :=
    PhaseSplitLayout.ofBudget x T.k (phaseLimbWidth x z T.k)
      (phaseLimbWidth_valid_left x z hkpos) xBudget
  let zSplit : PhaseSplitLayout z T.k (phaseLimbWidth x z T.k) :=
    PhaseSplitLayout.ofBudget z T.k (phaseLimbWidth x z T.k)
      (phaseLimbWidth_valid_right x z hkpos) zBudget
  let layout : Gate.PhaseProductLayout x z T.k :=
    { xSplit := xSplit
      zSplit := zSplit
      cross_owned_disjoint := by
        intro i j; unfold ExtReg.OwnedDisjoint
        exact List.disjoint_of_subset_left
          (PhaseSplitLayout.child_owned_subset_parent xSplit i)
          (List.disjoint_of_subset_right
            (PhaseSplitLayout.child_owned_subset_parent zSplit j)
            hworkspace.owned_disjoint) }
  have hreqX_formula (i : Fin T.k) :
      reqX i = (nextSignedWidth x z T.ops - (xSplit.child i).width) +
        (reserveNeed P (nextSignedWidth x z T.ops) (nextSignedWidth x z T.ops)).1 := by
    dsimp [reqX, requiredXChildReserve, requiredChildReserve,
      RecursivePhaseWorkspace.PhaseSide.width,
      RecursivePhaseWorkspace.PhaseSide.reserveComponent]
    rw [hlimb, hnext, xSplit.child_width]
  have hreqZ_formula (i : Fin T.k) :
      reqZ i = (nextSignedWidth x z T.ops - (zSplit.child i).width) +
        (reserveNeed P (nextSignedWidth x z T.ops) (nextSignedWidth x z T.ops)).2 := by
    dsimp [reqZ, requiredZChildReserve, requiredChildReserve,
      RecursivePhaseWorkspace.PhaseSide.width,
      RecursivePhaseWorkspace.PhaseSide.reserveComponent]
    rw [hlimb, hnext, zSplit.child_width]
  have hxChildCapacity (i : Fin T.k) : reqX i ≤ (xSplit.child i).capacity := by
    have h := ReserveBudget.required_le_childReserve_size (parent := x) hkpos reqX hxfit i
    simpa [xSplit, PhaseSplitLayout.ofBudget, PhaseSplitLayout.child,
      ExtReg.withReserve, ExtReg.capacity] using h
  have hzChildCapacity (i : Fin T.k) : reqZ i ≤ (zSplit.child i).capacity := by
    have h := ReserveBudget.required_le_childReserve_size (parent := z) hkpos reqZ hzfit i
    simpa [zSplit, PhaseSplitLayout.ofBudget, PhaseSplitLayout.child,
      ExtReg.withReserve, ExtReg.capacity] using h
  have hcapacity :
      (initSignedLayoutState layout).CanGrowToNeeds (scanNeededWidths x z T.ops) := by
    change LayoutState.CanGrowTo (initSignedLayoutState layout) (nextSignedWidth x z T.ops)
    constructor
    · intro i
      change nextSignedWidth x z T.ops - (xSplit.child i).width ≤ (xSplit.child i).capacity
      have hsize := hxChildCapacity i
      rw [hreqX_formula i] at hsize
      omega
    · intro i
      change nextSignedWidth x z T.ops - (zSplit.child i).width ≤ (zSplit.child i).capacity
      have hsize := hzChildCapacity i
      rw [hreqZ_formula i] at hsize
      omega
  refine
    { layout := layout
      capacity := hcapacity
      childWorkspace := ?_
      childInputSize := ?_ }
  · dsimp only
    intro i
    let src : LayoutState T.k := initSignedLayoutState layout
    let dst : LayoutState T.k := targetSignedLayoutState src (scanNeededWidths x z T.ops)
    have howned : ExtReg.OwnedDisjoint (dst.xslot i) (dst.zslot i) := by
      have hpair := targetSignedLayoutState_owned_disjoint layout (scanNeededWidths x z T.ops)
      simpa [src, dst] using hpair.2.2 i i
    have hxgrow :
        (xSplit.child i).CanGrow (nextSignedWidth x z T.ops - (xSplit.child i).width) := by
      have h := hcapacity.1 i
      change (xSplit.child i).CanGrow (nextSignedWidth x z T.ops - (xSplit.child i).width) at h
      exact h
    have hzgrow :
        (zSplit.child i).CanGrow (nextSignedWidth x z T.ops - (zSplit.child i).width) := by
      have h := hcapacity.2 i
      change (zSplit.child i).CanGrow (nextSignedWidth x z T.ops - (zSplit.child i).width) at h
      exact h
    have hxcapacity :
        (dst.xslot i).capacity
          = (xSplit.child i).capacity - (nextSignedWidth x z T.ops - (xSplit.child i).width) := by
      change
        ((xSplit.child i).grow (nextSignedWidth x z T.ops - (xSplit.child i).width)).capacity
          = (xSplit.child i).capacity - (nextSignedWidth x z T.ops - (xSplit.child i).width)
      exact ExtReg.capacity_grow (xSplit.child i)
        (nextSignedWidth x z T.ops - (xSplit.child i).width) hxgrow
    have hzcapacity :
        (dst.zslot i).capacity
          = (zSplit.child i).capacity - (nextSignedWidth x z T.ops - (zSplit.child i).width) := by
      change
        ((zSplit.child i).grow (nextSignedWidth x z T.ops - (zSplit.child i).width)).capacity
          = (zSplit.child i).capacity - (nextSignedWidth x z T.ops - (zSplit.child i).width)
      exact ExtReg.capacity_grow (zSplit.child i)
        (nextSignedWidth x z T.ops - (zSplit.child i).width) hzgrow
    have hxwidth : (dst.xslot i).width = nextSignedWidth x z T.ops := by
      simpa [src, dst, nextSignedWidth] using
        targetSignedLayoutState_xslot_width_scan layout T.ops i hcapacity
    have hzwidth : (dst.zslot i).width = nextSignedWidth x z T.ops := by
      simpa [src, dst, nextSignedWidth] using
        targetSignedLayoutState_zslot_width_scan layout T.ops i hcapacity
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
    let dst : LayoutState T.k := targetSignedLayoutState src (scanNeededWidths x z T.ops)
    have hxwidth : (dst.xslot i).width = nextSignedWidth x z T.ops := by
      simpa [src, dst, nextSignedWidth] using
        targetSignedLayoutState_xslot_width_scan layout T.ops i hcapacity
    have hzwidth : (dst.zslot i).width = nextSignedWidth x z T.ops := by
      simpa [src, dst, nextSignedWidth] using
        targetSignedLayoutState_zslot_width_scan layout T.ops i hcapacity
    unfold phaseInputSize
    rw [hxwidth, hzwidth, max_self]

end Shor.Policy
