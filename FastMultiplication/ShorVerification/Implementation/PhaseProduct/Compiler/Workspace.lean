import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Compile

/-!
# Phase-Product Compiler: Workspace

The recursive-workspace size model (`RecursivePhaseWorkspace.reserveNeed` and
friends), the static workspace-sufficiency predicates
(`SignedRecursiveWorkspaceOK`, `CSignedRecursiveWorkspaceOK`), the concrete
reserve-budget construction (`PhaseSplitLayout.ofBudget`,
`ReserveBudget.ofRequirements`), and the canonical deterministic recursive
step (`CanonicalSignedStep`, `canonicalSignedStep`). Split out of
`DefsCore.lean`. This is the top of the `Compiler/*` chain: everything that
used to import `DefsCore` now imports this file.
-/

namespace Shor
open Gate
open Operations
open scoped BigOperators

/-! ---------------------------------------------------------
    Workspace preservation and reserve-budget construction
--------------------------------------------------------- -/

/-- Growing every slot to the target width preserves control disjointness. -/
theorem controlDisjoint_target
    {x z : ExtReg}
    {k : ℕ}
    (layout : Gate.PhaseProductLayout x z k)
    (ctrl : ℕ)
    (need : NeededWidths k)
    (hctrl : layout.ControlDisjoint ctrl) :
    let src := initSignedLayoutState layout
    let dst := targetSignedLayoutState src need
    (∀ i, ctrl ∉ (dst.xslot i).ownedQubits) ∧
    (∀ i, ctrl ∉ (dst.zslot i).ownedQubits) := by
  intro src dst
  obtain ⟨hx, hz⟩ := hctrl
  refine ⟨?_, ?_⟩
  · intro i
    simpa [dst, targetSignedLayoutState, growExtRegTo, src, initSignedLayoutState, ExtReg.ownedQubits_grow] using hx i
  · intro i
    simpa [dst, targetSignedLayoutState, growExtRegTo, src, initSignedLayoutState, ExtReg.ownedQubits_grow] using hz i

/-- Growing an extendable register only moves qubits from reserve to active; ownership is unchanged. -/

@[simp]
theorem ExtReg.ownedQubits_grow
    (e : ExtReg)
    (n : ℕ) :
    (e.grow n).ownedQubits = e.ownedQubits := by
  simp [ExtReg.ownedQubits, ExtReg.grow, Reg.append, ExtReg.newBits, Reg.take, ExtReg.remainingReserve, Reg.drop, List.append_assoc, List.take_append_drop]

/-- Target widening preserves pairwise owned-disjointness of all slots. -/
theorem targetSignedLayoutState_owned_disjoint
    {x z : ExtReg}
    {k : ℕ}
    (layout : Gate.PhaseProductLayout x z k)
    (need : NeededWidths k) :
    (targetSignedLayoutState
      (initSignedLayoutState layout)
      need).OwnedPairwiseDisjoint := by
  obtain ⟨hx, hz, hxz⟩ := initSignedLayoutState_owned_disjoint layout
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    simpa [targetSignedLayoutState, growExtRegTo, ExtReg.OwnedDisjoint, ExtReg.ownedQubits_grow] using hx i j hij
  · intro i j hij
    simpa [targetSignedLayoutState, growExtRegTo, ExtReg.OwnedDisjoint, ExtReg.ownedQubits_grow] using hz i j hij
  · intro i j
    simpa [targetSignedLayoutState, growExtRegTo, ExtReg.OwnedDisjoint, ExtReg.ownedQubits_grow] using hxz i j

/-- Consecutive variable-width slices reconstruct the corresponding prefix. -/
private theorem flatten_consecutive_slices
    (L : List ℕ) :
    ∀ (k : ℕ) (size : Fin k → ℕ),
      (List.ofFn fun i =>
        List.take (size i)
          (List.drop
            (((List.ofFn size).take i.1).sum)
            L)).flatten
        =
      List.take ((List.ofFn size).sum) L := by
  intro k
  induction k with
  | zero =>
      intro size
      simp
  | succ k ih =>
      intro size
      let size' : Fin k → ℕ :=
        fun i => size i.castSucc
      have htake (i : Fin k) :
          (List.ofFn size).take i.1
            =
              (List.ofFn size').take i.1 := by
        rw [List.ofFn_succ', List.concat_eq_append]
        simp [size', List.take_append_of_le_length]
      have htakeLast :
          (List.ofFn size).take k
            =
          List.ofFn size' := by
        rw [List.ofFn_succ', List.concat_eq_append]
        simp [size']
      have hsum :
          (List.ofFn size).sum
            =
          (List.ofFn size').sum
            + size (Fin.last k) := by
        rw [List.ofFn_succ']
        simp [size']
      rw [List.ofFn_succ', List.concat_eq_append, List.flatten_append]
      simp only [Fin.val_castSucc, List.flatten_cons, List.flatten_nil, List.append_nil]
      have hlastVal : (Fin.last k).1 = k := rfl
      rw [hlastVal]
      simp_rw [htake]
      change
        (List.ofFn fun i : Fin k =>
          List.take (size' i)
            (List.drop
              (((List.ofFn size').take i.1).sum)
              L)).flatten
          ++
        List.take (size (Fin.last k))
          (List.drop
            (((List.ofFn size).take k).sum)
            L)
          =
        List.take ((List.ofFn size).sum) L
      rw [ih size', htakeLast, hsum, List.take_add]

theorem ReserveBudget.flatten_childReserve
    {parent : ExtReg}
    {k : ℕ}
    (budget : ReserveBudget parent k) :
    (List.ofFn fun i =>
      (budget.childReserve i).qubits).flatten
      =
    parent.reserve.qubits := by
  simp only [ReserveBudget.childReserve, ReserveBudget.offset, Reg.take, Reg.drop]
  rw [flatten_consecutive_slices]
  rw [budget.total]
  simp [ExtReg.capacity, regSize, Reg.width]

private theorem phaseChunkActive_sublist
    (parent : ExtReg)
    (k W : ℕ)
    (i : Fin k) :
    (phaseChunkActive parent k W i).qubits.Sublist
      parent.active.qubits := by
  simp only [phaseChunkActive, phaseChunkStart, Reg.take, Reg.drop]
  exact (List.take_sublist _ _).trans (List.drop_sublist _ _)

private theorem ReserveBudget.childReserve_sublist
    {parent : ExtReg}
    {k : ℕ}
    (budget : ReserveBudget parent k)
    (i : Fin k) :
    (budget.childReserve i).qubits.Sublist
      parent.reserve.qubits := by
  simp only [ReserveBudget.childReserve, ReserveBudget.offset, Reg.take, Reg.drop]
  exact
    (List.take_sublist _ _).trans
      (List.drop_sublist _ _)

private theorem phaseChunkActive_childReserve_disjoint
    {parent : ExtReg}
    {k W : ℕ}
    (budget : ReserveBudget parent k)
    (i j : Fin k) :
    List.Disjoint
      (phaseChunkActive parent k W i).qubits
      (budget.childReserve j).qubits := by
  have hactive :=
    phaseChunkActive_sublist parent k W i
  have hreserve :=
    budget.childReserve_sublist j
  have hparent :
      parent.active.qubits.Disjoint
        parent.reserve.qubits := by
    simpa [Disjoint] using
      parent.active_reserve_disjoint
  exact
    List.disjoint_of_subset_left hactive.subset
      (List.disjoint_of_subset_right
        hreserve.subset
        hparent)

private theorem pairwise_disjoint_ofFn
    {α : Type*}
    {k : ℕ}
    {f : Fin k → List α}
    (hpair : (List.ofFn f).Pairwise List.Disjoint)
    {i j : Fin k}
    (hij : i ≠ j) :
    (f i).Disjoint (f j) := by
  have hval : i.1 ≠ j.1 := by
    intro h
    apply hij
    exact Fin.ext h
  rcases Nat.lt_or_gt_of_ne hval with hijlt | hjilt
  ·
    have h := (List.pairwise_iff_getElem.mp hpair)  i.1 j.1 (by simp) (by simp) hijlt
    simpa using h
  ·
    have h :=
      (List.pairwise_iff_getElem.mp hpair)
        j.1
        i.1
        (by simp)
        (by simp)
        hjilt
    simpa using h.symm

/-- Build an abstract split layout from concrete active slices and a reserve budget. -/
def PhaseSplitLayout.ofBudget
    (parent : ExtReg)
    (k W : ℕ)
    (hvalid : ValidPhaseSplit parent k W)
    (budget : ReserveBudget parent k) :
    PhaseSplitLayout parent k W :=
  {
    valid := hvalid
    reserve := budget.childReserve
    active_reserve_disjoint := by
      intro i
      simpa [Disjoint] using
        phaseChunkActive_childReserve_disjoint
          (W := W)
          budget i i
    reserve_partition := by
      exact budget.flatten_childReserve
    child_owned_pairwise := by
      intro i j hij
      have hAA :
          List.Disjoint
            (phaseChunkActive parent k W i).qubits
            (phaseChunkActive parent k W j).qubits := by
        simpa [Disjoint] using
          phaseChunkActive_pairwise_disjoint
            parent k W hvalid hij
      have hAR :
          List.Disjoint
            (phaseChunkActive parent k W i).qubits
            (budget.childReserve j).qubits :=
        phaseChunkActive_childReserve_disjoint
          (W := W)
          budget i j
      have hRA :
          List.Disjoint
            (budget.childReserve i).qubits
            (phaseChunkActive parent k W j).qubits :=
        (phaseChunkActive_childReserve_disjoint
          (W := W)
          budget j i).symm
      have hflatNodup :
          ((List.ofFn fun t : Fin k =>
            (budget.childReserve t).qubits).flatten).Nodup := by
        rw [budget.flatten_childReserve]
        exact parent.reserve.nodup
      have hreservePairwise :
          (List.ofFn fun t : Fin k =>
            (budget.childReserve t).qubits).Pairwise
              List.Disjoint :=
        (List.nodup_flatten.mp hflatNodup).2
      have hRR :
          List.Disjoint
            (budget.childReserve i).qubits
            (budget.childReserve j).qubits :=
        pairwise_disjoint_ofFn
          (f := fun t : Fin k =>
            (budget.childReserve t).qubits)
          hreservePairwise
          hij
      intro q hqLeft hqRight
      rcases List.mem_append.mp hqLeft with hqAi | hqRi
      · rcases List.mem_append.mp hqRight with hqAj | hqRj
        · exact hAA hqAi hqAj
        · exact hAR hqAi hqRj
      · rcases List.mem_append.mp hqRight with hqAj | hqRj
        · exact hRA hqRi hqAj
        · exact hRR hqRi hqRj
  }

/-! =========================================================
    Section 4: Recursive workspace size model
    The recursive compiler needs reserve space for current-level chunk growth and
    for each descendant phase-product call. These width-only definitions compute
    conservative reserve requirements from logical operand widths.
========================================================= -/

namespace RecursivePhaseWorkspace

/--
A canonical extendable register used only for width calculations.
It has the requested active width and no reserve. Its physical qubit locations
are irrelevant because `scanNeededWidths` and `phaseLimbWidth` depend only on
the active widths.
-/
def widthModelX (wx : ℕ) : ExtReg := ExtReg.ofReg (Reg.interval 0 wx)

/--
A second width-model register placed after `widthModelX`, so the two model
active registers are physically disjoint.
-/
def widthModelZ (wx wz : ℕ) : ExtReg := ExtReg.ofReg (Reg.interval wx wz)

/-- The phase-limb width determined by a pair of logical operand widths. -/
def limbWidth (k wx wz : ℕ) : ℕ := phaseLimbWidth (widthModelX wx) (widthModelZ wx wz) k

/--
The common width required after compiling one level of the operation program.
-/
def nextWidth {k : ℕ} (ops : Prog k) (wx wz : ℕ) : ℕ := nextSignedWidth (widthModelX wx) (widthModelZ wx wz) ops

/--
The two operand sides of a recursive phase-product workspace.
Several reserve formulas are identical except for whether they inspect the
`x` width/component or the `z` width/component. This index lets the common
formula be stated once.
-/
inductive PhaseSide where
  | x
  | z

namespace PhaseSide

/-- Select the logical width for one operand side. -/
def width
    (side : PhaseSide)
    (wx wz : ℕ) :
    ℕ :=
  match side with
  | .x => wx
  | .z => wz

/-- Select the corresponding component from an `(x, z)` reserve pair. -/
def reserveComponent
    (side : PhaseSide)
    (need : ℕ × ℕ) :
    ℕ :=
  match side with
  | .x => need.1
  | .z => need.2

end PhaseSide

/--
The reserve needed merely to grow all chunks on one side at the current
level.
This does not include the reserves needed by descendant recursive calls.
-/
def immediateNeed
    {k : ℕ}
    (side : PhaseSide)
    (ops : Prog k)
    (wx wz : ℕ) :
    ℕ :=
  let Wphase := limbWidth k wx wz
  let Wnext := nextWidth ops wx wz
  ∑ i : Fin k,
    (Wnext - phaseSplitLogicalWidth (side.width wx wz) Wphase k i)

/-- The reserve needed merely to grow all `x` chunks at this level. -/
abbrev immediateXNeed
    {k : ℕ}
    (ops : Prog k)
    (wx wz : ℕ) :
    ℕ :=
  immediateNeed PhaseSide.x ops wx wz

/-- The reserve needed merely to grow all `z` chunks at this level. -/
abbrev immediateZNeed
    {k : ℕ}
    (ops : Prog k)
    (wx wz : ℕ) :
    ℕ :=
  immediateNeed PhaseSide.z ops wx wz

/--
A conservative reserve requirement for the complete recursive compilation.
The result is:
* `.1`: reserve required on the `x` side;
* `.2`: reserve required on the `z` side.
When the next recursive width is not smaller, lowering uses the base
phase-product implementation, so no reserve is required.
Otherwise, every one of the `k` chunks receives:
1. enough reserve for its immediate growth;
2. enough remaining reserve for a complete descendant recursive call.
This bound is intentionally conservative: it provisions recursive workspace
for every child, even if a particular operation program does not invoke a
phase product on every child.
-/
def reserveNeed
    {k : ℕ}
    (ops : Prog k)
    (wx wz : ℕ) :
    ℕ × ℕ :=
  let Wnext := nextWidth ops wx wz
  if _hrec : Wnext < max wx wz then
    let childNeed :=
      reserveNeed ops Wnext Wnext
    (
      immediateXNeed ops wx wz + k * childNeed.1,
      immediateZNeed ops wx wz + k * childNeed.2
    )
  else
    (0, 0)
termination_by max wx wz
decreasing_by
  simpa using _hrec
/-- First projection of `reserveNeed`, exposing the recursive branch for simplification. -/
@[simp] theorem reserveNeed_fst
    {k : ℕ}
    (ops : Prog k)
    (wx wz : ℕ) :
    (reserveNeed ops wx wz).1 =
      if _hrec : nextWidth ops wx wz < max wx wz then
        immediateXNeed ops wx wz + k * (reserveNeed ops (nextWidth ops wx wz) (nextWidth ops wx wz)).1
      else 0 := by
  rw [reserveNeed]
  split_ifs with h <;> rfl
/-- Second projection of `reserveNeed`, exposing the recursive branch for simplification. -/
@[simp] theorem reserveNeed_snd
    {k : ℕ}
    (ops : Prog k)
    (wx wz : ℕ) :
    (reserveNeed ops wx wz).2 =
      if _hrec : nextWidth ops wx wz < max wx wz then
        immediateZNeed ops wx wz + k * (reserveNeed ops (nextWidth ops wx wz) (nextWidth ops wx wz)).2
      else 0 := by
  rw [reserveNeed]
  split_ifs with h <;> rfl

end RecursivePhaseWorkspace

/-! =========================================================
    Section 5: Static workspace-sufficiency predicates
========================================================= -/

/--
Static workspace requirements for an uncontrolled recursive signed phase
product.
This predicate contains only physical-layout and capacity information. It
does not refer to a basis state or quantum state.
-/
structure SignedRecursiveWorkspaceOK
    {k : ℕ}
    (ops : Prog k)
    (x z : ExtReg) :
    Prop where
  /-- The complete owned regions of `x` and `z` do not overlap. -/
  owned_disjoint : ExtReg.OwnedDisjoint x z
  /-- `x.reserve` is large enough for the complete recursive compilation. -/
  x_reserve_sufficient :
    (RecursivePhaseWorkspace.reserveNeed ops x.width z.width).1 ≤ x.capacity
  /-- `z.reserve` is large enough for the complete recursive compilation. -/
  z_reserve_sufficient :
    (RecursivePhaseWorkspace.reserveNeed ops x.width z.width).2 ≤ z.capacity

/-! =========================================================
    Section 6: Canonical recursive step construction
    The canonical step builds a phase-product layout whose child chunks have
    exactly the next recursive width and enough reserve for all descendant calls.
========================================================= -/

namespace RecursivePhaseWorkspace

/--
Reserve required by the `i`th child on one operand side.
The first summand is consumed by the current compilation level. The second
summand remains available to the recursive child.
-/
def requiredChildReserve
    {k : ℕ}
    (side : PhaseSide)
    (ops : Prog k)
    (wx wz : ℕ)
    (i : Fin k) : ℕ :=
  let Wphase := limbWidth k wx wz
  let Wnext := nextWidth ops wx wz
  let childNeed := side.reserveComponent (reserveNeed ops Wnext Wnext)
  (Wnext - phaseSplitLogicalWidth (side.width wx wz) Wphase k i) + childNeed

/-- Reserve required by the `i`th `x` child. -/
abbrev requiredXChildReserve
    {k : ℕ}
    (ops : Prog k)
    (wx wz : ℕ)
    (i : Fin k) : ℕ :=
  requiredChildReserve PhaseSide.x ops wx wz i

/-- Reserve required by the `i`th `z` child. -/
abbrev requiredZChildReserve
    {k : ℕ}
    (ops : Prog k)
    (wx wz : ℕ)
    (i : Fin k) : ℕ :=
  requiredChildReserve PhaseSide.z ops wx wz i

/-- Summing child requirements gives immediate need plus one descendant reserve for each child. -/
lemma requiredChildReserve_sum
    {k : ℕ}
    (side : PhaseSide)
    (ops : Prog k)
    (wx wz : ℕ) :
    (List.ofFn (requiredChildReserve side ops wx wz)).sum =
    immediateNeed side ops wx wz + k * side.reserveComponent (reserveNeed ops (nextWidth ops wx wz) (nextWidth ops wx wz)) := by
  rw [List.sum_ofFn]
  simp only [requiredChildReserve, immediateNeed]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

/-- Sum formula for `x` child reserve requirements. -/
lemma requiredXChildReserve_sum
    {k : ℕ}
    (ops : Prog k)
    (wx wz : ℕ) :
    (List.ofFn (requiredXChildReserve ops wx wz)).sum =
    immediateXNeed ops wx wz + k * (reserveNeed ops (nextWidth ops wx wz) (nextWidth ops wx wz)).1 := by
  exact requiredChildReserve_sum (side := PhaseSide.x) ops wx wz

/-- Sum formula for `z` child reserve requirements. -/
lemma requiredZChildReserve_sum
    {k : ℕ}
    (ops : Prog k)
    (wx wz : ℕ) :
    (List.ofFn (requiredZChildReserve ops wx wz)).sum =
    immediateZNeed ops wx wz + k * (reserveNeed ops (nextWidth ops wx wz) (nextWidth ops wx wz)).2 := by
  exact requiredChildReserve_sum (side := PhaseSide.z) ops wx wz

end RecursivePhaseWorkspace

namespace ReserveBudget

/-- Last child index, used as the deterministic recipient for reserve slack. -/
def topIndex {k : ℕ} (hk : 0 < k) : Fin k := ⟨k - 1, by omega⟩

/-- Add all unused parent reserve to the top child while keeping other child requirements fixed. -/
def fillSlack
    {k : ℕ}
    (hk : 0 < k)
    (capacity : ℕ)
    (required : Fin k → ℕ) :
    Fin k → ℕ :=
  let top := topIndex hk
  let used := (List.ofFn required).sum
  Function.update
    required
    top
    (required top + (capacity - used))

/-- The slack-filled child reserve sizes sum exactly to the parent capacity. -/
lemma fillSlack_sum
    {k : ℕ}
    (hk : 0 < k)
    (capacity : ℕ)
    (required : Fin k → ℕ)
    (hfit :
      (List.ofFn required).sum ≤ capacity) :
    (List.ofFn
      (fillSlack hk capacity required)).sum
      =
    capacity := by
  have hused : (List.ofFn required).sum = ∑ x : Fin k, required x := List.sum_ofFn
  simp only [fillSlack, List.sum_ofFn]
  rw [Finset.sum_update_of_mem (Finset.mem_univ (topIndex hk)),
    ← Finset.erase_eq]
  have hAT : required (topIndex hk) + ∑ x ∈ Finset.univ.erase (topIndex hk), required x = ∑ x : Fin k, required x :=
    Finset.add_sum_erase _ _ (Finset.mem_univ _)
  have hSle : ∑ x : Fin k, required x ≤ capacity := by
    rw [← hused]; exact hfit
  omega

/-- Every child receives at least its required reserve after slack filling. -/
lemma required_le_fillSlack
    {k : ℕ}
    (hk : 0 < k)
    (capacity : ℕ)
    (required : Fin k → ℕ)
    (i : Fin k) :
    required i ≤ fillSlack hk capacity required i := by
  simp only [fillSlack, Function.update_apply]
  by_cases h : i = topIndex hk
  · rw [if_pos h, h]; exact Nat.le_add_right _ _
  · rw [if_neg h]

/-- Build a concrete reserve budget from per-child requirements that fit in the parent reserve. -/
def ofRequirements
    {parent : ExtReg}
    {k : ℕ}
    (hk : 0 < k)
    (required : Fin k → ℕ)
    (hfit : (List.ofFn required).sum ≤ parent.capacity) :
    ReserveBudget parent k :=
  {
    size := fillSlack hk parent.capacity required
    total := by exact fillSlack_sum hk parent.capacity required hfit
  }

/-- Each concrete child-reserve slice has at least the requested size. -/
theorem required_le_childReserve_size
    {parent : ExtReg}
    {k : ℕ}
    (hk : 0 < k)
    (required : Fin k → ℕ)
    (hfit :
      (List.ofFn required).sum
        ≤ parent.capacity)
    (i : Fin k) :
    required i ≤
      regSize ((ofRequirements hk required hfit).childReserve i) := by
  set budget := ofRequirements hk required hfit with hbudget
  -- `budget.size i` is exactly the slack-filled requirement, ≥ `required i`.
  have h1 : required i ≤ budget.size i := by
    show required i ≤ fillSlack hk parent.capacity required i
    exact required_le_fillSlack hk parent.capacity required i
  -- The `i`th slice starts at `offset i` and has room for `size i`.
  have hbound : budget.offset i + budget.size i ≤ parent.capacity := by
    have hi : i.1 < (List.ofFn budget.size).length := by rw [List.length_ofFn]; exact i.2
    have hstep : ((List.ofFn budget.size).take (i.1 + 1)).sum = budget.offset i + budget.size i := by
      unfold ReserveBudget.offset; rw [List.sum_take_succ _ _ hi, List.getElem_ofFn]
    have hle : ((List.ofFn budget.size).take (i.1 + 1)).sum ≤ (List.ofFn budget.size).sum := by
      conv_rhs =>
        rw [← List.take_append_drop (i.1 + 1) (List.ofFn budget.size)]
      rw [List.sum_append]; exact Nat.le_add_right _ _
    have htot : (List.ofFn budget.size).sum = parent.capacity := budget.total
    omega
  -- Hence the physical `take` does not truncate: the slice has size `size i`.
  have h2 : regSize (budget.childReserve i) = budget.size i := by
    have hcap : parent.reserve.qubits.length = parent.capacity := rfl
    simp only [regSize, Reg.width, ReserveBudget.childReserve, Reg.take,
      Reg.drop, List.length_take, List.length_drop]
    omega
  rw [h2]; exact h1

end ReserveBudget

/--
The information produced at one deterministic recursive signed phase-product
step.
-/
structure CanonicalSignedStep
    {k : ℕ}
    (ops : Prog k)
    (x z : ExtReg) where
  layout : Gate.PhaseProductLayout x z k
  capacity : (initSignedLayoutState layout).CanGrowToNeeds (scanNeededWidths x z ops)
  /--
  After current-level growth, every paired child has enough remaining
  workspace for the complete descendant recursion.
  -/
  childWorkspace :
    let src :=
      initSignedLayoutState layout
    let dst :=
      targetSignedLayoutState src (scanNeededWidths x z ops)
    ∀ i : Fin k,
      SignedRecursiveWorkspaceOK ops (dst.xslot i) (dst.zslot i)
  /--
  Every phase-product leaf emitted by this level has the recursive width
  `nextSignedWidth x z ops`.
  -/
  childInputSize :
    let src :=
      initSignedLayoutState layout
    let dst :=
      targetSignedLayoutState src (scanNeededWidths x z ops)
    ∀ i : Fin k,
      phaseInputSize
        (dst.xslot i)
        (dst.zslot i)
        =
      nextSignedWidth x z ops

/-- Canonical deterministic construction of one recursive signed phase-product step. -/
def canonicalSignedStep
    {k : ℕ}
    (hk : 1 < k)
    (ops : Prog k)
    (x z : ExtReg)
    (hrec : nextSignedWidth x z ops < phaseInputSize x z)
    (hworkspace : SignedRecursiveWorkspaceOK ops x z) :
    CanonicalSignedStep ops x z := by
  let reqX : Fin k → ℕ :=
    RecursivePhaseWorkspace.requiredXChildReserve
      ops x.width z.width
  let reqZ : Fin k → ℕ :=
    RecursivePhaseWorkspace.requiredZChildReserve
      ops x.width z.width
  have hkpos : 0 < k := by omega
  -- The width-model registers reproduce the operands' active widths.
  have hwmX :
      (RecursivePhaseWorkspace.widthModelX x.width).width = x.width := by
    simp [RecursivePhaseWorkspace.widthModelX, ExtReg.width, ExtReg.ofReg,
      regSize, Reg.width, Reg.interval]
  have hwmZ :
      (RecursivePhaseWorkspace.widthModelZ x.width z.width).width = z.width := by
    simp [RecursivePhaseWorkspace.widthModelZ, ExtReg.width, ExtReg.ofReg,
      regSize, Reg.width, Reg.interval]
  -- Consequently every width-only quantity matches the concrete operands.
  have hlimb :
      phaseLimbWidth
        (RecursivePhaseWorkspace.widthModelX x.width)
        (RecursivePhaseWorkspace.widthModelZ x.width z.width) k
        = phaseLimbWidth x z k := by
    simp only [phaseLimbWidth, hwmX, hwmZ]
  have hinit :
      initWidthState
        (RecursivePhaseWorkspace.widthModelX x.width)
        (RecursivePhaseWorkspace.widthModelZ x.width z.width) k
        = initWidthState x z k := by
    simp only [initWidthState, hwmX, hwmZ, hlimb]
  have hnext :
      RecursivePhaseWorkspace.nextWidth ops x.width z.width
        = nextSignedWidth x z ops := by
    simp only [RecursivePhaseWorkspace.nextWidth, nextSignedWidth,
      scanNeededWidths, hinit]
  -- The recursion guard `hrec` transfers to the width-model formulation.
  have hrec' :
      RecursivePhaseWorkspace.nextWidth ops x.width z.width
        < max x.width z.width := by
    rw [hnext]; exact hrec
  have hxfit :
      (List.ofFn reqX).sum ≤ x.capacity := by
    show (List.ofFn
      (RecursivePhaseWorkspace.requiredXChildReserve
        ops x.width z.width)).sum ≤ x.capacity
    rw [RecursivePhaseWorkspace.requiredXChildReserve_sum]
    have hres := hworkspace.x_reserve_sufficient
    rw [RecursivePhaseWorkspace.reserveNeed_fst, dif_pos hrec'] at hres
    exact hres
  have hzfit :
      (List.ofFn reqZ).sum ≤ z.capacity := by
    show (List.ofFn
      (RecursivePhaseWorkspace.requiredZChildReserve
        ops x.width z.width)).sum ≤ z.capacity
    rw [RecursivePhaseWorkspace.requiredZChildReserve_sum]
    have hres := hworkspace.z_reserve_sufficient
    rw [RecursivePhaseWorkspace.reserveNeed_snd, dif_pos hrec'] at hres
    exact hres
  let xBudget : ReserveBudget x k := ReserveBudget.ofRequirements hkpos reqX hxfit
  let zBudget : ReserveBudget z k := ReserveBudget.ofRequirements hkpos reqZ hzfit
  let xSplit : PhaseSplitLayout x k (phaseLimbWidth x z k) :=
    PhaseSplitLayout.ofBudget x k (phaseLimbWidth x z k) (phaseLimbWidth_valid_left x z hkpos) xBudget
  let zSplit : PhaseSplitLayout z k (phaseLimbWidth x z k) :=
    PhaseSplitLayout.ofBudget z k (phaseLimbWidth x z k) (phaseLimbWidth_valid_right x z hkpos) zBudget
  have hlimb' : RecursivePhaseWorkspace.limbWidth k x.width z.width = phaseLimbWidth x z k := hlimb
  have child_owned_subset :
      ∀ {parent : ExtReg} {W : ℕ} (split : PhaseSplitLayout parent k W) (i : Fin k),
        (split.child i).ownedQubits ⊆ parent.ownedQubits := by
    intro parent W split i qbit hq
    change
      qbit ∈ (phaseChunkActive parent k W i).qubits ++ (split.reserve i).qubits at hq
    change qbit ∈ parent.active.qubits ++ parent.reserve.qubits
    rw [List.mem_append] at hq ⊢
    rcases hq with hqActive | hqReserve
    · left
      simp only [phaseChunkActive, Reg.take, Reg.drop] at hqActive
      exact List.mem_of_mem_drop (List.mem_of_mem_take hqActive)
    · right
      have hqFlatten :
          qbit ∈
            (List.ofFn fun j : Fin k =>
              (split.reserve j).qubits).flatten := by
        rw [List.mem_flatten]
        refine ⟨(split.reserve i).qubits, ?_, hqReserve⟩
        simp
      rw [split.reserve_partition] at hqFlatten
      exact hqFlatten
  let layout :
      Gate.PhaseProductLayout x z k :=
    {
      xSplit := xSplit
      zSplit := zSplit
      cross_owned_disjoint := by
        intro i j; unfold ExtReg.OwnedDisjoint
        exact List.disjoint_of_subset_left (child_owned_subset xSplit i)
          (List.disjoint_of_subset_right (child_owned_subset zSplit j) hworkspace.owned_disjoint)
    }
  have hreqX_formula
      (i : Fin k) :
      reqX i = (nextSignedWidth x z ops - (xSplit.child i).width) +
        (RecursivePhaseWorkspace.reserveNeed ops (nextSignedWidth x z ops) (nextSignedWidth x z ops)).1 := by
    dsimp [
      reqX,
      RecursivePhaseWorkspace.requiredXChildReserve,
      RecursivePhaseWorkspace.requiredChildReserve,
      RecursivePhaseWorkspace.PhaseSide.width,
      RecursivePhaseWorkspace.PhaseSide.reserveComponent
    ]
    rw [hlimb', hnext, xSplit.child_width]
  have hreqZ_formula
      (i : Fin k) :
      reqZ i = (nextSignedWidth x z ops - (zSplit.child i).width) +
        (RecursivePhaseWorkspace.reserveNeed ops (nextSignedWidth x z ops) (nextSignedWidth x z ops)).2 := by
    dsimp [
      reqZ,
      RecursivePhaseWorkspace.requiredZChildReserve,
      RecursivePhaseWorkspace.requiredChildReserve,
      RecursivePhaseWorkspace.PhaseSide.width,
      RecursivePhaseWorkspace.PhaseSide.reserveComponent
    ]
    rw [hlimb', hnext, zSplit.child_width]
  have hxChildCapacity
      (i : Fin k) :
      reqX i ≤ (xSplit.child i).capacity := by
    have h := ReserveBudget.required_le_childReserve_size (parent := x) hkpos reqX hxfit i
    simpa [
      xSplit,
      PhaseSplitLayout.ofBudget,
      PhaseSplitLayout.child,
      ExtReg.withReserve,
      ExtReg.capacity
    ] using h
  have hzChildCapacity
      (i : Fin k) :
      reqZ i ≤ (zSplit.child i).capacity := by
    have h := ReserveBudget.required_le_childReserve_size (parent := z) hkpos reqZ hzfit i
    simpa [
      zSplit,
      PhaseSplitLayout.ofBudget,
      PhaseSplitLayout.child,
      ExtReg.withReserve,
      ExtReg.capacity
    ] using h
  have hcapacity :
      (initSignedLayoutState layout).CanGrowToNeeds
        (scanNeededWidths x z ops) := by
    change
      LayoutState.CanGrowTo
        (initSignedLayoutState layout)
        (nextSignedWidth x z ops)
    constructor
    · intro i
      change nextSignedWidth x z ops - (xSplit.child i).width ≤ (xSplit.child i).capacity
      have hsize := hxChildCapacity i
      rw [hreqX_formula i] at hsize
      omega
    · intro i
      change nextSignedWidth x z ops - (zSplit.child i).width ≤ (zSplit.child i).capacity
      have hsize := hzChildCapacity i
      rw [hreqZ_formula i] at hsize
      omega
  refine
    {
      layout := layout
      capacity := hcapacity
      childWorkspace := ?_
      childInputSize := ?_
    }
  · dsimp only
    intro i
    let src : LayoutState k := initSignedLayoutState layout
    let dst : LayoutState k := targetSignedLayoutState src (scanNeededWidths x z ops)
    have howned :
        ExtReg.OwnedDisjoint
          (dst.xslot i)
          (dst.zslot i) := by
      have hpair := targetSignedLayoutState_owned_disjoint layout (scanNeededWidths x z ops)
      simpa [src, dst] using hpair.2.2 i i
    have hxgrow :
        (xSplit.child i).CanGrow
          (nextSignedWidth x z ops -
            (xSplit.child i).width) := by
      have h := hcapacity.1 i
      change (xSplit.child i).CanGrow (nextSignedWidth x z ops - (xSplit.child i).width) at h
      exact h
    have hzgrow :
        (zSplit.child i).CanGrow
          (nextSignedWidth x z ops -
            (zSplit.child i).width) := by
      have h := hcapacity.2 i
      change (zSplit.child i).CanGrow (nextSignedWidth x z ops - (zSplit.child i).width) at h
      exact h
    have hxcapacity :
        (dst.xslot i).capacity
          =
        (xSplit.child i).capacity -
          (nextSignedWidth x z ops -
            (xSplit.child i).width) := by
      change
        ((xSplit.child i).grow
          (nextSignedWidth x z ops -
            (xSplit.child i).width)).capacity
          =
        (xSplit.child i).capacity -
          (nextSignedWidth x z ops -
            (xSplit.child i).width)
      exact
        ExtReg.capacity_grow
          (xSplit.child i)
          (nextSignedWidth x z ops -
            (xSplit.child i).width)
          hxgrow
    have hzcapacity :
        (dst.zslot i).capacity
          =
        (zSplit.child i).capacity -
          (nextSignedWidth x z ops -
            (zSplit.child i).width) := by
      change
        ((zSplit.child i).grow
          (nextSignedWidth x z ops -
            (zSplit.child i).width)).capacity
          =
        (zSplit.child i).capacity -
          (nextSignedWidth x z ops -
            (zSplit.child i).width)
      exact
        ExtReg.capacity_grow
          (zSplit.child i)
          (nextSignedWidth x z ops -
            (zSplit.child i).width)
          hzgrow
    have hxwidth :
        (dst.xslot i).width =
          nextSignedWidth x z ops := by
      simpa [src, dst, nextSignedWidth] using targetSignedLayoutState_xslot_width_scan layout ops i hcapacity
    have hzwidth :
        (dst.zslot i).width =
          nextSignedWidth x z ops := by
      simpa [src, dst, nextSignedWidth] using targetSignedLayoutState_zslot_width_scan layout ops i hcapacity
    refine
      {
        owned_disjoint := howned
        x_reserve_sufficient := ?_
        z_reserve_sufficient := ?_
      }
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
    let src : LayoutState k := initSignedLayoutState layout
    let dst : LayoutState k := targetSignedLayoutState src (scanNeededWidths x z ops)
    have hxwidth :
        (dst.xslot i).width =
          nextSignedWidth x z ops := by
      simpa [src, dst, nextSignedWidth] using targetSignedLayoutState_xslot_width_scan layout ops i hcapacity
    have hzwidth :
        (dst.zslot i).width =
          nextSignedWidth x z ops := by
      simpa [src, dst, nextSignedWidth] using targetSignedLayoutState_zslot_width_scan layout ops i hcapacity
    unfold phaseInputSize
    rw [hxwidth, hzwidth, max_self]


/-- Every child register selected by a phase split is physically owned by its parent. -/
lemma PhaseSplitLayout.child_owned_subset_parent
    {parent : ExtReg}
    {k W : ℕ}
    (split : PhaseSplitLayout parent k W)
    (i : Fin k) :
    (split.child i).ownedQubits ⊆ parent.ownedQubits := by
  intro qbit hq
  change qbit ∈ (phaseChunkActive parent k W i).qubits ++ (split.reserve i).qubits at hq
  change qbit ∈ parent.active.qubits ++ parent.reserve.qubits
  rw [List.mem_append] at hq ⊢
  rcases hq with hqActive | hqReserve
  · left
    simp only [phaseChunkActive, Reg.take, Reg.drop] at hqActive
    exact List.mem_of_mem_drop (List.mem_of_mem_take hqActive)
  · right
    have hqFlatten :
        qbit ∈ (List.ofFn fun j : Fin k => (split.reserve j).qubits).flatten := by
      rw [List.mem_flatten]
      refine ⟨(split.reserve i).qubits, ?_, hqReserve⟩
      simp
    rw [split.reserve_partition] at hqFlatten
    exact hqFlatten

/-- If a control qubit is outside the parent operands, it is outside every layout child. -/
lemma Gate.PhaseProductLayout.controlDisjoint_of_ctrlDisjoint
    {x z : ExtReg}
    {k : ℕ}
    (layout : Gate.PhaseProductLayout x z k)
    {ctrl : ℕ}
    (hctrl : ExtReg.CtrlDisjoint ctrl x z) :
    layout.ControlDisjoint ctrl := by
  constructor
  · intro i hmem
    exact hctrl.1 (PhaseSplitLayout.child_owned_subset_parent layout.xSplit i hmem)
  · intro i hmem
    exact hctrl.2 (PhaseSplitLayout.child_owned_subset_parent layout.zSplit i hmem)

/--
Static workspace requirements for a controlled recursive signed phase
product.
In addition to the uncontrolled conditions, the control qubit must be outside
both operands' complete owned regions, including their future workspace.
-/
structure CSignedRecursiveWorkspaceOK
    {k : ℕ}
    (ops : Prog k)
    (ctrl : ℕ)
    (x z : ExtReg) :
    Prop extends SignedRecursiveWorkspaceOK ops x z where
  control_disjoint : ExtReg.CtrlDisjoint ctrl x z

end Shor
