import ForShor.ShorVerification.Implementation.PhaseProduct.Statement
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.Compile

/-!
# Phase-Product Compiler: Workspace

The recursive-workspace size model (`RecursivePhaseWorkspace.reserveNeed` and
friends), the static workspace-sufficiency predicates
(`SignedRecursiveWorkspaceOK`, `CSignedRecursiveWorkspaceOK`), the concrete
reserve-budget construction (`PhaseSplitLayout.ofBudget`,
`ReserveBudget.ofRequirements`). The canonical recursive step that uses them
is `Policy.canonicalStep` in `PolicyWorkspace.lean`.
-/

/-! ---------------------------------------------------------
    Chunks and reserve slices lie inside the parent
--------------------------------------------------------- -/

namespace Shor

theorem phaseChunkActive_sublist
    (parent : ExtReg)
    (k W : ℕ)
    (i : Fin k) :
    (phaseChunkActive parent k W i).qubits.Sublist
      parent.active.qubits := by
  simp only [phaseChunkActive, Reg.take, Reg.drop]
  exact (List.take_sublist _ _).trans (List.drop_sublist _ _)

theorem ReserveBudget.childReserve_sublist
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

theorem phaseChunkActive_childReserve_disjoint
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
  have hparent : parent.active.qubits.Disjoint parent.reserve.qubits := by
    simpa [Disjoint] using parent.active_reserve_disjoint
  exact
    List.disjoint_of_subset_left hactive.subset
      (List.disjoint_of_subset_right
        hreserve.subset
        hparent)

end Shor

/-! ---------------------------------------------------------
    Workspace preservation and reserve-budget construction (moved from `Statement.lean`)
--------------------------------------------------------- -/

namespace Shor
open Gate
open Operations
open scoped BigOperators

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
    simpa [dst, targetSignedLayoutState, growExtRegTo, src, initSignedLayoutState, Gate.ExtReg.ownedQubits_grow] using hx i
  · intro i
    simpa [dst, targetSignedLayoutState, growExtRegTo, src, initSignedLayoutState, Gate.ExtReg.ownedQubits_grow] using hz i

/-- Target widening preserves pairwise owned-disjointness of all slots. -/
theorem targetSignedLayoutState_owned_disjoint
    {x z : ExtReg}
    {k : ℕ}
    {layout : Gate.PhaseProductLayout x z k}
    (hv : layout.Valid)
    (need : NeededWidths k) :
    (targetSignedLayoutState
      (initSignedLayoutState layout)
      need).OwnedPairwiseDisjoint := by
  obtain ⟨hx, hz, hxz⟩ := initSignedLayoutState_owned_disjoint hv
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    simpa [targetSignedLayoutState, growExtRegTo, ExtReg.OwnedDisjoint, Gate.ExtReg.ownedQubits_grow] using hx i j hij
  · intro i j hij
    simpa [targetSignedLayoutState, growExtRegTo, ExtReg.OwnedDisjoint, Gate.ExtReg.ownedQubits_grow] using hz i j hij
  · intro i j
    simpa [targetSignedLayoutState, growExtRegTo, ExtReg.OwnedDisjoint, Gate.ExtReg.ownedQubits_grow] using hxz i j

/-- Consecutive variable-width slices reconstruct the corresponding prefix. -/
private theorem flatten_consecutive_slices
    (L : List ℕ) :
    ∀ (k : ℕ) (size : Fin k → ℕ),
      (List.ofFn fun i => List.take (size i) (List.drop (((List.ofFn size).take i.1).sum) L)).flatten
        = List.take ((List.ofFn size).sum) L := by
  intro k
  induction k with
  | zero =>
      intro size
      simp
  | succ k ih =>
      intro size
      let size' : Fin k → ℕ :=
        fun i => size i.castSucc
      have htake (i : Fin k) : (List.ofFn size).take i.1 = (List.ofFn size').take i.1 := by
        rw [List.ofFn_succ', List.concat_eq_append]
        simp [size', List.take_append_of_le_length]
      have htakeLast : (List.ofFn size).take k = List.ofFn size' := by
        rw [List.ofFn_succ', List.concat_eq_append]
        simp [size']
      have hsum : (List.ofFn size).sum = (List.ofFn size').sum + size (Fin.last k) := by
        rw [List.ofFn_succ']
        simp [size']
      rw [List.ofFn_succ', List.concat_eq_append, List.flatten_append]
      simp only [Fin.val_castSucc, List.flatten_cons, List.flatten_nil, List.append_nil]
      have hlastVal : (Fin.last k).1 = k := rfl
      rw [hlastVal]
      simp_rw [htake]
      change
        (List.ofFn fun i : Fin k =>
          List.take (size' i) (List.drop (((List.ofFn size').take i.1).sum) L)).flatten
          ++ List.take (size (Fin.last k)) (List.drop (((List.ofFn size).take k).sum) L)
          = List.take ((List.ofFn size).sum) L
      rw [ih size', htakeLast, hsum, List.take_add]

theorem ReserveBudget.flatten_childReserve
    {parent : ExtReg} {k : ℕ} (budget : ReserveBudget parent k)
    (htotal : (List.ofFn budget.size).sum = parent.capacity) :
    (List.ofFn fun i => (budget.childReserve i).qubits).flatten = parent.reserve.qubits := by
  simp only [ReserveBudget.childReserve, ReserveBudget.offset, Reg.take, Reg.drop]
  rw [flatten_consecutive_slices]
  rw [htotal]
  simp [ExtReg.capacity, regSize, Reg.width]

theorem pairwise_disjoint_ofFn
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

/-- A budget layout is valid when the split is valid and the budget uses the
whole parent reserve. -/
theorem PhaseSplitLayout.ofBudget_valid
    {parent : ExtReg}
    {k W : ℕ}
    (hvalid : ValidPhaseSplit parent k W)
    (budget : ReserveBudget parent k)
    (htotal : (List.ofFn budget.size).sum = parent.capacity) :
    (PhaseSplitLayout.ofBudget parent k W budget).Valid where
  reserve_partition := budget.flatten_childReserve htotal
  child_owned_pairwise := by
    intro i j hij
    have hAA :
        List.Disjoint (phaseChunkActive parent k W i).qubits
          (phaseChunkActive parent k W j).qubits := by
      simpa [Disjoint] using phaseChunkActive_pairwise_disjoint parent k W hvalid hij
    have hAR : List.Disjoint (phaseChunkActive parent k W i).qubits (budget.childReserve j).qubits :=
      phaseChunkActive_childReserve_disjoint (W := W) budget i j
    have hRA : List.Disjoint (budget.childReserve i).qubits (phaseChunkActive parent k W j).qubits :=
      (phaseChunkActive_childReserve_disjoint (W := W) budget j i).symm
    have hflatNodup :
        ((List.ofFn fun t : Fin k => (budget.childReserve t).qubits).flatten).Nodup := by
      rw [budget.flatten_childReserve htotal]
      exact parent.reserve.nodup
    have hreservePairwise :
        (List.ofFn fun t : Fin k => (budget.childReserve t).qubits).Pairwise List.Disjoint :=
      (List.nodup_flatten.mp hflatNodup).2
    have hRR : List.Disjoint (budget.childReserve i).qubits (budget.childReserve j).qubits :=
      pairwise_disjoint_ofFn (f := fun t : Fin k => (budget.childReserve t).qubits)
        hreservePairwise hij
    intro q hqLeft hqRight
    rcases List.mem_append.mp hqLeft with hqAi | hqRi
    · rcases List.mem_append.mp hqRight with hqAj | hqRj
      · exact hAA hqAi hqAj
      · exact hAR hqAi hqRj
    · rcases List.mem_append.mp hqRight with hqAj | hqRj
      · exact hRA hqRi hqAj
      · exact hRR hqRi hqRj

/-! =========================================================
    Canonical recursive step construction
    The canonical step builds a phase-product layout whose child chunks have
    exactly the next recursive width and enough reserve for all descendant calls.
========================================================= -/

namespace ReserveBudget

/-- The slack-filled child reserve sizes sum exactly to the parent capacity. -/
lemma fillSlack_sum
    {k : ℕ}
    (hk : 0 < k)
    (capacity : ℕ)
    (required : Fin k → ℕ)
    (hfit :
      (List.ofFn required).sum ≤ capacity) :
    (List.ofFn (fillSlack hk capacity required)).sum = capacity := by
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
  · rw [ite_eq_left h, h]; exact Nat.le_add_right _ _
  · rw [ite_eq_right h]

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
      regSize ((ofRequirements (parent := parent) hk required).childReserve i) := by
  set budget := ofRequirements (parent := parent) hk required with hbudget
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
    have htot : (List.ofFn budget.size).sum = parent.capacity :=
      fillSlack_sum hk parent.capacity required hfit
    omega
  -- Hence the physical `take` does not truncate: the slice has size `size i`.
  have h2 : regSize (budget.childReserve i) = budget.size i := by
    have hcap : parent.reserve.qubits.length = parent.capacity := rfl
    simp only [regSize, Reg.width, ReserveBudget.childReserve, Reg.take,
      Reg.drop, List.length_take, List.length_drop]
    omega
  rw [h2]; exact h1

end ReserveBudget

/-- Every child register selected by a phase split is physically owned by its parent. -/
lemma PhaseSplitLayout.child_owned_subset_parent
    {parent : ExtReg}
    {k W : ℕ}
    {split : PhaseSplitLayout parent k W}
    (hv : split.Valid)
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
    rw [hv.reserve_partition] at hqFlatten
    exact hqFlatten

/-- If a control qubit is outside the parent operands, it is outside every layout child. -/
lemma Gate.PhaseProductLayout.controlDisjoint_of_ctrlDisjoint
    {x z : ExtReg}
    {k : ℕ}
    {layout : Gate.PhaseProductLayout x z k}
    (hv : layout.Valid)
    {ctrl : ℕ}
    (hctrl : ExtReg.CtrlDisjoint ctrl x z) :
    layout.ControlDisjoint ctrl := by
  constructor
  · intro i hmem
    exact hctrl.1 (PhaseSplitLayout.child_owned_subset_parent hv.xSplit i hmem)
  · intro i hmem
    exact hctrl.2 (PhaseSplitLayout.child_owned_subset_parent hv.zSplit i hmem)

end Shor

namespace Shor
open Gate
open Operations
open scoped BigOperators

/-! =========================================================
    Recursive workspace size model
    The recursive compiler needs reserve space for current-level chunk growth and
    for each descendant phase-product call. These width-only definitions compute
    conservative reserve requirements from logical operand widths.
========================================================= -/

namespace RecursivePhaseWorkspace

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
    Canonical recursive step construction
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

end Shor
