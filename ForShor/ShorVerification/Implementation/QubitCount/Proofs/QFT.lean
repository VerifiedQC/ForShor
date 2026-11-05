import ForShor.ShorVerification.Implementation.QubitCount.Proofs.Unsigned
import ForShor.ShorVerification.Implementation.QFT.Statement

/-!
# Qubit count: the QFT

The lowered QFT on a register `r` with workspace pools `xWork` and `zWork`
returns the live set it started from and peaks `Rec.qftPeak` above it.

The proof also covers a start set in which the first qubit of `xWork` is
already live. That qubit is the first one the QFT's first phase product
activates, so the activation costs nothing and the phase product's release
leaves it dead; from then on the walk is the fresh one. This is what happens
to the scratch register's first reserve qubit in Step 4 of a modular
multiplication, after Step 3 has used it without activating it.
-/

namespace Shor
namespace QubitCount

open Gate

/-! ## The budget -/

lemma qftPeak_lt_two (P : ShorLoweringPolicy) {n : ℕ} (h : n < 2) : Rec.qftPeak P n = 0 := by
  interval_cases n <;> simp [Rec.qftPeak, Rec.qftPeakOf]

lemma qftPeak_split (P : ShorLoweringPolicy) {n : ℕ} (h : 2 ≤ n) :
    Rec.qftPeak P n
      = max (2 + Rec.peakReserve P (n / 2 + 1) (n - n / 2 + 1))
          (max (Rec.qftPeak P (n / 2)) (Rec.qftPeak P (n - n / 2))) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' h
  simp only [Rec.qftPeak]
  rw [Rec.qftPeakOf]

/-! ## The canonical plan -/

/-- The first pool qubit, as a set. -/
abbrev firstOf (xWork : Reg) : Finset ℕ := regQubitSet (xWork.take 1)

lemma firstOf_card_le (xWork : Reg) : (firstOf xWork).card ≤ 1 := by
  rw [card_regQubitSet]
  simp [Reg.take, regSize, Reg.width]

lemma firstOf_subset (xWork : Reg) : firstOf xWork ⊆ regQubitSet xWork :=
  regQubitSet_subset_of_sublist (List.take_sublist _ _)

/--
The walk of the canonical lowered QFT on a register of width at least two,
from a live set that holds the register, none of `zWork`, and of `xWork` at
most its first qubit. The walk ends without that qubit and peaks `qftPeak`
above the set without it. A narrower register only acts on live qubits. From
a set holding none of `xWork`, the walk is well formed.
-/
theorem qftPlan_walk (P : ShorLoweringPolicy) (hP : P.Admissible) (xW zW : Reg) (r : Reg)
    (h : Policy.QFTWorkspaceOK P r xW zW) (L : Finset ℕ)
    (hr : regQubitSet r ⊆ L) (hz : _root_.Disjoint L (regQubitSet zW))
    (hx : L ∩ regQubitSet xW ⊆ firstOf xW) :
    after (lowerQFTPlan (Policy.qftPlan P r xW zW h)) true L
        = (if 2 ≤ regSize r then L \ firstOf xW else L) ∧
    peak scratch (lowerQFTPlan (Policy.qftPlan P r xW zW h)) true L
        = (if 2 ≤ regSize r then (L \ firstOf xW).card + Rec.qftPeak P (regSize r)
            else L.card) ∧
    (_root_.Disjoint L (regQubitSet xW) →
      WellFormed (lowerQFTPlan (Policy.qftPlan P r xW zW h)) true L) := by
  by_cases hzero : regSize r = 0
  · have hp : lowerQFTPlan (Policy.qftPlan P r xW zW h) = LowGate.id := by
      rw [Policy.qftPlan]; simp only [hzero, ↓reduceDIte]; rfl
    rw [hp]
    simp [after, peak, WellFormed, hzero]
  by_cases hone : regSize r = 1
  · have hp : lowerQFTPlan (Policy.qftPlan P r xW zW h)
        = LowGate.H (r.lowQubit (by omega)) := by
      rw [Policy.qftPlan]; simp only [hone, ↓reduceDIte]; rfl
    have hq : r.lowQubit (by omega) ∈ L := by
      apply hr
      rw [mem_regQubitSet]
      exact List.get_mem _ _
    rw [hp]
    simp [after, peak, WellFormed, hone, LowGate.usedQubits, hq]
  have hlarge : 2 ≤ regSize r := by omega
  set ws : Gate.PhaseProdWorkspace (leftReg r) (rightReg r) := h.phaseWorkspace hlarge with hws
  have hphase : Policy.WorkspaceOK P (ws.xExt.grow 1) (ws.zExt.grow 1) := by
    simpa [ws] using h.policySignedWorkspaceOK hlarge
  have hp : lowerQFTPlan (Policy.qftPlan P r xW zW h)
      = (lowerQFTPlan (Policy.qftPlan P (rightReg r) xW zW (h.right hlarge)) ;;
          lowerGateRec (Policy.phaseProdUsingPlan P (qftPhi (regSize r)) ws) ;;
          lowerQFTPlan (Policy.qftPlan P (leftReg r) xW zW (h.left hlarge)) ;;
          LowGate.RadixReverse r (regSize r / 2)) := by
    rw [Policy.qftPlan]; simp only [hzero, hone, ↓reduceDIte]; rfl
  -- The plan is `zeroExtend ; zeroExtend ; signedPlan ; zeroDealloc ; zeroDealloc`.
  have hvPP : (Policy.phaseProdUsingPlan P (qftPhi (regSize r)) ws).Valid :=
    ⟨trivial, trivial, Policy.signedPlan_valid P _ _ _ hphase, trivial, trivial⟩
  obtain ⟨c, hvc, hc⟩ :=
    ppUsing_plan_shape (Policy.phaseProdUsingPlan P (qftPhi (regSize r)) ws) hvPP
  -- register facts
  have hrx : _root_.Disjoint (regQubitSet r) (regQubitSet xW) := regQubitSet_disjoint h.data_x_disjoint
  have hrz : _root_.Disjoint (regQubitSet r) (regQubitSet zW) := regQubitSet_disjoint h.data_z_disjoint
  have hxzW : _root_.Disjoint (regQubitSet xW) (regQubitSet zW) := regQubitSet_disjoint h.work_disjoint
  have hleft : regQubitSet (leftReg r) ⊆ regQubitSet r :=
    regQubitSet_subset_of_sublist (List.take_sublist _ _)
  have hright : regQubitSet (rightReg r) ⊆ regQubitSet r :=
    regQubitSet_subset_of_sublist (List.drop_sublist _ _)
  set L₀ := L \ firstOf xW with hL₀
  have hL₀x : _root_.Disjoint L₀ (regQubitSet xW) := by
    rw [Finset.disjoint_left]
    intro q hq hqx
    rw [hL₀, Finset.mem_sdiff] at hq
    exact hq.2 (hx (Finset.mem_inter.mpr ⟨hq.1, hqx⟩))
  have hrL₀ : regQubitSet r ⊆ L₀ := by
    intro q hq
    rw [hL₀, Finset.mem_sdiff]
    exact ⟨hr hq, fun h' => Finset.disjoint_left.mp hrx hq (firstOf_subset xW h')⟩
  have hL₀z : _root_.Disjoint L₀ (regQubitSet zW) :=
    Finset.disjoint_of_subset_left Finset.sdiff_subset hz
  have hL₀card : L.card ≤ L₀.card + 1 := by
    have := Finset.card_le_card (show L ⊆ L₀ ∪ firstOf xW from by
      intro q hq; by_cases h' : q ∈ firstOf xW
      · exact Finset.mem_union_right _ h'
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hq, h'⟩))
    have := Finset.card_union_le L₀ (firstOf xW)
    have := firstOf_card_le xW
    omega
  -- the two qubits the phase product activates
  have hbx : allocBits ws.xExt 1 = firstOf xW := rfl
  have hbz : allocBits ws.zExt 1 = firstOf zW := rfl
  -- the right half
  obtain ⟨aR, pR, wR⟩ := qftPlan_walk P hP xW zW (rightReg r) (h.right hlarge) L
    (hright.trans hr) hz hx
  set M := after (lowerQFTPlan (Policy.qftPlan P (rightReg r) xW zW (h.right hlarge))) true L
    with hM
  have hMsub : M ⊆ L := by rw [aR]; split <;> simp [Finset.sdiff_subset]
  have hMx : M ∪ firstOf xW = L ∪ firstOf xW := by
    rw [aR]; split
    · exact Finset.sdiff_union_self_eq_union
    · rfl
  have hMd : M \ firstOf xW = L₀ := by
    rw [aR]; split
    · exact Finset.sdiff_idem _ _
    · rfl
  -- the middle phase product
  have hxa : regQubitSet (ws.xExt.grow 1).active ⊆ L ∪ firstOf xW ∪ firstOf zW := by
    rw [grow_active, hbx]
    intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (hr (hleft hq)))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hq)
  have hza : regQubitSet (ws.zExt.grow 1).active ⊆ L ∪ firstOf xW ∪ firstOf zW := by
    rw [grow_active, hbz]
    intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (hr (hright hq)))
    · exact Finset.mem_union_right _ hq
  have hres2 : _root_.Disjoint (L ∪ firstOf xW ∪ firstOf zW)
      (regQubitSet (ws.xExt.grow 1).reserve ∪ regQubitSet (ws.zExt.grow 1).reserve) := by
    have hxr : regQubitSet (ws.xExt.grow 1).reserve ⊆ regQubitSet xW := grow_reserve_subset _ _
    have hzr : regQubitSet (ws.zExt.grow 1).reserve ⊆ regQubitSet zW := grow_reserve_subset _ _
    have hxb := allocBits_disjoint_grow_reserve ws.xExt 1
    have hzb := allocBits_disjoint_grow_reserve ws.zExt 1
    rw [hbx] at hxb
    rw [hbz] at hzb
    rw [Finset.disjoint_union_right]
    refine ⟨?_, ?_⟩
    · rw [Finset.disjoint_union_left, Finset.disjoint_union_left]
      refine ⟨⟨?_, hxb⟩, ?_⟩
      · rw [Finset.disjoint_right]
        intro q hq hqL
        have hqx : q ∈ regQubitSet xW := hxr hq
        have : q ∈ firstOf xW := hx (Finset.mem_inter.mpr ⟨hqL, hqx⟩)
        exact Finset.disjoint_left.mp hxb this hq
      · exact Finset.disjoint_of_subset_left (firstOf_subset zW)
          (Finset.disjoint_of_subset_right hxr hxzW.symm)
    · rw [Finset.disjoint_union_left, Finset.disjoint_union_left]
      exact ⟨⟨Finset.disjoint_of_subset_right hzr hz,
        Finset.disjoint_of_subset_left (firstOf_subset xW)
          (Finset.disjoint_of_subset_right hzr hxzW)⟩, hzb⟩
  obtain ⟨aS, pS, wS⟩ := plan_walk hP c hvc (L ∪ firstOf xW ∪ firstOf zW) ⟨rfl, hxa, hza, hres2⟩
  simp only [gAfter, gPeak, ppEx] at aS pS
  have hxz' : _root_.Disjoint (allocBits ws.xExt 1) (allocBits ws.zExt 1) := by
    rw [hbx, hbz]
    exact Finset.disjoint_of_subset_left (firstOf_subset xW)
      (Finset.disjoint_of_subset_right (firstOf_subset zW) hxzW)
  have hzM : _root_.Disjoint (allocBits ws.zExt 1) M := by
    rw [hbz]
    exact Finset.disjoint_of_subset_right hMsub
      (Finset.disjoint_of_subset_left (firstOf_subset zW) hz.symm)
  have hSa : after (lowerGateRec c) true (M ∪ allocBits ws.xExt 1 ∪ allocBits ws.zExt 1)
      = M ∪ allocBits ws.xExt 1 ∪ allocBits ws.zExt 1 := by
    rw [hbx, hbz, hMx]; exact aS
  have hSp : peak scratch (lowerGateRec c) true (M ∪ allocBits ws.xExt 1 ∪ allocBits ws.zExt 1)
      = (M ∪ allocBits ws.xExt 1 ∪ allocBits ws.zExt 1).card
        + Rec.peakReserve P (ws.xExt.grow 1).width (ws.zExt.grow 1).width := by
    rw [hbx, hbz, hMx]; exact pS
  have hW := wrap_walk ws.xExt_canGrow ws.zExt_canGrow hxz' hzM hSa hSp
  rw [hbx, hMd] at hW
  obtain ⟨aP, pP, wP⟩ := hW
  have hwx : (ws.xExt.grow 1).width = regSize (leftReg r) + 1 :=
    ExtReg.width_grow ws.xExt 1 ws.xExt_canGrow
  have hwz : (ws.zExt.grow 1).width = regSize (rightReg r) + 1 :=
    ExtReg.width_grow ws.zExt 1 ws.zExt_canGrow
  rw [hwx, hwz] at pP
  -- the left half
  obtain ⟨aL, pL, wL⟩ := qftPlan_walk P hP xW zW (leftReg r) (h.left hlarge) L₀
    (hleft.trans hrL₀) hL₀z (by rw [Finset.disjoint_iff_inter_eq_empty.mp hL₀x]; simp)
  have hL₀d : L₀ \ firstOf xW = L₀ :=
    Finset.sdiff_eq_self_of_disjoint (Finset.disjoint_of_subset_right (firstOf_subset xW) hL₀x)
  rw [hL₀d] at aL pL
  have aL' : after (lowerQFTPlan (Policy.qftPlan P (leftReg r) xW zW (h.left hlarge))) true L₀ = L₀ := by
    rw [aL]; split <;> rfl
  have pL' : peak scratch (lowerQFTPlan (Policy.qftPlan P (leftReg r) xW zW (h.left hlarge)))
      true L₀ = L₀.card + Rec.qftPeak P (regSize (leftReg r)) := by
    rw [pL]; split
    · rfl
    · rw [qftPeak_lt_two P (by omega)]; rfl
  have hrad : L₀ ∪ LowGate.usedQubits (LowGate.RadixReverse r (regSize r / 2)) = L₀ :=
    Finset.union_eq_left.mpr hrL₀
  -- assemble
  rw [hp, hc]
  simp only [after, peak, WellFormed, scratch_RadixReverse]
  rw [← hM, aP, aL', hrad, ite_eq_left hlarge, ite_eq_left hlarge]
  rw [pP, pL', qftPeak_split P hlarge, regSize_leftReg, regSize_rightReg]
  rw [regSize_leftReg] at pL'
  refine ⟨rfl, ?_, ?_⟩
  · rw [pR, ← hL₀]
    split
    · next hR =>
        rw [regSize_rightReg] at hR ⊢
        simp only [← max_add_add_left]
        apply le_antisymm <;> simp only [max_le_iff, le_max_iff] <;> omega
    · next hR =>
        rw [regSize_rightReg] at hR
        rw [qftPeak_lt_two P (n := regSize r - regSize r / 2) (by omega)]
        simp only [← max_add_add_left]
        apply le_antisymm <;> simp only [max_le_iff, le_max_iff] <;> omega
  · intro hLx
    have hL₀L : L₀ = L := Finset.sdiff_eq_self_of_disjoint
      (Finset.disjoint_of_subset_right (firstOf_subset xW) hLx)
    refine ⟨wR hLx, ?_, ?_, ?_⟩
    · have hMeq : M = L := by
        rw [aR]; split
        · rw [← hL₀, hL₀L]
        · rfl
      have hw1 : _root_.Disjoint (firstOf xW) M := by
        rw [hMeq]; exact Finset.disjoint_of_subset_left (firstOf_subset xW) hLx.symm
      have hw2 : WellFormed (lowerGateRec c) true (M ∪ firstOf xW ∪ allocBits ws.zExt 1) := by
        rw [hbz, hMx]; exact wS
      exact wP hw1 hw2
    · exact wL hL₀x
    · exact hrL₀
termination_by regSize r
decreasing_by
  · have hhalfPos : 0 < regSize r / 2 := Nat.div_pos (by omega) (by decide)
    have hright : regSize r - regSize r / 2 < regSize r := Nat.sub_lt (by omega) hhalfPos
    simpa [rightReg, halfSplitPoint] using hright
  · have hleft : regSize r / 2 < regSize r := Nat.div_lt_self (by omega) (by decide)
    simpa [leftReg, halfSplitPoint] using hleft

/-! ## The claim -/

/-- The pools of a reserve-backed QFT lie in the register's reserve. -/
lemma qftPools_subset (P : ShorLoweringPolicy) (r : ExtReg) :
    regQubitSet (Policy.qftXWork P r) ⊆ regQubitSet r.reserve ∧
    regQubitSet (Policy.qftZWork P r) ⊆ regQubitSet r.reserve :=
  ⟨regQubitSet_subset_of_sublist (List.take_sublist _ _),
   regQubitSet_subset_of_sublist ((List.take_sublist _ _).trans (List.drop_sublist _ _))⟩

/-- A lowered QFT returns the live set it started from and uses `qftPeak`
qubits beyond it at its peak, scratch included, when its register is live and
its reserve is not. -/
theorem qftPeak_claim (P : ShorLoweringPolicy) :
    P.Admissible →
    ∀ (r : ExtReg) (hws : Policy.QFTReserveOK P r) (L : Finset ℕ),
      regQubitSet r.active ⊆ L → _root_.Disjoint L (regQubitSet r.reserve) →
      after (Policy.lowerQFT P r hws) true L = L ∧
      (Policy.lowerQFT P r hws).peakQubits L = L.card + Rec.qftPeak P r.width ∧
      WellFormed (Policy.lowerQFT P r hws) true L := by
  intro hP r hws L hr hres
  have hpools := qftPools_subset P r
  have hLx : _root_.Disjoint L (regQubitSet (Policy.qftXWork P r)) :=
    Finset.disjoint_of_subset_right hpools.1 hres
  have hLz : _root_.Disjoint L (regQubitSet (Policy.qftZWork P r)) :=
    Finset.disjoint_of_subset_right hpools.2 hres
  have hfirst : L \ firstOf (Policy.qftXWork P r) = L := Finset.sdiff_eq_self_of_disjoint
    (Finset.disjoint_of_subset_right (firstOf_subset _) hLx)
  obtain ⟨a, p, w⟩ := qftPlan_walk P hP _ _ r.active hws.explicitWorkspace L hr hLz
    (by rw [Finset.disjoint_iff_inter_eq_empty.mp hLx]; simp)
  rw [hfirst] at a p
  refine ⟨?_, ?_, w hLx⟩
  · show after (lowerQFTPlan (Policy.reserveQftPlan P r hws)) true L = L
    rw [Policy.reserveQftPlan, a]; split <;> rfl
  · show peak scratch (lowerQFTPlan (Policy.reserveQftPlan P r hws)) true L = _
    rw [Policy.reserveQftPlan, p]
    split
    · rfl
    · next h2 => rw [show r.width = regSize r.active from rfl, qftPeak_lt_two P (by omega)]; rfl

end QubitCount
end Shor
