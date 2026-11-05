import ForShor.ShorVerification.Implementation.QubitCount.Statement

/-!
# Qubit count: registers as sets of qubits

The register facts the counting proofs use, stated on `regQubitSet`: growing
a register moves the first qubits of its reserve into its active part, the
moved qubits number exactly as many as were asked for when the reserve is
large enough, and the chunks of a phase-product layout own disjoint parts of
their parent's reserve.
-/

namespace Shor
namespace QubitCount

lemma mem_regQubitSet {r : Reg} {q : ℕ} : q ∈ regQubitSet r ↔ q ∈ r.qubits := by
  simp [regQubitSet]

lemma card_regQubitSet (r : Reg) : (regQubitSet r).card = regSize r := by
  simp [regQubitSet, List.toFinset_card_of_nodup r.nodup, regSize, Reg.width]

lemma regQubitSet_subset_of_sublist {r s : Reg} (h : r.qubits.Sublist s.qubits) :
    regQubitSet r ⊆ regQubitSet s := by
  intro q hq
  rw [mem_regQubitSet] at hq ⊢
  exact h.subset hq

lemma regQubitSet_disjoint {r s : Reg} (h : Shor.Disjoint r s) :
    _root_.Disjoint (regQubitSet r) (regQubitSet s) := by
  rw [Finset.disjoint_left]
  intro q hr hs
  rw [mem_regQubitSet] at hr hs
  exact List.disjoint_left.mp h hr hs

lemma active_reserve_disjoint (e : ExtReg) :
    _root_.Disjoint (regQubitSet e.active) (regQubitSet e.reserve) :=
  regQubitSet_disjoint e.active_reserve_disjoint

lemma allocBits_subset_reserve (e : ExtReg) (n : ℕ) :
    allocBits e n ⊆ regQubitSet e.reserve :=
  regQubitSet_subset_of_sublist (List.take_sublist n e.reserve.qubits)

lemma card_allocBits (e : ExtReg) {n : ℕ} (h : e.CanGrow n) : (allocBits e n).card = n := by
  rw [allocBits, card_regQubitSet]
  simp only [ExtReg.newBits, Reg.take, regSize, Reg.width, List.length_take]
  simp only [ExtReg.CanGrow, ExtReg.capacity, regSize, Reg.width] at h
  omega

@[simp] lemma allocBits_zero (e : ExtReg) : allocBits e 0 = ∅ := by
  simp [allocBits, regQubitSet, ExtReg.newBits, Reg.take]

lemma grow_active (e : ExtReg) (n : ℕ) :
    regQubitSet (e.grow n).active = regQubitSet e.active ∪ allocBits e n := by
  simp [regQubitSet, allocBits, ExtReg.grow, Reg.append, List.toFinset_append]

lemma grow_reserve_subset (e : ExtReg) (n : ℕ) :
    regQubitSet (e.grow n).reserve ⊆ regQubitSet e.reserve :=
  regQubitSet_subset_of_sublist (List.drop_sublist n e.reserve.qubits)

lemma allocBits_disjoint_grow_reserve (e : ExtReg) (n : ℕ) :
    _root_.Disjoint (allocBits e n) (regQubitSet (e.grow n).reserve) := by
  rw [Finset.disjoint_left]
  intro q h1 h2
  simp only [allocBits, mem_regQubitSet, ExtReg.newBits, Reg.take] at h1
  simp only [mem_regQubitSet, ExtReg.grow, ExtReg.remainingReserve, Reg.drop] at h2
  exact List.disjoint_take_drop e.reserve.nodup le_rfl h1 h2

/-- Growing is monotone in what it owns: the grown active part and the
remaining reserve lie inside the original active part and reserve. -/
lemma grow_active_subset (e : ExtReg) (n : ℕ) :
    regQubitSet (e.grow n).active ⊆ regQubitSet e.active ∪ regQubitSet e.reserve := by
  rw [grow_active]
  exact Finset.union_subset_union le_rfl (allocBits_subset_reserve e n)

/-! ## Phase-product layouts -/

section Layout

variable {x z : ExtReg} {k : ℕ}

lemma splitReserve_subset {parent : ExtReg} {W : ℕ} (s : PhaseSplitLayout parent k W)
    (hv : s.Valid) (i : Fin k) : regQubitSet (s.reserve i) ⊆ regQubitSet parent.reserve := by
  intro q hq
  rw [mem_regQubitSet] at hq ⊢
  rw [← hv.reserve_partition, List.mem_flatten]
  exact ⟨(s.reserve i).qubits, List.mem_ofFn.mpr ⟨i, rfl⟩, hq⟩

lemma splitActive_subset {parent : ExtReg} {W : ℕ} (s : PhaseSplitLayout parent k W)
    (i : Fin k) : regQubitSet (s.child i).active ⊆ regQubitSet parent.active := by
  apply regQubitSet_subset_of_sublist
  simp only [PhaseSplitLayout.child, ExtReg.withReserve, phaseChunkActive, Reg.take, Reg.drop]
  exact (List.take_sublist _ _).trans (List.drop_sublist _ _)

lemma splitChild_reserve {parent : ExtReg} {W : ℕ} (s : PhaseSplitLayout parent k W)
    (i : Fin k) : (s.child i).reserve = s.reserve i := rfl

lemma splitReserve_disjoint {parent : ExtReg} {W : ℕ} (s : PhaseSplitLayout parent k W)
    (hv : s.Valid) {i j : Fin k} (hij : i ≠ j) :
    _root_.Disjoint (regQubitSet (s.reserve i)) (regQubitSet (s.reserve j)) := by
  rw [Finset.disjoint_left]
  intro q hi hj
  rw [mem_regQubitSet] at hi hj
  exact List.disjoint_left.mp (hv.child_owned_pairwise i j hij)
    (List.mem_append_right _ hi) (List.mem_append_right _ hj)

lemma crossReserve_disjoint (layout : Gate.PhaseProductLayout x z k) (hv : layout.Valid)
    (i j : Fin k) :
    _root_.Disjoint (regQubitSet (layout.xSplit.reserve i))
      (regQubitSet (layout.zSplit.reserve j)) := by
  rw [Finset.disjoint_left]
  intro q hi hj
  rw [mem_regQubitSet] at hi hj
  have h := hv.cross_owned_disjoint i j
  simp only [ExtReg.OwnedDisjoint, ExtReg.ownedQubits] at h
  exact List.disjoint_left.mp h (List.mem_append_right _ hi) (List.mem_append_right _ hj)

end Layout

end QubitCount
end Shor
