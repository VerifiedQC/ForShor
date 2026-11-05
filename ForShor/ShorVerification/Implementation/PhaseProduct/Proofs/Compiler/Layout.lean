import ForShor.ShorVerification.Implementation.PhaseProduct.Statement
import ForShor.ShorVerification.Framework.AbstractMachine.Gates
import ForShor.ShorVerification.Framework.AbstractMachine.LowGate
import ForShor.ShorVerification.Framework.Semantics.GateSemantics
import ForShor.ShorVerification.Framework.Semantics.LowGateSemantics
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Registers
import ForShor.ShorVerification.Framework.ToomCookTable
import Mathlib.Tactic

/-!
# Phase-Product Compiler: Layout

Chunk-to-register layout states (`LayoutState`), the top-heavy phase-splitting
parameters, the abstract `ExtReg` split interface (`PhaseSplitLayout`,
`Gate.PhaseProductLayout`), and the concrete growth/reserve bookkeeping used to
go from an initial split layout to a widened target layout
(`initSignedLayoutState`, `targetSignedLayoutState`, `growExtRegTo`,
`ExtReg.CanGrowTo`, `LayoutState.CanGrowToNeeds`, `ReserveBudget`).
-/

/-! ---------------------------------------------------------
    Phase-Product Compiler: Layout (moved from `Statement.lean`)
--------------------------------------------------------- -/

namespace Shor
open Gate
open Operations
open scoped BigOperators

/-! =========================================================
    Layout states and width bookkeeping
========================================================= -/

/-- Every slot has enough reserve to grow to common target width `W`. -/
def LayoutState.CanGrowTo {k : ℕ} (st : LayoutState k) (W : ℕ) : Prop :=
  (∀ i, (st.xslot i).CanGrow (W - (st.xslot i).width)) ∧ (∀ i, (st.zslot i).CanGrow (W - (st.zslot i).width))

/-- All owned qubits in the layout are pairwise separated across `x`, `z`, and cross slots. -/
def LayoutState.OwnedPairwiseDisjoint {k : ℕ} (st : LayoutState k) : Prop :=
  (∀ i j, i ≠ j → ExtReg.OwnedDisjoint (st.xslot i) (st.xslot j)) ∧
  (∀ i j, i ≠ j → ExtReg.OwnedDisjoint (st.zslot i) (st.zslot j)) ∧
  (∀ i j, ExtReg.OwnedDisjoint (st.xslot i) (st.zslot j))

/-! =========================================================
    Abstract `ExtReg` split interface
========================================================= -/

/-- Validity conditions for the top-heavy split of `parent` into `k` chunks of lower width `W`. -/
def ValidPhaseSplit (e : ExtReg) (k W : ℕ) : Prop :=
  0 < k ∧ (k - 1) * W ≤ e.width ∧ (e.width = 0 ∨ (k - 1) * W < e.width)

/-- The invariants of a split layout: the child reserves partition the parent
reserve, and distinct children own disjoint qubits. -/
structure PhaseSplitLayout.Valid {parent : ExtReg} {k W : ℕ} (layout : PhaseSplitLayout parent k W) :
    Prop where
  reserve_partition : (List.ofFn fun i => (layout.reserve i).qubits).flatten = parent.reserve.qubits
  child_owned_pairwise :
    ∀ i j, i ≠ j →
      List.Disjoint
        ((phaseChunkActive parent k W i).qubits ++ (layout.reserve i).qubits)
        ((phaseChunkActive parent k W j).qubits ++ (layout.reserve j).qubits)

theorem PhaseSplitLayout.child_owned_disjoint
    {parent : ExtReg}
    {k W : ℕ}
    {layout : PhaseSplitLayout parent k W}
    (hv : layout.Valid)
    {i j : Fin k}
    (hij : i ≠ j) :
    ExtReg.OwnedDisjoint (layout.child i) (layout.child j) := by
  simpa [PhaseSplitLayout.child, ExtReg.OwnedDisjoint, ExtReg.ownedQubits]
    using hv.child_owned_pairwise i j hij

/-- The invariants of a phase-product layout: both splits are valid, and every
`x` child is disjoint from every `z` child. -/
structure Gate.PhaseProductLayout.Valid {x z : ExtReg} {k : ℕ} (layout : Gate.PhaseProductLayout x z k) :
    Prop where
  xSplit : layout.xSplit.Valid
  zSplit : layout.zSplit.Valid
  cross_owned_disjoint : ∀ i j, ExtReg.OwnedDisjoint (layout.xSplit.child i) (layout.zSplit.child j)

/-- The reserve has enough bits for `growExtRegTo e W`. -/
def ExtReg.CanGrowTo (e : ExtReg) (W : ℕ) : Prop := e.CanGrow (W - e.width)

theorem width_growExtRegTo (e : ExtReg) (W : ℕ) (hle : e.width ≤ W) (hcap : e.CanGrowTo W) :
    (growExtRegTo e W).width = W := by
  unfold growExtRegTo ExtReg.CanGrowTo at *
  rw [ExtReg.width_grow e (W - e.width) hcap]
  omega

theorem initSignedLayoutState_owned_disjoint
    {x z : ExtReg} {k : ℕ} {layout : Gate.PhaseProductLayout x z k} (hv : layout.Valid) :
    (initSignedLayoutState layout).OwnedPairwiseDisjoint := by
  constructor
  · intro i j hij
    exact PhaseSplitLayout.child_owned_disjoint hv.xSplit hij
  constructor
  · intro i j hij
    exact PhaseSplitLayout.child_owned_disjoint hv.zSplit hij
  · intro i j
    exact hv.cross_owned_disjoint i j

/-- `src` has enough reserve to realize all scanned width needs. -/
def LayoutState.CanGrowToNeeds {k : ℕ} (src : LayoutState k) (need : NeededWidths k) : Prop := src.CanGrowTo (commonNeededWidth need)

/-- The top chunk of a valid top-heavy split has positive width when the parent does. -/
lemma phaseLimbWidth_top_nonempty (w other k : ℕ) (hk : 0 < k) :
    w = 0 ∨ (k - 1) * min (w / k) (other / k) < w := by
  by_cases hw : w = 0
  · exact Or.inl hw
  right
  have hwpos : 0 < w := Nat.pos_of_ne_zero hw
  let q := w / k
  have hW : min (w / k) (other / k) ≤ q := Nat.min_le_left _ _
  have hleft : (k - 1) * min (w / k) (other / k) ≤ (k - 1) * q := Nat.mul_le_mul_left _ hW
  have hkpred : k - 1 < k := by omega
  by_cases hq : q = 0
  · have hmin_zero : min (w / k) (other / k) = 0 := Nat.eq_zero_of_le_zero (by simpa [hq] using hW)
    simp [hmin_zero]
    exact hwpos
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
    have hstrict : (k - 1) * q < k * q := Nat.mul_lt_mul_of_pos_right hkpred hqpos
    have hdiv : k * q ≤ w := by
      dsimp [q]
      simpa [Nat.mul_comm] using Nat.div_mul_le_self w k
    exact lt_of_le_of_lt hleft (lt_of_lt_of_le hstrict hdiv)

lemma phaseLimbWidth_valid_left (x z : ExtReg) {k : ℕ} (hk : 0 < k) :
    ValidPhaseSplit x k (phaseLimbWidth x z k) := by
  refine ⟨hk, ?_, ?_⟩
  · unfold phaseLimbWidth
    have hW : min (x.width / k) (z.width / k) ≤ x.width / k := Nat.min_le_left _ _
    have h₁ : (k - 1) * min (x.width / k) (z.width / k) ≤ (k - 1) * (x.width / k) :=
      Nat.mul_le_mul_left _ hW
    have h₂ : (k - 1) * (x.width / k) ≤ k * (x.width / k) :=
      Nat.mul_le_mul_right _ (Nat.sub_le k 1)
    have h₃ : k * (x.width / k) ≤ x.width := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self x.width k
    exact h₁.trans (h₂.trans h₃)
  · unfold phaseLimbWidth
    exact phaseLimbWidth_top_nonempty x.width z.width k hk

lemma phaseLimbWidth_valid_right (x z : ExtReg) {k : ℕ} (hk : 0 < k) :
    ValidPhaseSplit z k (phaseLimbWidth x z k) := by
  refine ⟨hk, ?_, ?_⟩
  · unfold phaseLimbWidth
    have hW : min (x.width / k) (z.width / k) ≤ z.width / k := Nat.min_le_right _ _
    have h₁ : (k - 1) * min (x.width / k) (z.width / k) ≤ (k - 1) * (z.width / k) :=
      Nat.mul_le_mul_left _ hW
    have h₂ : (k - 1) * (z.width / k) ≤ k * (z.width / k) :=
      Nat.mul_le_mul_right _ (Nat.sub_le k 1)
    have h₃ : k * (z.width / k) ≤ z.width := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self z.width k
    exact h₁.trans (h₂.trans h₃)
  · unfold phaseLimbWidth
    simpa [Nat.min_comm] using phaseLimbWidth_top_nonempty z.width x.width k hk

end Shor

/-! ---------------------------------------------------------
    Chunk width, reconstruction, and disjointness proofs (moved from `Statement.lean`)
--------------------------------------------------------- -/

namespace Shor
open Gate
open Operations
open scoped BigOperators

/-- Length of a concrete `drop`/`take` slice that lies inside a register. -/
lemma regSize_drop_take_of_add_le (r : Reg) (start len : ℕ) (h : start + len ≤ regSize r) :
    regSize ((r.drop start).take len) = len := by
  change ((r.qubits.drop start).take len).length = len
  rw [List.length_take, List.length_drop]
  apply Nat.min_eq_left
  unfold regSize Reg.width at h
  omega

lemma phaseChunkActive_width (e : ExtReg) (k W : ℕ) (i : Fin k) (hvalid : ValidPhaseSplit e k W) :
    regSize (phaseChunkActive e k W i) = phaseSplitLogicalWidth e.width W k i := by
  obtain ⟨_hk, hbound, _htopNonempty⟩ := hvalid
  unfold phaseChunkActive
  by_cases htop : isTopChunk i
  · have hik : k - 1 = i.1 := by
      unfold isTopChunk at htop
      omega
    have hstart : i.1 * W ≤ e.width := by simpa [hik] using hbound
    apply regSize_drop_take_of_add_le
    simp only [phaseSplitLogicalWidth, htop, ite_eq_left]
    exact le_of_eq <| by
      calc
        i.1 * W + (e.width - i.1 * W) = e.width := Nat.add_sub_of_le hstart
        _ = regSize e.active := rfl
  · have hi : i.1 + 1 ≤ k - 1 := by
      unfold isTopChunk at htop
      have hle : i.1 + 1 ≤ k := Nat.succ_le_of_lt i.2
      omega
    have hmul : (i.1 + 1) * W ≤ (k - 1) * W := Nat.mul_le_mul_right W hi
    have hfit : i.1 * W + W ≤ e.width := by
      calc
        i.1 * W + W = (i.1 + 1) * W := by rw [Nat.add_mul]; simp
        _ ≤ (k - 1) * W := hmul
        _ ≤ e.width := hbound
    apply regSize_drop_take_of_add_le
    simpa [phaseSplitLogicalWidth, htop, ExtReg.width] using hfit

lemma PhaseSplitLayout.child_width {parent : ExtReg} {k W : ℕ} (layout : PhaseSplitLayout parent k W)
    (hvalid : ValidPhaseSplit parent k W) (i : Fin k) :
    (layout.child i).width = phaseSplitLogicalWidth parent.width W k i := by
  unfold PhaseSplitLayout.child ExtReg.width
  exact phaseChunkActive_width parent k W i hvalid

/-- The `x` children of a phase-product layout have their logical chunk widths. -/
lemma Gate.PhaseProductLayout.xchild_width {x z : ExtReg} {k : ℕ} (layout : Gate.PhaseProductLayout x z k)
    (i : Fin k) :
    (layout.xSplit.child i).width = phaseSplitLogicalWidth x.width (phaseLimbWidth x z k) k i :=
  layout.xSplit.child_width (phaseLimbWidth_valid_left x z (Fin.pos i)) i

/-- The `z` children of a phase-product layout have their logical chunk widths. -/
lemma Gate.PhaseProductLayout.zchild_width {x z : ExtReg} {k : ℕ} (layout : Gate.PhaseProductLayout x z k)
    (i : Fin k) :
    (layout.zSplit.child i).width = phaseSplitLogicalWidth z.width (phaseLimbWidth x z k) k i :=
  layout.zSplit.child_width (phaseLimbWidth_valid_right x z (Fin.pos i)) i

/-- Two consecutive-block slices of a `Nodup` list are disjoint whenever the
    first block ends no later than the second one starts. -/
theorem slice_disjoint {L : List ℕ} (hL : L.Nodup) {a b c d : ℕ} (h : b + a ≤ d) :
    (List.take a (List.drop b L)).Disjoint (List.take c (List.drop d L)) := by
  have e1 : List.take a (List.drop b L) = List.drop b (List.take (b + a) L) := by
    rw [List.drop_take]; congr 1; omega
  have sub1 : (List.take a (List.drop b L)).Sublist (List.take (b + a) L) := by
    rw [e1]; exact List.drop_sublist _ _
  have sub2 : (List.take c (List.drop d L)).Sublist (List.drop d L) :=
    List.take_sublist _ _
  have hdisj : (List.take (b + a) L).Disjoint (List.drop d L) :=
    List.disjoint_take_drop hL h
  exact List.disjoint_of_subset_left sub1.subset
    (List.disjoint_of_subset_right sub2.subset hdisj)

theorem phaseChunkActive_pairwise_disjoint
    (e : ExtReg)
    (k W : ℕ)
    (hvalid : ValidPhaseSplit e k W)
    {i j : Fin k}
    (hij : i ≠ j) :
    Disjoint (phaseChunkActive e k W i) (phaseChunkActive e k W j) := by
  obtain ⟨hk, hcap⟩ := hvalid
  have hL : e.active.qubits.Nodup := e.active.nodup
  have hijn : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
  have hik := i.2; have hjk := j.2
  rcases Nat.lt_or_gt_of_ne hijn with hlt | hgt
  · have hnotop : ¬ isTopChunk i := by unfold isTopChunk; omega
    have hsi : phaseSplitLogicalWidth e.width W k i = W := by
      simp [phaseSplitLogicalWidth, hnotop]
    have hexp : ((i : ℕ) + 1) * W = (i : ℕ) * W + W := by ring
    have h1 : ((i : ℕ) + 1) * W ≤ (j : ℕ) * W := Nat.mul_le_mul_right W (by omega)
    have key : (i : ℕ) * W + W ≤ (j : ℕ) * W := by omega
    simp only [Disjoint, phaseChunkActive, Reg.take, Reg.drop, hsi]
    exact slice_disjoint hL key
  · have hnotop : ¬ isTopChunk j := by unfold isTopChunk; omega
    have hsj : phaseSplitLogicalWidth e.width W k j = W := by
      simp [phaseSplitLogicalWidth, hnotop]
    have hexp : ((j : ℕ) + 1) * W = (j : ℕ) * W + W := by ring
    have h1 : ((j : ℕ) + 1) * W ≤ (i : ℕ) * W := Nat.mul_le_mul_right W (by omega)
    have key : (j : ℕ) * W + W ≤ (i : ℕ) * W := by omega
    simp only [Disjoint, phaseChunkActive, Reg.take, Reg.drop, hsj]
    exact (slice_disjoint hL key).symm

end Shor

namespace Shor
open Gate
open Operations
open scoped BigOperators

/-! =========================================================
    Abstract `ExtReg` split interface
========================================================= -/

/-- Interpret a child chunk as unsigned, except for the top chunk, which is signed. -/
def splitChunkInt {Basis : Type u} [RegEncoding Basis] {parent : ExtReg} {k W : ℕ}
    (layout : PhaseSplitLayout parent k W) (i : Fin k) (b : Basis) : ℤ :=
  if i.1 + 1 = k
    then tcDecodeWidth (parent.width - i.1 * W) ((layout.child i).toNat b)
    else (layout.child i).toNat b

/-! ---------------------------------------------------------
    Chunk width, reconstruction, and disjointness proofs
--------------------------------------------------------- -/

/-- Flattening `n` consecutive width-`W` blocks recovers the length-`n·W` prefix. -/
theorem flatten_blocks (L : List ℕ) (W : ℕ) : ∀ n : ℕ,
    (List.ofFn (n := n) fun i : Fin n => List.take W (List.drop (i.1 * W) L)).flatten
      = List.take (n * W) L := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.flatten_append]
    simp only [Fin.val_castSucc, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [ih]
    have hmul : (n + 1) * W = n * W + W := by ring
    have hlast : (Fin.last n).1 = n := rfl
    rw [hlast, hmul, List.take_add]

end Shor
