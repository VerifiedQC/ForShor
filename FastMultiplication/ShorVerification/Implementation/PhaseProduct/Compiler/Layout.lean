import FastMultiplication.ShorVerification.Framework.AbstractMachine.Gates
import FastMultiplication.ShorVerification.Framework.AbstractMachine.LowGate
import FastMultiplication.ShorVerification.Framework.Semantics.GateSemantics
import FastMultiplication.ShorVerification.Framework.Semantics.LowGateSemantics
import FastMultiplication.ShorVerification.Implementation.Shared.Registers
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Core.Coverage
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

namespace Shor
open Gate
open Operations
open scoped BigOperators

/-! =========================================================
    Layout states and width bookkeeping
========================================================= -/

/-- Current chunk-to-register assignment for the paired `x` and `z` work arrays. -/
structure LayoutState (k : ℕ) where
  xslot : Fin k → ExtReg
  zslot : Fin k → ExtReg

/-- Every slot has enough reserve to grow to common target width `W`. -/
def LayoutState.CanGrowTo {k : ℕ} (st : LayoutState k) (W : ℕ) : Prop :=
  (∀ i, (st.xslot i).CanGrow (W - (st.xslot i).width)) ∧ (∀ i, (st.zslot i).CanGrow (W - (st.zslot i).width))

/-- All owned qubits in the layout are pairwise separated across `x`, `z`, and cross slots. -/
def LayoutState.OwnedPairwiseDisjoint {k : ℕ} (st : LayoutState k) : Prop :=
  (∀ i j, i ≠ j → ExtReg.OwnedDisjoint (st.xslot i) (st.xslot j)) ∧
  (∀ i j, i ≠ j → ExtReg.OwnedDisjoint (st.zslot i) (st.zslot j)) ∧
  (∀ i j, ExtReg.OwnedDisjoint (st.xslot i) (st.zslot j))

/-- Width bookkeeping only: current logical widths of each chunk. -/
structure WidthState (k : ℕ) where
  xw : Fin k → ℕ
  zw : Fin k → ℕ

/-- Symbolic width transition for one source operation. -/
def updateWidthState {k : ℕ} (st : WidthState k) : valid_ops k → WidthState k
  | .shiftL i n =>
      { xw := Function.update st.xw i (st.xw i + n)
        zw := Function.update st.zw i (st.zw i + n) }
  | .shiftR i n =>
      { xw := Function.update st.xw i (st.xw i - n)
        zw := Function.update st.zw i (st.zw i - n) }
  | .negate i =>
      { xw := Function.update st.xw i (st.xw i + 1)
        zw := Function.update st.zw i (st.zw i + 1) }
  | .addScaled dst src _negsrc sh =>
      let newX := 1 + max (st.xw dst) (st.xw src + sh)
      let newZ := 1 + max (st.zw dst) (st.zw src + sh)
      { xw := Function.update st.xw dst newX
        zw := Function.update st.zw dst newZ }
  | .phaseProduct _ =>
      st

/-- Per-slot maximum widths discovered by scanning the source program. -/
structure NeededWidths (k : ℕ) where
  xneed : Fin k → ℕ
  zneed : Fin k → ℕ

/-- Pointwise maximum of two width-demand records. -/
def mergeNeededWidths {k : ℕ} (a b : NeededWidths k) : NeededWidths k where
  xneed := fun i => max (a.xneed i) (b.xneed i)
  zneed := fun i => max (a.zneed i) (b.zneed i)

/-- Regard current widths as the current lower bound on needed widths. -/
def widthsOfState {k : ℕ} (st : WidthState k) : NeededWidths k where
  xneed := st.xw
  zneed := st.zw

/--
Lower-limb width for the top-heavy phase layout.
This deliberately uses floor division. The lower `k - 1` limbs have width `w / k`,
and the most significant limb absorbs all remaining bits.
For example, `w = 5`, `k = 4` gives widths `1, 1, 1, 2`.
-/
def phaseLimbWidthOfWidth (w k : ℕ) : ℕ := w / k

/--
Common radix width for decomposing both operands.
Use `min`, not `max`: the lower limbs must fit inside both operands.
The larger operand simply gets a larger top chunk.
-/
def phaseLimbWidth (x z : ExtReg) (k : ℕ) : ℕ :=
  min (phaseLimbWidthOfWidth x.width k) (phaseLimbWidthOfWidth z.width k)

/-! =========================================================
    Top-heavy phase splitting parameters
========================================================= -/

/-- The most significant chunk is the last chunk. -/
def isTopChunk {k : ℕ} (i : Fin k) : Prop := i.1 + 1 = k
instance {k : ℕ} (i : Fin k) : Decidable (isTopChunk i) := by
  unfold isTopChunk
  infer_instance

/-- Logical width of chunk `i`; the last chunk absorbs the remainder. -/
def phaseSplitLogicalWidth (w W k : ℕ) (i : Fin k) : ℕ := if isTopChunk i then w - i.1 * W else W

/-- Starting bit offset of chunk `i` in the parent active register. -/
def phaseChunkStart {k : ℕ} (W : ℕ) (i : Fin k) : ℕ := i.1 * W

/-- Concrete active register slice corresponding to chunk `i`. -/
def phaseChunkActive (e : ExtReg) (k W : ℕ) (i : Fin k) : Reg :=
  (e.active.drop (phaseChunkStart W i)).take (phaseSplitLogicalWidth e.width W k i)

/-! =========================================================
    Abstract `ExtReg` split interface
========================================================= -/

/-- Validity conditions for the top-heavy split of `parent` into `k` chunks of lower width `W`. -/
def ValidPhaseSplit (e : ExtReg) (k W : ℕ) : Prop :=
  0 < k ∧ (k - 1) * W ≤ e.width ∧ (e.width = 0 ∨ (k - 1) * W < e.width)

/-- Abstract split of one extendable register into active chunks plus a reserve partition. -/
structure PhaseSplitLayout (parent : ExtReg) (k W : ℕ) where
  valid : ValidPhaseSplit parent k W
  reserve : Fin k → Reg
  active_reserve_disjoint : ∀ i, Disjoint (phaseChunkActive parent k W i) (reserve i)
  reserve_partition : (List.ofFn fun i => (reserve i).qubits).flatten = parent.reserve.qubits
  child_owned_pairwise :
    ∀ i j, i ≠ j →
      List.Disjoint
        ((phaseChunkActive parent k W i).qubits ++ (reserve i).qubits)
        ((phaseChunkActive parent k W j).qubits ++ (reserve j).qubits)

/-- The `i`th child extendable register induced by a split layout. -/
def PhaseSplitLayout.child {parent : ExtReg} {k W : ℕ} (layout : PhaseSplitLayout parent k W)
    (i : Fin k) : ExtReg :=
  ExtReg.withReserve (phaseChunkActive parent k W i) (layout.reserve i) (layout.active_reserve_disjoint i)

theorem PhaseSplitLayout.child_owned_disjoint
    {parent : ExtReg}
    {k W : ℕ}
    (layout : PhaseSplitLayout parent k W)
    {i j : Fin k}
    (hij : i ≠ j) :
    ExtReg.OwnedDisjoint (layout.child i) (layout.child j) := by
  simpa [PhaseSplitLayout.child, ExtReg.OwnedDisjoint, ExtReg.ownedQubits]
    using layout.child_owned_pairwise i j hij

/-- Pair of compatible split layouts for the two operands of a phase product. -/
structure Gate.PhaseProductLayout (x z : ExtReg) (k : ℕ) where
  xSplit : PhaseSplitLayout x k (phaseLimbWidth x z k)
  zSplit : PhaseSplitLayout z k (phaseLimbWidth x z k)
  cross_owned_disjoint : ∀ i j, ExtReg.OwnedDisjoint (xSplit.child i) (zSplit.child j)

/-- Interpret a child chunk as unsigned, except for the top chunk, which is signed. -/
def splitChunkInt {Basis : Type u} [RegEncoding Basis] {parent : ExtReg} {k W : ℕ}
    (layout : PhaseSplitLayout parent k W) (i : Fin k) (b : Basis) : ℤ :=
  if i.1 + 1 = k
    then tcDecodeWidth (parent.width - i.1 * W) ((layout.child i).toNat b)
    else (layout.child i).toNat b

/-- Uniform target width chosen to dominate every scanned `x` and `z` need, plus a sign bit. -/
def commonNeededWidth {k : ℕ} (need : NeededWidths k) : ℕ :=
  1 + Finset.univ.sup (fun i : Fin k => max (need.xneed i) (need.zneed i))

/-- Number of high bits added when growing `src` into `dst`. -/
def extraDelta (src dst : ExtReg) : ℕ := dst.width - src.width

/-- Grow an extendable register just enough to reach target width `W`. -/
def growExtRegTo (e : ExtReg) (W : ℕ) : ExtReg := e.grow (W - e.width)

/-- The reserve has enough bits for `growExtRegTo e W`. -/
def ExtReg.CanGrowTo (e : ExtReg) (W : ℕ) : Prop := e.CanGrow (W - e.width)

theorem width_growExtRegTo (e : ExtReg) (W : ℕ) (hle : e.width ≤ W) (hcap : e.CanGrowTo W) :
    (growExtRegTo e W).width = W := by
  unfold growExtRegTo ExtReg.CanGrowTo at *
  rw [ExtReg.width_grow e (W - e.width) hcap]
  omega

/-- Initial signed compiler layout obtained by taking the split children as slots. -/
def initSignedLayoutState {x z : ExtReg} {k : ℕ} (layout : Gate.PhaseProductLayout x z k) : LayoutState k :=
  { xslot := fun i => layout.xSplit.child i, zslot := fun i => layout.zSplit.child i }

theorem initSignedLayoutState_owned_disjoint
    {x z : ExtReg} {k : ℕ} (layout : Gate.PhaseProductLayout x z k) :
    (initSignedLayoutState layout).OwnedPairwiseDisjoint := by
  constructor
  · intro i j hij
    exact layout.xSplit.child_owned_disjoint hij
  constructor
  · intro i j hij
    exact layout.zSplit.child_owned_disjoint hij
  · intro i j
    exact layout.cross_owned_disjoint i j

/-- Final widened chunk views for the compiled signed body.
Each final slot is obtained by widening the corresponding abstract initial
split chunk. No concrete register splitting is used here.
-/
def targetSignedLayoutState {k : ℕ} (src : LayoutState k) (need : NeededWidths k) : LayoutState k :=
  let Wwork := commonNeededWidth need
  { xslot := fun i => growExtRegTo (src.xslot i) Wwork, zslot := fun i => growExtRegTo (src.zslot i) Wwork }

/-- `src` has enough reserve to realize all scanned width needs. -/
def LayoutState.CanGrowToNeeds {k : ℕ} (src : LayoutState k) (need : NeededWidths k) : Prop := src.CanGrowTo (commonNeededWidth need)

/-- Partition of a parent reserve into `k` child reserve sizes. -/
structure ReserveBudget (parent : ExtReg) (k : ℕ) where
  size : Fin k → ℕ
  total : (List.ofFn size).sum = parent.capacity

/-- Starting reserve offset for child `i`. -/
def ReserveBudget.offset {parent : ExtReg} {k : ℕ} (budget : ReserveBudget parent k) (i : Fin k) : ℕ :=
  ((List.ofFn budget.size).take i.1).sum

/-- Concrete reserve slice assigned to child `i`. -/
def ReserveBudget.childReserve {parent : ExtReg} {k : ℕ} (budget : ReserveBudget parent k) (i : Fin k) : Reg :=
  (parent.reserve.drop (budget.offset i)).take (budget.size i)

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
  · unfold phaseLimbWidth phaseLimbWidthOfWidth
    have hW : min (x.width / k) (z.width / k) ≤ x.width / k := Nat.min_le_left _ _
    have h₁ : (k - 1) * min (x.width / k) (z.width / k) ≤ (k - 1) * (x.width / k) :=
      Nat.mul_le_mul_left _ hW
    have h₂ : (k - 1) * (x.width / k) ≤ k * (x.width / k) :=
      Nat.mul_le_mul_right _ (Nat.sub_le k 1)
    have h₃ : k * (x.width / k) ≤ x.width := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self x.width k
    exact h₁.trans (h₂.trans h₃)
  · unfold phaseLimbWidth phaseLimbWidthOfWidth
    exact phaseLimbWidth_top_nonempty x.width z.width k hk

lemma phaseLimbWidth_valid_right (x z : ExtReg) {k : ℕ} (hk : 0 < k) :
    ValidPhaseSplit z k (phaseLimbWidth x z k) := by
  refine ⟨hk, ?_, ?_⟩
  · unfold phaseLimbWidth phaseLimbWidthOfWidth
    have hW : min (x.width / k) (z.width / k) ≤ z.width / k := Nat.min_le_right _ _
    have h₁ : (k - 1) * min (x.width / k) (z.width / k) ≤ (k - 1) * (z.width / k) :=
      Nat.mul_le_mul_left _ hW
    have h₂ : (k - 1) * (z.width / k) ≤ k * (z.width / k) :=
      Nat.mul_le_mul_right _ (Nat.sub_le k 1)
    have h₃ : k * (z.width / k) ≤ z.width := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self z.width k
    exact h₁.trans (h₂.trans h₃)
  · unfold phaseLimbWidth phaseLimbWidthOfWidth
    simpa [Nat.min_comm] using phaseLimbWidth_top_nonempty z.width x.width k hk

/-! ---------------------------------------------------------
    Chunk width, reconstruction, and disjointness proofs
--------------------------------------------------------- -/

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
    simp only [phaseChunkStart, phaseSplitLogicalWidth, htop, if_pos]
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
    simpa [phaseChunkStart, phaseSplitLogicalWidth, htop] using hfit

lemma PhaseSplitLayout.child_width {parent : ExtReg} {k W : ℕ} (layout : PhaseSplitLayout parent k W)
    (i : Fin k) :
    (layout.child i).width = phaseSplitLogicalWidth parent.width W k i := by
  unfold PhaseSplitLayout.child ExtReg.width
  exact phaseChunkActive_width parent k W i layout.valid

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
    simp only [Disjoint, phaseChunkActive, phaseChunkStart, Reg.take, Reg.drop, hsi]
    exact slice_disjoint hL key
  · have hnotop : ¬ isTopChunk j := by unfold isTopChunk; omega
    have hsj : phaseSplitLogicalWidth e.width W k j = W := by
      simp [phaseSplitLogicalWidth, hnotop]
    have hexp : ((j : ℕ) + 1) * W = (j : ℕ) * W + W := by ring
    have h1 : ((j : ℕ) + 1) * W ≤ (i : ℕ) * W := Nat.mul_le_mul_right W (by omega)
    have key : (j : ℕ) * W + W ≤ (i : ℕ) * W := by omega
    simp only [Disjoint, phaseChunkActive, phaseChunkStart, Reg.take, Reg.drop, hsj]
    exact (slice_disjoint hL key).symm

end Shor
