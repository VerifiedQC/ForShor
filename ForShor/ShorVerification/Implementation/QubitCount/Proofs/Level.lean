import ForShor.ShorVerification.Implementation.QubitCount.Proofs.GateWalk
import ForShor.ShorVerification.Implementation.QubitCount.Proofs.Budgets
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.Allocation

/-!
# Qubit count: one level of the phase-product recursion

A recursive level of the phase product grows each of its `k` chunk pairs from
its own slice of the parent reserves, runs the arithmetic body with a phase
product on every interpolation point, and returns the grown qubits. With the
phase products left opaque, this file shows that the level returns the live
set it started from, and that its peak is the starting size, plus the qubits
the growth activates, plus one child's cost if there is a child at all.
-/

namespace Shor
namespace QubitCount

open Gate Operations

/-! ## Single chunks -/

section Chunk

variable {k : ℕ} (ex : ExtReg → ExtReg → ℕ) (n : ℕ)

lemma alloc_chunk (i : Fin k) (s t : ExtReg) (L : Finset ℕ) :
    gAfter (allocChunkGate i s t) L = L ∪ allocBits s (extraDelta s t) ∧
    gPeak ex (allocChunkGate i s t) L = (L ∪ allocBits s (extraDelta s t)).card ∧
    (_root_.Disjoint (allocBits s (extraDelta s t)) L → gGood n (allocChunkGate i s t) L) := by
  unfold allocChunkGate
  dsimp only
  split_ifs with h0 htop
  · simp [gAfter, gPeak, gGood, h0]
  · refine ⟨rfl, ?_, fun h => ?_⟩
    · simp only [gPeak, gPrim, peak, move_true]
      exact max_eq_right (Finset.card_le_card Finset.subset_union_left)
    · simpa [gGood, gPrim, WellFormed] using h
  · refine ⟨rfl, ?_, fun h => ?_⟩
    · simp only [gPeak, gPrim, peak, move_true]
      exact max_eq_right (Finset.card_le_card Finset.subset_union_left)
    · simpa [gGood, gPrim, WellFormed] using h

lemma dealloc_chunk (i : Fin k) (s t : ExtReg) (L : Finset ℕ) :
    gAfter (deallocChunkGate i s t) L = L \ allocBits s (extraDelta s t) ∧
    gPeak ex (deallocChunkGate i s t) L = L.card ∧
    (allocBits s (extraDelta s t) ⊆ L → gGood n (deallocChunkGate i s t) L) := by
  unfold deallocChunkGate
  dsimp only
  split_ifs with h0 htop
  · simp [gAfter, gPeak, gGood, h0]
  · refine ⟨rfl, ?_, fun h => ?_⟩
    · simp only [gPeak, gPrim, peak, Bool.not_true, move_false]
      exact max_eq_left (Finset.card_le_card Finset.sdiff_subset)
    · simpa [gGood, gPrim, WellFormed] using h
  · refine ⟨rfl, ?_, fun h => ?_⟩
    · simp only [gPeak, gPrim, peak, Bool.not_true, move_false]
      exact max_eq_left (Finset.card_le_card Finset.sdiff_subset)
    · simpa [gGood, gPrim, WellFormed] using h

end Chunk

/-! ## The allocation and deallocation folds -/

section Folds

variable {k : ℕ} (src dst : LayoutState k)

/-- The qubits the allocation of chunk `i` activates on the `x` side. -/
def bitsX (i : Fin k) : Finset ℕ :=
  allocBits (src.xslot i) (extraDelta (src.xslot i) (dst.xslot i))

/-- The qubits the allocation of chunk `i` activates on the `z` side. -/
def bitsZ (i : Fin k) : Finset ℕ :=
  allocBits (src.zslot i) (extraDelta (src.zslot i) (dst.zslot i))

/-- The qubits the first `j` chunk allocations activate. -/
def allocSet (j : ℕ) : Finset ℕ :=
  (Finset.univ.filter (fun i : Fin k => i.1 < j)).biUnion
    (fun i => bitsX src dst i ∪ bitsZ src dst i)

lemma mem_allocSet {j : ℕ} {q : ℕ} :
    q ∈ allocSet src dst j ↔ ∃ i : Fin k, i.1 < j ∧ (q ∈ bitsX src dst i ∨ q ∈ bitsZ src dst i) := by
  simp [allocSet, Finset.mem_biUnion]

lemma allocSet_succ {j : ℕ} (hj : j < k) :
    allocSet src dst (j + 1)
      = allocSet src dst j ∪ (bitsX src dst ⟨j, hj⟩ ∪ bitsZ src dst ⟨j, hj⟩) := by
  ext q
  simp only [mem_allocSet, Finset.mem_union]
  constructor
  · rintro ⟨i, hi, hq⟩
    by_cases hij : i.1 < j
    · exact Or.inl ⟨i, hij, hq⟩
    · have : i = ⟨j, hj⟩ := Fin.ext (by simp only; omega)
      subst this
      exact Or.inr hq
  · rintro (⟨i, hi, hq⟩ | hq)
    · exact ⟨i, by omega, hq⟩
    · exact ⟨⟨j, hj⟩, by simp, hq⟩

/-- The chunk allocations activate pairwise disjoint sets of non-live qubits. -/
structure FreshBits (L : Finset ℕ) : Prop where
  x_fresh : ∀ i, _root_.Disjoint (bitsX src dst i) L
  z_fresh : ∀ i, _root_.Disjoint (bitsZ src dst i) L
  xz : ∀ i j, _root_.Disjoint (bitsX src dst i) (bitsZ src dst j)
  xx : ∀ i j, i ≠ j → _root_.Disjoint (bitsX src dst i) (bitsX src dst j)
  zz : ∀ i j, i ≠ j → _root_.Disjoint (bitsZ src dst i) (bitsZ src dst j)

variable {src dst}

lemma FreshBits.x_allocSet {L : Finset ℕ} (h : FreshBits src dst L) {j : ℕ} (hj : j < k) :
    _root_.Disjoint (bitsX src dst ⟨j, hj⟩) (L ∪ allocSet src dst j) := by
  rw [Finset.disjoint_union_right]
  refine ⟨h.x_fresh _, ?_⟩
  rw [Finset.disjoint_right]
  intro q hq hx
  obtain ⟨i, hi, hq'⟩ := (mem_allocSet src dst).mp hq
  have hne : i ≠ ⟨j, hj⟩ := fun e => by subst e; simp at hi
  rcases hq' with hq' | hq'
  · exact Finset.disjoint_left.mp (h.xx _ _ hne.symm) hx hq'
  · exact Finset.disjoint_left.mp (h.xz _ _) hx hq'

lemma FreshBits.z_allocSet {L : Finset ℕ} (h : FreshBits src dst L) {j : ℕ} (hj : j < k) :
    _root_.Disjoint (bitsZ src dst ⟨j, hj⟩)
      (L ∪ allocSet src dst j ∪ bitsX src dst ⟨j, hj⟩) := by
  rw [Finset.disjoint_union_right, Finset.disjoint_union_right]
  refine ⟨⟨h.z_fresh _, ?_⟩, (h.xz _ _).symm⟩
  rw [Finset.disjoint_right]
  intro q hq hz
  obtain ⟨i, hi, hq'⟩ := (mem_allocSet src dst).mp hq
  have hne : i ≠ ⟨j, hj⟩ := fun e => by subst e; simp at hi
  rcases hq' with hq' | hq'
  · exact Finset.disjoint_left.mp (h.xz _ _) hq' hz
  · exact Finset.disjoint_left.mp (h.zz _ _ hne.symm) hz hq'

/-- The first `j` allocations activate exactly their chunks' qubits, and the
live set only grows while they run. -/
theorem allocs_walk (ex : ExtReg → ExtReg → ℕ) (n : ℕ) {L : Finset ℕ}
    (hfresh : FreshBits src dst L) :
    ∀ (j : ℕ) (hj : j ≤ k),
      gAfter (compileSignedAllocationsAux src dst j hj) L = L ∪ allocSet src dst j ∧
      gPeak ex (compileSignedAllocationsAux src dst j hj) L = (L ∪ allocSet src dst j).card ∧
      gGood n (compileSignedAllocationsAux src dst j hj) L := by
  intro j
  induction j with
  | zero =>
      intro hj
      simp [compileSignedAllocationsAux, gAfter, gPeak, gGood, allocSet]
  | succ j ih =>
      intro hj
      have hjk : j < k := hj
      obtain ⟨a1, p1, g1⟩ := ih (Nat.le_of_lt hjk)
      obtain ⟨ax, px, gx⟩ := alloc_chunk ex n (⟨j, hjk⟩ : Fin k)
        (src.xslot ⟨j, hjk⟩) (dst.xslot ⟨j, hjk⟩) (L ∪ allocSet src dst j)
      obtain ⟨az, pz, gz⟩ := alloc_chunk ex n (⟨j, hjk⟩ : Fin k)
        (src.zslot ⟨j, hjk⟩) (dst.zslot ⟨j, hjk⟩)
        (L ∪ allocSet src dst j ∪ bitsX src dst ⟨j, hjk⟩)
      have hset : L ∪ allocSet src dst (j + 1)
          = L ∪ allocSet src dst j ∪ bitsX src dst ⟨j, hjk⟩ ∪ bitsZ src dst ⟨j, hjk⟩ := by
        rw [allocSet_succ src dst hjk]; simp only [Finset.union_assoc]
      have hfx := hfresh.x_allocSet hjk
      have hfz := hfresh.z_allocSet hjk
      simp only [bitsX, bitsZ] at hset hfx hfz az pz gz
      simp only [compileSignedAllocationsAux, gAfter, gPeak, gGood]
      rw [a1, ax, az, hset, p1, px, pz]
      refine ⟨rfl, ?_, g1, gx hfx, gz hfz⟩
      have h1 := Finset.card_le_card (Finset.subset_union_left (s₁ := L ∪ allocSet src dst j)
        (s₂ := allocBits (src.xslot ⟨j, hjk⟩) (extraDelta (src.xslot ⟨j, hjk⟩)
          (dst.xslot ⟨j, hjk⟩))))
      have h2 := Finset.card_le_card (Finset.subset_union_left
        (s₁ := L ∪ allocSet src dst j ∪ allocBits (src.xslot ⟨j, hjk⟩)
          (extraDelta (src.xslot ⟨j, hjk⟩) (dst.xslot ⟨j, hjk⟩)))
        (s₂ := allocBits (src.zslot ⟨j, hjk⟩) (extraDelta (src.zslot ⟨j, hjk⟩)
          (dst.zslot ⟨j, hjk⟩))))
      omega

/-- The deallocations of the first `j` chunks return what their allocations
activated, and the live set only shrinks while they run. -/
theorem deallocs_walk (ex : ExtReg → ExtReg → ℕ) (n : ℕ) {L : Finset ℕ}
    (hfresh : FreshBits src dst L) :
    ∀ (j : ℕ) (hj : j ≤ k),
      gAfter (compileSignedDeallocationsAux src dst j hj) (L ∪ allocSet src dst j) = L ∧
      gPeak ex (compileSignedDeallocationsAux src dst j hj) (L ∪ allocSet src dst j)
        = (L ∪ allocSet src dst j).card ∧
      gGood n (compileSignedDeallocationsAux src dst j hj) (L ∪ allocSet src dst j) := by
  intro j
  induction j with
  | zero =>
      intro hj
      simp [compileSignedDeallocationsAux, gAfter, gPeak, gGood, allocSet]
  | succ j ih =>
      intro hj
      have hjk : j < k := hj
      obtain ⟨a1, p1, g1⟩ := ih (Nat.le_of_lt hjk)
      have hset : L ∪ allocSet src dst (j + 1)
          = L ∪ allocSet src dst j ∪ bitsX src dst ⟨j, hjk⟩ ∪ bitsZ src dst ⟨j, hjk⟩ := by
        rw [allocSet_succ src dst hjk]; simp only [Finset.union_assoc]
      have hzS : (L ∪ allocSet src dst j ∪ bitsX src dst ⟨j, hjk⟩ ∪ bitsZ src dst ⟨j, hjk⟩)
          \ bitsZ src dst ⟨j, hjk⟩ = L ∪ allocSet src dst j ∪ bitsX src dst ⟨j, hjk⟩ :=
        Finset.union_sdiff_cancel_right (hfresh.z_allocSet hjk).symm
      have hxS : (L ∪ allocSet src dst j ∪ bitsX src dst ⟨j, hjk⟩) \ bitsX src dst ⟨j, hjk⟩
          = L ∪ allocSet src dst j :=
        Finset.union_sdiff_cancel_right (hfresh.x_allocSet hjk).symm
      obtain ⟨az, pz, gz⟩ := dealloc_chunk ex n (⟨j, hjk⟩ : Fin k)
        (src.zslot ⟨j, hjk⟩) (dst.zslot ⟨j, hjk⟩)
        (L ∪ allocSet src dst j ∪ bitsX src dst ⟨j, hjk⟩ ∪ bitsZ src dst ⟨j, hjk⟩)
      obtain ⟨ax, px, gx⟩ := dealloc_chunk ex n (⟨j, hjk⟩ : Fin k)
        (src.xslot ⟨j, hjk⟩) (dst.xslot ⟨j, hjk⟩) (L ∪ allocSet src dst j ∪ bitsX src dst ⟨j, hjk⟩)
      simp only [bitsX, bitsZ] at hset hzS hxS az pz gz ax px gx
      rw [hset]
      simp only [compileSignedDeallocationsAux, gAfter, gPeak, gGood]
      rw [az, hzS, ax, hxS, a1, pz, px, p1]
      refine ⟨rfl, ?_, gz Finset.subset_union_right, gx Finset.subset_union_right, g1⟩
      have h1 := Finset.card_le_card (Finset.subset_union_left (s₁ := L ∪ allocSet src dst j)
        (s₂ := allocBits (src.xslot ⟨j, hjk⟩) (extraDelta (src.xslot ⟨j, hjk⟩)
          (dst.xslot ⟨j, hjk⟩))))
      have h2 := Finset.card_le_card (Finset.subset_union_left
        (s₁ := L ∪ allocSet src dst j ∪ allocBits (src.xslot ⟨j, hjk⟩)
          (extraDelta (src.xslot ⟨j, hjk⟩) (dst.xslot ⟨j, hjk⟩)))
        (s₂ := allocBits (src.zslot ⟨j, hjk⟩) (extraDelta (src.zslot ⟨j, hjk⟩)
          (dst.zslot ⟨j, hjk⟩))))
      omega

/-- The full allocation activates `Σᵢ (|bitsX i| + |bitsZ i|)` qubits. -/
lemma card_allocSet {L : Finset ℕ} (hfresh : FreshBits src dst L) :
    (L ∪ allocSet src dst k).card
      = L.card + (∑ i, (bitsX src dst i).card + ∑ i, (bitsZ src dst i).card) := by
  have hall : allocSet src dst k
      = Finset.univ.biUnion (fun i => bitsX src dst i ∪ bitsZ src dst i) := by
    simp [allocSet]
  have hpair : (↑(Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint
      (fun i => bitsX src dst i ∪ bitsZ src dst i) := by
    intro i _ j _ hij
    simp only [Function.onFun]
    rw [Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right]
    exact ⟨⟨hfresh.xx i j hij, hfresh.xz i j⟩, ⟨(hfresh.xz j i).symm, hfresh.zz i j hij⟩⟩
  have hdisj : _root_.Disjoint L (allocSet src dst k) := by
    rw [Finset.disjoint_right]
    intro q hq hL
    obtain ⟨i, _, hq'⟩ := (mem_allocSet src dst).mp hq
    rcases hq' with hq' | hq'
    · exact Finset.disjoint_left.mp (hfresh.x_fresh i) hq' hL
    · exact Finset.disjoint_left.mp (hfresh.z_fresh i) hq' hL
  rw [Finset.card_union_of_disjoint hdisj, hall, Finset.card_biUnion hpair,
    ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact Finset.card_union_of_disjoint (hfresh.xz i i)

end Folds

/-! ## The arithmetic body -/

section Body

variable {k : ℕ}

lemma max_max_add (a c : ℕ) : max a (max a (a + c)) = a + c := by
  rw [max_eq_right (Nat.le_add_right a c), max_eq_right (Nat.le_add_right a c)]

lemma max_body (a c A B : ℕ) : max (a + c) (max (a + c) (a + max A B)) = a + max A (max c B) := by
  omega

lemma max_leaf (a e A B : ℕ) (hA : A ≤ e) : max (a + e) (a + max A B) = a + max e (max 0 B) := by
  omega

/-- Whether an annotated program emits at least one phase product. -/
def hasLeaf : List (AnnotatedOp k) → Bool
  | [] => false
  | ⟨.phaseProduct _, some _⟩ :: _ => true
  | _ :: rest => hasLeaf rest

@[simp] lemma hasLeaf_nil : hasLeaf ([] : List (AnnotatedOp k)) = false := rfl
@[simp] lemma hasLeaf_shiftL (i : Fin k) (m : ℕ) (t : Option (Fin (q k))) (rest) :
    hasLeaf (⟨.shiftL i m, t⟩ :: rest) = hasLeaf rest := rfl
@[simp] lemma hasLeaf_shiftR (i : Fin k) (m : ℕ) (t : Option (Fin (q k))) (rest) :
    hasLeaf (⟨.shiftR i m, t⟩ :: rest) = hasLeaf rest := rfl
@[simp] lemma hasLeaf_negate (i : Fin k) (t : Option (Fin (q k))) (rest) :
    hasLeaf (⟨.negate i, t⟩ :: rest) = hasLeaf rest := rfl
@[simp] lemma hasLeaf_addScaled (d s : Fin k) (b : Bool) (m : ℕ) (t : Option (Fin (q k)))
    (rest) : hasLeaf (⟨.addScaled d s b m, t⟩ :: rest) = hasLeaf rest := rfl
@[simp] lemma hasLeaf_pp_none (i : Fin k) (rest) :
    hasLeaf (⟨.phaseProduct i, none⟩ :: rest) = hasLeaf rest := rfl
@[simp] lemma hasLeaf_pp_some (i : Fin k) (l : Fin (q k)) (rest) :
    hasLeaf (⟨.phaseProduct i, some l⟩ :: rest) = true := rfl

/-- The largest scratch the arithmetic of an annotated program charges, on
chunks of width `W`. -/
def annScratch (W : ℕ) : List (AnnotatedOp k) → ℕ
  | [] => 0
  | a :: rest => max (Policy.opScratch a.op W) (annScratch W rest)

lemma annScratch_annotate (W : ℕ) :
    ∀ (ops : List (valid_ops k)) (m : ℕ),
      annScratch W (annotatePhaseTermsAux k m ops) = Policy.opsScratch ops W := by
  intro ops
  induction ops with
  | nil => intro m; rfl
  | cons op rest ih =>
      intro m
      cases op <;> simp [annotatePhaseTermsAux, annScratch, Policy.opsScratch, ih]

/-- The body leaves the live set alone; its peak is the larger of one child's
cost, if it has a child at all, and its arithmetic's scratch. -/
theorem body_walk (hk : 1 < k) (phi : Angle) (coeff : Fin (q k) → ℚ) (st : LayoutState k)
    (ex : ExtReg → ExtReg → ℕ) (e n : ℕ) (L : Finset ℕ)
    (hact : ∀ i, regQubitSet (st.xslot i).active ⊆ L ∧ regQubitSet (st.zslot i).active ⊆ L)
    (hpp : ∀ i, PPGood n (st.xslot i) (st.zslot i) L)
    (hex : ∀ i, ex (st.xslot i) (st.zslot i) = e) {W : ℕ}
    (hW : ∀ i, (st.xslot i).width = W ∧ (st.zslot i).width = W) :
    ∀ ops : List (AnnotatedOp k),
      gAfter (compileAnnotatedOpsToSignedGateAux k hk phi coeff st ops) L = L ∧
      gPeak ex (compileAnnotatedOpsToSignedGateAux k hk phi coeff st ops) L
        = L.card + max (if hasLeaf ops then e else 0) (annScratch W ops) ∧
      gGood n (compileAnnotatedOpsToSignedGateAux k hk phi coeff st ops) L := by
  have touch : ∀ u : LowGate, TouchIn L u →
      after u true L = L ∧ peak scratch u true L = L.card + tmax scratch u ∧ WellFormed u true L :=
    fun u hu => touch_walk_anc scratch L u hu true
  intro ops
  induction ops with
  | nil => simp [compileAnnotatedOpsToSignedGateAux, gAfter, gPeak, gGood, hasLeaf, annScratch]
  | cons a rest ih =>
      obtain ⟨op, term?⟩ := a
      obtain ⟨ia, ip, ig⟩ := ih
      cases op with
      | shiftL i m =>
          obtain ⟨a1, p1, w1⟩ := touch (.ShiftL (st.xslot i) m) (hact i).1
          obtain ⟨a2, p2, w2⟩ := touch (.ShiftL (st.zslot i) m) (hact i).2
          simp only [compileAnnotatedOpsToSignedGateAux, gAfter, gPeak, gGood, gPrim, hasLeaf_shiftL]
          rw [a1, a2, ia, p1, p2, ip]
          refine ⟨rfl, ?_, w1, w2, ig⟩
          simp only [annScratch, tmax_ShiftL, scratch_ShiftL, Policy.opScratch]
          exact max_body _ _ _ _
      | shiftR i m =>
          obtain ⟨a1, p1, w1⟩ := touch (.ShiftR (st.xslot i) m) (hact i).1
          obtain ⟨a2, p2, w2⟩ := touch (.ShiftR (st.zslot i) m) (hact i).2
          simp only [compileAnnotatedOpsToSignedGateAux, gAfter, gPeak, gGood, gPrim, hasLeaf_shiftR]
          rw [a1, a2, ia, p1, p2, ip]
          refine ⟨rfl, ?_, w1, w2, ig⟩
          simp only [annScratch, tmax_ShiftR, scratch_ShiftR, Policy.opScratch]
          exact max_body _ _ _ _
      | negate i =>
          obtain ⟨a1, p1, w1⟩ := touch (.Negate (st.xslot i)) (hact i).1
          obtain ⟨a2, p2, w2⟩ := touch (.Negate (st.zslot i)) (hact i).2
          simp only [compileAnnotatedOpsToSignedGateAux, gAfter, gPeak, gGood, gPrim, hasLeaf_negate]
          rw [a1, a2, ia, p1, p2, ip]
          refine ⟨rfl, ?_, w1, w2, ig⟩
          simp only [annScratch, tmax_Negate, scratch_Negate, (hW i).1, (hW i).2, Policy.opScratch]
          exact max_body _ _ _ _
      | addScaled d s b m =>
          obtain ⟨a1, p1, w1⟩ := touch (.AddScaled (st.xslot d) (st.xslot s) b m)
            (Finset.union_subset (hact d).1 (hact s).1)
          obtain ⟨a2, p2, w2⟩ := touch (.AddScaled (st.zslot d) (st.zslot s) b m)
            (Finset.union_subset (hact d).2 (hact s).2)
          simp only [compileAnnotatedOpsToSignedGateAux, gAfter, gPeak, gGood, gPrim, hasLeaf_addScaled]
          rw [a1, a2, ia, p1, p2, ip]
          refine ⟨rfl, ?_, w1, w2, ig⟩
          simp only [annScratch, tmax_AddScaled, scratch_AddScaled, Policy.opScratch]
          exact max_body _ _ _ _
      | phaseProduct i =>
          cases term? with
          | none =>
              simp only [compileAnnotatedOpsToSignedGateAux, hasLeaf_pp_none, annScratch,
                Policy.opScratch]
              refine ⟨ia, ?_, ig⟩
              rw [ip, Nat.zero_max]; rfl
          | some l =>
              simp only [compileAnnotatedOpsToSignedGateAux, gAfter, gPeak, gGood, hasLeaf_pp_some,
                ite_true]
              rw [ia, hex i]
              refine ⟨rfl, ?_, hpp i, ig⟩
              rw [ip]
              simp only [annScratch, Policy.opScratch]
              exact max_leaf _ _ _ _ (by split <;> omega)

/-- The controlled body: the same, with the control live. -/
theorem cbody_walk (hk : 1 < k) (ctrl : ℕ) (phi : Angle) (coeff : Fin (q k) → ℚ)
    (st : LayoutState k) (ex : ExtReg → ExtReg → ℕ) (e n : ℕ) (L : Finset ℕ) (hc : ctrl ∈ L)
    (hact : ∀ i, regQubitSet (st.xslot i).active ⊆ L ∧ regQubitSet (st.zslot i).active ⊆ L)
    (hpp : ∀ i, PPGood n (st.xslot i) (st.zslot i) L)
    (hex : ∀ i, ex (st.xslot i) (st.zslot i) = e) {W : ℕ}
    (hW : ∀ i, (st.xslot i).width = W ∧ (st.zslot i).width = W) :
    ∀ ops : List (AnnotatedOp k),
      gAfter (controlPhaseLeaves ctrl (compileAnnotatedOpsToSignedGateAux k hk phi coeff st ops))
        L = L ∧
      gPeak ex (controlPhaseLeaves ctrl
          (compileAnnotatedOpsToSignedGateAux k hk phi coeff st ops)) L
        = L.card + max (if hasLeaf ops then e else 0) (annScratch W ops) ∧
      gGood n (controlPhaseLeaves ctrl
          (compileAnnotatedOpsToSignedGateAux k hk phi coeff st ops)) L := by
  have touch : ∀ u : LowGate, TouchIn L u →
      after u true L = L ∧ peak scratch u true L = L.card + tmax scratch u ∧ WellFormed u true L :=
    fun u hu => touch_walk_anc scratch L u hu true
  intro ops
  induction ops with
  | nil =>
      simp [compileAnnotatedOpsToSignedGateAux, controlPhaseLeaves, gAfter, gPeak, gGood,
        hasLeaf, annScratch]
  | cons a rest ih =>
      obtain ⟨op, term?⟩ := a
      obtain ⟨ia, ip, ig⟩ := ih
      cases op with
      | shiftL i m =>
          obtain ⟨a1, p1, w1⟩ := touch (.ShiftL (st.xslot i) m) (hact i).1
          obtain ⟨a2, p2, w2⟩ := touch (.ShiftL (st.zslot i) m) (hact i).2
          simp only [compileAnnotatedOpsToSignedGateAux, controlPhaseLeaves, gAfter, gPeak,
            gGood, gPrim, hasLeaf_shiftL]
          rw [a1, a2, ia, p1, p2, ip]
          refine ⟨rfl, ?_, w1, w2, ig⟩
          simp only [annScratch, tmax_ShiftL, scratch_ShiftL, Policy.opScratch]
          exact max_body _ _ _ _
      | shiftR i m =>
          obtain ⟨a1, p1, w1⟩ := touch (.ShiftR (st.xslot i) m) (hact i).1
          obtain ⟨a2, p2, w2⟩ := touch (.ShiftR (st.zslot i) m) (hact i).2
          simp only [compileAnnotatedOpsToSignedGateAux, controlPhaseLeaves, gAfter, gPeak,
            gGood, gPrim, hasLeaf_shiftR]
          rw [a1, a2, ia, p1, p2, ip]
          refine ⟨rfl, ?_, w1, w2, ig⟩
          simp only [annScratch, tmax_ShiftR, scratch_ShiftR, Policy.opScratch]
          exact max_body _ _ _ _
      | negate i =>
          obtain ⟨a1, p1, w1⟩ := touch (.Negate (st.xslot i)) (hact i).1
          obtain ⟨a2, p2, w2⟩ := touch (.Negate (st.zslot i)) (hact i).2
          simp only [compileAnnotatedOpsToSignedGateAux, controlPhaseLeaves, gAfter, gPeak,
            gGood, gPrim, hasLeaf_negate]
          rw [a1, a2, ia, p1, p2, ip]
          refine ⟨rfl, ?_, w1, w2, ig⟩
          simp only [annScratch, tmax_Negate, scratch_Negate, (hW i).1, (hW i).2, Policy.opScratch]
          exact max_body _ _ _ _
      | addScaled d s b m =>
          obtain ⟨a1, p1, w1⟩ := touch (.AddScaled (st.xslot d) (st.xslot s) b m)
            (Finset.union_subset (hact d).1 (hact s).1)
          obtain ⟨a2, p2, w2⟩ := touch (.AddScaled (st.zslot d) (st.zslot s) b m)
            (Finset.union_subset (hact d).2 (hact s).2)
          simp only [compileAnnotatedOpsToSignedGateAux, controlPhaseLeaves, gAfter, gPeak,
            gGood, gPrim, hasLeaf_addScaled]
          rw [a1, a2, ia, p1, p2, ip]
          refine ⟨rfl, ?_, w1, w2, ig⟩
          simp only [annScratch, tmax_AddScaled, scratch_AddScaled, Policy.opScratch]
          exact max_body _ _ _ _
      | phaseProduct i =>
          cases term? with
          | none =>
              simp only [compileAnnotatedOpsToSignedGateAux, hasLeaf_pp_none, annScratch,
                Policy.opScratch]
              refine ⟨ia, ?_, ig⟩
              rw [ip, Nat.zero_max]; rfl
          | some l =>
              simp only [compileAnnotatedOpsToSignedGateAux, controlPhaseLeaves, gAfter, gPeak,
                gGood, hasLeaf_pp_some, ite_true]
              rw [ia, hex i]
              refine ⟨rfl, ?_, ⟨hc, hpp i⟩, ig⟩
              rw [ip]
              simp only [annScratch, Policy.opScratch]
              exact max_leaf _ _ _ _ (by split <;> omega)

end Body

end QubitCount
end Shor
