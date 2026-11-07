import ForShor.ShorVerification.Implementation.QubitCount.Proofs.Lowering
import ForShor.ShorVerification.Implementation.ModularExponentiation.Statement

/-!
# Qubit count: building blocks of the order-finding circuit

`SFact P pc G d L M p` says that the high-level gate `G`, walked in direction `d`
from the live set `L`, is ready to be counted, ends at `M`, and peaks at `p`.
This file gives the facts for the pieces the order-finding circuit is built
from: Hadamard layers, the two phase-product wrappers, the QFT with a fresh
pool or with its first pool qubit live, and the Step-4 difference.
-/

namespace Shor
namespace QubitCount

open Gate

variable (P : ShorLoweringPolicy)

/-- `G` walked in direction `d` from `L` is ready, ends at `M`, peaks at `p`,
when a phase product on operands of widths `wx`, `wz` and spare capacities
`cx`, `cz` peaks `pc wx cx wz cz` above its start. -/
def SFact (pc : ℕ → ℕ → ℕ → ℕ → ℕ) (G : Gate) (d : Bool) (L M : Finset ℕ) (p : ℕ) : Prop :=
  sGood P G d L ∧ sAfter P G d L = M ∧ sPeak P pc G d L = p

variable {P} {pc : ℕ → ℕ → ℕ → ℕ → ℕ}

lemma SFact.seq {U V : Gate} {L M K : Finset ℕ} {c a b : ℕ}
    (hU : SFact P pc U true L M (c + a)) (hV : SFact P pc V true M K (c + b)) :
    SFact P pc (U ;; V) true L K (c + max a b) := by
  obtain ⟨g1, a1, p1⟩ := hU
  obtain ⟨g2, a2, p2⟩ := hV
  refine ⟨⟨g1, by rw [a1]; exact g2⟩, ?_, ?_⟩
  · show sAfter P V true (sAfter P U true L) = K
    rw [a1, a2]
  · show max (sPeak P pc U true L) (sPeak P pc V true (sAfter P U true L)) = _
    rw [p1, a1, p2, max_add_add_left]

lemma SFact.seqB {U V : Gate} {L M K : Finset ℕ} {c a b : ℕ}
    (hV : SFact P pc V false L M (c + a)) (hU : SFact P pc U false M K (c + b)) :
    SFact P pc (U ;; V) false L K (c + max a b) := by
  obtain ⟨g1, a1, p1⟩ := hV
  obtain ⟨g2, a2, p2⟩ := hU
  refine ⟨⟨g1, by rw [a1]; exact g2⟩, ?_, ?_⟩
  · show sAfter P U false (sAfter P V false L) = K
    rw [a1, a2]
  · show max (sPeak P pc V false L) (sPeak P pc U false (sAfter P V false L)) = _
    rw [p1, a1, p2, max_add_add_left]

lemma SFact.adj {U : Gate} {d : Bool} {L M : Finset ℕ} {p : ℕ}
    (h : SFact P pc U (!d) L M p) : SFact P pc (†U) d L M p := h

lemma SFact.id (d : Bool) (L : Finset ℕ) : SFact P pc .id d L L (L.card + 0) := by
  cases d <;> exact ⟨trivial, rfl, rfl⟩

lemma SFact.congr_peak {G : Gate} {d : Bool} {L M : Finset ℕ} {p p' : ℕ}
    (h : SFact P pc G d L M p) (e : p = p') : SFact P pc G d L M p' := e ▸ h

/-! ## Primitives acting on live qubits -/

lemma SFact.H {q : ℕ} {L : Finset ℕ} (hq : q ∈ L) (d : Bool) :
    SFact P pc (.H q) d L L (L.card + 0) := by
  have h : L ∪ LowGate.usedQubits (.H q) = L := by simp [LowGate.usedQubits, hq]
  show WellFormed (.H q) d L ∧ after (.H q) d L = L ∧ peak (scratchFor P.negation) (.H q) d L = L.card + 0
  simp [WellFormed, after, peak, LowGate.usedQubits, hq]

lemma SFact.X {q : ℕ} {L : Finset ℕ} (hq : q ∈ L) (d : Bool) :
    SFact P pc (.X q) d L L (L.card + 0) := by
  have h : L ∪ LowGate.usedQubits (.X q) = L := by simp [LowGate.usedQubits, hq]
  show WellFormed (.X q) d L ∧ after (.X q) d L = L ∧ peak (scratchFor P.negation) (.X q) d L = L.card + 0
  simp [WellFormed, after, peak, LowGate.usedQubits, hq]

lemma SFact.CNOT {c t : ℕ} {L : Finset ℕ} (hc : c ∈ L) (ht : t ∈ L) (d : Bool) :
    SFact P pc (.CNOT c t) d L L (L.card + 0) := by
  have hs : LowGate.usedQubits (.CNOT c t) ⊆ L := by
    simp [LowGate.usedQubits, Finset.insert_subset_iff, hc, ht]
  have h : L ∪ LowGate.usedQubits (.CNOT c t) = L := Finset.union_eq_left.mpr hs
  show WellFormed (.CNOT c t) d L ∧ after (.CNOT c t) d L = L ∧
    peak (scratchFor P.negation) (.CNOT c t) d L = L.card + 0
  refine ⟨hs, h, ?_⟩
  show (L ∪ _).card + scratchFor P.negation (.CNOT c t) = _
  rw [h, scratchFor_CNOT]

lemma SFact.Negate {r : ExtReg} {L : Finset ℕ} (hr : regQubitSet r.active ⊆ L) (d : Bool) :
    SFact P pc (.Negate r) d L L (L.card + negationScratch P.negation r.width) := by
  have h : L ∪ LowGate.usedQubits (.Negate r) = L := Finset.union_eq_left.mpr hr
  show WellFormed (.Negate r) d L ∧ after (.Negate r) d L = L ∧
    peak (scratchFor P.negation) (.Negate r) d L = L.card + negationScratch P.negation r.width
  refine ⟨hr, h, ?_⟩
  show (L ∪ _).card + scratchFor P.negation (.Negate r) = _
  rw [h, scratchFor_Negate]

lemma SFact.AddScaled {dst src : ExtReg} {b : Bool} {n : ℕ} {L : Finset ℕ}
    (h1 : regQubitSet dst.active ⊆ L) (h2 : regQubitSet src.active ⊆ L) (d : Bool) :
    SFact P pc (.AddScaled dst src b n) d L L (L.card + 1) := by
  have hs : LowGate.usedQubits (.AddScaled dst src b n) ⊆ L := Finset.union_subset h1 h2
  have h : L ∪ LowGate.usedQubits (.AddScaled dst src b n) = L := Finset.union_eq_left.mpr hs
  show WellFormed (.AddScaled dst src b n) d L ∧ after (.AddScaled dst src b n) d L = L ∧
    peak (scratchFor P.negation) (.AddScaled dst src b n) d L = L.card + 1
  refine ⟨hs, h, ?_⟩
  show (L ∪ _).card + scratchFor P.negation (.AddScaled dst src b n) = _
  rw [h, scratchFor_AddScaled]

/-- Extending by one qubit forwards activates it; backwards releases it. -/
lemma SFact.extend_fwd {r : ExtReg} {L : Finset ℕ} {c : ℕ} (hfresh : _root_.Disjoint (allocBits r 1) L)
    (hcap : r.CanGrow 1) (hc : L.card = c) :
    SFact P pc (.zeroExtend r 1) true L (L ∪ allocBits r 1) (c + 1) := by
  have hcard : (L ∪ allocBits r 1).card = c + 1 := by
    rw [Finset.card_union_of_disjoint hfresh.symm, card_allocBits r hcap, hc]
  show MoveOK true (allocBits r 1) L ∧ move true (allocBits r 1) L = _ ∧
    max L.card (move true (allocBits r 1) L).card = _
  refine ⟨hfresh, rfl, ?_⟩
  rw [move_true, hcard, hc]
  exact max_eq_right (Nat.le_succ c)

lemma SFact.extend_bwd {r : ExtReg} {L : Finset ℕ} {c : ℕ} (hfresh : _root_.Disjoint (allocBits r 1) L)
    (hcap : r.CanGrow 1) (hc : L.card = c) :
    SFact P pc (.zeroExtend r 1) false (L ∪ allocBits r 1) L (c + 1) := by
  have hcard : (L ∪ allocBits r 1).card = c + 1 := by
    rw [Finset.card_union_of_disjoint hfresh.symm, card_allocBits r hcap, hc]
  show MoveOK false (allocBits r 1) (L ∪ allocBits r 1) ∧ move false (allocBits r 1) (L ∪ allocBits r 1) = _ ∧
    max (L ∪ allocBits r 1).card (move false (allocBits r 1) (L ∪ allocBits r 1)).card = _
  refine ⟨Finset.subset_union_right, Finset.union_sdiff_cancel_right hfresh.symm, ?_⟩
  rw [move_false, Finset.union_sdiff_cancel_right hfresh.symm, hcard, hc]
  exact max_eq_left (Nat.le_succ c)

lemma SFact.dealloc_fwd {r : ExtReg} {L : Finset ℕ} {c : ℕ} (hfresh : _root_.Disjoint (allocBits r 1) L)
    (hcap : r.CanGrow 1) (hc : L.card = c) :
    SFact P pc (.zeroDealloc r 1) true (L ∪ allocBits r 1) L (c + 1) := by
  have := SFact.extend_bwd (P := P) (pc := pc) hfresh hcap hc
  obtain ⟨g, a, p⟩ := this
  exact ⟨g, a, p⟩

lemma SFact.dealloc_bwd {r : ExtReg} {L : Finset ℕ} {c : ℕ} (hfresh : _root_.Disjoint (allocBits r 1) L)
    (hcap : r.CanGrow 1) (hc : L.card = c) :
    SFact P pc (.zeroDealloc r 1) false L (L ∪ allocBits r 1) (c + 1) := by
  have := SFact.extend_fwd (P := P) (pc := pc) hfresh hcap hc
  obtain ⟨g, a, p⟩ := this
  exact ⟨g, a, p⟩

/-! ## Hadamard layers -/

lemma SFact.H_reg {r : Reg} {L : Finset ℕ} (hr : regQubitSet r ⊆ L) (d : Bool) :
    SFact P pc (H_reg r) d L L (L.card + 0) := by
  have key : ∀ (qs : List ℕ) (acc : Gate), (∀ q ∈ qs, q ∈ L) →
      SFact P pc acc d L L (L.card + 0) →
      SFact P pc (qs.foldl (fun acc q => Gate.H q ;; acc) acc) d L L (L.card + 0) := by
    intro qs
    induction qs with
    | nil => intro acc _ h; exact h
    | cons q qs ih =>
        intro acc hqs h
        apply ih _ (fun q' hq' => hqs q' (List.mem_cons_of_mem _ hq'))
        have hH := SFact.H (P := P) (pc := pc) (hqs q (List.mem_cons_self)) d
        cases d
        · exact (SFact.seqB h hH).congr_peak (by simp)
        · exact (SFact.seq hH h).congr_peak (by simp)
  apply key _ _ (fun q hq => hr ((mem_regQubitSet).mpr hq)) (SFact.id d L)

/-! ## The phase-product wrappers -/

section Wrap

variable {x z : Reg} (ws : Gate.PhaseProdWorkspace x z) {L : Finset ℕ}

lemma wrapFacts (hx : regQubitSet x ⊆ L) (hz : regQubitSet z ⊆ L)
    (hres : _root_.Disjoint L (regQubitSet ws.xReserve ∪ regQubitSet ws.zReserve)) :
    let bx := allocBits ws.xExt 1
    let bz := allocBits ws.zExt 1
    _root_.Disjoint bx L ∧ _root_.Disjoint bz (L ∪ bx) ∧
    ppLive (ws.xExt.grow 1) (ws.zExt.grow 1) (L ∪ bx ∪ bz) ∧
    (L ∪ bx ∪ bz).card = L.card + 2 ∧
    (ws.xExt.grow 1).width = regSize x + 1 ∧ (ws.zExt.grow 1).width = regSize z + 1 := by
  intro bx bz
  have hbxR : bx ⊆ regQubitSet ws.xReserve := allocBits_subset_reserve ws.xExt 1
  have hbzR : bz ⊆ regQubitSet ws.zReserve := allocBits_subset_reserve ws.zExt 1
  have hxzR : _root_.Disjoint (regQubitSet ws.xReserve) (regQubitSet ws.zReserve) :=
    regQubitSet_disjoint ws.reserve_disjoint
  have hLx : _root_.Disjoint L (regQubitSet ws.xReserve) := (Finset.disjoint_union_right.mp hres).1
  have hLz : _root_.Disjoint L (regQubitSet ws.zReserve) := (Finset.disjoint_union_right.mp hres).2
  have h1 : _root_.Disjoint bx L := Finset.disjoint_of_subset_left hbxR hLx.symm
  have h2 : _root_.Disjoint bz (L ∪ bx) := Finset.disjoint_union_right.mpr
    ⟨Finset.disjoint_of_subset_left hbzR hLz.symm,
     Finset.disjoint_of_subset_left hbzR (Finset.disjoint_of_subset_right hbxR hxzR.symm)⟩
  have hxr : regQubitSet (ws.xExt.grow 1).reserve ⊆ regQubitSet ws.xReserve := grow_reserve_subset _ _
  have hzr : regQubitSet (ws.zExt.grow 1).reserve ⊆ regQubitSet ws.zReserve := grow_reserve_subset _ _
  have hxb : _root_.Disjoint bx (regQubitSet (ws.xExt.grow 1).reserve) :=
    allocBits_disjoint_grow_reserve ws.xExt 1
  have hzb : _root_.Disjoint bz (regQubitSet (ws.zExt.grow 1).reserve) :=
    allocBits_disjoint_grow_reserve ws.zExt 1
  refine ⟨h1, h2, ⟨?_, ?_, ?_⟩, ?_, ExtReg.width_grow ws.xExt 1 ws.xExt_canGrow,
    ExtReg.width_grow ws.zExt 1 ws.zExt_canGrow⟩
  · rw [grow_active]
    intro q hq
    simp only [Finset.mem_union] at hq ⊢
    rcases hq with hq | hq
    · exact Or.inl (Or.inl (hx hq))
    · exact Or.inl (Or.inr hq)
  · rw [grow_active]
    intro q hq
    simp only [Finset.mem_union] at hq ⊢
    rcases hq with hq | hq
    · exact Or.inl (Or.inl (hz hq))
    · exact Or.inr hq
  · rw [Finset.disjoint_union_left, Finset.disjoint_union_left, Finset.disjoint_union_right,
      Finset.disjoint_union_right, Finset.disjoint_union_right]
    refine ⟨⟨⟨Finset.disjoint_of_subset_right hxr hLx, Finset.disjoint_of_subset_right hzr hLz⟩,
      ⟨hxb, Finset.disjoint_of_subset_left hbxR (Finset.disjoint_of_subset_right hzr hxzR)⟩⟩,
      ⟨Finset.disjoint_of_subset_left hbzR (Finset.disjoint_of_subset_right hxr hxzR.symm), hzb⟩⟩
  · rw [Finset.card_union_of_disjoint h2.symm, Finset.card_union_of_disjoint h1.symm,
      card_allocBits _ ws.xExt_canGrow, card_allocBits _ ws.zExt_canGrow]

/-- The unsigned phase product, from a live set holding its operands and none
of its two spare pools, in either direction. -/
lemma SFact.ppUsing (phi : Angle) (hx : regQubitSet x ⊆ L) (hz : regQubitSet z ⊆ L)
    (hres : _root_.Disjoint L (regQubitSet ws.xReserve ∪ regQubitSet ws.zReserve)) (d : Bool) :
    SFact P pc (Gate.PhaseProdUsing phi x z ws) d L L
      (L.card + (2 + pc (regSize x + 1) (regSize ws.xReserve - 1) (regSize z + 1)
        (regSize ws.zReserve - 1))) := by
  obtain ⟨h1, h2, hpp, hcard, hwx, hwz⟩ := wrapFacts ws hx hz hres
  have hcap2 : (L ∪ allocBits ws.xExt 1).card = L.card + 1 := by
    rw [Finset.card_union_of_disjoint h1.symm, card_allocBits _ ws.xExt_canGrow]
  have leaf : SFact P pc (.SignedPhaseProd phi (ws.xExt.grow 1) (ws.zExt.grow 1)) d
      (L ∪ allocBits ws.xExt 1 ∪ allocBits ws.zExt 1) (L ∪ allocBits ws.xExt 1 ∪ allocBits ws.zExt 1)
      (L.card + (2 + pc (regSize x + 1) (regSize ws.xReserve - 1) (regSize z + 1)
        (regSize ws.zReserve - 1))) := by
    refine ⟨hpp, rfl, ?_⟩
    show _ + _ = _
    rw [hcard, hwx, hwz, ExtReg.capacity_grow _ 1 ws.xExt_canGrow,
      ExtReg.capacity_grow _ 1 ws.zExt_canGrow, Nat.add_assoc]
    rfl
  unfold Gate.PhaseProdUsing
  cases d
  · have e1 := SFact.dealloc_bwd (P := P) (pc := pc) h1 ws.xExt_canGrow rfl
    have e2 := SFact.dealloc_bwd (P := P) (pc := pc) h2 ws.zExt_canGrow hcap2
    have e4 := SFact.extend_bwd (P := P) (pc := pc) h2 ws.zExt_canGrow hcap2
    have e5 := SFact.extend_bwd (P := P) (pc := pc) h1 ws.xExt_canGrow rfl
    rw [show L.card + 1 + 1 = L.card + 2 by ring] at e2 e4
    have := SFact.seqB (SFact.seqB (SFact.seqB (SFact.seqB e1 e2) leaf) e4) e5
    exact this.congr_peak (by simp only [← Nat.add_assoc] at *; omega)
  · have e1 := SFact.extend_fwd (P := P) (pc := pc) h1 ws.xExt_canGrow rfl
    have e2 := SFact.extend_fwd (P := P) (pc := pc) h2 ws.zExt_canGrow hcap2
    have e4 := SFact.dealloc_fwd (P := P) (pc := pc) h2 ws.zExt_canGrow hcap2
    have e5 := SFact.dealloc_fwd (P := P) (pc := pc) h1 ws.xExt_canGrow rfl
    rw [show L.card + 1 + 1 = L.card + 2 by ring] at e2 e4
    have := SFact.seq e1 (SFact.seq e2 (SFact.seq leaf (SFact.seq e4 e5)))
    exact this.congr_peak (by omega)

/-- The controlled unsigned phase product. -/
lemma SFact.cppUsing (ctrl : ℕ) (phi : Angle) (hc : ctrl ∈ L) (hx : regQubitSet x ⊆ L)
    (hz : regQubitSet z ⊆ L)
    (hres : _root_.Disjoint L (regQubitSet ws.xReserve ∪ regQubitSet ws.zReserve)) (d : Bool) :
    SFact P pc (Gate.CPhaseProdUsing ctrl phi x z ws) d L L
      (L.card + (2 + pc (regSize x + 1) (regSize ws.xReserve - 1) (regSize z + 1)
        (regSize ws.zReserve - 1))) := by
  obtain ⟨h1, h2, hpp, hcard, hwx, hwz⟩ := wrapFacts ws hx hz hres
  have hcap2 : (L ∪ allocBits ws.xExt 1).card = L.card + 1 := by
    rw [Finset.card_union_of_disjoint h1.symm, card_allocBits _ ws.xExt_canGrow]
  have leaf : SFact P pc (.CSignedPhaseProd ctrl phi (ws.xExt.grow 1) (ws.zExt.grow 1)) d
      (L ∪ allocBits ws.xExt 1 ∪ allocBits ws.zExt 1) (L ∪ allocBits ws.xExt 1 ∪ allocBits ws.zExt 1)
      (L.card + (2 + pc (regSize x + 1) (regSize ws.xReserve - 1) (regSize z + 1)
        (regSize ws.zReserve - 1))) := by
    refine ⟨⟨Finset.mem_union_left _ (Finset.mem_union_left _ hc), hpp⟩, rfl, ?_⟩
    show _ + _ = _
    rw [hcard, hwx, hwz, ExtReg.capacity_grow _ 1 ws.xExt_canGrow,
      ExtReg.capacity_grow _ 1 ws.zExt_canGrow, Nat.add_assoc]
    rfl
  unfold Gate.CPhaseProdUsing
  cases d
  · have e1 := SFact.dealloc_bwd (P := P) (pc := pc) h1 ws.xExt_canGrow rfl
    have e2 := SFact.dealloc_bwd (P := P) (pc := pc) h2 ws.zExt_canGrow hcap2
    have e4 := SFact.extend_bwd (P := P) (pc := pc) h2 ws.zExt_canGrow hcap2
    have e5 := SFact.extend_bwd (P := P) (pc := pc) h1 ws.xExt_canGrow rfl
    rw [show L.card + 1 + 1 = L.card + 2 by ring] at e2 e4
    have := SFact.seqB (SFact.seqB (SFact.seqB (SFact.seqB e1 e2) leaf) e4) e5
    exact this.congr_peak (by simp only [← Nat.add_assoc] at *; omega)
  · have e1 := SFact.extend_fwd (P := P) (pc := pc) h1 ws.xExt_canGrow rfl
    have e2 := SFact.extend_fwd (P := P) (pc := pc) h2 ws.zExt_canGrow hcap2
    have e4 := SFact.dealloc_fwd (P := P) (pc := pc) h2 ws.zExt_canGrow hcap2
    have e5 := SFact.dealloc_fwd (P := P) (pc := pc) h1 ws.xExt_canGrow rfl
    rw [show L.card + 1 + 1 = L.card + 2 by ring] at e2 e4
    have := SFact.seq e1 (SFact.seq e2 (SFact.seq leaf (SFact.seq e4 e5)))
    exact this.congr_peak (by omega)

end Wrap

/-! ## The QFT -/

/-- A QFT from a live set holding its register and none of its reserve. -/
lemma SFact.qft {r : ExtReg} {L : Finset ℕ} (hr : regQubitSet r.active ⊆ L)
    (hres : _root_.Disjoint L (regQubitSet r.reserve)) (d : Bool) :
    SFact P pc (.QFT r) d L L (L.card + Rec.qftPeak P r.width) := by
  have hpools := qftPools_subset P r
  have hfirst : L \ firstOf (Policy.qftXWork P r) = L := Finset.sdiff_eq_self_of_disjoint
    (Finset.disjoint_of_subset_right ((firstOf_subset _).trans hpools.1) hres)
  have hafter : sAfter P (.QFT r) d L = L := by
    show (if 2 ≤ r.width then L \ firstOf (Policy.qftXWork P r) else L) = L
    rw [hfirst]; split <;> rfl
  have hpeak : sPeak P pc (.QFT r) d L = L.card + Rec.qftPeak P r.width := by
    show (if 2 ≤ r.width then (L \ firstOf (Policy.qftXWork P r)).card + Rec.qftPeak P r.width
      else L.card) = _
    rw [hfirst]; split
    · rfl
    · next h => rw [qftPeak_lt_two P (by omega)]; rfl
  refine ⟨?_, hafter, hpeak⟩
  cases d
  · exact ⟨hr, hres⟩
  · refine ⟨hr, Finset.disjoint_of_subset_right hpools.2 hres, ?_⟩
    rw [Finset.disjoint_iff_inter_eq_empty.mp (Finset.disjoint_of_subset_right hpools.1 hres)]
    exact Finset.empty_subset _

/-- A QFT on a register of width at least two whose first reserve qubit is
live: it ends without that qubit and peaks as from the set without it. -/
lemma SFact.qft_prelive {r : ExtReg} {L : Finset ℕ} (hw : 2 ≤ r.width)
    (hr : regQubitSet r.active ⊆ L) (hres : _root_.Disjoint L (regQubitSet r.reserve)) :
    SFact P pc (.QFT r) true (L ∪ allocBits r 1) L (L.card + Rec.qftPeak P r.width) := by
  have hpools := qftPools_subset P r
  -- the x-side pool starts with the first reserve qubit
  have hneed : 1 ≤ (Policy.qftWorkspaceNeed P r.width).1 := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' hw
    rw [hm]; simp [Policy.qftWorkspaceNeed, qftWorkspaceNeedOf]
  have hfirst : firstOf (Policy.qftXWork P r) = allocBits r 1 := by
    simp only [firstOf, Policy.qftXWork, qftXWorkOf, allocBits, ExtReg.newBits, Reg.take,
      List.take_take, Nat.min_eq_left hneed]
  have hbR : allocBits r 1 ⊆ regQubitSet r.reserve := allocBits_subset_reserve r 1
  have hbL : _root_.Disjoint (allocBits r 1) L := Finset.disjoint_of_subset_left hbR hres.symm
  have hdiff : (L ∪ allocBits r 1) \ allocBits r 1 = L := Finset.union_sdiff_cancel_right hbL.symm
  refine ⟨⟨hr.trans Finset.subset_union_left, ?_, ?_⟩, ?_, ?_⟩
  · -- the z-side pool is disjoint from the first reserve qubit
    have hzb : _root_.Disjoint (allocBits r 1) (regQubitSet (Policy.qftZWork P r)) := by
      rw [← hfirst]
      rw [Finset.disjoint_left]
      intro q h1 h2
      simp only [firstOf, Policy.qftXWork, qftXWorkOf, Policy.qftZWork, qftZWorkOf,
        mem_regQubitSet, Reg.take, Reg.drop] at h1 h2
      have h1' : q ∈ (List.take (Policy.qftWorkspaceNeed P r.width).1 r.reserve.qubits) :=
        List.mem_of_mem_take h1
      exact List.disjoint_take_drop r.reserve.nodup le_rfl h1' (List.mem_of_mem_take h2)
    exact Finset.disjoint_union_left.mpr ⟨Finset.disjoint_of_subset_right hpools.2 hres, hzb⟩
  · rw [hfirst]
    intro q hq
    rw [Finset.mem_inter, Finset.mem_union] at hq
    rcases hq.1 with h | h
    · exact absurd (hpools.1 hq.2) (Finset.disjoint_left.mp hres h)
    · exact h
  · show (if 2 ≤ r.width then (L ∪ allocBits r 1) \ firstOf (Policy.qftXWork P r)
      else L ∪ allocBits r 1) = L
    rw [ite_eq_left hw, hfirst, hdiff]
  · show (if 2 ≤ r.width then ((L ∪ allocBits r 1) \ firstOf (Policy.qftXWork P r)).card
      + Rec.qftPeak P r.width else (L ∪ allocBits r 1).card) = _
    rw [ite_eq_left hw, hfirst, hdiff]

end QubitCount
end Shor
