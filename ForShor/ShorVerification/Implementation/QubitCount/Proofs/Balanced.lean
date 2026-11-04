import ForShor.ShorVerification.Implementation.QubitCount.Proofs.OrderFinding

/-!
# Qubit count: balanced phase products

`Balanced.balance` replaces each phase product by `Balanced.siteGate`: either
the product itself or a split into blocks, each block extending its part of
the wider operand and the narrower operand to a common width, running one
product there, and returning the extension bits. Which of the two a site runs
is decided by `Balanced.fitsB` on the operands' widths and spare capacities.
Walked with the products opaque, a balanced gate walks as its source does,
except that each product peaks as the site it became (`Rec.sitePeak`,
which takes the same branch).

The order-finding facts of `OrderFinding.lean` hold for any cost of the
products, so with `Rec.sitePeak` they give the balanced count.
-/

namespace Shor
namespace QubitCount

open Gate _root_.Shor.Balanced

variable {P : ShorLoweringPolicy} {pc : ℕ → ℕ → ℕ → ℕ → ℕ}

/-! ## Extensions by any number of qubits -/

/-- An extension, walked forwards, activates its bits. -/
lemma SFact.ext_fwd {E : Gate} {r : ExtReg} {n : ℕ} (hE : E = .zeroExtend r n ∨ E = .signExtend r n)
    {L : Finset ℕ} (hfresh : _root_.Disjoint (allocBits r n) L) (hcap : r.CanGrow n) :
    SFact P pc E true L (L ∪ allocBits r n) (L.card + n) := by
  have hcard : (L ∪ allocBits r n).card = L.card + n := by
    rw [Finset.card_union_of_disjoint hfresh.symm, card_allocBits r hcap]
  rcases hE with rfl | rfl <;>
  · refine ⟨(moveOK_true _ _).mpr hfresh, rfl, ?_⟩
    show max L.card (move true (allocBits r n) L).card = _
    rw [move_true, hcard]; exact max_eq_right (Nat.le_add_right _ _)

/-- An extension, walked backwards, releases its bits. -/
lemma SFact.ext_bwd {E : Gate} {r : ExtReg} {n : ℕ} (hE : E = .zeroExtend r n ∨ E = .signExtend r n)
    {L : Finset ℕ} (hfresh : _root_.Disjoint (allocBits r n) L) (hcap : r.CanGrow n) :
    SFact P pc E false (L ∪ allocBits r n) L (L.card + n) := by
  have hcard : (L ∪ allocBits r n).card = L.card + n := by
    rw [Finset.card_union_of_disjoint hfresh.symm, card_allocBits r hcap]
  have hdiff : (L ∪ allocBits r n) \ allocBits r n = L := Finset.union_sdiff_cancel_right hfresh.symm
  rcases hE with rfl | rfl <;>
  · refine ⟨(moveOK_false _ _).mpr Finset.subset_union_right, hdiff, ?_⟩
    show max (L ∪ allocBits r n).card (move false (allocBits r n) (L ∪ allocBits r n)).card = _
    rw [move_false, hdiff, hcard]; exact max_eq_left (Nat.le_add_right _ _)

/-- A deallocation, walked forwards, releases its bits. -/
lemma SFact.dealloc_fwd' {D : Gate} {r : ExtReg} {n : ℕ}
    (hD : D = .zeroDealloc r n ∨ D = .signDealloc r n)
    {L : Finset ℕ} (hfresh : _root_.Disjoint (allocBits r n) L) (hcap : r.CanGrow n) :
    SFact P pc D true (L ∪ allocBits r n) L (L.card + n) := by
  obtain ⟨g, a, p⟩ := SFact.ext_bwd (P := P) (pc := pc) (E := .zeroExtend r n) (Or.inl rfl) hfresh hcap
  rcases hD with rfl | rfl <;> exact ⟨g, a, p⟩

/-- A deallocation, walked backwards, activates its bits. -/
lemma SFact.dealloc_bwd' {D : Gate} {r : ExtReg} {n : ℕ}
    (hD : D = .zeroDealloc r n ∨ D = .signDealloc r n)
    {L : Finset ℕ} (hfresh : _root_.Disjoint (allocBits r n) L) (hcap : r.CanGrow n) :
    SFact P pc D false L (L ∪ allocBits r n) (L.card + n) := by
  obtain ⟨g, a, p⟩ := SFact.ext_fwd (P := P) (pc := pc) (E := .zeroExtend r n) (Or.inl rfl) hfresh hcap
  rcases hD with rfl | rfl <;> exact ⟨g, a, p⟩

/-! ## One block product -/

/-- The control of a product of kind `c`, if any, is live. -/
def ctlLive : Ctl → Finset ℕ → Prop
  | .none, _ => True
  | .ctrl q, L => q ∈ L

lemma ctlLive_mono {c : Ctl} {L L' : Finset ℕ} (h : L ⊆ L') (hc : ctlLive c L) : ctlLive c L' := by
  cases c with
  | none => trivial
  | ctrl q => exact h hc

lemma SFact.ctlGate (c : Ctl) (φ : Angle) {X Z : ExtReg} {L : Finset ℕ} (hc : ctlLive c L)
    (h : ppLive X Z L) (d : Bool) :
    SFact P pc (c.gate φ X Z) d L L (L.card + pc X.width X.capacity Z.width Z.capacity) := by
  cases c with
  | none => exact ⟨h, rfl, rfl⟩
  | ctrl q => exact ⟨⟨hc, h⟩, rfl, rfl⟩

/-- Extend two operands, run a product of kind `c` on the extended operands,
and release the extensions, in either direction. -/
lemma SFact.sandwich (c : Ctl) (φ : Angle) {E1 E2 D2 D1 : Gate} {X Z : ExtReg} {a b : ℕ}
    (hE1 : E1 = .zeroExtend X a ∨ E1 = .signExtend X a)
    (hE2 : E2 = .zeroExtend Z b ∨ E2 = .signExtend Z b)
    (hD2 : D2 = .zeroDealloc Z b ∨ D2 = .signDealloc Z b)
    (hD1 : D1 = .zeroDealloc X a ∨ D1 = .signDealloc X a)
    (hX : X.CanGrow a) (hZ : Z.CanGrow b) {L : Finset ℕ} (hc : ctlLive c L)
    (hXa : regQubitSet X.active ⊆ L) (hZa : regQubitSet Z.active ⊆ L)
    (hXr : _root_.Disjoint L (regQubitSet X.reserve)) (hZr : _root_.Disjoint L (regQubitSet Z.reserve))
    (hXZ : _root_.Disjoint (regQubitSet X.reserve) (regQubitSet Z.reserve)) (d : Bool) :
    SFact P pc (E1 ;; E2 ;; c.gate φ (X.grow a) (Z.grow b) ;; D2 ;; D1) d L L
      (L.card + (a + b + pc (X.width + a) (X.grow a).capacity (Z.width + b) (Z.grow b).capacity)) := by
  have hbxR : allocBits X a ⊆ regQubitSet X.reserve := allocBits_subset_reserve X a
  have hbzR : allocBits Z b ⊆ regQubitSet Z.reserve := allocBits_subset_reserve Z b
  have h1 : _root_.Disjoint (allocBits X a) L := Finset.disjoint_of_subset_left hbxR hXr.symm
  have h2 : _root_.Disjoint (allocBits Z b) (L ∪ allocBits X a) := Finset.disjoint_union_right.mpr
    ⟨Finset.disjoint_of_subset_left hbzR hZr.symm,
     Finset.disjoint_of_subset_left hbzR (Finset.disjoint_of_subset_right hbxR hXZ.symm)⟩
  have hc1 : (L ∪ allocBits X a).card = L.card + a := by
    rw [Finset.card_union_of_disjoint h1.symm, card_allocBits X hX]
  have hc2 : (L ∪ allocBits X a ∪ allocBits Z b).card = L.card + (a + b) := by
    rw [Finset.card_union_of_disjoint h2.symm, hc1, card_allocBits Z hZ, Nat.add_assoc]
  have hlive : ppLive (X.grow a) (Z.grow b) (L ∪ allocBits X a ∪ allocBits Z b) := by
    have hxr := grow_reserve_subset X a
    have hzr := grow_reserve_subset Z b
    have hxb := allocBits_disjoint_grow_reserve X a
    have hzb := allocBits_disjoint_grow_reserve Z b
    refine ⟨?_, ?_, ?_⟩
    · rw [grow_active]
      exact Finset.union_subset (hXa.trans (Finset.subset_union_left.trans Finset.subset_union_left))
        (Finset.subset_union_right.trans Finset.subset_union_left)
    · rw [grow_active]
      exact Finset.union_subset (hZa.trans (Finset.subset_union_left.trans Finset.subset_union_left))
        Finset.subset_union_right
    · rw [Finset.disjoint_union_left, Finset.disjoint_union_left, Finset.disjoint_union_right,
        Finset.disjoint_union_right, Finset.disjoint_union_right]
      exact ⟨⟨⟨Finset.disjoint_of_subset_right hxr hXr, Finset.disjoint_of_subset_right hzr hZr⟩,
        ⟨hxb, Finset.disjoint_of_subset_left hbxR (Finset.disjoint_of_subset_right hzr hXZ)⟩⟩,
        ⟨Finset.disjoint_of_subset_left hbzR (Finset.disjoint_of_subset_right hxr hXZ.symm), hzb⟩⟩
  have leaf : SFact P pc (c.gate φ (X.grow a) (Z.grow b)) d (L ∪ allocBits X a ∪ allocBits Z b)
      (L ∪ allocBits X a ∪ allocBits Z b)
      (L.card + (a + b + pc (X.width + a) (X.grow a).capacity (Z.width + b) (Z.grow b).capacity)) := by
    refine (SFact.ctlGate c φ (ctlLive_mono ?_ hc) hlive d).congr_peak ?_
    · exact Finset.subset_union_left.trans Finset.subset_union_left
    · rw [hc2, ExtReg.width_grow X a hX, ExtReg.width_grow Z b hZ, Nat.add_assoc]
  cases d
  · have e1 := SFact.dealloc_bwd' (P := P) (pc := pc) hD1 h1 hX
    have e2 := SFact.dealloc_bwd' (P := P) (pc := pc) hD2 h2 hZ
    have e4 := SFact.ext_bwd (P := P) (pc := pc) hE2 h2 hZ
    have e5 := SFact.ext_bwd (P := P) (pc := pc) hE1 h1 hX
    rw [hc1, Nat.add_assoc] at e2 e4
    have := SFact.seqB (SFact.seqB (SFact.seqB (SFact.seqB e1 e2) leaf) e4) e5
    exact this.congr_peak (by omega)
  · have e1 := SFact.ext_fwd (P := P) (pc := pc) hE1 h1 hX
    have e2 := SFact.ext_fwd (P := P) (pc := pc) hE2 h2 hZ
    have e4 := SFact.dealloc_fwd' (P := P) (pc := pc) hD2 h2 hZ
    have e5 := SFact.dealloc_fwd' (P := P) (pc := pc) hD1 h1 hX
    rw [hc1, Nat.add_assoc] at e2 e4
    have := SFact.seq e1 (SFact.seq e2 (SFact.seq leaf (SFact.seq e4 e5)))
    exact this.congr_peak (by omega)

/-! ## The split -/

lemma reserve_disjoint_of_owned {x z : ExtReg} (h : ExtReg.OwnedDisjoint x z) :
    _root_.Disjoint (regQubitSet x.reserve) (regQubitSet z.reserve) :=
  Finset.disjoint_of_subset_left (reserve_sub_own x)
    (Finset.disjoint_of_subset_right (reserve_sub_own z) (ownSet_disjoint h))

lemma ppLive_swap {x z : ExtReg} {L : Finset ℕ} (h : ppLive x z L) : ppLive z x L :=
  ⟨h.2.1, h.1, by rw [Finset.union_comm]; exact h.2.2⟩

lemma SFact.lowGate (c : Ctl) (φ : Angle) {x z : ExtReg} {w t : ℕ} {L : Finset ℕ}
    (hc : ctlLive c L) (hl : ppLive x z L)
    (hxz : _root_.Disjoint (regQubitSet x.reserve) (regQubitSet z.reserve))
    (hw : w ≤ x.width) (hwt : w ≤ t) (hzt : z.width ≤ t)
    (hcx : t - w ≤ x.capacity) (hcz : t - z.width ≤ z.capacity) (d : Bool) :
    SFact P (Rec.ppPeak P) (lowGate c φ x z w t) d L L
      (L.card + ((t - w) + (t - z.width) + Rec.peakReserve P t t)) := by
  have hXa : regQubitSet (lowBlock x w).active ⊆ L :=
    (regQubitSet_subset_of_sublist (List.take_sublist _ _)).trans hl.1
  have := SFact.sandwich (P := P) (pc := Rec.ppPeak P) c φ (Or.inl rfl) (Or.inr rfl) (Or.inr rfl)
    (Or.inl rfl) (X := lowBlock x w) (Z := z) (a := t - w) (b := t - z.width) hcx hcz hc hXa hl.2.1
    (Finset.disjoint_union_right.mp hl.2.2).1 (Finset.disjoint_union_right.mp hl.2.2).2 hxz d
  unfold Balanced.lowGate
  refine this.congr_peak ?_
  rw [lowBlock_width x w hw, show w + (t - w) = t by omega, show z.width + (t - z.width) = t by omega]
  rfl

lemma SFact.topGate (c : Ctl) (φ : Angle) {x z : ExtReg} {t : ℕ} {L : Finset ℕ}
    (hc : ctlLive c L) (hl : ppLive x z L)
    (hxz : _root_.Disjoint (regQubitSet x.reserve) (regQubitSet z.reserve))
    (hxt : x.width ≤ t) (hzt : z.width ≤ t)
    (hcx : t - x.width ≤ x.capacity) (hcz : t - z.width ≤ z.capacity) (d : Bool) :
    SFact P (Rec.ppPeak P) (topGate c φ x z t) d L L
      (L.card + ((t - x.width) + (t - z.width) + Rec.peakReserve P t t)) := by
  have := SFact.sandwich (P := P) (pc := Rec.ppPeak P) c φ (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl)
    (X := x) (Z := z) (a := t - x.width) (b := t - z.width) hcx hcz hc hl.1 hl.2.1
    (Finset.disjoint_union_right.mp hl.2.2).1 (Finset.disjoint_union_right.mp hl.2.2).2 hxz d
  unfold Balanced.topGate
  refine this.congr_peak ?_
  rw [show x.width + (t - x.width) = t by omega, show z.width + (t - z.width) = t by omega]
  rfl

/-- A split whose plan fits returns to its start set, peaking `Rec.splitPeakOf`
above it. -/
lemma SFact.split (c : Ctl) :
    ∀ (bs : List Block) (φ : Angle) (t : ℕ) (x z : ExtReg) (L : Finset ℕ),
      ctlLive c L → ppLive x z L →
      _root_.Disjoint (regQubitSet x.reserve) (regQubitSet z.reserve) →
      fitsB P bs t x z = true → ∀ d : Bool,
      SFact P (Rec.ppPeak P) (splitGate c φ bs t x z) d L L
        (L.card + Rec.splitPeakOf (Rec.peakReserve P) bs t x.width z.width)
  | [], φ, t, x, z, L, hc, hl, hxz, hfit, d => by
      obtain ⟨h1, h2, h3, h4⟩ := fitsB_nil.mp hfit
      exact SFact.topGate c φ hc hl hxz h1 h2 (by omega) (by omega) d
  | b :: bs, φ, t, x, z, L, hc, hl, hxz, hfit, d => by
      obtain ⟨hw, ht, hzt, hx, hz, hrest⟩ := fitsB_cons.mp hfit
      have fL := SFact.lowGate (P := P) c φ hc hl hxz (le_of_lt hw) (by omega) hzt
        (by omega) (by omega) d
      have hl' : ppLive (highPart x b.w) z L :=
        ⟨(regQubitSet_subset_of_sublist (List.drop_sublist _ _)).trans hl.1, hl.2.1, hl.2.2⟩
      have fR := SFact.split c bs (φ * 2 ^ b.w) t (highPart x b.w) z L hc hl' hxz hrest d
      rw [highPart_width] at fR
      show SFact P (Rec.ppPeak P) (Balanced.lowGate c φ x z b.w b.t ;;
        splitGate c (φ * 2 ^ b.w) bs t (highPart x b.w) z) d L L _
      cases d
      · exact (SFact.seqB fR fL).congr_peak (by simp only [Rec.splitPeakOf]; rw [max_comm])
      · exact (SFact.seq fL fR).congr_peak (by simp only [Rec.splitPeakOf])

/-! ## A balanced site -/

lemma fitsB_eq_planFits :
    ∀ (bs : List Block) (t : ℕ) (x z : ExtReg),
      fitsB P bs t x z = Rec.planFits P bs t x.width x.capacity z.width z.capacity
  | [], t, x, z => by simp [fitsB, Rec.planFits]
  | b :: bs, t, x, z => by
      simp only [fitsB, Rec.planFits, fitsB_eq_planFits bs t (highPart x b.w) z, highPart_width,
        highPart_capacity]

/-- A balanced site returns to its start set, peaking `sitePeak` above it:
the split when its plan fits, the product itself otherwise. -/
lemma SFact.site (R : Rule) (c : Ctl) (φ : Angle) {x z : ExtReg} {L : Finset ℕ}
    (hown : ExtReg.OwnedDisjoint x z) (hc : ctlLive c L) (hl : ppLive x z L) (d : Bool) :
    SFact P (Rec.ppPeak P) (siteGate P R c φ x z) d L L
      (L.card + Rec.sitePeak P R x.width x.capacity z.width z.capacity) := by
  have hxz := reserve_disjoint_of_owned hown
  have base : SFact P (Rec.ppPeak P) (c.gate φ x z) d L L
      (L.card + Rec.peakReserve P x.width z.width) := SFact.ctlGate c φ hc hl d
  unfold siteGate Rec.sitePeak
  split_ifs with h1 h2
  · rcases R.plan x.width z.width with _ | p
    · exact base
    · dsimp only
      rw [fitsB_eq_planFits]
      split_ifs with hf
      · exact SFact.split c p.lower φ p.top x z L hc hl hxz ((fitsB_eq_planFits _ _ _ _).trans hf) d
      · exact base
  · rcases R.plan z.width x.width with _ | p
    · exact base
    · dsimp only
      rw [fitsB_eq_planFits]
      split_ifs with hf
      · exact SFact.split c p.lower φ p.top z x L hc (ppLive_swap hl) hxz.symm
          ((fitsB_eq_planFits _ _ _ _).trans hf) d
      · exact base
  · exact base

/-! ## The balancing pass -/

/-- Balancing changes the walk only at the phase products, each of which
peaks as the site it became. -/
theorem balance_walk (R : Rule) :
    ∀ (G : Gate) (_hws : Policy.GateWorkspaceOK P G) (d : Bool) (L : Finset ℕ),
      sGood P G d L →
      sGood P (balance P R G) d L ∧ sAfter P (balance P R G) d L = sAfter P G d L ∧
      sPeak P (Rec.ppPeak P) (balance P R G) d L = sPeak P (Rec.sitePeak P R) G d L := by
  intro G
  induction G with
  | seq U V ihU ihV =>
      intro hws d L h
      cases d
      · obtain ⟨hV, hU⟩ := h
        obtain ⟨gV, aV, pV⟩ := ihV hws.2 false L hV
        obtain ⟨gU, aU, pU⟩ := ihU hws.1 false _ hU
        refine ⟨⟨gV, by rw [aV]; exact gU⟩, ?_, ?_⟩
        · show sAfter P (balance P R U) false (sAfter P (balance P R V) false L) = _
          rw [aV, aU]; rfl
        · show max (sPeak P _ (balance P R V) false L)
            (sPeak P _ (balance P R U) false (sAfter P (balance P R V) false L)) = _
          rw [pV, aV, pU]; rfl
      · obtain ⟨hU, hV⟩ := h
        obtain ⟨gU, aU, pU⟩ := ihU hws.1 true L hU
        obtain ⟨gV, aV, pV⟩ := ihV hws.2 true _ hV
        refine ⟨⟨gU, by rw [aU]; exact gV⟩, ?_, ?_⟩
        · show sAfter P (balance P R V) true (sAfter P (balance P R U) true L) = _
          rw [aU, aV]; rfl
        · show max (sPeak P _ (balance P R U) true L)
            (sPeak P _ (balance P R V) true (sAfter P (balance P R U) true L)) = _
          rw [pU, aU, pV]; rfl
  | adj U ih =>
      intro hws d L h
      exact ih hws (!d) L h
  | SignedPhaseProd φ x z =>
      intro hws d L h
      obtain ⟨g, a, p⟩ := SFact.site (P := P) R .none φ hws.owned_disjoint trivial h d
      exact ⟨g, a, p⟩
  | CSignedPhaseProd q φ x z =>
      intro hws d L h
      obtain ⟨g, a, p⟩ := SFact.site (P := P) R (.ctrl q) φ hws.owned_disjoint h.1 h.2 d
      exact ⟨g, a, p⟩
  | id | H _ | X _ | CNOT _ _ | Toffoli _ _ _ | RadixReverse _ _ | ShiftL _ _ | ShiftR _ _
  | Negate _ | AddScaled _ _ _ _ | zeroExtend _ _ | signExtend _ _ | zeroDealloc _ _
  | signDealloc _ _ | QFT _ | CmpGeConst _ _ _ _ | CSubConst _ _ _ _ | idealCtrlModMul _ _ _ _ =>
      intro _ _ _ h; exact ⟨h, rfl, rfl⟩

/-! ## The claim -/

theorem orderFindingPeakFormulaBalancedRec (P : ShorLoweringPolicy) (R : Rule) :
    Rec.OrderFindingPeakFormulaBalanced P R := by
  intro hP a N x y work scratch flag hmod hs4 hws hlay
  obtain ⟨g, -, hp⟩ := orderFinding_fact (P := P) (pc := Rec.sitePeak P R) a hmod hs4 hlay
  obtain ⟨gb, -, pb⟩ := balance_walk (P := P) R _ hws true _ g
  obtain ⟨-, lp⟩ := lower_walk P hP _ (balance_ok P R _ hws) true _ gb
  show peak QubitCount.scratch (Policy.lowerGate P _ (balance_ok P R _ hws)) true _ = _
  rw [lp, pb, hp, base_card hmod hs4 hlay]

end QubitCount
end Shor
