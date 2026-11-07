import ForShor.ShorVerification.Implementation.QubitCount.Proofs.Level
import ForShor.ShorVerification.Implementation.QubitCount.Proofs.Budgets
import ForShor.ShorVerification.Implementation.PhaseProduct.Statement
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Lowering.Lower
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Lowering.PlanReadiness.PlanValid

/-!
# Qubit count: the phase product

The lowered signed phase product returns the live set it started from, and
its peak is that set's size plus `Rec.peakReserve`. The proof is an
induction over lowering plans: a base case acts on its operands only, and a
recursive level activates exactly the reserve qubits that `immediateXNeed` and
`immediateZNeed` count, then runs its children one at a time.
-/

namespace Shor
namespace QubitCount

open Gate Operations
open RecursivePhaseWorkspace (immediateXNeed immediateZNeed immediateNeed nextWidth limbWidth
  nextWidthBy immediateNeedBy immediateXNeedBy immediateZNeedBy)

/-! ## One level, with the layout's facts -/

section Level

variable (R : WidthRule) {x z : ExtReg} {k : ℕ} (layout : Gate.PhaseProductLayout x z k) (ops : Prog k)

/-- The source and grown slots of one level. -/
abbrev srcOf : LayoutState k := initSignedLayoutState layout
abbrev dstOf : LayoutState k :=
  targetSignedLayoutState (srcOf layout) (neededWidthsBy R x z ops)

variable {R layout ops}

lemma extraDelta_x (hcap : (srcOf layout).CanGrowToNeeds (neededWidthsBy R x z ops)) (i : Fin k) :
    extraDelta ((srcOf layout).xslot i) ((dstOf R layout ops).xslot i)
      = nextSignedWidthBy R x z ops - ((srcOf layout).xslot i).width := by
  unfold extraDelta
  rw [targetSignedLayoutState_xslot_width_by R layout ops i hcap]
  rfl

lemma extraDelta_z (hcap : (srcOf layout).CanGrowToNeeds (neededWidthsBy R x z ops)) (i : Fin k) :
    extraDelta ((srcOf layout).zslot i) ((dstOf R layout ops).zslot i)
      = nextSignedWidthBy R x z ops - ((srcOf layout).zslot i).width := by
  unfold extraDelta
  rw [targetSignedLayoutState_zslot_width_by R layout ops i hcap]
  rfl

lemma dst_x_eq (hcap : (srcOf layout).CanGrowToNeeds (neededWidthsBy R x z ops)) (i : Fin k) :
    (dstOf R layout ops).xslot i
      = ((srcOf layout).xslot i).grow
          (extraDelta ((srcOf layout).xslot i) ((dstOf R layout ops).xslot i)) := by
  rw [extraDelta_x hcap i]; rfl

lemma dst_z_eq (hcap : (srcOf layout).CanGrowToNeeds (neededWidthsBy R x z ops)) (i : Fin k) :
    (dstOf R layout ops).zslot i
      = ((srcOf layout).zslot i).grow
          (extraDelta ((srcOf layout).zslot i) ((dstOf R layout ops).zslot i)) := by
  rw [extraDelta_z hcap i]; rfl

lemma bitsX_subset (i : Fin k) :
    bitsX (srcOf layout) (dstOf R layout ops) i ⊆ regQubitSet (layout.xSplit.reserve i) :=
  allocBits_subset_reserve _ _

lemma bitsZ_subset (i : Fin k) :
    bitsZ (srcOf layout) (dstOf R layout ops) i ⊆ regQubitSet (layout.zSplit.reserve i) :=
  allocBits_subset_reserve _ _

/-- The chunk allocations of a level activate disjoint qubits outside the
live set, when the live set holds none of the operands' reserves. -/
lemma freshBits_of_layout (hv : layout.Valid) {L : Finset ℕ}
    (hres : _root_.Disjoint L (regQubitSet x.reserve ∪ regQubitSet z.reserve)) :
    FreshBits (srcOf layout) (dstOf R layout ops) L := by
  have hxL : ∀ i, _root_.Disjoint (regQubitSet (layout.xSplit.reserve i)) L := fun i =>
    (Finset.disjoint_of_subset_left (splitReserve_subset layout.xSplit hv.xSplit i)
      (Finset.disjoint_union_left.mp hres.symm |>.1))
  have hzL : ∀ i, _root_.Disjoint (regQubitSet (layout.zSplit.reserve i)) L := fun i =>
    (Finset.disjoint_of_subset_left (splitReserve_subset layout.zSplit hv.zSplit i)
      (Finset.disjoint_union_left.mp hres.symm |>.2))
  exact
    { x_fresh := fun i => Finset.disjoint_of_subset_left (bitsX_subset i) (hxL i)
      z_fresh := fun i => Finset.disjoint_of_subset_left (bitsZ_subset i) (hzL i)
      xz := fun i j => Finset.disjoint_of_subset_left (bitsX_subset i)
        (Finset.disjoint_of_subset_right (bitsZ_subset j) (crossReserve_disjoint layout hv i j))
      xx := fun i j hij => Finset.disjoint_of_subset_left (bitsX_subset i)
        (Finset.disjoint_of_subset_right (bitsX_subset j)
          (splitReserve_disjoint layout.xSplit hv.xSplit hij))
      zz := fun i j hij => Finset.disjoint_of_subset_left (bitsZ_subset i)
        (Finset.disjoint_of_subset_right (bitsZ_subset j)
          (splitReserve_disjoint layout.zSplit hv.zSplit hij)) }

lemma mem_allocSet_all {i : Fin k} {q : ℕ} :
    (q ∈ bitsX (srcOf layout) (dstOf R layout ops) i ∨ q ∈ bitsZ (srcOf layout) (dstOf R layout ops) i) →
      q ∈ allocSet (srcOf layout) (dstOf R layout ops) k := fun h =>
  (mem_allocSet _ _).mpr ⟨i, i.2, h⟩

/-- After the allocations, every grown chunk is live. -/
lemma dst_active_subset (hcap : (srcOf layout).CanGrowToNeeds (neededWidthsBy R x z ops))
    {L : Finset ℕ} (hx : regQubitSet x.active ⊆ L) (hz : regQubitSet z.active ⊆ L) (i : Fin k) :
    regQubitSet ((dstOf R layout ops).xslot i).active ⊆ L ∪ allocSet (srcOf layout) (dstOf R layout ops) k ∧
    regQubitSet ((dstOf R layout ops).zslot i).active ⊆ L ∪ allocSet (srcOf layout) (dstOf R layout ops) k := by
  constructor
  · rw [dst_x_eq hcap i, grow_active]
    refine Finset.union_subset_union ((splitActive_subset layout.xSplit i).trans hx) ?_
    intro q hq
    exact mem_allocSet_all (Or.inl hq)
  · rw [dst_z_eq hcap i, grow_active]
    refine Finset.union_subset_union ((splitActive_subset layout.zSplit i).trans hz) ?_
    intro q hq
    exact mem_allocSet_all (Or.inr hq)

/-- After the allocations, every grown chunk's remaining reserve is still not
live. -/
lemma dst_reserve_disjoint (hv : layout.Valid) (hcap : (srcOf layout).CanGrowToNeeds (neededWidthsBy R x z ops))
    {L : Finset ℕ} (hres : _root_.Disjoint L (regQubitSet x.reserve ∪ regQubitSet z.reserve))
    (i : Fin k) :
    _root_.Disjoint (L ∪ allocSet (srcOf layout) (dstOf R layout ops) k)
      (regQubitSet ((dstOf R layout ops).xslot i).reserve ∪
        regQubitSet ((dstOf R layout ops).zslot i).reserve) := by
  have hfresh := freshBits_of_layout (R := R) (ops := ops) (layout := layout) hv hres
  have hxR : regQubitSet ((dstOf R layout ops).xslot i).reserve ⊆ regQubitSet (layout.xSplit.reserve i) := by
    rw [dst_x_eq hcap i]; exact grow_reserve_subset _ _
  have hzR : regQubitSet ((dstOf R layout ops).zslot i).reserve ⊆ regQubitSet (layout.zSplit.reserve i) := by
    rw [dst_z_eq hcap i]; exact grow_reserve_subset _ _
  have hxOwn : _root_.Disjoint (bitsX (srcOf layout) (dstOf R layout ops) i)
      (regQubitSet ((dstOf R layout ops).xslot i).reserve) := by
    rw [dst_x_eq hcap i]; exact allocBits_disjoint_grow_reserve _ _
  have hzOwn : _root_.Disjoint (bitsZ (srcOf layout) (dstOf R layout ops) i)
      (regQubitSet ((dstOf R layout ops).zslot i).reserve) := by
    rw [dst_z_eq hcap i]; exact allocBits_disjoint_grow_reserve _ _
  rw [Finset.disjoint_union_left]
  constructor
  · exact Finset.disjoint_of_subset_right
      (Finset.union_subset_union
        (hxR.trans (splitReserve_subset layout.xSplit hv.xSplit i))
        (hzR.trans (splitReserve_subset layout.zSplit hv.zSplit i))) hres
  · rw [Finset.disjoint_left]
    intro q hq hR
    obtain ⟨j, _, hq'⟩ := (mem_allocSet _ _).mp hq
    rcases Finset.mem_union.mp hR with hR | hR
    · rcases hq' with hq' | hq'
      · by_cases hij : j = i
        · subst hij; exact Finset.disjoint_left.mp hxOwn hq' hR
        · exact Finset.disjoint_left.mp (splitReserve_disjoint layout.xSplit hv.xSplit hij)
            (bitsX_subset j hq') (hxR hR)
      · exact Finset.disjoint_left.mp (crossReserve_disjoint layout hv i j) (hxR hR)
          (bitsZ_subset j hq')
    · rcases hq' with hq' | hq'
      · exact Finset.disjoint_left.mp (crossReserve_disjoint layout hv j i) (bitsX_subset j hq')
          (hzR hR)
      · by_cases hij : j = i
        · subst hij; exact Finset.disjoint_left.mp hzOwn hq' hR
        · exact Finset.disjoint_left.mp (splitReserve_disjoint layout.zSplit hv.zSplit hij)
            (bitsZ_subset j hq') (hzR hR)

lemma dst_inputSize (hcap : (srcOf layout).CanGrowToNeeds (neededWidthsBy R x z ops)) (i : Fin k) :
    phaseInputSize ((dstOf R layout ops).xslot i) ((dstOf R layout ops).zslot i)
      = nextSignedWidthBy R x z ops := by
  unfold phaseInputSize
  rw [targetSignedLayoutState_xslot_width_by R layout ops i hcap,
    targetSignedLayoutState_zslot_width_by R layout ops i hcap, max_self]
  rfl

/-- After the allocations, every chunk has the next width. -/
lemma dst_widths (hcap : (srcOf layout).CanGrowToNeeds (neededWidthsBy R x z ops)) (i : Fin k) :
    ((dstOf R layout ops).xslot i).width = nextSignedWidthBy R x z ops ∧
    ((dstOf R layout ops).zslot i).width = nextSignedWidthBy R x z ops :=
  ⟨by rw [targetSignedLayoutState_xslot_width_by R layout ops i hcap]; rfl,
   by rw [targetSignedLayoutState_zslot_width_by R layout ops i hcap]; rfl⟩

/-- The number of qubits one level activates is the immediate need. -/
lemma sum_bits (hcap : (srcOf layout).CanGrowToNeeds (neededWidthsBy R x z ops)) :
    ∑ i, (bitsX (srcOf layout) (dstOf R layout ops) i).card
        + ∑ i, (bitsZ (srcOf layout) (dstOf R layout ops) i).card
      = immediateXNeedBy R ops x.width z.width + immediateZNeedBy R ops x.width z.width := by
  have hW : nextWidthBy R ops x.width z.width = nextSignedWidthBy R x z ops :=
    Policy.nextSignedWidthBy_eq_widthModel R ops x z
  have hlimb : limbWidth k x.width z.width = phaseLimbWidth x z k := Policy.limbWidth_eq k x z
  have hX : immediateXNeedBy R ops x.width z.width = ∑ i : Fin k,
      (nextWidthBy R ops x.width z.width - phaseSplitLogicalWidth x.width (limbWidth k x.width z.width) k i) :=
    rfl
  have hZ : immediateZNeedBy R ops x.width z.width = ∑ i : Fin k,
      (nextWidthBy R ops x.width z.width - phaseSplitLogicalWidth z.width (limbWidth k x.width z.width) k i) :=
    rfl
  rw [hX, hZ, hW, hlimb]
  congr 1
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [bitsX, card_allocBits _ (by rw [extraDelta_x hcap i]; exact hcap.1 i), extraDelta_x hcap i]
    show _ - (layout.xSplit.child i).width = _
    rw [layout.xchild_width i]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [bitsZ, card_allocBits _ (by rw [extraDelta_z hcap i]; exact hcap.2 i), extraDelta_z hcap i]
    show _ - (layout.zSplit.child i).width = _
    rw [layout.zchild_width i]

lemma max_level (a c : ℕ) : max a (max (a + c) a) = a + c := by
  rw [max_eq_left (Nat.le_add_right a c), max_eq_right (Nat.le_add_right a c)]

/-- One compiled level: it returns the live set it started from, and its peak
is the start size plus the immediate need plus the larger of one child, if it
has one, and the body's scratch. -/
theorem level_walk (m : NegationMethod) (hv : layout.Valid) (hk : 1 < k) (phi : Angle) (coeff : Fin (q k) → ℚ)
    (hcap : (srcOf layout).CanGrowToNeeds (neededWidthsBy R x z ops))
    (ex : ExtReg → ExtReg → ℕ) (e : ℕ) {L : Finset ℕ}
    (hx : regQubitSet x.active ⊆ L) (hz : regQubitSet z.active ⊆ L)
    (hres : _root_.Disjoint L (regQubitSet x.reserve ∪ regQubitSet z.reserve))
    (hex : ∀ i, ex ((dstOf R layout ops).xslot i) ((dstOf R layout ops).zslot i) = e) :
    gGood (nextSignedWidthBy R x z ops) (compileOpsToSignedGateBy R k hk phi x z layout coeff ops) L ∧
    gAfter (compileOpsToSignedGateBy R k hk phi x z layout coeff ops) L = L ∧
    gPeak m ex (compileOpsToSignedGateBy R k hk phi x z layout coeff ops) L
      = L.card + (immediateXNeedBy R ops x.width z.width + immediateZNeedBy R ops x.width z.width)
        + max (if hasLeaf (annotatePhaseTermsAux k 0 ops) then e else 0)
            (Policy.opsScratch m ops (nextSignedWidthBy R x z ops)) := by
  have hfresh := freshBits_of_layout (R := R) (ops := ops) (layout := layout) hv hres
  obtain ⟨a1, p1, g1⟩ := allocs_walk m ex (nextSignedWidthBy R x z ops) hfresh k le_rfl
  obtain ⟨a3, p3, g3⟩ := deallocs_walk m ex (nextSignedWidthBy R x z ops) hfresh k le_rfl
  obtain ⟨a2, p2, g2⟩ := body_walk m hk phi coeff (dstOf R layout ops) ex e (nextSignedWidthBy R x z ops)
    (L ∪ allocSet (srcOf layout) (dstOf R layout ops) k) (dst_active_subset hcap hx hz)
    (fun i => ⟨dst_inputSize hcap i, (dst_active_subset hcap hx hz i).1,
      (dst_active_subset hcap hx hz i).2, dst_reserve_disjoint hv hcap hres i⟩)
    hex (dst_widths hcap) (annotatePhaseTermsAux k 0 ops)
  simp only [compileOpsToSignedGateBy, compileSignedAllocations, compileSignedDeallocations,
    gAfter, gPeak, gGood]
  rw [a1, a2, a3, p1, p2, p3]
  refine ⟨⟨g1, g2, g3⟩, rfl, ?_⟩
  rw [card_allocSet hfresh, sum_bits hcap, annScratch_annotate m]
  exact max_level _ _

/-- The controlled level: the same, with the control live. -/
theorem clevel_walk (m : NegationMethod) (hv : layout.Valid) (hk : 1 < k) (ctrl : ℕ) (phi : Angle) (coeff : Fin (q k) → ℚ)
    (hcap : (srcOf layout).CanGrowToNeeds (neededWidthsBy R x z ops))
    (ex : ExtReg → ExtReg → ℕ) (e : ℕ) {L : Finset ℕ} (hc : ctrl ∈ L)
    (hx : regQubitSet x.active ⊆ L) (hz : regQubitSet z.active ⊆ L)
    (hres : _root_.Disjoint L (regQubitSet x.reserve ∪ regQubitSet z.reserve))
    (hex : ∀ i, ex ((dstOf R layout ops).xslot i) ((dstOf R layout ops).zslot i) = e) :
    gGood (nextSignedWidthBy R x z ops) (controlPhaseLeaves ctrl (compileOpsToSignedGateBy R k hk phi x z layout coeff ops)) L ∧
    gAfter (controlPhaseLeaves ctrl (compileOpsToSignedGateBy R k hk phi x z layout coeff ops)) L = L ∧
    gPeak m ex (controlPhaseLeaves ctrl (compileOpsToSignedGateBy R k hk phi x z layout coeff ops)) L
      = L.card + (immediateXNeedBy R ops x.width z.width + immediateZNeedBy R ops x.width z.width)
        + max (if hasLeaf (annotatePhaseTermsAux k 0 ops) then e else 0)
            (Policy.opsScratch m ops (nextSignedWidthBy R x z ops)) := by
  have hfresh := freshBits_of_layout (R := R) (ops := ops) (layout := layout) hv hres
  obtain ⟨a1, p1, g1⟩ := allocs_walk m ex (nextSignedWidthBy R x z ops) hfresh k le_rfl
  obtain ⟨a3, p3, g3⟩ := deallocs_walk m ex (nextSignedWidthBy R x z ops) hfresh k le_rfl
  obtain ⟨a2, p2, g2⟩ := cbody_walk m hk ctrl phi coeff (dstOf R layout ops) ex e
    (nextSignedWidthBy R x z ops) (L ∪ allocSet (srcOf layout) (dstOf R layout ops) k)
    (Finset.mem_union_left _ hc) (dst_active_subset hcap hx hz)
    (fun i => ⟨dst_inputSize hcap i, (dst_active_subset hcap hx hz i).1,
      (dst_active_subset hcap hx hz i).2, dst_reserve_disjoint hv hcap hres i⟩)
    hex (dst_widths hcap) (annotatePhaseTermsAux k 0 ops)
  simp only [compileOpsToSignedGateBy, controlPhaseLeaves]
  rw [controlPhaseLeaves_compileSignedAllocations, controlPhaseLeaves_compileSignedDeallocations]
  simp only [compileSignedAllocations, compileSignedDeallocations, gAfter, gPeak, gGood]
  rw [a1, a2, a3, p1, p2, p3]
  refine ⟨⟨g1, g2, g3⟩, rfl, ?_⟩
  rw [card_allocSet hfresh, sum_bits hcap, annScratch_annotate m]
  exact max_level _ _

end Level

/-! ## Admissible tables recurse -/

lemma hasLeaf_annotate {k : ℕ} :
    ∀ (ops : Prog k) (m : ℕ), m < q k → 0 < phaseProductCount ops →
      hasLeaf (annotatePhaseTermsAux k m ops) = true := by
  intro ops
  induction ops with
  | nil => intro m _ h; simp [phaseProductCount] at h
  | cons op rest ih =>
      intro m hm hcount
      cases op with
      | phaseProduct i =>
          simp only [annotatePhaseTermsAux, dite_eq_left hm]
          rfl
      | shiftL i n =>
          simp only [phaseProductCount] at hcount
          exact ih m hm hcount
      | shiftR i n =>
          simp only [phaseProductCount] at hcount
          exact ih m hm hcount
      | negate i =>
          simp only [phaseProductCount] at hcount
          exact ih m hm hcount
      | addScaled d s b n =>
          simp only [phaseProductCount] at hcount
          exact ih m hm hcount

/-- Every table an admissible policy picks emits at least one phase product. -/
lemma hasLeaf_of_admissible {T : ToomCookTable} (h : T.Admissible) :
    hasLeaf (annotatePhaseTermsAux T.k 0 T.ops) = true := by
  have hk := T.hk
  have hcount : phaseProductCount T.ops = T.pts.length :=
    ProgConsumesPts.phaseProductCount_eq (by omega) _ _ _ h.2.1.consumes
  apply hasLeaf_annotate
  · simp [q]; omega
  · rw [hcount, T.hpts]; simp [q]; omega

/-! ## The budget unfolds along the plan -/

/-- The phase-product cost charged at a leaf. -/
def ppEx (P : ShorLoweringPolicy) (x z : ExtReg) : ℕ := Rec.peakReserve P x.width z.width

lemma peakReserve_of_stops {P : ShorLoweringPolicy} {x z : ExtReg} {n : ℕ}
    (hn : phaseInputSize x z = n) (hstop : P.Stops n (fun T => nextSignedWidthBy P.widthRule x z T.ops)) :
    Rec.peakReserve P x.width z.width = 0 := by
  rw [Rec.peakReserve]
  have hn' : max x.width z.width = n := hn
  rw [hn']
  cases hT : P.choose n with
  | none => rfl
  | some T =>
      dsimp only
      rw [dite_eq_right]
      rw [Policy.nextSignedWidthBy_eq_widthModel]
      exact hstop T hT

lemma peakReserve_of_step {P : ShorLoweringPolicy} {x z : ExtReg} {n : ℕ} {T : ToomCookTable}
    (hn : phaseInputSize x z = n) (hT : P.choose n = some T)
    (hrec : nextSignedWidthBy P.widthRule x z T.ops < n) :
    Rec.peakReserve P x.width z.width
      = immediateXNeedBy P.widthRule T.ops x.width z.width + immediateZNeedBy P.widthRule T.ops x.width z.width
        + max (Rec.peakReserve P (nextSignedWidthBy P.widthRule x z T.ops) (nextSignedWidthBy P.widthRule x z T.ops))
            (Policy.opsScratch P.negation T.ops (nextSignedWidthBy P.widthRule x z T.ops)) := by
  rw [Rec.peakReserve]
  have hn' : max x.width z.width = n := hn
  rw [hn', hT]
  dsimp only
  have hW := Policy.nextSignedWidthBy_eq_widthModel P.widthRule T.ops x z
  rw [dite_eq_left (by rw [hW]; exact hrec), hW]

/-! ## The plan induction -/

/-- The lowered circuit of any valid plan walks exactly as its gate does with
phase products charged `peakReserve`, scratch included, and is well formed. -/
theorem plan_walk {P : ShorLoweringPolicy} (hP : P.Admissible) {n : ℕ} {U : Gate}
    (p : PhaseLoweringPlan P n U) (hv : p.Valid) :
    ∀ L : Finset ℕ, gGood n U L →
      after (lowerGateRec p) true L = gAfter U L ∧
      peak (scratchFor P.negation) (lowerGateRec p) true L = gPeak P.negation (ppEx P) U L ∧
      WellFormed (lowerGateRec p) true L := by
  induction p with
  | id n => intro L _; simp [lowerGateRec, gAfter, gPeak, after, peak, WellFormed]
  | seq left right ihl ihr =>
      intro L h
      obtain ⟨hl, hr⟩ := h
      obtain ⟨al, pl, wl⟩ := ihl hv.1 L hl
      obtain ⟨ar, pr, wr⟩ := ihr hv.2 _ hr
      simp only [lowerGateRec, after, peak, WellFormed, gAfter, gPeak]
      rw [al, ar, pl, pr]
      exact ⟨rfl, rfl, wl, wr⟩
  | H _ _ | X _ _ | ShiftL _ _ _ | ShiftR _ _ _ | Negate _ _ | AddScaled _ _ _ _ _
  | zeroExtend _ _ _ | signExtend _ _ _ | zeroDealloc _ _ _ | signDealloc _ _ _
  | RadixReverse _ _ _ =>
      intro L h
      exact ⟨rfl, rfl, h⟩
  | signedBase phi x z =>
      intro L h
      obtain ⟨hn, hx, hz, _⟩ := h
      obtain ⟨a, pk, w⟩ := touch_walk_quiet P.negation L _ (touchIn_naive phi hx hz) (tmax_naive P.negation phi x z) true
      simp only [lowerGateRec, gAfter, gPeak, ppEx]
      rw [a, pk, peakReserve_of_stops hn (hn ▸ hv)]
      exact ⟨rfl, rfl, w⟩
  | signedStep phi x z T layout child ih =>
      obtain ⟨⟨hT, hrec, hlayout, hcap⟩, hvChild⟩ := hv
      intro L h
      obtain ⟨hn, hx, hz, hres⟩ := h
      have hex : ∀ i, ppEx P ((dstOf P.widthRule layout T.ops).xslot i) ((dstOf P.widthRule layout T.ops).zslot i)
          = Rec.peakReserve P (nextSignedWidthBy P.widthRule x z T.ops) (nextSignedWidthBy P.widthRule x z T.ops) := by
        intro i
        simp only [ppEx]
        rw [targetSignedLayoutState_xslot_width_by P.widthRule layout T.ops i hcap,
          targetSignedLayoutState_zslot_width_by P.widthRule layout T.ops i hcap]
        rfl
      obtain ⟨g, a, pk⟩ := level_walk P.negation (ops := T.ops) hlayout T.hk phi
        (cramerCoeffFromPtsWidth T.k (phaseLimbWidth x z T.k) T.pts T.hpts) hcap (ppEx P) _ hx hz hres hex
      obtain ⟨a', p', w'⟩ := ih hvChild L g
      simp only [lowerGateRec, gAfter, gPeak]
      refine ⟨a'.trans a, ?_, w'⟩
      rw [p', compiledSignedPhaseGateBy, pk, hasLeaf_of_admissible (hP.of_choose hT), ite_eq_left rfl,
        ppEx, peakReserve_of_step hn (hn ▸ hT) (hn ▸ hrec), Nat.add_assoc]
  | cSignedBase ctrl phi x z =>
      intro L h
      obtain ⟨hc, hn, hx, hz, _⟩ := h
      obtain ⟨a, pk, w⟩ := touch_walk_quiet P.negation L _ (touchIn_cnaive phi hc hx hz)
        (tmax_cnaive P.negation ctrl phi x z) true
      simp only [lowerGateRec, gAfter, gPeak, ppEx]
      rw [a, pk, peakReserve_of_stops hn (hn ▸ hv)]
      exact ⟨rfl, rfl, w⟩
  | cSignedStep ctrl phi x z T layout child ih =>
      obtain ⟨⟨⟨hT, hrec, hlayout, hcap⟩, -⟩, hvChild⟩ := hv
      intro L h
      obtain ⟨hc, hn, hx, hz, hres⟩ := h
      have hex : ∀ i, ppEx P ((dstOf P.widthRule layout T.ops).xslot i) ((dstOf P.widthRule layout T.ops).zslot i)
          = Rec.peakReserve P (nextSignedWidthBy P.widthRule x z T.ops) (nextSignedWidthBy P.widthRule x z T.ops) := by
        intro i
        simp only [ppEx]
        rw [targetSignedLayoutState_xslot_width_by P.widthRule layout T.ops i hcap,
          targetSignedLayoutState_zslot_width_by P.widthRule layout T.ops i hcap]
        rfl
      obtain ⟨g, a, pk⟩ := clevel_walk P.negation (ops := T.ops) hlayout T.hk ctrl phi
        (cramerCoeffFromPtsWidth T.k (phaseLimbWidth x z T.k) T.pts T.hpts) hcap (ppEx P) _ hc hx hz hres hex
      obtain ⟨a', p', w'⟩ := ih hvChild L g
      simp only [lowerGateRec, gAfter, gPeak]
      refine ⟨a'.trans a, ?_, w'⟩
      rw [p', compiledCSignedPhaseGateBy, compileOpsToCSignedGateBy, pk, hasLeaf_of_admissible (hP.of_choose hT), ite_eq_left rfl,
        ppEx, peakReserve_of_step hn (hn ▸ hT) (hn ▸ hrec), Nat.add_assoc]

/-! ## The phase-product facts -/

/-- A lowered signed phase product returns the live set it started from, uses
`peakReserve` qubits beyond it at its peak, scratch included, and never misuses
a qubit, when its
operands are live and their reserves are not. -/
theorem signedPhaseProductPeak (P : ShorLoweringPolicy) :
    P.Admissible →
    ∀ (phi : Angle) (x z : ExtReg), Policy.WorkspaceOK P x z → ∀ (L : Finset ℕ),
      regQubitSet x.active ⊆ L → regQubitSet z.active ⊆ L →
      _root_.Disjoint L (regQubitSet x.reserve ∪ regQubitSet z.reserve) →
      after (Policy.lowerSignedPhaseProd P phi x z) true L = L ∧
      (Policy.lowerSignedPhaseProd P phi x z).peakQubitsFor P.negation L
        = L.card + Rec.peakReserve P x.width z.width ∧
      WellFormed (Policy.lowerSignedPhaseProd P phi x z) true L := by
  intro hP phi x z hws L hx hz hres
  obtain ⟨a, pk, w⟩ := plan_walk hP (Policy.signedPlan P phi x z) (Policy.signedPlan_valid P phi x z hws) L
    ⟨rfl, hx, hz, hres⟩
  exact ⟨a, by simpa [LowGate.peakQubitsFor, gPeak, ppEx, Policy.lowerSignedPhaseProd] using pk, w⟩

/-- The controlled form, with the control qubit live. -/
theorem cSignedPhaseProductPeak (P : ShorLoweringPolicy) :
    P.Admissible →
    ∀ (ctrl : ℕ) (phi : Angle) (x z : ExtReg), Policy.CWorkspaceOK P ctrl x z →
      ∀ (L : Finset ℕ),
      ctrl ∈ L → regQubitSet x.active ⊆ L → regQubitSet z.active ⊆ L →
      _root_.Disjoint L (regQubitSet x.reserve ∪ regQubitSet z.reserve) →
      after (Policy.lowerCSignedPhaseProd P ctrl phi x z) true L = L ∧
      (Policy.lowerCSignedPhaseProd P ctrl phi x z).peakQubitsFor P.negation L
        = L.card + Rec.peakReserve P x.width z.width ∧
      WellFormed (Policy.lowerCSignedPhaseProd P ctrl phi x z) true L := by
  intro hP ctrl phi x z hws L hc hx hz hres
  obtain ⟨a, pk, w⟩ :=
    plan_walk hP (Policy.cSignedPlan P ctrl phi x z)
      (Policy.cSignedPlan_valid P ctrl phi x z hws) L ⟨hc, rfl, hx, hz, hres⟩
  exact ⟨a, by simpa [LowGate.peakQubitsFor, gPeak, ppEx, Policy.lowerCSignedPhaseProd] using pk, w⟩

end QubitCount
end Shor
