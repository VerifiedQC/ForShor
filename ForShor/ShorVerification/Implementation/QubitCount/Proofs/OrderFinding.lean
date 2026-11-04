import ForShor.ShorVerification.Implementation.QubitCount.Proofs.ModMul

/-!
# Qubit count: the order-finding circuit

The order-finding circuit is a Hadamard layer on the exponent register, the
initialisation of the data register, one controlled modular multiplication
per exponent qubit, and an inverse QFT on the exponent register. From the set
of its five registers' active qubits (the data register with its carry bit),
each part returns to that set, so the peak is the set's size plus the
largest part's extra.
-/

namespace Shor
namespace QubitCount

open Gate

variable {P : ShorLoweringPolicy} {pc : ℕ → ℕ → ℕ → ℕ → ℕ}

/-! ## Ownership as sets -/

/-- Every qubit a register owns. -/
def ownSet (e : ExtReg) : Finset ℕ := regQubitSet e.active ∪ regQubitSet e.reserve

lemma ownSet_disjoint {a b : ExtReg} (h : ExtReg.OwnedDisjoint a b) :
    _root_.Disjoint (ownSet a) (ownSet b) := by
  rw [Finset.disjoint_left]
  intro q ha hb
  simp only [ownSet, Finset.mem_union, mem_regQubitSet] at ha hb
  have ha' : q ∈ a.ownedQubits := by simp only [ExtReg.ownedQubits, List.mem_append]; exact ha
  have hb' : q ∈ b.ownedQubits := by simp only [ExtReg.ownedQubits, List.mem_append]; exact hb
  exact List.disjoint_left.mp h ha' hb'

lemma not_mem_ownSet {e : ExtReg} {q : ℕ} (h : q ∉ e.ownedQubits) : q ∉ ownSet e := by
  intro hq
  simp only [ownSet, Finset.mem_union, mem_regQubitSet] at hq
  exact h (by simp only [ExtReg.ownedQubits, List.mem_append]; exact hq)

lemma active_sub_own (e : ExtReg) : regQubitSet e.active ⊆ ownSet e := Finset.subset_union_left
lemma reserve_sub_own (e : ExtReg) : regQubitSet e.reserve ⊆ ownSet e := Finset.subset_union_right

lemma ownSet_grow (e : ExtReg) (n : ℕ) : ownSet (e.grow n) = ownSet e := by
  ext q
  simp only [ownSet, Finset.mem_union, mem_regQubitSet]
  have h := congrArg (q ∈ ·) (Gate.ExtReg.ownedQubits_grow e n)
  simp only [ExtReg.ownedQubits, List.mem_append] at h
  exact Iff.of_eq h

lemma yGrow_active_sub (y : ExtReg) : regQubitSet (y.grow 1).active ⊆ ownSet y := by
  rw [← ownSet_grow y 1]; exact active_sub_own _

lemma yGrow_reserve_sub (y : ExtReg) : regQubitSet (y.grow 1).reserve ⊆ ownSet y := by
  rw [← ownSet_grow y 1]; exact reserve_sub_own _

/-! ## The base set -/

section Base

variable {x y work scratch : ExtReg} {flag N : ℕ}
  (hmod : ModMulCircuitWorkspaceOK y work)
  (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
  (hlay : OrderFindingSpaceLayout x y work scratch flag)

local notation "L0" => orderFindingBaseSet x y work scratch flag

include hmod hs4 hlay

lemma base_facts :
    _root_.Disjoint (ownSet x) (ownSet y) ∧ _root_.Disjoint (ownSet x) (ownSet work) ∧
    _root_.Disjoint (ownSet x) (ownSet scratch) ∧ _root_.Disjoint (ownSet y) (ownSet work) ∧
    _root_.Disjoint (ownSet y) (ownSet scratch) ∧ _root_.Disjoint (ownSet work) (ownSet scratch) ∧
    flag ∉ ownSet x ∧ flag ∉ ownSet y ∧ flag ∉ ownSet work ∧ flag ∉ ownSet scratch := by
  have hys := ownSet_disjoint hs4.data_scratch_disjoint
  have hfy := not_mem_ownSet hs4.flag_not_data
  rw [ownSet_grow] at hys hfy
  exact ⟨ownSet_disjoint hlay.exponent_data_disjoint, ownSet_disjoint hlay.exponent_work_disjoint,
    ownSet_disjoint hlay.exponent_scratch_disjoint, ownSet_disjoint hmod.2.2, hys,
    ownSet_disjoint hs4.work_scratch_disjoint, not_mem_ownSet hlay.flag_outside_exponent, hfy,
    not_mem_ownSet hs4.flag_not_work, not_mem_ownSet hs4.flag_not_scratch⟩

omit hmod hs4 hlay in
/-- Every qubit of the base set lies in one of the five registers' live parts. -/
lemma mem_base {q : ℕ} (hq : q ∈ L0) :
    q ∈ regQubitSet x.active ∨ q ∈ regQubitSet (y.grow 1).active ∨ q ∈ regQubitSet work.active ∨
      q ∈ regQubitSet scratch.active ∨ q = flag := by
  simp only [orderFindingBaseSet, Finset.mem_union, Finset.mem_singleton] at hq
  tauto

omit hmod hs4 hlay in
/-- A set that the five live parts avoid is disjoint from the base set. -/
lemma base_disjoint {R : Finset ℕ} (hx : _root_.Disjoint (regQubitSet x.active) R)
    (hy : _root_.Disjoint (regQubitSet (y.grow 1).active) R)
    (hw : _root_.Disjoint (regQubitSet work.active) R)
    (hs : _root_.Disjoint (regQubitSet scratch.active) R) (hf : flag ∉ R) :
    _root_.Disjoint L0 R := by
  rw [Finset.disjoint_left]
  intro q hq hR
  rcases mem_base hq with h | h | h | h | h
  · exact Finset.disjoint_left.mp hx h hR
  · exact Finset.disjoint_left.mp hy h hR
  · exact Finset.disjoint_left.mp hw h hR
  · exact Finset.disjoint_left.mp hs h hR
  · subst h; exact hf hR

omit hmod hs4 hlay in
lemma mem_base_of {q : ℕ} (hq : q ∈ regQubitSet x.active ∨ q ∈ regQubitSet (y.grow 1).active ∨
    q ∈ regQubitSet work.active ∨ q ∈ regQubitSet scratch.active ∨ q = flag) : q ∈ L0 := by
  simp only [orderFindingBaseSet, Finset.mem_union, Finset.mem_singleton]
  tauto

lemma mulSpace_base {ctrl : ℕ} (hc : ctrl ∈ regQubitSet x.active) :
    MulSpace y work scratch flag ctrl L0 := by
  obtain ⟨hxy, hxw, hxs, hyw, hys, hws, _, hfy, hfw, hfs⟩ := base_facts hmod hs4 hlay
  have hyA := yGrow_active_sub y
  have hyR := yGrow_reserve_sub y
  exact
    { ctrl_mem := mem_base_of (Or.inl hc)
      flag_mem := mem_base_of (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      data_live := fun q h => mem_base_of (Or.inr (Or.inl h))
      work_live := fun q h => mem_base_of (Or.inr (Or.inr (Or.inl h)))
      scratch_live := fun q h => mem_base_of (Or.inr (Or.inr (Or.inr (Or.inl h))))
      data_res := base_disjoint
        (Finset.disjoint_of_subset_left (active_sub_own x) (Finset.disjoint_of_subset_right hyR hxy))
        (active_reserve_disjoint (y.grow 1))
        (Finset.disjoint_of_subset_left (active_sub_own work)
          (Finset.disjoint_of_subset_right hyR hyw.symm))
        (Finset.disjoint_of_subset_left (active_sub_own scratch)
          (Finset.disjoint_of_subset_right hyR hys.symm))
        (fun h => hfy (hyR h))
      work_res := base_disjoint
        (Finset.disjoint_of_subset_left (active_sub_own x)
          (Finset.disjoint_of_subset_right (reserve_sub_own work) hxw))
        (Finset.disjoint_of_subset_left hyA
          (Finset.disjoint_of_subset_right (reserve_sub_own work) hyw))
        (active_reserve_disjoint work)
        (Finset.disjoint_of_subset_left (active_sub_own scratch)
          (Finset.disjoint_of_subset_right (reserve_sub_own work) hws.symm))
        (fun h => hfw (reserve_sub_own work h))
      scratch_res := base_disjoint
        (Finset.disjoint_of_subset_left (active_sub_own x)
          (Finset.disjoint_of_subset_right (reserve_sub_own scratch) hxs))
        (Finset.disjoint_of_subset_left hyA
          (Finset.disjoint_of_subset_right (reserve_sub_own scratch) hys))
        (Finset.disjoint_of_subset_left (active_sub_own work)
          (Finset.disjoint_of_subset_right (reserve_sub_own scratch) hws))
        (active_reserve_disjoint scratch)
        (fun h => hfs (reserve_sub_own scratch h))
      data_work := Finset.disjoint_of_subset_left hyR
        (Finset.disjoint_of_subset_right (reserve_sub_own work) hyw)
      data_scratch := Finset.disjoint_of_subset_left hyR
        (Finset.disjoint_of_subset_right (reserve_sub_own scratch) hys)
      work_scratch := Finset.disjoint_of_subset_left (reserve_sub_own work)
        (Finset.disjoint_of_subset_right (reserve_sub_own scratch) hws) }

/-- The exponent register's reserve is not live. -/
lemma base_x_reserve : _root_.Disjoint L0 (regQubitSet x.reserve) := by
  obtain ⟨hxy, hxw, hxs, _, _, _, hfx, _, _, _⟩ := base_facts hmod hs4 hlay
  exact base_disjoint (active_reserve_disjoint x)
    (Finset.disjoint_of_subset_left (yGrow_active_sub y)
      (Finset.disjoint_of_subset_right (reserve_sub_own x) hxy.symm))
    (Finset.disjoint_of_subset_left (active_sub_own work)
      (Finset.disjoint_of_subset_right (reserve_sub_own x) hxw.symm))
    (Finset.disjoint_of_subset_left (active_sub_own scratch)
      (Finset.disjoint_of_subset_right (reserve_sub_own x) hxs.symm))
    (fun h => hfx (reserve_sub_own x h))

/-- The base set's size is the sum of the five live parts. -/
lemma base_card :
    (L0).card = x.width + (y.width + 1) + work.width + scratch.width + 1 := by
  obtain ⟨hxy, hxw, hxs, hyw, hys, hws, hfx, hfy, hfw, hfs⟩ := base_facts hmod hs4 hlay
  have hyA := yGrow_active_sub y
  have hcap1 : y.CanGrow 1 := le_trans (by norm_num) hmod.1
  have d1 : _root_.Disjoint (regQubitSet x.active) (regQubitSet (y.grow 1).active) :=
    Finset.disjoint_of_subset_left (active_sub_own x) (Finset.disjoint_of_subset_right hyA hxy)
  have d2 : _root_.Disjoint (regQubitSet x.active ∪ regQubitSet (y.grow 1).active)
      (regQubitSet work.active) :=
    Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_of_subset_left (active_sub_own x)
        (Finset.disjoint_of_subset_right (active_sub_own work) hxw),
       Finset.disjoint_of_subset_left hyA (Finset.disjoint_of_subset_right (active_sub_own work) hyw)⟩
  have d3 : _root_.Disjoint (regQubitSet x.active ∪ regQubitSet (y.grow 1).active ∪
      regQubitSet work.active) (regQubitSet scratch.active) :=
    Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_left.mpr
        ⟨Finset.disjoint_of_subset_left (active_sub_own x)
          (Finset.disjoint_of_subset_right (active_sub_own scratch) hxs),
         Finset.disjoint_of_subset_left hyA
          (Finset.disjoint_of_subset_right (active_sub_own scratch) hys)⟩,
       Finset.disjoint_of_subset_left (active_sub_own work)
        (Finset.disjoint_of_subset_right (active_sub_own scratch) hws)⟩
  have d4 : flag ∉ regQubitSet x.active ∪ regQubitSet (y.grow 1).active ∪
      regQubitSet work.active ∪ regQubitSet scratch.active := by
    simp only [Finset.mem_union, not_or]
    exact ⟨⟨⟨fun h => hfx (active_sub_own x h), fun h => hfy (hyA h)⟩,
      fun h => hfw (active_sub_own work h)⟩, fun h => hfs (active_sub_own scratch h)⟩
  have hgw : (y.grow 1).width = y.width + 1 := ExtReg.width_grow y 1 hcap1
  simp only [orderFindingBaseSet]
  rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr d4),
    Finset.card_union_of_disjoint d3, Finset.card_union_of_disjoint d2,
    Finset.card_union_of_disjoint d1, card_regQubitSet, card_regQubitSet, card_regQubitSet,
    card_regQubitSet, Finset.card_singleton]
  rw [show regSize (y.grow 1).active = (y.grow 1).width from rfl, hgw]
  rfl

end Base

/-! ## The exponentiation -/

lemma modExpSteps_fact {D W S : ExtReg} {flag a N : ℕ} {L : Finset ℕ}
    (hmod : ModMulCircuitWorkspaceOK D W) (hs4 : CmpLtNWWorkspace N (D.grow 1) W S flag) :
    ∀ (ctrls : List ℕ) (e : ℕ), (∀ c ∈ ctrls, MulSpace D W S flag c L) →
      SFact P pc (modExpApproxStepsValid a N D W S flag hmod hs4 e ctrls) true L L
        (L.card + if ctrls = [] then 0 else
          Rec.modMulPeakWith P pc D.width D.capacity W.width W.capacity S.width S.capacity) := by
  intro ctrls
  induction ctrls with
  | nil => intro e _; exact SFact.id true L
  | cons ctrl rest ih =>
      intro e h
      have f1 := core_fact (P := P) (pc := pc) ((a ^ (2 ^ e)) % N) N hmod hs4 (h ctrl (by simp))
      have f2 := ih (e + 1) (fun c hc => h c (List.mem_cons_of_mem _ hc))
      refine (SFact.seq f1 f2).congr_peak ?_
      simp only [reduceCtorEq, ite_false]
      congr 1
      split <;> simp

/-! ## The order-finding circuit -/

theorem orderFinding_fact {x y work scratch : ExtReg} {flag N : ℕ} (a : ℕ)
    (hmod : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hlay : OrderFindingSpaceLayout x y work scratch flag) :
    SFact P pc (orderFindingApprox a N x y work scratch flag hmod hs4) true
      (orderFindingBaseSet x y work scratch flag) (orderFindingBaseSet x y work scratch flag)
      ((orderFindingBaseSet x y work scratch flag).card
        + Rec.orderFindingPeakWith P pc x.width y.width y.capacity work.width work.capacity
          scratch.width scratch.capacity) := by
  set L0 := orderFindingBaseSet x y work scratch flag with hL0
  have hx : regQubitSet x.active ⊆ L0 := fun q h => mem_base_of (Or.inl h)
  have hy : regQubitSet (y.grow 1).active ⊆ L0 :=
    fun q h => mem_base_of (Or.inr (Or.inl h))
  have fH := SFact.H_reg (P := P) (pc := pc) hx true
  have fI : SFact P pc (initY1 y.active) true L0 L0 (L0.card + 0) := by
    unfold initY1
    split
    · exact SFact.id true L0
    · next q rest heq =>
        apply SFact.X
        apply hy
        rw [grow_active]
        apply Finset.mem_union_left
        rw [mem_regQubitSet, heq]
        exact List.mem_cons_self
  have fM := modExpSteps_fact (P := P) (pc := pc) (a := a) (L := L0) hmod hs4 x.active.qubits 0
    (fun c hc => mulSpace_base hmod hs4 hlay ((mem_regQubitSet).mpr hc))
  have fQ : SFact P pc (IQFT x) true L0 L0 (L0.card + Rec.qftPeak P x.width) :=
    SFact.adj (SFact.qft hx (base_x_reserve hmod hs4 hlay) false)
  have := SFact.seq fH (SFact.seq fI (SFact.seq fM fQ))
  refine this.congr_peak ?_
  congr 1
  simp only [Rec.orderFindingPeakWith]
  have hw : x.width = x.active.qubits.length := rfl
  by_cases hnil : x.active.qubits = []
  · have : ¬ 0 < x.width := by rw [hw, hnil]; simp
    simp [hnil, this]
  · have : 0 < x.width := by rw [hw]; exact List.length_pos_of_ne_nil hnil
    simp [hnil, this]

/-! ## The claims -/

theorem orderFindingPeakFormulaRec (P : ShorLoweringPolicy) : Rec.OrderFindingPeakFormula P := by
  intro hP a N x y work scratch flag hmod hs4 hws hlay
  obtain ⟨g, -, hp⟩ := orderFinding_fact (P := P) (pc := Rec.ppPeak P) a hmod hs4 hlay
  obtain ⟨-, lp⟩ := lower_walk P hP _ hws true _ g
  have hcard := base_card hmod hs4 hlay
  show peak QubitCount.scratch (Policy.lowerGate P _ hws) true _ = _
  rw [lp, hp, hcard]; rfl

lemma reference_aux (P : ShorLoweringPolicy) (hP : P.Admissible) (inst : ShorOrderFindingInstance)
    (m : ℕ)
    (hws : Policy.GateWorkspaceOK P (orderFindingApprox inst.a inst.N
      (Reference.allocateReferenceLayout P inst m).x (Reference.allocateReferenceLayout P inst m).data
      (Reference.allocateReferenceLayout P inst m).work
      (Reference.allocateReferenceLayout P inst m).scratch
      (Reference.allocateReferenceLayout P inst m).flag
      (Reference.reference_modMulCircuitWorkspaceOK P inst m)
      (Reference.reference_step4Workspace P inst m))) :
    (orderFindingApproxLow P inst.a inst.N (Reference.allocateReferenceLayout P inst m).x
      (Reference.allocateReferenceLayout P inst m).data (Reference.allocateReferenceLayout P inst m).work
      (Reference.allocateReferenceLayout P inst m).scratch (Reference.allocateReferenceLayout P inst m).flag
        (Reference.reference_modMulCircuitWorkspaceOK P inst m)
        (Reference.reference_step4Workspace P inst m) hws).peakQubits
        (orderFindingBaseSet (Reference.allocateReferenceLayout P inst m).x
          (Reference.allocateReferenceLayout P inst m).data
          (Reference.allocateReferenceLayout P inst m).work
          (Reference.allocateReferenceLayout P inst m).scratch
          (Reference.allocateReferenceLayout P inst m).flag)
      = Reference.referenceXWidth inst + (Reference.referenceDataWidth inst + 1)
          + Reference.referenceWorkWidth inst m + Reference.referenceScratchWidth inst m + 1
        + Rec.orderFindingPeak P (Reference.referenceXWidth inst)
          (Reference.referenceDataWidth inst) (Reference.referenceWorkWidth inst m)
          (Reference.referenceScratchWidth inst m) := by
  have hlay : OrderFindingSpaceLayout (Reference.allocateReferenceLayout P inst m).x
      (Reference.allocateReferenceLayout P inst m).data
      (Reference.allocateReferenceLayout P inst m).work
      (Reference.allocateReferenceLayout P inst m).scratch
      (Reference.allocateReferenceLayout P inst m).flag :=
    ⟨Reference.reference_exponent_data_disjoint P inst m,
     Reference.reference_exponent_work_disjoint P inst m,
     Reference.reference_exponent_scratch_disjoint P inst m,
     Reference.reference_flag_outside_exponent P inst m⟩
  have hp := orderFindingPeakFormulaRec P hP inst.a inst.N (Reference.allocateReferenceLayout P inst m).x
      (Reference.allocateReferenceLayout P inst m).data (Reference.allocateReferenceLayout P inst m).work
      (Reference.allocateReferenceLayout P inst m).scratch (Reference.allocateReferenceLayout P inst m).flag
    (Reference.reference_modMulCircuitWorkspaceOK P inst m)
    (Reference.reference_step4Workspace P inst m) hws hlay
  have hxw : (Reference.allocateReferenceLayout P inst m).x.width = Reference.referenceXWidth inst :=
    Reference.allocateReferenceLayout_x_width P inst m
  have hdw : (Reference.allocateReferenceLayout P inst m).data.width
      = Reference.referenceDataWidth inst :=
    Reference.allocateReferenceLayout_data_width P inst m
  have hww : (Reference.allocateReferenceLayout P inst m).work.width
      = Reference.referenceWorkWidth inst m :=
    Reference.allocateReferenceLayout_work_width P inst m
  have hsw : (Reference.allocateReferenceLayout P inst m).scratch.width
      = Reference.referenceScratchWidth inst m :=
    Reference.allocateReferenceLayout_scratch_width P inst m
  rw [hxw, hdw, hww, hsw] at hp
  exact hp

theorem referencePeakFormulaRec (P : ShorLoweringPolicy) : Rec.ReferencePeakFormula P := by
  intro hP inst m
  exact reference_aux P hP inst m _

end QubitCount
end Shor
