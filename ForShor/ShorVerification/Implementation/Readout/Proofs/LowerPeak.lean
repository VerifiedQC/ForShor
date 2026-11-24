import ForShor.ShorVerification.Implementation.Readout.Lowering
import ForShor.ShorVerification.Implementation.QubitCount.Proofs.BalancedU

/-!
# Readout: the peak of the lowered semiclassical circuit

`semiclassical_peak_formula` proves `Policy.SemiclassicalPeakFormula P` for every
policy: the lowered real circuit `orderFindingSemiclassicalLow` (initY1, then `m ≥ 1`
rounds `H c ;; CmodMulInPlaceCore … (ctrl := c) ;; ffPhase c j ;; H c ;; measureReset c`),
walked from `orderFindingBaseSetSC`, peaks at `Policy.orderFindingQubitsSC`.

The proof mirrors `orderFindingPeakFormulaRec`. Each unitary part is walked by the
existing machinery: `lower_walk` turns the walk of `Policy.lowerGate P u` into the
opaque-block walk of `u`, whose facts (`SFact`) are the existing ones: `SFact.H`,
`SFact.X` for `initY1`, and `core_fact` for the real multiplier, which holds for
any control qubit `ctrl` that is live while the multiplier's registers are live
and their reserves are not (`MulSpace`). The new steps are `ffPhase c j` and
`measureReset c` on the live control (`insert c L = L`, no allocation) and the
induction over the rounds.

`semiclassical_peak_eq` is the form for every `m`: the peak is
`|base| + (if m = 0 then 0 else orderFindingPeakSC)`.
-/

namespace Shor
namespace Readout

open QubitCount

variable {P : ShorLoweringPolicy}

/-! ## Walk facts for `MLowGate` -/

/-- `g`, walked forwards from `L` with the scratch of `P.negation`, ends at `M` and
peaks at `p`. -/
def MFact (P : ShorLoweringPolicy) (g : MLowGate) (L M : Finset ℕ) (p : ℕ) : Prop :=
  MLowGate.after g L = M ∧ MLowGate.peakQubitsFor P.negation g L = p

lemma MFact.seq {a b : MLowGate} {L M K : Finset ℕ} {c x y : ℕ}
    (ha : MFact P a L M (c + x)) (hb : MFact P b M K (c + y)) :
    MFact P (.seq a b) L K (c + max x y) := by
  obtain ⟨a1, p1⟩ := ha
  obtain ⟨a2, p2⟩ := hb
  refine ⟨?_, ?_⟩
  · show MLowGate.after b (MLowGate.after a L) = K
    rw [a1, a2]
  · show max (MLowGate.peak _ a L) (MLowGate.peak _ b (MLowGate.after a L)) = _
    rw [a1]
    show max (MLowGate.peakQubitsFor P.negation a L) (MLowGate.peakQubitsFor P.negation b M) = _
    rw [p1, p2, max_add_add_left]

lemma MFact.congr_peak {g : MLowGate} {L M : Finset ℕ} {p p' : ℕ} (h : MFact P g L M p)
    (e : p = p') : MFact P g L M p' := e ▸ h

/-- A lowered unitary part walks as its opaque-block walk (`lower_walk`). -/
lemma MFact.lowered (hP : P.Admissible) {u : Gate} (hws : Policy.GateWorkspaceOK P u)
    {L M : Finset ℕ} {p : ℕ} (h : SFact P (Rec.ppPeak P) u true L M p) :
    MFact P (.unitary (Policy.lowerGate P u hws)) L M p := by
  obtain ⟨g, a, pk⟩ := h
  obtain ⟨la, lp⟩ := lower_walk P hP u hws true L g
  exact ⟨la.trans a, lp.trans pk⟩

/-- `measureReset q` on a live qubit: nothing allocated. -/
lemma MFact.measureReset {q : ℕ} {L : Finset ℕ} (hq : q ∈ L) :
    MFact P (.measureReset q) L L (L.card + 0) := by
  refine ⟨Finset.insert_eq_of_mem hq, ?_⟩
  show (insert q L).card = _
  rw [Finset.insert_eq_of_mem hq, Nat.add_zero]

/-- `ffPhase q j` on a live qubit: nothing allocated. -/
lemma MFact.ffPhase {q j : ℕ} {L : Finset ℕ} (hq : q ∈ L) :
    MFact P (.ffPhase q j) L L (L.card + 0) := by
  refine ⟨Finset.insert_eq_of_mem hq, ?_⟩
  show QubitCount.peak (scratchFor P.negation) (LowGate.Phase q 0) true L = _
  simp [QubitCount.peak, LowGate.usedQubits, hq]

/-! ## Gate lowerings that walk as their opaque-block walk -/

/-- The gate lowering `f` walks every unitary part as the opaque-block walk with the
phase-product budget `pc` (`SFact P pc`). -/
def LowersAs (P : ShorLoweringPolicy) (pc : ℕ → ℕ → ℕ → ℕ → ℕ)
    (f : (u : Gate) → Policy.GateWorkspaceOK P u → LowGate) : Prop :=
  ∀ (u : Gate) (hws : Policy.GateWorkspaceOK P u) (L M : Finset ℕ) (p : ℕ),
    SFact P pc u true L M p → MFact P (.unitary (f u hws)) L M p

/-- `Policy.lowerGate` walks with the direct budget (`lower_walk`). -/
lemma lowersAs_direct (hP : P.Admissible) : LowersAs P (Rec.ppPeak P) (Policy.lowerGate P) :=
  fun _ hws _ _ _ h => MFact.lowered hP hws h

/-- The balanced lowering walks with the site budget (`balance_walk`, then `lower_walk`). -/
lemma lowersAs_balanced (hP : P.Admissible) (R : Balanced.Rule) :
    LowersAs P (Rec.sitePeak P R)
      (fun u h => Policy.lowerGate P (Balanced.balance P R u) (Balanced.balance_ok P R u h)) := by
  intro u hws L M p h
  obtain ⟨g, a, pk⟩ := h
  obtain ⟨gb, ab, pb⟩ := balance_walk (P := P) R u hws true L g
  exact MFact.lowered hP (Balanced.balance_ok P R u hws) ⟨gb, ab.trans a, pb.trans pk⟩

/-! ## The rounds -/

variable {pc : ℕ → ℕ → ℕ → ℕ → ℕ} {f : (u : Gate) → Policy.GateWorkspaceOK P u → LowGate}

/-- One lowered round on a live control `c`, when the multiplier returns to `L`
and peaks `e` above it. -/
lemma round_fact (hf : LowersAs P pc f) {U : Gate} {c j : ℕ} {L : Finset ℕ} {e : ℕ}
    (hc : c ∈ L) (hU : SFact P pc U true L L (L.card + e))
    (hws : MGate.WorkspaceOK P (.seq (.unitary (Gate.H c)) (.seq (.unitary U)
        (.seq (.ffPhase c j) (.seq (.unitary (Gate.H c)) (.measureReset c)))))) :
    MFact P (Policy.lowerMWith P f (.seq (.unitary (Gate.H c)) (.seq (.unitary U)
        (.seq (.ffPhase c j) (.seq (.unitary (Gate.H c)) (.measureReset c))))) hws)
      L L (L.card + e) := by
  have fH := hf _ hws.1 _ _ _ (SFact.H (P := P) (pc := pc) hc true)
  have fH' := hf _ hws.2.2.2.1 _ _ _ (SFact.H (P := P) (pc := pc) hc true)
  have fU := hf _ hws.2.1 _ _ _ hU
  have := MFact.seq fH (MFact.seq fU (MFact.seq (MFact.ffPhase (P := P) (j := j) hc)
    (MFact.seq fH' (MFact.measureReset (P := P) hc))))
  refine this.congr_peak ?_
  simp

/-- **The rounds.** `m` lowered rounds on a live control `c`, each multiplier
returning to `L` and peaking `e` above it, return to `L` and peak `e` above it
(`0` with no round). -/
theorem rounds_fact (hf : LowersAs P pc f) (U : ℕ → Gate) {c : ℕ} {L : Finset ℕ} {e : ℕ}
    (hc : c ∈ L) (hU : ∀ j, SFact P pc (U j) true L L (L.card + e)) :
    ∀ (m : ℕ) (hws : MGate.WorkspaceOK P (readoutRounds U c m)),
      MFact P (Policy.lowerMWith P f (readoutRounds U c m) hws) L L
        (L.card + if m = 0 then 0 else e) := by
  intro m
  induction m with
  | zero =>
      intro hws
      exact (hf _ hws _ _ _ (SFact.id (P := P) (pc := pc) true L)).congr_peak (by simp)
  | succ k ih =>
      intro hws
      have := MFact.seq (ih hws.1) (round_fact (j := k) hf hc (hU k) hws.2)
      refine this.congr_peak ?_
      simp only [Nat.succ_ne_zero, ite_false]
      congr 1
      split <;> simp

/-! ## The base set -/

section Base

variable {c : ℕ} {y work scratch : ExtReg} {flag N : ℕ}
  (hmod : ModMulCircuitWorkspaceOK y work)
  (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
  (hlay : SemiclassicalLayout c y work scratch flag)

local notation "L0" => orderFindingBaseSetSC c y work scratch flag

omit hmod hs4 hlay in
lemma mem_baseSC {q : ℕ} (hq : q ∈ L0) :
    q = c ∨ q ∈ regQubitSet (y.grow 1).active ∨ q ∈ regQubitSet work.active ∨
      q ∈ regQubitSet scratch.active ∨ q = flag := by
  simp only [orderFindingBaseSetSC, Finset.mem_union, Finset.mem_singleton] at hq
  tauto

omit hmod hs4 hlay in
lemma mem_baseSC_of {q : ℕ} (hq : q = c ∨ q ∈ regQubitSet (y.grow 1).active ∨
    q ∈ regQubitSet work.active ∨ q ∈ regQubitSet scratch.active ∨ q = flag) : q ∈ L0 := by
  simp only [orderFindingBaseSetSC, Finset.mem_union, Finset.mem_singleton]
  tauto

omit hmod hs4 hlay in
lemma baseSC_disjoint {R : Finset ℕ} (hc : c ∉ R)
    (hy : _root_.Disjoint (regQubitSet (y.grow 1).active) R)
    (hw : _root_.Disjoint (regQubitSet work.active) R)
    (hs : _root_.Disjoint (regQubitSet scratch.active) R) (hf : flag ∉ R) :
    _root_.Disjoint L0 R := by
  rw [Finset.disjoint_left]
  intro q hq hR
  rcases mem_baseSC hq with h | h | h | h | h
  · subst h; exact hc hR
  · exact Finset.disjoint_left.mp hy h hR
  · exact Finset.disjoint_left.mp hw h hR
  · exact Finset.disjoint_left.mp hs h hR
  · subst h; exact hf hR

include hmod hs4 hlay in
/-- The base set is a live set the real multiplier, controlled by `c`, can run from. -/
lemma mulSpace_baseSC : MulSpace y work scratch flag c L0 := by
  have hyw := ownSet_disjoint hmod.2.2
  have hys := ownSet_disjoint hs4.data_scratch_disjoint
  have hws := ownSet_disjoint hs4.work_scratch_disjoint
  have hfy := not_mem_ownSet hs4.flag_not_data
  rw [ownSet_grow] at hys hfy
  have hfw := not_mem_ownSet hs4.flag_not_work
  have hfs := not_mem_ownSet hs4.flag_not_scratch
  have hcy := not_mem_ownSet hlay.c_not_mem_data
  have hcw := not_mem_ownSet hlay.c_not_mem_work
  have hcs := not_mem_ownSet hlay.c_not_mem_scratch
  have hyA := yGrow_active_sub y
  have hyR := yGrow_reserve_sub y
  exact
    { ctrl_mem := mem_baseSC_of (Or.inl rfl)
      flag_mem := mem_baseSC_of (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      data_live := fun q h => mem_baseSC_of (Or.inr (Or.inl h))
      work_live := fun q h => mem_baseSC_of (Or.inr (Or.inr (Or.inl h)))
      scratch_live := fun q h => mem_baseSC_of (Or.inr (Or.inr (Or.inr (Or.inl h))))
      data_res := baseSC_disjoint (fun h => hcy (hyR h))
        (active_reserve_disjoint (y.grow 1))
        (Finset.disjoint_of_subset_left (active_sub_own work)
          (Finset.disjoint_of_subset_right hyR hyw.symm))
        (Finset.disjoint_of_subset_left (active_sub_own scratch)
          (Finset.disjoint_of_subset_right hyR hys.symm))
        (fun h => hfy (hyR h))
      work_res := baseSC_disjoint (fun h => hcw (reserve_sub_own work h))
        (Finset.disjoint_of_subset_left hyA
          (Finset.disjoint_of_subset_right (reserve_sub_own work) hyw))
        (active_reserve_disjoint work)
        (Finset.disjoint_of_subset_left (active_sub_own scratch)
          (Finset.disjoint_of_subset_right (reserve_sub_own work) hws.symm))
        (fun h => hfw (reserve_sub_own work h))
      scratch_res := baseSC_disjoint (fun h => hcs (reserve_sub_own scratch h))
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

omit hmod hs4 hlay in
/-- `initY1` on the data register acts on a live qubit. -/
lemma initY1_factSC (pc : ℕ → ℕ → ℕ → ℕ → ℕ) :
    SFact P pc (initY1 y.active) true L0 L0 ((L0).card + 0) := by
  have hy : regQubitSet (y.grow 1).active ⊆ L0 := fun q h => mem_baseSC_of (Or.inr (Or.inl h))
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

end Base

/-! ## The circuit, for any lowering that walks as its blocks -/

/-- **The lowered circuit, any lowering.** For a gate lowering `f` that walks as the
opaque-block walk with budget `pc`, the lowered real semiclassical circuit returns to
the base set and peaks at `|base| + (if m = 0 then 0 else modMulPeakWith pc …)`. -/
theorem circuit_fact (hf : LowersAs P pc f) (a N c m : ℕ) (y work scratch : ExtReg) (flag : ℕ)
    (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hws : MGate.WorkspaceOK P (orderFindingSemiclassical a N c m y work scratch flag hw hs4))
    (hlay : SemiclassicalLayout c y work scratch flag) :
    MFact P (Policy.lowerMWith P f (orderFindingSemiclassical a N c m y work scratch flag hw hs4) hws)
      (orderFindingBaseSetSC c y work scratch flag) (orderFindingBaseSetSC c y work scratch flag)
      ((orderFindingBaseSetSC c y work scratch flag).card
        + if m = 0 then 0 else Rec.modMulPeakWith P pc y.width y.capacity work.width
            work.capacity scratch.width scratch.capacity) := by
  have hc : c ∈ orderFindingBaseSetSC c y work scratch flag := mem_baseSC_of (Or.inl rfl)
  have hms := mulSpace_baseSC hw hs4 hlay
  have hU : ∀ j, SFact P pc
      (semiclassicalMultipliers a N c m y work scratch flag hw hs4 j) true
      (orderFindingBaseSetSC c y work scratch flag) (orderFindingBaseSetSC c y work scratch flag)
      ((orderFindingBaseSetSC c y work scratch flag).card
        + Rec.modMulPeakWith P pc y.width y.capacity work.width work.capacity
          scratch.width scratch.capacity) :=
    fun j => core_fact _ N hw hs4 hms
  have fI := hf _ hws.1 _ _ _ (initY1_factSC (P := P) (c := c) (y := y) (work := work)
    (scratch := scratch) (flag := flag) pc)
  have fR := rounds_fact hf _ hc hU m hws.2
  exact (MFact.seq fI fR).congr_peak (by simp)

/-! ## The budget -/

/-- One multiplication's peak with the walk's budgets is `Policy.orderFindingPeakSC`
(for any spare capacities: the direct phase products do not read them). -/
theorem orderFindingPeakSC_eq (P : ShorLoweringPolicy) (dW dC wW wC sW sC : ℕ) :
    Policy.orderFindingPeakSC P dW wW sW
      = Rec.modMulPeakWith P (Rec.ppPeak P) dW dC wW wC sW sC := by
  simp only [Policy.orderFindingPeakSC, orderFindingPeakSCD, orderFindingPeakSCWith,
    modMulPeakWith, modMulPhasePeaksWith, Rec.modMulPeakWith, Rec.modMulPhasePeaksWith,
    Rec.ppPeak, qftPeakD_eq, peakReserveD_eq]

/-! ## The claims -/

/-- **The lowered semiclassical circuit, every `m`.** Under the hypotheses of
`Policy.SemiclassicalPeakFormula` except `1 ≤ m`, the lowered circuit returns to
the base set and peaks at `|base| + (if m = 0 then 0 else orderFindingPeakSC)`. -/
theorem semiclassical_peak_eq (P : ShorLoweringPolicy) (hP : P.Admissible) (a N c m : ℕ)
    (y work scratch : ExtReg) (flag : ℕ) (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hws : MGate.WorkspaceOK P (orderFindingSemiclassical a N c m y work scratch flag hw hs4))
    (hlay : SemiclassicalLayout c y work scratch flag) :
    MLowGate.after (orderFindingSemiclassicalLow P a N c m y work scratch flag hw hs4 hws)
        (orderFindingBaseSetSC c y work scratch flag)
      = orderFindingBaseSetSC c y work scratch flag ∧
    (orderFindingSemiclassicalLow P a N c m y work scratch flag hw hs4 hws).peakQubitsFor
        P.negation (orderFindingBaseSetSC c y work scratch flag)
      = (orderFindingBaseSetSC c y work scratch flag).card
        + if m = 0 then 0 else Policy.orderFindingPeakSC P y.width work.width scratch.width := by
  have := circuit_fact (lowersAs_direct hP) a N c m y work scratch flag hw hs4 hws hlay
  refine ⟨this.1, this.2.trans ?_⟩
  rw [orderFindingPeakSC_eq P _ y.capacity _ work.capacity _ scratch.capacity]

/-- **The qubit-count formula for the lowered semiclassical circuit**
(`Policy.SemiclassicalPeakFormula`), for every policy. -/
theorem semiclassical_peak_formula (P : ShorLoweringPolicy) : Policy.SemiclassicalPeakFormula P := by
  intro hP a N c m y work scratch flag hw hs4 hws hlay hm
  rw [(semiclassical_peak_eq P hP a N c m y work scratch flag hw hs4 hws hlay).2,
    orderFindingBaseSetSC_card hw hs4 hlay, Policy.orderFindingQubitsSC]
  simp only [show m ≠ 0 by omega, ite_false]

/-! ## The balanced variants -/

/-- The balanced semiclassical peak with the walk's budgets. -/
theorem orderFindingPeakBalancedSC_eq (P : ShorLoweringPolicy) (R : Balanced.Rule)
    (dW dC wW wC sW sC : ℕ) :
    Policy.orderFindingPeakBalancedSC P R dW dC wW wC sW sC
      = Rec.modMulPeakWith P (Rec.sitePeak P R) dW dC wW wC sW sC := by
  simp only [Policy.orderFindingPeakBalancedSC, orderFindingPeakBalancedSCD, orderFindingPeakSCWith,
    modMulPeakWith, modMulPhasePeaksWith, Rec.modMulPeakWith, Rec.modMulPhasePeaksWith,
    qftPeakD_eq, sitePeakD_eq]

/-- **The qubit-count formula for the balanced lowered semiclassical circuit**
(`Policy.SemiclassicalPeakFormulaBalanced`), for every policy and rule. -/
theorem semiclassical_peak_formula_balanced (P : ShorLoweringPolicy) (R : Balanced.Rule) :
    Policy.SemiclassicalPeakFormulaBalanced P R := by
  intro hP a N c m y work scratch flag hw hs4 hws hlay hm
  have := circuit_fact (lowersAs_balanced hP R) a N c m y work scratch flag hw hs4 hws hlay
  show MLowGate.peakQubitsFor P.negation (Policy.lowerMWith P _ _ hws) _ = _
  rw [this.2, orderFindingBaseSetSC_card hw hs4 hlay, Policy.orderFindingQubitsBalancedSC,
    orderFindingPeakBalancedSC_eq]
  simp only [show m ≠ 0 by omega, ite_false]

/-- Under `MGate.Fits`, the unconditional split lowers as the balanced one. -/
theorem lowerMBalancedU_eq (P : ShorLoweringPolicy) (R : Balanced.Rule) :
    ∀ (g : MGate) (h : MGate.WorkspaceOK P g) (hf : MGate.Fits P R g),
      Policy.lowerMBalancedU P R g h hf = Policy.lowerMBalanced P R g h := by
  intro g
  induction g with
  | unitary u =>
      intro h hf
      show MLowGate.unitary _ = MLowGate.unitary _
      rw [Balanced.lowerGate_congr P (Balanced.balanceU_eq _ hf) (Balanced.balanceU_ok P R _ h hf)
        (Balanced.balance_ok P R _ h)]
  | seq a b iha ihb =>
      intro h hf
      show MLowGate.seq _ _ = MLowGate.seq _ _
      rw [iha h.1 hf.1, ihb h.2 hf.2]; rfl
  | measureReset q => intro _ _; rfl
  | ffPhase q j => intro _ _; rfl

/-- When the four sites of the multiplier fit, the balanced semiclassical count is the
width-only one. -/
theorem orderFindingQubitsBalancedSC_eq_USC (P : ShorLoweringPolicy) (R : Balanced.Rule)
    (dW dC wW wC sW sC : ℕ)
    (h : ∀ s ∈ orderFindingSites dW dC wW wC sW sC, SiteFitsAt P R s) :
    Policy.orderFindingQubitsBalancedSC P R dW dC wW wC sW sC
      = Policy.orderFindingQubitsUSC P R dW wW sW := by
  simp only [orderFindingSites, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, SiteFitsAt] at h
  obtain ⟨h1, h2, h4, h5⟩ := h
  unfold Policy.orderFindingQubitsBalancedSC Policy.orderFindingPeakBalancedSC
    orderFindingPeakBalancedSCD Policy.orderFindingQubitsUSC Policy.orderFindingPeakUSC
    orderFindingPeakUSCD orderFindingPeakSCWith modMulPeakWith modMulPhasePeaksWith sitePeakD
  dsimp only
  rw [sitePeakOf_eq_U _ _ _ _ _ _ _ h1, sitePeakOf_eq_U _ _ _ _ _ _ _ h2,
    sitePeakOf_eq_U _ _ _ _ _ _ _ h4, sitePeakOf_eq_U _ _ _ _ _ _ _ h5]

/-- **The qubit-count formula for the unconditionally balanced lowered semiclassical
circuit** (`Policy.SemiclassicalPeakFormulaBalancedU`), for every policy and rule. -/
theorem semiclassical_peak_formula_balanced_u (P : ShorLoweringPolicy) (R : Balanced.Rule) :
    Policy.SemiclassicalPeakFormulaBalancedU P R := by
  intro hP a N c m y work scratch flag hw hs4 hws hf hlay hm
  have hB := semiclassical_peak_formula_balanced P R hP a N c m y work scratch flag hw hs4 hws hlay hm
  unfold orderFindingSemiclassicalLowBalancedU
  rw [lowerMBalancedU_eq]
  refine hB.trans (orderFindingQubitsBalancedSC_eq_USC P R _ _ _ _ _ _ (coreFits_sites P R hw hs4 ?_))
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hU : Balanced.Fits P R (semiclassicalMultipliers a N c (k + 1) y work scratch flag hw hs4 k) :=
    hf.2.2.2.1
  exact coreFits_of_fits_core P R _ N c hw hs4 hU

end Readout
end Shor
