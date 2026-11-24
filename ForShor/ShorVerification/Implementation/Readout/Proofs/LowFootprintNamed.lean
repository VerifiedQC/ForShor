import ForShor.ShorVerification.Implementation.Readout.LowLocality
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Lowering.PlanReadiness.PlanValid

/-!
# Readout: the lowered QFT and phase-product blocks name only their operands' qubits

`Implementation/Readout/LowLocality.lean` bounded the footprint of `Policy.lowerGate P G h` by
`G.qubitSupport ∪ Gate.qftPhaseFoot P G h`, the residual being the footprint of the lowered QFT
and phase-product blocks. Here that residual is bounded by names.

* `lowerGateRec_lowFootprint`: for EVERY phase-product lowering plan `plan` of a gate `U` that
  is `Valid` (every recursive step's layout is valid, `PhaseLoweringPlan.Valid`, the condition
  the existing planner proofs already establish), every qubit of the footprint of
  `lowerGateRec plan` is in `U.qubitSupport`. The one fact about a recursive step used is
  `PhaseSplitLayout.Valid.reserve_partition`: each child's reserve is a piece of the parent
  operand's reserve. Without `Valid` the statement is false in general: a `signedStep` node may
  carry ANY layout, whose child reserves are arbitrary registers.
* `qftPlan_lowFootprint`: the lowered QFT plan on `r` with workspace pools `xW`, `zW` names only
  qubits of `r`, `xW`, `zW` (no hypothesis beyond the plan's own `QFTWorkspaceOK`).
* `qftPhaseFoot_subset`: the residual `Gate.qftPhaseFoot P G h` is inside `G.qubitSupport` for
  every gate `G` and lowering workspace `h` (the hypotheses `QFTReserveOK`, `WorkspaceOK`,
  `CWorkspaceOK` that `Policy.GateWorkspaceOK` already requires discharge `Valid`; the QFT pools
  `qftXWork P r`, `qftZWork P r` are slices of `r.reserve`).
* `lowerGate_lowFootprint_named`: `lowFootprint (Policy.lowerGate P G h) ⊆ G.qubitSupport`.
  `lowerM_lowSupport_named`: the same for the measurement language.
-/

namespace Shor
namespace Readout

open Gate Operations

/-! ## Generic support facts for the compiled phase-product gate -/

/-- Every owned qubit of every slot of a layout state lies in `S`. -/
def SlotsIn {k : ℕ} (st : LayoutState k) (S : Set ℕ) : Prop :=
  ∀ i, (∀ q ∈ (st.xslot i).ownedQubits, q ∈ S) ∧ (∀ q ∈ (st.zslot i).ownedQubits, q ∈ S)

theorem support_allocChunkGate {k : ℕ} (i : Fin k) (src dst : ExtReg) :
    ∀ q ∈ (allocChunkGate i src dst).qubitSupport, q ∈ src.ownedQubits := by
  intro q hq
  unfold allocChunkGate at hq
  dsimp only at hq
  split_ifs at hq
  · simp [Gate.qubitSupport] at hq
  · exact hq
  · exact hq

theorem support_deallocChunkGate {k : ℕ} (i : Fin k) (src dst : ExtReg) :
    ∀ q ∈ (deallocChunkGate i src dst).qubitSupport, q ∈ src.ownedQubits := by
  intro q hq
  unfold deallocChunkGate at hq
  dsimp only at hq
  split_ifs at hq
  · simp [Gate.qubitSupport] at hq
  · exact hq
  · exact hq

theorem support_allocationsAux {k : ℕ} (src dst : LayoutState k) {S : Set ℕ}
    (hS : SlotsIn src S) : ∀ n hn, (compileSignedAllocationsAux src dst n hn).qubitSupport ⊆ S := by
  intro n
  induction n with
  | zero => intro hn q hq; simp [compileSignedAllocationsAux, Gate.qubitSupport] at hq
  | succ n ih =>
    intro hn q hq
    simp only [compileSignedAllocationsAux, Gate.qubitSupport, Set.mem_union] at hq
    rcases hq with hq | hq | hq
    · exact ih _ hq
    · exact (hS _).1 q (support_allocChunkGate _ _ _ q hq)
    · exact (hS _).2 q (support_allocChunkGate _ _ _ q hq)

theorem support_deallocationsAux {k : ℕ} (src dst : LayoutState k) {S : Set ℕ}
    (hS : SlotsIn src S) :
    ∀ n hn, (compileSignedDeallocationsAux src dst n hn).qubitSupport ⊆ S := by
  intro n
  induction n with
  | zero => intro hn q hq; simp [compileSignedDeallocationsAux, Gate.qubitSupport] at hq
  | succ n ih =>
    intro hn q hq
    simp only [compileSignedDeallocationsAux, Gate.qubitSupport, Set.mem_union] at hq
    rcases hq with hq | hq | hq
    · exact (hS _).2 q (support_deallocChunkGate _ _ _ q hq)
    · exact (hS _).1 q (support_deallocChunkGate _ _ _ q hq)
    · exact ih _ hq

theorem support_body {k : ℕ} {hk : 1 < k} {phi : Angle} {coeff : Fin (q k) → ℚ}
    {st : LayoutState k} {S : Set ℕ} (hS : SlotsIn st S) :
    ∀ ops, (compileAnnotatedOpsToSignedGateAux k hk phi coeff st ops).qubitSupport ⊆ S := by
  intro ops
  induction ops with
  | nil => intro p hp; simp [compileAnnotatedOpsToSignedGateAux, Gate.qubitSupport] at hp
  | cons a rest ih =>
    obtain ⟨op, term⟩ := a
    intro p hp
    have hx : ∀ i p, p ∈ (st.xslot i).ownedQubits → p ∈ S := fun i => (hS i).1
    have hz : ∀ i p, p ∈ (st.zslot i).ownedQubits → p ∈ S := fun i => (hS i).2
    cases op with
    | shiftL i n =>
      simp only [compileAnnotatedOpsToSignedGateAux, Gate.qubitSupport, Set.mem_union,
        Set.mem_ofPred_eq] at hp
      rcases hp with hp | hp | hp
      · exact hx i p hp
      · exact hz i p hp
      · exact ih hp
    | shiftR i n =>
      simp only [compileAnnotatedOpsToSignedGateAux, Gate.qubitSupport, Set.mem_union,
        Set.mem_ofPred_eq] at hp
      rcases hp with hp | hp | hp
      · exact hx i p hp
      · exact hz i p hp
      · exact ih hp
    | negate i =>
      simp only [compileAnnotatedOpsToSignedGateAux, Gate.qubitSupport, Set.mem_union,
        Set.mem_ofPred_eq] at hp
      rcases hp with hp | hp | hp
      · exact hx i p hp
      · exact hz i p hp
      · exact ih hp
    | addScaled d s ng sh =>
      simp only [compileAnnotatedOpsToSignedGateAux, Gate.qubitSupport, Set.mem_union,
        Set.mem_ofPred_eq] at hp
      rcases hp with (hp | hp) | (hp | hp) | hp
      · exact hx d p hp
      · exact hx s p hp
      · exact hz d p hp
      · exact hz s p hp
      · exact ih hp
    | phaseProduct i =>
      cases term with
      | none => exact ih (by simpa [compileAnnotatedOpsToSignedGateAux] using hp)
      | some l =>
        simp only [compileAnnotatedOpsToSignedGateAux, Gate.qubitSupport, Set.mem_union,
          Set.mem_ofPred_eq] at hp
        rcases hp with (hp | hp) | hp
        · exact hx i p hp
        · exact hz i p hp
        · exact ih hp

theorem slotsIn_init {x z : ExtReg} {k : ℕ} {layout : Gate.PhaseProductLayout x z k}
    (hv : layout.Valid) :
    SlotsIn (initSignedLayoutState layout) {p | p ∈ x.ownedQubits ∨ p ∈ z.ownedQubits} := by
  intro i
  constructor
  · intro p hp
    left
    simp only [initSignedLayoutState, PhaseSplitLayout.child, ExtReg.withReserve,
      ExtReg.ownedQubits, List.mem_append] at hp
    rcases hp with hp | hp
    · exact List.mem_append_left _ (((List.take_sublist _ _).trans (List.drop_sublist _ _)).subset hp)
    · refine List.mem_append_right _ ?_
      rw [← hv.xSplit.reserve_partition]
      exact List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, hp⟩
  · intro p hp
    right
    simp only [initSignedLayoutState, PhaseSplitLayout.child, ExtReg.withReserve,
      ExtReg.ownedQubits, List.mem_append] at hp
    rcases hp with hp | hp
    · exact List.mem_append_left _ (((List.take_sublist _ _).trans (List.drop_sublist _ _)).subset hp)
    · refine List.mem_append_right _ ?_
      rw [← hv.zSplit.reserve_partition]
      exact List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, hp⟩

theorem slotsIn_target {k : ℕ} {st : LayoutState k} {S : Set ℕ} (hS : SlotsIn st S)
    (need : NeededWidths k) : SlotsIn (targetSignedLayoutState st need) S := by
  intro i
  simp only [targetSignedLayoutState, growExtRegTo, Gate.ExtReg.ownedQubits_grow]
  exact hS i

theorem support_compiledSignedPhaseGateBy {R : WidthRule} {k : ℕ} {hk : 1 < k} {pts : List Point}
    {hpts : pts.length = q k} {ops : Prog k} {phi : Angle} {x z : ExtReg}
    {layout : Gate.PhaseProductLayout x z k} (hv : layout.Valid) :
    (compiledSignedPhaseGateBy R k hk pts hpts ops phi x z layout).qubitSupport
      ⊆ (Gate.SignedPhaseProd phi x z).qubitSupport := by
  have h0 := slotsIn_init hv
  intro p hp
  unfold compiledSignedPhaseGateBy compileOpsToSignedGateBy at hp
  simp only [Gate.qubitSupport, Set.mem_union] at hp
  rcases hp with hp | hp | hp
  · exact support_allocationsAux _ _ h0 _ _ hp
  · exact support_body (slotsIn_target h0 _) _ hp
  · exact support_deallocationsAux _ _ h0 _ _ hp

theorem support_controlPhaseLeaves (c : ℕ) (G : Gate) :
    ∀ p ∈ (controlPhaseLeaves c G).qubitSupport, p = c ∨ p ∈ G.qubitSupport := by
  induction G with
  | seq U V ihU ihV =>
    intro p hp
    rcases hp with hp | hp
    · rcases ihU p hp with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases ihV p hp with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
  | SignedPhaseProd phi x z => intro p hp; exact hp
  | _ => intro p hp; exact Or.inr hp

/-! ## The naive leaves -/

theorem mem_signedTermsAux {w : ℕ} :
    ∀ {i : ℕ} {l : List ℕ} {t : ℕ × ℤ}, t ∈ signedTermsAux w i l → t.1 ∈ l
  | _, [], _, h => by simp [signedTermsAux] at h
  | i, a :: l, t, h => by
    simp only [signedTermsAux, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_signedTermsAux h)

theorem foot_sequence (S : Set ℕ) :
    ∀ (l : List LowGate), (∀ g ∈ l, ∀ p ∈ g.lowFootprint, p ∈ S) →
      ∀ p ∈ (LowGate.sequence l).lowFootprint, p ∈ S
  | [], _, p, hp => by simp [LowGate.sequence, LowGate.lowFootprint] at hp
  | g :: l, h, p, hp => by
    simp only [LowGate.sequence, LowGate.lowFootprint, Finset.mem_union] at hp
    rcases hp with hp | hp
    · exact h g (List.mem_cons_self ..) p hp
    · exact foot_sequence S l (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')) p hp

theorem foot_CPhase (a t : ℕ) (θ : Angle) :
    ∀ p ∈ (LowGate.CPhase a t θ).lowFootprint, p = a ∨ p = t := by
  intro p hp
  unfold LowGate.CPhase at hp
  split_ifs at hp <;> simp [LowGate.lowFootprint] at hp <;> tauto

theorem foot_CCPhase (a b c : ℕ) (θ : Angle) :
    ∀ p ∈ (LowGate.CCPhase a b c θ).lowFootprint, p = a ∨ p = b ∨ p = c := by
  intro p hp
  unfold LowGate.CCPhase at hp
  split_ifs at hp
  · rcases foot_CPhase _ _ _ p hp with h | h <;> tauto
  · rcases foot_CPhase _ _ _ p hp with h | h <;> tauto
  · rcases foot_CPhase _ _ _ p hp with h | h <;> tauto
  · simp only [LowGate.lowFootprint, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton] at hp
    rcases hp with hp | hp | hp | hp | hp
    · rcases foot_CPhase _ _ _ p hp with h | h <;> tauto
    all_goals tauto

theorem foot_naiveSigned (phi : Angle) (x z : ExtReg) :
    ∀ p ∈ (LowGate.Naive_SignedPhaseProd phi x z).lowFootprint,
      p ∈ x.active.qubits ∨ p ∈ z.active.qubits := by
  refine foot_sequence {p | p ∈ x.active.qubits ∨ p ∈ z.active.qubits} _ ?_
  intro g hg
  simp only [LowGate.naiveSignedPhaseGates, List.mem_flatMap, List.mem_map] at hg
  obtain ⟨xT, hxT, zT, hzT, rfl⟩ := hg
  intro p hp
  rcases foot_CPhase _ _ _ p hp with rfl | rfl
  · exact Or.inl (mem_signedTermsAux hxT)
  · exact Or.inr (mem_signedTermsAux hzT)

theorem foot_naiveCSigned (c : ℕ) (phi : Angle) (x z : ExtReg) :
    ∀ p ∈ (LowGate.Naive_CSignedPhaseProd c phi x z).lowFootprint,
      p = c ∨ p ∈ x.active.qubits ∨ p ∈ z.active.qubits := by
  refine foot_sequence {p | p = c ∨ p ∈ x.active.qubits ∨ p ∈ z.active.qubits} _ ?_
  intro g hg
  simp only [LowGate.naiveCSignedPhaseGates, List.mem_flatMap, List.mem_map] at hg
  obtain ⟨xT, hxT, zT, hzT, rfl⟩ := hg
  intro p hp
  rcases foot_CCPhase _ _ _ _ p hp with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl (mem_signedTermsAux hxT))
  · exact Or.inr (Or.inr (mem_signedTermsAux hzT))

/-! ## Valid plans -/

/-- **Every valid phase-product lowering plan names only its gate's qubits.** For every plan
`plan` of a gate `U` with `plan.Valid`, every qubit in the footprint of `lowerGateRec plan` is
in `U.qubitSupport`. -/
theorem lowerGateRec_lowFootprint {P : ShorLoweringPolicy} {n : ℕ} {U : Gate}
    (plan : PhaseLoweringPlan P n U) (hv : plan.Valid) :
    ∀ p ∈ (lowerGateRec plan).lowFootprint, p ∈ U.qubitSupport := by
  have hact : ∀ (e : ExtReg) (p : ℕ), p ∈ e.active.qubits → p ∈ e.ownedQubits :=
    fun e p h => List.mem_append_left _ h
  induction plan with
  | id => intro p hp; simp [lowerGateRec, LowGate.lowFootprint] at hp
  | seq left right ihL ihR =>
    intro p hp
    simp only [lowerGateRec, LowGate.lowFootprint, Finset.mem_union] at hp
    rcases hp with hp | hp
    · exact Or.inl (ihL hv.1 p hp)
    · exact Or.inr (ihR hv.2 p hp)
  | H _ b => intro p hp; simpa [lowerGateRec, LowGate.lowFootprint, Gate.qubitSupport] using hp
  | X _ b => intro p hp; simpa [lowerGateRec, LowGate.lowFootprint, Gate.qubitSupport] using hp
  | ShiftL _ r m | ShiftR _ r m | Negate _ r =>
    intro p hp
    simp only [lowerGateRec, LowGate.lowFootprint, extRegActiveQubits, List.mem_toFinset] at hp
    exact hact r p hp
  | AddScaled _ d s b m =>
    intro p hp
    simp only [lowerGateRec, LowGate.lowFootprint, extRegActiveQubits, Finset.mem_union,
      List.mem_toFinset] at hp
    rcases hp with hp | hp
    · exact Or.inl (hact d p hp)
    · exact Or.inr (hact s p hp)
  | zeroExtend _ r m | signExtend _ r m | signDealloc _ r m =>
    intro p hp; exact mem_owned_of_grow' hp
  | zeroDealloc _ r m => intro p hp; simp [lowerGateRec, LowGate.lowFootprint] at hp
  | RadixReverse _ r m =>
    intro p hp
    simp only [lowerGateRec, LowGate.lowFootprint, List.mem_toFinset] at hp
    exact hp
  | signedBase phi x z =>
    intro p hp
    rcases foot_naiveSigned phi x z p hp with h | h
    · exact Or.inl (hact x p h)
    · exact Or.inr (hact z p h)
  | signedStep phi x z T layout child ih =>
    intro p hp
    exact support_compiledSignedPhaseGateBy hv.1.2.2.1 (ih hv.2 p hp)
  | cSignedBase c phi x z =>
    intro p hp
    rcases foot_naiveCSigned c phi x z p hp with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (hact x p h))
    · exact Or.inr (Or.inr (hact z p h))
  | cSignedStep c phi x z T layout child ih =>
    intro p hp
    rcases support_controlPhaseLeaves c
        (compiledSignedPhaseGateBy P.widthRule T.k T.hk T.pts T.hpts T.ops phi x z layout) p
        (ih hv.2 p hp) with h | h
    · exact Or.inl h
    · exact Or.inr (support_compiledSignedPhaseGateBy hv.1.1.2.2.1 h)

/-! ## The QFT -/

theorem support_PhaseProdUsing (phi : Angle) {x z : Reg} (ws : Gate.PhaseProdWorkspace x z) :
    ∀ p ∈ (Gate.PhaseProdUsing phi x z ws).qubitSupport,
      p ∈ x.qubits ∨ p ∈ ws.xReserve.qubits ∨ p ∈ z.qubits ∨ p ∈ ws.zReserve.qubits := by
  have hx : ∀ p, p ∈ ws.xExt.ownedQubits → p ∈ x.qubits ∨ p ∈ ws.xReserve.qubits := fun p h => by
    simpa [Gate.PhaseProdWorkspace.xExt, ExtReg.ownedQubits] using h
  have hz : ∀ p, p ∈ ws.zExt.ownedQubits → p ∈ z.qubits ∨ p ∈ ws.zReserve.qubits := fun p h => by
    simpa [Gate.PhaseProdWorkspace.zExt, ExtReg.ownedQubits] using h
  intro p hp
  simp only [Gate.PhaseProdUsing, Gate.qubitSupport, Set.mem_union, Set.mem_ofPred_eq,
    Gate.ExtReg.ownedQubits_grow] at hp
  rcases hp with h | h | (h | h) | h | h
  · rcases hx p h with h' | h' <;> tauto
  · rcases hz p h with h' | h' <;> tauto
  · rcases hx p h with h' | h' <;> tauto
  · rcases hz p h with h' | h' <;> tauto
  · rcases hz p h with h' | h' <;> tauto
  · rcases hx p h with h' | h' <;> tauto

/-- **The lowered QFT plan names only the register and its two workspace pools.** -/
theorem qftPlan_lowFootprint (P : ShorLoweringPolicy) :
    ∀ (n : ℕ) (r xW zW : Reg) (h : Policy.QFTWorkspaceOK P r xW zW), regSize r ≤ n →
      ∀ p ∈ (lowerQFTPlan (Policy.qftPlan P r xW zW h)).lowFootprint,
        p ∈ r.qubits ∨ p ∈ xW.qubits ∨ p ∈ zW.qubits := by
  intro n
  induction n with
  | zero =>
    intro r xW zW h hn p hp
    have hzero : regSize r = 0 := by omega
    have hpl : lowerQFTPlan (Policy.qftPlan P r xW zW h) = LowGate.id := by
      rw [Policy.qftPlan]; simp only [hzero, ↓reduceDIte]; rfl
    rw [hpl] at hp
    simp [LowGate.lowFootprint] at hp
  | succ n ih =>
    intro r xW zW h hn p hp
    by_cases hzero : regSize r = 0
    · have hpl : lowerQFTPlan (Policy.qftPlan P r xW zW h) = LowGate.id := by
        rw [Policy.qftPlan]; simp only [hzero, ↓reduceDIte]; rfl
      rw [hpl] at hp
      simp [LowGate.lowFootprint] at hp
    by_cases hone : regSize r = 1
    · have hpl : lowerQFTPlan (Policy.qftPlan P r xW zW h)
          = LowGate.H (r.lowQubit (by omega)) := by
        rw [Policy.qftPlan]; simp only [hone, ↓reduceDIte]; rfl
      rw [hpl] at hp
      simp only [LowGate.lowFootprint, Finset.mem_singleton] at hp
      subst hp
      exact Or.inl (List.get_mem _ _)
    have hlarge : 2 ≤ regSize r := by omega
    set ws : Gate.PhaseProdWorkspace (leftReg r) (rightReg r) := h.phaseWorkspace hlarge with hws
    have hphase : Policy.WorkspaceOK P (ws.xExt.grow 1) (ws.zExt.grow 1) := by
      simpa [ws] using h.policySignedWorkspaceOK hlarge
    have hpl : lowerQFTPlan (Policy.qftPlan P r xW zW h)
        = (lowerQFTPlan (Policy.qftPlan P (rightReg r) xW zW (h.right hlarge)) ;;
            lowerGateRec (Policy.phaseProdUsingPlan P (qftPhi (regSize r)) ws) ;;
            lowerQFTPlan (Policy.qftPlan P (leftReg r) xW zW (h.left hlarge)) ;;
            LowGate.RadixReverse r (regSize r / 2)) := by
      rw [Policy.qftPlan]; simp only [hzero, hone, ↓reduceDIte]; rfl
    have hvPP : (Policy.phaseProdUsingPlan P (qftPhi (regSize r)) ws).Valid :=
      ⟨trivial, trivial, Policy.signedPlan_valid P _ _ _ hphase, trivial, trivial⟩
    have hR : ∀ p, p ∈ (rightReg r).qubits → p ∈ r.qubits := fun p h => List.mem_of_mem_drop h
    have hL : ∀ p, p ∈ (leftReg r).qubits → p ∈ r.qubits := fun p h => List.mem_of_mem_take h
    rw [hpl] at hp
    simp only [LowGate.lowFootprint, Finset.mem_union] at hp
    rcases hp with hp | hp | hp | hp
    · rcases ih (rightReg r) xW zW (h.right hlarge) (by rw [regSize_rightReg]; omega) p hp with
        h1 | h1 | h1
      · exact Or.inl (hR p h1)
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr h1)
    · rcases support_PhaseProdUsing _ ws p (lowerGateRec_lowFootprint _ hvPP p hp) with
        h1 | h1 | h1 | h1
      · exact Or.inl (hL p h1)
      · exact Or.inr (Or.inl h1)
      · exact Or.inl (hR p h1)
      · exact Or.inr (Or.inr h1)
    · rcases ih (leftReg r) xW zW (h.left hlarge) (by rw [regSize_leftReg]; omega) p hp with
        h1 | h1 | h1
      · exact Or.inl (hL p h1)
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr h1)
    · simp only [List.mem_toFinset] at hp
      exact Or.inl hp

/-- **The lowered QFT names only the register's owned qubits.** Its workspace pools
`qftXWork P r`, `qftZWork P r` are slices of `r.reserve`. -/
theorem lowerQFT_lowFootprint (P : ShorLoweringPolicy) (r : ExtReg) (h : Policy.QFTReserveOK P r) :
    ∀ p ∈ (Policy.lowerQFT P r h).lowFootprint, p ∈ r.ownedQubits := by
  intro p hp
  rcases qftPlan_lowFootprint P _ r.active _ _ h.explicitWorkspace le_rfl p hp with h1 | h1 | h1
  · exact List.mem_append_left _ h1
  · exact List.mem_append_right _ (List.mem_of_mem_take h1)
  · exact List.mem_append_right _ (List.mem_of_mem_drop (List.mem_of_mem_take h1))

/-! ## The residual is named -/

/-- **The residual footprint is named.** For every gate `G` and lowering workspace `h`, the
footprint of the lowered QFT and phase-product blocks of `G` is inside `G.qubitSupport`. -/
theorem qftPhaseFoot_subset (P : ShorLoweringPolicy) :
    ∀ (G : Gate) (h : Policy.GateWorkspaceOK P G),
      (↑(Gate.qftPhaseFoot P G h) : Set ℕ) ⊆ G.qubitSupport := by
  intro G
  induction G with
  | seq U V ihU ihV =>
    intro h p hp
    simp only [Gate.qftPhaseFoot, Finset.coe_union, Set.mem_union] at hp
    rcases hp with hp | hp
    · exact Or.inl (ihU h.1 hp)
    · exact Or.inr (ihV h.2 hp)
  | adj U ih => intro h; exact ih h
  | QFT r => intro h p hp; exact lowerQFT_lowFootprint P r h p hp
  | SignedPhaseProd phi x z =>
    intro h p hp
    exact lowerGateRec_lowFootprint (Policy.signedPlan P phi x z)
      (Policy.signedPlan_valid P phi x z h) p hp
  | CSignedPhaseProd c phi x z =>
    intro h p hp
    exact lowerGateRec_lowFootprint (Policy.cSignedPlan P c phi x z)
      (Policy.cSignedPlan_valid P c phi x z h) p hp
  | _ => intro _ p hp; simp [Gate.qftPhaseFoot] at hp

/-- `qftPhaseFoot_subset` for the measurement language. -/
theorem mgate_qftPhaseFoot_subset (P : ShorLoweringPolicy) :
    ∀ (g : MGate) (h : MGate.WorkspaceOK P g),
      (↑(MGate.qftPhaseFoot P g h) : Set ℕ) ⊆ g.qubitSupport := by
  intro g
  induction g with
  | unitary u => intro h; exact qftPhaseFoot_subset P u h
  | seq a b iha ihb =>
    intro h p hp
    simp only [MGate.qftPhaseFoot, Finset.coe_union, Set.mem_union] at hp
    rcases hp with hp | hp
    · exact Or.inl (iha h.1 hp)
    · exact Or.inr (ihb h.2 hp)
  | measureReset _ => intro _ _ hp; simp [MGate.qftPhaseFoot] at hp
  | ffPhase _ _ => intro _ _ hp; simp [MGate.qftPhaseFoot] at hp

/-- **The lowering's footprint is named.** -/
theorem lowerGate_lowFootprint_named (P : ShorLoweringPolicy) (G : Gate)
    (h : Policy.GateWorkspaceOK P G) :
    (↑(Policy.lowerGate P G h).lowFootprint : Set ℕ) ⊆ G.qubitSupport := fun _ hp =>
  (lowerGate_lowFootprint_subset P G h hp).elim id (fun h' => qftPhaseFoot_subset P G h h')

/-- **The lowering's low support is named** (measurement language). -/
theorem lowerM_lowSupport_named (P : ShorLoweringPolicy) (g : MGate)
    (h : MGate.WorkspaceOK P g) :
    (↑(Policy.lowerM P g h).lowSupport : Set ℕ) ⊆ g.qubitSupport := fun _ hp =>
  (lowerM_lowSupport_subset P g h hp).elim id (fun h' => mgate_qftPhaseFoot_subset P g h h')

end Readout
end Shor
