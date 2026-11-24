import ForShor.ShorVerification.Implementation.Readout.Proofs.LowFootprintNamed

/-!
# Readout: the walk's residual `qftPhaseReach` is named

`Gate.qftPhaseReach P G h` (`Readout/Lowering.lean`) is the residual of the existing support
link of the peak walk (`lowerGate_reach_subset`): the walk reach `QubitCount.reach` of the
lowered QFT and phase-product blocks. Until now it was by definition the blocks' own reach.
Here it is bounded by names.

`QubitCount.reach` differs from `LowGate.lowFootprint` at the extension and deallocation
nodes (`reach (zeroDealloc r n) = allocBits r n`, while `lowFootprint (zeroDealloc r n) = ∅`;
`reach (signExtend r n) = allocBits r n` misses `r.active`). So both are bounded through one
larger set, `LowGate.ownedFoot`: `lowFootprint` with every extension and deallocation
`(r, n)` (all four kinds) charged `extRegGrowQubits r n` (`r.active` and `r.newBits n`).
`lowFootprint g ⊆ ownedFoot g` and `QubitCount.reach g ⊆ ownedFoot g`.

The bound on valid phase-product plans and on the QFT plan is the B4 proof with `ownedFoot` in
place of `lowFootprint` (`lowerGateRec_ownedFoot`, `qftPlan_ownedFoot`, `lowerQFT_ownedFoot`).

* `qftPhaseReach_subset`: `Gate.qftPhaseReach P G h ⊆ G.qubitSupport`, every `G`, `h`.
* `lowerGate_reach_named`: `QubitCount.reach (Policy.lowerGate P G h) ⊆ G.qubitSupport`.
* `semiclassical_lowered_qubits_named`: the existing `semiclassical_lowered_qubits` without its
  residual: walked from its base set, every qubit the lowered real semiclassical circuit can make
  live is in `semiclassicalQubits`.
* `lowerGate_lowFootprint_subset_support`: the uniform form of the footprint bound, for every
  gate `G` (in particular every gate the semiclassical circuit uses) and lowering workspace.
-/

namespace Shor

/-- `lowFootprint`, with every extension and deallocation `(r, n)` charged
`extRegGrowQubits r n`: contains both `lowFootprint` and the walk's `QubitCount.reach`. -/
def LowGate.ownedFoot : LowGate → Finset ℕ
  | .id => ∅
  | .seq U V => U.ownedFoot ∪ V.ownedFoot
  | .adj U => U.ownedFoot
  | .H q => {q}
  | .X q => {q}
  | .Phase q _ => {q}
  | .CNOT c t => {c, t}
  | .Toffoli c₁ c₂ t => {c₁, c₂, t}
  | .ShiftL r _ => extRegActiveQubits r
  | .ShiftR r _ => extRegActiveQubits r
  | .Negate r => extRegActiveQubits r
  | .AddScaled d s _ _ => extRegActiveQubits d ∪ extRegActiveQubits s
  | .zeroExtend r n => extRegGrowQubits r n
  | .signExtend r n => extRegGrowQubits r n
  | .zeroDealloc r n => extRegGrowQubits r n
  | .signDealloc r n => extRegGrowQubits r n
  | .RadixReverse r _ => r.qubits.toFinset

theorem LowGate.lowFootprint_subset_ownedFoot (g : LowGate) : g.lowFootprint ⊆ g.ownedFoot := by
  induction g with
  | seq U V ihU ihV => exact Finset.union_subset_union ihU ihV
  | adj U ih => exact ih
  | zeroDealloc r n => simp [LowGate.lowFootprint]
  | _ => exact le_rfl

theorem LowGate.reach_subset_ownedFoot (g : LowGate) : QubitCount.reach g ⊆ g.ownedFoot := by
  have halloc : ∀ (r : ExtReg) (n : ℕ), QubitCount.allocBits r n ⊆ extRegGrowQubits r n := by
    intro r n p hp
    simp only [QubitCount.allocBits, QubitCount.mem_regQubitSet] at hp
    simp only [extRegGrowQubits, ExtReg.grow, Reg.append, List.mem_toFinset, List.mem_append]
    exact Or.inr hp
  induction g with
  | seq U V ihU ihV => exact Finset.union_subset_union ihU ihV
  | adj U ih => exact ih
  | zeroExtend r n => exact halloc r n
  | signExtend r n => exact halloc r n
  | zeroDealloc r n => exact halloc r n
  | signDealloc r n => exact halloc r n
  | _ => exact le_rfl

namespace Readout

open Gate Operations

/-! ## The naive leaves -/

theorem foot_sequenceO (S : Set ℕ) :
    ∀ (l : List LowGate), (∀ g ∈ l, ∀ p ∈ g.ownedFoot, p ∈ S) →
      ∀ p ∈ (LowGate.sequence l).ownedFoot, p ∈ S
  | [], _, p, hp => by simp [LowGate.sequence, LowGate.ownedFoot] at hp
  | g :: l, h, p, hp => by
    simp only [LowGate.sequence, LowGate.ownedFoot, Finset.mem_union] at hp
    rcases hp with hp | hp
    · exact h g (List.mem_cons_self ..) p hp
    · exact foot_sequenceO S l (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')) p hp

theorem foot_CPhaseO (a t : ℕ) (θ : Angle) :
    ∀ p ∈ (LowGate.CPhase a t θ).ownedFoot, p = a ∨ p = t := by
  intro p hp
  unfold LowGate.CPhase at hp
  split_ifs at hp <;> simp [LowGate.ownedFoot] at hp <;> tauto

theorem foot_CCPhaseO (a b c : ℕ) (θ : Angle) :
    ∀ p ∈ (LowGate.CCPhase a b c θ).ownedFoot, p = a ∨ p = b ∨ p = c := by
  intro p hp
  unfold LowGate.CCPhase at hp
  split_ifs at hp
  · rcases foot_CPhaseO _ _ _ p hp with h | h <;> tauto
  · rcases foot_CPhaseO _ _ _ p hp with h | h <;> tauto
  · rcases foot_CPhaseO _ _ _ p hp with h | h <;> tauto
  · simp only [LowGate.ownedFoot, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton] at hp
    rcases hp with hp | hp | hp | hp | hp
    · rcases foot_CPhaseO _ _ _ p hp with h | h <;> tauto
    all_goals tauto

theorem foot_naiveSignedO (phi : Angle) (x z : ExtReg) :
    ∀ p ∈ (LowGate.Naive_SignedPhaseProd phi x z).ownedFoot,
      p ∈ x.active.qubits ∨ p ∈ z.active.qubits := by
  refine foot_sequenceO {p | p ∈ x.active.qubits ∨ p ∈ z.active.qubits} _ ?_
  intro g hg
  simp only [LowGate.naiveSignedPhaseGates, List.mem_flatMap, List.mem_map] at hg
  obtain ⟨xT, hxT, zT, hzT, rfl⟩ := hg
  intro p hp
  rcases foot_CPhaseO _ _ _ p hp with rfl | rfl
  · exact Or.inl (mem_signedTermsAux hxT)
  · exact Or.inr (mem_signedTermsAux hzT)

theorem foot_naiveCSignedO (c : ℕ) (phi : Angle) (x z : ExtReg) :
    ∀ p ∈ (LowGate.Naive_CSignedPhaseProd c phi x z).ownedFoot,
      p = c ∨ p ∈ x.active.qubits ∨ p ∈ z.active.qubits := by
  refine foot_sequenceO {p | p = c ∨ p ∈ x.active.qubits ∨ p ∈ z.active.qubits} _ ?_
  intro g hg
  simp only [LowGate.naiveCSignedPhaseGates, List.mem_flatMap, List.mem_map] at hg
  obtain ⟨xT, hxT, zT, hzT, rfl⟩ := hg
  intro p hp
  rcases foot_CCPhaseO _ _ _ _ p hp with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl (mem_signedTermsAux hxT))
  · exact Or.inr (Or.inr (mem_signedTermsAux hzT))

/-! ## Valid plans -/

/-- **Every valid phase-product lowering plan names only its gate's qubits.** For every plan
`plan` of a gate `U` with `plan.Valid`, every qubit in the footprint of `lowerGateRec plan` is
in `U.qubitSupport`. -/
theorem lowerGateRec_ownedFoot {P : ShorLoweringPolicy} {n : ℕ} {U : Gate}
    (plan : PhaseLoweringPlan P n U) (hv : plan.Valid) :
    ∀ p ∈ (lowerGateRec plan).ownedFoot, p ∈ U.qubitSupport := by
  have hact : ∀ (e : ExtReg) (p : ℕ), p ∈ e.active.qubits → p ∈ e.ownedQubits :=
    fun e p h => List.mem_append_left _ h
  induction plan with
  | id => intro p hp; simp [lowerGateRec, LowGate.ownedFoot] at hp
  | seq left right ihL ihR =>
    intro p hp
    simp only [lowerGateRec, LowGate.ownedFoot, Finset.mem_union] at hp
    rcases hp with hp | hp
    · exact Or.inl (ihL hv.1 p hp)
    · exact Or.inr (ihR hv.2 p hp)
  | H _ b => intro p hp; simpa [lowerGateRec, LowGate.ownedFoot, Gate.qubitSupport] using hp
  | X _ b => intro p hp; simpa [lowerGateRec, LowGate.ownedFoot, Gate.qubitSupport] using hp
  | ShiftL _ r m | ShiftR _ r m | Negate _ r =>
    intro p hp
    simp only [lowerGateRec, LowGate.ownedFoot, extRegActiveQubits, List.mem_toFinset] at hp
    exact hact r p hp
  | AddScaled _ d s b m =>
    intro p hp
    simp only [lowerGateRec, LowGate.ownedFoot, extRegActiveQubits, Finset.mem_union,
      List.mem_toFinset] at hp
    rcases hp with hp | hp
    · exact Or.inl (hact d p hp)
    · exact Or.inr (hact s p hp)
  | zeroExtend _ r m | signExtend _ r m | zeroDealloc _ r m | signDealloc _ r m =>
    intro p hp; exact mem_owned_of_grow' hp
  | RadixReverse _ r m =>
    intro p hp
    simp only [lowerGateRec, LowGate.ownedFoot, List.mem_toFinset] at hp
    exact hp
  | signedBase phi x z =>
    intro p hp
    rcases foot_naiveSignedO phi x z p hp with h | h
    · exact Or.inl (hact x p h)
    · exact Or.inr (hact z p h)
  | signedStep phi x z T layout child ih =>
    intro p hp
    exact support_compiledSignedPhaseGateBy hv.1.2.2.1 (ih hv.2 p hp)
  | cSignedBase c phi x z =>
    intro p hp
    rcases foot_naiveCSignedO c phi x z p hp with h | h | h
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

/-- **The lowered QFT plan names only the register and its two workspace pools.** -/
theorem qftPlan_ownedFoot (P : ShorLoweringPolicy) :
    ∀ (n : ℕ) (r xW zW : Reg) (h : Policy.QFTWorkspaceOK P r xW zW), regSize r ≤ n →
      ∀ p ∈ (lowerQFTPlan (Policy.qftPlan P r xW zW h)).ownedFoot,
        p ∈ r.qubits ∨ p ∈ xW.qubits ∨ p ∈ zW.qubits := by
  intro n
  induction n with
  | zero =>
    intro r xW zW h hn p hp
    have hzero : regSize r = 0 := by omega
    have hpl : lowerQFTPlan (Policy.qftPlan P r xW zW h) = LowGate.id := by
      rw [Policy.qftPlan]; simp only [hzero, ↓reduceDIte]; rfl
    rw [hpl] at hp
    simp [LowGate.ownedFoot] at hp
  | succ n ih =>
    intro r xW zW h hn p hp
    by_cases hzero : regSize r = 0
    · have hpl : lowerQFTPlan (Policy.qftPlan P r xW zW h) = LowGate.id := by
        rw [Policy.qftPlan]; simp only [hzero, ↓reduceDIte]; rfl
      rw [hpl] at hp
      simp [LowGate.ownedFoot] at hp
    by_cases hone : regSize r = 1
    · have hpl : lowerQFTPlan (Policy.qftPlan P r xW zW h)
          = LowGate.H (r.lowQubit (by omega)) := by
        rw [Policy.qftPlan]; simp only [hone, ↓reduceDIte]; rfl
      rw [hpl] at hp
      simp only [LowGate.ownedFoot, Finset.mem_singleton] at hp
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
    simp only [LowGate.ownedFoot, Finset.mem_union] at hp
    rcases hp with hp | hp | hp | hp
    · rcases ih (rightReg r) xW zW (h.right hlarge) (by rw [regSize_rightReg]; omega) p hp with
        h1 | h1 | h1
      · exact Or.inl (hR p h1)
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr h1)
    · rcases support_PhaseProdUsing _ ws p (lowerGateRec_ownedFoot _ hvPP p hp) with
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
theorem lowerQFT_ownedFoot (P : ShorLoweringPolicy) (r : ExtReg) (h : Policy.QFTReserveOK P r) :
    ∀ p ∈ (Policy.lowerQFT P r h).ownedFoot, p ∈ r.ownedQubits := by
  intro p hp
  rcases qftPlan_ownedFoot P _ r.active _ _ h.explicitWorkspace le_rfl p hp with h1 | h1 | h1
  · exact List.mem_append_left _ h1
  · exact List.mem_append_right _ (List.mem_of_mem_take h1)
  · exact List.mem_append_right _ (List.mem_of_mem_drop (List.mem_of_mem_take h1))


/-! ## The residual of the walk is named -/

theorem qftPhaseReach_subset (P : ShorLoweringPolicy) :
    ∀ (G : Gate) (h : Policy.GateWorkspaceOK P G),
      (↑(Gate.qftPhaseReach P G h) : Set ℕ) ⊆ G.qubitSupport := by
  intro G
  induction G with
  | seq U V ihU ihV =>
    intro h p hp
    simp only [Gate.qftPhaseReach, Finset.coe_union, Set.mem_union] at hp
    rcases hp with hp | hp
    · exact Or.inl (ihU h.1 hp)
    · exact Or.inr (ihV h.2 hp)
  | adj U ih => intro h; exact ih h
  | QFT r =>
    intro h p hp
    exact lowerQFT_ownedFoot P r h p (LowGate.reach_subset_ownedFoot _ hp)
  | SignedPhaseProd phi x z =>
    intro h p hp
    exact lowerGateRec_ownedFoot (Policy.signedPlan P phi x z)
      (Policy.signedPlan_valid P phi x z h) p (LowGate.reach_subset_ownedFoot _ hp)
  | CSignedPhaseProd c phi x z =>
    intro h p hp
    exact lowerGateRec_ownedFoot (Policy.cSignedPlan P c phi x z)
      (Policy.cSignedPlan_valid P c phi x z h) p (LowGate.reach_subset_ownedFoot _ hp)
  | _ => intro _ _ hp; simp [Gate.qftPhaseReach] at hp

theorem mgate_qftPhaseReach_subset (P : ShorLoweringPolicy) :
    ∀ (g : MGate) (h : MGate.WorkspaceOK P g),
      (↑(MGate.qftPhaseReach P g h) : Set ℕ) ⊆ g.qubitSupport := by
  intro g
  induction g with
  | unitary u => intro h; exact qftPhaseReach_subset P u h
  | seq a b iha ihb =>
    intro h p hp
    simp only [MGate.qftPhaseReach, Finset.coe_union, Set.mem_union] at hp
    rcases hp with hp | hp
    · exact Or.inl (iha h.1 hp)
    · exact Or.inr (ihb h.2 hp)
  | measureReset _ => intro _ _ hp; simp [MGate.qftPhaseReach] at hp
  | ffPhase _ _ => intro _ _ hp; simp [MGate.qftPhaseReach] at hp

/-- **The walk's reach of the lowering is named.** -/
theorem lowerGate_reach_named (P : ShorLoweringPolicy) (G : Gate)
    (h : Policy.GateWorkspaceOK P G) :
    (↑(QubitCount.reach (Policy.lowerGate P G h)) : Set ℕ) ⊆ G.qubitSupport := fun _ hp =>
  (lowerGate_reach_subset P G h hp).elim id (fun h' => qftPhaseReach_subset P G h h')

/-- **Uniform footprint bound.** For EVERY gate `G` and lowering workspace `h` (in particular
every unitary part of the semiclassical circuit), the footprint of `Policy.lowerGate P G h` is
inside `G.qubitSupport`. This is an ALIAS of `lowerGate_lowFootprint_named` (identical
statement, proved by it), kept under this name for the audit's reference. -/
theorem lowerGate_lowFootprint_subset_support (P : ShorLoweringPolicy) (G : Gate)
    (h : Policy.GateWorkspaceOK P G) :
    (↑(Policy.lowerGate P G h).lowFootprint : Set ℕ) ⊆ G.qubitSupport :=
  lowerGate_lowFootprint_named P G h

/-- **The lowered semiclassical circuit's walk, named.** The existing
`semiclassical_lowered_qubits` without its residual: every qubit the lowered real circuit's walk
from `orderFindingBaseSetSC` can make live is in `semiclassicalQubits`. -/
theorem semiclassical_lowered_qubits_named (P : ShorLoweringPolicy) (a N c m : ℕ)
    (y work scratch : ExtReg) (flag : ℕ) (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hws : MGate.WorkspaceOK P (orderFindingSemiclassical a N c m y work scratch flag hw hs4)) :
    (↑(orderFindingBaseSetSC c y work scratch flag
        ∪ MLowGate.reach (orderFindingSemiclassicalLow P a N c m y work scratch flag hw hs4 hws))
        : Set ℕ)
      ⊆ semiclassicalQubits c y work scratch flag := fun _ hp =>
  (semiclassical_lowered_qubits P a N c m y work scratch flag hw hs4 hws hp).elim id
    (fun h' => orderFindingSemiclassical_support a N m hw hs4
      (mgate_qftPhaseReach_subset P _ hws h'))

end Readout
end Shor
