import ForShor.ShorVerification.Implementation.Readout.Lowering

/-!
# Readout: the lowered qubits and the syntactic support

What the base-set discipline of the existing qubit count gives, stated for the
lowered measurement language, and how it links to the syntactic support of
`Support.lean` (`MGate.qubitSupport`, `orderFindingSemiclassical_support`).

* `MLowGate.after_subset_and_peak_le`: walked from a live set `L`, the live set of
  a lowered program never leaves `L ∪ reach g`, and neither does its peak (scratch
  aside). This is the analogue of `QubitCount.after_subset_and_peak_le`.
* `cmpGe_reach_subset`, `cSub_reach_subset`: the two constant-arithmetic blocks stay
  inside their operands' owned qubits and the flag (their unit qubit is the first
  reserve qubit of the scratch register).
* `lowerGate_reach_subset`: every qubit the walk of `Policy.lowerGate P G` can make live
  is named by `G` (`Gate.qubitSupport`, `ExtReg` operands with their reserves), or lies
  in `Gate.qftPhaseReach P G h`, the reach of the lowered QFT and phase-product blocks.
  `lowerM_reach_subset` lifts it to `MGate`.
* `semiclassical_lowered_qubits`: for the lowered real semiclassical circuit, every
  qubit its walk from the base set `orderFindingBaseSetSC` can make live is the
  control `c`, an owned qubit of `y`, `work`, `scratch`, the flag
  (`semiclassicalQubits`), or a qubit reached inside a lowered QFT or phase-product
  block of a multiplier (`MGate.qftPhaseReach`).

**Not stated as a named set: which qubits the QFT and phase-product blocks reach.** The
term `qftPhaseReach` is, by definition, the reach of those lowered blocks themselves, so
for them the inclusion above says nothing beyond "a block uses the qubits it uses". That
is a statement about the syntactic support only. The qubit COUNT does not need it: the
lowered QFT and phase-product blocks are counted by the existing proved walk exactly as in
the coherent circuit (`QubitCount.lower_walk` via `qft_block` / `signed_block` /
`csigned_block`): every named qubit they touch is counted in `semiclassical_peak_formula`,
and their scratch is counted as a number. What is not proved is a syntactic list of the
names those blocks reach (`qftPhaseReach`), which the qubit count does not need. Negation
scratch and rotation-synthesis ancillas are counted as numbers or not modelled, as in the
coherent theorems. Everything else (the skeleton
`H c`, `ffPhase`, `measureReset`, `initY1`, the primitive gates of the multiplier, and
its constant-arithmetic blocks) is bounded by the support.
-/

namespace Shor
namespace Readout

open QubitCount

/-! ## The walk stays in the start set and the reach -/

/-- The live set of a lowered measurement-language program never leaves the
start set and the qubits the program can reach, and neither does its peak
without scratch. -/
theorem MLowGate.after_subset_and_peak_le :
    ∀ (g : MLowGate) (L : Finset ℕ),
      MLowGate.after g L ⊆ L ∪ MLowGate.reach g ∧
      MLowGate.peak (fun _ => 0) g L ≤ (L ∪ MLowGate.reach g).card := by
  intro g
  induction g with
  | unitary u => intro L; exact QubitCount.after_subset_and_peak_le u true L
  | seq a b iha ihb =>
      intro L
      obtain ⟨ha1, ha2⟩ := iha L
      obtain ⟨hb1, hb2⟩ := ihb (MLowGate.after a L)
      have hsub : MLowGate.after a L ∪ MLowGate.reach b ⊆ L ∪ MLowGate.reach (.seq a b) := by
        intro q hq
        simp only [Finset.mem_union, MLowGate.reach] at hq ⊢
        rcases hq with hq | hq
        · rcases Finset.mem_union.mp (ha1 hq) with h | h <;> tauto
        · tauto
      refine ⟨hb1.trans hsub, max_le ?_ ?_⟩
      · exact ha2.trans (Finset.card_le_card (Finset.union_subset_union le_rfl
          (by simp [MLowGate.reach])))
      · exact hb2.trans (Finset.card_le_card hsub)
  | measureReset q =>
      intro L
      have h : insert q L = L ∪ {q} := by rw [Finset.insert_eq, Finset.union_comm]
      exact ⟨h.le, by show (insert q L).card ≤ _; rw [h]; rfl⟩
  | ffPhase q j =>
      intro L
      have h : insert q L = L ∪ {q} := by rw [Finset.insert_eq, Finset.union_comm]
      refine ⟨h.le, ?_⟩
      show QubitCount.peak (fun _ => 0) (LowGate.Phase q 0) true L ≤ _
      simp [QubitCount.peak, LowGate.usedQubits, MLowGate.reach]

/-! ## The constant-arithmetic blocks stay in their operands -/

lemma reach_copyBitPowers (dst : ExtReg) (ctrl : ℕ) :
    ∀ bits : List ℕ, QubitCount.reach (lowerCopyBitPowers dst ctrl bits)
      ⊆ insert ctrl (regQubitSet dst.active) := by
  intro bits
  induction bits with
  | nil => simp [lowerCopyBitPowers, QubitCount.reach]
  | cons i bits ih =>
      unfold lowerCopyBitPowers
      split
      · intro q hq
        simp only [QubitCount.reach, LowGate.usedQubits, Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton] at hq
        rcases hq with (rfl | rfl) | hq
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem ((mem_regQubitSet).mpr (List.get_mem _ _))
        · exact ih hq
      · exact ih

private lemma mem_owned_of_active {e : ExtReg} {q : ℕ} (h : q ∈ regQubitSet e.active) :
    q ∈ e.ownedQubits := List.mem_append_left _ ((mem_regQubitSet).mp h)

private lemma mem_owned_of_alloc {e : ExtReg} {n q : ℕ} (h : q ∈ allocBits e n) :
    q ∈ e.ownedQubits :=
  List.mem_append_right _ ((mem_regQubitSet).mp (allocBits_subset_reserve e n h))

private lemma mem_owned_of_grow {e : ExtReg} {n q : ℕ} (h : q ∈ regQubitSet (e.grow n).active) :
    q ∈ e.ownedQubits := by
  rw [← Gate.ExtReg.ownedQubits_grow e n]; exact mem_owned_of_active h

private lemma unit_mem_owned (s : ExtReg) (h : s.CanGrow 1) :
    constArithmeticUnitQubit s h ∈ s.ownedQubits := by
  apply mem_owned_of_alloc (n := 1)
  rw [allocBits_one_eq s h]; exact Finset.mem_singleton_self _

/-- **The lowered comparison stays in its operands**: every qubit the walk of
`lowerCmpGeConst N d s f h` can make live is an owned qubit of `d` or `s` or the flag. -/
theorem cmpGe_reach_subset (N : ℕ) (d s : ExtReg) (f : ℕ)
    (h : ConstArithmeticWorkspace N d s f) :
    (↑(QubitCount.reach (lowerCmpGeConst N d s f h)) : Set ℕ) ⊆ (Gate.CmpGeConst N d s f).qubitSupport := by
  have hu := unit_mem_owned s h.scratch_can_grow
  have hcp := reach_copyBitPowers s (constArithmeticUnitQubit s h.scratch_can_grow) N.bitIndices
  intro q hq
  simp only [lowerCmpGeConst, lowerPrepareNegConst, lowerCopyConstFromUnit, QubitCount.reach,
    LowGate.usedQubits, extRegActiveQubits, Finset.coe_union, Set.mem_union, Finset.mem_coe,
    Finset.coe_singleton, Set.mem_singleton_iff, Finset.coe_insert, Set.mem_insert_iff] at hq
  show q ∈ d.ownedQubits ∨ q ∈ s.ownedQubits ∨ q = f
  have hs : ∀ q, q ∈ s.active.qubits.toFinset → q ∈ s.ownedQubits := fun q h' =>
    List.mem_append_left _ (List.mem_toFinset.mp h')
  have hcp' : ∀ q, q ∈ QubitCount.reach (lowerCopyBitPowers s
      (constArithmeticUnitQubit s h.scratch_can_grow) N.bitIndices) → q ∈ s.ownedQubits := by
    intro q h'
    rcases Finset.mem_insert.mp (hcp h') with rfl | h''
    · exact hu
    · exact mem_owned_of_active h''
  have hsign : ∀ hl, s.active.get ⟨s.width - 1, hl⟩ ∈ s.ownedQubits := fun hl =>
    List.mem_append_left _ (List.get_mem _ _)
  have hd : ∀ q, q ∈ (d.grow 1).active.qubits.toFinset → q ∈ d.ownedQubits := fun q h' =>
    mem_owned_of_grow ((mem_regQubitSet).mpr (List.mem_toFinset.mp h'))
  have ha : ∀ q, q ∈ allocBits d 1 → q ∈ d.ownedQubits := fun q h' => mem_owned_of_alloc h'
  rcases hq with (h1 | h1 | h1) | (h1 | (h1 | h1) | h1) | (h1 | h1 | h1) | (h1 | (h1 | h1) | h1) |
      h1 | h1 | h1
  all_goals first
    | exact Or.inr (Or.inr h1)
    | exact Or.inl (ha _ h1)
    | exact Or.inl (hd _ h1)
    | exact Or.inr (Or.inl (hs _ h1))
    | exact Or.inr (Or.inl (hcp' _ h1))
    | (subst h1; exact Or.inr (Or.inl hu))
    | (subst h1; exact Or.inr (Or.inl (hsign _)))

/-- **The lowered controlled subtraction stays in its operands.** -/
theorem cSub_reach_subset (N : ℕ) (d s : ExtReg) (f : ℕ)
    (h : ConstArithmeticWorkspace N d s f) :
    (↑(QubitCount.reach (lowerCSubConst N d s f h)) : Set ℕ) ⊆ (Gate.CSubConst N d s f).qubitSupport := by
  have hu := unit_mem_owned s h.scratch_can_grow
  have hcp := reach_copyBitPowers s (constArithmeticUnitQubit s h.scratch_can_grow) N.bitIndices
  have hs : ∀ q, q ∈ s.active.qubits.toFinset → q ∈ s.ownedQubits := fun q h' =>
    List.mem_append_left _ (List.mem_toFinset.mp h')
  have hd : ∀ q, q ∈ d.active.qubits.toFinset → q ∈ d.ownedQubits := fun q h' =>
    List.mem_append_left _ (List.mem_toFinset.mp h')
  have hcp' : ∀ q, q ∈ QubitCount.reach (lowerCopyBitPowers s
      (constArithmeticUnitQubit s h.scratch_can_grow) N.bitIndices) → q ∈ s.ownedQubits := by
    intro q h'
    rcases Finset.mem_insert.mp (hcp h') with rfl | h''
    · exact hu
    · exact mem_owned_of_active h''
  intro q hq
  simp only [lowerCSubConst, lowerCopyConstFromUnit, QubitCount.reach,
    LowGate.usedQubits, extRegActiveQubits, Finset.coe_union, Set.mem_union, Finset.mem_coe,
    Finset.coe_singleton, Set.mem_singleton_iff, Finset.coe_insert, Set.mem_insert_iff] at hq
  show q ∈ d.ownedQubits ∨ q ∈ s.ownedQubits ∨ q = f
  rcases hq with ((h1 | h1) | h1 | h1) | (h1 | h1) | (h1 | h1) | h1 | h1
  all_goals first
    | exact Or.inr (Or.inr h1)
    | exact Or.inl (hd _ h1)
    | exact Or.inr (Or.inl (hs _ h1))
    | exact Or.inr (Or.inl (hcp' _ h1))
    | (subst h1; exact Or.inr (Or.inl hu))

/-! ## Outside the QFT and phase-product blocks, the lowering touches only named qubits -/

/-- **Outside its QFT and phase-product blocks, the lowering uses only named qubits.**
Every qubit the walk of `Policy.lowerGate P G h` can make live is named by `G`
(`Gate.qubitSupport`, `ExtReg` operands with their reserves), or is reached inside one
of its lowered QFT or phase-product blocks (`Gate.qftPhaseReach`, the blocks' own reach:
no named list is stated for them; the peak walk counts them, see the module docstring).
The constant comparison and subtraction blocks are covered by the first alternative
(`cmpGe_reach_subset`, `cSub_reach_subset`). -/
theorem lowerGate_reach_subset (P : ShorLoweringPolicy) :
    ∀ (G : Gate) (h : Policy.GateWorkspaceOK P G),
      (↑(QubitCount.reach (Policy.lowerGate P G h)) : Set ℕ)
        ⊆ G.qubitSupport ∪ ↑(Gate.qftPhaseReach P G h) := by
  have hown : ∀ (e : ExtReg) (q : ℕ), q ∈ e.active.qubits → q ∈ e.ownedQubits :=
    fun e q h => List.mem_append_left _ h
  have hres : ∀ (e : ExtReg) (n q : ℕ), q ∈ allocBits e n → q ∈ e.ownedQubits := fun e n q h =>
    List.mem_append_right _ ((mem_regQubitSet).mp (allocBits_subset_reserve e n h))
  intro G
  induction G with
  | id => intro _; simp [Policy.lowerGate, QubitCount.reach]
  | seq U V ihU ihV =>
      intro h q hq
      simp only [Policy.lowerGate, QubitCount.reach, Finset.coe_union, Set.mem_union] at hq
      rcases hq with hq | hq
      · rcases ihU h.1 hq with h1 | h1
        · exact Or.inl (Or.inl h1)
        · exact Or.inr (Finset.mem_union_left _ h1)
      · rcases ihV h.2 hq with h1 | h1
        · exact Or.inl (Or.inr h1)
        · exact Or.inr (Finset.mem_union_right _ h1)
  | adj U ih => intro h; exact ih h
  | H _ | X _ =>
      intro _ q hq
      simp only [Policy.lowerGate, QubitCount.reach, LowGate.usedQubits, Finset.coe_singleton] at hq
      exact Or.inl hq
  | CNOT a b =>
      intro _ q hq
      simp only [Policy.lowerGate, QubitCount.reach, LowGate.usedQubits, Finset.coe_insert,
        Finset.coe_singleton] at hq
      exact Or.inl hq
  | Toffoli a b t =>
      intro _ q hq
      simp only [Policy.lowerGate, QubitCount.reach, LowGate.usedQubits, Finset.coe_insert,
        Finset.coe_singleton] at hq
      exact Or.inl hq
  | QFT r => intro h q hq; exact Or.inr hq
  | SignedPhaseProd phi x z => intro h q hq; exact Or.inr hq
  | CSignedPhaseProd ctrl phi x z => intro h q hq; exact Or.inr hq
  | CmpGeConst N d s f => intro h q hq; exact Or.inl (cmpGe_reach_subset N d s f h hq)
  | CSubConst N d s f => intro h q hq; exact Or.inl (cSub_reach_subset N d s f h hq)
  | RadixReverse r m =>
      intro _ q hq
      simp only [Policy.lowerGate, QubitCount.reach, LowGate.usedQubits, Finset.mem_coe,
        List.mem_toFinset] at hq
      exact Or.inl hq
  | ShiftL r n | ShiftR r n | Negate r =>
      intro _ q hq
      simp only [Policy.lowerGate, QubitCount.reach, LowGate.usedQubits, extRegActiveQubits,
        Finset.mem_coe, List.mem_toFinset] at hq
      exact Or.inl (hown r q hq)
  | AddScaled d s b n =>
      intro _ q hq
      simp only [Policy.lowerGate, QubitCount.reach, LowGate.usedQubits, extRegActiveQubits,
        Finset.coe_union, Set.mem_union, Finset.mem_coe, List.mem_toFinset] at hq
      rcases hq with hq | hq
      · exact Or.inl (Or.inl (hown d q hq))
      · exact Or.inl (Or.inr (hown s q hq))
  | zeroExtend r n | signExtend r n | zeroDealloc r n | signDealloc r n =>
      intro _ q hq
      exact Or.inl (hres r n q hq)
  | idealCtrlModMul _ _ _ _ => intro h; exact h.elim

/-- `lowerGate_reach_subset` for the measurement language. -/
theorem lowerM_reach_subset (P : ShorLoweringPolicy) :
    ∀ (g : MGate) (h : MGate.WorkspaceOK P g),
      (↑(MLowGate.reach (Policy.lowerM P g h)) : Set ℕ)
        ⊆ g.qubitSupport ∪ ↑(MGate.qftPhaseReach P g h) := by
  intro g
  induction g with
  | unitary u => intro h; exact lowerGate_reach_subset P u h
  | seq a b iha ihb =>
      intro h q hq
      simp only [Policy.lowerM, Policy.lowerMWith, MLowGate.reach, Finset.coe_union, Set.mem_union] at hq
      rcases hq with hq | hq
      · rcases iha h.1 hq with h1 | h1
        · exact Or.inl (Or.inl h1)
        · exact Or.inr (Finset.mem_union_left _ h1)
      · rcases ihb h.2 hq with h1 | h1
        · exact Or.inl (Or.inr h1)
        · exact Or.inr (Finset.mem_union_right _ h1)
  | measureReset q =>
      intro _ q' hq
      simp only [Policy.lowerM, Policy.lowerMWith, MLowGate.reach, Finset.coe_singleton] at hq
      exact Or.inl hq
  | ffPhase q j =>
      intro _ q' hq
      simp only [Policy.lowerM, Policy.lowerMWith, MLowGate.reach, Finset.coe_singleton] at hq
      exact Or.inl hq

/-! ## The semiclassical circuit -/

/-- The base set of the semiclassical circuit is made of its registers' qubits. -/
theorem orderFindingBaseSetSC_subset (c : ℕ) (y work scratch : ExtReg) (flag : ℕ) :
    (↑(orderFindingBaseSetSC c y work scratch flag) : Set ℕ)
      ⊆ semiclassicalQubits c y work scratch flag := by
  intro q hq
  have hyA := yGrow_active_sub y
  simp only [orderFindingBaseSetSC, Finset.coe_union, Finset.coe_singleton, Set.mem_union,
    Set.mem_singleton_iff, Finset.mem_coe] at hq
  rcases hq with (((h | h) | h) | h) | h
  · exact Or.inl h
  · have := hyA h
    simp only [ownSet, Finset.mem_union, mem_regQubitSet] at this
    exact Or.inr (Or.inl (by simp only [ExtReg.ownedQubits, List.mem_append]; exact this))
  · exact Or.inr (Or.inr (Or.inl (List.mem_append_left _ ((mem_regQubitSet).mp h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (List.mem_append_left _ ((mem_regQubitSet).mp h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- **The lowered semiclassical circuit's qubits.** Walked from its base set, every
qubit the lowered real circuit can make live (`orderFindingBaseSetSC ∪ reach`), hence
every qubit live at any step, is the control `c`, an owned qubit of `y`, `work` or
`scratch`, the flag, or a qubit reached inside a lowered QFT or phase-product block of a multiplier
(`MGate.qftPhaseReach`: no named list is stated for these, but the peak walk counts every
qubit they touch, see the module docstring). -/
theorem semiclassical_lowered_qubits (P : ShorLoweringPolicy) (a N c m : ℕ)
    (y work scratch : ExtReg) (flag : ℕ) (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hws : MGate.WorkspaceOK P (orderFindingSemiclassical a N c m y work scratch flag hw hs4)) :
    (↑(orderFindingBaseSetSC c y work scratch flag
        ∪ MLowGate.reach (orderFindingSemiclassicalLow P a N c m y work scratch flag hw hs4 hws))
        : Set ℕ)
      ⊆ semiclassicalQubits c y work scratch flag
        ∪ ↑(MGate.qftPhaseReach P (orderFindingSemiclassical a N c m y work scratch flag hw hs4) hws) := by
  intro q hq
  rw [Finset.coe_union, Set.mem_union] at hq
  rcases hq with hq | hq
  · exact Or.inl (orderFindingBaseSetSC_subset c y work scratch flag hq)
  · rcases lowerM_reach_subset P _ hws hq with h | h
    · exact Or.inl (orderFindingSemiclassical_support a N m hw hs4 h)
    · exact Or.inr h

end Readout
end Shor
