import ForShor.ShorVerification.Implementation.QubitCount.Statement

/-!
# Qubit count: facts about the walk

Well-formedness of the walk and the qubits a circuit can reach, and facts that
hold for every `LowGate`: running a well-formed circuit backwards undoes it at
the same peak, the scratch charge adds at most the circuit's largest single
charge, the walk is monotone in its starting set, and the live set stays inside
the start set and the qubits the circuit reaches.
-/

namespace Shor
namespace QubitCount

/-! ## Well-formedness and reach -/

/-- An activation must not touch a live qubit, and a release must only
release live qubits. -/
def MoveOK (activate : Bool) (B L : Finset ℕ) : Prop :=
  if activate then _root_.Disjoint B L else B ⊆ L

/-- The walk never misuses a qubit: every primitive acts on live qubits only,
every extension activates qubits that are not live, and every deallocation
releases qubits that are. -/
def WellFormed : LowGate → Bool → Finset ℕ → Prop
  | .id, _, _ => True
  | .seq U V, true, L => WellFormed U true L ∧ WellFormed V true (after U true L)
  | .seq U V, false, L => WellFormed V false L ∧ WellFormed U false (after V false L)
  | .adj U, d, L => WellFormed U (!d) L
  | .H q, _, L => LowGate.usedQubits (.H q) ⊆ L
  | .X q, _, L => LowGate.usedQubits (.X q) ⊆ L
  | .Phase q a, _, L => LowGate.usedQubits (.Phase q a) ⊆ L
  | .CNOT c t, _, L => LowGate.usedQubits (.CNOT c t) ⊆ L
  | .Toffoli c₁ c₂ t, _, L => LowGate.usedQubits (.Toffoli c₁ c₂ t) ⊆ L
  | .ShiftL r n, _, L => LowGate.usedQubits (.ShiftL r n) ⊆ L
  | .ShiftR r n, _, L => LowGate.usedQubits (.ShiftR r n) ⊆ L
  | .Negate r, _, L => LowGate.usedQubits (.Negate r) ⊆ L
  | .AddScaled dst src s k, _, L => LowGate.usedQubits (.AddScaled dst src s k) ⊆ L
  | .RadixReverse r m, _, L => LowGate.usedQubits (.RadixReverse r m) ⊆ L
  | .zeroExtend r n, d, L => MoveOK d (allocBits r n) L
  | .signExtend r n, d, L => MoveOK d (allocBits r n) L
  | .zeroDealloc r n, d, L => MoveOK (!d) (allocBits r n) L
  | .signDealloc r n, d, L => MoveOK (!d) (allocBits r n) L

/-- Every qubit the walk of `g` can make live: the qubits its primitives act on
and the qubits its extensions and deallocations move. -/
def reach : LowGate → Finset ℕ
  | .id => ∅
  | .seq U V => reach U ∪ reach V
  | .adj U => reach U
  | .zeroExtend r n => allocBits r n
  | .signExtend r n => allocBits r n
  | .zeroDealloc r n => allocBits r n
  | .signDealloc r n => allocBits r n
  | g => LowGate.usedQubits g

/-! ## The scratch of each primitive -/

@[simp] lemma scratch_H (q : ℕ) : scratch (.H q) = 0 := rfl
@[simp] lemma scratch_X (q : ℕ) : scratch (.X q) = 0 := rfl
@[simp] lemma scratch_Phase (q : ℕ) (a : Angle) : scratch (.Phase q a) = 0 := rfl
@[simp] lemma scratch_CNOT (c t : ℕ) : scratch (.CNOT c t) = 0 := rfl
@[simp] lemma scratch_Toffoli (a b t : ℕ) : scratch (.Toffoli a b t) = 0 := rfl
@[simp] lemma scratch_ShiftL (r : ExtReg) (n : ℕ) : scratch (.ShiftL r n) = 0 := rfl
@[simp] lemma scratch_ShiftR (r : ExtReg) (n : ℕ) : scratch (.ShiftR r n) = 0 := rfl
@[simp] lemma scratch_RadixReverse (r : Reg) (m : ℕ) : scratch (.RadixReverse r m) = 0 := rfl
@[simp] lemma scratch_Negate (r : ExtReg) : scratch (.Negate r) = 1 := rfl
@[simp] lemma scratch_AddScaled (d s : ExtReg) (b : Bool) (n : ℕ) :
    scratch (.AddScaled d s b n) = 1 := rfl

/-! ## Activations and releases -/

@[simp] lemma move_true (B L : Finset ℕ) : move true B L = L ∪ B := rfl
@[simp] lemma move_false (B L : Finset ℕ) : move false B L = L \ B := rfl
@[simp] lemma moveOK_true (B L : Finset ℕ) : MoveOK true B L ↔ _root_.Disjoint B L := by
  simp [MoveOK]
@[simp] lemma moveOK_false (B L : Finset ℕ) : MoveOK false B L ↔ B ⊆ L := by
  simp [MoveOK]

/-- An allowed activation or release is undone by the opposite move, which is
itself allowed, and the larger of the two sets is the same either way. -/
lemma move_reverse {d : Bool} {B L : Finset ℕ} (h : MoveOK d B L) :
    MoveOK (!d) B (move d B L) ∧ move (!d) B (move d B L) = L ∧
    max (move d B L).card (move (!d) B (move d B L)).card = max L.card (move d B L).card := by
  cases d
  · simp only [moveOK_false] at h
    have h2 : move true B (move false B L) = L := Finset.sdiff_union_of_subset h
    refine ⟨?_, h2, ?_⟩
    · simpa using (Finset.disjoint_sdiff : _root_.Disjoint B (L \ B))
    · rw [Bool.not_false, h2]; exact max_comm _ _
  · simp only [moveOK_true] at h
    have h2 : move false B (move true B L) = L := Finset.union_sdiff_cancel_right h.symm
    refine ⟨?_, h2, ?_⟩
    · simp
    · rw [Bool.not_true, h2]; exact max_comm _ _

lemma move_mono (d : Bool) (B : Finset ℕ) {L L' : Finset ℕ} (h : L ⊆ L') :
    move d B L ⊆ move d B L' := by
  cases d
  · exact Finset.sdiff_subset_sdiff h le_rfl
  · exact Finset.union_subset_union h le_rfl

lemma move_subset (d : Bool) (B L : Finset ℕ) : move d B L ⊆ L ∪ B := by
  cases d
  · exact (Finset.sdiff_subset).trans Finset.subset_union_left
  · exact le_rfl

lemma card_le_max_move (d : Bool) (B L : Finset ℕ) :
    L.card ≤ max L.card (move d B L).card := le_max_left _ _

/-! ## Reversal -/

/-- Running a well-formed walk backwards from where it ended returns to where
it started, through the same peak, and is itself well formed. -/
theorem reverse (anc : LowGate → ℕ) :
    ∀ (g : LowGate) (d : Bool) (L : Finset ℕ), WellFormed g d L →
      WellFormed g (!d) (after g d L) ∧ after g (!d) (after g d L) = L ∧
      peak anc g (!d) (after g d L) = peak anc g d L := by
  intro g
  induction g with
  | id => intro d L _; cases d <;> simp [after, peak, WellFormed]
  | seq U V ihU ihV =>
      intro d L h
      cases d
      · obtain ⟨hV, hU⟩ := h
        obtain ⟨hV', hVa, hVp⟩ := ihV false L hV
        obtain ⟨hU', hUa, hUp⟩ := ihU false (after V false L) hU
        simp only [Bool.not_false] at hV' hVa hVp hU' hUa hUp
        refine ⟨⟨hU', ?_⟩, ?_, ?_⟩
        · simpa [after, hUa] using hV'
        · simp [after, hUa, hVa]
        · simp only [Bool.not_false, peak, after, hUa, hUp, hVp]; exact max_comm _ _
      · obtain ⟨hU, hV⟩ := h
        obtain ⟨hU', hUa, hUp⟩ := ihU true L hU
        obtain ⟨hV', hVa, hVp⟩ := ihV true (after U true L) hV
        simp only [Bool.not_true] at hV' hVa hVp hU' hUa hUp
        refine ⟨⟨hV', ?_⟩, ?_, ?_⟩
        · simpa [after, hVa] using hU'
        · simp [after, hUa, hVa]
        · simp only [Bool.not_true, peak, after, hVa, hUp, hVp]; exact max_comm _ _
  | adj U ih =>
      intro d L h
      have := ih (!d) L h
      simp only [Bool.not_not] at this
      simpa only [WellFormed, after, peak, Bool.not_not] using this
  | H q | X q | Phase q a | CNOT c t | Toffoli c₁ c₂ t | ShiftL r n | ShiftR r n | Negate r
  | AddScaled dst src s k | RadixReverse r m =>
      intro d L h
      simp only [WellFormed] at h
      have hL := Finset.union_eq_left.mpr h
      simp only [WellFormed, after, peak, hL]
      exact ⟨h, trivial, trivial⟩
  | zeroExtend r n | signExtend r n =>
      intro d L h
      obtain ⟨h1, h2, h3⟩ := move_reverse (d := d) (B := allocBits r n) (L := L) h
      refine ⟨h1, h2, ?_⟩
      simp only [peak, after]
      rw [h2] at h3 ⊢; exact h3
  | zeroDealloc r n | signDealloc r n =>
      intro d L h
      obtain ⟨h1, h2, h3⟩ := move_reverse (d := !d) (B := allocBits r n) (L := L) h
      simp only [Bool.not_not] at h1 h2 h3
      refine ⟨?_, ?_, ?_⟩
      · simpa only [WellFormed, after, Bool.not_not] using h1
      · simpa only [after, Bool.not_not] using h2
      · simp only [peak, after, Bool.not_not]
        rw [h2] at h3 ⊢; exact h3

/-! ## Scratch charges -/

/-- Charging each primitive its clean scratch qubits raises the peak by at
most the largest single charge in the circuit. -/
theorem peak_le_add_cleanAnc (M : LowGateResourceModel) :
    ∀ (g : LowGate) (d : Bool) (L : Finset ℕ),
      peak (fun u => (LowGate.resources M u).cleanAnc) g d L
        ≤ peak (fun _ => 0) g d L + (LowGate.resources M g).cleanAnc := by
  intro g
  induction g with
  | id => intro d L; simp [peak]
  | seq U V ihU ihV =>
      intro d L
      cases d
      · simp only [peak, LowGate.resources, GateResources.seq]
        have h1 := ihV false L
        have h2 := ihU false (after V false L)
        omega
      · simp only [peak, LowGate.resources, GateResources.seq]
        have h1 := ihU true L
        have h2 := ihV true (after U true L)
        omega
  | adj U ih => intro d L; simpa [peak, LowGate.resources] using ih (!d) L
  | H _ | X _ | Phase _ _ | CNOT _ _ | Toffoli _ _ _ | ShiftL _ _ | ShiftR _ _ | Negate _
  | AddScaled _ _ _ _ | RadixReverse _ _ =>
      intro d L; simp [peak]
  | zeroExtend _ _ | signExtend _ _ | zeroDealloc _ _ | signDealloc _ _ =>
      intro d L; simp [peak]

/-! ## Monotonicity -/

/-- A larger starting set gives a larger set at every later point and a
peak at least as large. -/
theorem mono (anc : LowGate → ℕ) :
    ∀ (g : LowGate) (d : Bool) {L L' : Finset ℕ}, L ⊆ L' →
      after g d L ⊆ after g d L' ∧ peak anc g d L ≤ peak anc g d L' := by
  intro g
  induction g with
  | id => intro d L L' h; exact ⟨h, Finset.card_le_card h⟩
  | seq U V ihU ihV =>
      intro d L L' h
      cases d
      · obtain ⟨hV1, hV2⟩ := ihV false h
        obtain ⟨hU1, hU2⟩ := ihU false hV1
        exact ⟨hU1, max_le_max hV2 hU2⟩
      · obtain ⟨hU1, hU2⟩ := ihU true h
        obtain ⟨hV1, hV2⟩ := ihV true hU1
        exact ⟨hV1, max_le_max hU2 hV2⟩
  | adj U ih => intro d L L' h; exact ih (!d) h
  | H _ | X _ | Phase _ _ | CNOT _ _ | Toffoli _ _ _ | ShiftL _ _ | ShiftR _ _ | Negate _
  | AddScaled _ _ _ _ | RadixReverse _ _ =>
      intro d L L' h
      simp only [after, peak]
      exact ⟨Finset.union_subset_union h le_rfl,
        Nat.add_le_add_right (Finset.card_le_card (Finset.union_subset_union h le_rfl)) _⟩
  | zeroExtend r n | signExtend r n =>
      intro d L L' h
      have hs := move_mono d (allocBits r n) h
      exact ⟨hs, max_le_max (Finset.card_le_card h) (Finset.card_le_card hs)⟩
  | zeroDealloc r n | signDealloc r n =>
      intro d L L' h
      have hs := move_mono (!d) (allocBits r n) h
      exact ⟨hs, max_le_max (Finset.card_le_card h) (Finset.card_le_card hs)⟩

/-! ## The reach bound -/

/-- The live set never leaves the starting set and the qubits the circuit can
reach, so neither does the peak (scratch charges aside). -/
theorem after_subset_and_peak_le :
    ∀ (g : LowGate) (d : Bool) (L : Finset ℕ),
      after g d L ⊆ L ∪ reach g ∧ peak (fun _ => 0) g d L ≤ (L ∪ reach g).card := by
  intro g
  induction g with
  | id => intro d L; simp [after, peak, reach]
  | seq U V ihU ihV =>
      intro d L
      cases d
      · obtain ⟨hV1, hV2⟩ := ihV false L
        obtain ⟨hU1, hU2⟩ := ihU false (after V false L)
        have hsub : after V false L ∪ reach U ⊆ L ∪ reach (U.seq V) := by
          intro q hq
          simp only [Finset.mem_union, reach] at hq ⊢
          rcases hq with hq | hq
          · rcases Finset.mem_union.mp (hV1 hq) with h | h <;> tauto
          · tauto
        refine ⟨hU1.trans hsub, max_le ?_ ?_⟩
        · exact hV2.trans (Finset.card_le_card (Finset.union_subset_union le_rfl
            (by simp [reach])))
        · exact hU2.trans (Finset.card_le_card hsub)
      · obtain ⟨hU1, hU2⟩ := ihU true L
        obtain ⟨hV1, hV2⟩ := ihV true (after U true L)
        have hsub : after U true L ∪ reach V ⊆ L ∪ reach (U.seq V) := by
          intro q hq
          simp only [Finset.mem_union, reach] at hq ⊢
          rcases hq with hq | hq
          · rcases Finset.mem_union.mp (hU1 hq) with h | h <;> tauto
          · tauto
        refine ⟨hV1.trans hsub, max_le ?_ ?_⟩
        · exact hU2.trans (Finset.card_le_card (Finset.union_subset_union le_rfl
            (by simp [reach])))
        · exact hV2.trans (Finset.card_le_card hsub)
  | adj U ih => intro d L; simpa [after, peak, reach] using ih (!d) L
  | H _ | X _ | Phase _ _ | CNOT _ _ | Toffoli _ _ _ | ShiftL _ _ | ShiftR _ _ | Negate _
  | AddScaled _ _ _ _ | RadixReverse _ _ =>
      intro d L; simp [after, peak, reach]
  | zeroExtend r n | signExtend r n =>
      intro d L
      refine ⟨move_subset d _ L, max_le (Finset.card_le_card Finset.subset_union_left)
        (Finset.card_le_card (move_subset d _ L))⟩
  | zeroDealloc r n | signDealloc r n =>
      intro d L
      refine ⟨move_subset (!d) _ L, max_le (Finset.card_le_card Finset.subset_union_left)
        (Finset.card_le_card (move_subset (!d) _ L))⟩

end QubitCount
end Shor
