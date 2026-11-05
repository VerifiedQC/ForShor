import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Statement
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Recursion.Build
/-!
# The rest of the census through the full recursion: And† and CNOT

`PolicyImpl.resources` (Recursion.lean) proves the Rz / Toffoli / X / H fields of every
gate-level recursion equal `ptpResources P n`. Here:

* `ptpAndDag P n`: the number of uncomputing Toffolis (`† Toffoli`, the Qualtran
  `And(uncompute=True)`, 0 T) at every depth (`PolicyImpl.adjToffCount`). Computing
  Toffolis (Qualtran `And`, 4 T) = `ptpResources.toffoli - ptpAndDag`.
* `ptpCnotFull P n`: CNOT including the sign-extension fan-out of the split
  (ForShor charges `signExtend r m` as `m` CNOT, and the un-extension `† alloc` the same):
  per node `6 (C' - topLimbWidth)` on top of `ptpResources`' `3 (A + N)(5C' - 7)`
  (`PolicyImpl.cnot`).
-/

namespace Shor
namespace PTP

open Shor

/-- Uncomputing Toffolis (And†) along the ladder: `w² + w³` per leaf of width `w`. -/
def ptpAndDag (P : PTPPolicy) (n : ℕ) : ℕ :=
  match P.choose n with
  | none => n * n + n * n * n
  | some T =>
      if _h : childWidth n T.ops < n then cpCount T.ops * ptpAndDag P (childWidth n T.ops)
      else n * n + n * n * n
termination_by n


/-- CNOT along the ladder, sign-extension fan-out included. -/
def ptpCnotFull (P : PTPPolicy) (n : ℕ) : ℕ :=
  match P.choose n with
  | none => 0
  | some T =>
      if _h : childWidth n T.ops < n then
        3 * ((addCount T.ops + negCount T.ops) * (5 * childWidth n T.ops - 7)) +
          6 * (childWidth n T.ops - topLimbWidth n T.k) +
          cpCount T.ops * ptpCnotFull P (childWidth n T.ops)
      else 0
termination_by n

theorem body_count {k : ℕ} (f : LowGate → ℕ) (hid : f .id = 0)
    (hseq : ∀ U V, f (.seq U V) = f U + f V) (Lay : NodeLayout k)
    (hop : ∀ (s : Fin 3) (op : Operations.valid_ops k), f (opGate Lay s op) = 0)
    (child : ℕ → Fin k → LowGate) (c : ℕ) (hc : ∀ t i, f (child t i) = c) :
    ∀ (ops : Prog k) (t : ℕ), f (body Lay child t ops) = cpCount ops * c := by
  intro ops
  induction ops with
  | nil => intro t; simp [body, hid, cpCount]
  | cons op ops ih =>
      intro t
      cases op with
      | phaseProduct i => simp only [body, hseq, hc, ih, cpCount]; ring
      | _ => simp only [body, opGates, hseq, hop, ih, cpCount]; ring

theorem adjToffCount_alloc {X : Fin 3 → ExtReg} {k C' : ℕ} (SL : SplitLayout X k C') :
    adjToffCount SL.alloc = 0 := by
  have hl : adjToffCount (LowGate.sequence ((List.finRange 3).flatMap fun s =>
      (List.finRange k).map fun j => LowGate.zeroExtend (SL.pre s j) (SL.ext s j))) = 0 := by
    rw [count_sequence adjToffCount rfl (fun _ _ => rfl)]
    apply List.sum_eq_zero
    intro a ha
    simp only [List.mem_map, List.mem_flatMap] at ha
    obtain ⟨_, ⟨_, _, _, _, rfl⟩, rfl⟩ := ha
    rfl
  show adjToffCount (LowGate.sequence _) + (0 + (0 + 0)) = 0
  rw [hl]

/-- **And† through the full recursion.** -/
theorem PolicyImpl.andDag_count {P : PTPPolicy} {X : Fin 3 → ExtReg} {C : ℕ} {W : List ℕ}
    {G : Angle → LowGate} (h : PolicyImpl P X C W G) (θ : Angle) :
    adjToffCount (G θ) = ptpAndDag P C := by
  induction h generalizing θ with
  | leaf X C t u hX hstop hD hA =>
      have hl : ptpAndDag P C = C * C + C * C * C := by
        rw [ptpAndDag]
        rcases hcC : P.choose C with _ | T
        · rfl
        · simp only [Nat.not_lt.mpr (hstop T hcC), ↓reduceDIte]
      have := (ptpLeafSandwich_counts θ (X 0) (X 1) (X 2) t u).2.2.1
      simp only [hX] at this
      rw [this, hl]
  | node X C T hX hC hc hlt SL G W' Wc hWc hW' hsub ih =>
      have hn : ptpAndDag P C = cpCount T.ops * ptpAndDag P (childWidth C T.ops) := by
        rw [ptpAndDag, hc]
        simp only [hlt, ↓reduceDIte]
      show adjToffCount (ptpSubNode T SL _) = _
      unfold ptpSubNode
      simp only [adjToffCount, adjToffCount_alloc, zero_add]
      rw [hn]
      refine body_count adjToffCount rfl (fun _ _ => rfl) SL.lay (fun s op => by cases op <;> rfl)
        _ _ (fun t j => ih j _) T.ops 0

theorem cnot_alloc {X : Fin 3 → ExtReg} {k C' : ℕ} (SL : SplitLayout X k C') :
    (LowGate.resources shorGateResourceModel SL.alloc).cnot =
      SL.ext 0 SL.top + SL.ext 1 SL.top + SL.ext 2 SL.top := by
  unfold SplitLayout.alloc
  simp only [LowGate.resources, GateResources.seq]
  have : (LowGate.resources shorGateResourceModel (LowGate.sequence
      ((List.finRange 3).flatMap fun s => (List.finRange k).map fun j =>
        LowGate.zeroExtend (SL.pre s j) (SL.ext s j)))).cnot = 0 := by
    have h := field_sequence fCnot shorGateResourceModel
      ((List.finRange 3).flatMap fun s => (List.finRange k).map fun j =>
        LowGate.zeroExtend (SL.pre s j) (SL.ext s j))
    simp only [fCnot] at h
    rw [h]
    apply List.sum_eq_zero
    intro a ha
    simp only [List.mem_map, List.mem_flatMap] at ha
    obtain ⟨_, ⟨_, _, _, _, rfl⟩, rfl⟩ := ha
    rfl
  rw [this]
  simp [shorGateResourceModel]
  ring

/-- The top extension of a split layout is `C' - topLimbWidth`. -/
theorem SplitLayout.ext_top {X : Fin 3 → ExtReg} {k C' C : ℕ} (SL : SplitLayout X k C')
    (hX : ∀ s, (X s).width = C) (s : Fin 3) : SL.ext s SL.top = C' - topLimbWidth C k := by
  have h1 := SL.ext_width s SL.top
  have h2 := SL.pre_active s SL.top
  have hk := SL.two_le
  have hw : (SL.pre s SL.top).width = C - (k - 1) * (C / k) := by
    show regSize (SL.pre s SL.top).active = _
    rw [h2, hX s]
    simp only [chunkReg, top, show k - 1 + 1 = k by omega, ↓reduceIte, regSize_drop]
    rw [show regSize (X s).active = C from hX s]
  unfold topLimbWidth
  omega

/-- **CNOT through the full recursion** (sign-extension fan-out included). -/
theorem PolicyImpl.cnot {P : PTPPolicy} {X : Fin 3 → ExtReg} {C : ℕ} {W : List ℕ}
    {G : Angle → LowGate} (h : PolicyImpl P X C W G) (θ : Angle) :
    (LowGate.resources shorGateResourceModel (G θ)).cnot = ptpCnotFull P C := by
  induction h generalizing θ with
  | leaf X C t u hX hstop hD hA =>
      have hl : ptpCnotFull P C = 0 := by
        rw [ptpCnotFull]
        rcases hcC : P.choose C with _ | T
        · rfl
        · simp only [Nat.not_lt.mpr (hstop T hcC), ↓reduceDIte]
      rw [hl]
      exact (ptpLeafSandwich_resources shorGateResourceModel θ (X 0) (X 1) (X 2) t u).2.2.1
  | node X C T hX hC hc hlt SL G W' Wc hWc hW' hsub ih =>
      have hn : ptpCnotFull P C =
          3 * ((addCount T.ops + negCount T.ops) * (5 * childWidth C T.ops - 7)) +
            6 * (childWidth C T.ops - topLimbWidth C T.k) +
            cpCount T.ops * ptpCnotFull P (childWidth C T.ops) := by
        rw [ptpCnotFull, hc]
        simp only [hlt, ↓reduceDIte]
      show (LowGate.resources shorGateResourceModel (ptpSubNode T SL _)).cnot = _
      unfold ptpSubNode
      have hb := (body_field fCnot SL.lay (fun t j => G j (θ * coeffN T C t))
        (ptpCnotFull P (childWidth C T.ops)) (fun t j => ih j _) T.ops 0).trans (bodyField_eq fCnot SL.lay.width _ T.ops)
      simp only [fCnot, opRes, cuccaroModAddResources] at hb
      simp only [LowGate.resources, GateResources.seq, cnot_alloc, SL.ext_top hX]
      rw [show (LowGate.resources shorGateResourceModel (body SL.lay _ 0 T.ops)).cnot = _ from hb, hn]
      show _ = 3 * ((addCount T.ops + negCount T.ops) * (5 * SL.lay.width - 7)) + _ + _
      ring

/-! ## Qubits -/

theorem SplitLayout.mem_slot {X : Fin 3 → ExtReg} {k C' : ℕ} (SL : SplitLayout X k C') {s : Fin 3}
    {j : Fin k} {q : ℕ} (h : q ∈ (SL.lay.slot s j).active.qubits) :
    q ∈ (X s).active.qubits ∨ q ∈ SL.R := by
  simp only [SplitLayout.lay, ExtReg.grow, Reg.append, List.mem_append] at h
  rcases h with h | h
  · left; rw [SL.pre_active] at h; exact mem_chunkReg h
  · right; exact SL.mem_R h

/-- **Qubits of a gate-level recursion**: only the three registers and the workspace. -/
theorem PolicyImpl.usedQubits {P : PTPPolicy} {X : Fin 3 → ExtReg} {C : ℕ} {W : List ℕ}
    {G : Angle → LowGate} (h : PolicyImpl P X C W G) (θ : Angle) :
    ∀ q ∈ LowGate.usedQubits (G θ), (∃ s, q ∈ (X s).active.qubits) ∨ q ∈ W := by
  induction h generalizing θ with
  | leaf X C t u hX hstop hD hA =>
      intro q hq
      have := ptpLeafSandwich_usedQubits_subset θ (X 0) (X 1) (X 2) t u hq
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, extRegActiveQubits,
        List.mem_toFinset] at this
      rcases this with ((h0 | h1) | h2) | rfl | rfl
      · exact Or.inl ⟨0, h0⟩
      · exact Or.inl ⟨1, h1⟩
      · exact Or.inl ⟨2, h2⟩
      · exact Or.inr (by simp)
      · exact Or.inr (by simp)
  | node X C T hX hC hc hlt SL G W' Wc hWc hW' hsub ih =>
      -- every qubit is in a child slot or in W'
      have key : ∀ q ∈ LowGate.usedQubits (ptpSubNode T SL (fun t j => G j (θ * coeffN T C t))),
          q ∈ slotQubits SL.lay ∨ q ∈ W' := by
        have hslots : ∀ s j, extRegGrowQubits (SL.pre s j) (SL.ext s j) ⊆ slotQubits SL.lay :=
          fun s j q hq => mem_slotQubits SL.lay (s := s) (i := j) (by
            simp only [extRegGrowQubits, List.mem_toFinset] at hq
            exact hq)
        have halloc : LowGate.usedQubits SL.alloc ⊆ slotQubits SL.lay := by
          unfold SplitLayout.alloc
          simp only [LowGate.usedQubits]
          refine Finset.union_subset ?_ (Finset.union_subset (hslots _ _)
            (Finset.union_subset (hslots _ _) (hslots _ _)))
          have gen : ∀ gs : List LowGate, (∀ g ∈ gs, LowGate.usedQubits g ⊆ slotQubits SL.lay) →
              LowGate.usedQubits (LowGate.sequence gs) ⊆ slotQubits SL.lay := by
            intro gs
            induction gs with
            | nil => intro _; simp [LowGate.sequence, LowGate.usedQubits]
            | cons g gs ihg =>
                intro hg
                simp only [LowGate.sequence, LowGate.usedQubits]
                exact Finset.union_subset (hg g (by simp)) (ihg fun g' h' => hg g' (by simp [h']))
          apply gen
          intro g hg
          simp only [List.mem_flatMap, List.mem_map] at hg
          obtain ⟨s, _, j, _, rfl⟩ := hg
          exact hslots s j
        have hbody := body_usedQubits_subset SL.lay (fun t j => G j (θ * coeffN T C t))
          (slotQubits SL.lay ∪ W'.toFinset) Finset.subset_union_left (fun t j q hq => by
            rcases ih j _ q hq with ⟨s, hs⟩ | hw
            · exact Finset.mem_union_left _ (mem_slotQubits SL.lay hs)
            · exact Finset.mem_union_right _ (List.mem_toFinset.mpr (hWc j q hw))) T.ops 0
        intro q hq
        unfold ptpSubNode at hq
        simp only [LowGate.usedQubits, Finset.mem_union] at hq
        rcases hq with hq | hq | hq
        · exact Or.inl (halloc hq)
        · rcases Finset.mem_union.mp (hbody hq) with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_toFinset.mp h)
        · exact Or.inl (halloc hq)
      intro q hq
      rcases key q hq with h | h
      · simp only [slotQubits, Finset.mem_biUnion, Finset.mem_univ, true_and, List.mem_toFinset] at h
        obtain ⟨s, j, hm⟩ := h
        rcases SL.mem_slot hm with hx | hr
        · exact Or.inl ⟨s, hx⟩
        · exact Or.inr (List.mem_append_left _ hr)
      · exact Or.inr (List.mem_append_right _ h)

/-- The qubit count of a constructed recursion: at most `3 n + ptpWorkspace P n`. -/
theorem qubits_le_of_policyImpl {P : PTPPolicy} {X : Fin 3 → ExtReg} {n base : ℕ} {W : List ℕ}
    {G : Angle → LowGate} (h : PolicyImpl P X n W G) (hX : ∀ s, (X s).width = n)
    (hW : ∀ q ∈ W, base ≤ q ∧ q < base + ptpWorkspace P n) (θ : Angle) :
    (LowGate.usedQubits (G θ)).card ≤ 3 * n + ptpWorkspace P n := by
  have hsub : LowGate.usedQubits (G θ) ⊆
      ((X 0).active.qubits.toFinset ∪ (X 1).active.qubits.toFinset ∪ (X 2).active.qubits.toFinset) ∪
        Finset.Ico base (base + ptpWorkspace P n) := by
    intro q hq
    rcases h.usedQubits θ q hq with ⟨s, hs⟩ | hw
    · apply Finset.mem_union_left
      fin_cases s <;> simp_all
    · apply Finset.mem_union_right
      have := hW q hw
      simp only [Finset.mem_Ico]; omega
  have hcard : ∀ s, (X s).active.qubits.toFinset.card ≤ n := fun s =>
    (List.toFinset_card_le _).trans (le_of_eq (hX s))
  calc (LowGate.usedQubits (G θ)).card
      ≤ _ := Finset.card_le_card hsub
    _ ≤ ((X 0).active.qubits.toFinset ∪ (X 1).active.qubits.toFinset ∪
          (X 2).active.qubits.toFinset).card + (Finset.Ico base (base + ptpWorkspace P n)).card :=
        Finset.card_union_le _ _
    _ ≤ (n + n + n) + ptpWorkspace P n := by
        refine Nat.add_le_add ?_ (by simp)
        refine (Finset.card_union_le _ _).trans (Nat.add_le_add ?_ (hcard 2))
        exact (Finset.card_union_le _ _).trans (Nat.add_le_add (hcard 0) (hcard 1))
    _ = 3 * n + ptpWorkspace P n := by ring

/-- **O2, full form.** For a checked policy `P`, every width `n` and three pairwise
disjoint `n`-qubit registers below `base`, there is a gate-level circuit family following
`P`, with workspace above `base`, that is correct on every basis state with fitting
operands and clean workspace, and whose complete census (ForShor `shorGateResourceModel`)
is the policy formulas: Rz, Toffoli, X, H = `ptpResources P n`, CNOT = `ptpCnotFull P n`,
uncomputing Toffolis (And†) = `ptpAndDag P n`; qubits touched ≤ `3 n + ptpWorkspace P n`
(model scratch `cleanAnc` of the arithmetic primitives aside). -/
theorem ptp_gate_full {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (P : PTPPolicy) (hP : P.check = true) (n : ℕ) (X : Fin 3 → ExtReg) (base : ℕ)
    (hG : Good X n base) :
    ∃ (W : List ℕ) (G : Angle → LowGate), PolicyImpl P X n W G ∧
      (∀ q ∈ W, base ≤ q ∧ q < base + ptpWorkspace P n) ∧
      (∀ (φ : Angle) (b : qs.Basis), (∀ s, FitsSignedWidth n (extToInt (X s) b)) →
        (∀ q ∈ W, RegEncoding.bit q b = false) →
        LowerGateClass.evalL (qs := qs) (G φ) (qs.ket b) =
          Complex.exp (((Angle.toReal φ : ℝ) : ℂ) * Complex.I *
            (((extToInt (X 0) b : ℤ) : ℂ) * ((extToInt (X 1) b : ℤ) : ℂ) *
              ((extToInt (X 2) b : ℤ) : ℂ))) • qs.ket b) ∧
      (∀ φ : Angle, let R := LowGate.resources shorGateResourceModel (G φ)
        R.rz = (ptpResources P n).rz ∧ R.toffoli = (ptpResources P n).toffoli ∧
          R.x = (ptpResources P n).x ∧ R.h = (ptpResources P n).h ∧
          R.cnot = ptpCnotFull P n ∧ adjToffCount (G φ) = ptpAndDag P n ∧
          (LowGate.usedQubits (G φ)).card ≤ 3 * n + ptpWorkspace P n) := by
  obtain ⟨W, G, hI, hB⟩ := exists_policyImpl P hP n X base hG
  refine ⟨W, G, hI, hB, fun φ b hfit hcl => evalL_policyImpl_ket hP hI φ b hfit hcl,
    fun φ => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hI.resources φ
  exact ⟨h1, h2, h3, h4, hI.cnot φ, hI.andDag_count φ, qubits_le_of_policyImpl hI hG.1 hB φ⟩

end PTP
end Shor
