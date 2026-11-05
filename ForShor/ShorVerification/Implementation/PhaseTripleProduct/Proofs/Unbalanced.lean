import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Statement
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Controlled
/-!
# Unbalanced operand widths at gate level (blueprint item O6), by in-place padding

The gate-level recursion (`PolicyImplD`, `ptp_gate_full_exact`) takes three registers of one common
width `n`. For operands of widths `n₀, n₁, n₂ ≤ n` this file **sign-extends each operand in place**
into its clean reserve (`LowGate.signExtend`, ForShor's own allocation primitive) to width `n`, runs
the balanced circuit on the grown registers, and undoes the extension with the adjoint:

    padGate ;; G ;; †padGate.

Values are preserved by sign extension (`extToInt_grow_signExtendBasis`), so the circuit applies
`exp(iπφ·⟦X₀⟧⟦X₁⟧⟦X₂⟧)` for the *original* operands. This is a padding construction, **not** a native
unbalanced node: the recursion still runs at the common width `n` (a node working at the minimum
limb width `min(nₛ/k)` would be cheaper and is not built or proved). Cost: the three extensions
and their adjoints, priced by the resource model's `signExtend`.
-/

namespace Shor
namespace PTP

open Shor



/-- Basis effect of the extension. -/
noncomputable def padBasis {Basis : Type*} [RegEncoding Basis] (X : Fin 3 → ExtReg)
    (d : Fin 3 → ℕ) (b : Basis) : Basis :=
  signExtendBasis (X 2) (d 2) (signExtendBasis (X 1) (d 1) (signExtendBasis (X 0) (d 0) b))



section Pad

variable {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]

theorem evalL_padGate_ket (X : Fin 3 → ExtReg) (d : Fin 3 → ℕ) (b : qs.Basis) :
    LowerGateClass.evalL (qs := qs) (padGate X d) (qs.ket b) = qs.ket (padBasis X d b) := by
  simp only [padGate, padBasis, LowerGateClass.evalL_seq, LowerGateClass.evalL_signExtend_ket_total]

theorem mem_newBits_grow (e : ExtReg) (n : ℕ) {q : ℕ} (h : q ∈ (e.newBits n).qubits) :
    q ∈ (e.grow n).active.qubits := by
  simp only [ExtReg.grow, Reg.append, List.mem_append]; exact Or.inr h

theorem mem_active_grow (e : ExtReg) (n : ℕ) {q : ℕ} (h : q ∈ e.active.qubits) :
    q ∈ (e.grow n).active.qubits := by
  simp only [ExtReg.grow, Reg.append, List.mem_append]; exact Or.inl h

theorem adisj_not_mem {x z : ExtReg} (h : ExtReg.ActiveDisjoint x z) {q : ℕ}
    (hq : q ∈ x.active.qubits) : q ∉ z.active.qubits := by
  have := h
  simp only [ExtReg.ActiveDisjoint, Shor.Disjoint, List.disjoint_left] at this
  exact this hq


theorem extToInt_step_of_disjoint {Basis : Type*} [RegEncoding Basis] (e r : ExtReg) (n : ℕ)
    (b : Basis) (h : ∀ q ∈ e.active.qubits, q ∉ (r.newBits n).qubits) :
    extToInt e (signExtendBasis r n b) = extToInt e b := by
  unfold extToInt ExtReg.toNat
  rw [toNat_congr_bits e.active _ b (fun q hq => bit_signExtendBasis_out r n b (h q hq))]

variable {X : Fin 3 → ExtReg} {d : Fin 3 → ℕ}

/-- New bits of operand `s` avoid the grown register of any other operand. -/
theorem newBits_avoid (h : PadOK X d) {s s' : Fin 3} (hne : s ≠ s') {q : ℕ}
    (hq : q ∈ ((X s).newBits (d s)).qubits) : q ∉ (padReg X d s').active.qubits :=
  adisj_not_mem (h.disj s s' hne) (mem_newBits_grow _ _ hq)

omit [LowerGateClass qs] in
theorem extToInt_pad_step_other (h : PadOK X d) {s s' : Fin 3} (hne : s ≠ s') (b : qs.Basis) :
    extToInt (padReg X d s') (signExtendBasis (X s) (d s) b) = extToInt (padReg X d s') b :=
  extToInt_step_of_disjoint _ _ _ b (fun _q hq hqn => newBits_avoid h hne hqn hq)

omit [LowerGateClass qs] in
theorem extToInt_base_step_other (h : PadOK X d) {s s' : Fin 3} (hne : s ≠ s') (b : qs.Basis) :
    extToInt (X s') (signExtendBasis (X s) (d s) b) = extToInt (X s') b :=
  extToInt_step_of_disjoint _ _ _ b (fun _q hq hqn =>
    newBits_avoid h hne hqn (mem_active_grow _ _ hq))

omit [LowerGateClass qs] in
/-- **Value and frame facts of the padding.** With all reserves zero, the grown registers hold
the original values, and every qubit outside the grown registers is unchanged. -/
theorem padBasis_spec (h : PadOK X d) (b : qs.Basis)
    (hz : ∀ s, ∀ q ∈ ((X s).newBits (d s)).qubits, RegEncoding.bit q b = false) :
    (∀ s, extToInt (padReg X d s) (padBasis X d b) = extToInt (X s) b) ∧
    (∀ q, (∀ s, q ∉ (padReg X d s).active.qubits) → RegEncoding.bit q (padBasis X d b) =
      RegEncoding.bit q b) := by
  set b1 := signExtendBasis (X 0) (d 0) b with hb1
  set b2 := signExtendBasis (X 1) (d 1) b1 with hb2
  have hbit1 : ∀ q, q ∉ ((X 0).newBits (d 0)).qubits → RegEncoding.bit q b1 = RegEncoding.bit q b :=
    fun q hq => bit_signExtendBasis_out _ _ b hq
  have hz1 : ∀ q ∈ ((X 1).newBits (d 1)).qubits, RegEncoding.bit q b1 = false := fun q hq => by
    rw [hbit1 q (fun hm => newBits_avoid h (by decide : (1 : Fin 3) ≠ 0) hq
      (mem_newBits_grow _ _ hm)), hz 1 q hq]
  have hbit2 : ∀ q, q ∉ ((X 1).newBits (d 1)).qubits → RegEncoding.bit q b2 = RegEncoding.bit q b1 :=
    fun q hq => bit_signExtendBasis_out _ _ b1 hq
  have hz2 : ∀ q ∈ ((X 2).newBits (d 2)).qubits, RegEncoding.bit q b2 = false := fun q hq => by
    rw [hbit2 q (fun hm => newBits_avoid h (by decide : (2 : Fin 3) ≠ 1) hq
      (mem_newBits_grow _ _ hm)), hbit1 q (fun hm => newBits_avoid h (by decide : (2 : Fin 3) ≠ 0) hq
      (mem_newBits_grow _ _ hm)), hz 2 q hq]
  have v0 : extToInt (padReg X d 0) b1 = extToInt (X 0) b :=
    extToInt_grow_signExtendBasis (X 0) (d 0) b (h.cap 0) (freshZero_of_bits _ (hz 0))
  have v1 : extToInt (padReg X d 1) b2 = extToInt (X 1) b1 :=
    extToInt_grow_signExtendBasis (X 1) (d 1) b1 (h.cap 1) (freshZero_of_bits _ hz1)
  have v2 : extToInt (padReg X d 2) (padBasis X d b) = extToInt (X 2) b2 :=
    extToInt_grow_signExtendBasis (X 2) (d 2) b2 (h.cap 2) (freshZero_of_bits _ hz2)
  refine ⟨fun s => ?_, fun q hq => ?_⟩
  · fin_cases s
    · show extToInt (padReg X d 0) (padBasis X d b) = _
      rw [padBasis, extToInt_pad_step_other h (by decide : (2 : Fin 3) ≠ 0),
        extToInt_pad_step_other h (by decide : (1 : Fin 3) ≠ 0)]
      exact v0
    · show extToInt (padReg X d 1) (padBasis X d b) = _
      rw [padBasis, extToInt_pad_step_other h (by decide : (2 : Fin 3) ≠ 1)]
      show extToInt (padReg X d 1) b2 = _
      rw [v1, hb1, extToInt_base_step_other h (by decide : (0 : Fin 3) ≠ 1)]
      rfl
    · show extToInt (padReg X d 2) (padBasis X d b) = _
      rw [v2, hb2, extToInt_base_step_other h (by decide : (1 : Fin 3) ≠ 2), hb1,
        extToInt_base_step_other h (by decide : (0 : Fin 3) ≠ 2)]
      rfl
  · have hn : ∀ s, q ∉ ((X s).newBits (d s)).qubits := fun s hm => hq s (mem_newBits_grow _ _ hm)
    rw [padBasis, bit_signExtendBasis_out _ _ _ (hn 2), bit_signExtendBasis_out _ _ _ (hn 1),
      bit_signExtendBasis_out _ _ _ (hn 0)]

end Pad


/-! ## Correctness and census of the padded circuit -/

theorem fitsSignedWidth_mono {m n : ℕ} {z : ℤ} (h : FitsSignedWidth m z) (hmn : m ≤ n) :
    FitsSignedWidth n z := by
  obtain ⟨h0, h1, h2⟩ := h
  refine ⟨by omega, ?_, ?_⟩
  · have : (2 ^ (m - 1) : ℕ) ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : ((2 ^ (m - 1) : ℕ) : ℤ) ≤ ((2 ^ (n - 1) : ℕ) : ℤ) := by exact_mod_cast this
    unfold signedMin at *; linarith
  · have : (2 ^ (m - 1) : ℕ) ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : ((2 ^ (m - 1) : ℕ) : ℤ) ≤ ((2 ^ (n - 1) : ℕ) : ℤ) := by exact_mod_cast this
    unfold signedMax at *; linarith


theorem mem_padNew {X : Fin 3 → ExtReg} {d : Fin 3 → ℕ} {q : ℕ} :
    q ∈ padNew X d ↔ ∃ s, q ∈ ((X s).newBits (d s)).qubits := by
  simp [padNew]


section PadCorrect

variable {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
variable {X : Fin 3 → ExtReg} {d : Fin 3 → ℕ}

/-- **Padding preserves PTP correctness.** If `G` meets the balanced contract on the grown
registers, the padded circuit applies the PTP phase of the *original* operands. -/
theorem evalL_pad_ptp_ket (h : PadOK X d) {n : ℕ} (hn : ∀ s, (X s).width + d s = n) {W : List ℕ}
    {φ : Angle} {G : LowGate}
    (hW : ∀ q ∈ W, ∀ s, q ∉ (padReg X d s).active.qubits)
    (hGu : ∀ b₁ : qs.Basis, (∀ s, FitsSignedWidth n (extToInt (padReg X d s) b₁)) →
      (∀ q ∈ W, RegEncoding.bit q b₁ = false) →
      LowerGateClass.evalL (qs := qs) G (qs.ket b₁) =
        ptpEigenphase φ (padReg X d) b₁ • qs.ket b₁)
    (b : qs.Basis) (hb : PTPCleanBasisU qs X (padNew X d ++ W) b) :
    LowerGateClass.evalL (qs := qs) (padCtl X d G) (qs.ket b) = ptpEigenphase φ X b • qs.ket b := by
  have hz : ∀ s, ∀ q ∈ ((X s).newBits (d s)).qubits, RegEncoding.bit q b = false :=
    fun s q hq => hb.2 q (List.mem_append_left _ (mem_padNew.mpr ⟨s, hq⟩))
  obtain ⟨hv, hbits⟩ := padBasis_spec h b hz
  have hG := hGu (padBasis X d b)
    (fun s => by
      rw [hv s]
      exact fitsSignedWidth_mono (hb.1 s) (by have := hn s; omega))
    (fun q hq => by
      rw [hbits q (hW q hq)]
      exact hb.2 q (List.mem_append_right _ hq))
  unfold padCtl
  rw [LowerGateClass.evalL_seq, LowerGateClass.evalL_seq, evalL_padGate_ket, hG,
    LowerGateClass.evalL_smul]
  have hinv := LowerGateClass.evalL_adj_apply (qs := qs) (padGate X d) (qs.ket b)
  rw [evalL_padGate_ket] at hinv
  rw [hinv]
  congr 1
  unfold ptpEigenphase
  simp only [hv]

end PadCorrect

theorem resources_padGate (d : Fin 3 → ℕ) (X : Fin 3 → ExtReg) :
    let R := LowGate.resources shorGateResourceModel (padGate X d)
    R.rz = 0 ∧ R.toffoli = 0 ∧ R.x = 0 ∧ R.h = 0 ∧ R.cnot = d 0 + d 1 + d 2 := by
  simp [padGate, LowGate.resources, GateResources.seq, shorGateResourceModel]
  omega


/-! ## Exact-board unbalanced PTP -/



/-- **Main theorem: unequal operand widths, exact board.** -/
theorem ptp_pad_lowerExact_correct_core {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (P : PTPPolicy) (n : ℕ) (X : Fin 3 → ExtReg) (d : Fin 3 → ℕ) (base : ℕ) :
    PTPPadLowerExactCorrect qs P n X d base := by
  intro hP hpad hG
  have hn : ∀ s, (X s).width + d s = n := fun s => by
    have := hG.1 s
    rwa [show (padReg X d s).width = (X s).width + d s from
      ExtReg.width_grow _ _ (hpad.cap s)] at this
  obtain ⟨W, G, hI, hB, _, hR⟩ := ptp_gate_full_exact (qs := qs) P hP n (padReg X d) base hG
  have hWd : ∀ q ∈ W, ∀ s, q ∉ (padReg X d s).active.qubits := fun q hq s hm => by
    have h1 := (hB q hq).1
    have h2 := hG.2.2 s q hm
    omega
  refine ⟨W, G, hI, hB, ?_, ?_⟩
  · intro φ U ψ hψ
    have hU0 : U.op 0 = 0 := by
      have h := U.op_smul 0 (0 : qs.State); simpa using h
    exact evalL_eq_of_clean_kets U.op hU0 U.op_add U.op_smul
      (fun b hb => by
        rw [U.op_ket]
        exact evalL_pad_ptp_ket hpad hn hWd
          (fun b₁ hfit hclean => evalL_policyImplD_ket hP (admissible_exact P) hI φ b₁ hfit hclean)
          b hb) hψ
  · intro φ
    obtain ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7⟩ := hR φ
    obtain ⟨p1, p2, p3, p4, p5⟩ := resources_padGate d X
    have hRc : LowGate.resources shorGateResourceModel (padCtl X d (G φ)) =
        GateResources.seq (LowGate.resources shorGateResourceModel (padGate X d))
          (GateResources.seq (LowGate.resources shorGateResourceModel (G φ))
            (LowGate.resources shorGateResourceModel (padGate X d))) := by
      simp only [padCtl, LowGate.resources]
    have hAc : adjToffCount (padCtl X d (G φ)) = adjToffCount (G φ) := by
      simp [padCtl, padGate, adjToffCount]
    have hpad : ∀ q ∈ LowGate.usedQubits (padGate X d), ∃ s, q ∈ (padReg X d s).active.qubits := by
      intro q hq
      simp only [padGate, LowGate.usedQubits, Finset.mem_union, extRegGrowQubits,
        List.mem_toFinset] at hq
      rcases hq with h0 | h1 | h2
      · exact ⟨0, h0⟩
      · exact ⟨1, h1⟩
      · exact ⟨2, h2⟩
    have hun : ∀ q, (∃ s, q ∈ (padReg X d s).active.qubits) →
        q ∈ (padReg X d 0).active.qubits.toFinset ∪ (padReg X d 1).active.qubits.toFinset ∪
          (padReg X d 2).active.qubits.toFinset := by
      rintro q ⟨s, hs⟩
      simp only [Finset.mem_union, List.mem_toFinset]
      fin_cases s
      · exact Or.inl (Or.inl hs)
      · exact Or.inl (Or.inr hs)
      · exact Or.inr hs
    have hsub : LowGate.usedQubits (padCtl X d (G φ)) ⊆
        ((padReg X d 0).active.qubits.toFinset ∪ (padReg X d 1).active.qubits.toFinset ∪
          (padReg X d 2).active.qubits.toFinset) ∪ Finset.Ico base (base + ptpWorkspaceX P n) := by
      intro q hq
      simp only [padCtl, LowGate.usedQubits, Finset.mem_union] at hq
      rcases hq with hp | hg | hp
      · exact Finset.mem_union_left _ (hun q (hpad q hp))
      · rcases hI.usedQubits φ q hg with hs | hw
        · exact Finset.mem_union_left _ (hun q hs)
        · apply Finset.mem_union_right
          have := hB q hw
          simp only [Finset.mem_Ico]; omega
      · exact Finset.mem_union_left _ (hun q (hpad q hp))
    have hcard : ∀ s : Fin 3, (padReg X d s).active.qubits.toFinset.card ≤ n := fun s =>
      (List.toFinset_card_le _).trans (le_of_eq (hG.1 s))
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hRc]; simp only [GateResources.seq]; omega
    · rw [hRc]; simp only [GateResources.seq]; omega
    · rw [hRc]; simp only [GateResources.seq]; omega
    · rw [hRc]; simp only [GateResources.seq]; omega
    · rw [hRc]; simp only [GateResources.seq]; omega
    · rw [hAc]; exact hr6
    · calc (LowGate.usedQubits (padCtl X d (G φ))).card
          ≤ _ := Finset.card_le_card hsub
        _ ≤ ((padReg X d 0).active.qubits.toFinset ∪ (padReg X d 1).active.qubits.toFinset ∪
              (padReg X d 2).active.qubits.toFinset).card +
            (Finset.Ico base (base + ptpWorkspaceX P n)).card := Finset.card_union_le _ _
        _ ≤ (n + n + n) + ptpWorkspaceX P n := by
            refine Nat.add_le_add ?_ (by simp)
            refine (Finset.card_union_le _ _).trans (Nat.add_le_add ?_ (hcard 2))
            exact (Finset.card_union_le _ _).trans (Nat.add_le_add (hcard 0) (hcard 1))
        _ = 3 * n + ptpWorkspaceX P n := by ring

end PTP
end Shor
