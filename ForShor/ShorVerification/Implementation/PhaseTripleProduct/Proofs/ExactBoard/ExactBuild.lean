import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Statement
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.ExactBoard.ExactRecursion
/-!
# O5 closed: gate-level PTP recursion at EXACT widths exists, is correct, and is counted

`mkSplitD`: the explicit split layout of `Build.lean` (`mkSplit`) at any child width `C'` meeting
the layout floor `ptpFloor T.k C ≤ C'` (lower chunks `< C'`, top chunk `≤ C'`); the floor is
implied by `ptpTightWidth T C ≤ C'` (`floor_le_tight`), so it costs nothing at exact widths.

* `exists_policyImplD`: for a checked policy and any admissible rule (every node width ≥ exact),
  every width `C` and disjoint `C`-qubit registers below `base`, a `PolicyImplD` exists with
  workspace in `[base, base + ptpWorkspaceD P wd C)`;
* `ptp_gate_full_D`: existence + correctness + full census + qubits, any admissible rule;
* `ptp_gate_full_exact` (headline, O5): the same on the exact board (`exactRule`);
* `ptp_gate_full_of_D`: the original `ptp_gate_full` (scan) re-derived as a corollary.
-/

namespace Shor
namespace PTP

open Shor

/-- Lower chunk widths are below, the top chunk width at most, any `C' ≥ ptpFloor k C`. -/
theorem limb_le_floor {k : ℕ} (C C' : ℕ) (hF : ptpFloor k C ≤ C') (i : Fin k) :
    ((i : ℕ) + 1 ≠ k → C / k < C') ∧ ((i : ℕ) + 1 = k → C - (k - 1) * (C / k) ≤ C') := by
  unfold ptpFloor topWidth at hF
  have h1 := le_of_max_le_left hF
  have h2 := le_of_max_le_right hF
  exact ⟨fun _ => by omega, fun _ => h2⟩

/-- **The split layout** of `X` at a node (width `C`) into child slots of any width `C'` above the
layout floor. -/
def mkSplitD (X : Fin 3 → ExtReg) (C base : ℕ) (T : PTPTable) (C' : ℕ) (hk : 2 ≤ T.k)
    (hG : Good X C base) (hF : ptpFloor T.k C ≤ C') : SplitLayout X T.k C' where
  pre := preOf X C base C' T.k hG
  ext s j := extOf C C' T.k j
  two_le := hk
  pre_active s j := rfl
  can_grow s j := by
    simp [ExtReg.CanGrow, ExtReg.capacity, preOf, ExtReg.withReserve, Reg.interval, regSize,
      Reg.width]
  ext_width s j := by
    have hXs : regSize (X s).active = C := hG.1 s
    have hw : (X s).width = C := hG.1 s
    have hlt := limb_le_floor C C' hF j
    show regSize (chunkReg (X s).active T.k ((X s).width / T.k) j) + extOf C _ T.k j = _
    rw [hw]
    by_cases hj : (j : ℕ) + 1 = T.k
    · have hlen := chunkReg_length (X s).active T.k (C / T.k) j (Or.inr hj)
      simp only [hj, ↓reduceIte] at hlen; rw [hXs] at hlen
      have hjk : (j : ℕ) = T.k - 1 := by omega
      rw [hjk] at hlen
      simp only [regSize, Reg.width] at hlen ⊢
      rw [hlen]
      have ht := hlt.2 hj
      unfold extOf
      simp only [hj, ↓reduceIte]
      omega
    · have hle : (j : ℕ) * (C / T.k) + C / T.k ≤ regSize (X s).active := by
        have : ((j : ℕ) + 1) * (C / T.k) ≤ T.k * (C / T.k) :=
          Nat.mul_le_mul_right _ (by omega)
        have := Nat.mul_div_le C T.k
        nlinarith
      have hlen := chunkReg_length (X s).active T.k (C / T.k) j (Or.inl hle)
      simp only [hj, ↓reduceIte] at hlen
      simp only [regSize, Reg.width] at hlen ⊢
      rw [hlen]
      have hl := hlt.1 hj
      unfold extOf
      simp only [hj, ↓reduceIte]
      omega
  ext_pos s j hj := by
    have hl := (limb_le_floor C C' hF j).1 hj
    unfold extOf
    simp only [hj, ↓reduceIte]
    omega
  disjoint := by
    intro s j s' j' hne q h1 h2
    have hext : ∀ j : Fin T.k, extOf C C' T.k j ≤ C' := fun _ => Nat.sub_le _ _
    rcases mem_grow_preOf h1 with c1 | r1 <;> rcases mem_grow_preOf h2 with c2 | r2
    · by_cases hs : s = s'
      · subst hs
        have hj : j ≠ j' := fun e => hne (by rw [e])
        rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hj) with hlt | hlt
        · exact chunk_disjoint _ _ _ hlt c1 (by rw [hG.1 s] at c2 ⊢; exact c2)
        · exact chunk_disjoint _ _ _ hlt c2 (by rw [hG.1 s] at c1 ⊢; exact c1)
      · exact (List.disjoint_left.mp (hG.2.1 s s' hs)) (mem_chunkReg c1) (mem_chunkReg c2)
    · have := hG.2.2 s q (mem_chunkReg c1); omega
    · have := hG.2.2 s' q (mem_chunkReg c2); omega
    · have e1 := idx_of_range (hext j) r1
      have e2 := idx_of_range (hext j') r2
      obtain ⟨rfl, rfl⟩ := slotIdx_inj (e1.symm.trans e2)
      exact hne rfl

theorem mem_R_mkSplitD {X : Fin 3 → ExtReg} {C base : ℕ} {T : PTPTable} {C' : ℕ} {hk : 2 ≤ T.k}
    {hG : Good X C base} {hF : ptpFloor T.k C ≤ C'} {q : ℕ}
    (h : q ∈ (mkSplitD X C base T C' hk hG hF).R) :
    base ≤ q ∧ q < base + 3 * T.k * C' := by
  simp only [SplitLayout.R, List.mem_flatMap, List.mem_finRange, true_and] at h
  obtain ⟨s, j, hq⟩ := h
  have hq' := mem_interval.mp (List.mem_of_mem_take hq)
  have hi := slotIdx_lt s j
  have he : extOf C C' T.k j ≤ C' := Nat.sub_le _ _
  have : (slotIdx T.k s j + 1) * C' ≤ 3 * T.k * C' := Nat.mul_le_mul_right _ hi
  constructor
  · exact le_trans (Nat.le_add_right _ _) hq'.1
  · have h2 := hq'.2
    rw [Nat.add_mul, one_mul] at this
    omega

theorem slot_lt_mkSplitD {X : Fin 3 → ExtReg} {C base : ℕ} {T : PTPTable} {C' : ℕ} {hk : 2 ≤ T.k}
    {hG : Good X C base} {hF : ptpFloor T.k C ≤ C'} (s : Fin 3) (j : Fin T.k) {q : ℕ}
    (h : q ∈ ((mkSplitD X C base T C' hk hG hF).lay.slot s j).active.qubits) :
    q < base + 3 * T.k * C' := by
  rcases mem_grow_preOf (hG := hG) (C' := C') h with c | r
  · have := hG.2.2 s q (mem_chunkReg c); omega
  · have hi := slotIdx_lt s j
    have he : extOf C C' T.k j ≤ C' := Nat.sub_le _ _
    have : (slotIdx T.k s j + 1) * C' ≤ 3 * T.k * C' := Nat.mul_le_mul_right _ hi
    rw [Nat.add_mul, one_mul] at this
    omega

/-- **O5 (existence), any admissible width rule.** -/
theorem exists_policyImplD (P : PTPPolicy) (hP : P.check = true) (wd : WidthRule)
    (hwd : Admissible P wd) :
    ∀ (C : ℕ) (X : Fin 3 → ExtReg) (base : ℕ), Good X C base →
      ∃ (W : List ℕ) (G : Angle → LowGate),
        PolicyImplD P wd X C W G ∧ ∀ q ∈ W, base ≤ q ∧ q < base + ptpWorkspaceD P wd C := by
  intro C
  induction C using Nat.strong_induction_on with
  | _ C ih =>
  intro X base hG
  by_cases hnode : ∃ T, P.choose C = some T ∧ wd T C < C
  · obtain ⟨T, hc, hlt⟩ := hnode
    obtain ⟨b, hb, rfl⟩ := PTPPolicy.choose_mem hc
    have hT := PTPPolicy.check_tables hP b hb
    have hk : 2 ≤ b.table.k := ((PTPTable.contract_iff b.table).mp hT).1
    have hC : 0 < C := by omega
    have hF : ptpFloor b.table.k C ≤ wd b.table C :=
      (floor_le_tight b.table hT C).trans (hwd b hb C hC)
    have hn : ptpWorkspaceD P wd C = 3 * b.table.k * wd b.table C + ptpWorkspaceD P wd (wd b.table C) := by
      rw [ptpWorkspaceD, hc]
      simp only [hlt, ↓reduceDIte]
    set T := b.table
    set SL := mkSplitD X C base T (wd T C) hk hG hF
    have hgood : ∀ j, Good (fun s => SL.lay.slot s j) (wd T C) (base + 3 * T.k * (wd T C)) := by
      intro j
      refine ⟨fun s => SL.lay.slot_width s j, fun s s' hs => SL.disjoint s j s' j (by
        intro e; exact hs (Prod.mk.inj e).1), fun s q hq => slot_lt_mkSplitD s j hq⟩
    have hex := fun j => ih (wd T C) hlt (fun s => SL.lay.slot s j) (base + 3 * T.k * (wd T C)) (hgood j)
    choose Wc Gc hImpl hBound using hex
    refine ⟨SL.R ++ List.range' (base + 3 * T.k * (wd T C)) (ptpWorkspaceD P wd (wd T C)), _,
      PolicyImplD.node X C T hG.1 hC hc hlt SL Gc
        (List.range' (base + 3 * T.k * (wd T C)) (ptpWorkspaceD P wd (wd T C))) Wc ?_ ?_
        hImpl, ?_⟩
    · intro j q hq
      have := hBound j q hq
      rw [List.mem_range'_1]; omega
    · intro q hq s j hs
      rw [List.mem_range'_1] at hq
      have := slot_lt_mkSplitD s j hs
      omega
    · intro q hq
      rw [hn]
      rcases List.mem_append.mp hq with hq | hq
      · have := mem_R_mkSplitD hq; omega
      · rw [List.mem_range'_1] at hq; omega
  · push Not at hnode
    have hstop : ∀ T, P.choose C = some T → C ≤ wd T C := fun T hT => hnode T hT
    have hD : LeafActiveDisjoint (X 0) (X 1) (X 2) :=
      ⟨hG.2.1 0 1 (by decide), hG.2.1 0 2 (by decide), hG.2.1 1 2 (by decide)⟩
    have hoff : ∀ s, ∀ q, base ≤ q → q ∉ (X s).active.qubits := fun s q hq hm => by
      have := hG.2.2 s q hm; omega
    have hA : SandwichAnc (X 0) (X 1) (X 2) base (base + 1) :=
      ⟨by omega, hoff 0 _ le_rfl, hoff 1 _ le_rfl, hoff 2 _ le_rfl, hoff 0 _ (by omega),
        hoff 1 _ (by omega), hoff 2 _ (by omega)⟩
    have hw : ptpWorkspaceD P wd C = 2 := by
      rw [ptpWorkspaceD]
      rcases hcC : P.choose C with _ | T
      · rfl
      · simp only [Nat.not_lt.mpr (hstop T hcC), ↓reduceDIte]
    refine ⟨[base, base + 1], _, PolicyImplD.leaf X C base (base + 1) hG.1 hstop hD hA, ?_⟩
    rw [hw]
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    omega

/-- **O5, full form, any admissible width rule**: existence, correctness, complete census
(`ptp*D` formulas) and qubits for every rule whose node widths are at least exact. -/
theorem ptp_gate_full_D {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (P : PTPPolicy) (hP : P.check = true) (wd : WidthRule) (hwd : Admissible P wd)
    (n : ℕ) (X : Fin 3 → ExtReg) (base : ℕ) (hG : Good X n base) :
    ∃ (W : List ℕ) (G : Angle → LowGate), PolicyImplD P wd X n W G ∧
      (∀ q ∈ W, base ≤ q ∧ q < base + ptpWorkspaceD P wd n) ∧
      (∀ (φ : Angle) (b : qs.Basis), (∀ s, FitsSignedWidth n (extToInt (X s) b)) →
        (∀ q ∈ W, RegEncoding.bit q b = false) →
        LowerGateClass.evalL (qs := qs) (G φ) (qs.ket b) =
          Complex.exp (((Angle.toReal φ : ℝ) : ℂ) * Complex.I *
            (((extToInt (X 0) b : ℤ) : ℂ) * ((extToInt (X 1) b : ℤ) : ℂ) *
              ((extToInt (X 2) b : ℤ) : ℂ))) • qs.ket b) ∧
      (∀ φ : Angle, let R := LowGate.resources shorGateResourceModel (G φ)
        R.rz = (ptpResourcesD P wd n).rz ∧ R.toffoli = (ptpResourcesD P wd n).toffoli ∧
          R.x = (ptpResourcesD P wd n).x ∧ R.h = (ptpResourcesD P wd n).h ∧
          R.cnot = ptpCnotFullD P wd n ∧ adjToffCount (G φ) = ptpAndDagD P wd n ∧
          (LowGate.usedQubits (G φ)).card ≤ 3 * n + ptpWorkspaceD P wd n) := by
  obtain ⟨W, G, hI, hB⟩ := exists_policyImplD P hP wd hwd n X base hG
  refine ⟨W, G, hI, hB, fun φ b hfit hcl => evalL_policyImplD_ket hP hwd hI φ b hfit hcl,
    fun φ => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hI.resources φ
  exact ⟨h1, h2, h3, h4, hI.cnot φ, hI.andDag_count φ, qubits_le_of_policyImplD hI hG.1 hB φ⟩

/-- **O5 headline: gate-level PTP correctness and census at EXACT widths.** For a checked
policy `P`, every width `n` and three pairwise disjoint `n`-qubit registers below `base`, there
is a ForShor-`LowGate` circuit family following `P` on the exact board (every node's children at
`ptpTightWidth`; in-place split, zero/sign extension, table program, children, un-extension,
sandwich leaves), with workspace above `base`, correct on every basis state with fitting operands
and clean workspace, whose census is the exact-ladder formulas: Rz/Toffoli/X/H =
`ptpResourcesX P n`, CNOT = `ptpCnotFullX P n`, And† = `ptpAndDagX P n`, qubits ≤
`3 n + ptpWorkspaceX P n`. Uncontrolled. -/
theorem ptp_gate_full_exact {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (P : PTPPolicy) (hP : P.check = true) (n : ℕ) (X : Fin 3 → ExtReg) (base : ℕ)
    (hG : Good X n base) :
    ∃ (W : List ℕ) (G : Angle → LowGate), PolicyImplX P X n W G ∧
      (∀ q ∈ W, base ≤ q ∧ q < base + ptpWorkspaceX P n) ∧
      (∀ (φ : Angle) (b : qs.Basis), (∀ s, FitsSignedWidth n (extToInt (X s) b)) →
        (∀ q ∈ W, RegEncoding.bit q b = false) →
        LowerGateClass.evalL (qs := qs) (G φ) (qs.ket b) =
          Complex.exp (((Angle.toReal φ : ℝ) : ℂ) * Complex.I *
            (((extToInt (X 0) b : ℤ) : ℂ) * ((extToInt (X 1) b : ℤ) : ℂ) *
              ((extToInt (X 2) b : ℤ) : ℂ))) • qs.ket b) ∧
      (∀ φ : Angle, let R := LowGate.resources shorGateResourceModel (G φ)
        R.rz = (ptpResourcesX P n).rz ∧ R.toffoli = (ptpResourcesX P n).toffoli ∧
          R.x = (ptpResourcesX P n).x ∧ R.h = (ptpResourcesX P n).h ∧
          R.cnot = ptpCnotFullX P n ∧ adjToffCount (G φ) = ptpAndDagX P n ∧
          (LowGate.usedQubits (G φ)).card ≤ 3 * n + ptpWorkspaceX P n) :=
  ptp_gate_full_D P hP exactRule (admissible_exact P) n X base hG

/-- **Scan corollary**: the original `ptp_gate_full` (statement verbatim) re-derived from the
admissible-rule theorem at `scanRule` (`ptpTightWidth ≤ childWidth`). -/
theorem ptp_gate_full_of_D {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
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
  obtain ⟨W, G, hI, hB, hC, hR⟩ :=
    ptp_gate_full_D (qs := qs) P hP scanRule (admissible_scan P hP) n X base hG
  simp only [ptpResourcesD_scan, ptpCnotFullD_scan, ptpAndDagD_scan, ptpWorkspaceD_scan] at hB hR
  exact ⟨W, G, hI.toScan, hB, hC, hR⟩

end PTP
end Shor
