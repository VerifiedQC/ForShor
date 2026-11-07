import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Statement
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.ExactBoard.ExactNode
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Recursion.CensusFull
/-!
# O5: gate-level PTP recursion under any admissible width rule (exact widths included)

`PolicyImpl` (Recursion.lean) fixes the child width of every node to the PTP scan
`childWidth C T.ops`. Here the child width is a parameter `wd : WidthRule`
(`wd T C` = working width of the children of the node with table `T` at width `C`):

* `PolicyImplD P wd`: gate-level recursions following `P` with node widths `wd`;
* `Admissible P wd`: every band's node width is at least exact (`ptpTightWidth ≤ wd`, `0 < n`);
  `exactRule` (the exact board) and `scanRule` (the PTP scan) are admissible;
* `PolicyImplD.specOn`: correctness through the full recursion for every admissible rule;
* census: `ptpResourcesD`, `ptpCnotFullD`, `ptpAndDagD`, `ptpWorkspaceD` (the `ptp*` formulas
  with `childWidth` replaced by `wd`), proved equal to the circuit's counts at every depth
  (`PolicyImplD.resources`, `.cnot`, `.andDag_count`, `qubits_le_of_policyImplD`);
* scan corollaries: `PolicyImpl P = PolicyImplD P scanRule` (`PolicyImpl.toD`,
  `PolicyImplD.toScan`), the `D` formulas at `scanRule` are the original ones
  (`ptpResourcesD_scan`, …), and `PolicyImpl.specOn_of_exact` re-derives `PolicyImpl.specOn`.
-/

namespace Shor
namespace PTP

open Shor



/-- The PTP scan (the original rule of `PolicyImpl`). -/
abbrev scanRule : WidthRule := fun T n => childWidth n T.ops


theorem admissible_exact (P : PTPPolicy) : Admissible P exactRule := fun _ _ _ _ => le_rfl

theorem admissible_scan (P : PTPPolicy) (hP : P.check = true) : Admissible P scanRule :=
  fun b hb _ hn => tight_le_childWidth b.table (PTPPolicy.check_tables hP b hb) hn



/-- **O5: gate-level correctness through the full recursion, any admissible width rule.** -/
theorem PolicyImplD.specOn {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    {P : PTPPolicy} (hP : P.check = true) {wd : WidthRule} (hwd : Admissible P wd)
    {X : Fin 3 → ExtReg} {C : ℕ} {W : List ℕ} {G : Angle → LowGate}
    (h : PolicyImplD P wd X C W G) (θ : Angle) : SpecOn (qs := qs) X C W θ (G θ) := by
  induction h generalizing θ with
  | leaf X C t u _ _ hD hA => exact specOn_leafSandwich X C t u hD hA θ
  | node X C T hX hC hc hlt SL G W' Wc hWc hW' _ ih =>
      obtain ⟨b, hb, rfl⟩ := PTPPolicy.choose_mem hc
      exact specOn_ptpSubNode_exact hX hC b.table (PTPPolicy.check_tables hP b hb) SL
        (hwd b hb C hC) θ _ W' hW' fun t j => (ih j (θ * coeffN b.table C t)).mono (hWc j)

/-- Basis-state form. -/
theorem evalL_policyImplD_ket {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    {P : PTPPolicy} (hP : P.check = true) {wd : WidthRule} (hwd : Admissible P wd)
    {X : Fin 3 → ExtReg} {n : ℕ} {W : List ℕ}
    {G : Angle → LowGate} (h : PolicyImplD P wd X n W G) (φ : Angle) (b : qs.Basis)
    (hfit : ∀ s, FitsSignedWidth n (extToInt (X s) b))
    (hclean : ∀ q ∈ W, RegEncoding.bit q b = false) :
    LowerGateClass.evalL (qs := qs) (G φ) (qs.ket b) =
      Complex.exp (((Angle.toReal φ : ℝ) : ℂ) * Complex.I *
        (((extToInt (X 0) b : ℤ) : ℂ) * ((extToInt (X 1) b : ℤ) : ℂ) *
          ((extToInt (X 2) b : ℤ) : ℂ))) • qs.ket b := by
  rw [h.specOn hP hwd φ b hfit hclean]
  congr 2
  simp only [Angle.toReal]
  push_cast
  ring

/-! ## The scan rule is the original `PolicyImpl` -/

theorem PolicyImpl.toD {P : PTPPolicy} {X : Fin 3 → ExtReg} {C : ℕ} {W : List ℕ}
    {G : Angle → LowGate} (h : PolicyImpl P X C W G) : PolicyImplD P scanRule X C W G := by
  induction h with
  | leaf X C t u hX hstop hD hA => exact PolicyImplD.leaf (wd := scanRule) X C t u hX hstop hD hA
  | node X C T hX hC hc hlt SL G W' Wc hWc hW' _ ih =>
      exact PolicyImplD.node (wd := scanRule) X C T hX hC hc hlt SL G W' Wc hWc hW' ih

theorem PolicyImplD.toScan {P : PTPPolicy} {X : Fin 3 → ExtReg} {C : ℕ} {W : List ℕ}
    {G : Angle → LowGate} (h : PolicyImplD P scanRule X C W G) : PolicyImpl P X C W G := by
  induction h with
  | leaf X C t u hX hstop hD hA => exact PolicyImpl.leaf X C t u hX hstop hD hA
  | node X C T hX hC hc hlt SL G W' Wc hWc hW' _ ih =>
      exact PolicyImpl.node X C T hX hC hc hlt SL G W' Wc hWc hW' ih

/-- **Scan corollary**: `PolicyImpl.specOn` re-derived from the exact-width proof. -/
theorem PolicyImpl.specOn_of_exact {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    {P : PTPPolicy} (hP : P.check = true) {X : Fin 3 → ExtReg} {C : ℕ} {W : List ℕ}
    {G : Angle → LowGate} (h : PolicyImpl P X C W G) (θ : Angle) :
    SpecOn (qs := qs) X C W θ (G θ) :=
  h.toD.specOn hP (admissible_scan P hP) θ

/-! ## Census formulas for a width rule -/






theorem ptpResourcesD_scan (P : PTPPolicy) : ∀ n, ptpResourcesD P scanRule n = ptpResources P n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases hc : P.choose n with _ | T
    · rw [ptpResourcesD, ptpResources, hc]
    · rw [ptpResourcesD, ptpResources, hc]
      by_cases hlt : childWidth n T.ops < n
      · simp only [scanRule, hlt, ↓reduceDIte, ih _ hlt]
      · simp only [scanRule, hlt, ↓reduceDIte]

theorem ptpAndDagD_scan (P : PTPPolicy) : ∀ n, ptpAndDagD P scanRule n = ptpAndDag P n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases hc : P.choose n with _ | T
    · rw [ptpAndDagD, ptpAndDag, hc]
    · rw [ptpAndDagD, ptpAndDag, hc]
      by_cases hlt : childWidth n T.ops < n
      · simp only [scanRule, hlt, ↓reduceDIte, ih _ hlt]
      · simp only [scanRule, hlt, ↓reduceDIte]

theorem ptpCnotFullD_scan (P : PTPPolicy) : ∀ n, ptpCnotFullD P scanRule n = ptpCnotFull P n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases hc : P.choose n with _ | T
    · rw [ptpCnotFullD, ptpCnotFull, hc]
    · rw [ptpCnotFullD, ptpCnotFull, hc]
      by_cases hlt : childWidth n T.ops < n
      · simp only [scanRule, hlt, ↓reduceDIte, ih _ hlt]
      · simp only [scanRule, hlt, ↓reduceDIte]

theorem ptpWorkspaceD_scan (P : PTPPolicy) : ∀ n, ptpWorkspaceD P scanRule n = ptpWorkspace P n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases hc : P.choose n with _ | T
    · rw [ptpWorkspaceD, ptpWorkspace, hc]
    · rw [ptpWorkspaceD, ptpWorkspace, hc]
      by_cases hlt : childWidth n T.ops < n
      · simp only [scanRule, hlt, ↓reduceDIte, ih _ hlt]
      · simp only [scanRule, hlt, ↓reduceDIte]

/-! ## Census through the full recursion, any width rule -/

/-- **Rz / Toffoli / X / H through the full recursion** (`PolicyImpl.resources` for `wd`). -/
theorem PolicyImplD.resources {P : PTPPolicy} {wd : WidthRule} {X : Fin 3 → ExtReg} {C : ℕ}
    {W : List ℕ} {G : Angle → LowGate} (h : PolicyImplD P wd X C W G) (θ : Angle) :
    let R := LowGate.resources P.resourceModel (G θ)
    R.rz = (ptpResourcesD P wd C).rz ∧ R.toffoli = (ptpResourcesD P wd C).toffoli ∧
      R.x = (ptpResourcesD P wd C).x ∧ R.h = (ptpResourcesD P wd C).h := by
  unfold PTPPolicy.resourceModel
  induction h generalizing θ with
  | leaf X C t u hX hstop hD hA =>
      have hl : ptpResourcesD P wd C = leafCensus C := by
        rw [ptpResourcesD]
        rcases hcC : P.choose C with _ | T
        · rfl
        · simp only [Nat.not_lt.mpr (hstop T hcC), ↓reduceDIte]
      obtain ⟨h1, h2, _, h4, h5, _⟩ := ptpLeafSandwich_resources _ θ
        (X 0) (X 1) (X 2) t u
      simp only [hl, leafCensus, hX] at h1 h2 h4 h5 ⊢
      exact ⟨h1, h2, h4, h5⟩
  | node X C T hX hC hc hlt SL G W' Wc hWc hW' hsub ih =>
      have hn : ptpResourcesD P wd C = nodeCensusFor P.negation (wd T C) (addCount T.ops)
          (negCount T.ops) (cpCount T.ops) (ptpResourcesD P wd (wd T C)) := by
        rw [ptpResourcesD, hc]
        simp only [hlt, ↓reduceDIte]
      have hch := fun j => ih j
      have key : ∀ (F : AddField), (∀ n, F.f { cnot := n } = 0) → ∀ (c : ℕ),
          (∀ j θ', F.f (LowGate.resources (shorGateResourceModelFor P.negation) (G j θ')) = c) →
          F.f (LowGate.resources (shorGateResourceModelFor P.negation)
            (ptpSubNode T SL (fun t j => G j (θ * coeffN T C t)))) =
          3 * (addCount T.ops * F.f (cuccaroModAddResources (wd T C)) +
            negCount T.ops * F.f (opRes P.negation (wd T C) (.negate (k := 1) 0))) +
              cpCount T.ops * c := by
        intro F hF c hc'
        unfold ptpSubNode
        simp only [LowGate.resources, F.seq, alloc_field_zero P.negation SL F hF, zero_add, add_zero]
        exact (body_field F P.negation SL.lay _ c (fun t j => hc' j _) T.ops 0).trans
          (bodyField_eq F P.negation SL.lay.width c T.ops)
      have hrz := key fRz (fun _ => rfl) _ fun j θ' => (hch j θ').1
      have hto := key fToff (fun _ => rfl) _ fun j θ' => (hch j θ').2.1
      have hx := key fX (fun _ => rfl) _ fun j θ' => (hch j θ').2.2.1
      have hh := key fH (fun _ => rfl) _ fun j θ' => (hch j θ').2.2.2
      simp only [fRz, fToff, fX, fH, opRes, cuccaroModAddResources] at hrz hto hx hh
      dsimp only
      rw [hn]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [show (LowGate.resources (shorGateResourceModelFor P.negation) _).rz = _ from hrz]
        simp only [nodeCensusFor]; try ring
      · rw [show (LowGate.resources (shorGateResourceModelFor P.negation) _).toffoli = _ from hto]
        simp only [nodeCensusFor]
      · rw [show (LowGate.resources (shorGateResourceModelFor P.negation) _).x = _ from hx]
        simp only [nodeCensusFor]
      · rw [show (LowGate.resources (shorGateResourceModelFor P.negation) _).h = _ from hh]
        simp only [nodeCensusFor]; try ring

/-- **And† through the full recursion**, any width rule. -/
theorem PolicyImplD.andDag_count {P : PTPPolicy} {wd : WidthRule} {X : Fin 3 → ExtReg} {C : ℕ}
    {W : List ℕ} {G : Angle → LowGate} (h : PolicyImplD P wd X C W G) (θ : Angle) :
    adjToffCount (G θ) = ptpAndDagD P wd C := by
  induction h generalizing θ with
  | leaf X C t u hX hstop hD hA =>
      have hl : ptpAndDagD P wd C = C * C + C * C * C := by
        rw [ptpAndDagD]
        rcases hcC : P.choose C with _ | T
        · rfl
        · simp only [Nat.not_lt.mpr (hstop T hcC), ↓reduceDIte]
      have := (ptpLeafSandwich_counts θ (X 0) (X 1) (X 2) t u).2.2.1
      simp only [hX] at this
      rw [this, hl]
  | node X C T hX hC hc hlt SL G W' Wc hWc hW' hsub ih =>
      have hn : ptpAndDagD P wd C = cpCount T.ops * ptpAndDagD P wd (wd T C) := by
        rw [ptpAndDagD, hc]
        simp only [hlt, ↓reduceDIte]
      show adjToffCount (ptpSubNode T SL _) = _
      unfold ptpSubNode
      simp only [adjToffCount, adjToffCount_alloc, zero_add]
      rw [hn]
      refine body_count adjToffCount rfl (fun _ _ => rfl) SL.lay (fun s op => by cases op <;> rfl)
        _ _ (fun t j => ih j _) T.ops 0

/-- **CNOT through the full recursion** (sign-extension fan-out included), any width rule. -/
theorem PolicyImplD.cnot {P : PTPPolicy} {wd : WidthRule} {X : Fin 3 → ExtReg} {C : ℕ}
    {W : List ℕ} {G : Angle → LowGate} (h : PolicyImplD P wd X C W G) (θ : Angle) :
    (LowGate.resources P.resourceModel (G θ)).cnot = ptpCnotFullD P wd C := by
  unfold PTPPolicy.resourceModel
  induction h generalizing θ with
  | leaf X C t u hX hstop hD hA =>
      have hl : ptpCnotFullD P wd C = 0 := by
        rw [ptpCnotFullD]
        rcases hcC : P.choose C with _ | T
        · rfl
        · simp only [Nat.not_lt.mpr (hstop T hcC), ↓reduceDIte]
      rw [hl]
      exact (ptpLeafSandwich_resources _ θ (X 0) (X 1) (X 2) t u).2.2.1
  | node X C T hX hC hc hlt SL G W' Wc hWc hW' hsub ih =>
      have hn : ptpCnotFullD P wd C =
          3 * (addCount T.ops * (5 * wd T C - 7) + negCount T.ops * negateCnotGatesFor P.negation (wd T C)) +
            6 * (wd T C - topLimbWidth C T.k) +
            cpCount T.ops * ptpCnotFullD P wd (wd T C) := by
        rw [ptpCnotFullD, hc]
        simp only [hlt, ↓reduceDIte]
      show (LowGate.resources (shorGateResourceModelFor P.negation) (ptpSubNode T SL _)).cnot = _
      unfold ptpSubNode
      have hb := (body_field fCnot P.negation SL.lay (fun t j => G j (θ * coeffN T C t))
        (ptpCnotFullD P wd (wd T C)) (fun t j => ih j _) T.ops 0).trans
          (bodyField_eq fCnot P.negation SL.lay.width _ T.ops)
      simp only [fCnot, opRes, cuccaroModAddResources] at hb
      simp only [LowGate.resources, GateResources.seq, cnot_alloc, SL.ext_top hX]
      rw [show (LowGate.resources (shorGateResourceModelFor P.negation) (body SL.lay _ 0 T.ops)).cnot = _
        from hb, hn]
      show _ = 3 * (addCount T.ops * (5 * SL.lay.width - 7) +
        negCount T.ops * negateCnotGatesFor P.negation (SL.lay.width)) + _ + _
      ring

/-- **Clean scratch through the full recursion**, any width rule: every gate-level recursion following `P`
holds at most `ptpCleanAncD P wd C` clean qubits at once in the policy's resource model `P.resourceModel`
(`1` per node that adds or negates under `oneQubit`; `C' + 1` at a node of width `C'` that negates under
`scratch`; the sandwich leaves hold none). -/
theorem PolicyImplD.cleanAnc_le {P : PTPPolicy} {wd : WidthRule} {X : Fin 3 → ExtReg} {C : ℕ}
    {W : List ℕ} {G : Angle → LowGate} (h : PolicyImplD P wd X C W G) (θ : Angle) :
    (LowGate.resources P.resourceModel (G θ)).cleanAnc ≤ ptpCleanAncD P wd C := by
  unfold PTPPolicy.resourceModel
  induction h generalizing θ with
  | leaf X C t u hX hstop hD hA =>
      rw [(ptpLeafSandwich_resources _ θ (X 0) (X 1) (X 2) t u).2.2.2.2.2]
      exact Nat.zero_le _
  | node X C T hX hC hc hlt SL G W' Wc hWc hW' hsub ih =>
      have hn : ptpCleanAncD P wd C =
          max (nodeCleanAncFor P.negation (wd T C) (addCount T.ops) (negCount T.ops))
            (ptpCleanAncD P wd (wd T C)) := by
        rw [ptpCleanAncD, hc]
        simp only [hlt, ↓reduceDIte]
      show (LowGate.resources (shorGateResourceModelFor P.negation) (ptpSubNode T SL _)).cleanAnc ≤ _
      unfold ptpSubNode
      have hb := body_cleanAnc_leFor P.negation SL.lay (fun t j => G j (θ * coeffN T C t))
        (ptpCleanAncD P wd (wd T C)) (fun t j => ih j _) T.ops 0
      simp only [LowGate.resources, GateResources.seq, cleanAnc_alloc]
      rw [hn]
      have hb' : (LowGate.resources (shorGateResourceModelFor P.negation)
          (body SL.lay (fun t j ↦ G j (θ * coeffN T C t)) 0 T.ops)).cleanAnc ≤
          max (nodeCleanAncFor P.negation (wd T C) (addCount T.ops) (negCount T.ops))
            (ptpCleanAncD P wd (wd T C)) := hb
      omega

/-- **Qubits of a gate-level recursion**, any width rule: only the registers and the workspace. -/
theorem PolicyImplD.usedQubits {P : PTPPolicy} {wd : WidthRule} {X : Fin 3 → ExtReg} {C : ℕ}
    {W : List ℕ} {G : Angle → LowGate} (h : PolicyImplD P wd X C W G) (θ : Angle) :
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

/-- Qubit count of a recursion whose workspace lies in `[base, base + M)`: at most `3 n + M`. -/
theorem qubits_le_of_policyImplD {P : PTPPolicy} {wd : WidthRule} {X : Fin 3 → ExtReg}
    {n base M : ℕ} {W : List ℕ} {G : Angle → LowGate} (h : PolicyImplD P wd X n W G)
    (hX : ∀ s, (X s).width = n) (hW : ∀ q ∈ W, base ≤ q ∧ q < base + M) (θ : Angle) :
    (LowGate.usedQubits (G θ)).card ≤ 3 * n + M := by
  have hsub : LowGate.usedQubits (G θ) ⊆
      ((X 0).active.qubits.toFinset ∪ (X 1).active.qubits.toFinset ∪ (X 2).active.qubits.toFinset) ∪
        Finset.Ico base (base + M) := by
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
          (X 2).active.qubits.toFinset).card + (Finset.Ico base (base + M)).card :=
        Finset.card_union_le _ _
    _ ≤ (n + n + n) + M := by
        refine Nat.add_le_add ?_ (by simp)
        refine (Finset.card_union_le _ _).trans (Nat.add_le_add ?_ (hcard 2))
        exact (Finset.card_union_le _ _).trans (Nat.add_le_add (hcard 0) (hcard 1))
    _ = 3 * n + M := by ring

end PTP
end Shor
