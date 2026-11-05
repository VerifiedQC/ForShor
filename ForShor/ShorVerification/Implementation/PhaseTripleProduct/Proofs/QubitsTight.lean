import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Statement
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.ExactBoard.ExactBuild
/-!
# Tight qubit accounting for the constructed PTP circuit (blueprint item O7)

`ptp_gate_full_exact` bounds the qubit count by `3n + ptpWorkspaceX P n`, where the workspace is
an *interval* `[base, base + ptpWorkspace)` whose slot blocks are spaced `C'` apart although only
`extOf` qubits of each block are used. Here the count is made tight:

* `ptpWsTD P wd n`: workspace actually used: at a node, the `3 (k C' - n)` extension qubits
  (all three operands grow from `n` to `k` slots of width `C'`) plus the children's workspace,
  which the children **share**; two leaf ancillas at the bottom;
* `poolU`: the canonical set of workspace qubits the construction touches (`card ≤ ptpWsTD`,
  `card_poolU_le`);
* `exists_policyImplD_tight`: the existence theorem with the extra clause that every qubit the
  circuit touches is in the registers or in `poolU`, hence `qubits_le_tight`:
  `|used| ≤ 3 n + ptpWsTD P wd n`;
* `ptpWsTD_le_formula`: `3 n + ptpWsTD ≤` the `ptpQubits`-shaped formula
  `3 n + 3 · ptpReserveNeedD + max (ptpCleanAncD) 2` (at the scan rule this is `ptpQubits`), so the
  formula, previously unproved, is a proved **upper bound** on the number of distinct qubits the
  circuit names (`LowGate.usedQubits`).

**What is not bounded.** The framework's qubit total is `usedQubits + resources.cleanAnc`
(`LowGate.qubitCount`); the Cuccaro/negation scratch counted in `cleanAnc` is *not* part of these
bounds, and `cleanAnc` of the full recursive circuit is not proved here (only single-node lemmas such
as `ptpNode_cleanAnc_le`). The formula is also loose by up to a factor `k` per level below depth one:
`ptpReserveNeed` gives every child slot a private workspace, while the construction shares one pool.
-/

namespace Shor
namespace PTP

open Shor Operations

/-! ## Definitions -/




theorem ptpReserveNeedD_scan (P : PTPPolicy) : ∀ n, ptpReserveNeedD P scanRule n = ptpReserveNeed P n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases hc : P.choose n with _ | T
    · rw [ptpReserveNeedD, ptpReserveNeed, hc]
    · rw [ptpReserveNeedD, ptpReserveNeed, hc]
      by_cases hlt : childWidth n T.ops < n
      · simp only [scanRule, hlt, ↓reduceDIte, ih _ hlt]
      · simp only [scanRule, hlt, ↓reduceDIte]

theorem ptpCleanAncD_scan (P : PTPPolicy) : ∀ n, ptpCleanAncD P scanRule n = ptpCleanAnc P n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases hc : P.choose n with _ | T
    · rw [ptpCleanAncD, ptpCleanAnc, hc]
    · rw [ptpCleanAncD, ptpCleanAnc, hc]
      by_cases hlt : childWidth n T.ops < n
      · simp only [scanRule, hlt, ↓reduceDIte, ih _ hlt]
      · simp only [scanRule, hlt, ↓reduceDIte]

/-- **The formula bounds the tight count** (any width rule, tables with `k ≥ 1`). -/
theorem ptpWsTD_le_formula (P : PTPPolicy) (wd : WidthRule)
    (hk : ∀ n T, P.choose n = some T → 1 ≤ T.k) :
    ∀ n, ptpWsTD P wd n ≤ 3 * ptpReserveNeedD P wd n + max (ptpCleanAncD P wd n) 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases hc : P.choose n with _ | T
    · rw [ptpWsTD, ptpReserveNeedD, ptpCleanAncD, hc]; simp
    · by_cases hlt : wd T n < n
      · have h1 := ih _ hlt
        have hk1 := hk n T hc
        rw [ptpWsTD, ptpReserveNeedD, ptpCleanAncD, hc]
        simp only [hlt, ↓reduceDIte]
        set r := ptpReserveNeedD P wd (wd T n)
        set a := ptpCleanAncD P wd (wd T n)
        have h2 : r ≤ T.k * r := Nat.le_mul_of_pos_left r hk1
        have h3 : max a 2 ≤ max (max (if negCount T.ops = 0 then (if addCount T.ops = 0 then 0 else 1)
            else wd T n + 1) a) 2 := max_le_max (le_max_right _ _) le_rfl
        omega
      · rw [ptpWsTD, ptpReserveNeedD, ptpCleanAncD, hc]
        simp only [hlt, ↓reduceDIte]; simp


/-! ## The canonical pool -/

/-- The extension qubits of one node: block `(s, j)` is `[base + (sk + j) C', … + extOf)`. -/
def nodeExt (base C C' k : ℕ) : Finset ℕ :=
  Finset.univ.biUnion fun p : Fin 3 × Fin k =>
    Finset.Ico (base + slotIdx k p.1 p.2 * C') (base + slotIdx k p.1 p.2 * C' + extOf C C' k p.2)

/-- Every workspace qubit the construction touches. -/
def poolU (P : PTPPolicy) (wd : WidthRule) (n base : ℕ) : Finset ℕ :=
  match P.choose n with
  | none => {base, base + 1}
  | some T =>
      if _h : wd T n < n then
        nodeExt base n (wd T n) T.k ∪ poolU P wd (wd T n) (base + 3 * T.k * wd T n)
      else {base, base + 1}
termination_by n

theorem sum_chunk (k C : ℕ) (hk : 0 < k) :
    ∑ j : Fin k, (if (j : ℕ) + 1 = k then C - (k - 1) * (C / k) else C / k) = C := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Fin.sum_univ_castSucc]
  have h1 : ∀ i : Fin k', (if ((i.castSucc : Fin (k' + 1)) : ℕ) + 1 = k' + 1 then
      C - (k' + 1 - 1) * (C / (k' + 1)) else C / (k' + 1)) = C / (k' + 1) := fun i => by
    have : (i : ℕ) < k' := i.2
    simp; omega
  simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  simp only [Fin.val_last, ↓reduceIte, Nat.add_sub_cancel]
  have : k' * (C / (k' + 1)) ≤ C :=
    (Nat.mul_le_mul_right _ (Nat.le_succ k')).trans (Nat.mul_div_le C (k' + 1))
  omega

theorem sum_extOf (k C C' : ℕ) (hk : 2 ≤ k) (hF : ptpFloor k C ≤ C') :
    ∑ j : Fin k, extOf C C' k j = k * C' - C := by
  have hc : ∀ j : Fin k, extOf C C' k j + (if (j : ℕ) + 1 = k then C - (k - 1) * (C / k) else C / k)
      = C' := by
    intro j
    have := limb_le_floor C C' hF j
    unfold extOf
    by_cases hj : (j : ℕ) + 1 = k
    · have := this.2 hj; simp only [hj, ↓reduceIte] at *; omega
    · have := this.1 hj; simp only [hj, ↓reduceIte] at *; omega
  have hsum : ∑ j : Fin k, extOf C C' k j + C = k * C' := by
    have hs := sum_chunk k C (by omega)
    have h1 : ∑ j : Fin k, extOf C C' k j +
        ∑ j : Fin k, (if (j : ℕ) + 1 = k then C - (k - 1) * (C / k) else C / k) = k * C' := by
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun j _ => hc j)]
      simp
    omega
  omega

theorem card_nodeExt_le (base C C' k : ℕ) (hk : 2 ≤ k) (hF : ptpFloor k C ≤ C') :
    (nodeExt base C C' k).card ≤ 3 * (k * C' - C) := by
  unfold nodeExt
  refine Finset.card_biUnion_le.trans ?_
  have : ∀ p : Fin 3 × Fin k,
      (Finset.Ico (base + slotIdx k p.1 p.2 * C')
        (base + slotIdx k p.1 p.2 * C' + extOf C C' k p.2)).card = extOf C C' k p.2 := by
    intro p; simp
  simp only [this]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [sum_extOf k C C' hk hF]

theorem card_poolU_le (P : PTPPolicy) (wd : WidthRule)
    (hfl : ∀ n T, P.choose n = some T → wd T n < n → 2 ≤ T.k ∧ ptpFloor T.k n ≤ wd T n) :
    ∀ n base, (poolU P wd n base).card ≤ ptpWsTD P wd n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro base
    rcases hc : P.choose n with _ | T
    · rw [poolU, ptpWsTD, hc]; simp
    · by_cases hlt : wd T n < n
      · obtain ⟨hk, hF⟩ := hfl n T hc hlt
        rw [poolU, ptpWsTD, hc]
        simp only [hlt, ↓reduceDIte]
        refine (Finset.card_union_le _ _).trans ?_
        have := card_nodeExt_le base n (wd T n) T.k hk hF
        have := ih _ hlt (base + 3 * T.k * wd T n)
        omega
      · rw [poolU, ptpWsTD, hc]; simp only [hlt, ↓reduceDIte]; simp


/-! ## Used qubits of one node, relative to a child pool -/

theorem ptpSubNode_used {X : Fin 3 → ExtReg} {T : PTPTable} {C' : ℕ} (SL : SplitLayout X T.k C')
    (gc : ℕ → Fin T.k → LowGate) (E : Finset ℕ)
    (hch : ∀ t j, ∀ q ∈ LowGate.usedQubits (gc t j), q ∈ slotQubits SL.lay ∨ q ∈ E) :
    ∀ q ∈ LowGate.usedQubits (ptpSubNode T SL gc), q ∈ slotQubits SL.lay ∨ q ∈ E := by
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
  have hbody := body_usedQubits_subset SL.lay gc (slotQubits SL.lay ∪ E) Finset.subset_union_left
    (fun t j q hq => by
      rcases hch t j q hq with h | h
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ h) T.ops 0
  intro q hq
  unfold ptpSubNode at hq
  simp only [LowGate.usedQubits, Finset.mem_union] at hq
  rcases hq with hq | hq | hq
  · exact Or.inl (halloc hq)
  · rcases Finset.mem_union.mp (hbody hq) with h | h
    · exact Or.inl h
    · exact Or.inr h
  · exact Or.inl (halloc hq)

theorem mem_nodeExt_of_R {X : Fin 3 → ExtReg} {C base : ℕ} {T : PTPTable} {C' : ℕ} {hk : 2 ≤ T.k}
    {hG : Good X C base} {hF : ptpFloor T.k C ≤ C'} {q : ℕ}
    (h : q ∈ (mkSplitD X C base T C' hk hG hF).R) : q ∈ nodeExt base C C' T.k := by
  simp only [SplitLayout.R, List.mem_flatMap, List.mem_finRange, true_and] at h
  obtain ⟨s, j, hq⟩ := h
  have hq' := mem_interval.mp (List.mem_of_mem_take hq)
  simp only [nodeExt, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_Ico]
  exact ⟨(s, j), hq'.1, hq'.2⟩


/-! ## Tight existence and the qubit bound -/

/-- **O7 (existence, tight).** `exists_policyImplD` with the extra clause: every qubit the circuit
touches lies in the three registers or in the canonical pool `poolU P wd C base`. -/
theorem exists_policyImplD_tight (P : PTPPolicy) (hP : P.check = true) (wd : WidthRule)
    (hwd : Admissible P wd) :
    ∀ (C : ℕ) (X : Fin 3 → ExtReg) (base : ℕ), Good X C base →
      ∃ (W : List ℕ) (G : Angle → LowGate),
        PolicyImplD P wd X C W G ∧ (∀ q ∈ W, base ≤ q ∧ q < base + ptpWorkspaceD P wd C) ∧
        ∀ φ, ∀ q ∈ LowGate.usedQubits (G φ),
          (∃ s, q ∈ (X s).active.qubits) ∨ q ∈ poolU P wd C base := by
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
    have hpool : poolU P wd C base = nodeExt base C (wd b.table C) b.table.k ∪
        poolU P wd (wd b.table C) (base + 3 * b.table.k * wd b.table C) := by
      rw [poolU, hc]; simp only [hlt, ↓reduceDIte]
    set T := b.table
    set SL := mkSplitD X C base T (wd T C) hk hG hF
    have hgood : ∀ j, Good (fun s => SL.lay.slot s j) (wd T C) (base + 3 * T.k * (wd T C)) := by
      intro j
      refine ⟨fun s => SL.lay.slot_width s j, fun s s' hs => SL.disjoint s j s' j (by
        intro e; exact hs (Prod.mk.inj e).1), fun s q hq => slot_lt_mkSplitD s j hq⟩
    have hex := fun j => ih (wd T C) hlt (fun s => SL.lay.slot s j) (base + 3 * T.k * (wd T C)) (hgood j)
    choose Wc Gc hImpl hBound hUsed using hex
    refine ⟨SL.R ++ List.range' (base + 3 * T.k * (wd T C)) (ptpWorkspaceD P wd (wd T C)), _,
      PolicyImplD.node X C T hG.1 hC hc hlt SL Gc
        (List.range' (base + 3 * T.k * (wd T C)) (ptpWorkspaceD P wd (wd T C))) Wc ?_ ?_
        hImpl, ?_, ?_⟩
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
    · intro φ q hq
      have hsubn := ptpSubNode_used SL (fun t j => Gc j (φ * coeffN T C t))
        (poolU P wd (wd T C) (base + 3 * T.k * wd T C)) (fun t j q hq => by
          rcases hUsed j (φ * coeffN T C t) q hq with ⟨s, hs⟩ | hp
          · exact Or.inl (mem_slotQubits SL.lay hs)
          · exact Or.inr hp) q hq
      rcases hsubn with h | h
      · simp only [slotQubits, Finset.mem_biUnion, Finset.mem_univ, true_and,
          List.mem_toFinset] at h
        obtain ⟨s, j, hm⟩ := h
        rcases SL.mem_slot hm with hx | hr
        · exact Or.inl ⟨s, hx⟩
        · right; rw [hpool]; exact Finset.mem_union_left _ (mem_nodeExt_of_R hr)
      · right; rw [hpool]; exact Finset.mem_union_right _ h
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
    have hpool : poolU P wd C base = {base, base + 1} := by
      rw [poolU]
      rcases hcC : P.choose C with _ | T
      · rfl
      · simp only [Nat.not_lt.mpr (hstop T hcC), ↓reduceDIte]
    refine ⟨[base, base + 1], _, PolicyImplD.leaf X C base (base + 1) hG.1 hstop hD hA, ?_, ?_⟩
    · rw [hw]
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      omega
    · intro φ q hq
      have := ptpLeafSandwich_usedQubits_subset φ (X 0) (X 1) (X 2) base (base + 1) hq
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, extRegActiveQubits,
        List.mem_toFinset] at this
      rcases this with ((h0 | h1) | h2) | rfl | rfl
      · exact Or.inl ⟨0, h0⟩
      · exact Or.inl ⟨1, h1⟩
      · exact Or.inl ⟨2, h2⟩
      · right; rw [hpool]; simp
      · right; rw [hpool]; simp


theorem ptpWsTD_le_workspace (P : PTPPolicy) (wd : WidthRule) :
    ∀ n, ptpWsTD P wd n ≤ ptpWorkspaceD P wd n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases hc : P.choose n with _ | T
    · rw [ptpWsTD, ptpWorkspaceD, hc]
    · by_cases hlt : wd T n < n
      · have := ih _ hlt
        rw [ptpWsTD, ptpWorkspaceD, hc]; simp only [hlt, ↓reduceDIte]
        have : T.k * wd T n - n ≤ T.k * wd T n := Nat.sub_le _ _
        have h2 : 3 * (T.k * wd T n) = 3 * T.k * wd T n := by ring
        omega
      · rw [ptpWsTD, ptpWorkspaceD, hc]; simp only [hlt, ↓reduceDIte]; rfl

/-- **Tight qubit count of the constructed circuit** (any admissible width rule): it touches at most
`3 n + ptpWsTD P wd n` qubits, and that is at most the `ptpQubits`-shaped formula
`3 n + 3 ptpReserveNeedD + max ptpCleanAncD 2`. -/
theorem ptp_qubits_tight_core (P : PTPPolicy) (hP : P.check = true) (wd : WidthRule)
    (hwd : Admissible P wd) (n : ℕ) (X : Fin 3 → ExtReg) (base : ℕ) (hG : Good X n base) :
    ∃ (W : List ℕ) (G : Angle → LowGate), PolicyImplD P wd X n W G ∧
      ∀ φ, (LowGate.usedQubits (G φ)).card ≤ 3 * n + ptpWsTD P wd n ∧
        3 * n + ptpWsTD P wd n ≤
          3 * n + (3 * ptpReserveNeedD P wd n + max (ptpCleanAncD P wd n) 2) := by
  obtain ⟨W, G, hI, _, hU⟩ := exists_policyImplD_tight P hP wd hwd n X base hG
  have hfl : ∀ m T, P.choose m = some T → wd T m < m → 2 ≤ T.k ∧ ptpFloor T.k m ≤ wd T m := by
    intro m T hc hlt
    obtain ⟨b, hb, rfl⟩ := PTPPolicy.choose_mem hc
    have hT := PTPPolicy.check_tables hP b hb
    exact ⟨((PTPTable.contract_iff b.table).mp hT).1,
      (floor_le_tight b.table hT m).trans (hwd b hb m (by omega))⟩
  have hk : ∀ m T, P.choose m = some T → 1 ≤ T.k := by
    intro m T hc
    obtain ⟨b, hb, rfl⟩ := PTPPolicy.choose_mem hc
    have hT := PTPPolicy.check_tables hP b hb
    have := ((PTPTable.contract_iff b.table).mp hT).1
    omega
  refine ⟨W, G, hI, fun φ => ⟨?_, ?_⟩⟩
  · have hsub : LowGate.usedQubits (G φ) ⊆
        ((X 0).active.qubits.toFinset ∪ (X 1).active.qubits.toFinset ∪
          (X 2).active.qubits.toFinset) ∪ poolU P wd n base := by
      intro q hq
      rcases hU φ q hq with ⟨s, hs⟩ | hp
      · apply Finset.mem_union_left
        fin_cases s <;> simp_all
      · exact Finset.mem_union_right _ hp
    have hcard : ∀ s, (X s).active.qubits.toFinset.card ≤ n := fun s =>
      (List.toFinset_card_le _).trans (le_of_eq (hG.1 s))
    have hp := card_poolU_le P wd hfl n base
    calc (LowGate.usedQubits (G φ)).card ≤ _ := Finset.card_le_card hsub
      _ ≤ ((X 0).active.qubits.toFinset ∪ (X 1).active.qubits.toFinset ∪
            (X 2).active.qubits.toFinset).card + (poolU P wd n base).card := Finset.card_union_le _ _
      _ ≤ (n + n + n) + ptpWsTD P wd n := by
          refine Nat.add_le_add ?_ hp
          refine (Finset.card_union_le _ _).trans (Nat.add_le_add ?_ (hcard 2))
          exact (Finset.card_union_le _ _).trans (Nat.add_le_add (hcard 0) (hcard 1))
      _ = 3 * n + ptpWsTD P wd n := by ring
  · have := ptpWsTD_le_formula P wd hk n
    omega

/-- Exact board (some `PolicyImplX` witness; not tied to the witness of `ptp_gate_full_exact`, though
both come from the same construction): the circuit touches at most `3 n + ptpWsTD P exactRule n`
qubits (never more than the interval bound `3 n + ptpWorkspaceX P n`). -/
theorem ptp_qubits_tight_exact_core (P : PTPPolicy) (hP : P.check = true) (n : ℕ)
    (X : Fin 3 → ExtReg) (base : ℕ) (hG : Good X n base) :
    ∃ (W : List ℕ) (G : Angle → LowGate), PolicyImplX P X n W G ∧
      ∀ φ, (LowGate.usedQubits (G φ)).card ≤ 3 * n + ptpWsTD P exactRule n ∧
        ptpWsTD P exactRule n ≤ ptpWorkspaceX P n :=
  let ⟨W, G, hI, h⟩ := ptp_qubits_tight_core P hP exactRule (admissible_exact P) n X base hG
  ⟨W, G, hI, fun φ => ⟨(h φ).1, ptpWsTD_le_workspace P exactRule n⟩⟩


/-- **`ptpQubits` is a proved upper bound** (scan board): there is a circuit following `P` with the
PTP scan widths touching at most `ptpQubits P n` qubits. -/
theorem ptp_qubits_le_ptpQubits_core (P : PTPPolicy) (hP : P.check = true) (n : ℕ)
    (X : Fin 3 → ExtReg) (base : ℕ) (hG : Good X n base) :
    ∃ (W : List ℕ) (G : Angle → LowGate), PolicyImpl P X n W G ∧
      ∀ φ, (LowGate.usedQubits (G φ)).card ≤ ptpQubits P n := by
  obtain ⟨W, G, hI, h⟩ := ptp_qubits_tight_core P hP scanRule (admissible_scan P hP) n X base hG
  refine ⟨W, G, hI.toScan, fun φ => ?_⟩
  have := h φ
  rw [ptpReserveNeedD_scan, ptpCleanAncD_scan] at this
  unfold ptpQubits
  omega

end PTP
end Shor
