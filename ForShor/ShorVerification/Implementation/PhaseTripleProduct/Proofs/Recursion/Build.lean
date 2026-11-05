import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Statement
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Recursion.Recursion
/-!
# O2 closed: every checked PTP policy has a gate-level recursion at every width

`exists_policyImpl`: for a checked policy `P`, every width `C` and any three pairwise
disjoint `C`-qubit registers whose qubits lie below `base`, there is a gate-level
recursion following `P` (`PolicyImpl`) whose workspace lies in `[base, base + ptpWorkspace P C)`.
The construction is explicit (in the proof): at each node the child slot `(s, j)` is chunk
`j` of `X s` plus `C' - |chunk|` fresh qubits at `base + (s k + j) C'`; the children share
the pool above `base + 3 k C'`; the leaves use two fresh ancillas.
With `PolicyImpl.specOn` this gives gate-level correctness through the full recursion
(`ptp_gate_correct`), and with `PolicyImpl.resources` the Rz / Toffoli / X / H census
`ptpResources P n` becomes a theorem at every depth (`ptp_gate_census`).
-/

namespace Shor
namespace PTP

open Shor

/-! ## List facts -/

theorem mem_chunkReg {r : Reg} {k L : ℕ} {j : Fin k} {q : ℕ} (h : q ∈ (chunkReg r k L j).qubits) :
    q ∈ r.qubits := by
  unfold chunkReg at h
  split at h
  · exact List.mem_of_mem_drop h
  · exact List.mem_of_mem_drop (List.mem_of_mem_take h)

theorem chunkReg_length (r : Reg) (k L : ℕ) (j : Fin k) (h : (j : ℕ) * L + L ≤ regSize r ∨ (j : ℕ) + 1 = k) :
    (chunkReg r k L j).qubits.length = if (j : ℕ) + 1 = k then regSize r - j * L else L := by
  unfold chunkReg
  split
  · simp [Reg.drop, regSize, Reg.width]
  · rename_i hj
    have h' : (j : ℕ) * L + L ≤ regSize r := by tauto
    simp only [Reg.take, Reg.drop, List.length_take, List.length_drop]
    simp only [regSize, Reg.width] at h'
    omega

/-- A lower chunk lies in the prefix `take m` once `jL + L ≤ m`. -/
theorem mem_take_of_lower {r : Reg} {k L : ℕ} {j : Fin k} (hj : (j : ℕ) + 1 ≠ k) {m : ℕ}
    (hm : (j : ℕ) * L + L ≤ m) {q : ℕ} (h : q ∈ (chunkReg r k L j).qubits) : q ∈ r.qubits.take m := by
  unfold chunkReg at h
  simp only [hj, ↓reduceIte] at h
  simp only [Reg.take, Reg.drop] at h
  have e : List.take L (List.drop ((j : ℕ) * L) r.qubits) =
      List.drop ((j : ℕ) * L) (List.take ((j : ℕ) * L + L) r.qubits) := by
    rw [List.drop_take]; congr 1; omega
  rw [e] at h
  have h2 := List.mem_of_mem_drop h
  rw [show List.take ((j : ℕ) * L + L) r.qubits = List.take ((j : ℕ) * L + L) (List.take m r.qubits) by
    rw [List.take_take, min_eq_left hm]] at h2
  exact List.mem_of_mem_take h2

theorem mem_drop_chunk {r : Reg} {k L : ℕ} {j : Fin k} {q : ℕ} (h : q ∈ (chunkReg r k L j).qubits) :
    q ∈ r.qubits.drop (j * L) := by
  unfold chunkReg at h
  split at h
  · exact h
  · exact List.mem_of_mem_take h

/-- Distinct chunks of a register are disjoint. -/
theorem chunk_disjoint (r : Reg) (k L : ℕ) {j j' : Fin k} (hjj : (j : ℕ) < j') {q : ℕ}
    (h1 : q ∈ (chunkReg r k L j).qubits) (h2 : q ∈ (chunkReg r k L j').qubits) : False := by
  have hj : (j : ℕ) + 1 ≠ k := by have := j'.2; omega
  have a := mem_take_of_lower hj (m := (j' : ℕ) * L)
    (by nlinarith [Nat.mul_le_mul_right L (show (j : ℕ) + 1 ≤ j' by omega)]) h1
  have b := mem_drop_chunk h2
  exact take_drop_disjoint r (j' * L) a b

theorem mem_interval {lo n q : ℕ} : q ∈ (Reg.interval lo n).qubits ↔ lo ≤ q ∧ q < lo + n := by
  simp only [Reg.interval, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · intro h; exact ⟨q - lo, by omega, by omega⟩

theorem wMax_initW_ge (C L k : ℕ) (i : Fin k) :
    (if (i : ℕ) + 1 = k then C - (k - 1) * L else L) ≤ wMax (initW C L k) := by
  have h := get_le_wMax (initW C L k) i
  have e : wget (initW C L k) i = (if (i : ℕ) + 1 = k then C - (k - 1) * L else L) := by
    simp [wget, initW, List.getD_eq_getElem?_getD]
  rw [e] at h
  exact h

theorem wMax_le_scanMax {k : ℕ} (w : Widths) (ops : Prog k) : wMax w ≤ scanMax w ops := by
  cases ops with
  | nil => exact le_rfl
  | cons op ops => exact le_max_left _ _

/-- The child width exceeds every initial limb width. -/
theorem limb_lt_childWidth {k : ℕ} (C : ℕ) (ops : Prog k) (i : Fin k) :
    (if (i : ℕ) + 1 = k then C - (k - 1) * (C / k) else C / k) < childWidth C ops := by
  have h1 := wMax_initW_ge C (C / k) k i
  have h2 := wMax_le_scanMax (initW C (C / k) k) ops
  have hW : limbWidth3 (fun _ => C) k = C / k := by simp [limbWidth3]
  simp only [childWidth, childWidth3, hW]
  omega

/-! ## The construction -/


/-- Extension size of child slot `(s, j)`. -/
def extOf (C C' k : ℕ) (j : Fin k) : ℕ :=
  C' - (if (j : ℕ) + 1 = k then C - (k - 1) * (C / k) else C / k)

/-- Index of slot `(s, j)` in the reserve. -/
def slotIdx (k : ℕ) (s : Fin 3) (j : Fin k) : ℕ := (s : ℕ) * k + j

theorem slotIdx_lt {k : ℕ} (s : Fin 3) (j : Fin k) : slotIdx k s j < 3 * k := by
  unfold slotIdx
  have := s.2; have := j.2
  nlinarith

theorem slotIdx_inj {k : ℕ} {s s' : Fin 3} {j j' : Fin k} (h : slotIdx k s j = slotIdx k s' j') :
    s = s' ∧ j = j' := by
  unfold slotIdx at h
  have hj := j.2; have hj' := j'.2
  have hs : (s : ℕ) = s' := by
    have e1 : ((s : ℕ) * k + j) / k = s := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, zero_add]
    have e2 : ((s' : ℕ) * k + j') / k = s' := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj', zero_add]
    rw [← e1, ← e2, h]
  refine ⟨Fin.ext hs, Fin.ext ?_⟩
  rw [hs] at h; omega

/-- The pre-growth chunk register of slot `(s, j)`, reserve at `base + idx · C'`. -/
def preOf (X : Fin 3 → ExtReg) (C base C' k : ℕ) (hG : Good X C base) (s : Fin 3) (j : Fin k) : ExtReg :=
  ExtReg.withReserve (chunkReg (X s).active k ((X s).width / k) j)
    (Reg.interval (base + slotIdx k s j * C') (extOf C C' k j)) (by
      intro q h1 h2
      have := hG.2.2 s q (mem_chunkReg h1)
      have := (mem_interval.mp h2).1
      omega)

theorem mem_grow_preOf {X : Fin 3 → ExtReg} {C base C' k : ℕ} {hG : Good X C base} {s : Fin 3}
    {j : Fin k} {q : ℕ}
    (h : q ∈ ((preOf X C base C' k hG s j).grow (extOf C C' k j)).active.qubits) :
    q ∈ (chunkReg (X s).active k ((X s).width / k) j).qubits ∨
      (base + slotIdx k s j * C' ≤ q ∧ q < base + slotIdx k s j * C' + extOf C C' k j) := by
  simp only [ExtReg.grow, Reg.append, List.mem_append] at h
  rcases h with h | h
  · exact Or.inl h
  · right
    have := List.mem_of_mem_take h
    exact mem_interval.mp this

theorem idx_of_range {base i C' e q : ℕ} (he : e ≤ C') (h : base + i * C' ≤ q ∧ q < base + i * C' + e) :
    (q - base) / C' = i := by
  apply Nat.div_eq_of_lt_le
  · have := h.1; omega
  · have := h.2; rw [Nat.add_mul, one_mul]; omega

/-- **The split layout** of `X` at a node (width `C`, child width `C'`). -/
def mkSplit (X : Fin 3 → ExtReg) (C base : ℕ) (T : PTPTable) (hk : 2 ≤ T.k) (hG : Good X C base)
    (_hC : 0 < C) : SplitLayout X T.k (childWidth C T.ops) where
  pre := preOf X C base (childWidth C T.ops) T.k hG
  ext s j := extOf C (childWidth C T.ops) T.k j
  two_le := hk
  pre_active s j := rfl
  can_grow s j := by
    simp [ExtReg.CanGrow, ExtReg.capacity, preOf, ExtReg.withReserve, Reg.interval, regSize,
      Reg.width]
  ext_width s j := by
    have hXs : regSize (X s).active = C := hG.1 s
    have hw : (X s).width = C := hG.1 s
    have hlt := limb_lt_childWidth C T.ops j
    show regSize (chunkReg (X s).active T.k ((X s).width / T.k) j) + extOf C _ T.k j = _
    rw [hw]
    by_cases hj : (j : ℕ) + 1 = T.k
    · have hlen := chunkReg_length (X s).active T.k (C / T.k) j (Or.inr hj)
      simp only [hj, ↓reduceIte] at hlen; rw [hXs] at hlen
      have hjk : (j : ℕ) = T.k - 1 := by omega
      rw [hjk] at hlen
      simp only [regSize, Reg.width] at hlen ⊢
      rw [hlen]
      unfold extOf
      simp only [hj, ↓reduceIte] at hlt ⊢
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
      unfold extOf
      simp only [hj, ↓reduceIte] at hlt ⊢
      omega
  ext_pos s j hj := by
    have hlt := limb_lt_childWidth C T.ops j
    unfold extOf
    simp only [hj, ↓reduceIte] at hlt ⊢
    omega
  disjoint := by
    intro s j s' j' hne q h1 h2
    have hext : ∀ j : Fin T.k, extOf C (childWidth C T.ops) T.k j ≤ childWidth C T.ops :=
      fun _ => Nat.sub_le _ _
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


theorem mem_R_mkSplit {X : Fin 3 → ExtReg} {C base : ℕ} {T : PTPTable} {hk : 2 ≤ T.k}
    {hG : Good X C base} {hC : 0 < C} {q : ℕ} (h : q ∈ (mkSplit X C base T hk hG hC).R) :
    base ≤ q ∧ q < base + 3 * T.k * childWidth C T.ops := by
  simp only [SplitLayout.R, List.mem_flatMap, List.mem_finRange, true_and] at h
  obtain ⟨s, j, hq⟩ := h
  have hq' := mem_interval.mp (List.mem_of_mem_take hq)
  have hi := slotIdx_lt s j
  have he : extOf C (childWidth C T.ops) T.k j ≤ childWidth C T.ops := Nat.sub_le _ _
  have : (slotIdx T.k s j + 1) * childWidth C T.ops ≤ 3 * T.k * childWidth C T.ops :=
    Nat.mul_le_mul_right _ hi
  constructor
  · exact le_trans (Nat.le_add_right _ _) hq'.1
  · have h2 := hq'.2
    rw [Nat.add_mul, one_mul] at this
    omega

theorem slot_lt_mkSplit {X : Fin 3 → ExtReg} {C base : ℕ} {T : PTPTable} {hk : 2 ≤ T.k}
    {hG : Good X C base} {hC : 0 < C} (s : Fin 3) (j : Fin T.k) {q : ℕ}
    (h : q ∈ ((mkSplit X C base T hk hG hC).lay.slot s j).active.qubits) :
    q < base + 3 * T.k * childWidth C T.ops := by
  rcases mem_grow_preOf (hG := hG) (C' := childWidth C T.ops) h with c | r
  · have := hG.2.2 s q (mem_chunkReg c); omega
  · have hi := slotIdx_lt s j
    have he : extOf C (childWidth C T.ops) T.k j ≤ childWidth C T.ops := Nat.sub_le _ _
    have : (slotIdx T.k s j + 1) * childWidth C T.ops ≤ 3 * T.k * childWidth C T.ops :=
      Nat.mul_le_mul_right _ hi
    rw [Nat.add_mul, one_mul] at this
    omega

/-- Workspace of the construction along the ladder: `3 k C'` extension qubits per level
(slot `(s, j)` gets a `C'`-spaced block, of which `C' - |chunk|` are used) plus the two
leaf ancillas; children at a level share one pool. -/
def ptpWorkspace (P : PTPPolicy) (n : ℕ) : ℕ :=
  match P.choose n with
  | none => 2
  | some T =>
      if _h : childWidth n T.ops < n then 3 * T.k * childWidth n T.ops + ptpWorkspace P (childWidth n T.ops)
      else 2
termination_by n

/-- **O2 (existence).** For a checked policy `P`, every width `C` and every three pairwise
disjoint `C`-qubit registers below `base`, there is a gate-level PTP recursion following
`P` whose workspace lies in `[base, base + ptpWorkspace P C)`. -/
theorem exists_policyImpl (P : PTPPolicy) (hP : P.check = true) :
    ∀ (C : ℕ) (X : Fin 3 → ExtReg) (base : ℕ), Good X C base →
      ∃ (W : List ℕ) (G : Angle → LowGate),
        PolicyImpl P X C W G ∧ ∀ q ∈ W, base ≤ q ∧ q < base + ptpWorkspace P C := by
  intro C
  induction C using Nat.strong_induction_on with
  | _ C ih =>
  intro X base hG
  by_cases hnode : ∃ T, P.choose C = some T ∧ childWidth C T.ops < C
  · obtain ⟨T, hc, hlt⟩ := hnode
    obtain ⟨b, hb, rfl⟩ := PTPPolicy.choose_mem hc
    have hk : 2 ≤ b.table.k :=
      ((PTPTable.contract_iff b.table).mp (PTPPolicy.check_tables hP b hb)).1
    have hC : 0 < C := by omega
    set T := b.table
    set SL := mkSplit X C base T hk hG hC
    have hgood : ∀ j, Good (fun s => SL.lay.slot s j) (childWidth C T.ops) (base + 3 * T.k * childWidth C T.ops) := by
      intro j
      refine ⟨fun s => SL.lay.slot_width s j, fun s s' hs => SL.disjoint s j s' j (by
        intro e; exact hs (Prod.mk.inj e).1), fun s q hq => slot_lt_mkSplit s j hq⟩
    have hex := fun j => ih (childWidth C T.ops) hlt (fun s => SL.lay.slot s j) (base + 3 * T.k * childWidth C T.ops) (hgood j)
    choose Wc Gc hImpl hBound using hex
    have hn : ptpWorkspace P C = 3 * T.k * childWidth C T.ops + ptpWorkspace P (childWidth C T.ops) := by
      rw [ptpWorkspace, hc]
      simp only [hlt, ↓reduceDIte]
    refine ⟨SL.R ++ List.range' (base + 3 * T.k * childWidth C T.ops) (ptpWorkspace P (childWidth C T.ops)), _,
      PolicyImpl.node X C T hG.1 hC hc hlt SL Gc
        (List.range' (base + 3 * T.k * childWidth C T.ops) (ptpWorkspace P (childWidth C T.ops))) Wc ?_ ?_
        hImpl, ?_⟩
    · intro j q hq
      have := hBound j q hq
      rw [List.mem_range'_1]; omega
    · intro q hq s j hs
      rw [List.mem_range'_1] at hq
      have := slot_lt_mkSplit s j hs
      omega
    · intro q hq
      rw [hn]
      rcases List.mem_append.mp hq with hq | hq
      · have := mem_R_mkSplit hq; omega
      · rw [List.mem_range'_1] at hq; omega
  · push Not at hnode
    have hstop : ∀ T, P.choose C = some T → C ≤ childWidth C T.ops := fun T hT => hnode T hT
    have hD : LeafActiveDisjoint (X 0) (X 1) (X 2) :=
      ⟨hG.2.1 0 1 (by decide), hG.2.1 0 2 (by decide), hG.2.1 1 2 (by decide)⟩
    have hoff : ∀ s, ∀ q, base ≤ q → q ∉ (X s).active.qubits := fun s q hq hm => by
      have := hG.2.2 s q hm; omega
    have hA : SandwichAnc (X 0) (X 1) (X 2) base (base + 1) :=
      ⟨by omega, hoff 0 _ le_rfl, hoff 1 _ le_rfl, hoff 2 _ le_rfl, hoff 0 _ (by omega),
        hoff 1 _ (by omega), hoff 2 _ (by omega)⟩
    have hw : ptpWorkspace P C = 2 := by
      rw [ptpWorkspace]
      rcases hcC : P.choose C with _ | T
      · rfl
      · simp only [Nat.not_lt.mpr (hstop T hcC), ↓reduceDIte]
    refine ⟨[base, base + 1], _, PolicyImpl.leaf X C base (base + 1) hG.1 hstop hD hA, ?_⟩
    rw [hw]
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    omega

/-- **O2: gate-level correctness and census of PTP through the full recursion.** For a
checked policy `P`, every width `n` and every three pairwise disjoint `n`-qubit registers
below `base`, there is a circuit family `G` following `P` with workspace `W ⊆ [base, …)`
such that, for every angle `φ`: on every basis state whose registers fit signed `n` bits and
whose workspace is `|0⟩`, `G φ` multiplies by `exp(i π φ ⟦X 0⟧⟦X 1⟧⟦X 2⟧)` and returns the
state; and its Rz, Toffoli, X and H counts (ForShor `shorGateResourceModel`) are exactly
`ptpResources P n`. -/
theorem ptp_gate_correct {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
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
          R.x = (ptpResources P n).x ∧ R.h = (ptpResources P n).h) := by
  obtain ⟨W, G, hI, hB⟩ := exists_policyImpl P hP n X base hG
  exact ⟨W, G, hI, hB, fun φ b hfit hcl => evalL_policyImpl_ket hP hI φ b hfit hcl,
    fun φ => hI.resources φ⟩

end PTP
end Shor
