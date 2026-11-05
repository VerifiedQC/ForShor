import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Statement
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Recursion.Recursion
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Values.Exact
/-!
# O5: gate-level PTP node at EXACT widths

The gate-level node theorems of `Node.lean` / `Recursion.lean` assume the working width is at
least the PTP scan (`childWidth n T.ops ≤ Lay.width`). Here the hypothesis is weakened to the
exact width, `ptpTightWidth T n ≤ Lay.width` (`Exact.lean`), and the scan versions are
recovered as corollaries (`tight_le_childWidth`).

What the layout needs (the "floor"). ForShor's PhaseProduct allocation grows every slot by at
least one bit, so its compiler width is `max tight floor`. The PTP split (`SplitLayout`)
needs `ext > 0` only for the zero-extended LOWER chunks (`C' ≥ n/k + 1`); the sign-extended
top chunk only needs `C' ≥ topWidth` (`ext = 0` allowed). Both are implied by the exact width,
because the initial limbs are themselves reachable register values (the start state is in
`reachRows`): `lower_lt_tight`, `top_le_tight`, `floor_le_tight`. So `exactWidth T n :=
max (ptpTightWidth T n) (ptpFloor T.k n) = ptpTightWidth T n` (`exactWidth_eq`): no floor term.

* `body_eval_genF`: body simulation under `AllFits` (signed fit, `-2^(C-1)` allowed) instead of
  `AllBounded (C-1)` (strict magnitude), which the exact width needs: the exact width is
  defined by signed fit.
* `evalL_nodeBody_ket_exact`, `evalL_ptpNode_ket_exact`, `evalL_ptpNodeCCPhase_ket_exact`:
  one node, any width ≥ exact.
* `specOn_ptpSubNode_exact`: the O2 step at any width ≥ exact.
* `*_scan`: the original statements re-derived from the exact ones.
-/

namespace Shor
namespace PTP

open Shor Operations

/-! ## The layout floor is implied by the exact width -/

theorem mem_traceVals_head {k : ℕ} (V : Vals k) (ops : Prog k) (j : Fin k) :
    V j ∈ traceVals V ops := by
  cases ops <;> simp [traceVals, List.mem_ofFn]

/-- Lower limbs are zero-extended: one bit above `n / k` is needed, and the exact width has it. -/
theorem lower_lt_tight (T : PTPTable) (hT : T.contract = true) (n : ℕ) :
    n / T.k < ptpTightWidth T n := by
  obtain ⟨hk2, _, _⟩ := (PTPTable.contract_iff T).mp hT
  have hk : 0 < T.k := by omega
  have hpos := ptpTightWidth_pos T n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using hpos
  obtain ⟨x, hx, hl⟩ := box_surj hk hn (fun j => limbHi T.k n j)
    (fun j => ⟨limbLo_le_limbHi n j, le_rfl⟩)
  have hmem : limbsAt T.k (limbWidth n T.k) x ⟨0, hk⟩ ∈ opTrace T n x :=
    mem_traceVals_head _ _ _
  have hf := tight_fits T hT le_rfl x hx _ hmem
  rw [limbWidth_eq, hl] at hf
  have hj : ¬ ((⟨0, hk⟩ : Fin T.k).val + 1 = T.k) := by simp; omega
  simp only [limbHi, hj, ↓reduceIte] at hf
  obtain ⟨-, -, h2⟩ := hf
  unfold signedMax at h2
  push_cast at h2
  have h3 : (2 : ℤ) ^ (n / T.k) ≤ 2 ^ (ptpTightWidth T n - 1) := Int.sub_one_lt_iff.mp h2
  have h4 : n / T.k ≤ ptpTightWidth T n - 1 := by
    by_contra hc
    push Not at hc
    have := pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hc
    linarith
  omega

/-- The top limb is sign-extended: `topWidth` bits are needed, and the exact width has them. -/
theorem top_le_tight (T : PTPTable) (hT : T.contract = true) (n : ℕ) :
    topWidth T.k n ≤ ptpTightWidth T n := by
  obtain ⟨hk2, _, _⟩ := (PTPTable.contract_iff T).mp hT
  have hk : 0 < T.k := by omega
  have hpos := ptpTightWidth_pos T n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [topWidth]
  obtain ⟨x, hx, hl⟩ := box_surj hk hn (fun j => limbLo T.k n j)
    (fun j => ⟨le_rfl, limbLo_le_limbHi n j⟩)
  have hmem : limbsAt T.k (limbWidth n T.k) x ⟨T.k - 1, by omega⟩ ∈ opTrace T n x :=
    mem_traceVals_head _ _ _
  have hf := tight_fits T hT le_rfl x hx _ hmem
  rw [limbWidth_eq, hl] at hf
  have hj : (⟨T.k - 1, by omega⟩ : Fin T.k).val + 1 = T.k := by simp; omega
  simp only [limbLo, hj, ↓reduceIte] at hf
  obtain ⟨-, h1, -⟩ := hf
  unfold signedMin at h1
  push_cast at h1
  have h3 : (2 : ℤ) ^ (topWidth T.k n - 1) ≤ 2 ^ (ptpTightWidth T n - 1) := by linarith
  have h4 : topWidth T.k n - 1 ≤ ptpTightWidth T n - 1 := by
    by_contra hc
    push Not at hc
    have := pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hc
    linarith
  have ht : 0 < topWidth T.k n := by unfold topWidth; have := top_offset_lt hk hn; omega
  omega

/-- The width the in-place split needs at parent width `n`: lower chunks zero-extended by at
least one bit, the top chunk at least its own width. -/
def ptpFloor (k n : ℕ) : ℕ := max (n / k + 1) (topWidth k n)

theorem floor_le_tight (T : PTPTable) (hT : T.contract = true) (n : ℕ) :
    ptpFloor T.k n ≤ ptpTightWidth T n :=
  max_le (lower_lt_tight T hT n) (top_le_tight T hT n)

/-- The PTP analogue of ForShor's compiler width `max tight floor`. -/
def exactWidth (T : PTPTable) (n : ℕ) : ℕ := max (ptpTightWidth T n) (ptpFloor T.k n)

/-- **No floor term**: for a table passing the contract, the exact width already meets the
layout floor, so `exactWidth = ptpTightWidth` at every `n`. -/
theorem exactWidth_eq (T : PTPTable) (hT : T.contract = true) (n : ℕ) :
    exactWidth T n = ptpTightWidth T n :=
  max_eq_left (floor_le_tight T hT n)

/-! ## Body simulation under signed fit -/

theorem AllFits.headF {k : ℕ} {C : ℕ} {V : Vals k} {ops : Prog k} (h : AllFits C V ops) :
    ∀ i, FitsSignedWidth C (V i) := by
  cases ops with
  | nil => exact h
  | cons _ _ => exact h.1

/-- `opBasis_inv` with the new values given as signed fits. -/
theorem opBasis_invF {k : ℕ} {Basis : Type*} [RegEncoding Basis] (Lay : NodeLayout k)
    {b0 b : Basis} {V : Files k} (hI : Inv Lay b0 b V) (s : Fin 3)
    (op : valid_ops k) (hfit : ∀ j, FitsSignedWidth Lay.width (vStepF id (V s) op j))
    (hex : ShiftExact (V s) op) (hok : opOK? op = true) :
    Inv Lay b0 (opBasis Lay s b op) (updF V s (vStepF id (V s) op)) := by
  obtain ⟨hval, hbit⟩ := hI
  have hfits : ∀ j, FitsSignedWidth (Lay.slot s j).width (vStepF id (V s) op j) := by
    intro j; rw [Lay.slot_width]; exact hfit j
  have hdst : extToInt (Lay.slot s (dstOf op)) (opBasis Lay s b op) =
      vStepF id (V s) op (dstOf op) := by
    have hf := hfits (dstOf op)
    cases op with
    | shiftL i n =>
        simp only [opBasis, dstOf] at hf ⊢
        simp only [vStepF, upd, id] at hf ⊢
        rw [mul_comm] at hf ⊢
        rw [← hval s i] at hf ⊢
        exact extToInt_shiftLBasis_of_fits _ _ _ hf
    | shiftR i n =>
        simp only [opBasis, dstOf] at hf ⊢
        simp only [vStepF, upd, id] at hf ⊢
        apply extToInt_shiftRBasis_of_exact _ _ _ _ _ hf
        rw [hval s i]
        exact (Int.mul_ediv_cancel' hex).symm
    | negate i =>
        simp only [opBasis, dstOf] at hf ⊢
        simp only [vStepF, upd, id] at hf ⊢
        rw [extToInt_negateBasis, hval s i]
        rw [← hval s i] at hf
        rw [hval s i] at hf
        exact tcWrapInt_eq_of_fits hf.1 (by rw [Lay.slot_width] at hf ⊢; exact hf)
    | addScaled d src neg sh =>
        simp only [opBasis, dstOf] at hf ⊢
        simp only [vStepF, upd, id] at hf ⊢
        have hne : d ≠ src := by simpa [opOK?] using hok
        have hds : ExtReg.ActiveDisjoint (Lay.slot s d) (Lay.slot s src) :=
          Lay.disjoint s d s src (by simp [hne])
        rw [extToInt_addScaledBasis_dst _ _ _ _ _ hds]
        have hv : addScaledValue (Lay.slot s d) (Lay.slot s src) neg sh b =
            V s d + (if neg then -1 else 1) * V s src * 2 ^ sh := by
          simp only [addScaledValue, hval]; ring
        rw [hv]
        exact tcWrapInt_eq_of_fits hf.1 hf
    | phaseProduct i => simp [opBasis, dstOf, vStepF, hval]
  have hother : ∀ s' i', (s', i') ≠ (s, dstOf op) →
      extToInt (Lay.slot s' i') (opBasis Lay s b op) = extToInt (Lay.slot s' i') b := by
    intro s' i' hne
    have hd : ExtReg.ActiveDisjoint (Lay.slot s' i') (Lay.slot s (dstOf op)) :=
      Lay.disjoint s' i' s (dstOf op) hne
    cases op with
    | shiftL i n => exact extToInt_shiftLBasis_of_activeDisjoint _ _ _ _ hd
    | shiftR i n => exact extToInt_shiftRBasis_of_activeDisjoint _ _ _ _ hd
    | negate i => exact extToInt_negateBasis_of_activeDisjoint _ _ _ hd
    | addScaled d src neg sh =>
        have hne' : d ≠ src := by simpa [opOK?] using hok
        exact extToInt_addScaledBasis_of_activeDisjoint _ _ _ _ _ _
          (Lay.disjoint s d s src (by simp [hne'])) hd
    | phaseProduct i => rfl
  refine ⟨?_, ?_⟩
  · intro s' i'
    by_cases h : (s', i') = (s, dstOf op)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      rw [hdst]; simp [updF]
    · rw [hother s' i' h, hval s' i']
      by_cases hs : s' = s
      · subst hs
        have hi : i' ≠ dstOf op := fun e => h (by rw [e])
        simp [updF, vStepF_ne (V s') op i' hi]
      · simp [updF, hs]
  · intro q hq
    have hq' : q ∉ (Lay.slot s (dstOf op)).active.qubits := hq s (dstOf op)
    rw [← hbit q hq]
    cases op with
    | shiftL i n => exact bit_shiftLBasis_out _ _ _ _ hq'
    | shiftR i n => exact bit_shiftRBasis_out _ _ _ _ hq'
    | negate i => exact bit_negateBasis_out _ _ _ hq'
    | addScaled d src neg sh => exact bit_addScaledBasis_out _ _ _ _ _ _ hq'
    | phaseProduct i => rfl

theorem opGates_stepF {k : ℕ} {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (Lay : NodeLayout k) {b0 b : qs.Basis} {V : Files k}
    (hI : Inv Lay b0 b V) (op : valid_ops k)
    (hfit : ∀ s j, FitsSignedWidth Lay.width (vStepF id (V s) op j))
    (hex : ∀ s, ShiftExact (V s) op) (hok : opOK? op = true) :
    ∃ b', LowerGateClass.evalL (qs := qs) (opGates Lay op) (qs.ket b) = qs.ket b' ∧
      Inv Lay b0 b' (fun s => vStepF id (V s) op) := by
  have h1 := opBasis_invF Lay hI 0 op (hfit 0) (hex 0) hok
  have h2 := opBasis_invF Lay h1 1 op (by simpa [updF] using hfit 1)
    (by simpa [updF] using hex 1) hok
  have h3 := opBasis_invF Lay h2 2 op (by simpa [updF] using hfit 2)
    (by simpa [updF] using hex 2) hok
  refine ⟨opBasis Lay 2 (opBasis Lay 1 (opBasis Lay 0 b op) op) op, ?_, ?_⟩
  · rw [opGates, LowerGateClass.evalL_seq, LowerGateClass.evalL_seq, evalL_opGate, evalL_opGate,
      evalL_opGate]
  · have e : updF (updF (updF V 0 (vStepF id (V 0) op)) 1
        (vStepF id ((updF V 0 (vStepF id (V 0) op)) 1) op)) 2
        (vStepF id ((updF (updF V 0 (vStepF id (V 0) op)) 1
          (vStepF id ((updF V 0 (vStepF id (V 0) op)) 1) op)) 2) op) =
        fun s => vStepF id (V s) op := by
      funext s
      fin_cases s <;> simp [updF]
    rw [← e]; exact h3

/-- **Body simulation under signed fit** (`body_eval_gen` with `AllFits` in place of
`AllBounded (C-1)`). -/
theorem body_eval_genF {k : ℕ} {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (Lay : NodeLayout k) (θ : ℕ → ℚ) (b0 : qs.Basis)
    (child : ℕ → Fin k → LowGate) (hchild : ChildSpec Lay θ b0 child) :
    ∀ (ops : Prog k) (t : ℕ) (V : Files k) (b : qs.Basis), Inv Lay b0 b V →
      (∀ s, AllFits Lay.width (V s) ops) → (∀ s, ExactShifts (V s) ops) →
      wellFormed? ops = true →
      ∃ b', LowerGateClass.evalL (qs := qs) (body Lay child t ops) (qs.ket b) =
        Complex.exp (((Angle.toReal (bodyPhase θ t V ops) : ℝ) : ℂ) * Complex.I) • qs.ket b' ∧
        Inv Lay b0 b' (fun s => (runF id (V s) ops).2)
  | [], t, V, b, hI, _, _, _ => ⟨b, by simp [body, bodyPhase, LowerGateClass.evalL_id], by
      simpa [runF] using hI⟩
  | op :: ops, t, V, b, hI, hB, hX, hW => by
      have hok : opOK? op = true := by
        simp only [wellFormed?, Bool.and_eq_true] at hW; exact hW.1
      have hW' : wellFormed? ops = true := by
        simp only [wellFormed?, Bool.and_eq_true] at hW; exact hW.2
      have hB' : ∀ s, AllFits Lay.width (vStepF id (V s) op) ops := fun s => (hB s).2
      have hX' : ∀ s, ExactShifts (vStepF id (V s) op) ops := fun s => (hX s).2
      have hfit : ∀ s j, FitsSignedWidth Lay.width (vStepF id (V s) op j) :=
        fun s => (hB' s).headF
      cases op with
      | phaseProduct i =>
          have hB'' : ∀ s, AllFits Lay.width (V s) ops := fun s => (hB s).2
          have hX'' : ∀ s, ExactShifts (V s) ops := fun s => (hX s).2
          obtain ⟨b', he, hI'⟩ := body_eval_genF Lay θ b0 child hchild ops (t + 1) V b hI hB''
            hX'' hW'
          refine ⟨b', ?_, by simpa [runF] using hI'⟩
          have hpre : ∀ s, FitsSignedWidth Lay.width (extToInt (Lay.slot s i) b) := by
            intro s; rw [hI.1]; exact (hB s).1 i
          simp only [body, bodyPhase, LowerGateClass.evalL_seq]
          rw [hchild t i b hpre hI.2, hI.1, hI.1, hI.1, LowerGateClass.evalL_smul, he, smul_smul,
            ← Complex.exp_add, Angle.toReal_add]
          congr 2
          push_cast
          ring
      | shiftL i n =>
          obtain ⟨b1, he1, hI1⟩ := opGates_stepF Lay hI _ hfit (fun s => (hX s).1) hok
          obtain ⟨b', he, hI'⟩ := body_eval_genF Lay θ b0 child hchild ops t _ b1 hI1 hB' hX' hW'
          exact ⟨b', by simp only [body, bodyPhase, LowerGateClass.evalL_seq]; rw [he1, he], by
            simpa [runF] using hI'⟩
      | shiftR i n =>
          obtain ⟨b1, he1, hI1⟩ := opGates_stepF Lay hI _ hfit (fun s => (hX s).1) hok
          obtain ⟨b', he, hI'⟩ := body_eval_genF Lay θ b0 child hchild ops t _ b1 hI1 hB' hX' hW'
          exact ⟨b', by simp only [body, bodyPhase, LowerGateClass.evalL_seq]; rw [he1, he], by
            simpa [runF] using hI'⟩
      | negate i =>
          obtain ⟨b1, he1, hI1⟩ := opGates_stepF Lay hI _ hfit (fun s => (hX s).1) hok
          obtain ⟨b', he, hI'⟩ := body_eval_genF Lay θ b0 child hchild ops t _ b1 hI1 hB' hX' hW'
          exact ⟨b', by simp only [body, bodyPhase, LowerGateClass.evalL_seq]; rw [he1, he], by
            simpa [runF] using hI'⟩
      | addScaled d src neg sh =>
          obtain ⟨b1, he1, hI1⟩ := opGates_stepF Lay hI _ hfit (fun s => (hX s).1) hok
          obtain ⟨b', he, hI'⟩ := body_eval_genF Lay θ b0 child hchild ops t _ b1 hI1 hB' hX' hW'
          exact ⟨b', by simp only [body, bodyPhase, LowerGateClass.evalL_seq]; rw [he1, he], by
            simpa [runF] using hI'⟩

/-! ## One node at exact width -/

/-- **PTP node body correctness at any width ≥ exact (gate level, any children meeting
`ChildSpec`).** As `evalL_nodeBody_ket`, with `hC : ptpTightWidth T n ≤ Lay.width` in place of
`childWidth n T.ops ≤ Lay.width`. -/
theorem evalL_nodeBody_ket_exact {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (T : PTPTable) (hT : T.contract = true) (n : ℕ) (x : Fin 3 → ℤ)
    (hx : ∀ s, FitsSignedWidth n (x s)) (Lay : NodeLayout T.k)
    (hC : ptpTightWidth T n ≤ Lay.width) (φ : Angle) (b : qs.Basis)
    (hb : ∀ s i, extToInt (Lay.slot s i) b = limbsAt T.k (limbWidth n T.k) (x s) i)
    (child : ℕ → Fin T.k → LowGate) (hchild : ChildSpec Lay (fun t => φ * coeffN T n t) b child) :
    LowerGateClass.evalL (qs := qs) (body Lay child 0 T.ops) (qs.ket b) =
      Complex.exp (((Angle.toReal φ : ℝ) : ℂ) * Complex.I *
        (((x 0 : ℤ) : ℂ) * ((x 1 : ℤ) : ℂ) * ((x 2 : ℤ) : ℂ))) • qs.ket b := by
  obtain ⟨hk, _, hsafe⟩ := (PTPTable.contract_iff T).mp hT
  set L : Files T.k := fun s => limbsAt T.k (limbWidth n T.k) (x s) with hL
  have hn : ∀ s : Fin 3, 0 < (fun _ => n) s := fun s => (hx s).1
  have hws := fun s => node_width_sound T hT (fun _ => n) hn x hx s
  have hrun := (returnsToStartCheck_iff T.ops State.start_state).mp
    hsafe.returns_start
  -- every register value along the run fits the exact width (Exact.lean `tight_fits`)
  have hB : ∀ s, AllFits Lay.width (L s) T.ops := fun s =>
    (allFits_iff Lay.width T.ops (L s)).mpr (tight_fits T hT hC (x s) (hx s))
  have hX : ∀ s, ExactShifts (L s) T.ops := by
    intro s
    obtain ⟨hex, _⟩ := run_val (L s) T.ops State.start_state State.start_state hrun
    rwa [valOf_start] at hex
  have hI0 : Inv Lay b b L := ⟨fun s i => hb s i, fun _ _ => rfl⟩
  obtain ⟨b', he, hI'⟩ := body_eval_genF Lay (fun t => φ * coeffN T n t) b child hchild
    T.ops 0 L b hI0 hB hX hsafe.safe_add
  have hfin : (fun s => (runF id (L s) T.ops).2) = L := by
    funext s; exact (hws s).2.2.2.2
  rw [hfin] at hI'
  have hb' : b' = b := inv_unique Lay hI' hI0
  rw [he, hb']
  congr 2
  rw [bodyPhase_eq]
  have hlen : cpCount T.ops = T.pts.length := by
    rw [← cpCount_eq_length id T.ops (L 0)]
    exact (congrArg List.length (children_eq T hT n (x 0))).trans (by simp)
  rw [hlen, ← Fin.sum_univ_eq_sum_range (fun j => φ * coeffN T n (0 + j) *
      ((runF id (L 0) T.ops).1.getD j 0 : ℚ) * ((runF id (L 1) T.ops).1.getD j 0 : ℚ) *
      ((runF id (L 2) T.ops).1.getD j 0 : ℚ))]
  have key := node_identity T hT n φ x
  have hsum : (∑ j : Fin T.pts.length, φ * coeffN T n (0 + (j : ℕ)) *
      ((runF id (L 0) T.ops).1.getD j 0 : ℚ) * ((runF id (L 1) T.ops).1.getD j 0 : ℚ) *
      ((runF id (L 2) T.ops).1.getD j 0 : ℚ)) = φ * x 0 * x 1 * x 2 := by
    rw [← key]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hcj : coeffN T n (0 + (j : ℕ)) = T.coeff n j := by
      simp [coeffN, j.2]
    rw [hcj, Fin.prod_univ_three]
    have h0 := children_getD T hT n (x 0) j
    have h1 := children_getD T hT n (x 1) j
    have h2 := children_getD T hT n (x 2) j
    simp only [PTPTable.children] at h0 h1 h2
    simp only [hL, h0, h1, h2]
    ring
  rw [hsum]
  simp only [Angle.toReal]
  push_cast
  ring

/-- **PTP node correctness at any width ≥ exact (gate level, sandwich-leaf children).** -/
theorem evalL_ptpNode_ket_exact {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (T : PTPTable) (hT : T.contract = true) (n : ℕ) (x : Fin 3 → ℤ)
    (hx : ∀ s, FitsSignedWidth n (x s)) (Lay : NodeLayout T.k)
    (hC : ptpTightWidth T n ≤ Lay.width) (φ : Angle) (ta ua : ℕ) (hA : NodeAnc Lay ta ua)
    (b : qs.Basis) (hclean : AncClean ta ua b)
    (hb : ∀ s i, extToInt (Lay.slot s i) b = limbsAt T.k (limbWidth n T.k) (x s) i) :
    LowerGateClass.evalL (qs := qs) (ptpNode T Lay n φ ta ua) (qs.ket b) =
      Complex.exp (((Angle.toReal φ : ℝ) : ℂ) * Complex.I *
        (((x 0 : ℤ) : ℂ) * ((x 1 : ℤ) : ℂ) * ((x 2 : ℤ) : ℂ))) • qs.ket b :=
  evalL_nodeBody_ket_exact T hT n x hx Lay hC φ b hb _
    (leafSandwich_childSpec Lay _ b ta ua hA hclean)

/-- CCPhase-leaf node at any width ≥ exact. -/
theorem evalL_ptpNodeCCPhase_ket_exact {qs : QSemantics} [RegEncoding qs.Basis]
    [LowerGateClass qs] (T : PTPTable) (hT : T.contract = true) (n : ℕ) (x : Fin 3 → ℤ)
    (hx : ∀ s, FitsSignedWidth n (x s)) (Lay : NodeLayout T.k)
    (hC : ptpTightWidth T n ≤ Lay.width) (φ : Angle) (b : qs.Basis)
    (hb : ∀ s i, extToInt (Lay.slot s i) b = limbsAt T.k (limbWidth n T.k) (x s) i) :
    LowerGateClass.evalL (qs := qs) (ptpNodeCCPhase T Lay n φ) (qs.ket b) =
      Complex.exp (((Angle.toReal φ : ℝ) : ℂ) * Complex.I *
        (((x 0 : ℤ) : ℂ) * ((x 1 : ℤ) : ℂ) * ((x 2 : ℤ) : ℂ))) • qs.ket b :=
  evalL_nodeBody_ket_exact T hT n x hx Lay hC φ b hb _ (leafCCPhase_childSpec Lay _ b)

/-- **Scan corollary**: `evalL_ptpNode_ket` (hypothesis `childWidth ≤ width`) follows from the
exact version, since `ptpTightWidth ≤ childWidth` (`tight_le_childWidth`). -/
theorem evalL_ptpNode_ket_scan {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]
    (T : PTPTable) (hT : T.contract = true) (n : ℕ) (x : Fin 3 → ℤ)
    (hx : ∀ s, FitsSignedWidth n (x s)) (Lay : NodeLayout T.k)
    (hC : childWidth n T.ops ≤ Lay.width) (φ : Angle) (ta ua : ℕ) (hA : NodeAnc Lay ta ua)
    (b : qs.Basis) (hclean : AncClean ta ua b)
    (hb : ∀ s i, extToInt (Lay.slot s i) b = limbsAt T.k (limbWidth n T.k) (x s) i) :
    LowerGateClass.evalL (qs := qs) (ptpNode T Lay n φ ta ua) (qs.ket b) =
      Complex.exp (((Angle.toReal φ : ℝ) : ℂ) * Complex.I *
        (((x 0 : ℤ) : ℂ) * ((x 1 : ℤ) : ℂ) * ((x 2 : ℤ) : ℂ))) • qs.ket b :=
  evalL_ptpNode_ket_exact T hT n x hx Lay
    (le_trans (tight_le_childWidth T hT (hx 0).1) hC) φ ta ua hA b hclean hb

/-! ## The O2 step at exact width -/

section Spec

variable {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]

/-- **O2 step at any child width ≥ exact.** As `specOn_ptpSubNode`, with
`ptpTightWidth T C ≤ C'` in place of `childWidth C T.ops ≤ C'`. (The layout facts the split
needs, `ext > 0` on lower chunks, are fields of `SplitLayout`; that such a layout exists at
`C' ≥ ptpTightWidth` is `floor_le_tight`, used in `ExactBuild.lean`.) -/
theorem specOn_ptpSubNode_exact {X : Fin 3 → ExtReg} {C C' : ℕ} (hX : ∀ s, (X s).width = C)
    (hC : 0 < C) (T : PTPTable) (hT : T.contract = true) (SL : SplitLayout X T.k C')
    (hCw : ptpTightWidth T C ≤ C') (θ : Angle) (gc : ℕ → Fin T.k → LowGate) (W' : List ℕ)
    (hW' : ∀ q ∈ W', ∀ s j, q ∉ (SL.lay.slot s j).active.qubits)
    (hgc : ∀ t j, SpecOn (qs := qs) (fun s => SL.lay.slot s j) C' W' (θ * coeffN T C t) (gc t j)) :
    SpecOn (qs := qs) X C (SL.R ++ W') θ (ptpSubNode T SL gc) := by
  intro b hfit hcl
  have hR : ∀ q ∈ SL.R, RegEncoding.bit q b = false := fun q hq => hcl q (by simp [hq])
  have hW'b : ∀ q ∈ W', RegEncoding.bit q b = false := fun q hq => hcl q (by simp [hq])
  set b1 := SL.allocBasis b with hb1
  have hW'R : ∀ q ∈ W', q ∉ SL.R := fun q hq hR' => by
    obtain ⟨s, j, hm⟩ := SL.R_sub_slots hR'
    exact hW' q hq s j hm
  have hW'1 : ∀ q ∈ W', RegEncoding.bit q b1 = false := fun q hq => by
    rw [hb1, SL.bit_allocBasis_out b (hW'R q hq)]; exact hW'b q hq
  have hchild : ChildSpec SL.lay (fun t => θ * coeffN T C t) b1 gc :=
    childSpec_of_specOn SL.lay _ b1 gc W' hW' hW'1 hgc
  have hbody := evalL_nodeBody_ket_exact (qs := qs) T hT C (fun s => extToInt (X s) b) hfit
    SL.lay hCw θ b1 (fun s j => SL.slot_value hX hC b hR s j) gc hchild
  have hket : qs.ket b1 = LowerGateClass.evalL (qs := qs) SL.alloc (qs.ket b) :=
    (SL.evalL_alloc b).symm
  unfold ptpSubNode
  rw [LowerGateClass.evalL_seq, LowerGateClass.evalL_seq, SL.evalL_alloc, ← hb1, hbody,
    LowerGateClass.evalL_smul, hket, LowerGateClass.evalL_adj_apply]
  congr 2
  simp only [Angle.toReal]
  push_cast
  ring

/-- **Scan corollary** of `specOn_ptpSubNode_exact`: the original `specOn_ptpSubNode`. -/
theorem specOn_ptpSubNode_scan {X : Fin 3 → ExtReg} {C C' : ℕ} (hX : ∀ s, (X s).width = C)
    (hC : 0 < C) (T : PTPTable) (hT : T.contract = true) (SL : SplitLayout X T.k C')
    (hCw : childWidth C T.ops ≤ C') (θ : Angle) (gc : ℕ → Fin T.k → LowGate) (W' : List ℕ)
    (hW' : ∀ q ∈ W', ∀ s j, q ∉ (SL.lay.slot s j).active.qubits)
    (hgc : ∀ t j, SpecOn (qs := qs) (fun s => SL.lay.slot s j) C' W' (θ * coeffN T C t) (gc t j)) :
    SpecOn (qs := qs) X C (SL.R ++ W') θ (ptpSubNode T SL gc) :=
  specOn_ptpSubNode_exact hX hC T hT SL (le_trans (tight_le_childWidth T hT hC) hCw) θ gc W' hW' hgc

end Spec

end PTP
end Shor
