import ForShor.ShorVerification.Implementation.QubitCount.Proofs.Blocks

/-!
# Qubit count: one controlled modular multiplication

From a live set holding the control, the flag, and the active parts of the
data register (with its carry bit), the work register and the scratch
register, and none of their reserves, the five steps of
`CmodMulInPlaceCore` return to that set. Step 3 leaves the scratch register's
first reserve qubit live, and Step 4's first QFT releases it. The peak,
scratch included, is the start size plus `Rec.modMulPeak`.
-/

namespace Shor
namespace QubitCount

open Gate

variable {P : ShorLoweringPolicy} {pc : ℕ → ℕ → ℕ → ℕ → ℕ}

/-- The live set one multiplication starts from. -/
structure MulSpace (D W S : ExtReg) (flag ctrl : ℕ) (L : Finset ℕ) : Prop where
  ctrl_mem : ctrl ∈ L
  flag_mem : flag ∈ L
  data_live : regQubitSet (D.grow 1).active ⊆ L
  work_live : regQubitSet W.active ⊆ L
  scratch_live : regQubitSet S.active ⊆ L
  data_res : _root_.Disjoint L (regQubitSet (D.grow 1).reserve)
  work_res : _root_.Disjoint L (regQubitSet W.reserve)
  scratch_res : _root_.Disjoint L (regQubitSet S.reserve)
  data_work : _root_.Disjoint (regQubitSet (D.grow 1).reserve) (regQubitSet W.reserve)
  data_scratch : _root_.Disjoint (regQubitSet (D.grow 1).reserve) (regQubitSet S.reserve)
  work_scratch : _root_.Disjoint (regQubitSet W.reserve) (regQubitSet S.reserve)

namespace MulSpace

variable {D W S : ExtReg} {flag ctrl : ℕ} {L : Finset ℕ} (h : MulSpace D W S flag ctrl L)
include h

lemma data_active_live : regQubitSet D.active ⊆ L := by
  refine Finset.Subset.trans ?_ h.data_live
  rw [grow_active]; exact Finset.subset_union_left

lemma res_dw : _root_.Disjoint L (regQubitSet (D.grow 1).reserve ∪ regQubitSet W.reserve) :=
  Finset.disjoint_union_right.mpr ⟨h.data_res, h.work_res⟩

lemma res_wd : _root_.Disjoint L (regQubitSet W.reserve ∪ regQubitSet (D.grow 1).reserve) :=
  Finset.disjoint_union_right.mpr ⟨h.work_res, h.data_res⟩

lemma res_ws : _root_.Disjoint L (regQubitSet W.reserve ∪ regQubitSet S.reserve) :=
  Finset.disjoint_union_right.mpr ⟨h.work_res, h.scratch_res⟩

end MulSpace

/-! ## The spare capacities of the phase-product operands -/

section Caps

variable {D W : ExtReg} (hmod : ModMulCircuitWorkspaceOK D W)

lemma step1_xcap : regSize hmod.step1Workspace.xReserve - 1 = D.capacity - 2 := by
  show regSize (D.reserve.drop 1) - 1 = _
  simp only [regSize, Reg.width, Reg.drop, List.length_drop, ExtReg.capacity]
  omega

lemma step1_zcap : regSize hmod.step1Workspace.zReserve - 1 = W.capacity - 1 := rfl

lemma step2_xcap : regSize hmod.step2Workspace.xReserve - 1 = W.capacity - 1 := rfl

lemma step2_zcap : regSize hmod.step2Workspace.zReserve - 1 = D.capacity - 2 := by
  show (D.grow 1).capacity - 1 = _
  rw [ExtReg.capacity_grow D 1 (le_trans (by norm_num) hmod.1)]
  omega

lemma step5_xcap : regSize hmod.step5Workspace.xReserve - 1 = D.capacity - 2 := by
  show (D.grow 1).capacity - 1 = _
  rw [ExtReg.capacity_grow D 1 (le_trans (by norm_num) hmod.1)]
  omega

lemma step5_zcap : regSize hmod.step5Workspace.zReserve - 1 = W.capacity - 1 := rfl

end Caps

section Steps

variable {D W S : ExtReg} {flag ctrl : ℕ} {L : Finset ℕ}

lemma step1_fact (c N : ℕ) (hmod : ModMulCircuitWorkspaceOK D W) (h : MulSpace D W S flag ctrl L) :
    SFact P pc (step1 c N ctrl D W hmod) true L L
      (L.card + max (2 + pc (D.width + 1) (D.capacity - 2) (W.width + 1) (W.capacity - 1))
        (Rec.qftPeak P W.width)) := by
  have f1 := SFact.H_reg (P := P) (pc := pc) h.work_live true
  have f2 := SFact.cppUsing (P := P) (pc := pc) hmod.step1Workspace ctrl
    ((2 * (((c + N - 1) % N : ℕ) : ℚ)) / (N : ℚ)) h.ctrl_mem h.data_active_live h.work_live
    h.res_dw true
  rw [step1_xcap hmod, step1_zcap hmod] at f2
  have f3 : SFact P pc (IQFT hmod.step1Workspace.zExt) true L L
      (L.card + Rec.qftPeak P W.width) :=
    SFact.adj (SFact.qft (P := P) (pc := pc) (r := hmod.step1Workspace.zExt) h.work_live h.work_res false)
  exact (SFact.seq f1 (SFact.seq f2 f3)).congr_peak (by simp; rfl)

lemma step2_fact (N : ℕ) (hmod : ModMulCircuitWorkspaceOK D W) (h : MulSpace D W S flag ctrl L) :
    SFact P pc (step2 N D W hmod) true L L
      (L.card + max (Rec.qftPeak P (D.width + 1))
        (2 + pc (W.width + 1) (W.capacity - 1) (D.width + 2) (D.capacity - 2))) := by
  have hcap1 : D.CanGrow 1 := le_trans (by norm_num) hmod.1
  have hw1 : (D.grow 1).width = D.width + 1 := ExtReg.width_grow D 1 hcap1
  have f1 : SFact P pc (Gate.QFT hmod.step2Workspace.zExt) true L L
      (L.card + Rec.qftPeak P (D.width + 1)) := by
    rw [← hw1]; exact SFact.qft (P := P) (pc := pc) (r := hmod.step2Workspace.zExt) h.data_live h.data_res true
  have f2 := SFact.ppUsing (P := P) (pc := pc) hmod.step2Workspace
    ((2 * (N : ℚ)) / (2 : ℚ) ^ (regSize W.active + regSize (D.grow 1).active))
    h.work_live h.data_live h.res_wd true
  rw [step2_xcap hmod, step2_zcap hmod] at f2
  have f3 : SFact P pc (IQFT hmod.step2Workspace.zExt) true L L
      (L.card + Rec.qftPeak P (D.width + 1)) := by
    rw [← hw1]
    exact SFact.adj (SFact.qft (P := P) (pc := pc) (r := hmod.step2Workspace.zExt) h.data_live h.data_res false)
  have := SFact.seq f1 (SFact.seq f2 f3)
  refine this.congr_peak ?_
  have hr : regSize (D.grow 1).active + 1 = D.width + 2 := by
    rw [show regSize (D.grow 1).active = (D.grow 1).width from rfl, hw1]
  rw [hr, show regSize W.active = W.width from rfl]
  congr 1
  apply le_antisymm <;> simp only [max_le_iff, le_max_iff] <;> omega

lemma scratch_canGrow {N : ℕ} {D' : ExtReg} (hs4 : CmpLtNWWorkspace N D' W S flag) : S.CanGrow 1 := by
  have := hs4.mulWorkspace.z_can_grow
  rw [hs4.mul_zReserve_eq] at this
  exact this

lemma scratch_wide {N : ℕ} {D' : ExtReg} (hs4 : CmpLtNWWorkspace N D' W S flag) : 2 ≤ S.width := by
  have := hs4.scratch_width
  show 2 ≤ regSize S.active
  rw [this]; unfold cmpLtNWWidth; omega

lemma mulWs_zExt {N : ℕ} {D' : ExtReg} (hs4 : CmpLtNWWorkspace N D' W S flag) :
    hs4.mulWorkspace.zExt = S := by
  have h := hs4.mul_zReserve_eq
  rcases S with ⟨a, r, hd⟩
  simp only [Gate.PhaseProdWorkspace.zExt, ExtReg.withReserve] at h ⊢
  simp [h]

lemma step3_fact (N : ℕ) (hs4 : CmpLtNWWorkspace N (D.grow 1) W S flag)
    (h : MulSpace D W S flag ctrl L) :
    SFact P pc (step3 N (D.grow 1) S flag) true L (L ∪ allocBits S 1) (L.card + 3) := by
  have hSc := scratch_canGrow hs4
  have hbS : _root_.Disjoint (allocBits S 1) L :=
    Finset.disjoint_of_subset_left (allocBits_subset_reserve S 1) h.scratch_res.symm
  have hcard1 : (L ∪ allocBits S 1).card = L.card + 1 := by
    rw [Finset.card_union_of_disjoint hbS.symm, card_allocBits S hSc]
  have hbD : _root_.Disjoint (allocBits (D.grow 1) 1) (L ∪ allocBits S 1) := by
    have hsub := allocBits_subset_reserve (D.grow 1) 1
    exact Finset.disjoint_union_right.mpr
      ⟨Finset.disjoint_of_subset_left hsub h.data_res.symm,
       Finset.disjoint_of_subset_left hsub
        (Finset.disjoint_of_subset_right (allocBits_subset_reserve S 1) h.data_scratch)⟩
  have hw2 := scratch_wide hs4
  have f1 : SFact P pc (.CmpGeConst N (D.grow 1) S flag) true L (L ∪ allocBits S 1)
      (L.card + 3) :=
    ⟨⟨h.data_live, h.scratch_live, h.flag_mem, hbD⟩, rfl,
      by show (L ∪ allocBits S 1).card + 2 = _; rw [hcard1]⟩
  have hU : (L ∪ allocBits S 1) ∪ allocBits S 1 = L ∪ allocBits S 1 := by
    rw [Finset.union_assoc, Finset.union_self]
  have f2 : SFact P pc (.CSubConst N (D.grow 1) S flag) true (L ∪ allocBits S 1) (L ∪ allocBits S 1)
      (L.card + 2) :=
    ⟨⟨h.data_live.trans Finset.subset_union_left, h.scratch_live.trans Finset.subset_union_left,
      Finset.mem_union_left _ h.flag_mem⟩, hU, by
        show ((L ∪ allocBits S 1) ∪ allocBits S 1).card + 1 = _
        rw [hU, hcard1]⟩
  exact (SFact.seq f1 f2).congr_peak (by simp)

/-- The Step-4 difference, forwards and backwards. -/
lemma diff_facts (D' : ExtReg) (hcap : D'.CanGrow 1) (shift : ℕ)
    (hD' : regQubitSet D'.active ⊆ L) (hS : regQubitSet S.active ⊆ L)
    (hres : _root_.Disjoint L (regQubitSet D'.reserve)) :
    SFact P pc (Gate.zeroExtend D' 1 ;; Gate.Negate S ;; Gate.AddScaled S (D'.grow 1) false shift ;;
        Gate.zeroDealloc D' 1) true L L (L.card + 2) ∧
    SFact P pc (Gate.zeroExtend D' 1 ;; Gate.Negate S ;; Gate.AddScaled S (D'.grow 1) false shift ;;
        Gate.zeroDealloc D' 1) false L L (L.card + 2) := by
  have hb : _root_.Disjoint (allocBits D' 1) L :=
    Finset.disjoint_of_subset_left (allocBits_subset_reserve D' 1) hres.symm
  have hcard : (L ∪ allocBits D' 1).card = L.card + 1 := by
    rw [Finset.card_union_of_disjoint hb.symm, card_allocBits D' hcap]
  have hS' : regQubitSet S.active ⊆ L ∪ allocBits D' 1 := hS.trans Finset.subset_union_left
  have hG : regQubitSet (D'.grow 1).active ⊆ L ∪ allocBits D' 1 := by
    rw [grow_active]; exact Finset.union_subset_union hD' le_rfl
  have fN : ∀ d, SFact P pc (Gate.Negate S) d (L ∪ allocBits D' 1) (L ∪ allocBits D' 1)
      (L.card + (1 + 1)) :=
    fun d => (SFact.Negate (P := P) (pc := pc) hS' d).congr_peak (by rw [hcard, Nat.add_assoc])
  have fA : ∀ d, SFact P pc (Gate.AddScaled S (D'.grow 1) false shift) d (L ∪ allocBits D' 1)
      (L ∪ allocBits D' 1) (L.card + (1 + 1)) :=
    fun d => (SFact.AddScaled (P := P) (pc := pc) hS' hG d).congr_peak (by rw [hcard])
  constructor
  · have := SFact.seq (SFact.extend_fwd (P := P) (pc := pc) hb hcap rfl)
      (SFact.seq (fN true) (SFact.seq (fA true) (SFact.dealloc_fwd (P := P) (pc := pc) hb hcap rfl)))
    exact this.congr_peak (by omega)
  · have := SFact.seqB (SFact.seqB (SFact.seqB (SFact.dealloc_bwd (P := P) (pc := pc) hb hcap rfl) (fA false))
      (fN false)) (SFact.extend_bwd (P := P) (pc := pc) hb hcap rfl)
    exact this.congr_peak (by omega)

lemma step4_fact (N : ℕ) (hs4 : CmpLtNWWorkspace N (D.grow 1) W S flag)
    (h : MulSpace D W S flag ctrl L) :
    SFact P pc (step4 N (D.grow 1) W S flag hs4) true (L ∪ allocBits S 1) L
      (L.card + max (Rec.qftPeak P S.width)
        (max (2 + pc (W.width + 1) (W.capacity - 1) (S.width + 1) (S.capacity - 1))
          2)) := by
  have hz := mulWs_zExt hs4
  have hxr : regQubitSet hs4.mulWorkspace.xReserve = regQubitSet W.reserve := by
    rw [hs4.mul_xReserve_eq]
  have hzr : regQubitSet hs4.mulWorkspace.zReserve = regQubitSet S.reserve := by
    rw [hs4.mul_zReserve_eq]
  have hres : _root_.Disjoint L (regQubitSet hs4.mulWorkspace.xReserve ∪
      regQubitSet hs4.mulWorkspace.zReserve) := by
    rw [hxr, hzr]; exact h.res_ws
  have qPre : SFact P pc (.QFT hs4.mulWorkspace.zExt) true (L ∪ allocBits S 1) L
      (L.card + Rec.qftPeak P S.width) := by
    rw [hz]; exact SFact.qft_prelive (scratch_wide hs4) h.scratch_live h.scratch_res
  have qF : ∀ d, SFact P pc (.QFT hs4.mulWorkspace.zExt) d L L (L.card + Rec.qftPeak P S.width) := by
    intro d; rw [hz]; exact SFact.qft h.scratch_live h.scratch_res d
  have pp : ∀ (phi : Angle) d, SFact P pc (Gate.PhaseProdUsing phi W.active S.active hs4.mulWorkspace) d
      L L (L.card + (2 + pc (W.width + 1) (W.capacity - 1) (S.width + 1) (S.capacity - 1))) :=
    fun phi d => (SFact.ppUsing hs4.mulWorkspace phi h.work_live h.scratch_live hres d).congr_peak
      (by rw [hs4.mul_xReserve_eq, hs4.mul_zReserve_eq]; rfl)
  have hsign : ∀ hlt, cmpLtNWSignQubit S hlt ∈ L := fun hlt => by
    apply h.scratch_live; rw [mem_regQubitSet]; exact List.get_mem _ _
  obtain ⟨dF, dB⟩ := diff_facts (P := P) (pc := pc) (L := L) (D.grow 1) hs4.data_can_grow (regSize W.active)
    h.data_live h.scratch_live h.data_res
  unfold step4 cmpLtNW fastConstMulInto cmpLtNWDifference
  dsimp only
  have mulF := SFact.seq qPre (SFact.seq (pp ((2 * (N : ℚ)) / (ASize hs4.mulWorkspace.zExt.active : ℚ)) true)
    (SFact.adj (qF false)))
  have mulB := SFact.seqB (SFact.seqB (SFact.adj (P := P) (pc := pc) (d := false) (qF true))
    (pp ((2 * (N : ℚ)) / (ASize hs4.mulWorkspace.zExt.active : ℚ)) false)) (qF false)
  have := SFact.seq mulF (SFact.seq dF (SFact.seq (SFact.CNOT (hsign (lt_of_lt_of_le two_pos (scratch_wide hs4)))
    h.flag_mem true)
    (SFact.seq (SFact.adj dB) (SFact.adj mulB))))
  refine this.congr_peak ?_
  congr 1
  apply le_antisymm <;> simp only [max_le_iff, le_max_iff] <;> omega

lemma step5_fact (k5 N : ℕ) (hmod : ModMulCircuitWorkspaceOK D W) (h : MulSpace D W S flag ctrl L) :
    SFact P pc (step5 k5 N ctrl D W hmod) true L L
      (L.card + max (2 + pc (D.width + 2) (D.capacity - 2) (W.width + 1) (W.capacity - 1))
        (Rec.qftPeak P W.width)) := by
  have hcap1 : D.CanGrow 1 := le_trans (by norm_num) hmod.1
  have hw1 : regSize (D.grow 1).active + 1 = D.width + 2 := by
    rw [show regSize (D.grow 1).active = (D.grow 1).width from rfl, ExtReg.width_grow D 1 hcap1]
  have fH := SFact.H_reg (P := P) (pc := pc) h.work_live false
  have fC := SFact.cppUsing (P := P) (pc := pc) hmod.step5Workspace ctrl
    ((2 * ((k5 % N : ℕ) : ℚ)) / (N : ℚ)) h.ctrl_mem h.data_live h.work_live h.res_dw false
  rw [step5_xcap hmod, step5_zcap hmod] at fC
  have fQ : SFact P pc (IQFT hmod.step5Workspace.zExt) false L L (L.card + Rec.qftPeak P W.width) :=
    SFact.adj (P := P) (pc := pc) (d := false)
      (SFact.qft (P := P) (pc := pc) (r := hmod.step5Workspace.zExt) h.work_live h.work_res true)
  unfold step5
  have := SFact.adj (P := P) (pc := pc) (d := true) (SFact.seqB (SFact.seqB fQ fC) fH)
  refine this.congr_peak ?_
  rw [hw1, show regSize W.active = W.width from rfl]
  congr 1
  apply le_antisymm <;> simp only [max_le_iff, le_max_iff] <;> omega

lemma core_max (p1 qW qD p2 qS p4 p5 : ℕ) :
    max (max (2 + p1) qW) (max (max qD (2 + p2)) (max 3 (max (max qS (max (2 + p4) 2))
      (max (2 + p5) qW))))
    = max (2 + p1) (max qW (max qD (max (2 + p2) (max 3 (max qS (max (2 + p4)
      (max (2 + p5) 0))))))) := by
  apply le_antisymm
  · repeat' apply max_le
    all_goals simp only [le_max_iff] <;> omega
  · repeat' apply max_le
    all_goals simp only [le_max_iff] <;> omega

/-- One controlled modular multiplication returns to its start set, peaking
`modMulPeak` above it. -/
theorem core_fact (c N : ℕ) (hmod : ModMulCircuitWorkspaceOK D W)
    (hs4 : CmpLtNWWorkspace N (D.grow 1) W S flag) (h : MulSpace D W S flag ctrl L) :
    SFact P pc (CmodMulInPlaceCore c N ctrl D W S flag hmod hs4) true L L
      (L.card + Rec.modMulPeakWith P pc D.width D.capacity W.width W.capacity S.width
        S.capacity) := by
  unfold CmodMulInPlaceCore
  dsimp only
  have := SFact.seq (step1_fact (P := P) (pc := pc) c N hmod h)
    (SFact.seq (step2_fact (P := P) (pc := pc) N hmod h)
      (SFact.seq (step3_fact (P := P) (pc := pc) N hs4 h)
        (SFact.seq (step4_fact (P := P) (pc := pc) N hs4 h) (step5_fact (P := P) (pc := pc) (step5Constant c N) N hmod h))))
  refine this.congr_peak ?_
  simp only [Rec.modMulPeakWith, Rec.modMulPhasePeaksWith, List.foldr]
  congr 1
  exact core_max _ _ _ _ _ _ _

end Steps

end QubitCount
end Shor
