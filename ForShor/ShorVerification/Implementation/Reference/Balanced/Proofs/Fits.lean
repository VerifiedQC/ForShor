import ForShor.ShorVerification.Implementation.Reference.Balanced.Proofs.Correctness
import ForShor.ShorVerification.Implementation.Reference.Standard.Main

/-!
# Balanced phase products: fitting plans

The pass without the fit check is the guarded pass wherever every site's plan
fits (`balanceU_eq`), so it keeps the workspace and the semantics. The default
rule's blocks are well formed (`defaultPlan_wf`), so its plan fits whenever the
operands hold its `siteNeed` (`siteFits_of_siteNeed`), and the reference layout
holds it at every site of every instance (`reference_fits`).
-/

namespace Shor
namespace Balanced

open Reference

/-! ## The pass without the fit check is the guarded pass -/

theorem siteGateU_eq {P : ShorLoweringPolicy} {R : Rule} (c : Ctl) (φ : Angle) {x z : ExtReg}
    (h : SiteFits P R x z) : siteGateU R c φ x z = siteGate P R c φ x z := by
  unfold siteGateU siteGate SiteFits at *
  split_ifs at h ⊢ with h1 h2
  · cases hp : R.plan x.width z.width with
    | none => rfl
    | some p => simp [h p hp]
  · cases hp : R.plan z.width x.width with
    | none => rfl
    | some p => simp [h p hp]
  · rfl

theorem balanceU_eq {P : ShorLoweringPolicy} {R : Rule} :
    ∀ G : Gate, Fits P R G → balanceU R G = balance P R G
  | .seq U V, h => by
      simp only [balanceU, balance]
      rw [balanceU_eq U h.1, balanceU_eq V h.2]
  | .adj U, h => by
      simp only [balanceU, balance]
      rw [balanceU_eq U h]
  | .SignedPhaseProd φ x z, h => siteGateU_eq .none φ h
  | .CSignedPhaseProd q φ x z, h => siteGateU_eq (.ctrl q) φ h
  | .id, _ | .H _, _ | .X _, _ | .CNOT _ _, _ | .Toffoli _ _ _, _ | .QFT _, _
  | .RadixReverse _ _, _ | .CmpGeConst _ _ _ _, _ | .CSubConst _ _ _ _, _ | .ShiftL _ _, _
  | .ShiftR _ _, _ | .Negate _, _ | .AddScaled _ _ _ _, _ | .zeroExtend _ _, _
  | .signExtend _ _, _ | .zeroDealloc _ _, _ | .signDealloc _ _, _
  | .idealCtrlModMul _ _ _ _, _ => rfl

theorem balanceU_ok (P : ShorLoweringPolicy) (R : Rule) (G : Gate)
    (hw : Policy.GateWorkspaceOK P G) (hf : Fits P R G) :
    Policy.GateWorkspaceOK P (balanceU R G) := by
  rw [balanceU_eq G hf]
  exact balance_ok P R G hw

theorem lowerGate_congr (P : ShorLoweringPolicy) {g g' : Gate} (e : g = g')
    (hg : Policy.GateWorkspaceOK P g) (hg' : Policy.GateWorkspaceOK P g') :
    Policy.lowerGate P g hg = Policy.lowerGate P g' hg' := by
  subst e
  rfl

section Lowering

variable (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]

/-- **End-to-end lowering with the unconditional split.** Under the source
circuit's preconditions and `Fits`, `Policy.lowerGate` on `balanceU R G`
implements `G`. -/
theorem Policy.lowerGate_balanceU_correctness (P : ShorLoweringPolicy) (hP : P.Admissible)
    (R : Rule) (G : Gate) (hw : Policy.GateWorkspaceOK P G) (hf : Fits P R G) (ψ : qs.State)
    (hclean : Policy.GateWorkspaceCleanState qs P G hw ψ) :
    LowerGateClass.evalL (qs := qs) (Policy.lowerGate P (balanceU R G) (balanceU_ok P R G hw hf)) ψ
      = qs.eval G ψ := by
  rw [lowerGate_congr P (balanceU_eq G hf) (balanceU_ok P R G hw hf) (balance_ok P R G hw)]
  exact Policy.lowerGate_balance_correctness qs P hP R G hw ψ hclean

end Lowering

/-! ## Well-formed plans -/

/-- The width conditions of `fitsB`: every block is narrower than what is left of
the split operand, reads unsigned at its width, and covers the small operand. -/
def PlanWF : List Block → ℕ → ℕ → ℕ → Prop
  | [], t, xw, zw => xw ≤ t ∧ zw ≤ t
  | b :: bs, t, xw, zw => b.w < xw ∧ b.w + 1 ≤ b.t ∧ zw ≤ b.t ∧ PlanWF bs t (xw - b.w) zw

theorem planWF_replicate {w t zw : ℕ} (hw : w + 1 ≤ t) (hz : zw ≤ t) :
    ∀ (n xw : ℕ), (n * w < xw ∨ n = 0) → xw - n * w ≤ t →
      PlanWF (List.replicate n ⟨w, t⟩) t xw zw
  | 0, xw, _, htop => by simp only [List.replicate_zero, PlanWF]; exact ⟨by simpa using htop, hz⟩
  | n + 1, xw, hlt, htop => by
      simp only [List.replicate_succ, PlanWF]
      rw [Nat.succ_mul] at hlt htop
      refine ⟨by omega, hw, hz, planWF_replicate hw hz n (xw - w) ?_ ?_⟩ <;> omega

/-- **`defaultPlan`'s blocks are well formed** for every pair of widths it plans. -/
theorem defaultPlan_wf {L s : ℕ} {p : Plan} (h : defaultPlan L s = some p) :
    PlanWF p.lower p.top L s := by
  unfold defaultPlan at h
  split_ifs at h with h1 h2
  · cases h
    simp only [PlanWF]
    omega
  · cases h
    have hs : 2 ≤ s := by omega
    have hB : (L + s - 1) / s * s ≤ L + s - 1 := Nat.div_mul_le_self _ _
    have hB1 : 1 ≤ (L + s - 1) / s := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
    have hlt : ((L + s - 1) / s - 1) * (s - 1) < L := by
      have : ((L + s - 1) / s - 1) * (s - 1) ≤ ((L + s - 1) / s - 1) * s :=
        Nat.mul_le_mul_left _ (by omega)
      have : ((L + s - 1) / s - 1) * s = (L + s - 1) / s * s - s := by
        rw [Nat.sub_mul, one_mul]
      omega
    exact planWF_replicate (by omega) (by omega) _ _ (Or.inl hlt) (by omega)

/-- With the guard's width conditions known, `fitsB` reduces to its capacity
conditions. -/
theorem fitsB_iff_of_wf {P : ShorLoweringPolicy} :
    ∀ {bs : List Block} {t : ℕ} {x z : ExtReg}, PlanWF bs t x.width z.width →
      (fitsB P bs t x z = true ↔
        (∀ b ∈ bs, (b.t - b.w) + (Policy.reserveNeed P b.t b.t).1 ≤ x.capacity ∧
          (b.t - z.width) + (Policy.reserveNeed P b.t b.t).2 ≤ z.capacity) ∧
        (t - (x.width - (bs.map Block.w).sum)) + (Policy.reserveNeed P t t).1 ≤ x.capacity ∧
        (t - z.width) + (Policy.reserveNeed P t t).2 ≤ z.capacity)
  | [], t, x, z, hwf => by
      simp only [PlanWF] at hwf
      simp [fitsB_nil, hwf.1, hwf.2]
  | b :: bs, t, x, z, hwf => by
      obtain ⟨h1, h2, h3, hrest⟩ := hwf
      have hw : (highPart x b.w).width = x.width - b.w := highPart_width x b.w
      have hc : (highPart x b.w).capacity = x.capacity := rfl
      rw [← hw] at hrest
      rw [fitsB_cons, fitsB_iff_of_wf hrest, hw, hc]
      simp only [h1, h2, h3, true_and, List.forall_mem_cons, List.map_cons, List.sum_cons]
      constructor
      · rintro ⟨hx, hz, hb, htx, htz⟩
        exact ⟨⟨⟨hx, hz⟩, hb⟩, by rwa [Nat.sub_add_eq], htz⟩
      · rintro ⟨⟨⟨hx, hz⟩, hb⟩, htx, htz⟩
        exact ⟨hx, hz, hb, by rwa [Nat.sub_add_eq] at htx, htz⟩

/-- A plan with well-formed blocks fits operands that hold its `planNeed`. -/
theorem fitsB_of_planNeed {P : ShorLoweringPolicy} :
    ∀ {bs : List Block} {t : ℕ} {x z : ExtReg}, PlanWF bs t x.width z.width →
      (planNeed P bs t x.width z.width).1 ≤ x.capacity →
      (planNeed P bs t x.width z.width).2 ≤ z.capacity → fitsB P bs t x z = true
  | [], t, x, z, hwf, hx, hz => by
      simp only [PlanWF] at hwf
      simp only [planNeed] at hx hz
      exact fitsB_nil.mpr ⟨hwf.1, hwf.2, hx, hz⟩
  | b :: bs, t, x, z, hwf, hx, hz => by
      obtain ⟨h1, h2, h3, hrest⟩ := hwf
      simp only [planNeed, max_le_iff] at hx hz
      rw [← highPart_width x b.w] at hrest hx hz
      exact fitsB_cons.mpr ⟨h1, h2, h3, hx.1, hz.1, fitsB_of_planNeed hrest hx.2 hz.2⟩

/-! The spare capacities of the phase-product operands of one modular multiplication. -/
section Caps

variable {D W : ExtReg} (hmod : ModMulCircuitWorkspaceOK D W)

private lemma step1_xcap : regSize hmod.step1Workspace.xReserve - 1 = D.capacity - 2 := by
  show regSize (D.reserve.drop 1) - 1 = _
  simp only [regSize, Reg.width, Reg.drop, List.length_drop, ExtReg.capacity]
  omega

private lemma step1_zcap : regSize hmod.step1Workspace.zReserve - 1 = W.capacity - 1 := rfl

private lemma step2_xcap : regSize hmod.step2Workspace.xReserve - 1 = W.capacity - 1 := rfl

private lemma step2_zcap : regSize hmod.step2Workspace.zReserve - 1 = D.capacity - 2 := by
  show (D.grow 1).capacity - 1 = _
  rw [ExtReg.capacity_grow D 1 (le_trans (by norm_num) hmod.1)]
  omega

private lemma step5_xcap : regSize hmod.step5Workspace.xReserve - 1 = D.capacity - 2 := by
  show (D.grow 1).capacity - 1 = _
  rw [ExtReg.capacity_grow D 1 (le_trans (by norm_num) hmod.1)]
  omega

private lemma step5_zcap : regSize hmod.step5Workspace.zReserve - 1 = W.capacity - 1 := rfl

end Caps

/-! ## `Fits` for the order-finding circuit, from its four sites -/

/-- The four phase-product sites of one controlled modular multiplication fit. -/
structure CoreFits (P : ShorLoweringPolicy) (R : Rule) {N : ℕ} {data work scratch : ExtReg} {flag : ℕ}
    (hmod : ModMulCircuitWorkspaceOK data work)
    (hstep4 : CmpLtNWWorkspace N (data.grow 1) work scratch flag) : Prop where
  step1 : SiteFits P R (hmod.step1Workspace.xExt.grow 1) (hmod.step1Workspace.zExt.grow 1)
  step2 : SiteFits P R (hmod.step2Workspace.xExt.grow 1) (hmod.step2Workspace.zExt.grow 1)
  step4 : SiteFits P R (hstep4.mulWorkspace.xExt.grow 1) (hstep4.mulWorkspace.zExt.grow 1)
  step5 : SiteFits P R (hmod.step5Workspace.xExt.grow 1) (hmod.step5Workspace.zExt.grow 1)


lemma fits_H_reg (P : ShorLoweringPolicy) (R : Rule) (r : Reg) : Fits P R (H_reg r) := by
  unfold H_reg
  suffices h : ∀ (l : List ℕ) (acc : Gate), Fits P R acc →
      Fits P R (l.foldl (fun acc q => (Gate.H q) ;; acc) acc) from h _ _ trivial
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons q l ih => intro acc h; exact ih _ ⟨trivial, h⟩

lemma fits_initY1 (P : ShorLoweringPolicy) (R : Rule) (y : Reg) : Fits P R (initY1 y) := by
  unfold initY1
  split <;> trivial

lemma fits_core (P : ShorLoweringPolicy) (R : Rule) (c N ctrl : ℕ) {data work scratch : ExtReg}
    {flag : ℕ} (hmod : ModMulCircuitWorkspaceOK data work)
    (hstep4 : CmpLtNWWorkspace N (data.grow 1) work scratch flag) (h : CoreFits P R hmod hstep4) :
    Fits P R (CmodMulInPlaceCore c N ctrl data work scratch flag hmod hstep4) := by
  unfold CmodMulInPlaceCore step1 step2 step3 step4 step5 cmpLtNW fastConstMulInto cmpLtNWDifference
    IQFT Gate.PhaseProdUsing Gate.CPhaseProdUsing
  simp [Fits, fits_H_reg, h.step1, h.step2, h.step4, h.step5]

lemma fits_steps (P : ShorLoweringPolicy) (R : Rule) (a N : ℕ) {data work scratch : ExtReg}
    {flag : ℕ} (hmod : ModMulCircuitWorkspaceOK data work)
    (hstep4 : CmpLtNWWorkspace N (data.grow 1) work scratch flag) (h : CoreFits P R hmod hstep4) :
    ∀ (e : ℕ) (ctrls : List ℕ),
      Fits P R (modExpApproxStepsValid a N data work scratch flag hmod hstep4 e ctrls)
  | _, [] => trivial
  | e, ctrl :: ctrls => by
      simp only [modExpApproxStepsValid, Fits]
      exact ⟨fits_core P R _ N ctrl hmod hstep4 h, fits_steps P R a N hmod hstep4 h (e + 1) ctrls⟩

/-- `Fits` for the order-finding circuit follows from its four sites. -/
theorem fits_orderFindingApprox (P : ShorLoweringPolicy) (R : Rule) (a N : ℕ)
    (x y work scratch : ExtReg) (flag : ℕ)
    (hmod : ModMulCircuitWorkspaceOK y work)
    (hstep4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) (h : CoreFits P R hmod hstep4) :
    Fits P R (orderFindingApprox a N x y work scratch flag hmod hstep4) := by
  unfold orderFindingApprox modExpApproxValid IQFT
  simp [Fits, fits_H_reg, fits_initY1, fits_steps P R a N hmod hstep4 h]

/-- A site whose operands hold the default rule's `siteNeed` fits. -/
theorem siteFits_of_siteNeed (P : ShorLoweringPolicy) {x z : ExtReg}
    (hx : (siteNeed P defaultRule x.width z.width).1 ≤ x.capacity)
    (hz : (siteNeed P defaultRule x.width z.width).2 ≤ z.capacity) :
    SiteFits P defaultRule x z := by
  unfold SiteFits
  unfold siteNeed at hx hz
  split_ifs at hx hz ⊢ with h1 h2
  · intro p hp
    simp only [hp] at hx hz
    exact fitsB_of_planNeed (defaultPlan_wf hp) hx hz
  · intro p hp
    simp only [hp] at hx hz
    exact fitsB_of_planNeed (defaultPlan_wf hp) hz hx

lemma siteFits_of_bounds (P : ShorLoweringPolicy) {x z : ExtReg} {wx cx wz cz : ℕ}
    (hx : x.width = wx) (hcx : x.capacity = cx) (hz : z.width = wz) (hcz : z.capacity = cz)
    (h1 : (siteNeed P defaultRule wx wz).1 ≤ cx) (h2 : (siteNeed P defaultRule wx wz).2 ≤ cz) :
    SiteFits P defaultRule x z := by
  subst hx hcx hz hcz
  exact siteFits_of_siteNeed P h1 h2

private lemma le_sub_of_add_max {k a b c : ℕ} (h : k + max a b ≤ c) : b ≤ c - k := by
  omega

/-- The four sites of one modular multiplication fit the default rule on
registers holding the reserve `referenceSiteReserve` sizes. -/
lemma coreFits_of_reserve (P : ShorLoweringPolicy) {N : ℕ} {X D W S : ExtReg} {flag : ℕ}
    (hmod : ModMulCircuitWorkspaceOK D W) (hs4 : CmpLtNWWorkspace N (D.grow 1) W S flag)
    (hD : (shorWorkspaceNeedOf (Policy.qftWorkspaceNeed P) (referenceSiteReserve P) X D W S).data
      ≤ D.capacity)
    (hW : (shorWorkspaceNeedOf (Policy.qftWorkspaceNeed P) (referenceSiteReserve P) X D W S).auxiliary
      ≤ W.capacity)
    (hS : (shorWorkspaceNeedOf (Policy.qftWorkspaceNeed P) (referenceSiteReserve P) X D W S).scratch
      ≤ S.capacity) :
    CoreFits P defaultRule hmod hs4 := by
  simp only [shorWorkspaceNeedOf, referenceSiteReserve, max_le_iff] at hD hW hS
  obtain ⟨hd1, -, hd2, hd5⟩ := hD
  obtain ⟨-, hw1, hw2, hw4, hw5⟩ := hW
  obtain ⟨-, hs4c⟩ := hS
  have hDg : D.CanGrow 1 := hmod.data_canGrow_one
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine siteFits_of_bounds P (wx := D.width + 1) (cx := D.capacity - 2) (wz := W.width + 1)
      (cz := W.capacity - 1) ?_ ?_ ?_ ?_ (le_sub_of_add_max hd1) (le_sub_of_add_max hw1)
    · rw [ExtReg.width_grow _ 1 (Gate.PhaseProdWorkspace.xExt_canGrow _)]
      rfl
    · rw [ExtReg.capacity_grow _ 1 (Gate.PhaseProdWorkspace.xExt_canGrow _)]
      exact step1_xcap hmod
    · rw [ExtReg.width_grow _ 1 (Gate.PhaseProdWorkspace.zExt_canGrow _)]
      rfl
    · rw [ExtReg.capacity_grow _ 1 (Gate.PhaseProdWorkspace.zExt_canGrow _)]
      exact step1_zcap hmod
  · refine siteFits_of_bounds P (wx := W.width + 1) (cx := W.capacity - 1) (wz := D.width + 2)
      (cz := D.capacity - 2) ?_ ?_ ?_ ?_ (le_sub_of_add_max hw2) (le_sub_of_add_max hd2)
    · rw [ExtReg.width_grow _ 1 (Gate.PhaseProdWorkspace.xExt_canGrow _)]
      rfl
    · rw [ExtReg.capacity_grow _ 1 (Gate.PhaseProdWorkspace.xExt_canGrow _)]
      exact step2_xcap hmod
    · rw [ExtReg.width_grow _ 1 (Gate.PhaseProdWorkspace.zExt_canGrow _)]
      show (D.grow 1).width + 1 = D.width + 2
      rw [ExtReg.width_grow D 1 hDg]
    · rw [ExtReg.capacity_grow _ 1 (Gate.PhaseProdWorkspace.zExt_canGrow _)]
      exact step2_zcap hmod
  · refine siteFits_of_bounds P (wx := W.width + 1) (cx := W.capacity - 1) (wz := S.width + 1)
      (cz := S.capacity - 1) ?_ ?_ ?_ ?_ (le_sub_of_add_max hw4) (le_sub_of_add_max hs4c)
    · rw [ExtReg.width_grow _ 1 (Gate.PhaseProdWorkspace.xExt_canGrow _)]
      rfl
    · rw [ExtReg.capacity_grow _ 1 (Gate.PhaseProdWorkspace.xExt_canGrow _)]
      show regSize hs4.mulWorkspace.xReserve - 1 = _
      rw [hs4.mul_xReserve_eq]
      rfl
    · rw [ExtReg.width_grow _ 1 (Gate.PhaseProdWorkspace.zExt_canGrow _)]
      rfl
    · rw [ExtReg.capacity_grow _ 1 (Gate.PhaseProdWorkspace.zExt_canGrow _)]
      show regSize hs4.mulWorkspace.zReserve - 1 = _
      rw [hs4.mul_zReserve_eq]
      rfl
  · refine siteFits_of_bounds P (wx := D.width + 2) (cx := D.capacity - 2) (wz := W.width + 1)
      (cz := W.capacity - 1) ?_ ?_ ?_ ?_ (le_sub_of_add_max hd5) (le_sub_of_add_max hw5)
    · rw [ExtReg.width_grow _ 1 (Gate.PhaseProdWorkspace.xExt_canGrow _)]
      show (D.grow 1).width + 1 = D.width + 2
      rw [ExtReg.width_grow D 1 hDg]
    · rw [ExtReg.capacity_grow _ 1 (Gate.PhaseProdWorkspace.xExt_canGrow _)]
      exact step5_xcap hmod
    · rw [ExtReg.width_grow _ 1 (Gate.PhaseProdWorkspace.zExt_canGrow _)]
      rfl
    · rw [ExtReg.capacity_grow _ 1 (Gate.PhaseProdWorkspace.zExt_canGrow _)]
      exact step5_zcap hmod

/-! ## The reference layout fits the default rule at every site -/

/-- Every reference layout fits the default rule's plan at every site. -/
theorem reference_fits (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (m : ℕ) :
    Fits P defaultRule
      (orderFindingApprox inst.a inst.N
        (allocateReferenceLayout P inst m).x (allocateReferenceLayout P inst m).data
        (allocateReferenceLayout P inst m).work (allocateReferenceLayout P inst m).scratch
        (allocateReferenceLayout P inst m).flag
        (reference_modMulCircuitWorkspaceOK P inst m) (reference_step4Workspace P inst m)) := by
  have hneed : shorWorkspaceNeedOf (Policy.qftWorkspaceNeed P) (referenceSiteReserve P)
      (allocateReferenceLayout P inst m).x (allocateReferenceLayout P inst m).data
      (allocateReferenceLayout P inst m).work (allocateReferenceLayout P inst m).scratch
      = referenceWorkspaceNeed P inst m :=
    reference_workspaceNeed_eq P inst m
  refine fits_orderFindingApprox _ _ _ _ _ _ _ _ _ _ _ (coreFits_of_reserve P (X := (allocateReferenceLayout P inst m).x) _ _ ?_ ?_ ?_)
  · rw [hneed, allocateReferenceLayout_data_capacity, referenceDataReserveSize]
    exact le_max_right _ _
  · rw [hneed, allocateReferenceLayout_work_capacity, referenceWorkReserveSize]
    exact le_max_right _ _
  · rw [hneed, allocateReferenceLayout_scratch_capacity, referenceScratchReserveSize]
    exact le_max_right _ _

end Balanced
end Shor
