import ForShor.ShorVerification.Implementation.QubitCount.Proofs.Formula

/-!
# Qubit count: the unconditional balanced split

`balanceU` splits every site, so its circuit's peak depends on the register widths
alone. The capacity-aware balanced count equals the width-only one wherever every
site's plan fits (`orderFindingQubitsBalanced_eq_U`), and `Balanced.Fits` says
exactly that of the circuit's four sites (`coreFits_sites`).
-/

namespace Shor
namespace QubitCount

open _root_.Shor.Balanced

/-! ## The width-only count -/

/-- `sitePeakOf` is `sitePeakU` at a site whose plan fits. -/
theorem sitePeakOf_eq_U (pp : ℕ → ℕ → ℕ) (rn : ℕ → ℕ → ℕ × ℕ) (R : Rule) (wx cx wz cz : ℕ)
    (h : (wz < wx → ∀ p, R.plan wx wz = some p → planFitsOf rn p.lower p.top wx cx wz cz = true) ∧
         (wx < wz → ∀ p, R.plan wz wx = some p → planFitsOf rn p.lower p.top wz cz wx cx = true)) :
    sitePeakOf pp rn R wx cx wz cz = sitePeakU pp R wx wz := by
  unfold sitePeakOf sitePeakU
  split_ifs with h1 h2
  · cases hp : R.plan wx wz with
    | none => rfl
    | some p => simp [h.1 h1 p hp]
  · cases hp : R.plan wz wx with
    | none => rfl
    | some p => simp [h.2 h2 p hp]
  · rfl

/-- The four sites of the order-finding circuit, as width and capacity tuples. -/
def orderFindingSites (dW dC wW wC sW sC : ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  [ (dW + 1, dC - 2, wW + 1, wC - 1), (wW + 1, wC - 1, dW + 2, dC - 2),
    (wW + 1, wC - 1, sW + 1, sC - 1), (dW + 2, dC - 2, wW + 1, wC - 1) ]

/-- The fit conditions `sitePeakOf_eq_U` asks of a site `(wx, cx, wz, cz)`. -/
def SiteFitsAt (P : ShorLoweringPolicy) (R : Rule) (s : ℕ × ℕ × ℕ × ℕ) : Prop :=
  (s.2.2.1 < s.1 → ∀ p, R.plan s.1 s.2.2.1 = some p →
    planFitsOf (reserveBudgetD P.widthRule (Policy.compile P)) p.lower p.top
      s.1 s.2.1 s.2.2.1 s.2.2.2 = true) ∧
  (s.1 < s.2.2.1 → ∀ p, R.plan s.2.2.1 s.1 = some p →
    planFitsOf (reserveBudgetD P.widthRule (Policy.compile P)) p.lower p.top
      s.2.2.1 s.2.2.2 s.1 s.2.1 = true)

/-- When the four sites' plans fit, the balanced count is the width-only one. -/
theorem orderFindingQubitsBalanced_eq_U (P : ShorLoweringPolicy) (R : Rule)
    (xW dW dC wW wC sW sC : ℕ)
    (h : ∀ s ∈ orderFindingSites dW dC wW wC sW sC, SiteFitsAt P R s) :
    Policy.orderFindingQubitsBalanced P R xW dW dC wW wC sW sC
      = Policy.orderFindingQubitsU P R xW dW wW sW := by
  simp only [orderFindingSites, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, SiteFitsAt] at h
  obtain ⟨h1, h2, h4, h5⟩ := h
  unfold Policy.orderFindingQubitsBalanced Policy.orderFindingPeakBalanced orderFindingPeakBalancedD
    Policy.orderFindingQubitsU Policy.orderFindingPeakU orderFindingPeakUD
    orderFindingPeakWith modMulPeakWith modMulPhasePeaksWith sitePeakD
  dsimp only
  rw [sitePeakOf_eq_U _ _ _ _ _ _ _ h1, sitePeakOf_eq_U _ _ _ _ _ _ _ h2,
    sitePeakOf_eq_U _ _ _ _ _ _ _ h4, sitePeakOf_eq_U _ _ _ _ _ _ _ h5]

/-- The peak of the unconditionally balanced circuit is the capacity-aware
balanced count: under `Fits` the pass is `balance`. -/
theorem orderFindingQubitsBalancedU_formula (P : ShorLoweringPolicy) (R : Rule) (hP : P.Admissible)
    (a N : ℕ) (x y work scratch : ExtReg) (flag : ℕ)
    (hmod : ModMulCircuitWorkspaceOK y work)
    (hstep4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hws : Policy.GateWorkspaceOK P (orderFindingApprox a N x y work scratch flag hmod hstep4))
    (hf : Fits P R (orderFindingApprox a N x y work scratch flag hmod hstep4))
    (hlay : OrderFindingSpaceLayout x y work scratch flag) :
    (orderFindingApproxLowBalancedU P R a N x y work scratch flag hmod hstep4 hws hf).peakQubits
        (orderFindingBaseSet x y work scratch flag)
      = Policy.orderFindingQubitsBalanced P R x.width
          y.width y.capacity work.width work.capacity scratch.width scratch.capacity := by
  unfold orderFindingApproxLowBalancedU
  rw [lowerGate_congr P (balanceU_eq _ hf) (balanceU_ok P R _ hws hf) (balance_ok P R _ hws)]
  exact orderFindingPeakFormulaBalanced P R hP a N x y work scratch flag hmod hstep4 hws hlay

/-! ## The sites of a circuit that fits -/

lemma planFits_eq_planFitsOf (P : ShorLoweringPolicy) :
    ∀ (bs : List Block) (t wx cx wz cz : ℕ),
      Rec.planFits P bs t wx cx wz cz = planFitsOf (Policy.reserveNeed P) bs t wx cx wz cz
  | [], _, _, _, _, _ => rfl
  | b :: bs, t, wx, cx, wz, cz => by
      simp only [Rec.planFits, planFitsOf, planFits_eq_planFitsOf P bs]

/-- A site that fits, as the conditions of `SiteFitsAt`. -/
lemma siteFits_at (P : ShorLoweringPolicy) (R : Rule) {x z : ExtReg} (h : SiteFits P R x z) :
    SiteFitsAt P R (x.width, x.capacity, z.width, z.capacity) := by
  unfold SiteFitsAt SiteFits at *
  dsimp only at *
  rw [reserveBudgetD_eq]
  refine ⟨fun hlt p hp => ?_, fun hlt p hp => ?_⟩
  · simp only [hlt, ↓reduceIte] at h
    rw [← planFits_eq_planFitsOf, ← fitsB_eq_planFits]
    exact h p hp
  · have hne : ¬ z.width < x.width := by omega
    simp only [hne, hlt, ↓reduceIte] at h
    rw [← planFits_eq_planFitsOf, ← fitsB_eq_planFits]
    exact h p hp

/-- The four sites of a modular multiplication whose sites fit. -/
lemma coreFits_sites (P : ShorLoweringPolicy) (R : Rule) {N : ℕ} {D W S : ExtReg} {flag : ℕ}
    (hmod : ModMulCircuitWorkspaceOK D W) (hs4 : CmpLtNWWorkspace N (D.grow 1) W S flag)
    (h : CoreFits P R hmod hs4) :
    ∀ s ∈ orderFindingSites D.width D.capacity W.width W.capacity S.width S.capacity,
      SiteFitsAt P R s := by
  have hDg : D.CanGrow 1 := le_trans (by norm_num) hmod.1
  have w1x : (hmod.step1Workspace.xExt.grow 1).width = D.width + 1 := by
    rw [ExtReg.width_grow _ 1 (Gate.PhaseProdWorkspace.xExt_canGrow _)]; rfl
  have c1x : (hmod.step1Workspace.xExt.grow 1).capacity = D.capacity - 2 := by
    rw [ExtReg.capacity_grow _ 1 (Gate.PhaseProdWorkspace.xExt_canGrow _)]; exact step1_xcap hmod
  have w1z : (hmod.step1Workspace.zExt.grow 1).width = W.width + 1 := by
    rw [ExtReg.width_grow _ 1 (Gate.PhaseProdWorkspace.zExt_canGrow _)]; rfl
  have c1z : (hmod.step1Workspace.zExt.grow 1).capacity = W.capacity - 1 := by
    rw [ExtReg.capacity_grow _ 1 (Gate.PhaseProdWorkspace.zExt_canGrow _)]; exact step1_zcap hmod
  have w2x : (hmod.step2Workspace.xExt.grow 1).width = W.width + 1 := by
    rw [ExtReg.width_grow _ 1 (Gate.PhaseProdWorkspace.xExt_canGrow _)]; rfl
  have c2x : (hmod.step2Workspace.xExt.grow 1).capacity = W.capacity - 1 := by
    rw [ExtReg.capacity_grow _ 1 (Gate.PhaseProdWorkspace.xExt_canGrow _)]; exact step2_xcap hmod
  have w2z : (hmod.step2Workspace.zExt.grow 1).width = D.width + 2 := by
    rw [ExtReg.width_grow _ 1 (Gate.PhaseProdWorkspace.zExt_canGrow _)]
    show (D.grow 1).width + 1 = D.width + 2
    rw [ExtReg.width_grow D 1 hDg]
  have c2z : (hmod.step2Workspace.zExt.grow 1).capacity = D.capacity - 2 := by
    rw [ExtReg.capacity_grow _ 1 (Gate.PhaseProdWorkspace.zExt_canGrow _)]; exact step2_zcap hmod
  have w4x : (hs4.mulWorkspace.xExt.grow 1).width = W.width + 1 := by
    rw [ExtReg.width_grow _ 1 (Gate.PhaseProdWorkspace.xExt_canGrow _)]; rfl
  have c4x : (hs4.mulWorkspace.xExt.grow 1).capacity = W.capacity - 1 := by
    rw [ExtReg.capacity_grow _ 1 (Gate.PhaseProdWorkspace.xExt_canGrow _)]
    show regSize hs4.mulWorkspace.xReserve - 1 = _
    rw [hs4.mul_xReserve_eq]; rfl
  have w4z : (hs4.mulWorkspace.zExt.grow 1).width = S.width + 1 := by
    rw [ExtReg.width_grow _ 1 (Gate.PhaseProdWorkspace.zExt_canGrow _)]; rfl
  have c4z : (hs4.mulWorkspace.zExt.grow 1).capacity = S.capacity - 1 := by
    rw [ExtReg.capacity_grow _ 1 (Gate.PhaseProdWorkspace.zExt_canGrow _)]
    show regSize hs4.mulWorkspace.zReserve - 1 = _
    rw [hs4.mul_zReserve_eq]; rfl
  have w5x : (hmod.step5Workspace.xExt.grow 1).width = D.width + 2 := by
    rw [ExtReg.width_grow _ 1 (Gate.PhaseProdWorkspace.xExt_canGrow _)]
    show (D.grow 1).width + 1 = D.width + 2
    rw [ExtReg.width_grow D 1 hDg]
  have c5x : (hmod.step5Workspace.xExt.grow 1).capacity = D.capacity - 2 := by
    rw [ExtReg.capacity_grow _ 1 (Gate.PhaseProdWorkspace.xExt_canGrow _)]; exact step5_xcap hmod
  have w5z : (hmod.step5Workspace.zExt.grow 1).width = W.width + 1 := by
    rw [ExtReg.width_grow _ 1 (Gate.PhaseProdWorkspace.zExt_canGrow _)]; rfl
  have c5z : (hmod.step5Workspace.zExt.grow 1).capacity = W.capacity - 1 := by
    rw [ExtReg.capacity_grow _ 1 (Gate.PhaseProdWorkspace.zExt_canGrow _)]; exact step5_zcap hmod
  have h1 := siteFits_at P R h.step1
  have h2 := siteFits_at P R h.step2
  have h4 := siteFits_at P R h.step4
  have h5 := siteFits_at P R h.step5
  rw [w1x, c1x, w1z, c1z] at h1
  rw [w2x, c2x, w2z, c2z] at h2
  rw [w4x, c4x, w4z, c4z] at h4
  rw [w5x, c5x, w5z, c5z] at h5
  simp only [orderFindingSites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  exact ⟨h1, h2, h4, h5⟩

/-- A modular multiplication that fits has its four sites fitting. -/
lemma coreFits_of_fits_core (P : ShorLoweringPolicy) (R : Rule) (c N ctrl : ℕ)
    {D W S : ExtReg} {flag : ℕ} (hmod : ModMulCircuitWorkspaceOK D W)
    (hs4 : CmpLtNWWorkspace N (D.grow 1) W S flag)
    (h : Fits P R (CmodMulInPlaceCore c N ctrl D W S flag hmod hs4)) : CoreFits P R hmod hs4 := by
  unfold CmodMulInPlaceCore step1 step2 step3 step4 step5 cmpLtNW fastConstMulInto cmpLtNWDifference
    IQFT Gate.PhaseProdUsing Gate.CPhaseProdUsing at h
  simp only [Fits] at h
  exact ⟨by tauto, by tauto, by tauto, by tauto⟩

/-- An order-finding circuit with a nonempty exponent register that fits has its
four sites fitting. -/
lemma coreFits_of_fits (P : ShorLoweringPolicy) (R : Rule) (a N : ℕ) (x y work scratch : ExtReg)
    (flag : ℕ) (hmod : ModMulCircuitWorkspaceOK y work)
    (hstep4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hf : Fits P R (orderFindingApprox a N x y work scratch flag hmod hstep4))
    (hx : x.width ≠ 0) : CoreFits P R hmod hstep4 := by
  unfold orderFindingApprox modExpApproxValid at hf
  obtain ⟨q, rest, hq⟩ : ∃ q rest, x.active.qubits = q :: rest := by
    cases hl : x.active.qubits with
    | nil => exact absurd (by simp [ExtReg.width, regSize, Reg.width, hl]) hx
    | cons q rest => exact ⟨q, rest, rfl⟩
  rw [hq] at hf
  simp only [modExpApproxStepsValid, Fits] at hf
  exact coreFits_of_fits_core P R _ N q hmod hstep4 (by tauto)

/-! ## The formula -/

theorem orderFindingPeakFormulaBalancedU (P : ShorLoweringPolicy) (R : Rule) :
    Policy.OrderFindingPeakFormulaBalancedU P R := by
  intro hP a N x y work scratch flag hmod hstep4 hws hf hlay
  rw [orderFindingQubitsBalancedU_formula P R hP a N x y work scratch flag hmod hstep4 hws hf hlay]
  by_cases hx : x.width = 0
  · simp [Policy.orderFindingQubitsBalanced, Policy.orderFindingPeakBalanced,
      orderFindingPeakBalancedD, Policy.orderFindingQubitsU, Policy.orderFindingPeakU,
      orderFindingPeakUD, orderFindingPeakWith, hx]
  · exact orderFindingQubitsBalanced_eq_U P R _ _ _ _ _ _ _
      (coreFits_sites P R hmod hstep4
        (coreFits_of_fits P R a N x y work scratch flag hmod hstep4 hf hx))

end QubitCount
end Shor
