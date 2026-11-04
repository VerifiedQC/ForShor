import ForShor.ShorVerification.Implementation.QubitCount.Main

/-!
# Balancing without the fit check

`siteGateU` splits every site the rule has a plan for; `balanceU` applies it
everywhere. Where every site's plan fits its operands' reserve (`Fits`),
`balanceU` is `balance`, so the correctness and the qubit count of the
conditional pass carry over, and the qubit count no longer depends on the
capacities. The reference layout's reserves (`referenceSiteReserve`) make the
default rule's plan fit at every site of every instance (`referenceFits_default`),
so `balancedUShorImplementation` takes no hypothesis.
-/

namespace Shor
namespace Balanced

open Reference

/-! ## Definitions -/

/-! ### The pass -/

/-- Balance a site whenever the rule has a plan for it. -/
def siteGateU (R : Rule) (c : Ctl) (φ : Angle) (x z : ExtReg) : Gate :=
  if z.width < x.width then
    match R.plan x.width z.width with
    | some p => splitGate c φ p.lower p.top x z
    | none => c.gate φ x z
  else if x.width < z.width then
    match R.plan z.width x.width with
    | some p => splitGate c φ p.lower p.top z x
    | none => c.gate φ x z
  else c.gate φ x z

/-- Every signed and controlled signed phase product becomes its `siteGateU`. -/
def balanceU (R : Rule) : Gate → Gate
  | .seq U V => .seq (balanceU R U) (balanceU R V)
  | .adj U => .adj (balanceU R U)
  | .SignedPhaseProd φ x z => siteGateU R .none φ x z
  | .CSignedPhaseProd q φ x z => siteGateU R (.ctrl q) φ x z
  | G => G

/-! ### Fitting a site's plan -/

/-- The rule's plan at a site fits the operands' reserve. -/
def SiteFits (P : ShorLoweringPolicy) (R : Rule) (x z : ExtReg) : Prop :=
  if z.width < x.width then
    ∀ p, R.plan x.width z.width = some p → fitsB P p.lower p.top x z = true
  else if x.width < z.width then
    ∀ p, R.plan z.width x.width = some p → fitsB P p.lower p.top z x = true
  else True

/-- Every phase-product site's plan fits. -/
def Fits (P : ShorLoweringPolicy) (R : Rule) : Gate → Prop
  | .seq U V => Fits P R U ∧ Fits P R V
  | .adj U => Fits P R U
  | .SignedPhaseProd _ x z => SiteFits P R x z
  | .CSignedPhaseProd _ _ x z => SiteFits P R x z
  | _ => True

/-- The four phase-product sites of one controlled modular multiplication fit. -/
structure CoreFits (P : ShorLoweringPolicy) (R : Rule) {N : ℕ} {data work scratch : ExtReg} {flag : ℕ}
    (hmod : ModMulCircuitWorkspaceOK data work)
    (hstep4 : CmpLtNWWorkspace N (data.grow 1) work scratch flag) : Prop where
  step1 : SiteFits P R (hmod.step1Workspace.xExt.grow 1) (hmod.step1Workspace.zExt.grow 1)
  step2 : SiteFits P R (hmod.step2Workspace.xExt.grow 1) (hmod.step2Workspace.zExt.grow 1)
  step4 : SiteFits P R (hstep4.mulWorkspace.xExt.grow 1) (hstep4.mulWorkspace.zExt.grow 1)
  step5 : SiteFits P R (hmod.step5Workspace.xExt.grow 1) (hmod.step5Workspace.zExt.grow 1)

/-- Every instance's reference layout, at the precision the reference chooses,
fits the rule's plan at every site. -/
def ReferenceFits (P : ShorLoweringPolicy) (R : Rule) : Prop :=
  ∀ inst : ShorOrderFindingInstance,
    Fits P R (orderFindingApprox inst.a inst.N
      (allocateReferenceLayout P inst (referenceChosenPrecision inst.N)).x
      (allocateReferenceLayout P inst (referenceChosenPrecision inst.N)).data
      (allocateReferenceLayout P inst (referenceChosenPrecision inst.N)).work
      (allocateReferenceLayout P inst (referenceChosenPrecision inst.N)).scratch
      (allocateReferenceLayout P inst (referenceChosenPrecision inst.N)).flag
      (reference_modMulCircuitWorkspaceOK P inst (referenceChosenPrecision inst.N))
      (reference_step4Workspace P inst (referenceChosenPrecision inst.N)))

/-- The width conditions of `fitsB`: every block is narrower than what is left of
the split operand, reads unsigned at its width, and covers the small operand. -/
def PlanWF : List Block → ℕ → ℕ → ℕ → Prop
  | [], t, xw, zw => xw ≤ t ∧ zw ≤ t
  | b :: bs, t, xw, zw => b.w < xw ∧ b.w + 1 ≤ b.t ∧ zw ≤ b.t ∧ PlanWF bs t (xw - b.w) zw

/-! ### The qubit count from the widths -/

/-- The cost of a split site from the widths alone. -/
def sitePeakU (pp : ℕ → ℕ → ℕ) (R : Rule) (wx wz : ℕ) : ℕ :=
  if wz < wx then
    match R.plan wx wz with
    | some p => splitPeakOf pp p.lower p.top wx wz
    | none => pp wx wz
  else if wx < wz then
    match R.plan wz wx with
    | some p => splitPeakOf pp p.lower p.top wz wx
    | none => pp wx wz
  else pp wx wz

/-- **The qubit count of the order-finding circuit with every site split**,
from the register widths alone. -/
def Policy.orderFindingQubitsU (P : ShorLoweringPolicy) (R : Rule) (xW dW wW sW : ℕ) : ℕ :=
  xW + (dW + 1) + wW + sW + 1
    + orderFindingPeakWith
        (fun wx _ wz _ => sitePeakU (peakReserveD P.widthRule (Policy.compile P)) R wx wz)
        (qftPeakD P.widthRule (Policy.compile P)) xW dW 0 wW 0 sW 0

/-- The four sites of the order-finding circuit, as width and capacity tuples. -/
def orderFindingSites (dW dC wW wC sW sC : ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  [ (dW + 1, dC - 2, wW + 1, wC - 1), (wW + 1, wC - 1, dW + 2, dC - 2),
    (wW + 1, wC - 1, sW + 1, sC - 1), (dW + 2, dC - 2, wW + 1, wC - 1) ]

/-! ## The workspace of the pass

The lowered circuits below are built from these. -/

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

/-! ## The circuits -/

/-- Lowered approximate order finding with every phase-product site split. -/
def orderFindingApproxLowBalancedU (P : ShorLoweringPolicy) (R : Rule)
    (a N : ℕ) (x y work scratch : ExtReg) (flag : ℕ)
    (hmod : ModMulCircuitWorkspaceOK y work)
    (hstep4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hws : Policy.GateWorkspaceOK P (orderFindingApprox a N x y work scratch flag hmod hstep4))
    (hf : Fits P R (orderFindingApprox a N x y work scratch flag hmod hstep4)) : LowGate :=
  Policy.lowerGate P (balanceU R (orderFindingApprox a N x y work scratch flag hmod hstep4))
    (balanceU_ok P R _ hws hf)

/-- The reference circuit at precision `m` with every site split. -/
def balancedUShorCircuit (P : ShorLoweringPolicy) (R : Rule) (inst : ShorOrderFindingInstance)
    (m : ℕ)
    (hf : Fits P R (orderFindingApprox inst.a inst.N
      (allocateReferenceLayout P inst m).x (allocateReferenceLayout P inst m).data
      (allocateReferenceLayout P inst m).work (allocateReferenceLayout P inst m).scratch
      (allocateReferenceLayout P inst m).flag
      (reference_modMulCircuitWorkspaceOK P inst m) (reference_step4Workspace P inst m))) :
    LowGate :=
  orderFindingApproxLowBalancedU P R inst.a inst.N
    (allocateReferenceLayout P inst m).x (allocateReferenceLayout P inst m).data
    (allocateReferenceLayout P inst m).work (allocateReferenceLayout P inst m).scratch
    (allocateReferenceLayout P inst m).flag
    (reference_modMulCircuitWorkspaceOK P inst m) (reference_step4Workspace P inst m)
    (reference_gateWorkspaceOK P inst m) hf

/-- The unconditionally balanced reference program at precision `m`. -/
def balancedUProgramAt (P : ShorLoweringPolicy) (R : Rule) (m : ℕ) (inst : ShorOrderFindingInstance)
    (hf : Fits P R (orderFindingApprox inst.a inst.N
      (allocateReferenceLayout P inst m).x (allocateReferenceLayout P inst m).data
      (allocateReferenceLayout P inst m).work (allocateReferenceLayout P inst m).scratch
      (allocateReferenceLayout P inst m).flag
      (reference_modMulCircuitWorkspaceOK P inst m) (reference_step4Workspace P inst m))) : ShorOrderFindingProgram where
  circuit := balancedUShorCircuit P R inst m hf
  output := (allocateReferenceLayout P inst m).x.active

/-- The unconditionally balanced submitted program. -/
noncomputable def balancedUSubmittedProgram (P : ShorLoweringPolicy) (R : Rule)
    (hfits : ReferenceFits P R) (inst : ShorOrderFindingInstance) : ShorOrderFindingProgram :=
  balancedUProgramAt P R (referenceChosenPrecision inst.N) inst (hfits inst)

/-! ## Theorems -/

/-! ### Well-formed plans -/

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

/-! ### `Fits` for the order-finding circuit, from its four sites -/

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
      exact QubitCount.step1_xcap hmod
    · rw [ExtReg.width_grow _ 1 (Gate.PhaseProdWorkspace.zExt_canGrow _)]
      rfl
    · rw [ExtReg.capacity_grow _ 1 (Gate.PhaseProdWorkspace.zExt_canGrow _)]
      exact QubitCount.step1_zcap hmod
  · refine siteFits_of_bounds P (wx := W.width + 1) (cx := W.capacity - 1) (wz := D.width + 2)
      (cz := D.capacity - 2) ?_ ?_ ?_ ?_ (le_sub_of_add_max hw2) (le_sub_of_add_max hd2)
    · rw [ExtReg.width_grow _ 1 (Gate.PhaseProdWorkspace.xExt_canGrow _)]
      rfl
    · rw [ExtReg.capacity_grow _ 1 (Gate.PhaseProdWorkspace.xExt_canGrow _)]
      exact QubitCount.step2_xcap hmod
    · rw [ExtReg.width_grow _ 1 (Gate.PhaseProdWorkspace.zExt_canGrow _)]
      show (D.grow 1).width + 1 = D.width + 2
      rw [ExtReg.width_grow D 1 hDg]
    · rw [ExtReg.capacity_grow _ 1 (Gate.PhaseProdWorkspace.zExt_canGrow _)]
      exact QubitCount.step2_zcap hmod
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
      exact QubitCount.step5_xcap hmod
    · rw [ExtReg.width_grow _ 1 (Gate.PhaseProdWorkspace.zExt_canGrow _)]
      rfl
    · rw [ExtReg.capacity_grow _ 1 (Gate.PhaseProdWorkspace.zExt_canGrow _)]
      exact QubitCount.step5_zcap hmod

/-! ### The reference layout fits the default rule at every site -/

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

/-- The default rule's split fits every instance's reference layout. -/
theorem referenceFits_default (P : ShorLoweringPolicy) : ReferenceFits P defaultRule :=
  fun inst => reference_fits P inst _

/-! ### Correctness -/

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

theorem balancedUShorCircuit_eq (P : ShorLoweringPolicy) (R : Rule) (inst : ShorOrderFindingInstance)
    (m : ℕ) (hf : Fits P R (orderFindingApprox inst.a inst.N
      (allocateReferenceLayout P inst m).x (allocateReferenceLayout P inst m).data
      (allocateReferenceLayout P inst m).work (allocateReferenceLayout P inst m).scratch
      (allocateReferenceLayout P inst m).flag
      (reference_modMulCircuitWorkspaceOK P inst m) (reference_step4Workspace P inst m))) :
    balancedUShorCircuit P R inst m hf = balancedShorCircuit P R inst m := by
  unfold balancedUShorCircuit orderFindingApproxLowBalancedU balancedShorCircuit
    orderFindingApproxLowBalanced
  exact lowerGate_congr _ (balanceU_eq _ hf) _ _

theorem balancedUSubmittedProgram_eq (P : ShorLoweringPolicy) (R : Rule) (hfits : ReferenceFits P R)
    (inst : ShorOrderFindingInstance) :
    balancedUSubmittedProgram P R hfits inst = balancedSubmittedProgram P R inst := by
  unfold balancedUSubmittedProgram balancedUProgramAt balancedSubmittedProgram balancedProgramAt
  rw [balancedUShorCircuit_eq]

section Success

variable (qs : QSemantics) [RegEncoding qs.Basis] [MeasureClass qs] [GateSemanticsFacts qs]
  [LowerGateClass qs]

theorem balancedUSubmittedProgram_correct (P : ShorLoweringPolicy) (hP : P.Admissible) (R : Rule)
    (hfits : ReferenceFits P R) :
    ∀ (T : ℕ → ℕ), ContinuedFractionSearchComplete T →
    ∀ inst : ShorOrderFindingInstance,
      0 ≤ referenceSuccessProbability inst.N ∧
      referenceSuccessProbability inst.N ≤ 1 ∧
      referenceSuccessProbability inst.N ≤
        probability_of_success
          (qs := qs)
          (evalC := LowerGateClass.evalL (qs := qs))
          (T := T)
          (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
          (x := (balancedUSubmittedProgram P R hfits inst).output)
          (r := ord inst.a inst.N inst.coprime)
          (Q := ASize (balancedUSubmittedProgram P R hfits inst).output)
          (C := (balancedUSubmittedProgram P R hfits inst).circuit)
          (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis))) := by
  intro T hT inst
  rw [balancedUSubmittedProgram_eq]
  exact balancedSubmittedProgram_correct (qs := qs) P hP R T hT inst

end Success

/-! ### The qubit count -/

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

/-- When the four sites' plans fit, the balanced count is the capacity-free one. -/
theorem orderFindingQubitsBalanced_eq_U (P : ShorLoweringPolicy) (R : Rule)
    (xW dW dC wW wC sW sC : ℕ)
    (h : ∀ s ∈ orderFindingSites dW dC wW wC sW sC,
      (s.2.2.1 < s.1 → ∀ p, R.plan s.1 s.2.2.1 = some p →
        planFitsOf (reserveBudgetD P.widthRule (Policy.compile P)) p.lower p.top
          s.1 s.2.1 s.2.2.1 s.2.2.2 = true) ∧
      (s.1 < s.2.2.1 → ∀ p, R.plan s.2.2.1 s.1 = some p →
        planFitsOf (reserveBudgetD P.widthRule (Policy.compile P)) p.lower p.top
          s.2.2.1 s.2.2.2 s.1 s.2.1 = true)) :
    Policy.orderFindingQubitsBalanced P R xW dW dC wW wC sW sC
      = Policy.orderFindingQubitsU P R xW dW wW sW := by
  simp only [orderFindingSites, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at h
  obtain ⟨h1, h2, h4, h5⟩ := h
  unfold Policy.orderFindingQubitsBalanced Policy.orderFindingPeakBalanced orderFindingPeakBalancedD
    Policy.orderFindingQubitsU
    orderFindingPeakWith modMulPeakWith modMulPhasePeaksWith sitePeakD
  dsimp only
  rw [sitePeakOf_eq_U _ _ _ _ _ _ _ h1, sitePeakOf_eq_U _ _ _ _ _ _ _ h2,
    sitePeakOf_eq_U _ _ _ _ _ _ _ h4, sitePeakOf_eq_U _ _ _ _ _ _ _ h5]

/-- **The qubit count of the unconditionally balanced circuit**, under the
hypotheses of `Policy.OrderFindingPeakFormula` and `Fits`. -/
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
  exact QubitCount.orderFindingPeakFormulaBalanced P R hP a N x y work scratch flag hmod hstep4 hws hlay

/-! ## The packaged implementation -/

section Implementation

variable (qs : QSemantics) [RegEncoding qs.Basis] [MeasureClass qs] [GateSemanticsFacts qs]
  [LowerGateClass qs]

/-- **The reference submission with every phase-product site split by the
default rule**, packaged into the framework's `ShorImplementation` contract. -/
noncomputable def balancedUShorImplementation (P : ShorLoweringPolicy) (hP : P.Admissible) :
    ShorImplementation (qs := qs) where
  program := balancedUSubmittedProgram P defaultRule (referenceFits_default P)
  successProbability := referenceSuccessProbability
  correct := balancedUSubmittedProgram_correct (qs := qs) P hP defaultRule (referenceFits_default P)
  trialCount := referenceTrialCount
  trialCount_correct := by
    intro N _
    apply referenceTrialCount_correct

end Implementation

/-! ## The standard `k = 2` policy at 2048 bits -/

lemma siteFits_of_numbers (P : ShorLoweringPolicy) (R : Rule) {x z : ExtReg} {wx cx wz cz : ℕ}
    (hx : x.width = wx) (hcx : x.capacity = cx) (hz : z.width = wz) (hcz : z.capacity = cz)
    (h1 : wz < wx → ∀ p, R.plan wx wz = some p →
      QubitCount.Rec.planFits P p.lower p.top wx cx wz cz = true)
    (h2 : wx < wz → ∀ p, R.plan wz wx = some p →
      QubitCount.Rec.planFits P p.lower p.top wz cz wx cx = true) :
    SiteFits P R x z := by
  unfold SiteFits
  rw [hx, hz]
  split_ifs with h h'
  · intro p hp
    rw [QubitCount.fitsB_eq_planFits, hx, hcx, hz, hcz]
    exact h1 h p hp
  · intro p hp
    rw [QubitCount.fitsB_eq_planFits, hx, hcx, hz, hcz]
    exact h2 h' p hp

/-- The four sites of the standard `k = 2` policy fit the default rule's plan on
registers of the 2048-bit widths with the reference layout's reserves. -/
lemma coreFits_2048 {N : ℕ} {D W S : ExtReg} {flag : ℕ}
    (hmod : ModMulCircuitWorkspaceOK D W) (hs4 : CmpLtNWWorkspace N (D.grow 1) W S flag)
    (hdw : D.width = 2048) (hww : W.width = 2347) (hsw : S.width = 4398)
    (hDc : 43009 ≤ D.capacity) (hWc : 42709 ≤ W.capacity) (hSc : 43005 ≤ S.capacity) :
    CoreFits standardPolicy2 defaultRule hmod hs4 := by
  have hrn : Policy.reserveNeed standardPolicy2 2348 2348 = (42708, 42708) := by
    have h := QubitCount.reserveBudgetD_2348_2348
    rwa [QubitCount.reserveBudgetD_eq] at h
  have hDg : D.CanGrow 1 := hmod.data_canGrow_one
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine siteFits_of_numbers _ _ (wx := 2049) (cx := D.capacity - 2) (wz := 2348)
      (cz := W.capacity - 1) ?_ ?_ ?_ ?_ ?_ ?_
    · rw [ExtReg.width_grow _ 1 (Gate.PhaseProdWorkspace.xExt_canGrow _)]
      show D.width + 1 = 2049
      omega
    · rw [ExtReg.capacity_grow _ 1 (Gate.PhaseProdWorkspace.xExt_canGrow _)]
      exact QubitCount.step1_xcap hmod
    · rw [ExtReg.width_grow _ 1 (Gate.PhaseProdWorkspace.zExt_canGrow _)]
      show W.width + 1 = 2348
      omega
    · rw [ExtReg.capacity_grow _ 1 (Gate.PhaseProdWorkspace.zExt_canGrow _)]
      exact QubitCount.step1_zcap hmod
    · intro h; omega
    · intro _ p hp
      simp only [defaultRule, defaultPlan_2348_2049, Option.some.injEq] at hp
      subst hp
      simp [QubitCount.Rec.planFits, hrn]
      omega
  · refine siteFits_of_numbers _ _ (wx := 2348) (cx := W.capacity - 1) (wz := 2050)
      (cz := D.capacity - 2) ?_ ?_ ?_ ?_ ?_ ?_
    · rw [ExtReg.width_grow _ 1 (Gate.PhaseProdWorkspace.xExt_canGrow _)]
      show W.width + 1 = 2348
      omega
    · rw [ExtReg.capacity_grow _ 1 (Gate.PhaseProdWorkspace.xExt_canGrow _)]
      exact QubitCount.step2_xcap hmod
    · rw [ExtReg.width_grow _ 1 (Gate.PhaseProdWorkspace.zExt_canGrow _)]
      show (D.grow 1).width + 1 = 2050
      rw [ExtReg.width_grow D 1 hDg]
      omega
    · rw [ExtReg.capacity_grow _ 1 (Gate.PhaseProdWorkspace.zExt_canGrow _)]
      exact QubitCount.step2_zcap hmod
    · intro _ p hp
      simp only [defaultRule, defaultPlan_2348_2050, Option.some.injEq] at hp
      subst hp
      simp [QubitCount.Rec.planFits, hrn]
      omega
    · intro h; omega
  · refine siteFits_of_numbers _ _ (wx := 2348) (cx := W.capacity - 1) (wz := 4399)
      (cz := S.capacity - 1) ?_ ?_ ?_ ?_ ?_ ?_
    · rw [ExtReg.width_grow _ 1 (Gate.PhaseProdWorkspace.xExt_canGrow _)]
      show W.width + 1 = 2348
      omega
    · rw [ExtReg.capacity_grow _ 1 (Gate.PhaseProdWorkspace.xExt_canGrow _)]
      show regSize hs4.mulWorkspace.xReserve - 1 = _
      rw [hs4.mul_xReserve_eq]
      rfl
    · rw [ExtReg.width_grow _ 1 (Gate.PhaseProdWorkspace.zExt_canGrow _)]
      show S.width + 1 = 4399
      omega
    · rw [ExtReg.capacity_grow _ 1 (Gate.PhaseProdWorkspace.zExt_canGrow _)]
      show regSize hs4.mulWorkspace.zReserve - 1 = _
      rw [hs4.mul_zReserve_eq]
      rfl
    · intro h; omega
    · intro _ p hp
      simp only [defaultRule, defaultPlan_4399_2348, Option.some.injEq] at hp
      subst hp
      simp [QubitCount.Rec.planFits, hrn]
      omega
  · refine siteFits_of_numbers _ _ (wx := 2050) (cx := D.capacity - 2) (wz := 2348)
      (cz := W.capacity - 1) ?_ ?_ ?_ ?_ ?_ ?_
    · rw [ExtReg.width_grow _ 1 (Gate.PhaseProdWorkspace.xExt_canGrow _)]
      show (D.grow 1).width + 1 = 2050
      rw [ExtReg.width_grow D 1 hDg]
      omega
    · rw [ExtReg.capacity_grow _ 1 (Gate.PhaseProdWorkspace.xExt_canGrow _)]
      exact QubitCount.step5_xcap hmod
    · rw [ExtReg.width_grow _ 1 (Gate.PhaseProdWorkspace.zExt_canGrow _)]
      show W.width + 1 = 2348
      omega
    · rw [ExtReg.capacity_grow _ 1 (Gate.PhaseProdWorkspace.zExt_canGrow _)]
      exact QubitCount.step5_zcap hmod
    · intro h; omega
    · intro _ p hp
      simp only [defaultRule, defaultPlan_2348_2050, Option.some.injEq] at hp
      subst hp
      simp [QubitCount.Rec.planFits, hrn]
      omega

/-- At 2048 bits the reference layout's reserves fit the default rule's plan at
every site of the standard `k = 2` policy. -/
theorem reference_fits_2048 (inst : ShorOrderFindingInstance) (hN : Is2048Bit inst.N) :
    Fits standardPolicy2 defaultRule
      (orderFindingApprox inst.a inst.N
        (allocateReferenceLayout standardPolicy2 inst m2048).x
        (allocateReferenceLayout standardPolicy2 inst m2048).data
        (allocateReferenceLayout standardPolicy2 inst m2048).work
        (allocateReferenceLayout standardPolicy2 inst m2048).scratch
        (allocateReferenceLayout standardPolicy2 inst m2048).flag
        (reference_modMulCircuitWorkspaceOK standardPolicy2 inst m2048)
        (reference_step4Workspace standardPolicy2 inst m2048)) := by
  obtain ⟨hd, hw, hs, -⟩ := QubitCount.reference_widths_2048 hN
  have hdw : (allocateReferenceLayout standardPolicy2 inst m2048).data.width
      = referenceDataWidth inst :=
    allocateReferenceLayout_data_width standardPolicy2 inst m2048
  have hww : (allocateReferenceLayout standardPolicy2 inst m2048).work.width
      = referenceWorkWidth inst m2048 :=
    allocateReferenceLayout_work_width standardPolicy2 inst m2048
  have hsw : (allocateReferenceLayout standardPolicy2 inst m2048).scratch.width
      = referenceScratchWidth inst m2048 :=
    allocateReferenceLayout_scratch_width standardPolicy2 inst m2048
  have hcap := allocatedReferenceWorkspaceLargeEnough standardPolicy2 inst m2048
  have hD := hcap.data_large_enough
  have hW := hcap.auxiliary_large_enough
  have hS := hcap.scratch_large_enough
  simp only [Policy.shorWorkspaceNeed, shorWorkspaceNeedOf, hdw, hww, hsw, hd, hw, hs,
    Nat.reduceAdd, QubitCount.reserveNeed_2049_2348, QubitCount.reserveNeed_2348_2050,
    QubitCount.reserveNeed_2050_2348, QubitCount.reserveNeed_2348_4399] at hD hW hS
  exact fits_orderFindingApprox _ _ _ _ _ _ _ _ _ _ _
    (coreFits_2048 _ _ (hdw.trans hd) (hww.trans hw) (hsw.trans hs)
      (by omega) (by omega) (by omega))

/-- The reference circuit at 2048 bits, every phase-product site split. -/
def balancedUShorCircuit2048 (inst : ShorOrderFindingInstance) (hN : Is2048Bit inst.N) : LowGate :=
  orderFindingApproxLowBalancedU standardPolicy2 defaultRule inst.a inst.N
    (allocateReferenceLayout standardPolicy2 inst m2048).x
    (allocateReferenceLayout standardPolicy2 inst m2048).data
    (allocateReferenceLayout standardPolicy2 inst m2048).work
    (allocateReferenceLayout standardPolicy2 inst m2048).scratch
    (allocateReferenceLayout standardPolicy2 inst m2048).flag
    (reference_modMulCircuitWorkspaceOK standardPolicy2 inst m2048)
    (reference_step4Workspace standardPolicy2 inst m2048)
    (reference_gateWorkspaceOK standardPolicy2 inst m2048)
    (reference_fits_2048 inst hN)

theorem balancedUShorCircuit2048_eq (inst : ShorOrderFindingInstance) (hN : Is2048Bit inst.N) :
    balancedUShorCircuit2048 inst hN = balancedShorCircuit standardPolicy2 defaultRule inst m2048 := by
  unfold balancedUShorCircuit2048 orderFindingApproxLowBalancedU balancedShorCircuit
    orderFindingApproxLowBalanced
  exact lowerGate_congr _ (balanceU_eq _ (reference_fits_2048 inst hN)) _ _

section Success2048

variable (qs : QSemantics) [RegEncoding qs.Basis] [MeasureClass qs] [GateSemanticsFacts qs]
  [LowerGateClass qs]

/-- **Correctness of the reference circuit at 2048 bits with every site split**:
it achieves the reference program's declared success bound. -/
theorem balancedUShorCircuit2048_success (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T)
    (inst : ShorOrderFindingInstance) (hN : Is2048Bit inst.N) :
    referenceSuccessProbabilityAt m2048 inst.N ≤
      probability_of_success (qs := qs) (evalC := LowerGateClass.evalL (qs := qs)) (T := T)
        (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
        (x := (allocateReferenceLayout standardPolicy2 inst m2048).x.active)
        (r := ord inst.a inst.N inst.coprime)
        (Q := ASize (allocateReferenceLayout standardPolicy2 inst m2048).x.active)
        (C := balancedUShorCircuit2048 inst hN)
        (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis))) := by
  rw [balancedUShorCircuit2048_eq]
  exact balancedProgramAt_success (qs := qs) standardPolicy2 (standardPolicy_admissible 2 (by decide))
    defaultRule m2048 T hT inst

end Success2048

/-- **The qubit count of the reference circuit at 2048 bits with every site
split**: 17,291 qubits (17,290 with a 4095-qubit exponent register), and never
more than 17,291 from an empty start. -/
theorem balancedUShorCircuit2048_qubits (inst : ShorOrderFindingInstance) (hN : Is2048Bit inst.N) :
    let layout := allocateReferenceLayout standardPolicy2 inst m2048
    let L0 := orderFindingBaseSet layout.x layout.data layout.work layout.scratch layout.flag
    (referenceXWidth inst = 4096 → (balancedUShorCircuit2048 inst hN).peakQubits L0 = 17291) ∧
    (referenceXWidth inst = 4095 → (balancedUShorCircuit2048 inst hN).peakQubits L0 = 17290) ∧
    (balancedUShorCircuit2048 inst hN).peakQubits ∅ ≤ 17291 := by
  intro layout L0
  rw [balancedUShorCircuit2048_eq]
  exact QubitCount.reference2048PeakBalanced inst hN

end Balanced
end Shor
