import ForShor.ShorVerification.Implementation.PhaseProduct.Statement
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Spec.Readiness
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.PolicyWorkspace

/-!
# The planner's plans are valid

The plans in `Statement.lean` are plain data: a recursive step records its
table and layout, but not why they are sound. `PhaseLoweringPlan.Valid` says
that every step's static facts hold; this file proves that the planner's output
satisfies it whenever the workspace condition holds.

The builders that assemble one step (`planCompileSignedAllocations`, the body
builders, `Policy.stepPlan`) produce valid plans whenever their recursive
callback does; the dispatcher (`Policy.signedPlanOf`) then supplies valid
children by well-founded recursion, with the facts of each step coming from
`Policy.canonicalStep_spec`.
-/

namespace Shor
open Gate
open Operations

namespace PhaseLoweringPlan

/-- Validity is unchanged by a cast of the plan's gate index. -/
lemma Valid.cast_gate_mpr
    {P : ShorLoweringPolicy}
    {initSize : ℕ}
    {U V : Gate}
    (h : V = U)
    (plan : PhaseLoweringPlan P initSize U)
    (hv : plan.Valid) :
    (Eq.mpr (congrArg (PhaseLoweringPlan P initSize) h) plan).Valid := by
  subst V
  exact hv

/-- Validity of a dependent `if` between two plans follows from validity of both branches. -/
lemma Valid.dite
    {P : ShorLoweringPolicy}
    {initSize : ℕ}
    {U : Gate}
    {c : Prop}
    {inst : Decidable c}
    {t : c → PhaseLoweringPlan P initSize U}
    {e : ¬c → PhaseLoweringPlan P initSize U}
    (ht : ∀ h, (t h).Valid)
    (he : ∀ h, (e h).Valid) :
    (@dite _ c inst t e).Valid := by
  by_cases h : c
  · rw [dite_eq_left h]; exact ht h
  · rw [dite_eq_right h]; exact he h

end PhaseLoweringPlan

/-- Allocation chunk plans contain only primitive nodes. -/
lemma planAllocChunkGate_valid
    {P : ShorLoweringPolicy}
    {k : ℕ}
    (initSize : ℕ)
    (i : Fin k)
    (src dst : ExtReg) :
    (planAllocChunkGate (P := P) initSize i src dst).Valid := by
  unfold planAllocChunkGate
  try dsimp only [_root_.id]
  apply PhaseLoweringPlan.Valid.dite
  · intro hzero
    apply PhaseLoweringPlan.Valid.cast_gate_mpr
    all_goals simp [allocChunkGate, hzero, PhaseLoweringPlan.Valid]
  · intro hzero
    apply PhaseLoweringPlan.Valid.cast_gate_mpr
    case hv =>
      apply PhaseLoweringPlan.Valid.dite
      · intro htop
        apply PhaseLoweringPlan.Valid.cast_gate_mpr
        all_goals simp [htop, PhaseLoweringPlan.Valid]
      · intro htop
        apply PhaseLoweringPlan.Valid.cast_gate_mpr
        all_goals simp [htop, PhaseLoweringPlan.Valid]
    all_goals simp [allocChunkGate, hzero]

/-- Deallocation chunk plans contain only primitive nodes. -/
lemma planDeallocChunkGate_valid
    {P : ShorLoweringPolicy}
    {k : ℕ}
    (initSize : ℕ)
    (i : Fin k)
    (src dst : ExtReg) :
    (planDeallocChunkGate (P := P) initSize i src dst).Valid := by
  unfold planDeallocChunkGate
  try dsimp only [_root_.id]
  apply PhaseLoweringPlan.Valid.dite
  · intro hzero
    apply PhaseLoweringPlan.Valid.cast_gate_mpr
    all_goals simp [deallocChunkGate, hzero, PhaseLoweringPlan.Valid]
  · intro hzero
    apply PhaseLoweringPlan.Valid.cast_gate_mpr
    case hv =>
      apply PhaseLoweringPlan.Valid.dite
      · intro htop
        apply PhaseLoweringPlan.Valid.cast_gate_mpr
        all_goals simp [htop, PhaseLoweringPlan.Valid]
      · intro htop
        apply PhaseLoweringPlan.Valid.cast_gate_mpr
        all_goals simp [htop, PhaseLoweringPlan.Valid]
    all_goals simp [deallocChunkGate, hzero]

/-- Allocation plans are valid. -/
lemma planCompileSignedAllocations_valid
    {P : ShorLoweringPolicy}
    {k : ℕ}
    (initSize : ℕ)
    (src dst : LayoutState k) :
    (planCompileSignedAllocations (P := P) initSize src dst).Valid := by
  have aux : ∀ n hn, (planCompileSignedAllocationsAux (P := P) initSize src dst n hn).Valid := by
    intro n
    induction n with
    | zero => intro hn; trivial
    | succ n ih =>
        intro hn
        dsimp only [planCompileSignedAllocationsAux]
        exact ⟨ih _, planAllocChunkGate_valid _ _ _ _, planAllocChunkGate_valid _ _ _ _⟩
  unfold planCompileSignedAllocations
  exact aux k le_rfl

/-- Deallocation plans are valid. -/
lemma planCompileSignedDeallocations_valid
    {P : ShorLoweringPolicy}
    {k : ℕ}
    (initSize : ℕ)
    (src dst : LayoutState k) :
    (planCompileSignedDeallocations (P := P) initSize src dst).Valid := by
  have aux : ∀ n hn, (planCompileSignedDeallocationsAux (P := P) initSize src dst n hn).Valid := by
    intro n
    induction n with
    | zero => intro hn; trivial
    | succ n ih =>
        intro hn
        dsimp only [planCompileSignedDeallocationsAux]
        exact ⟨planDeallocChunkGate_valid _ _ _ _, planDeallocChunkGate_valid _ _ _ _, ih _⟩
  unfold planCompileSignedDeallocations
  exact aux k le_rfl

/-- The annotated body plan is valid when every leaf plan is. -/
lemma planCompileAnnotatedOpsToSignedGateAux_valid
    {P : ShorLoweringPolicy}
    {k : ℕ}
    {hk : 1 < k}
    (initSize : ℕ)
    (phi : Angle)
    (phaseCoeff : Fin (q k) → ℚ)
    (st : LayoutState k)
    (recurse :
      ∀ (i : Fin k) (theta : Angle),
        PhaseLoweringPlan P initSize
          (Gate.SignedPhaseProd theta (st.xslot i) (st.zslot i)))
    (hrecurse : ∀ i theta, (recurse i theta).Valid) :
    ∀ annotatedOps : List (AnnotatedOp k),
      (planCompileAnnotatedOpsToSignedGateAux (hk := hk) initSize phi phaseCoeff st recurse
        annotatedOps).Valid
  | [] => trivial
  | ⟨op, phaseTerm?⟩ :: rest => by
      have ih := planCompileAnnotatedOpsToSignedGateAux_valid (hk := hk) initSize phi phaseCoeff st recurse
        hrecurse rest
      cases op with
      | shiftL i n => exact ⟨trivial, trivial, ih⟩
      | shiftR i n => exact ⟨trivial, trivial, ih⟩
      | negate i => exact ⟨trivial, trivial, ih⟩
      | addScaled dst src negSrc shift => exact ⟨trivial, trivial, ih⟩
      | phaseProduct i =>
          cases phaseTerm? with
          | some l => exact ⟨hrecurse _ _, ih⟩
          | none => exact ih

/-- The controlled annotated body plan is valid when every leaf plan is. -/
lemma planCompileAnnotatedOpsToCSignedGateAux_valid
    {P : ShorLoweringPolicy}
    {k : ℕ}
    {hk : 1 < k}
    (initSize : ℕ)
    (ctrl : ℕ)
    (phi : Angle)
    (phaseCoeff : Fin (q k) → ℚ)
    (st : LayoutState k)
    (recurse :
      ∀ (i : Fin k) (theta : Angle),
        PhaseLoweringPlan P initSize
          (Gate.CSignedPhaseProd ctrl theta (st.xslot i) (st.zslot i)))
    (hrecurse : ∀ i theta, (recurse i theta).Valid) :
    ∀ annotatedOps : List (AnnotatedOp k),
      (planCompileAnnotatedOpsToCSignedGateAux (hk := hk) initSize ctrl phi phaseCoeff st recurse
        annotatedOps).Valid
  | [] => trivial
  | ⟨op, phaseTerm?⟩ :: rest => by
      have ih := planCompileAnnotatedOpsToCSignedGateAux_valid (hk := hk) initSize ctrl phi phaseCoeff st
        recurse hrecurse rest
      cases op with
      | shiftL i n => exact ⟨trivial, trivial, ih⟩
      | shiftR i n => exact ⟨trivial, trivial, ih⟩
      | negate i => exact ⟨trivial, trivial, ih⟩
      | addScaled dst src negSrc shift => exact ⟨trivial, trivial, ih⟩
      | phaseProduct i =>
          cases phaseTerm? with
          | some l => exact ⟨hrecurse _ _, ih⟩
          | none => exact ih

/-- One recursive step's plan is valid when every child plan is. -/
lemma Policy.stepPlan_valid
    (P : ShorLoweringPolicy)
    (T : ToomCookTable)
    (phi : Angle)
    (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z T.k)
    (recurse :
      let src := initSignedLayoutState layout
      let dst := targetSignedLayoutState src (neededWidthsBy P.widthRule x z T.ops)
      ∀ (i : Fin T.k) (theta : Angle),
        PhaseLoweringPlan P (nextSignedWidthBy P.widthRule x z T.ops)
          (Gate.SignedPhaseProd theta (dst.xslot i) (dst.zslot i)))
    (hrecurse : ∀ i theta, (recurse i theta).Valid) :
    (Policy.stepPlan P T phi x z layout recurse).Valid := by
  unfold Policy.stepPlan
  dsimp only
  exact ⟨planCompileSignedAllocations_valid _ _ _,
    planCompileAnnotatedOpsToSignedGateAux_valid _ _ _ _ recurse hrecurse _,
    planCompileSignedDeallocations_valid _ _ _⟩

/-- The controlled twin. -/
lemma Policy.cStepPlan_valid
    (P : ShorLoweringPolicy)
    (T : ToomCookTable)
    (ctrl : ℕ)
    (phi : Angle)
    (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z T.k)
    (recurse :
      let src := initSignedLayoutState layout
      let dst := targetSignedLayoutState src (neededWidthsBy P.widthRule x z T.ops)
      ∀ (i : Fin T.k) (theta : Angle),
        PhaseLoweringPlan P (nextSignedWidthBy P.widthRule x z T.ops)
          (Gate.CSignedPhaseProd ctrl theta (dst.xslot i) (dst.zslot i)))
    (hrecurse : ∀ i theta, (recurse i theta).Valid) :
    (Policy.cStepPlan P T ctrl phi x z layout recurse).Valid := by
  unfold Policy.cStepPlan
  dsimp only
  exact
    PhaseLoweringPlan.Valid.cast_gate_mpr
      (by
        simp [compiledCSignedPhaseGateBy, compileOpsToCSignedGateBy, compileOpsToSignedGateBy,
          controlPhaseLeaves, controlPhaseLeaves_compileSignedAllocations,
          controlPhaseLeaves_compileSignedDeallocations])
      _
      ⟨planCompileSignedAllocations_valid _ _ _,
        planCompileAnnotatedOpsToCSignedGateAux_valid _ _ _ _ _ recurse hrecurse _,
        planCompileSignedDeallocations_valid _ _ _⟩

/-- The dispatcher's plan is valid whenever the workspace fits. -/
theorem Policy.signedPlanOf_valid
    (P : ShorLoweringPolicy)
    (phi : Angle)
    (x z : ExtReg)
    (n : ℕ)
    (hworkspace : Policy.WorkspaceOK P x z) :
    ∀ (o : Option ToomCookTable) (ho : P.choose (phaseInputSize x z) = o),
      (Policy.signedPlanOf P phi x z n o ho).Valid := by
  intro o ho
  cases o with
  | none =>
      rw [Policy.signedPlanOf]
      exact fun T hT => by rw [ho] at hT; simp at hT
  | some T =>
      rw [Policy.signedPlanOf]
      split
      next hrec =>
        have hspec := Policy.canonicalStep_spec ho hrec hworkspace
        refine ⟨⟨ho, hrec, hspec.valid, hspec.capacity⟩, ?_⟩
        apply Policy.stepPlan_valid
        intro i theta
        exact Policy.signedPlanOf_valid P theta _ _ _ (hspec.childWorkspace i) _ rfl
      next hstop =>
        exact fun T' hT' => by rw [ho] at hT'; cases hT'; exact hstop
termination_by phaseInputSize x z
decreasing_by
  all_goals
    refine lt_of_le_of_lt (phaseInputSize_target_le_by P.widthRule _ _ _) ?_
    assumption

/-- The controlled dispatcher's plan is valid whenever the workspace fits. -/
theorem Policy.cSignedPlanOf_valid
    (P : ShorLoweringPolicy)
    (ctrl : ℕ)
    (phi : Angle)
    (x z : ExtReg)
    (n : ℕ)
    (hworkspace : Policy.CWorkspaceOK P ctrl x z) :
    ∀ (o : Option ToomCookTable) (ho : P.choose (phaseInputSize x z) = o),
      (Policy.cSignedPlanOf P ctrl phi x z n o ho).Valid := by
  intro o ho
  cases o with
  | none =>
      rw [Policy.cSignedPlanOf]
      exact fun T hT => by rw [ho] at hT; simp at hT
  | some T =>
      rw [Policy.cSignedPlanOf]
      split
      next hrec =>
        have hspec := Policy.canonicalStep_spec ho hrec hworkspace.toWorkspaceOK
        have hctrl : (Policy.canonicalStep P T x z).ControlDisjoint ctrl :=
          Gate.PhaseProductLayout.controlDisjoint_of_ctrlDisjoint hspec.valid hworkspace.control_disjoint
        have hctrlDst :=
          controlDisjoint_target (Policy.canonicalStep P T x z) ctrl
            (neededWidthsBy P.widthRule x z T.ops) hctrl
        refine ⟨⟨⟨ho, hrec, hspec.valid, hspec.capacity⟩, hctrl⟩, ?_⟩
        apply Policy.cStepPlan_valid
        intro i theta
        exact Policy.cSignedPlanOf_valid P ctrl theta _ _ _
          { toWorkspaceOK := hspec.childWorkspace i
            control_disjoint := ⟨hctrlDst.1 i, hctrlDst.2 i⟩ } _ rfl
      next hstop =>
        exact fun T' hT' => by rw [ho] at hT'; cases hT'; exact hstop
termination_by phaseInputSize x z
decreasing_by
  all_goals
    refine lt_of_le_of_lt (phaseInputSize_target_le_by P.widthRule _ _ _) ?_
    assumption

/-- The policy plan is valid whenever the workspace fits. -/
theorem Policy.signedPlan_valid
    (P : ShorLoweringPolicy) (phi : Angle) (x z : ExtReg) (hworkspace : Policy.WorkspaceOK P x z) :
    (Policy.signedPlan P phi x z).Valid :=
  Policy.signedPlanOf_valid P phi x z _ hworkspace _ rfl

/-- The controlled policy plan is valid whenever the workspace fits. -/
theorem Policy.cSignedPlan_valid
    (P : ShorLoweringPolicy) (ctrl : ℕ) (phi : Angle) (x z : ExtReg)
    (hworkspace : Policy.CWorkspaceOK P ctrl x z) :
    (Policy.cSignedPlan P ctrl phi x z).Valid :=
  Policy.cSignedPlanOf_valid P ctrl phi x z _ hworkspace _ rfl

end Shor
