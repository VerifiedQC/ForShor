import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Math.Table_Generation.Core.Coverage
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Lowering.PlanReadiness.AllocDeallocReadiness
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Lowering.PlanReadiness.PlanValid

namespace Shor
open Gate
open Operations

/-! =========================================================
    Recursive Signed Phase-Product Readiness
    These lemmas assemble allocation, body readiness, recursive child readiness,
    and deallocation into readiness for the canonical signed phase-product
    lowering plan. The basis-ket proof is extended to arbitrary clean states by
    linearity.
========================================================= -/

/-- Readiness of the compiled signed phase-product plan on a clean basis ket. -/
lemma planCompiledSignedPhaseGate_ready_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    {P : ShorLoweringPolicy}
    (hP : P.Admissible)
    {k : ℕ}
    (hk : 1 < k)
    (pts : List Point)
    (hpts : pts.length = q k)
    (ops : Prog k)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops pts)
    (phi : Angle)
    (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z k)
    (hlayout : layout.Valid)
    (hcapacity : (initSignedLayoutState layout).CanGrowToNeeds (neededWidthsBy P.widthRule x z ops))
    (recurse :
      let src := initSignedLayoutState layout
      let dst := targetSignedLayoutState src (neededWidthsBy P.widthRule x z ops)
      ∀ i theta,
        PhaseLoweringPlan P (nextSignedWidthBy P.widthRule x z ops)
          (Gate.SignedPhaseProd theta (dst.xslot i) (dst.zslot i)))
    (hleaf :
      let src := initSignedLayoutState layout
      let dst := targetSignedLayoutState src (neededWidthsBy P.widthRule x z ops)
      ∀ i theta b',
        RecursiveWorkspaceCleanBasis (dst.xslot i) (dst.zslot i) b' →
        PhaseLoweringReady qs (recurse i theta) (qs.ket b'))
    (b : qs.Basis)
    (hclean : RecursiveWorkspaceCleanBasis x z b) :
    PhaseLoweringReady qs
      (planCompiledSignedPhaseGate hk pts hpts ops phi x z layout recurse)
      (qs.ket b) := by
  let need : NeededWidths k := neededWidthsBy P.widthRule x z ops
  let src : LayoutState k := initSignedLayoutState layout
  let dst : LayoutState k := targetSignedLayoutState src need
  let coeff : Fin (q k) → ℚ := cramerCoeffFromPtsWidth k (phaseLimbWidth x z k) pts hpts
  let annOps := annotatePhaseTermsAux k 0 ops
  let allocPlan :=
    planCompileSignedAllocations
      (P := P) (nextSignedWidthBy P.widthRule x z ops) src dst
  let bodyPlan :=
    planCompileAnnotatedOpsToSignedGateAux
      (P := P) (hk := hk) (nextSignedWidthBy P.widthRule x z ops) phi coeff dst recurse annOps
  let deallocPlan :=
    planCompileSignedDeallocations
      (P := P) (nextSignedWidthBy P.widthRule x z ops) src dst
  have hworkspace : CompilerWorkspaceOK src need b := by
    simpa [src, need] using
      compilerWorkspaceOK_of_recursiveWorkspaceCleanBasis_by (R := P.widthRule) ops x z layout hlayout hcapacity b hclean
  rcases eval_compileSignedAllocations_ket_fits_and_child_clean_by (R := P.widthRule)
        qs ops x z layout hlayout b hworkspace hclean with
    ⟨bAlloc, hAllocEval, hEncAlloc, hAllocClean⟩
  have hFits :
      ∀ {τ : State k},
        (∃ pre rest, ops = pre ++ rest ∧ run? pre State.start_state = some τ) →
        (∀ j : Fin k, FitsSignedWidth (ExtReg.width (dst.xslot j))
          (evalRowX (qs := qs) src (τ j) b)) ∧
        (∀ j : Fin k, FitsSignedWidth (ExtReg.width (dst.zslot j))
          (evalRowZ (qs := qs) src (τ j) b)) := by
    intro τ hτ
    simpa [src, dst, need] using
      allocated_widths_sound_by (R := P.widthRule) (qs := qs) layout ops hcapacity b (σ := τ) hτ
  have hdisjoint : LayoutSlotsDisjoint dst := by
    simpa [src, dst, need] using targetSignedLayoutState_owned_disjoint hlayout need
  have hblocks : BlockDecomposition (k := k) (by omega) State.start_state ops pts :=
    progConsumesPts_has_blockDecomposition (k := k) (by omega) ops State.start_state pts hC.1
  have hBodyReady : PhaseLoweringReady qs bodyPlan (qs.ket bAlloc) := by
    apply
      planCompileAnnotatedOps_ready_ket_of_blocks_from
        qs hk hP
        (nextSignedWidthBy P.widthRule x z ops) phi coeff src dst recurse hleaf
        hblocks 0 (by simpa using hpts) b bAlloc hdisjoint hFits hC.2 hEncAlloc
    exact hAllocClean
  have hAllocReady : PhaseLoweringReady qs allocPlan (qs.ket b) :=
    planCompileSignedAllocations_ready qs (nextSignedWidthBy P.widthRule x z ops) src dst (qs.ket b)
  have hLowAlloc :
      LowerGateClass.evalL (qs := qs) (lowerGateRec allocPlan) (qs.ket b) = qs.ket bAlloc := by
    calc
      LowerGateClass.evalL (qs := qs) (lowerGateRec allocPlan) (qs.ket b)
          = qs.eval (compileSignedAllocations k src dst) (qs.ket b) := by
            exact evalL_lowerGateRec_correct (qs := qs) hP allocPlan (qs.ket b) hAllocReady
      _ = qs.ket bAlloc := hAllocEval
  have hDeallocReady :
      PhaseLoweringReady qs deallocPlan
        (LowerGateClass.evalL (qs := qs) (lowerGateRec bodyPlan) (qs.ket bAlloc)) :=
    planCompileSignedDeallocations_ready qs (nextSignedWidthBy P.widthRule x z ops) src dst _
  unfold planCompiledSignedPhaseGate Policy.stepPlan
  dsimp only
  refine ⟨hAllocReady, ?_⟩
  rw [hLowAlloc]
  exact ⟨hBodyReady, hDeallocReady⟩

/-- Readiness of the policy dispatcher on a basis ket, by well-founded
recursion on the operand width.

The lookup result is quantified over, which is what makes the two defining
equations of `Policy.signedPlanOf` usable here: `cases o` then `rw` reduces
each branch, and only the shrinking branch does any work. The step's static
facts come from `Policy.canonicalStep_spec`. -/
lemma Policy.signedPlanOf_ready_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (P : ShorLoweringPolicy)
    (hP : P.Admissible)
    (phi : Angle)
    (x z : ExtReg)
    (b : qs.Basis)
    (hstatic : Policy.WorkspaceOK P x z)
    (hclean : RecursiveWorkspaceCleanBasis x z b) :
    ∀ (n : ℕ) (o : Option ToomCookTable) (ho : P.choose (phaseInputSize x z) = o),
      PhaseLoweringReady qs (Policy.signedPlanOf P phi x z n o ho) (qs.ket b) := by
  intro n o ho
  cases o with
  | none =>
      rw [Policy.signedPlanOf]
      trivial
  | some T =>
      rw [Policy.signedPlanOf]
      split
      next hrec =>
        obtain ⟨hInterp, hC, hRun⟩ := hP.of_choose ho
        have hspec := Policy.canonicalStep_spec ho hrec hstatic
        let step : Gate.PhaseProductLayout x z T.k := Policy.canonicalStep P T x z
        let src : LayoutState T.k := initSignedLayoutState step
        let dst : LayoutState T.k := targetSignedLayoutState src (neededWidthsBy P.widthRule x z T.ops)
        have hcurrent :
            CleanWorkspaceState qs (initSignedLayoutState step)
              (neededWidthsBy P.widthRule x z T.ops) (qs.ket b) :=
          cleanWorkspaceState_ket_of_recursiveWorkspaceCleanBasis_by (R := P.widthRule) qs T.ops x z step
            hspec.valid hspec.capacity b hclean
        dsimp only
        refine ⟨⟨ho, hrec, hspec.valid, hspec.capacity⟩, hcurrent, ?_⟩
        apply
          planCompiledSignedPhaseGate_ready_ket
            (qs := qs)
            (hP := hP)
            (hk := T.hk)
            (pts := T.pts)
            (hpts := T.hpts)
            (ops := T.ops)
            (hC := hC)
            (phi := phi)
            (x := x)
            (z := z)
            (layout := step)
            (hlayout := hspec.valid)
            (hcapacity := hspec.capacity)
            (b := b)
            (hclean := hclean)
        dsimp only
        intro i theta b' hclean'
        exact Policy.signedPlanOf_ready_ket qs P hP theta (dst.xslot i) (dst.zslot i) b'
          (hspec.childWorkspace i) hclean' _ _ rfl
      next =>
        exact True.intro
termination_by phaseInputSize x z
decreasing_by
  all_goals
    refine lt_of_le_of_lt (phaseInputSize_target_le_by P.widthRule _ _ _) ?_
    assumption

/-- Readiness of the policy planner on a basis ket. -/
lemma Policy.signedPlan_ready_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (P : ShorLoweringPolicy)
    (hP : P.Admissible)
    (phi : Angle)
    (x z : ExtReg)
    (b : qs.Basis)
    (hstatic : Policy.WorkspaceOK P x z)
    (hclean : RecursiveWorkspaceCleanBasis x z b) :
    PhaseLoweringReady qs (Policy.signedPlan P phi x z) (qs.ket b) :=
  Policy.signedPlanOf_ready_ket qs P hP phi x z b hstatic hclean _ _ rfl

/-- The canonical standard plan is ready on a basis ket with clean recursive
workspace: the constant-policy instance. -/
lemma standardSignedPhaseLoweringPlan_ready_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (k : ℕ)
    (hk : 1 < k)
    (phi : Angle)
    (x z : ExtReg)
    (ops : Prog k)
    (b : qs.Basis)
    {pts : List Point}
    {hpts : pts.length = q k}
    (hstatic : SignedRecursiveWorkspaceOK ops x z)
    (hclean : RecursiveWorkspaceCleanBasis x z b)
    (hInterp : GoodToomCookPoints k pts hpts)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops pts)
    (hRun : run? ops State.start_state = some State.start_state) :
    PhaseLoweringReady qs (standardSignedPhaseLoweringPlan k hk phi x z ops pts hpts) (qs.ket b) :=
  Policy.signedPlan_ready_ket qs (ShorLoweringPolicy.constPolicy ⟨k, hk, pts, hpts, ops⟩)
    (ShorLoweringPolicy.constPolicy_admissible ⟨hInterp, hC, hRun⟩) phi x z b
    (Policy.workspaceOK_const_iff.mpr hstatic) hclean

/-- The canonical standard plan is ready and preserves recursive cleanliness on any clean state. -/
theorem standardSignedPhaseLoweringPlan_ready_and_clean
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (k : ℕ)
    (hk : 1 < k)
    (phi : Angle)
    (x z : ExtReg)
    (ops : Prog k)
    (ψ : qs.State)
    {pts : List Point}
    {hpts : pts.length = q k}
    (hstatic : SignedRecursiveWorkspaceOK ops x z)
    (hclean : RecursiveWorkspaceCleanState qs x z ψ)
    (hInterp : GoodToomCookPoints k pts hpts)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops pts)
    (hRun : run? ops State.start_state = some State.start_state) :
    let plan := standardSignedPhaseLoweringPlan k hk phi x z ops pts hpts
    PhaseLoweringReady qs plan ψ ∧
    RecursiveWorkspaceCleanState qs x z (LowerGateClass.evalL (qs := qs) (lowerGateRec plan) ψ) := by
  dsimp only
  let plan := standardSignedPhaseLoweringPlan k hk phi x z ops pts hpts
  have hready : PhaseLoweringReady qs plan ψ := by
    induction hclean with
    | zero =>
        exact PhaseLoweringReady.zero qs plan
          (Policy.signedPlan_valid _ phi x z (Policy.workspaceOK_const_iff.mpr hstatic))
    | ket b hcleanBasis =>
        exact standardSignedPhaseLoweringPlan_ready_ket qs k hk phi x z ops b
          (pts := pts) (hpts := hpts) hstatic hcleanBasis hInterp hC hRun
    | add hψ hφ ihψ ihφ => exact PhaseLoweringReady.add qs plan ihψ ihφ
    | smul a hψ ihψ => exact PhaseLoweringReady.smul qs plan a ihψ
  constructor
  · exact hready
  · exact
      standardSignedPhaseLoweringPlan_preserves_clean_of_ready qs k hk phi x z ops
        (pts := pts) (hpts := hpts) ψ hclean hready hInterp hC hRun

/-- Readiness projection from the ready-and-clean theorem. -/
theorem standardSignedPhaseLoweringPlan_ready
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (k : ℕ)
    (hk : 1 < k)
    (phi : Angle)
    (x z : ExtReg)
    (ops : Prog k)
    (ψ : qs.State)
    {pts : List Point}
    {hpts : pts.length = q k}
    (hstatic : SignedRecursiveWorkspaceOK ops x z)
    (hclean : RecursiveWorkspaceCleanState qs x z ψ)
    (hInterp : GoodToomCookPoints k pts hpts)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops pts)
    (hRun : run? ops State.start_state = some State.start_state) :
    PhaseLoweringReady qs (standardSignedPhaseLoweringPlan k hk phi x z ops pts hpts) ψ := by
  exact (standardSignedPhaseLoweringPlan_ready_and_clean qs k hk phi x z ops ψ
    (pts := pts) (hpts := hpts) hstatic hclean hInterp hC hRun).1

/-- Public workspace-state invariant implies readiness for the canonical standard plan. -/
lemma standardSignedPhaseLoweringPlan_ready_of_workspace
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (k : ℕ)
    (hk : 1 < k)
    (phi : Angle)
    (x z : ExtReg)
    (ops : Prog k)
    (ψ : qs.State)
    {pts : List Point}
    {hpts : pts.length = q k}
    (hworkspace : SignedRecursiveWorkspaceStateOK qs ops x z ψ)
    (hInterp : GoodToomCookPoints k pts hpts)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops pts)
    (hRun : run? ops State.start_state = some State.start_state):
    PhaseLoweringReady qs (standardSignedPhaseLoweringPlan k hk phi x z ops pts hpts) ψ := by
  exact standardSignedPhaseLoweringPlan_ready qs k hk phi x z ops ψ
    (pts := pts) (hpts := hpts) hworkspace.static hworkspace.clean hInterp hC hRun

/-- Readiness of the compiled controlled signed phase-product plan on a clean basis ket. -/
lemma planCompiledCSignedPhaseGate_ready_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    {P : ShorLoweringPolicy}
    (hP : P.Admissible)
    {k : ℕ}
    (hk : 1 < k)
    (pts : List Point)
    (hpts : pts.length = q k)
    (ops : Prog k)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops pts)
    (ctrl : ℕ)
    (phi : Angle)
    (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z k)
    (hlayout : layout.Valid)
    (hcapacity : (initSignedLayoutState layout).CanGrowToNeeds (neededWidthsBy P.widthRule x z ops))
    (recurse :
      let src := initSignedLayoutState layout
      let dst := targetSignedLayoutState src (neededWidthsBy P.widthRule x z ops)
      ∀ i theta,
        PhaseLoweringPlan P (nextSignedWidthBy P.widthRule x z ops)
          (Gate.CSignedPhaseProd ctrl theta (dst.xslot i) (dst.zslot i)))
    (hleaf :
      let src := initSignedLayoutState layout
      let dst := targetSignedLayoutState src (neededWidthsBy P.widthRule x z ops)
      ∀ i theta b',
        RecursiveWorkspaceCleanBasis (dst.xslot i) (dst.zslot i) b' →
        PhaseLoweringReady qs (recurse i theta) (qs.ket b'))
    (b : qs.Basis)
    (hclean : RecursiveWorkspaceCleanBasis x z b) :
    PhaseLoweringReady qs
      (planCompiledCSignedPhaseGate hk pts hpts ops ctrl phi x z layout recurse)
      (qs.ket b) := by
  let need : NeededWidths k := neededWidthsBy P.widthRule x z ops
  let src : LayoutState k := initSignedLayoutState layout
  let dst : LayoutState k := targetSignedLayoutState src need
  let coeff : Fin (q k) → ℚ := cramerCoeffFromPtsWidth k (phaseLimbWidth x z k) pts hpts
  let annOps := annotatePhaseTermsAux k 0 ops
  let allocPlan :=
    planCompileSignedAllocations
      (P := P) (nextSignedWidthBy P.widthRule x z ops) src dst
  let bodyPlan :=
    planCompileAnnotatedOpsToCSignedGateAux
      (P := P) (hk := hk) (nextSignedWidthBy P.widthRule x z ops) ctrl phi coeff dst recurse annOps
  let deallocPlan :=
    planCompileSignedDeallocations
      (P := P) (nextSignedWidthBy P.widthRule x z ops) src dst
  have hworkspace : CompilerWorkspaceOK src need b := by
    simpa [src, need] using
      compilerWorkspaceOK_of_recursiveWorkspaceCleanBasis_by (R := P.widthRule) ops x z layout hlayout hcapacity b hclean
  rcases eval_compileSignedAllocations_ket_fits_and_child_clean_by (R := P.widthRule)
        qs ops x z layout hlayout b hworkspace hclean with
    ⟨bAlloc, hAllocEval, hEncAlloc, hAllocClean⟩
  have hFits :
      ∀ {τ : State k},
        (∃ pre rest, ops = pre ++ rest ∧ run? pre State.start_state = some τ) →
        (∀ j : Fin k, FitsSignedWidth (ExtReg.width (dst.xslot j))
          (evalRowX (qs := qs) src (τ j) b)) ∧
        (∀ j : Fin k, FitsSignedWidth (ExtReg.width (dst.zslot j))
          (evalRowZ (qs := qs) src (τ j) b)) := by
    intro τ hτ
    simpa [src, dst, need] using
      allocated_widths_sound_by (R := P.widthRule) (qs := qs) layout ops hcapacity b (σ := τ) hτ
  have hdisjoint : LayoutSlotsDisjoint dst := by
    simpa [src, dst, need] using targetSignedLayoutState_owned_disjoint hlayout need
  have hblocks : BlockDecomposition (k := k) (by omega) State.start_state ops pts :=
    progConsumesPts_has_blockDecomposition (k := k) (by omega) ops State.start_state pts hC.1
  have hBodyReady : PhaseLoweringReady qs bodyPlan (qs.ket bAlloc) := by
    apply
      planCompileAnnotatedOps_c_ready_ket_of_blocks_from
        qs hk hP
        (nextSignedWidthBy P.widthRule x z ops) ctrl phi coeff src dst recurse hleaf
        hblocks 0 (by simpa using hpts) b bAlloc hdisjoint hFits hC.2 hEncAlloc
    exact hAllocClean
  have hAllocReady : PhaseLoweringReady qs allocPlan (qs.ket b) :=
    planCompileSignedAllocations_ready qs (nextSignedWidthBy P.widthRule x z ops) src dst (qs.ket b)
  have hLowAlloc :
      LowerGateClass.evalL (qs := qs) (lowerGateRec allocPlan) (qs.ket b) = qs.ket bAlloc := by
    calc
      LowerGateClass.evalL (qs := qs) (lowerGateRec allocPlan) (qs.ket b)
          = qs.eval (compileSignedAllocations k src dst) (qs.ket b) := by
            exact evalL_lowerGateRec_correct (qs := qs) hP allocPlan (qs.ket b) hAllocReady
      _ = qs.ket bAlloc := hAllocEval
  have hDeallocReady :
      PhaseLoweringReady qs deallocPlan
        (LowerGateClass.evalL (qs := qs) (lowerGateRec bodyPlan) (qs.ket bAlloc)) :=
    planCompileSignedDeallocations_ready qs (nextSignedWidthBy P.widthRule x z ops) src dst _
  have hCompleteReady :
      PhaseLoweringReady qs (PhaseLoweringPlan.seq allocPlan (PhaseLoweringPlan.seq bodyPlan deallocPlan))
        (qs.ket b) := by
    refine ⟨hAllocReady, ?_⟩
    rw [hLowAlloc]
    exact ⟨hBodyReady, hDeallocReady⟩
  unfold planCompiledCSignedPhaseGate Policy.cStepPlan
  dsimp only
  exact
    PhaseLoweringReady.cast_gate_mpr
      qs
      (by
        simp [compiledCSignedPhaseGateBy, compileOpsToSignedGateBy, compileOpsToCSignedGateBy,
          controlPhaseLeaves, controlPhaseLeaves_compileSignedAllocations,
          controlPhaseLeaves_compileSignedDeallocations])
      _
      hCompleteReady

/-- Readiness of the controlled policy dispatcher on a basis ket. -/
lemma Policy.cSignedPlanOf_ready_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (P : ShorLoweringPolicy)
    (hP : P.Admissible)
    (ctrl : ℕ)
    (phi : Angle)
    (x z : ExtReg)
    (b : qs.Basis)
    (hstatic : Policy.CWorkspaceOK P ctrl x z)
    (hclean : RecursiveWorkspaceCleanBasis x z b) :
    ∀ (n : ℕ) (o : Option ToomCookTable) (ho : P.choose (phaseInputSize x z) = o),
      PhaseLoweringReady qs (Policy.cSignedPlanOf P ctrl phi x z n o ho) (qs.ket b) := by
  intro n o ho
  cases o with
  | none =>
      rw [Policy.cSignedPlanOf]
      trivial
  | some T =>
      rw [Policy.cSignedPlanOf]
      split
      next hrec =>
        obtain ⟨hInterp, hC, hRun⟩ := hP.of_choose ho
        have hspec := Policy.canonicalStep_spec ho hrec hstatic.toWorkspaceOK
        let step : Gate.PhaseProductLayout x z T.k := Policy.canonicalStep P T x z
        let src : LayoutState T.k := initSignedLayoutState step
        let dst : LayoutState T.k := targetSignedLayoutState src (neededWidthsBy P.widthRule x z T.ops)
        have hcurrent :
            CleanWorkspaceState qs (initSignedLayoutState step)
              (neededWidthsBy P.widthRule x z T.ops) (qs.ket b) :=
          cleanWorkspaceState_ket_of_recursiveWorkspaceCleanBasis_by (R := P.widthRule) qs T.ops x z step
            hspec.valid hspec.capacity b hclean
        have hctrlLayout : step.ControlDisjoint ctrl :=
          Gate.PhaseProductLayout.controlDisjoint_of_ctrlDisjoint hspec.valid hstatic.control_disjoint
        have hctrlDst :=
          controlDisjoint_target step ctrl (neededWidthsBy P.widthRule x z T.ops) hctrlLayout
        dsimp only
        refine ⟨⟨⟨ho, hrec, hspec.valid, hspec.capacity⟩, hctrlLayout⟩, hcurrent, ?_⟩
        apply
          planCompiledCSignedPhaseGate_ready_ket
            (qs := qs)
            (hP := hP)
            (hk := T.hk)
            (pts := T.pts)
            (hpts := T.hpts)
            (ops := T.ops)
            (hC := hC)
            (ctrl := ctrl)
            (phi := phi)
            (x := x)
            (z := z)
            (layout := step)
            (hlayout := hspec.valid)
            (hcapacity := hspec.capacity)
            (b := b)
            (hclean := hclean)
        dsimp only
        intro i theta b' hclean'
        have hchild : Policy.CWorkspaceOK P ctrl (dst.xslot i) (dst.zslot i) :=
          { toWorkspaceOK := hspec.childWorkspace i
            control_disjoint := ⟨hctrlDst.1 i, hctrlDst.2 i⟩ }
        exact Policy.cSignedPlanOf_ready_ket qs P hP ctrl theta (dst.xslot i) (dst.zslot i) b'
          hchild hclean' _ _ rfl
      next =>
        exact True.intro
termination_by phaseInputSize x z
decreasing_by
  all_goals
    refine lt_of_le_of_lt (phaseInputSize_target_le_by P.widthRule _ _ _) ?_
    assumption

/-- Readiness of the controlled policy planner on a basis ket. -/
lemma Policy.cSignedPlan_ready_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (P : ShorLoweringPolicy)
    (hP : P.Admissible)
    (ctrl : ℕ)
    (phi : Angle)
    (x z : ExtReg)
    (b : qs.Basis)
    (hstatic : Policy.CWorkspaceOK P ctrl x z)
    (hclean : RecursiveWorkspaceCleanBasis x z b) :
    PhaseLoweringReady qs (Policy.cSignedPlan P ctrl phi x z) (qs.ket b) :=
  Policy.cSignedPlanOf_ready_ket qs P hP ctrl phi x z b hstatic hclean _ _ rfl

/-- The canonical controlled standard plan is ready on a basis ket with clean
recursive workspace: the constant-policy instance. -/
lemma standardCSignedPhaseLoweringPlan_ready_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (k : ℕ)
    (hk : 1 < k)
    (ctrl : ℕ)
    (phi : Angle)
    (x z : ExtReg)
    (ops : Prog k)
    (b : qs.Basis)
    {pts : List Point}
    {hpts : pts.length = q k}
    (hstatic : CSignedRecursiveWorkspaceOK ops ctrl x z)
    (hclean : RecursiveWorkspaceCleanBasis x z b)
    (hInterp : GoodToomCookPoints k pts hpts)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops pts)
    (hRun : run? ops State.start_state = some State.start_state) :
    PhaseLoweringReady qs
      (standardCSignedPhaseLoweringPlan k hk ctrl phi x z ops pts hpts)
      (qs.ket b) :=
  Policy.cSignedPlan_ready_ket qs (ShorLoweringPolicy.constPolicy ⟨k, hk, pts, hpts, ops⟩)
    (ShorLoweringPolicy.constPolicy_admissible ⟨hInterp, hC, hRun⟩) ctrl phi x z b
    (Policy.cWorkspaceOK_const_iff.mpr hstatic) hclean

/-- Readiness of the canonical controlled standard plan on any clean state. -/
theorem standardCSignedPhaseLoweringPlan_ready
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (k : ℕ)
    (hk : 1 < k)
    (ctrl : ℕ)
    (phi : Angle)
    (x z : ExtReg)
    (ops : Prog k)
    (ψ : qs.State)
    {pts : List Point}
    {hpts : pts.length = q k}
    (hstatic : CSignedRecursiveWorkspaceOK ops ctrl x z)
    (hclean : RecursiveWorkspaceCleanState qs x z ψ)
    (hInterp : GoodToomCookPoints k pts hpts)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops pts)
    (hRun : run? ops State.start_state = some State.start_state) :
    PhaseLoweringReady qs (standardCSignedPhaseLoweringPlan k hk ctrl phi x z ops pts hpts) ψ := by
  induction hclean with
  | zero => exact PhaseLoweringReady.zero qs _ (Policy.cSignedPlan_valid _ ctrl phi x z (Policy.cWorkspaceOK_const_iff.mpr hstatic))
  | ket b hcleanBasis =>
      exact standardCSignedPhaseLoweringPlan_ready_ket qs k hk ctrl phi x z ops b
        (pts := pts) (hpts := hpts) hstatic hcleanBasis hInterp hC hRun
  | add hψ hφ ihψ ihφ => exact PhaseLoweringReady.add qs _ ihψ ihφ
  | smul a hψ ihψ => exact PhaseLoweringReady.smul qs _ a ihψ

/-- Public controlled workspace-state invariant implies readiness for the canonical controlled standard plan. -/
lemma standardCSignedPhaseLoweringPlan_ready_of_workspace
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (k : ℕ)
    (hk : 1 < k)
    (ctrl : ℕ)
    (phi : Angle)
    (x z : ExtReg)
    (ops : Prog k)
    (ψ : qs.State)
    {pts : List Point}
    {hpts : pts.length = q k}
    (hworkspace : CSignedRecursiveWorkspaceStateOK qs ops ctrl x z ψ)
    (hInterp : GoodToomCookPoints k pts hpts)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops pts)
    (hRun : run? ops State.start_state = some State.start_state):
    PhaseLoweringReady qs (standardCSignedPhaseLoweringPlan k hk ctrl phi x z ops pts hpts) ψ := by
  exact standardCSignedPhaseLoweringPlan_ready qs k hk ctrl phi x z ops ψ
    (pts := pts) (hpts := hpts) hworkspace.static hworkspace.clean hInterp hC hRun

/-! =========================================================
    Readiness on arbitrary clean states

    The ket lemmas above extend to any state in the clean closure by
    linearity, exactly as in the fixed-table case.
========================================================= -/

/-- The policy plan is ready on any clean state. -/
lemma Policy.signedPlan_ready
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (P : ShorLoweringPolicy)
    (hP : P.Admissible)
    (phi : Angle)
    (x z : ExtReg)
    (ψ : qs.State)
    (hstatic : Policy.WorkspaceOK P x z)
    (hclean : RecursiveWorkspaceCleanState qs x z ψ) :
    PhaseLoweringReady qs (Policy.signedPlan P phi x z) ψ := by
  induction hclean with
  | zero => exact PhaseLoweringReady.zero qs _ (Policy.signedPlan_valid P phi x z hstatic)
  | ket b hcleanBasis =>
      exact Policy.signedPlan_ready_ket qs P hP phi x z b hstatic hcleanBasis
  | add hψ hφ ihψ ihφ => exact PhaseLoweringReady.add qs _ ihψ ihφ
  | smul a hψ ihψ => exact PhaseLoweringReady.smul qs _ a ihψ

/-- The controlled policy plan is ready on any clean state. -/
lemma Policy.cSignedPlan_ready
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (P : ShorLoweringPolicy)
    (hP : P.Admissible)
    (ctrl : ℕ)
    (phi : Angle)
    (x z : ExtReg)
    (ψ : qs.State)
    (hstatic : Policy.CWorkspaceOK P ctrl x z)
    (hclean : RecursiveWorkspaceCleanState qs x z ψ) :
    PhaseLoweringReady qs (Policy.cSignedPlan P ctrl phi x z) ψ := by
  induction hclean with
  | zero => exact PhaseLoweringReady.zero qs _ (Policy.cSignedPlan_valid P ctrl phi x z hstatic)
  | ket b hcleanBasis =>
      exact Policy.cSignedPlan_ready_ket qs P hP ctrl phi x z b hstatic hcleanBasis
  | add hψ hφ ihψ ihφ => exact PhaseLoweringReady.add qs _ ihψ ihφ
  | smul a hψ ihψ => exact PhaseLoweringReady.smul qs _ a ihψ

/-- Readiness together with preservation of reserve cleanliness, for the
policy planner. The two halves are `Policy.signedPlan_ready` and
`Policy.signedPlan_preserves_clean_of_ready`. -/
theorem Policy.signedPlan_ready_and_clean
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (P : ShorLoweringPolicy)
    (hP : P.Admissible)
    (phi : Angle)
    (x z : ExtReg)
    (ψ : qs.State)
    (hstatic : Policy.WorkspaceOK P x z)
    (hclean : RecursiveWorkspaceCleanState qs x z ψ) :
    let plan := Policy.signedPlan P phi x z
    PhaseLoweringReady qs plan ψ ∧
    RecursiveWorkspaceCleanState qs x z (LowerGateClass.evalL (qs := qs) (lowerGateRec plan) ψ) := by
  have hready := Policy.signedPlan_ready qs P hP phi x z ψ hstatic hclean
  exact ⟨hready,
    Policy.signedPlan_preserves_clean_of_ready qs P phi x z ψ hclean hready hP⟩

end Shor
