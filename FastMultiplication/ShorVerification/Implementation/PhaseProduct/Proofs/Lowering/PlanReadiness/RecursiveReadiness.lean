import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.Lowering.PlanReadiness.AllocDeallocReadiness

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
    {k : ℕ}
    (hk : 1 < k)
    (pts : List Point)
    (hpts : pts.length = q k)
    (hInterp : GoodToomCookPoints k pts hpts)
    (ops : Prog k)
    (hC :
      ProgConsumesPtsSafe
        (k := k)
        (by omega)
        State.start_state
        ops
        pts)
    (hRun :
      run? ops State.start_state =
        some State.start_state)
    (phi : Angle)
    (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z k)
    (hcapacity :
      (initSignedLayoutState layout).CanGrowToNeeds
        (scanNeededWidths x z ops))
    (recurse :
      let src := initSignedLayoutState layout
      let dst :=
        targetSignedLayoutState src
          (scanNeededWidths x z ops)
      ∀ i theta,
        PhaseLoweringPlan
          k hk pts hpts ops
          (nextSignedWidth x z ops)
          (Gate.SignedPhaseProd
            theta
            (dst.xslot i)
            (dst.zslot i)))
    (hleaf :
      let src := initSignedLayoutState layout
      let dst :=
        targetSignedLayoutState src
          (scanNeededWidths x z ops)
      ∀ i theta b',
        RecursiveWorkspaceCleanBasis
            (dst.xslot i) (dst.zslot i) b' →
        PhaseLoweringReady
          qs (recurse i theta) (qs.ket b'))
    (b : qs.Basis)
    (hclean : RecursiveWorkspaceCleanBasis x z b) :
    PhaseLoweringReady
      qs
      (planCompiledSignedPhaseGate
        hk pts hpts ops phi x z layout recurse)
      (qs.ket b) := by
  let need : NeededWidths k :=
    scanNeededWidths x z ops
  let src : LayoutState k :=
    initSignedLayoutState layout
  let dst : LayoutState k :=
    targetSignedLayoutState src need
  let coeff : Fin (q k) → ℚ :=
    loweringPhaseCoeff k x z pts hpts
  let annOps :=
    annotatePhaseTermsAux k 0 ops
  let allocPlan :=
    planCompileSignedAllocations
      (hk := hk) (pts := pts) (hpts := hpts) (ops := ops)
      (nextSignedWidth x z ops) src dst
  let bodyPlan :=
    planCompileAnnotatedOpsToSignedGateAux
      (hk := hk) (pts := pts) (hpts := hpts) (ops := ops)
      (nextSignedWidth x z ops)
      phi coeff dst recurse annOps
  let deallocPlan :=
    planCompileSignedDeallocations
      (hk := hk) (pts := pts) (hpts := hpts) (ops := ops)
      (nextSignedWidth x z ops) src dst
  have hworkspace :
      CompilerWorkspaceOK src need b := by
    simpa [src, need] using
      compilerWorkspaceOK_of_recursiveWorkspaceCleanBasis ops x z layout hcapacity b hclean
  rcases
      eval_compileSignedAllocations_ket_fits_and_child_clean
        qs ops x z layout b hworkspace hclean
    with ⟨bAlloc, hAllocEval, hEncAlloc, hAllocClean⟩
  have hFits :
      ∀ {τ : State k},
        (∃ pre rest,
          ops = pre ++ rest ∧
          run? pre State.start_state = some τ) →
        (∀ j : Fin k,
          FitsSignedWidth
            (ExtReg.width (dst.xslot j))
            (evalRowX
              (qs := qs) src (τ j) b))
        ∧
        (∀ j : Fin k,
          FitsSignedWidth
            (ExtReg.width (dst.zslot j))
            (evalRowZ
              (qs := qs) src (τ j) b)) := by
    intro τ hτ
    simpa [src, dst, need] using
      allocated_widths_sound
        (qs := qs)
        layout
        ops
        hcapacity
        b
        (σ := τ)
        hτ
  have hdisjoint : LayoutSlotsDisjoint dst := by
    simpa [src, dst, need] using
      targetSignedLayoutState_owned_disjoint layout need
  have hblocks :
      BlockDecomposition
        (k := k)
        (by omega)
        State.start_state
        ops
        pts :=
    progConsumesPts_has_blockDecomposition
      (k := k)
      (by omega)
      ops
      State.start_state
      pts
      hC.1
  have hBodyReady :
      PhaseLoweringReady qs bodyPlan (qs.ket bAlloc) := by
    apply
      planCompileAnnotatedOps_ready_ket_of_blocks_from
        qs hk pts hpts hInterp
        ops hC hRun
        (nextSignedWidth x z ops)
        phi coeff src dst recurse hleaf
        hblocks
        0
        (by simpa using hpts)
        b
        bAlloc
        hdisjoint
        hFits
        hC.2
        hEncAlloc
    exact hAllocClean
  have hAllocReady :
      PhaseLoweringReady qs allocPlan (qs.ket b) :=
    planCompileSignedAllocations_ready
      qs hk pts hpts ops
      (nextSignedWidth x z ops)
      src dst
      (qs.ket b)
  have hLowAlloc :
      LowerGateClass.evalL
          (qs := qs)
          (lowerGateRec allocPlan)
          (qs.ket b)
        =
      qs.ket bAlloc := by
    calc
      LowerGateClass.evalL
          (qs := qs)
          (lowerGateRec allocPlan)
          (qs.ket b)
          =
        qs.eval
          (compileSignedAllocations k src dst)
          (qs.ket b) := by
            exact
              evalL_lowerGateRec_correct
                (qs := qs)
                (hInterp := hInterp)
                (hC := hC)
                (hRun := hRun)
                allocPlan
                (qs.ket b)
                hAllocReady
      _ = qs.ket bAlloc := hAllocEval
  have hDeallocReady :
      PhaseLoweringReady
        qs
        deallocPlan
        (LowerGateClass.evalL
          (qs := qs)
          (lowerGateRec bodyPlan)
          (qs.ket bAlloc)) :=
    planCompileSignedDeallocations_ready
      qs hk pts hpts ops
      (nextSignedWidth x z ops)
      src dst
      _
  unfold planCompiledSignedPhaseGate
  dsimp only
  refine ⟨hAllocReady, ?_⟩
  rw [hLowAlloc]
  exact ⟨hBodyReady, hDeallocReady⟩

/-- The canonical standard plan is ready on a basis ket with clean recursive workspace. -/
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
    (hstatic :
      SignedRecursiveWorkspaceOK ops x z)
    (hclean :
      RecursiveWorkspaceCleanBasis x z b)
    (hC :
      ProgConsumesPtsSafe
        (k := k)
        (by omega)
        State.start_state
        ops
        (genInterpolationPoints k))
    (hRun :
      run? ops State.start_state =
        some State.start_state) :
    PhaseLoweringReady
      qs
      (standardSignedPhaseLoweringPlan
        k hk phi x z ops hstatic)
      (qs.ket b) := by
  rw [standardSignedPhaseLoweringPlan]
  split
  next hrec =>
    let step : CanonicalSignedStep ops x z :=
      canonicalSignedStep
        hk ops x z hrec hstatic
    let src : LayoutState k :=
      initSignedLayoutState step.layout
    let dst : LayoutState k :=
      targetSignedLayoutState
        src
        (scanNeededWidths x z ops)
    have hcurrent :
        CleanWorkspaceState
          qs
          (initSignedLayoutState step.layout)
          (scanNeededWidths x z ops)
          (qs.ket b) :=
      cleanWorkspaceState_ket_of_recursiveWorkspaceCleanBasis
        qs
        ops
        x
        z
        step.layout
        step.capacity
        b
        hclean
    dsimp only
    refine And.intro hcurrent ?_
    apply
      planCompiledSignedPhaseGate_ready_ket
        (qs := qs)
        (hk := hk)
        (pts := genInterpolationPoints k)
        (hpts :=
          generatedInterpolationPoints_length k)
        (hInterp := by
          simpa using genInterpolationPoints_good k)
        (ops := ops)
        (hC := hC)
        (hRun := hRun)
        (phi := phi)
        (x := x)
        (z := z)
        (layout := step.layout)
        (hcapacity := step.capacity)
        (b := b)
        (hclean := hclean)
    dsimp only
    intro i theta b' hclean'
    have hchild :
        SignedRecursiveWorkspaceOK
          ops
          (dst.xslot i)
          (dst.zslot i) := by
      simpa [src, dst] using
        step.childWorkspace i
    have hsize :
        phaseInputSize
            (dst.xslot i)
            (dst.zslot i)
          =
        nextSignedWidth x z ops := by
      simpa [src, dst] using
        step.childInputSize i
    have hchildReady :
        PhaseLoweringReady
          qs
          (standardSignedPhaseLoweringPlan
            k
            hk
            theta
            (dst.xslot i)
            (dst.zslot i)
            ops
            hchild)
          (qs.ket b') := by
      exact
        standardSignedPhaseLoweringPlan_ready_ket
          (qs := qs)
          (k := k)
          (hk := hk)
          (phi := theta)
          (x := dst.xslot i)
          (z := dst.zslot i)
          (ops := ops)
          (b := b')
          (hstatic := hchild)
          (hclean := hclean')
          (hC := hC)
          (hRun := hRun)
    dsimp only [id_eq]
    convert hchildReady using 2
    all_goals
      first
        | exact hsize.symm
        | (rw [eq_mp_eq_cast]; exact cast_heq _ _)
  next hstop =>
    exact True.intro
termination_by phaseInputSize x z
decreasing_by
  have hsize :
      phaseInputSize (dst.xslot i) (dst.zslot i) = nextSignedWidth x z ops := by
    simpa [src, dst] using step.childInputSize i
  rw [hsize]
  assumption

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
    (hstatic :
      SignedRecursiveWorkspaceOK ops x z)
    (hclean :
      RecursiveWorkspaceCleanState qs x z ψ)
    (hC :
      ProgConsumesPtsSafe
        (k := k)
        (by omega)
        State.start_state
        ops
        (genInterpolationPoints k))
    (hRun :
      run? ops State.start_state =
        some State.start_state) :
    let plan :=
      standardSignedPhaseLoweringPlan
        k hk phi x z ops hstatic
    PhaseLoweringReady qs plan ψ
      ∧
    RecursiveWorkspaceCleanState
      qs x z
      (LowerGateClass.evalL
        (qs := qs)
        (lowerGateRec plan)
        ψ) := by
  dsimp only
  let plan :=
    standardSignedPhaseLoweringPlan
      k hk phi x z ops hstatic
  have hready :
      PhaseLoweringReady qs plan ψ := by
    induction hclean with
    | zero =>
        exact
          PhaseLoweringReady.zero
            qs plan
    | ket b hcleanBasis =>
        exact
          standardSignedPhaseLoweringPlan_ready_ket
            qs
            k
            hk
            phi
            x
            z
            ops
            b
            hstatic
            hcleanBasis
            hC
            hRun
    | add hψ hφ ihψ ihφ =>
        exact
          PhaseLoweringReady.add
            qs plan ihψ ihφ
    | smul a hψ ihψ =>
        exact
          PhaseLoweringReady.smul
            qs plan a ihψ
  constructor
  · exact hready
  · exact
      standardSignedPhaseLoweringPlan_preserves_clean_of_ready
        qs
        k
        hk
        phi
        x
        z
        ops
        ψ
        hstatic
        hclean
        hready
        hC
        hRun

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
    (hstatic : SignedRecursiveWorkspaceOK ops x z)
    (hclean : RecursiveWorkspaceCleanState qs x z ψ)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops (genInterpolationPoints k))
    (hRun : run? ops State.start_state = some State.start_state) :
    PhaseLoweringReady qs (standardSignedPhaseLoweringPlan k hk phi x z ops hstatic) ψ := by
  exact
    (standardSignedPhaseLoweringPlan_ready_and_clean qs k hk phi x z ops ψ
      hstatic
      hclean
      hC
      hRun).1

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
    (hworkspace : SignedRecursiveWorkspaceStateOK qs ops x z ψ)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops (genInterpolationPoints k))
    (hRun : run? ops State.start_state = some State.start_state):
    PhaseLoweringReady qs (standardSignedPhaseLoweringPlan k hk phi x z ops hworkspace.static) ψ := by
  exact
    standardSignedPhaseLoweringPlan_ready qs k hk phi x z ops ψ
      hworkspace.static hworkspace.clean hC hRun


/-- Readiness of the compiled controlled signed phase-product plan on a clean basis ket. -/
lemma planCompiledCSignedPhaseGate_ready_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    {k : ℕ}
    (hk : 1 < k)
    (pts : List Point)
    (hpts : pts.length = q k)
    (hInterp : GoodToomCookPoints k pts hpts)
    (ops : Prog k)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops pts)
    (hRun : run? ops State.start_state = some State.start_state)
    (ctrl : ℕ)
    (phi : Angle)
    (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z k)
    (hcapacity : (initSignedLayoutState layout).CanGrowToNeeds (scanNeededWidths x z ops))
    (recurse :
      let src := initSignedLayoutState layout
      let dst := targetSignedLayoutState src (scanNeededWidths x z ops)
      ∀ i theta,
        PhaseLoweringPlan k hk pts hpts ops (nextSignedWidth x z ops)
          (Gate.CSignedPhaseProd ctrl theta (dst.xslot i) (dst.zslot i)))
    (hleaf :
      let src := initSignedLayoutState layout
      let dst := targetSignedLayoutState src (scanNeededWidths x z ops)
      ∀ i theta b',
        RecursiveWorkspaceCleanBasis (dst.xslot i) (dst.zslot i) b' →
        PhaseLoweringReady qs (recurse i theta) (qs.ket b'))
    (b : qs.Basis)
    (hclean : RecursiveWorkspaceCleanBasis x z b) :
    PhaseLoweringReady qs
      (planCompiledCSignedPhaseGate hk pts hpts ops ctrl phi x z layout recurse)
      (qs.ket b) := by
  let need : NeededWidths k := scanNeededWidths x z ops
  let src : LayoutState k := initSignedLayoutState layout
  let dst : LayoutState k := targetSignedLayoutState src need
  let coeff : Fin (q k) → ℚ := loweringPhaseCoeff k x z pts hpts
  let annOps := annotatePhaseTermsAux k 0 ops
  let allocPlan :=
    planCompileSignedAllocations
      (hk := hk) (pts := pts) (hpts := hpts) (ops := ops)
      (nextSignedWidth x z ops) src dst
  let bodyPlan :=
    planCompileAnnotatedOpsToCSignedGateAux
      (hk := hk) (pts := pts) (hpts := hpts) (ops := ops)
      (nextSignedWidth x z ops) ctrl phi coeff dst recurse annOps
  let deallocPlan :=
    planCompileSignedDeallocations
      (hk := hk) (pts := pts) (hpts := hpts) (ops := ops)
      (nextSignedWidth x z ops) src dst
  have hworkspace : CompilerWorkspaceOK src need b := by
    simpa [src, need] using
      compilerWorkspaceOK_of_recursiveWorkspaceCleanBasis ops x z layout hcapacity b hclean
  rcases eval_compileSignedAllocations_ket_fits_and_child_clean
        qs ops x z layout b hworkspace hclean with
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
      allocated_widths_sound (qs := qs) layout ops hcapacity b (σ := τ) hτ
  have hdisjoint : LayoutSlotsDisjoint dst := by
    simpa [src, dst, need] using targetSignedLayoutState_owned_disjoint layout need
  have hblocks : BlockDecomposition (k := k) (by omega) State.start_state ops pts :=
    progConsumesPts_has_blockDecomposition (k := k) (by omega) ops State.start_state pts hC.1
  have hBodyReady : PhaseLoweringReady qs bodyPlan (qs.ket bAlloc) := by
    apply
      planCompileAnnotatedOps_c_ready_ket_of_blocks_from
        qs hk pts hpts hInterp ops hC hRun
        (nextSignedWidth x z ops) ctrl phi coeff src dst recurse hleaf
        hblocks 0 (by simpa using hpts) b bAlloc hdisjoint hFits hC.2 hEncAlloc
    exact hAllocClean
  have hAllocReady : PhaseLoweringReady qs allocPlan (qs.ket b) :=
    planCompileSignedAllocations_ready qs hk pts hpts ops (nextSignedWidth x z ops) src dst (qs.ket b)
  have hLowAlloc :
      LowerGateClass.evalL (qs := qs) (lowerGateRec allocPlan) (qs.ket b) = qs.ket bAlloc := by
    calc
      LowerGateClass.evalL (qs := qs) (lowerGateRec allocPlan) (qs.ket b)
          = qs.eval (compileSignedAllocations k src dst) (qs.ket b) := by
            exact evalL_lowerGateRec_correct (qs := qs) (hInterp := hInterp)
              (hC := hC) (hRun := hRun) allocPlan (qs.ket b) hAllocReady
      _ = qs.ket bAlloc := hAllocEval
  have hDeallocReady :
      PhaseLoweringReady qs deallocPlan
        (LowerGateClass.evalL (qs := qs) (lowerGateRec bodyPlan) (qs.ket bAlloc)) :=
    planCompileSignedDeallocations_ready qs hk pts hpts ops (nextSignedWidth x z ops) src dst _
  have hCompleteReady :
      PhaseLoweringReady qs (PhaseLoweringPlan.seq allocPlan (PhaseLoweringPlan.seq bodyPlan deallocPlan))
        (qs.ket b) := by
    refine ⟨hAllocReady, ?_⟩
    rw [hLowAlloc]
    exact ⟨hBodyReady, hDeallocReady⟩
  unfold planCompiledCSignedPhaseGate
  dsimp only
  exact
    PhaseLoweringReady.cast_gate_mpr
      qs
      (by
        simp [compiledCSignedPhaseGate, compileOpsToCSignedGate, compileOpsToSignedGate,
          controlPhaseLeaves, controlPhaseLeaves_compileSignedAllocations,
          controlPhaseLeaves_compileSignedDeallocations])
      _
      hCompleteReady

/-- The canonical controlled standard plan is ready on a basis ket with clean recursive workspace. -/
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
    (hstatic : CSignedRecursiveWorkspaceOK ops ctrl x z)
    (hclean : RecursiveWorkspaceCleanBasis x z b)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops (genInterpolationPoints k))
    (hRun : run? ops State.start_state = some State.start_state) :
    PhaseLoweringReady qs
      (standardCSignedPhaseLoweringPlan k hk ctrl phi x z ops hstatic)
      (qs.ket b) := by
  rw [standardCSignedPhaseLoweringPlan]
  split
  next hrec =>
    let step : CanonicalSignedStep ops x z :=
      canonicalSignedStep hk ops x z hrec hstatic.toSignedRecursiveWorkspaceOK
    let src : LayoutState k := initSignedLayoutState step.layout
    let dst : LayoutState k := targetSignedLayoutState src (scanNeededWidths x z ops)
    have hcurrent :
        CleanWorkspaceState qs (initSignedLayoutState step.layout)
          (scanNeededWidths x z ops) (qs.ket b) :=
      cleanWorkspaceState_ket_of_recursiveWorkspaceCleanBasis qs ops x z step.layout step.capacity b hclean
    dsimp only
    refine And.intro hcurrent ?_
    apply
      planCompiledCSignedPhaseGate_ready_ket
        (qs := qs)
        (hk := hk)
        (pts := genInterpolationPoints k)
        (hpts := generatedInterpolationPoints_length k)
        (hInterp := by simpa using genInterpolationPoints_good k)
        (ops := ops)
        (hC := hC)
        (hRun := hRun)
        (ctrl := ctrl)
        (phi := phi)
        (x := x)
        (z := z)
        (layout := step.layout)
        (hcapacity := step.capacity)
        (b := b)
        (hclean := hclean)
    dsimp only
    intro i theta b' hclean'
    have hchildSigned : SignedRecursiveWorkspaceOK ops (dst.xslot i) (dst.zslot i) := by
      simpa [src, dst] using step.childWorkspace i
    have hctrlLayout : step.layout.ControlDisjoint ctrl :=
      step.layout.controlDisjoint_of_ctrlDisjoint hstatic.control_disjoint
    have hctrlDst := controlDisjoint_target step.layout ctrl (scanNeededWidths x z ops) hctrlLayout
    have hchild : CSignedRecursiveWorkspaceOK ops ctrl (dst.xslot i) (dst.zslot i) :=
      { toSignedRecursiveWorkspaceOK := hchildSigned
        control_disjoint := by
          constructor
          · exact (by simpa [src, dst] using hctrlDst.1 i)
          · exact (by simpa [src, dst] using hctrlDst.2 i) }
    have hsize : phaseInputSize (dst.xslot i) (dst.zslot i) = nextSignedWidth x z ops := by
      simpa [src, dst] using step.childInputSize i
    have hchildReady :
        PhaseLoweringReady qs
          (standardCSignedPhaseLoweringPlan k hk ctrl theta (dst.xslot i) (dst.zslot i) ops hchild)
          (qs.ket b') := by
      exact standardCSignedPhaseLoweringPlan_ready_ket (qs := qs) (k := k) (hk := hk)
        (ctrl := ctrl) (phi := theta) (x := dst.xslot i) (z := dst.zslot i)
        (ops := ops) (b := b') (hstatic := hchild) (hclean := hclean') (hC := hC) (hRun := hRun)
    dsimp only [id_eq]
    convert hchildReady using 2
    all_goals
      first
        | exact hsize.symm
        | (rw [eq_mp_eq_cast]; exact cast_heq _ _)
  next hstop =>
    exact True.intro
termination_by phaseInputSize x z
decreasing_by
  have hsize : phaseInputSize (dst.xslot i) (dst.zslot i) = nextSignedWidth x z ops := by
    simpa [src, dst] using step.childInputSize i
  rw [hsize]
  assumption

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
    (hstatic : CSignedRecursiveWorkspaceOK ops ctrl x z)
    (hclean : RecursiveWorkspaceCleanState qs x z ψ)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops (genInterpolationPoints k))
    (hRun : run? ops State.start_state = some State.start_state) :
    PhaseLoweringReady qs (standardCSignedPhaseLoweringPlan k hk ctrl phi x z ops hstatic) ψ := by
  induction hclean with
  | zero => exact PhaseLoweringReady.zero qs _
  | ket b hcleanBasis =>
      exact standardCSignedPhaseLoweringPlan_ready_ket qs k hk ctrl phi x z ops b hstatic hcleanBasis hC hRun
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
    (hworkspace : CSignedRecursiveWorkspaceStateOK qs ops ctrl x z ψ)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops (genInterpolationPoints k))
    (hRun : run? ops State.start_state = some State.start_state):
    PhaseLoweringReady qs (standardCSignedPhaseLoweringPlan k hk ctrl phi x z ops hworkspace.static) ψ := by
  exact standardCSignedPhaseLoweringPlan_ready qs k hk ctrl phi x z ops ψ
    hworkspace.static hworkspace.clean hC hRun


end Shor
