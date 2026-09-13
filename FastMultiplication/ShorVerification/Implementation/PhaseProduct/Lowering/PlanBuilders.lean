import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Workspace
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Lowering.Plan

namespace Shor
open Gate
open Operations

/-! =========================================================
    Allocation and deallocation plan builders

    These definitions mirror the compiler constructors for moving values into
    and out of a recursive phase-product layout. Each allocation or deallocation
    gate is replaced by the corresponding primitive plan node.
========================================================= -/

/-- Plan for the allocation gate generated for one chunk. -/
def planAllocChunkGate
    {k : ℕ}
    {hk : 1 < k}
    {pts : List Point}
    {hpts : pts.length = q k}
    {ops : Prog k}
    (initSize : ℕ)
    (i : Fin k)
    (src dst : ExtReg) :
    PhaseLoweringPlan k hk pts hpts ops initSize (allocChunkGate i src dst) := by
  unfold allocChunkGate
  dsimp
  split
  · exact PhaseLoweringPlan.id initSize
  · split
    · exact
        PhaseLoweringPlan.signExtend initSize src (extraDelta src dst)
    · exact
        PhaseLoweringPlan.zeroExtend initSize src (extraDelta src dst)

/-- Plan for the deallocation gate generated for one chunk. -/
def planDeallocChunkGate
    {k : ℕ}
    {hk : 1 < k}
    {pts : List Point}
    {hpts : pts.length = q k}
    {ops : Prog k}
    (initSize : ℕ)
    (i : Fin k)
    (src dst : ExtReg) :
    PhaseLoweringPlan
      k hk pts hpts ops
      initSize
      (deallocChunkGate i src dst) := by
  unfold deallocChunkGate
  dsimp
  split
  · exact PhaseLoweringPlan.id initSize
  · split
    · exact
        PhaseLoweringPlan.signDealloc initSize src (extraDelta src dst)
    · exact
        PhaseLoweringPlan.zeroDealloc initSize src (extraDelta src dst)

/-- Plan for an allocation prefix. -/
def planCompileSignedAllocationsAux
    {k : ℕ}
    {hk : 1 < k}
    {pts : List Point}
    {hpts : pts.length = q k}
    {ops : Prog k}
    (initSize : ℕ)
    (src dst : LayoutState k) :
    ∀ (n : ℕ) (hn : n ≤ k),
      PhaseLoweringPlan k hk pts hpts ops initSize (compileSignedAllocationsAux src dst n hn)
  | 0, _ =>
      PhaseLoweringPlan.id initSize
  | n + 1, hn =>
      let hn' : n ≤ k :=  Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn

      let i : Fin k := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩

      let previous := planCompileSignedAllocationsAux initSize src dst n hn'

      let planX :=
        planAllocChunkGate (initSize := initSize) i (src.xslot i) (dst.xslot i)

      let planZ :=
        planAllocChunkGate (initSize := initSize) i (src.zslot i) (dst.zslot i)

      PhaseLoweringPlan.seq previous (PhaseLoweringPlan.seq planX planZ)

/-- Plan for the full signed allocation circuit. -/
def planCompileSignedAllocations
    {k : ℕ}
    {hk : 1 < k}
    {pts : List Point}
    {hpts : pts.length = q k}
    {ops : Prog k}
    (initSize : ℕ)
    (src dst : LayoutState k) :
    PhaseLoweringPlan k hk pts hpts ops initSize
      (compileSignedAllocations k src dst) := by
  unfold compileSignedAllocations
  exact planCompileSignedAllocationsAux initSize src dst k le_rfl

/-- Plan for a deallocation prefix. -/
def planCompileSignedDeallocationsAux
    {k : ℕ}
    {hk : 1 < k}
    {pts : List Point}
    {hpts : pts.length = q k}
    {ops : Prog k}
    (initSize : ℕ)
    (src dst : LayoutState k) :
    ∀ (n : ℕ) (hn : n ≤ k),
      PhaseLoweringPlan k hk pts hpts ops initSize
        (compileSignedDeallocationsAux src dst n hn)
  | 0, _ =>
      PhaseLoweringPlan.id initSize
  | n + 1, hn =>
      let hn' : n ≤ k :=  Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn

      let i : Fin k := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩

      let planZ := planDeallocChunkGate (initSize := initSize) i (src.zslot i) (dst.zslot i)

      let planX :=  planDeallocChunkGate (initSize := initSize) i (src.xslot i)  (dst.xslot i)

      let previous := planCompileSignedDeallocationsAux initSize src dst n hn'

      PhaseLoweringPlan.seq planZ (PhaseLoweringPlan.seq planX previous)

/-- Plan for the full signed deallocation circuit. -/
def planCompileSignedDeallocations
    {k : ℕ}
    {hk : 1 < k}
    {pts : List Point}
    {hpts : pts.length = q k}
    {ops : Prog k}
    (initSize : ℕ)
    (src dst : LayoutState k) :
    PhaseLoweringPlan  k hk pts hpts ops initSize
      (compileSignedDeallocations k src dst) := by
  unfold compileSignedDeallocations
  exact planCompileSignedDeallocationsAux initSize src dst k le_rfl

/-! =========================================================
    Annotated body plan builders

    The annotated body compiler contains ordinary arithmetic operations plus
    phase-product leaves. The caller supplies the recursive plan used at each
    leaf; these builders thread that callback through the generated body.
========================================================= -/

/-- Plan for the annotated body circuit, using `recurse` at phase-product leaves. -/
def planCompileAnnotatedOpsToSignedGateAux
    {k : ℕ}
    {hk : 1 < k}
    {pts : List Point}
    {hpts : pts.length = q k}
    {ops : Prog k}
    (initSize : ℕ)
    (phi : Angle)
    (phaseCoeff : Fin (q k) → ℚ)
    (st : LayoutState k)
    (recurse :
      ∀ (i : Fin k) (theta : Angle),
        PhaseLoweringPlan k hk pts hpts ops initSize
          (Gate.SignedPhaseProd theta (st.xslot i) (st.zslot i))) :
    ∀ annotatedOps : List (AnnotatedOp k),
      PhaseLoweringPlan k hk pts hpts ops initSize
        (compileAnnotatedOpsToSignedGateAux k hk phi phaseCoeff st annotatedOps)
  | [] =>
      PhaseLoweringPlan.id initSize
  | ⟨op, phaseTerm?⟩ :: rest =>
      let tail :=
        planCompileAnnotatedOpsToSignedGateAux initSize phi phaseCoeff st recurse rest

      match op with
      | .shiftL i n =>
          PhaseLoweringPlan.seq (PhaseLoweringPlan.ShiftL initSize (st.xslot i) n)
            (PhaseLoweringPlan.seq (PhaseLoweringPlan.ShiftL initSize (st.zslot i) n) tail)

      | .shiftR i n =>
          PhaseLoweringPlan.seq
            (PhaseLoweringPlan.ShiftR initSize (st.xslot i) n)
            (PhaseLoweringPlan.seq (PhaseLoweringPlan.ShiftR initSize (st.zslot i) n) tail)

      | .negate i =>
          PhaseLoweringPlan.seq
            (PhaseLoweringPlan.Negate initSize (st.xslot i))
            (PhaseLoweringPlan.seq (PhaseLoweringPlan.Negate initSize (st.zslot i)) tail)

      | .addScaled dst src negSrc shift =>
          PhaseLoweringPlan.seq
            (PhaseLoweringPlan.AddScaled initSize (st.xslot dst) (st.xslot src) negSrc shift)
            (PhaseLoweringPlan.seq
              (PhaseLoweringPlan.AddScaled initSize
                (st.zslot dst) (st.zslot src) negSrc shift)
              tail)

      | .phaseProduct i =>
          match phaseTerm? with
          | some l =>
              PhaseLoweringPlan.seq (recurse i (phi * phaseCoeff l)) tail
          | none =>
              tail

/-- Plan for the controlled annotated body circuit, using `recurse` at controlled phase-product leaves. -/
def planCompileAnnotatedOpsToCSignedGateAux
    {k : ℕ}
    {hk : 1 < k}
    {pts : List Point}
    {hpts : pts.length = q k}
    {ops : Prog k}
    (initSize : ℕ)
    (ctrl : ℕ)
    (phi : Angle)
    (phaseCoeff : Fin (q k) → ℚ)
    (st : LayoutState k)
    (recurse :
      ∀ (i : Fin k) (theta : Angle),
        PhaseLoweringPlan k hk pts hpts ops initSize
          (Gate.CSignedPhaseProd ctrl theta (st.xslot i) (st.zslot i))) :
    ∀ annotatedOps : List (AnnotatedOp k),
      PhaseLoweringPlan k hk pts hpts ops initSize
        (controlPhaseLeaves ctrl
          (compileAnnotatedOpsToSignedGateAux k hk phi phaseCoeff st annotatedOps))
  | [] =>
      PhaseLoweringPlan.id initSize
  | ⟨op, phaseTerm?⟩ :: rest =>
      let tail :=
        planCompileAnnotatedOpsToCSignedGateAux initSize ctrl phi phaseCoeff st recurse rest
      match op with
      | .shiftL i n =>
          PhaseLoweringPlan.seq (PhaseLoweringPlan.ShiftL initSize (st.xslot i) n)
            (PhaseLoweringPlan.seq (PhaseLoweringPlan.ShiftL initSize (st.zslot i) n) tail)
      | .shiftR i n =>
          PhaseLoweringPlan.seq (PhaseLoweringPlan.ShiftR initSize (st.xslot i) n)
            (PhaseLoweringPlan.seq (PhaseLoweringPlan.ShiftR initSize (st.zslot i) n) tail)
      | .negate i =>
          PhaseLoweringPlan.seq (PhaseLoweringPlan.Negate initSize (st.xslot i))
            (PhaseLoweringPlan.seq (PhaseLoweringPlan.Negate initSize (st.zslot i)) tail)
      | .addScaled dst src negSrc shift =>
          PhaseLoweringPlan.seq
            (PhaseLoweringPlan.AddScaled initSize (st.xslot dst) (st.xslot src) negSrc shift)
            (PhaseLoweringPlan.seq
              (PhaseLoweringPlan.AddScaled initSize (st.zslot dst) (st.zslot src) negSrc shift)
              tail)
      | .phaseProduct i =>
          match phaseTerm? with
          | some l =>
              PhaseLoweringPlan.seq (recurse i (phi * phaseCoeff l)) tail
          | none =>
              tail

/-! =========================================================
    One-level compiled phase-product plans

    A recursive step consists of allocation, the annotated body, and
    deallocation. These builders assemble those three pieces into plans for the
    compiled signed and controlled signed replacement gates.
========================================================= -/

/-- Plan for the compiled signed phase-product replacement at one recursive level. -/
def planCompiledSignedPhaseGate
    {k : ℕ}
    (hk : 1 < k)
    (pts : List Point)
    (hpts : pts.length = q k)
    (ops : Prog k)
    (phi : Angle)
    (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z k)
    (recurse :
      let src :=
        initSignedLayoutState layout
      let dst :=
        targetSignedLayoutState
          src
          (scanNeededWidths x z ops)
      ∀ (i : Fin k) (theta : Angle),
        PhaseLoweringPlan
          k hk pts hpts ops
          (nextSignedWidth x z ops)
          (Gate.SignedPhaseProd
            theta
            (dst.xslot i)
            (dst.zslot i))) :
    PhaseLoweringPlan
      k hk pts hpts ops
      (nextSignedWidth x z ops)
      (compiledSignedPhaseGate
        k hk pts hpts ops
        phi x z layout) := by
  let need : NeededWidths k :=
    scanNeededWidths x z ops
  let src : LayoutState k :=
    initSignedLayoutState layout
  let dst : LayoutState k :=
    targetSignedLayoutState src need
  let coeff : Fin (q k) → ℚ :=
    loweringPhaseCoeff
      k x z pts hpts
  let annotatedOps : List (AnnotatedOp k) :=
    annotatePhaseTermsAux k 0 ops
  have recurse' :
      ∀ (i : Fin k) (theta : Angle),
        PhaseLoweringPlan
          k hk pts hpts ops
          (nextSignedWidth x z ops)
          (Gate.SignedPhaseProd
            theta
            (dst.xslot i)
            (dst.zslot i)) := by
    simpa [src, dst, need] using recurse
  let allocationPlan :
      PhaseLoweringPlan
        k hk pts hpts ops
        (nextSignedWidth x z ops)
        (compileSignedAllocations
          k src dst) :=
    planCompileSignedAllocations
      (nextSignedWidth x z ops)
      src
      dst
  let bodyPlan :
      PhaseLoweringPlan k hk pts hpts ops
        (nextSignedWidth x z ops)
        (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst annotatedOps) :=
    planCompileAnnotatedOpsToSignedGateAux (nextSignedWidth x z ops)
      phi coeff dst recurse' annotatedOps
  let deallocationPlan :
      PhaseLoweringPlan k hk pts hpts ops
        (nextSignedWidth x z ops)
        (compileSignedDeallocations k src dst) :=
    planCompileSignedDeallocations (nextSignedWidth x z ops) src dst
  have completePlan :
      PhaseLoweringPlan
        k hk pts hpts ops
        (nextSignedWidth x z ops)
        (
          compileSignedAllocations k src dst
          ;;
          compileAnnotatedOpsToSignedGateAux
            k hk phi coeff dst annotatedOps
          ;;
          compileSignedDeallocations k src dst
        ) :=
    PhaseLoweringPlan.seq
      allocationPlan
      (PhaseLoweringPlan.seq
        bodyPlan
        deallocationPlan)
  simpa [
    compiledSignedPhaseGate,
    compileOpsToSignedGate,
    src,
    dst,
    need,
    coeff,
    annotatedOps
  ] using completePlan

/-- Plan for the compiled controlled signed phase-product replacement at one recursive level. -/
def planCompiledCSignedPhaseGate
    {k : ℕ}
    (hk : 1 < k)
    (pts : List Point)
    (hpts : pts.length = q k)
    (ops : Prog k)
    (ctrl : ℕ)
    (phi : Angle)
    (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z k)
    (recurse :
      let src := initSignedLayoutState layout
      let dst := targetSignedLayoutState src (scanNeededWidths x z ops)
      ∀ (i : Fin k) (theta : Angle),
        PhaseLoweringPlan k hk pts hpts ops (nextSignedWidth x z ops)
          (Gate.CSignedPhaseProd ctrl theta (dst.xslot i) (dst.zslot i))) :
    PhaseLoweringPlan k hk pts hpts ops (nextSignedWidth x z ops)
      (compiledCSignedPhaseGate k hk pts hpts ops ctrl phi x z layout) := by
  let need : NeededWidths k := scanNeededWidths x z ops
  let src : LayoutState k := initSignedLayoutState layout
  let dst : LayoutState k := targetSignedLayoutState src need
  let coeff : Fin (q k) → ℚ := loweringPhaseCoeff k x z pts hpts
  let annotatedOps : List (AnnotatedOp k) := annotatePhaseTermsAux k 0 ops
  have recurse' :
      ∀ (i : Fin k) (theta : Angle),
        PhaseLoweringPlan k hk pts hpts ops (nextSignedWidth x z ops)
          (Gate.CSignedPhaseProd ctrl theta (dst.xslot i) (dst.zslot i)) := by
    simpa [src, dst, need] using recurse
  let allocationPlan :
      PhaseLoweringPlan k hk pts hpts ops (nextSignedWidth x z ops)
        (compileSignedAllocations k src dst) :=
    planCompileSignedAllocations (nextSignedWidth x z ops) src dst
  let bodyPlan :
      PhaseLoweringPlan k hk pts hpts ops (nextSignedWidth x z ops)
        (controlPhaseLeaves ctrl
          (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst annotatedOps)) :=
    planCompileAnnotatedOpsToCSignedGateAux (nextSignedWidth x z ops)
      ctrl phi coeff dst recurse' annotatedOps
  let deallocationPlan :
      PhaseLoweringPlan k hk pts hpts ops (nextSignedWidth x z ops)
        (compileSignedDeallocations k src dst) :=
    planCompileSignedDeallocations (nextSignedWidth x z ops) src dst
  have completePlan :
      PhaseLoweringPlan k hk pts hpts ops (nextSignedWidth x z ops)
        (compileSignedAllocations k src dst ;;
          controlPhaseLeaves ctrl
            (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst annotatedOps) ;;
          compileSignedDeallocations k src dst) :=
    PhaseLoweringPlan.seq allocationPlan (PhaseLoweringPlan.seq bodyPlan deallocationPlan)
  simpa [compiledCSignedPhaseGate, compileOpsToCSignedGate, compileOpsToSignedGate,
    controlPhaseLeaves, controlPhaseLeaves_compileSignedAllocations,
    controlPhaseLeaves_compileSignedDeallocations, src, dst, need, coeff, annotatedOps]
    using completePlan

/-! =========================================================
    Canonical recursive phase-product plans

    The public canonical planners choose between the base case and one recursive
    compiled step using the static workspace invariant. Recursive children are
    produced from the child workspaces supplied by `CanonicalSignedStep`.
========================================================= -/

/-- Canonical recursive plan for a signed phase product from static recursive workspace data. -/
def standardSignedPhaseLoweringPlan
    (k : ℕ)
    (hk : 1 < k)
    (phi : Angle)
    (x z : ExtReg)
    (ops : Prog k)
    (hworkspace : SignedRecursiveWorkspaceOK ops x z) :
    StandardPhaseLoweringPlan k hk ops (phaseInputSize x z) (Gate.SignedPhaseProd phi x z) := by
  by_cases hrec :
      nextSignedWidth x z ops <
        phaseInputSize x z
  · let step : CanonicalSignedStep ops x z :=
      canonicalSignedStep hk ops x z hrec hworkspace
    let src : LayoutState k :=
      initSignedLayoutState step.layout
    let dst : LayoutState k :=
      targetSignedLayoutState
        src (scanNeededWidths x z ops)
    have recurse :
        ∀ (i : Fin k) (theta : Angle),
          PhaseLoweringPlan k hk (genInterpolationPoints k)
            (generatedInterpolationPoints_length k) ops
            (nextSignedWidth x z ops)
            (Gate.SignedPhaseProd theta (dst.xslot i) (dst.zslot i)) := by
      intro i theta
      have hchild :
          SignedRecursiveWorkspaceOK ops (dst.xslot i) (dst.zslot i) := by
        simpa [src, dst] using
          step.childWorkspace i
      have childPlan :=
        standardSignedPhaseLoweringPlan
          k hk theta (dst.xslot i) (dst.zslot i) ops hchild
      have hsize :
          phaseInputSize (dst.xslot i) (dst.zslot i)
            =
          nextSignedWidth x z ops := by
        simpa [src, dst] using
          step.childInputSize i
      simpa [hsize] using childPlan
    let child :
        PhaseLoweringPlan k hk (genInterpolationPoints k)
            (generatedInterpolationPoints_length k) ops
            (nextSignedWidth x z ops)
          (compiledSignedPhaseGate k hk (genInterpolationPoints k)
            (generatedInterpolationPoints_length k) ops phi x z step.layout) :=
      planCompiledSignedPhaseGate
        hk
        (genInterpolationPoints k)
        (generatedInterpolationPoints_length k)
        ops
        phi
        x
        z
        step.layout
        (by simpa [src, dst] using recurse)
    exact
      PhaseLoweringPlan.signedStep
        (k := k)
        (hk := hk)
        (pts := genInterpolationPoints k)
        (hpts :=
          generatedInterpolationPoints_length k)
        (ops := ops)
        phi
        x
        z
        step.layout
        hrec
        step.capacity
        child
  · exact
      PhaseLoweringPlan.signedBase
        (k := k)
        (hk := hk)
        (pts := genInterpolationPoints k)
        (hpts :=
          generatedInterpolationPoints_length k)
        (ops := ops)
        phi
        x
        z
        hrec
termination_by phaseInputSize x z
decreasing_by
  have hsize :
      phaseInputSize
          (dst.xslot i)
          (dst.zslot i)
        =
      nextSignedWidth x z ops := by
    simpa [src, dst] using
      step.childInputSize i
  rw [hsize]
  exact hrec

/-- Canonical recursive plan for a controlled signed phase product from static recursive workspace data. -/
def standardCSignedPhaseLoweringPlan
    (k : ℕ)
    (hk : 1 < k)
    (ctrl : ℕ)
    (phi : Angle)
    (x z : ExtReg)
    (ops : Prog k)
    (hworkspace : CSignedRecursiveWorkspaceOK ops ctrl x z) :
    StandardPhaseLoweringPlan k hk ops (phaseInputSize x z) (Gate.CSignedPhaseProd ctrl phi x z) := by
  by_cases hrec : nextSignedWidth x z ops < phaseInputSize x z
  · let step : CanonicalSignedStep ops x z :=
      canonicalSignedStep hk ops x z hrec hworkspace.toSignedRecursiveWorkspaceOK
    let src : LayoutState k := initSignedLayoutState step.layout
    let dst : LayoutState k := targetSignedLayoutState src (scanNeededWidths x z ops)
    have recurse :
        ∀ (i : Fin k) (theta : Angle),
          PhaseLoweringPlan k hk (genInterpolationPoints k) (generatedInterpolationPoints_length k)
            ops (nextSignedWidth x z ops)
            (Gate.CSignedPhaseProd ctrl theta (dst.xslot i) (dst.zslot i)) := by
      intro i theta
      have hchildSigned :
          SignedRecursiveWorkspaceOK ops (dst.xslot i) (dst.zslot i) := by
        simpa [src, dst] using step.childWorkspace i
      have hctrlLayout : step.layout.ControlDisjoint ctrl :=
        step.layout.controlDisjoint_of_ctrlDisjoint hworkspace.control_disjoint
      have hctrlDst := controlDisjoint_target step.layout ctrl (scanNeededWidths x z ops) hctrlLayout
      have hchild :
          CSignedRecursiveWorkspaceOK ops ctrl (dst.xslot i) (dst.zslot i) :=
        { toSignedRecursiveWorkspaceOK := hchildSigned
          control_disjoint := by
            constructor
            · exact (by simpa [src, dst] using hctrlDst.1 i)
            · exact (by simpa [src, dst] using hctrlDst.2 i) }
      have childPlan :=
        standardCSignedPhaseLoweringPlan k hk ctrl theta (dst.xslot i) (dst.zslot i) ops hchild
      have hsize : phaseInputSize (dst.xslot i) (dst.zslot i) = nextSignedWidth x z ops := by
        simpa [src, dst] using step.childInputSize i
      simpa [hsize] using childPlan
    let child :
        PhaseLoweringPlan k hk (genInterpolationPoints k) (generatedInterpolationPoints_length k)
          ops (nextSignedWidth x z ops)
          (compiledCSignedPhaseGate k hk (genInterpolationPoints k)
            (generatedInterpolationPoints_length k) ops ctrl phi x z step.layout) :=
      planCompiledCSignedPhaseGate hk (genInterpolationPoints k)
        (generatedInterpolationPoints_length k) ops ctrl phi x z step.layout
        (by simpa [src, dst] using recurse)
    exact
      PhaseLoweringPlan.cSignedStep
        (k := k)
        (hk := hk)
        (pts := genInterpolationPoints k)
        (hpts := generatedInterpolationPoints_length k)
        (ops := ops)
        ctrl phi x z step.layout hrec step.capacity
        (step.layout.controlDisjoint_of_ctrlDisjoint hworkspace.control_disjoint)
        child
  · exact
      PhaseLoweringPlan.cSignedBase
        (k := k)
        (hk := hk)
        (pts := genInterpolationPoints k)
        (hpts := generatedInterpolationPoints_length k)
        (ops := ops)
        ctrl phi x z hrec
termination_by phaseInputSize x z
decreasing_by
  have hsize : phaseInputSize (dst.xslot i) (dst.zslot i) = nextSignedWidth x z ops := by
    simpa [src, dst] using step.childInputSize i
  rw [hsize]
  exact hrec

end Shor
