import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Workspace
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.PolicyWorkspace
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Lowering.Plan

namespace Shor
open Gate
open Operations

/-! =========================================================
    Allocation and deallocation plan builders

    These definitions mirror the compiler constructors for moving values into
    and out of a recursive phase-product layout. Each allocation or deallocation
    gate is replaced by the corresponding primitive plan node.

    None of them mentions the table: they build primitive plan nodes, whose
    shapes are unchanged by policy indexing. The five table parameters are
    replaced by a single `{P}`, and `{k}` now comes from the gate rather than
    from the plan, so every call site is unaffected.
========================================================= -/

/-- Plan for the allocation gate generated for one chunk. -/
def planAllocChunkGate
    {P : ShorLoweringPolicy}
    {k : ℕ}
    (initSize : ℕ)
    (i : Fin k)
    (src dst : ExtReg) :
    PhaseLoweringPlan P initSize (allocChunkGate i src dst) := by
  unfold allocChunkGate
  dsimp
  split
  · exact PhaseLoweringPlan.id initSize
  · split
    · exact PhaseLoweringPlan.signExtend initSize src (extraDelta src dst)
    · exact PhaseLoweringPlan.zeroExtend initSize src (extraDelta src dst)

/-- Plan for the deallocation gate generated for one chunk. -/
def planDeallocChunkGate
    {P : ShorLoweringPolicy}
    {k : ℕ}
    (initSize : ℕ)
    (i : Fin k)
    (src dst : ExtReg) :
    PhaseLoweringPlan P initSize (deallocChunkGate i src dst) := by
  unfold deallocChunkGate
  dsimp
  split
  · exact PhaseLoweringPlan.id initSize
  · split
    · exact PhaseLoweringPlan.signDealloc initSize src (extraDelta src dst)
    · exact PhaseLoweringPlan.zeroDealloc initSize src (extraDelta src dst)

/-- Plan for an allocation prefix. -/
def planCompileSignedAllocationsAux
    {P : ShorLoweringPolicy}
    {k : ℕ}
    (initSize : ℕ)
    (src dst : LayoutState k) :
    ∀ (n : ℕ) (hn : n ≤ k),
      PhaseLoweringPlan P initSize (compileSignedAllocationsAux src dst n hn)
  | 0, _ =>
      PhaseLoweringPlan.id initSize
  | n + 1, hn =>
      let hn' : n ≤ k := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn
      let i : Fin k := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
      let previous := planCompileSignedAllocationsAux initSize src dst n hn'
      let planX := planAllocChunkGate (initSize := initSize) i (src.xslot i) (dst.xslot i)
      let planZ := planAllocChunkGate (initSize := initSize) i (src.zslot i) (dst.zslot i)
      PhaseLoweringPlan.seq previous (PhaseLoweringPlan.seq planX planZ)

/-- Plan for the full signed allocation circuit. -/
def planCompileSignedAllocations
    {P : ShorLoweringPolicy}
    {k : ℕ}
    (initSize : ℕ)
    (src dst : LayoutState k) :
    PhaseLoweringPlan P initSize
      (compileSignedAllocations k src dst) := by
  unfold compileSignedAllocations
  exact planCompileSignedAllocationsAux initSize src dst k le_rfl

/-- Plan for a deallocation prefix. -/
def planCompileSignedDeallocationsAux
    {P : ShorLoweringPolicy}
    {k : ℕ}
    (initSize : ℕ)
    (src dst : LayoutState k) :
    ∀ (n : ℕ) (hn : n ≤ k),
      PhaseLoweringPlan P initSize
        (compileSignedDeallocationsAux src dst n hn)
  | 0, _ =>
      PhaseLoweringPlan.id initSize
  | n + 1, hn =>
      let hn' : n ≤ k := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn
      let i : Fin k := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
      let planZ := planDeallocChunkGate (initSize := initSize) i (src.zslot i) (dst.zslot i)
      let planX := planDeallocChunkGate (initSize := initSize) i (src.xslot i) (dst.xslot i)
      let previous := planCompileSignedDeallocationsAux initSize src dst n hn'
      PhaseLoweringPlan.seq planZ (PhaseLoweringPlan.seq planX previous)

/-- Plan for the full signed deallocation circuit. -/
def planCompileSignedDeallocations
    {P : ShorLoweringPolicy}
    {k : ℕ}
    (initSize : ℕ)
    (src dst : LayoutState k) :
    PhaseLoweringPlan P initSize
      (compileSignedDeallocations k src dst) := by
  unfold compileSignedDeallocations
  exact planCompileSignedDeallocationsAux initSize src dst k le_rfl

/-! =========================================================
    Annotated body plan builders

    The annotated body compiler contains ordinary arithmetic operations plus
    phase-product leaves. The caller supplies the recursive plan used at each
    leaf; these builders thread that callback through the generated body.

    `hk` stays implicit: it occurs in the result type (through
    `compileAnnotatedOpsToSignedGateAux k hk …`), so unification against the
    expected type pins it, exactly as it did when it was a plan parameter.
========================================================= -/

/-- Plan for the annotated body circuit, using `recurse` at phase-product leaves. -/
def planCompileAnnotatedOpsToSignedGateAux
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
          (Gate.SignedPhaseProd theta (st.xslot i) (st.zslot i))) :
    ∀ annotatedOps : List (AnnotatedOp k),
      PhaseLoweringPlan P initSize
        (compileAnnotatedOpsToSignedGateAux k hk phi phaseCoeff st annotatedOps)
  | [] =>
      PhaseLoweringPlan.id initSize
  | ⟨op, phaseTerm?⟩ :: rest =>
      let tail :=
        planCompileAnnotatedOpsToSignedGateAux (hk := hk) initSize phi phaseCoeff st recurse rest

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
          (Gate.CSignedPhaseProd ctrl theta (st.xslot i) (st.zslot i))) :
    ∀ annotatedOps : List (AnnotatedOp k),
      PhaseLoweringPlan P initSize
        (controlPhaseLeaves ctrl
          (compileAnnotatedOpsToSignedGateAux k hk phi phaseCoeff st annotatedOps))
  | [] =>
      PhaseLoweringPlan.id initSize
  | ⟨op, phaseTerm?⟩ :: rest =>
      let tail :=
        planCompileAnnotatedOpsToCSignedGateAux (hk := hk)
          initSize ctrl phi phaseCoeff st recurse rest
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
    One-level compiled phase-product plans — the per-table step

    A recursive step consists of allocation, the annotated body, and
    deallocation. `Policy.stepPlan` assembles those three pieces for **one**
    table, taking the children as a `recurse` argument. It performs no lookup:
    that is the dispatcher's job below.

    The split is deliberate. If the lookup were inlined here, the extracted
    per-table IR body would carry the policy's threshold tests, and the
    per-table IR split would be lost.
========================================================= -/

/-- Plan for the compiled signed phase-product replacement at one recursive
level, under the table `T` the policy chose at this node. -/
def Policy.stepPlan
    (P : ShorLoweringPolicy)
    (T : ToomCookTable)
    (phi : Angle)
    (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z T.k)
    (recurse :
      let src := initSignedLayoutState layout
      let dst := targetSignedLayoutState src (scanNeededWidths x z T.ops)
      ∀ (i : Fin T.k) (theta : Angle),
        PhaseLoweringPlan P (nextSignedWidth x z T.ops)
          (Gate.SignedPhaseProd theta (dst.xslot i) (dst.zslot i))) :
    PhaseLoweringPlan P (nextSignedWidth x z T.ops)
      (compiledSignedPhaseGate T.k T.hk T.pts T.hpts T.ops phi x z layout) := by
  let need : NeededWidths T.k := scanNeededWidths x z T.ops
  let src : LayoutState T.k := initSignedLayoutState layout
  let dst : LayoutState T.k := targetSignedLayoutState src need
  let coeff : Fin (q T.k) → ℚ := loweringPhaseCoeff T.k x z T.pts T.hpts
  let annotatedOps : List (AnnotatedOp T.k) := annotatePhaseTermsAux T.k 0 T.ops
  have recurse' :
      ∀ (i : Fin T.k) (theta : Angle),
        PhaseLoweringPlan P (nextSignedWidth x z T.ops)
          (Gate.SignedPhaseProd theta (dst.xslot i) (dst.zslot i)) := by
    simpa [src, dst, need] using recurse
  let allocationPlan :
      PhaseLoweringPlan P (nextSignedWidth x z T.ops)
        (compileSignedAllocations T.k src dst) :=
    planCompileSignedAllocations (nextSignedWidth x z T.ops) src dst
  let bodyPlan :
      PhaseLoweringPlan P
        (nextSignedWidth x z T.ops)
        (compileAnnotatedOpsToSignedGateAux T.k T.hk phi coeff dst annotatedOps) :=
    planCompileAnnotatedOpsToSignedGateAux (hk := T.hk) (nextSignedWidth x z T.ops)
      phi coeff dst recurse' annotatedOps
  let deallocationPlan :
      PhaseLoweringPlan P
        (nextSignedWidth x z T.ops)
        (compileSignedDeallocations T.k src dst) :=
    planCompileSignedDeallocations (nextSignedWidth x z T.ops) src dst
  have completePlan :
      PhaseLoweringPlan P (nextSignedWidth x z T.ops)
        (compileSignedAllocations T.k src dst ;;
          compileAnnotatedOpsToSignedGateAux T.k T.hk phi coeff dst annotatedOps ;;
          compileSignedDeallocations T.k src dst) :=
    PhaseLoweringPlan.seq allocationPlan (PhaseLoweringPlan.seq bodyPlan deallocationPlan)
  simpa [compiledSignedPhaseGate, compileOpsToSignedGate, src, dst, need, coeff, annotatedOps]
    using completePlan

/-- Plan for the compiled controlled signed phase-product replacement at one
recursive level, under the table `T` the policy chose at this node. -/
def Policy.cStepPlan
    (P : ShorLoweringPolicy)
    (T : ToomCookTable)
    (ctrl : ℕ)
    (phi : Angle)
    (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z T.k)
    (recurse :
      let src := initSignedLayoutState layout
      let dst := targetSignedLayoutState src (scanNeededWidths x z T.ops)
      ∀ (i : Fin T.k) (theta : Angle),
        PhaseLoweringPlan P (nextSignedWidth x z T.ops)
          (Gate.CSignedPhaseProd ctrl theta (dst.xslot i) (dst.zslot i))) :
    PhaseLoweringPlan P (nextSignedWidth x z T.ops)
      (compiledCSignedPhaseGate T.k T.hk T.pts T.hpts T.ops ctrl phi x z layout) := by
  let need : NeededWidths T.k := scanNeededWidths x z T.ops
  let src : LayoutState T.k := initSignedLayoutState layout
  let dst : LayoutState T.k := targetSignedLayoutState src need
  let coeff : Fin (q T.k) → ℚ := loweringPhaseCoeff T.k x z T.pts T.hpts
  let annotatedOps : List (AnnotatedOp T.k) := annotatePhaseTermsAux T.k 0 T.ops
  have recurse' :
      ∀ (i : Fin T.k) (theta : Angle),
        PhaseLoweringPlan P (nextSignedWidth x z T.ops)
          (Gate.CSignedPhaseProd ctrl theta (dst.xslot i) (dst.zslot i)) := by
    simpa [src, dst, need] using recurse
  let allocationPlan :
      PhaseLoweringPlan P (nextSignedWidth x z T.ops)
        (compileSignedAllocations T.k src dst) :=
    planCompileSignedAllocations (nextSignedWidth x z T.ops) src dst
  let bodyPlan :
      PhaseLoweringPlan P (nextSignedWidth x z T.ops)
        (controlPhaseLeaves ctrl
          (compileAnnotatedOpsToSignedGateAux T.k T.hk phi coeff dst annotatedOps)) :=
    planCompileAnnotatedOpsToCSignedGateAux (hk := T.hk) (nextSignedWidth x z T.ops)
      ctrl phi coeff dst recurse' annotatedOps
  let deallocationPlan :
      PhaseLoweringPlan P (nextSignedWidth x z T.ops)
        (compileSignedDeallocations T.k src dst) :=
    planCompileSignedDeallocations (nextSignedWidth x z T.ops) src dst
  have completePlan :
      PhaseLoweringPlan P (nextSignedWidth x z T.ops)
        (compileSignedAllocations T.k src dst ;;
          controlPhaseLeaves ctrl
            (compileAnnotatedOpsToSignedGateAux T.k T.hk phi coeff dst annotatedOps) ;;
          compileSignedDeallocations T.k src dst) :=
    PhaseLoweringPlan.seq allocationPlan (PhaseLoweringPlan.seq bodyPlan deallocationPlan)
  simpa [compiledCSignedPhaseGate, compileOpsToCSignedGate, compileOpsToSignedGate,
    controlPhaseLeaves, controlPhaseLeaves_compileSignedAllocations,
    controlPhaseLeaves_compileSignedDeallocations, src, dst, need, coeff, annotatedOps]
    using completePlan

/-- The fixed-table spelling of `Policy.stepPlan`, kept so that every existing
caller compiles unchanged: `⟨k, hk, pts, hpts, ops⟩` is the table, and its
projections are definitionally the five arguments. -/
def planCompiledSignedPhaseGate
    {P : ShorLoweringPolicy}
    {k : ℕ}
    (hk : 1 < k)
    (pts : List Point)
    (hpts : pts.length = q k)
    (ops : Prog k)
    (phi : Angle)
    (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z k)
    (recurse :
      let src := initSignedLayoutState layout
      let dst := targetSignedLayoutState src (scanNeededWidths x z ops)
      ∀ (i : Fin k) (theta : Angle),
        PhaseLoweringPlan P (nextSignedWidth x z ops)
          (Gate.SignedPhaseProd theta (dst.xslot i) (dst.zslot i))) :
    PhaseLoweringPlan P (nextSignedWidth x z ops)
      (compiledSignedPhaseGate k hk pts hpts ops phi x z layout) :=
  Policy.stepPlan P ⟨k, hk, pts, hpts, ops⟩ phi x z layout recurse

/-- The fixed-table spelling of `Policy.cStepPlan`. -/
def planCompiledCSignedPhaseGate
    {P : ShorLoweringPolicy}
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
        PhaseLoweringPlan P (nextSignedWidth x z ops)
          (Gate.CSignedPhaseProd ctrl theta (dst.xslot i) (dst.zslot i))) :
    PhaseLoweringPlan P (nextSignedWidth x z ops)
      (compiledCSignedPhaseGate k hk pts hpts ops ctrl phi x z layout) :=
  Policy.cStepPlan P ⟨k, hk, pts, hpts, ops⟩ ctrl phi x z layout recurse

/-! =========================================================
    The dispatcher

    `Policy.signedPlan` is the only recursive definition: it consults the
    policy at the node's input width, applies the shrink test, and calls the
    per-table step with itself as `recurse`. `choose = none` and a
    non-shrinking table both land on the base case, which is exactly what
    `ShorLoweringPolicy.Stops` says.
========================================================= -/

/--
The dispatcher's body, with the lookup result `o` passed in as data together
with the proof `h` that it *is* the lookup.

Taking `o` as an argument rather than matching on `P.choose …` inline is what
keeps the definition's equation lemmas usable: the equation compiler matches
on a variable, so `signedPlanOf … none h` and `signedPlanOf … (some T) h`
reduce cleanly, and the `some` branch is a `dite` on the shrink test — the
shape the IR extractor and the readiness proofs both want. Matching inline
produces an `Option.casesOn` under an `Eq.ndrec` motive that neither `split`
nor `cases` can get through.
-/
def Policy.signedPlanOf
    (P : ShorLoweringPolicy)
    (phi : Angle)
    (x z : ExtReg)
    (hworkspace : Policy.WorkspaceOK P x z) :
    ∀ (o : Option ToomCookTable), P.choose (phaseInputSize x z) = o →
      PhaseLoweringPlan P (phaseInputSize x z) (Gate.SignedPhaseProd phi x z)
  | none, h =>
      PhaseLoweringPlan.signedBase phi x z (fun T hT => by rw [h] at hT; simp at hT)
  | some T, h =>
      if hrec : nextSignedWidth x z T.ops < phaseInputSize x z then
        let step : Policy.CanonicalStep P T x z := Policy.canonicalStep P T x z h hrec hworkspace
        let src : LayoutState T.k := initSignedLayoutState step.layout
        let dst : LayoutState T.k := targetSignedLayoutState src (scanNeededWidths x z T.ops)
        let recurse : ∀ (i : Fin T.k) (theta : Angle),
            PhaseLoweringPlan P (nextSignedWidth x z T.ops)
              (Gate.SignedPhaseProd theta (dst.xslot i) (dst.zslot i)) := fun i theta =>
          have hchild : Policy.WorkspaceOK P (dst.xslot i) (dst.zslot i) := step.childWorkspace i
          have hsize : phaseInputSize (dst.xslot i) (dst.zslot i) = nextSignedWidth x z T.ops :=
            step.childInputSize i
          hsize ▸ Policy.signedPlanOf P theta (dst.xslot i) (dst.zslot i) hchild _ rfl
        PhaseLoweringPlan.signedStep phi x z T h step.layout hrec step.capacity
          (Policy.stepPlan P T phi x z step.layout recurse)
      else
        PhaseLoweringPlan.signedBase phi x z
          (fun T' hT => by rw [h] at hT; obtain rfl := Option.some.inj hT; exact hrec)
termination_by phaseInputSize x z
decreasing_by
  exact (step.childInputSize i) ▸ hrec

/-- Canonical recursive plan for a signed phase product under a policy. -/
def Policy.signedPlan
    (P : ShorLoweringPolicy)
    (phi : Angle)
    (x z : ExtReg)
    (hworkspace : Policy.WorkspaceOK P x z) :
    PhaseLoweringPlan P (phaseInputSize x z) (Gate.SignedPhaseProd phi x z) :=
  Policy.signedPlanOf P phi x z hworkspace _ rfl

/-- The controlled dispatcher body. Same shape, propagating the
control-disjointness proof to the children. -/
def Policy.cSignedPlanOf
    (P : ShorLoweringPolicy)
    (ctrl : ℕ)
    (phi : Angle)
    (x z : ExtReg)
    (hworkspace : Policy.CWorkspaceOK P ctrl x z) :
    ∀ (o : Option ToomCookTable), P.choose (phaseInputSize x z) = o →
      PhaseLoweringPlan P (phaseInputSize x z) (Gate.CSignedPhaseProd ctrl phi x z)
  | none, h =>
      PhaseLoweringPlan.cSignedBase ctrl phi x z (fun T hT => by rw [h] at hT; simp at hT)
  | some T, h =>
      if hrec : nextSignedWidth x z T.ops < phaseInputSize x z then
        let step : Policy.CanonicalStep P T x z :=
          Policy.canonicalStep P T x z h hrec hworkspace.toWorkspaceOK
        let src : LayoutState T.k := initSignedLayoutState step.layout
        let dst : LayoutState T.k := targetSignedLayoutState src (scanNeededWidths x z T.ops)
        let recurse : ∀ (i : Fin T.k) (theta : Angle),
            PhaseLoweringPlan P (nextSignedWidth x z T.ops)
              (Gate.CSignedPhaseProd ctrl theta (dst.xslot i) (dst.zslot i)) := fun i theta =>
          have hctrlLayout : step.layout.ControlDisjoint ctrl :=
            step.layout.controlDisjoint_of_ctrlDisjoint hworkspace.control_disjoint
          have hctrlDst :=
            controlDisjoint_target step.layout ctrl (scanNeededWidths x z T.ops) hctrlLayout
          have hchild : Policy.CWorkspaceOK P ctrl (dst.xslot i) (dst.zslot i) :=
            { toWorkspaceOK := step.childWorkspace i
              control_disjoint := ⟨hctrlDst.1 i, hctrlDst.2 i⟩ }
          have hsize : phaseInputSize (dst.xslot i) (dst.zslot i) = nextSignedWidth x z T.ops :=
            step.childInputSize i
          hsize ▸ Policy.cSignedPlanOf P ctrl theta (dst.xslot i) (dst.zslot i) hchild _ rfl
        PhaseLoweringPlan.cSignedStep ctrl phi x z T h step.layout hrec step.capacity
          (step.layout.controlDisjoint_of_ctrlDisjoint hworkspace.control_disjoint)
          (Policy.cStepPlan P T ctrl phi x z step.layout recurse)
      else
        PhaseLoweringPlan.cSignedBase ctrl phi x z
          (fun T' hT => by rw [h] at hT; obtain rfl := Option.some.inj hT; exact hrec)
termination_by phaseInputSize x z
decreasing_by
  exact (step.childInputSize i) ▸ hrec

/-- Canonical recursive plan for a controlled signed phase product under a
policy. -/
def Policy.cSignedPlan
    (P : ShorLoweringPolicy)
    (ctrl : ℕ)
    (phi : Angle)
    (x z : ExtReg)
    (hworkspace : Policy.CWorkspaceOK P ctrl x z) :
    PhaseLoweringPlan P (phaseInputSize x z) (Gate.CSignedPhaseProd ctrl phi x z) :=
  Policy.cSignedPlanOf P ctrl phi x z hworkspace _ rfl

/-- At the constant policy the lookup always succeeds with the same table, so
the planner reduces to the plain shrink-test `dite` with no `Option` left in
the way.

This is `rfl`: `(constPolicy T).choose n` reduces to `some T` for *any* `n`
(the single band's threshold is `0`, and `Nat.ble 0 n` is `true` by
computation), and the equation proof is a `Prop`. `GateCount/` and the IR
extractor both unfold through this lemma to recover the `dite` they expect. -/
theorem Policy.signedPlan_constPolicy
    (T : ToomCookTable) (phi : Angle) (x z : ExtReg)
    (hws : Policy.WorkspaceOK (ShorLoweringPolicy.constPolicy T) x z) :
    Policy.signedPlan (ShorLoweringPolicy.constPolicy T) phi x z hws
      = Policy.signedPlanOf (ShorLoweringPolicy.constPolicy T) phi x z hws (some T)
          (ShorLoweringPolicy.constPolicy_choose T _) := rfl

/-- The controlled twin. -/
theorem Policy.cSignedPlan_constPolicy
    (T : ToomCookTable) (ctrl : ℕ) (phi : Angle) (x z : ExtReg)
    (hws : Policy.CWorkspaceOK (ShorLoweringPolicy.constPolicy T) ctrl x z) :
    Policy.cSignedPlan (ShorLoweringPolicy.constPolicy T) ctrl phi x z hws
      = Policy.cSignedPlanOf (ShorLoweringPolicy.constPolicy T) ctrl phi x z hws (some T)
          (ShorLoweringPolicy.constPolicy_choose T _) := rfl

/-- `workspaceOK_const_iff.mpr` with every argument explicit, so the IR
extractor can build it with `mkAppM`. -/
theorem Policy.workspaceOK_of_const (T : ToomCookTable) (x z : ExtReg)
    (h : SignedRecursiveWorkspaceOK T.ops x z) :
    Policy.WorkspaceOK (ShorLoweringPolicy.constPolicy T) x z :=
  Policy.workspaceOK_const_iff.mpr h

/-- The controlled twin, likewise fully explicit. -/
theorem Policy.cWorkspaceOK_of_const (T : ToomCookTable) (ctrl : ℕ) (x z : ExtReg)
    (h : CSignedRecursiveWorkspaceOK T.ops ctrl x z) :
    Policy.CWorkspaceOK (ShorLoweringPolicy.constPolicy T) ctrl x z :=
  Policy.cWorkspaceOK_const_iff.mpr h

/-! =========================================================
    The fixed-table planners

    Unchanged in statement. Each is the dispatcher at the constant policy,
    whose `WorkspaceOK` is the fixed-table predicate by
    `Policy.workspaceOK_const_iff`.
========================================================= -/

/-- Canonical recursive plan for a signed phase product from static recursive workspace data. -/
def standardSignedPhaseLoweringPlan
    (k : ℕ)
    (hk : 1 < k)
    (phi : Angle)
    (x z : ExtReg)
    (ops : Prog k)
    (pts : List Point)
    (hpts : pts.length = q k)
    (hworkspace : SignedRecursiveWorkspaceOK ops x z) :
    StandardPhaseLoweringPlan k hk pts hpts ops (phaseInputSize x z) (Gate.SignedPhaseProd phi x z) :=
  Policy.signedPlan (ShorLoweringPolicy.constPolicy ⟨k, hk, pts, hpts, ops⟩) phi x z
    (Policy.workspaceOK_const_iff.mpr hworkspace)

/-- Canonical recursive plan for a controlled signed phase product from static recursive workspace data. -/
def standardCSignedPhaseLoweringPlan
    (k : ℕ)
    (hk : 1 < k)
    (ctrl : ℕ)
    (phi : Angle)
    (x z : ExtReg)
    (ops : Prog k)
    (pts : List Point)
    (hpts : pts.length = q k)
    (hworkspace : CSignedRecursiveWorkspaceOK ops ctrl x z) :
    StandardPhaseLoweringPlan k hk pts hpts ops (phaseInputSize x z) (Gate.CSignedPhaseProd ctrl phi x z) :=
  Policy.cSignedPlan (ShorLoweringPolicy.constPolicy ⟨k, hk, pts, hpts, ops⟩) ctrl phi x z
    (Policy.cWorkspaceOK_const_iff.mpr hworkspace)

end Shor
