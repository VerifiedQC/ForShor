import ForShor.ShorVerification.Implementation.PhaseProduct.Statement
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.Workspace
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.PolicyWorkspace
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Lowering.Plan

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

namespace Shor
open Gate
open Operations

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
      let dst := targetSignedLayoutState src (neededWidthsBy P.widthRule x z ops)
      ∀ (i : Fin k) (theta : Angle),
        PhaseLoweringPlan P (nextSignedWidthBy P.widthRule x z ops)
          (Gate.SignedPhaseProd theta (dst.xslot i) (dst.zslot i))) :
    PhaseLoweringPlan P (nextSignedWidthBy P.widthRule x z ops)
      (compiledSignedPhaseGateBy P.widthRule k hk pts hpts ops phi x z layout) :=
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
      let dst := targetSignedLayoutState src (neededWidthsBy P.widthRule x z ops)
      ∀ (i : Fin k) (theta : Angle),
        PhaseLoweringPlan P (nextSignedWidthBy P.widthRule x z ops)
          (Gate.CSignedPhaseProd ctrl theta (dst.xslot i) (dst.zslot i))) :
    PhaseLoweringPlan P (nextSignedWidthBy P.widthRule x z ops)
      (compiledCSignedPhaseGateBy P.widthRule k hk pts hpts ops ctrl phi x z layout) :=
  Policy.cStepPlan P ⟨k, hk, pts, hpts, ops⟩ ctrl phi x z layout recurse

/-! =========================================================
    Facts about the dispatcher

    Its size label does not affect the lowered circuit, and the fixed-table
    planners are the dispatcher at the constant policy with the lookup
    resolved.
========================================================= -/

/-- The size a dispatcher plan is labelled with does not affect the circuit it
lowers to: the children are labelled `nextSignedWidthBy P.widthRule` either way. -/
theorem Policy.lowerGateRec_signedPlanOf_relabel
    (P : ShorLoweringPolicy) (phi : Angle) (x z : ExtReg) (n m : ℕ)
    (o : Option ToomCookTable) (ho : P.choose (phaseInputSize x z) = o) :
    lowerGateRec (Policy.signedPlanOf P phi x z n o ho)
      = lowerGateRec (Policy.signedPlanOf P phi x z m o ho) := by
  cases o with
  | none => rw [Policy.signedPlanOf, Policy.signedPlanOf]; rfl
  | some T =>
      rw [Policy.signedPlanOf, Policy.signedPlanOf]
      split <;> rfl

/-- The controlled twin. -/
theorem Policy.lowerGateRec_cSignedPlanOf_relabel
    (P : ShorLoweringPolicy) (ctrl : ℕ) (phi : Angle) (x z : ExtReg) (n m : ℕ)
    (o : Option ToomCookTable) (ho : P.choose (phaseInputSize x z) = o) :
    lowerGateRec (Policy.cSignedPlanOf P ctrl phi x z n o ho)
      = lowerGateRec (Policy.cSignedPlanOf P ctrl phi x z m o ho) := by
  cases o with
  | none => rw [Policy.cSignedPlanOf, Policy.cSignedPlanOf]; rfl
  | some T =>
      rw [Policy.cSignedPlanOf, Policy.cSignedPlanOf]
      split <;> rfl

/-- The fixed-table planner is the dispatcher at the constant policy, with the
lookup already resolved to its table. -/
theorem standardSignedPhaseLoweringPlan_eq
    (k : ℕ) (hk : 1 < k) (phi : Angle) (x z : ExtReg) (ops : Prog k) (pts : List Point)
    (hpts : pts.length = q k) :
    standardSignedPhaseLoweringPlan k hk phi x z ops pts hpts
      = Policy.signedPlanOf (ShorLoweringPolicy.constPolicy ⟨k, hk, pts, hpts, ops⟩) phi x z
          (phaseInputSize x z) (some ⟨k, hk, pts, hpts, ops⟩)
          (ShorLoweringPolicy.constPolicy_choose _ _) := rfl

/-- The controlled twin. -/
theorem standardCSignedPhaseLoweringPlan_eq
    (k : ℕ) (hk : 1 < k) (ctrl : ℕ) (phi : Angle) (x z : ExtReg) (ops : Prog k) (pts : List Point)
    (hpts : pts.length = q k) :
    standardCSignedPhaseLoweringPlan k hk ctrl phi x z ops pts hpts
      = Policy.cSignedPlanOf (ShorLoweringPolicy.constPolicy ⟨k, hk, pts, hpts, ops⟩) ctrl phi x z
          (phaseInputSize x z) (some ⟨k, hk, pts, hpts, ops⟩)
          (ShorLoweringPolicy.constPolicy_choose _ _) := rfl

end Shor
