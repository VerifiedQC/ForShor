import ForShor.ShorVerification.Implementation.PhaseProduct.Statement
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Lowering.Plan
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Spec.Cleanliness

/-!
# Phase-Product Plan Readiness

`PhaseLoweringReady`: the semantic precondition required to execute a
phase-product lowering plan on a state. Lowering plans contain primitive low
gates and recursive phase-product calls; primitive gates need no semantic
precondition, while recursive nodes require the step's static facts
(`SignedStepOK`), a clean recursive workspace before the child plan runs, and
then readiness for that child plan.
`QFT/Proofs/Lowering/PlanSemantics.lean` uses this definition directly, to
define its own `QFTLoweringReady`.

`PhaseLoweringPlan.Valid` is the state-independent part: every recursive step's
static facts hold. It is what readiness at the zero state amounts to.
-/

namespace Shor
open Gate
open Operations

/-- The static facts a recursive step relies on: the policy chose its table at
this node's width, the table shrinks the operands, the layout is valid, and
every chunk can grow to the width the step needs. The plan does not carry these; the planner's output satisfies
them under the workspace condition (`Policy.signedPlanOf_valid`). -/
def SignedStepOK (P : ShorLoweringPolicy) (x z : ExtReg) (T : ToomCookTable)
    (layout : Gate.PhaseProductLayout x z T.k) : Prop :=
  P.choose (phaseInputSize x z) = some T ∧ nextSignedWidthBy P.widthRule x z T.ops < phaseInputSize x z ∧
    layout.Valid ∧ (initSignedLayoutState layout).CanGrowToNeeds (neededWidthsBy P.widthRule x z T.ops)

/-- The controlled step's static facts: the uncontrolled ones, and the control
qubit is outside every child register. -/
def CSignedStepOK (P : ShorLoweringPolicy) (ctrl : ℕ) (x z : ExtReg) (T : ToomCookTable)
    (layout : Gate.PhaseProductLayout x z T.k) : Prop :=
  SignedStepOK P x z T layout ∧ layout.ControlDisjoint ctrl

/-- Every recursive step of the plan satisfies its static facts, and every base
case is one where the policy stops. -/
def PhaseLoweringPlan.Valid
    {P : ShorLoweringPolicy}
    {initSize : ℕ}
    {U : Gate}
    (plan : PhaseLoweringPlan P initSize U) : Prop := by
  induction plan with
  | id initSize => exact True
  | seq left right validLeft validRight => exact validLeft ∧ validRight
  | H initSize qbit => exact True
  | X initSize qbit => exact True
  | ShiftL initSize r n => exact True
  | ShiftR initSize r n => exact True
  | Negate initSize r => exact True
  | AddScaled initSize dst src negSrc shift => exact True
  | zeroExtend initSize r n => exact True
  | signExtend initSize r n => exact True
  | zeroDealloc initSize r n => exact True
  | signDealloc initSize r n => exact True
  | RadixReverse initSize r m => exact True
  | signedBase phi x z => exact P.Stops (phaseInputSize x z) (fun T => nextSignedWidthBy P.widthRule x z T.ops)
  | signedStep phi x z T layout child validChild =>
      exact SignedStepOK P x z T layout ∧ validChild
  | cSignedBase ctrl phi x z => exact P.Stops (phaseInputSize x z) (fun T => nextSignedWidthBy P.widthRule x z T.ops)
  | cSignedStep ctrl phi x z T layout child validChild =>
      exact CSignedStepOK P ctrl x z T layout ∧ validChild

/-- Semantic precondition required to execute a phase-product lowering plan on a state. -/
noncomputable def PhaseLoweringReady
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [LowerGateClass qs]
    {P : ShorLoweringPolicy}
    {initSize : ℕ}
    {U : Gate}
    (plan : PhaseLoweringPlan P initSize U) :
    qs.State → Prop := by
  induction plan with
  | id initSize => exact fun _ => True
  | seq left right readyLeft readyRight =>
      exact fun ψ => readyLeft ψ ∧
        readyRight (LowerGateClass.evalL (qs := qs) (lowerGateRec left) ψ)
  | H initSize qbit => exact fun _ => True
  | X initSize qbit => exact fun _ => True
  | ShiftL initSize r n => exact fun _ => True
  | ShiftR initSize r n => exact fun _ => True
  | Negate initSize r => exact fun _ => True
  | AddScaled initSize dst src negSrc shift => exact fun _ => True
  | zeroExtend initSize r n => exact fun _ => True
  | signExtend initSize r n => exact fun _ => True
  | zeroDealloc initSize r n => exact fun _ => True
  | signDealloc initSize r n => exact fun _ => True
  | RadixReverse initSize r m => exact fun _ => True
  | signedBase phi x z => exact fun _ => True
  | signedStep phi x z T layout child readyChild =>
      exact fun ψ =>
        SignedStepOK P x z T layout ∧
        CleanWorkspaceState qs (initSignedLayoutState layout) (neededWidthsBy P.widthRule x z T.ops) ψ ∧
        readyChild ψ
  | cSignedBase ctrl phi x z => exact fun _ => True
  | cSignedStep ctrl phi x z T layout child readyChild =>
      exact fun ψ =>
        CSignedStepOK P ctrl x z T layout ∧
        CleanWorkspaceState qs (initSignedLayoutState layout) (neededWidthsBy P.widthRule x z T.ops) ψ ∧
        readyChild ψ

end Shor
