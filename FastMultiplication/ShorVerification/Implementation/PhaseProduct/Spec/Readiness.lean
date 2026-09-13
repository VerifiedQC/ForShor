import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Lowering.Plan
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Spec.Cleanliness

/-!
# Phase-Product Plan Readiness

`PhaseLoweringReady`: the semantic precondition required to execute a
phase-product lowering plan on a state. Lowering plans contain primitive low
gates and recursive phase-product calls; primitive gates need no semantic
precondition, while recursive nodes require a clean recursive workspace
before the child plan runs and then readiness for that child plan.
`QFT/Spec/Readiness.lean` needs this definition directly, to define its own
`QFTLoweringReady`.
-/

namespace Shor
open Gate
open Operations

/-- Semantic precondition required to execute a phase-product lowering plan on a state. -/
noncomputable def PhaseLoweringReady
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [LowerGateClass qs]
    {k : ℕ}
    {hk : 1 < k}
    {pts : List Point}
    {hpts : pts.length = q k}
    {ops : Prog k}
    {initSize : ℕ}
    {U : Gate}
    (plan : PhaseLoweringPlan k hk pts hpts ops initSize U) :
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
  | signedBase phi x z hstop => exact fun _ => True
  | signedStep phi x z layout hrec hcapacity child readyChild =>
      exact fun ψ =>
        CleanWorkspaceState qs (initSignedLayoutState layout) (scanNeededWidths x z ops) ψ ∧
        readyChild ψ
  | cSignedBase ctrl phi x z hstop => exact fun _ => True
  | cSignedStep ctrl phi x z layout hrec hcapacity hctrl child readyChild =>
      exact fun ψ =>
        CleanWorkspaceState qs (initSignedLayoutState layout) (scanNeededWidths x z ops) ψ ∧
        readyChild ψ

end Shor
