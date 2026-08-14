import FastMultiplication.ShorVerification.Implementation.Shor.Defs
import FastMultiplication.ShorVerification.Implementation.QFT.Proofs.Lowering
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.LoweringCorrectness.Workspace

namespace Shor

/-!
# Shor workspace budgets and clean-state predicates

This file is the layer for the workspace directory. It names the static reserve
budgets and the dynamic clean-state invariants used by
`Workspace.ShorReadiness`.

Main declarations:

* `shorWorkspaceNeed` computes the reserve budget for exponent, data, and
  auxiliary registers.
* `ShorWorkspaceLargeEnough` is the public static capacity assumption.
* `ShorLoweringCleanState` is the clean-state invariant preserved by lowered
  Shor stages after the data carry bit is allowed to be live.
* `shorLoweringCleanState_ket` is the entry lemma that turns an initially clean
  basis state into the lowered clean invariant.
-/

/-! =========================================================
    Section 1: Static reserve budgets
========================================================= -/

/-! =========================================================
    Section 2: Public workspace preconditions
========================================================= -/

/-! =========================================================
    Section 3: Dynamic clean-state invariants

    The main invariant for lowered readiness is `ShorLoweringCleanState`.
    The older full/carry predicates are kept as small bridge names because
    several imported correctness statements still expose them.
========================================================= -/

namespace ThreeRegsCleanState
variable {qs : QSemantics} [RegEncoding qs.Basis] {r₁ r₂ r₃ : Reg}
/-- Smart constructors delegating to `CleanClosure`, preserving call sites. -/
theorem zero : ThreeRegsCleanState qs r₁ r₂ r₃ 0 := CleanClosure.zero
theorem ket (b : qs.Basis) (h₁ : FreshZero r₁ b) (h₂ : FreshZero r₂ b)
    (h₃ : FreshZero r₃ b) : ThreeRegsCleanState qs r₁ r₂ r₃ (qs.ket b) :=
  CleanClosure.ket b ⟨h₁, h₂, h₃⟩
theorem add {ψ φ : qs.State} (hψ : ThreeRegsCleanState qs r₁ r₂ r₃ ψ)
    (hφ : ThreeRegsCleanState qs r₁ r₂ r₃ φ) :
    ThreeRegsCleanState qs r₁ r₂ r₃ (ψ + φ) := CleanClosure.add hψ hφ
theorem smul (a : ℂ) {ψ : qs.State} (hψ : ThreeRegsCleanState qs r₁ r₂ r₃ ψ) :
    ThreeRegsCleanState qs r₁ r₂ r₃ (a • ψ) := CleanClosure.smul a hψ
/-- Custom eliminator preserving the original 3-hypothesis `ket` shape
(`| ket b h₁ h₂ h₃`) despite the generic single-predicate closure. -/
@[induction_eliminator, cases_eliminator]
def rec' {motive : (ψ : qs.State) → ThreeRegsCleanState qs r₁ r₂ r₃ ψ → Prop}
    (zero : motive 0 ThreeRegsCleanState.zero)
    (ket : ∀ (b : qs.Basis) (h₁ : FreshZero r₁ b) (h₂ : FreshZero r₂ b)
        (h₃ : FreshZero r₃ b),
        motive (qs.ket b) (ThreeRegsCleanState.ket b h₁ h₂ h₃))
    (add : ∀ {ψ φ : qs.State} (hψ : ThreeRegsCleanState qs r₁ r₂ r₃ ψ)
        (hφ : ThreeRegsCleanState qs r₁ r₂ r₃ φ),
        motive ψ hψ → motive φ hφ → motive (ψ + φ) (ThreeRegsCleanState.add hψ hφ))
    (smul : ∀ (a : ℂ) {ψ : qs.State} (hψ : ThreeRegsCleanState qs r₁ r₂ r₃ ψ),
        motive ψ hψ → motive (a • ψ) (ThreeRegsCleanState.smul a hψ))
    {ψ : qs.State} (h : ThreeRegsCleanState qs r₁ r₂ r₃ ψ) : motive ψ h := by
  induction h with
  | zero => exact zero
  | ket b hconj => exact ket b hconj.1 hconj.2.1 hconj.2.2
  | add hψ hφ ihψ ihφ => exact add hψ hφ ihψ ihφ
  | smul a hψ ih => exact smul a hψ ih
end ThreeRegsCleanState

/--
The invariant at entry to and exit from each modular-multiplication core.
-/
abbrev FullShorWorkspaceCleanState
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (x data work : ExtReg) :
    qs.State → Prop :=
  ThreeRegsCleanState
    qs
    x.reserve
    data.reserve
    work.reserve

namespace FullShorWorkspaceCleanState
variable {qs : QSemantics} [RegEncoding qs.Basis] {x data work : ExtReg}
@[induction_eliminator, cases_eliminator]
def rec' {motive : (ψ : qs.State) → FullShorWorkspaceCleanState qs x data work ψ → Prop}
    (zero : motive 0 ThreeRegsCleanState.zero)
    (ket : ∀ (b : qs.Basis) (h₁ : FreshZero x.reserve b) (h₂ : FreshZero data.reserve b)
        (h₃ : FreshZero work.reserve b),
        motive (qs.ket b) (ThreeRegsCleanState.ket b h₁ h₂ h₃))
    (add : ∀ {ψ φ : qs.State} (hψ : FullShorWorkspaceCleanState qs x data work ψ)
        (hφ : FullShorWorkspaceCleanState qs x data work φ),
        motive ψ hψ → motive φ hφ → motive (ψ + φ) (ThreeRegsCleanState.add hψ hφ))
    (smul : ∀ (a : ℂ) {ψ : qs.State} (hψ : FullShorWorkspaceCleanState qs x data work ψ),
        motive ψ hψ → motive (a • ψ) (ThreeRegsCleanState.smul a hψ))
    {ψ : qs.State} (h : FullShorWorkspaceCleanState qs x data work ψ) : motive ψ h :=
  ThreeRegsCleanState.rec' zero ket add smul h
end FullShorWorkspaceCleanState

/--
The lowering-clean invariant used throughout lowered Shor readiness.

The first bit of `data.reserve` is the algorithmic carry bit, so it is not part
of the lowering workspace that must remain clean between modular-multiplication
stages.
-/
abbrev ShorLoweringCleanState
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (x data work : ExtReg) :
    qs.State → Prop :=
  ThreeRegsCleanState
    qs
    x.reserve
    (data.reserve.drop 1)
    work.reserve

namespace ShorLoweringCleanState
variable {qs : QSemantics} [RegEncoding qs.Basis] {x data work : ExtReg}
@[induction_eliminator, cases_eliminator]
def rec' {motive : (ψ : qs.State) → ShorLoweringCleanState qs x data work ψ → Prop}
    (zero : motive 0 ThreeRegsCleanState.zero)
    (ket : ∀ (b : qs.Basis) (h₁ : FreshZero x.reserve b)
        (h₂ : FreshZero (data.reserve.drop 1) b) (h₃ : FreshZero work.reserve b),
        motive (qs.ket b) (ThreeRegsCleanState.ket b h₁ h₂ h₃))
    (add : ∀ {ψ φ : qs.State} (hψ : ShorLoweringCleanState qs x data work ψ)
        (hφ : ShorLoweringCleanState qs x data work φ),
        motive ψ hψ → motive φ hφ → motive (ψ + φ) (ThreeRegsCleanState.add hψ hφ))
    (smul : ∀ (a : ℂ) {ψ : qs.State} (hψ : ShorLoweringCleanState qs x data work ψ),
        motive ψ hψ → motive (a • ψ) (ThreeRegsCleanState.smul a hψ))
    {ψ : qs.State} (h : ShorLoweringCleanState qs x data work ψ) : motive ψ h :=
  ThreeRegsCleanState.rec' zero ket add smul h
end ShorLoweringCleanState

lemma fullShorWorkspaceCleanState_ket
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    {x data work : ExtReg}
    {b : qs.Basis}
    (hzero :
      ShorWorkspaceCleanInput x data work b) :
    FullShorWorkspaceCleanState
      qs x data work
      (qs.ket b) := by
  exact
    ThreeRegsCleanState.ket
      b
      hzero.1
      hzero.2.1
      hzero.2.2

lemma fullShorWorkspaceCleanState_to_carry
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    {x data work : ExtReg}
    {ψ : qs.State}
    (hclean :
      FullShorWorkspaceCleanState
        qs x data work ψ) :
    ShorLoweringCleanState
      qs x data work ψ := by
  induction hclean with
  | zero =>
      exact ThreeRegsCleanState.zero

  | ket b hx hdata hwork =>
      apply ThreeRegsCleanState.ket b hx
      · apply FreshZero.of_subset
          (data.reserve.drop 1)
          data.reserve
          b
        · intro q hq
          exact List.mem_of_mem_drop hq
        · exact hdata
      · exact hwork

  | add hψ hφ ihψ ihφ =>
      exact ThreeRegsCleanState.add ihψ ihφ

  | smul a hψ ihψ =>
      exact ThreeRegsCleanState.smul a ihψ

/--
Main clean-state entry lemma for this file.

It packages the initial reserve-zero assumption into the invariant used by all
lowered Shor readiness theorems. The first data reserve bit is deliberately
dropped because it is the modular-multiplication carry bit, not compiler
workspace.
-/
lemma shorLoweringCleanState_ket
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    {x data work : ExtReg}
    {b : qs.Basis}
    (hzero :
      ShorWorkspaceCleanInput
        x data work b) :
    ShorLoweringCleanState
      qs x data work
      (qs.ket b) := by
  exact
    fullShorWorkspaceCleanState_to_carry
      (fullShorWorkspaceCleanState_ket hzero)

end Shor
