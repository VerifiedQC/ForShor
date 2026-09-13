import FastMultiplication.ShorVerification.Implementation.Shor.Defs
import FastMultiplication.ShorVerification.Implementation.Shor.Spec.Cleanliness
import FastMultiplication.ShorVerification.Implementation.RegisterLemmas
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.Lowering.Workspace

namespace Shor

/-!
# Shor workspace budgets and clean-state predicates

The dynamic clean-state preservation lemmas for the clean-state invariants
declared in `Shor.Spec.Cleanliness`.

Main declarations:

* `shorConcreteCleanState_ket` / `ShorConcreteCleanState.to_lowering` bridge
  the concrete compiler-clean invariant to `ShorLoweringCleanState`.
* `fullShorWorkspaceCleanState_ket` / `fullShorWorkspaceCleanState_to_carry`
  do the same for the full (pre-carry) invariant.
* `shorLoweringCleanState_ket` is the entry lemma that turns an initially
  clean basis state into the lowered clean invariant.
-/

private lemma freshZero_append
    {Basis : Type u}
    [RegEncoding Basis]
    (left right : Reg)
    (hdisjoint : Disjoint left right)
    (b : Basis)
    (hleft : FreshZero left b)
    (hright : FreshZero right b) :
    FreshZero (Reg.append left right hdisjoint) b := by
  unfold FreshZero at hleft hright ⊢
  rw [RegEncoding.toNat_append]
  simp [hleft, hright]

lemma shorConcreteCleanState_ket
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    {x data work scratch : ExtReg}
    {hdisjoint : x.OwnedDisjoint scratch}
    {b : qs.Basis}
    (hzero :
      ShorWorkspaceCleanInput x data work scratch b)
    (hscratchActive : FreshZero scratch.active b) :
    ShorConcreteCleanState
      qs x data work scratch hdisjoint (qs.ket b) := by
  apply ThreeRegsCleanState.ket
  · unfold exponentScratchCleanReg
    apply freshZero_append
    · exact hzero.1
    · unfold ExtReg.ownedReg
      apply freshZero_append
      · exact hscratchActive
      · exact hzero.2.2.2
  · apply FreshZero.of_subset
      (data.reserve.drop 1) data.reserve b
    · intro q hq
      exact List.mem_of_mem_drop hq
    · exact hzero.2.1
  · exact hzero.2.2.1

lemma ShorConcreteCleanState.to_lowering
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    {x data work scratch : ExtReg}
    {hdisjoint : x.OwnedDisjoint scratch}
    {ψ : qs.State}
    (hclean :
      ShorConcreteCleanState
        qs x data work scratch hdisjoint ψ) :
    ShorLoweringCleanState qs x data work ψ := by
  induction hclean with
  | zero => exact ThreeRegsCleanState.zero
  | ket b hbasis =>
      rcases hbasis with ⟨hx, hdata, haux⟩
      apply ThreeRegsCleanState.ket b ?_ hdata haux
      apply FreshZero.of_subset
          x.reserve
          (exponentScratchCleanReg x scratch hdisjoint)
          b
      · intro q hq
        simp [exponentScratchCleanReg, Reg.append, hq]
      · exact hx
  | add hψ hφ ihψ ihφ =>
      exact ThreeRegsCleanState.add ihψ ihφ
  | smul a hψ ihψ =>
      exact ThreeRegsCleanState.smul a ihψ

lemma fullShorWorkspaceCleanState_ket
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    {x data work scratch : ExtReg}
    {b : qs.Basis}
    (hzero :
      ShorWorkspaceCleanInput x data work scratch b) :
    FullShorWorkspaceCleanState
      qs x data work
      (qs.ket b) := by
  exact
    ThreeRegsCleanState.ket
      b
      hzero.1
      hzero.2.1
      hzero.2.2.1

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
    {x data work scratch : ExtReg}
    {b : qs.Basis}
    (hzero :
      ShorWorkspaceCleanInput
        x data work scratch b) :
    ShorLoweringCleanState
      qs x data work
      (qs.ket b) := by
  exact
    fullShorWorkspaceCleanState_to_carry
      (fullShorWorkspaceCleanState_ket hzero)

end Shor
