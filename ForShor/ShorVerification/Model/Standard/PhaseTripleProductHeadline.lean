import ForShor.ShorVerification.Model.Standard.LowGates
import ForShor.ShorVerification.Model.Standard.Lift
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Main
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Controlled
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Witness.RecursionWitness

/-!
# PhaseTripleProduct in the Standard model (non-vacuity of the typeclass stack)

Every PTP gate theorem is stated over `qs : QSemantics`, `[RegEncoding qs.Basis]`,
`[LowerGateClass qs]`. If those laws were contradictory, every such theorem would hold
vacuously and `#print axioms` would not notice. `Model/Standard` is a concrete model of the
classes (a `Finsupp`-based Hilbert space with a `LowerGateClass` instance), which
`Headline.lean` uses to specialise the order-finding headlines. This file does the same for
PTP:

* `modelPhaseOp`, `modelCtlPhaseOp`: the specification operators `PTPPhaseOp` and
  `PTPCtlPhaseOp` exist in the model (a diagonal unit-modulus lift, `norm_ptpEigenphase`), so
  the hypotheses of the state-level claims are satisfiable;
* `model_ptp_lowerExact_correct`, `model_ptp_ctl_lowerExact_correct`: the claims specialised to
  `Model.qs` (every instance resolves);
* `model_witness_correct`: a concrete instance, the accepted `k = 2` policy `fixed` on the three
  20-qubit registers of `Proofs/Witness/RecursionWitness.lean`, whose gate-level circuit equals
  the model's phase operator on every clean state.

Like `Headline.lean`, this file reaches into `Implementation/`, and nothing outside `Model/` may
import it. Nothing here is used to prove anything else.
-/

namespace Shor
namespace Model

open PTP

theorem norm_ptpEigenphase {qs : QSemantics} [RegEncoding qs.Basis] (φ : Angle)
    (X : Fin 3 → ExtReg) (b : qs.Basis) : ‖ptpEigenphase φ X b‖ = 1 := by
  unfold ptpEigenphase
  have h : ((Angle.toReal φ : ℝ) : ℂ) * Complex.I *
      (((extToInt (X 0) b : ℤ) : ℂ) * ((extToInt (X 1) b : ℤ) : ℂ) *
        ((extToInt (X 2) b : ℤ) : ℂ)) =
      (((Angle.toReal φ * ((extToInt (X 0) b * extToInt (X 1) b * extToInt (X 2) b : ℤ) : ℝ) : ℝ)
        : ℂ)) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- The specification operator exists in the Standard model. -/
noncomputable def modelPhaseOp (X : Fin 3 → ExtReg) (φ : Angle) :
    PTPPhaseOp Model.qs X φ where
  op := fun ψ => Model.diagLift (fun b => ptpEigenphase (qs := Model.qs) φ X b)
    (fun b => norm_ptpEigenphase (qs := Model.qs) φ X b) ψ
  op_add := fun ψ χ => map_add _ ψ χ
  op_smul := fun a ψ => map_smul _ a ψ
  op_ket := fun b => Model.diagLift_ket _ _ b

theorem norm_ptpCtlEigenphase {qs : QSemantics} [RegEncoding qs.Basis] (φ : Angle) (c : ℕ)
    (X : Fin 3 → ExtReg) (b : qs.Basis) : ‖ptpCtlEigenphase φ c X b‖ = 1 := by
  unfold ptpCtlEigenphase
  split_ifs
  · exact norm_ptpEigenphase φ X b
  · simp

/-- The controlled specification operator exists in the Standard model. -/
noncomputable def modelCtlPhaseOp (c : ℕ) (X : Fin 3 → ExtReg) (φ : Angle) :
    PTPCtlPhaseOp Model.qs c X φ where
  op := fun ψ => Model.diagLift (fun b => ptpCtlEigenphase (qs := Model.qs) φ c X b)
    (fun b => norm_ptpCtlEigenphase (qs := Model.qs) φ c X b) ψ
  op_add := fun ψ χ => map_add _ ψ χ
  op_smul := fun a ψ => map_smul _ a ψ
  op_ket := fun b => Model.diagLift_ket _ _ b

/-- The controlled claim at `Model.qs`. -/
theorem model_ptp_ctl_lowerExact_correct (P : PTPPolicy) (n : ℕ) (X : Fin 3 → ExtReg)
    (Y : ExtReg) (c base : ℕ) : PTPCtlLowerExactCorrect Model.qs P n X Y c base :=
  ptp_ctl_lowerExact_correct (qs := Model.qs) P n X Y c base

/-- The main claim at `Model.qs`: every instance in its statement resolves. -/
theorem model_ptp_lowerExact_correct (P : PTPPolicy) (n : ℕ) (X : Fin 3 → ExtReg) (base : ℕ) :
    PTPLowerExactCorrect Model.qs P n X base :=
  ptp_lowerExact_correct Model.qs P n X base

/-- A concrete instance: the `RecursionWitness` registers satisfy `Good`. -/
theorem witness_good : Good PTP.Witness.X 20 60 := by
  refine ⟨?_, ?_, ?_⟩
  · intro s; revert s; decide +kernel
  · intro s s' h
    apply PTP.Witness.disj_of_check
    revert h
    revert s s'
    decide +kernel
  · intro s
    revert s
    decide +kernel

/-- **Concrete instance in the model.** The accepted `k = 2` policy `fixed` on the
`RecursionWitness` registers has an exact-board gate-level circuit that equals the model's
phase operator on every clean state. -/
theorem model_witness_correct :
    ∃ (W : List ℕ) (G : Angle → LowGate),
      PolicyImplX PTP.Instances.FaultChallenge.fixed PTP.Witness.X 20 W G ∧
      ∀ (φ : Angle) (ψ : Model.qs.State), PTPCleanState Model.qs PTP.Witness.X 20 W ψ →
        LowerGateClass.evalL (qs := Model.qs) (G φ) ψ = (modelPhaseOp PTP.Witness.X φ).op ψ := by
  obtain ⟨W, G, hI, _, hS, _⟩ := model_ptp_lowerExact_correct
    PTP.Instances.FaultChallenge.fixed 20 PTP.Witness.X 60
    PTP.Instances.FaultChallenge.fixed_accepted witness_good
  exact ⟨W, G, hI, fun φ ψ hψ => hS φ (modelPhaseOp PTP.Witness.X φ) ψ hψ⟩

/-!
## Axioms

```
#print axioms model_ptp_lowerExact_correct
#print axioms model_ptp_ctl_lowerExact_correct
-- depend on axioms: [propext, Classical.choice, Quot.sound]
```
-/

end Model
end Shor
