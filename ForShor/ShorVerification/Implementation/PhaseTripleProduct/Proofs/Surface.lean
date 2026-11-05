import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Statement
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.ExactBoard.ExactBuild
/-!
# PTP state-level lift: the circuit equals the specification on every clean state

The *definitions* of this layer (`ptpEigenphase`, `PTPPhaseOp`, `PTPCleanBasis`, `PTPCleanState`,
`PTPExactCensus`) and the claim `PTPLowerExactCorrect` live in `Statement.lean`. This file holds
the lemmas that lift the basis-ket result of `ptp_gate_full_exact` (`ExactBoard/ExactBuild.lean`)
to all states in the linear closure of the clean kets (`CleanClosure`):
`evalL_eq_of_clean_kets`, `evalL_eq_phaseOp_of_clean`, `evalL_policyImplD_state`. `Main.lean`
assembles them into `ptp_lowerExact_correct`.

What this does not give: that the specification operator exists in an arbitrary `qs` (it does in
ForShor's Standard model), or anything about states outside the clean closure.
-/

namespace Shor
namespace PTP

open Shor

/-! ## State-level lift -/

section Lift

variable {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]

theorem evalL_zero (L : LowGate) : LowerGateClass.evalL (qs := qs) L 0 = 0 := by
  have h := LowerGateClass.evalL_smul (qs := qs) L 0 (0 : qs.State)
  simpa using h

/-- **Linearity lift.** A circuit that acts as `U` on every clean basis ket acts as `U` on every
clean state. -/
theorem evalL_eq_of_clean_kets {L : LowGate} {P : qs.Basis → Prop} (U : qs.State → qs.State)
    (hU0 : U 0 = 0) (hUadd : ∀ ψ χ, U (ψ + χ) = U ψ + U χ)
    (hUsmul : ∀ (a : ℂ) ψ, U (a • ψ) = a • U ψ)
    (hket : ∀ b, P b → LowerGateClass.evalL (qs := qs) L (qs.ket b) = U (qs.ket b))
    {ψ : qs.State} (hψ : CleanClosure P ψ) :
    LowerGateClass.evalL (qs := qs) L ψ = U ψ := by
  induction hψ with
  | zero => rw [evalL_zero, hU0]
  | ket b h => exact hket b h
  | add _ _ ih1 ih2 => rw [LowerGateClass.evalL_add, hUadd, ih1, ih2]
  | smul a _ ih => rw [LowerGateClass.evalL_smul, hUsmul, ih]

omit [LowerGateClass qs] in
theorem PTPPhaseOp.op_zero {X : Fin 3 → ExtReg} {φ : Angle} (U : PTPPhaseOp qs X φ) :
    U.op 0 = 0 := by
  have h := U.op_smul 0 (0 : qs.State)
  simpa using h

/-- **State-level PTP correctness for any gate correct on the clean kets.** -/
theorem evalL_eq_phaseOp_of_clean {X : Fin 3 → ExtReg} {n : ℕ} {W : List ℕ} {φ : Angle}
    {L : LowGate}
    (hket : ∀ b : qs.Basis, PTPCleanBasis qs X n W b →
      LowerGateClass.evalL (qs := qs) L (qs.ket b) = ptpEigenphase φ X b • qs.ket b)
    (U : PTPPhaseOp qs X φ) {ψ : qs.State} (hψ : PTPCleanState qs X n W ψ) :
    LowerGateClass.evalL (qs := qs) L ψ = U.op ψ :=
  evalL_eq_of_clean_kets U.op U.op_zero U.op_add U.op_smul
    (fun b hb => by rw [U.op_ket, hket b hb]) hψ

/-- **The policy circuit at any admissible width rule is the PTP phase operator on every clean
state** (state-level form of `evalL_policyImplD_ket`). -/
theorem evalL_policyImplD_state {P : PTPPolicy} (hP : P.check = true) {wd : WidthRule}
    (hwd : Admissible P wd) {X : Fin 3 → ExtReg} {n : ℕ} {W : List ℕ} {G : Angle → LowGate}
    (h : PolicyImplD P wd X n W G) (φ : Angle) (U : PTPPhaseOp qs X φ) {ψ : qs.State}
    (hψ : PTPCleanState qs X n W ψ) :
    LowerGateClass.evalL (qs := qs) (G φ) ψ = U.op ψ :=
  evalL_eq_phaseOp_of_clean
    (fun b hb => evalL_policyImplD_ket hP hwd h φ b hb.1 hb.2) U hψ

end Lift

end PTP
end Shor
