import FastMultiplication.ShorVerification.Implementation.Shor.Defs
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Budgets
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.WholeProgramCorrectness
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Proofs.ModExp
import FastMultiplication.ShorVerification.Framework.Submission

namespace Shor
open Gate
open Classical

/-!
# Order-finding circuits and lowered Shor setup data

This module contains the circuit/setup declarations used by Shor workspace
readiness and by the final Shor correctness statements.

Main declarations:

* `orderFindingApprox` is the high-level circuit whose lowering workspace is
  proved ready in `Workspace.ShorReadiness`.
* `orderFindingApproxLow` applies the public lowerer once readiness is known.
* `ShorApproxSetup` collects the user-facing layout, workspace, precision, and
  clean-input assumptions for approximate Shor.
* `ShorApproxSetup.toIdealOrderFindingInput` is the final bridge from the
  approximate setup to the ideal order-finding input predicate.
-/

/-! =========================================================
    Section 1: Order-finding circuit definitions
========================================================= -/

/-! =========================================================
    Section 2: Lowering setup
========================================================= -/

/-! =========================================================
    Section 3: Approximate and ideal input predicates
========================================================= -/

private lemma active_get_mem_ownedQubits
    (x : ExtReg)
    (i : Fin (Reg.width x.active)) :
    x.active.get i ∈ x.ownedQubits := by
  rw [ExtReg.ownedQubits, List.mem_append]
  left
  dsimp [Reg.get]
  exact List.get_mem x.active.qubits _

theorem ShorApproxSetupMinimal.toShorApproxSetup
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    {η : ℝ}
    {x data work : ExtReg}
    {flag : ℕ}
    {b0 : qs.Basis}
    (h :
      ShorApproxSetupMinimal
        qs η x data work flag b0) :
    ShorApproxSetup
      qs η x data work flag b0 := by
  refine
    {
      register_layout := ?_
      circuit_workspace := ?_
      exponent_data_disjoint :=
        h.exponent_data_disjoint
      work_precision :=
        h.algorithm1_precision
      clean_input := ?_
    }

  · -- Reconstruct `ModExpLayout`.
    intro i

    have hctrlMem :
        x.active.get i ∈ x.active.qubits := by
      dsimp [Reg.get]
      exact List.get_mem x.active.qubits _

    have hctrlData :
        x.active.get i ∉ data.ownedQubits := by
      intro hdata

      exact
        h.exponent_data_disjoint
          (active_get_mem_ownedQubits x i)
          hdata

    have hctrlWork :
        x.active.get i ∉ work.ownedQubits :=
      h.controls_outside_work
        (x.active.get i)
        hctrlMem

    have hctrlFlag :
        x.active.get i ≠ flag := by
      intro heq
      apply h.flag_outside_controls
      rwa [← heq]

    exact
      ⟨h.data_work_disjoint,
        h.flag_outside_data,
        h.flag_outside_work,
        hctrlData,
        hctrlWork,
        hctrlFlag⟩

  · -- Reconstruct `ModMulCircuitWorkspaceOK`.
    exact
      ⟨h.data_can_grow_two,
        h.work_can_grow_one,
        h.data_work_disjoint⟩

  · -- Reconstruct `ShorCleanInput`.
    exact
      ⟨h.exponent_zero,
        h.data_zero,
        h.data_fresh,
        h.work_zero,
        h.work_fresh,
        h.flag_zero⟩
/--
Main bridge theorem for this file.

The approximate Shor setup contains extra implementation assumptions, but the
ideal specification only needs the exponent/data zero state and their
disjointness. This lemma forgets the implementation-only fields.
-/
lemma ShorApproxSetup.toIdealOrderFindingInput
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    {η : ℝ}
    {x y work : ExtReg}
    {flag : ℕ}
    {b0 : qs.Basis}
    (hsetup : ShorApproxSetup qs η  x y work flag b0) :
    IdealOrderFindingInput qs x y b0 := by
  rcases hsetup.clean_input with
    ⟨hx0, hy0, _hyFresh, _hwork0,
      _hworkFresh, _hflag0⟩

  exact
    ⟨hx0, hy0, hsetup.exponent_data_disjoint⟩

end Shor
