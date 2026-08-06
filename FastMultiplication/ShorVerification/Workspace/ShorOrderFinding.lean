import FastMultiplication.ShorVerification.Workspace.Shor
import FastMultiplication.ShorVerification.AbstractMachine.WholeProgramCorrectness
import FastMultiplication.ShorVerification.AlgorithmCorrectness.ModMulBounds.ModExp

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

def initY1 (y : Reg) : Gate :=
  match y.qubits with
  | [] => Gate.id
  | q :: _ => Gate.X q

/-- Approximate order finding using the proved valid-input ModExp circuit. -/
noncomputable def orderFindingApprox
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (a N : ℕ)
    (x y work : ExtReg)
    (flag : ℕ)
    (hworkspace : ModMulCircuitWorkspaceOK y work) : Gate :=
  (H_reg x.active) ;;
  (initY1 y.active) ;;
  (modExpApproxValid (Basis := qs.Basis) a N x.active y work flag hworkspace) ;;
  (IQFT x)


/-- The lowered implementation of approximate order finding. -/
noncomputable def orderFindingApproxLow
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (k : ℕ) (hk : 1 < k)
    (ops : Prog k)
    (a N : ℕ)
    (x y work : ExtReg)
    (flag : ℕ)
    (hmodWorkspace : ModMulCircuitWorkspaceOK y work)
    (hLowerWorkspace :
      GateWorkspaceOK ops (orderFindingApprox qs a N x y work flag hmodWorkspace)) :=
  lowerGate (Basis := qs.Basis) k hk ops
    (orderFindingApprox qs a N x y work flag hmodWorkspace) hLowerWorkspace

/-- Ideal order-finding circuit using exact modular exponentiation. -/
noncomputable def orderFindingIdeal
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [Spec]
    (a N : ℕ)
    (x y : ExtReg) : Gate :=
  (H_reg x.active) ;;
  (initY1 y.active) ;;
  (modExpIdeal' qs a N x.active y.active) ;;
  (IQFT x)

/-! =========================================================
    Section 2: Lowering setup
========================================================= -/

/-- Low-level lowering assumptions shared by lowered Shor statements. -/
structure ShorLoweringSetup where
  /-- Number of synthesis registers used by the lowering program. -/
  k : ℕ
  /-- At least two synthesis registers are available. -/
  hk : 1 < k
  /-- Program that consumes the interpolation points used by lowering. -/
  ops : Prog k
  /-- The point-consuming program is safe. -/
  consumes :
    ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops (genInterpolationPoints k)
  /-- The point-consuming program uncomputes back to the start state. -/
  returns : run? ops State.start_state = some State.start_state

/-! =========================================================
    Section 3: Approximate and ideal input predicates
========================================================= -/

/-- The input basis state is clean on every register used by Shor. -/
def ShorCleanInput
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (x y work : ExtReg)
    (flag : ℕ)
    (b0 : qs.Basis) : Prop :=
  RegEncoding.toNat x.active b0 = 0 ∧
  RegEncoding.toNat y.active b0 = 0 ∧
  y.FreshFor 2 b0 ∧
  RegEncoding.toNat work.active b0 = 0 ∧
  work.FreshFor 1 b0 ∧
  RegEncoding.toNat (qubitReg flag) b0 = 0

/--
Public assumptions for the approximate implementation of Shor.
-/
structure ShorApproxSetup
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (η : ℝ)
    (x y work : ExtReg)
    (flag : ℕ)
    (b0 : qs.Basis) : Prop where
  /-- The exponent, data, work, carry, and flag qubits do not overlap. -/
  register_layout :
    ModExpLayout x.active y work flag

  circuit_workspace :
    ModMulCircuitWorkspaceOK y work

  exponent_data_disjoint :
    ExtReg.OwnedDisjoint x y

  /-- The work register has enough extra bits for precision `η`. -/
  work_precision :
    Algorithm1Precision η y.active work.active

  /-- Shor begins in `|0⋯0⟩` on all registers it uses. -/
  clean_input :
    ShorCleanInput qs x y work flag b0

structure ShorApproxSetupMinimal
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (η : ℝ)
    (x data work : ExtReg)
    (flag : ℕ)
    (b0 : qs.Basis) :
    Prop where

  /- The data register has two available reserve qubits. -/
  data_can_grow_two :
    data.CanGrow 2

  /- The work register has one available reserve qubit. -/
  work_can_grow_one :
    work.CanGrow 1

  /- The exponent and data registers have no common owned qubits. -/
  exponent_data_disjoint :
    ExtReg.OwnedDisjoint x data

  /- The data and work registers have no common owned qubits. -/
  data_work_disjoint :
    ExtReg.OwnedDisjoint data work

  /- The flag is not owned by the data register. -/
  flag_outside_data :
    flag ∉ data.ownedQubits

  /- The flag is not owned by the work register. -/
  flag_outside_work :
    flag ∉ work.ownedQubits

  /- No active exponent/control qubit is owned by the work register. -/
  controls_outside_work :
    ∀ q ∈ x.active.qubits,
      q ∉ work.ownedQubits

  /- The flag is not an active exponent/control qubit. -/
  flag_outside_controls :
    flag ∉ x.active.qubits
  /-
  The error parameter and active work-register width satisfy
  Algorithm 1's precision requirement.
  -/
  algorithm1_precision :
    Algorithm1Precision
      η data.active work.active

  /- The exponent register starts at zero. -/
  exponent_zero :
    RegEncoding.toNat x.active b0 = 0

  /- The modular data register starts at zero. -/
  data_zero :
    RegEncoding.toNat data.active b0 = 0

  /- The two temporary data-extension qubits start at zero. -/
  data_fresh :
    data.FreshFor 2 b0

  /- The active work register starts at zero. -/
  work_zero :
    RegEncoding.toNat work.active b0 = 0

  /- The temporary work-extension qubit starts at zero. -/
  work_fresh :
    work.FreshFor 1 b0

  /-- The comparison flag starts at zero. -/
  flag_zero :
    RegEncoding.toNat (qubitReg flag) b0 = 0

private lemma active_get_mem_ownedQubits
    (x : ExtReg)
    (i : Fin (regSize x.active)) :
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
def IdealOrderFindingInput
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (x y : ExtReg)
    (b0 : qs.Basis) : Prop :=
  RegEncoding.toNat x.active b0 = 0 ∧
  RegEncoding.toNat y.active b0 = 0 ∧
  ExtReg.OwnedDisjoint x y

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
