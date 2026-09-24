import FastMultiplication.ShorVerification.Implementation.Shor.Circuit.Workspace
import FastMultiplication.ShorVerification.Implementation.Shor.Spec.Cleanliness
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.ModExp
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.Workspace
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Spec.Precision

/-!
# Shor Setup Records

The user-facing setup/readiness records consumed by the final Shor
correctness statements, and the bridge from the lower-level implementation
setup to the public one.
-/
namespace Shor
open Operations

/-! =========================================================
    Lowering Program Setup
========================================================= -/

/-- Low-level lowering assumptions shared by lowered Shor statements. -/
structure ShorLoweringSetup where
  /-- Number of synthesis registers used by the lowering program. -/
  k : ℕ
  /-- At least two synthesis registers are available. -/
  hk : 1 < k
  /-- Interpolation points the submission's table is built against. -/
  pts : List Point
  /-- One point per product coefficient. -/
  hpts : pts.length = q k
  /-- The chosen points interpolate a degree-`2k - 2` polynomial. -/
  good : GoodToomCookPoints k pts hpts
  /-- Program that consumes the interpolation points used by lowering. -/
  ops : Prog k
  /-- The point-consuming program is safe. -/
  consumes :
    ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops pts
  /-- The point-consuming program uncomputes back to the start state. -/
  returns : run? ops State.start_state = some State.start_state

/-! =========================================================
    Approximate Setup
========================================================= -/

/-- Public assumptions for the approximate implementation of Shor. -/
structure ShorApproxSetup
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (η : ℝ)
    (N : ℕ)
    (x y work scratch : ExtReg)
    (flag : ℕ)
    (b0 : qs.Basis) : Type where
  /-- The exponent, data, work, carry, and flag qubits do not overlap. -/
  register_layout :
    ModExpLayout x.active y work flag

  /-- The modular-exponentiation subcircuit has enough local workspace. -/
  circuit_workspace :
    ModMulCircuitWorkspaceOK y work

  /-- The concrete Step-4 comparator and its Step-3 scratch are well laid out. -/
  step4_workspace :
    CmpLtNWWorkspace N (y.grow 1) work scratch flag

  /-- The exponent register is owned separately from the modular data register. -/
  exponent_data_disjoint :
    ExtReg.OwnedDisjoint x y

  /-- The exponent register is owned separately from comparator scratch. -/
  exponent_scratch_disjoint :
    ExtReg.OwnedDisjoint x scratch

  /-- The work register has enough extra bits for precision `η`. -/
  work_precision :
    Algorithm1Precision η y.active work.active

  /-- Shor begins in `|0⋯0⟩` on all registers it uses. -/
  clean_input :
    ShorCleanInput qs x y work scratch flag b0

/--
Lower-level assumptions from which the public approximate setup is reconstructed
in `Shor.Spec.Setup` (`ShorApproxSetupMinimal.toShorApproxSetup`).
-/
structure ShorApproxSetupMinimal
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (η : ℝ)
    (N : ℕ)
    (x data work scratch : ExtReg)
    (flag : ℕ)
    (b0 : qs.Basis) :
    Type where

  /-- The data register has two available reserve qubits. -/
  data_can_grow_two :
    data.CanGrow 2

  /-- The work register has one available reserve qubit. -/
  work_can_grow_one :
    work.CanGrow 1

  /-- The comparator scratch layout is the same one used by Steps 3 and 4. -/
  step4_workspace :
    CmpLtNWWorkspace N (data.grow 1) work scratch flag

  /-- The exponent and data registers have no common owned qubits. -/
  exponent_data_disjoint :
    ExtReg.OwnedDisjoint x data

  /-- The exponent register is owned separately from comparator scratch. -/
  exponent_scratch_disjoint :
    ExtReg.OwnedDisjoint x scratch

  /-- The data and work registers have no common owned qubits. -/
  data_work_disjoint :
    ExtReg.OwnedDisjoint data work

  /-- The flag is not owned by the data register. -/
  flag_outside_data :
    flag ∉ data.ownedQubits

  /-- The flag is not owned by the work register. -/
  flag_outside_work :
    flag ∉ work.ownedQubits

  /-- No active exponent/control qubit is owned by the work register. -/
  controls_outside_work :
    ∀ q ∈ x.active.qubits,
      q ∉ work.ownedQubits

  /-- The flag is not an active exponent/control qubit. -/
  flag_outside_controls :
    flag ∉ x.active.qubits

  /--
  The error parameter and active work-register width satisfy
  Algorithm 1's precision requirement.
  -/
  algorithm1_precision :
    Algorithm1Precision
      η data.active work.active

  /-- The exponent register starts at zero. -/
  exponent_zero :
    RegEncoding.toNat x.active b0 = 0

  /-- The modular data register starts at zero. -/
  data_zero :
    RegEncoding.toNat data.active b0 = 0

  /-- The two temporary data-extension qubits start at zero. -/
  data_fresh :
    data.FreshFor 2 b0

  /-- The active work register starts at zero. -/
  work_zero :
    RegEncoding.toNat work.active b0 = 0

  /-- The temporary work-extension qubit starts at zero. -/
  work_fresh :
    work.FreshFor 1 b0

  /-- The active comparator scratch register starts at zero. -/
  scratch_zero :
    RegEncoding.toNat scratch.active b0 = 0

  /-- The borrowed comparator reserve bit starts at zero. -/
  scratch_fresh :
    scratch.FreshFor 1 b0

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

/-- Bridge from the lower-level setup to the public approximate setup. -/
def ShorApproxSetupMinimal.toShorApproxSetup
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    {η : ℝ}
    {N : ℕ}
    {x data work scratch : ExtReg}
    {flag : ℕ}
    {b0 : qs.Basis}
    (h :
      ShorApproxSetupMinimal
        qs η N x data work scratch flag b0) :
    ShorApproxSetup
      qs η N x data work scratch flag b0 := by
  refine
    {
      register_layout := ?_
      circuit_workspace := ?_
      step4_workspace := h.step4_workspace
      exponent_data_disjoint :=
        h.exponent_data_disjoint
      exponent_scratch_disjoint :=
        h.exponent_scratch_disjoint
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
        h.scratch_zero,
        h.scratch_fresh,
        h.flag_zero⟩

/-! =========================================================
    Lowered Readiness Package
========================================================= -/

/-- Public readiness package for static workspace and initial cleanliness. -/
structure LoweredShorReady
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (lowering : ShorLoweringSetup)
    (η : ℝ)
    (a N : ℕ)
    (x y work scratch : ExtReg)
    (flag : ℕ)
    (b0 : qs.Basis) :
    Type where

  /-- Layout, precision, and clean active-register assumptions. -/
  approx :
    ShorApproxSetupMinimal qs η N x y work scratch flag b0

  /-- Static reserve capacity is sufficient for all recursive lowerers. -/
  workspace_large_enough :
    ShorWorkspaceLargeEnough lowering.ops x y work scratch

  /-- Shared temporary resources do not overlap unsafe regions. -/
  workspace_isolated :
    ShorWorkspaceIsolation x work scratch flag

  /-- All reserve registers that may be allocated begin at zero. -/
  workspace_initially_zero :
    ShorWorkspaceCleanInput x y work scratch b0

/-! =========================================================
    Classical Factoring Instance
========================================================= -/

/-- Classical assumptions on a modulus for the final factoring theorem. -/
structure ShorFactoringInstance where
  /-- The modulus to factor. -/
  N : ℕ
  /-- Shor's classical reduction is stated for odd composite moduli. -/
  odd : Odd N
  /-- The modulus is nontrivial. -/
  gt_two : N > 2
  /-- The modulus is not a prime power. -/
  not_prime_power : ∀ (p k : ℕ), Nat.Prime p → N ≠ p ^ k

end Shor
