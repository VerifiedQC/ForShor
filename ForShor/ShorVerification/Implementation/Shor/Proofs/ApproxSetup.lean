import ForShor.ShorVerification.Implementation.Shor.Statement

/-!
# The approximate setup

`ShorApproxSetup` is the register layout, workspace, precision and clean-input facts of the
approximate order-finding circuit in the form the correctness and gate-count proofs consume.
`LoweredShorReady.toShorApproxSetup` (`Workspace.lean`) builds it from the hypothesis of the
claims.
-/

namespace Shor

section
open Operations

/-- The input basis state is clean on every register used by Shor. -/
def ShorCleanInput (qs : QSemantics) [RegEncoding qs.Basis] (x y work scratch : ExtReg)
    (flag : ℕ) (b0 : qs.Basis) : Prop :=
  RegEncoding.toNat x.active b0 = 0 ∧ RegEncoding.toNat y.active b0 = 0 ∧ y.FreshFor 2 b0 ∧
  RegEncoding.toNat work.active b0 = 0 ∧ work.FreshFor 1 b0 ∧
  RegEncoding.toNat scratch.active b0 = 0 ∧ scratch.FreshFor 1 b0 ∧
  RegEncoding.toNat (qubitReg flag) b0 = 0

/-- Public assumptions for the approximate implementation of Shor. -/
structure ShorApproxSetup (qs : QSemantics) [RegEncoding qs.Basis] (η : ℝ) (N : ℕ)
    (x y work scratch : ExtReg) (flag : ℕ) (b0 : qs.Basis) : Type where
  /-- The exponent, data, work, carry, and flag qubits do not overlap. -/
  register_layout : ModExpLayout x.active y work flag
  /-- The modular-exponentiation subcircuit has enough local workspace. -/
  circuit_workspace : ModMulCircuitWorkspaceOK y work
  /-- The concrete Step-4 comparator and its Step-3 scratch are well laid out. -/
  step4_workspace : CmpLtNWWorkspace N (y.grow 1) work scratch flag
  /-- The exponent register is owned separately from the modular data register. -/
  exponent_data_disjoint : ExtReg.OwnedDisjoint x y
  /-- The exponent register is owned separately from comparator scratch. -/
  exponent_scratch_disjoint : ExtReg.OwnedDisjoint x scratch
  /-- The work register has enough extra bits for precision `η`. -/
  work_precision : Algorithm1Precision η y.active work.active
  /-- Shor begins in `|0⋯0⟩` on all registers it uses. -/
  clean_input : ShorCleanInput qs x y work scratch flag b0

end

end Shor
