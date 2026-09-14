import FastMultiplication.ShorVerification.Implementation.Reference.StandardLoweringSetup
import FastMultiplication.ShorVerification.Implementation.Reference.ReferenceShorImplementation
import FastMultiplication.Emit.LowGateJson

/-!
# Emitter acceptance tests

Small-`N` sanity checks for the JSON printer. These are acceptance tests, not
part of the verified core: nothing here is imported by
`Shor.Shor_correct`/`Shor.exists_shorGateCountBound`.
-/

namespace Shor.Emit.Tests

open Lean (Json)

/-- A tiny concrete instance: `a = 2`, `N = 3` (`gcd 2 3 = 1`, `0 < 2 < 3`). -/
def smallLowering : ShorLoweringSetup := standardLoweringSetup 2 (by decide)

def smallInst : ShorOrderFindingInstance := ⟨2, 15, by decide, by decide⟩

def smallProgram : ShorOrderFindingProgram :=
  Reference.referenceProgramAt smallLowering 0 smallInst

def smallJson : Json := emitProgram smallProgram (Json.mkObj [])

-- 1. The emitted document round-trips: the `gate_count` field extracted back
-- out of the JSON agrees with the value computed directly on the circuit.
example :
    ((smallJson.getObjVal? "gate_count").bind Json.getNat?).toOption
      =
    some (LowGate.gateCount shorGateCostModel smallProgram.circuit) := by
  native_decide

-- 1b. The document declares the expected schema.
example :
    ((smallJson.getObjVal? "schema").bind Json.getStr?).toOption = some "forshor.lowgate/v2" := by
  native_decide

/-- 2. Every `Angle` has a positive denominator (structural: `ℚ`'s invariant). -/
example (a : Angle) : 0 < a.den := a.pos

/-- 2b. Every register's physical qubit list is duplicate-free (structural:
`Reg`'s own `nodup` field, carried by construction). -/
example (r : Reg) : r.qubits.Nodup := r.nodup

/-- 3. The final submitted program is the reference program at the chosen
precision — documents that `standardLoweringSetup`/`referenceProgramAt` (what
the emitter calls) matches what `referenceShorImplementation` actually
submits. -/
example (lowering : ShorLoweringSetup) (inst : ShorOrderFindingInstance) :
    Reference.referenceSubmittedProgram lowering inst
      =
    Reference.referenceProgramAt lowering (Reference.referenceChosenPrecision inst.N) inst :=
  rfl

/-- 4. Exercise the `k = 3` (`q k = 5`) interpolation-coefficient path. -/
def k3Lowering : ShorLoweringSetup := standardLoweringSetup 3 (by decide)

def k3Program : ShorOrderFindingProgram :=
  Reference.referenceProgramAt k3Lowering 0 smallInst

example : 0 < LowGate.gateCount shorGateCostModel k3Program.circuit := by native_decide

#eval LowGate.gateCount shorGateCostModel k3Program.circuit
end Shor.Emit.Tests
