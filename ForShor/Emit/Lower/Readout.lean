import ForShor.ShorVerification.Implementation.Readout.Proofs.SemiclassicalHyps
import ForShor.ShorVerification.Implementation.Reference.Standard.Proofs.Readiness
import ForShor.Emit.Lower.Shor
import ForShor.Emit.Json.MLowGateJson

/-!
# `readout` subcommand: the lowered semiclassical order-finding circuit

`forshor_emit readout <k> <a> <N> <level> <rounds>` prints
`orderFindingSemiclassicalLow` (`Implementation/Readout/Lowering.lean`) under the one-band
standard policy of arity `k`, at the reference layout `allocateReferenceLayout` for the
instance `(a, N)` at approximation level `level`, with `rounds` readout rounds, as a
`forshor.mlowgate/v1` document (`Emit/Json/MLowGateJson.lean`). The control qubit is the
first qubit of the reference exponent register (`referenceControl`), the choice of
`reference_semiclassical_peak`; the full readout of the reference instance has
`rounds = referenceXWidth inst`.

This is the only entry point that prints the new schema; every other subcommand is
unchanged. The workspace hypothesis of the lowering comes from the coherent circuit's at
the same layout (`semiclassical_hyps_of_coherent`, `Readout/Proofs/SemiclassicalHyps.lean`).
-/

namespace Shor.Readout.EmitRef

open Shor

/-- The semiclassical control qubit at the reference layout: the first qubit of the
reference exponent register (the default `0` is never used, the register is non-empty,
`referenceControl_cons`). -/
def referenceControl (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (ℓ : ℕ) : ℕ :=
  (Reference.allocateReferenceLayout P inst ℓ).x.active.qubits.headD 0

theorem referenceControl_cons (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (ℓ : ℕ) :
    ∃ rest, (Reference.allocateReferenceLayout P inst ℓ).x.active.qubits
      = referenceControl P inst ℓ :: rest := by
  have hxw : (Reference.allocateReferenceLayout P inst ℓ).x.width = Reference.referenceXWidth inst :=
    Reference.allocateReferenceLayout_x_width P inst ℓ
  have hpos : 0 < (Reference.allocateReferenceLayout P inst ℓ).x.active.qubits.length := by
    show 0 < (Reference.allocateReferenceLayout P inst ℓ).x.width
    rw [hxw, Reference.referenceXWidth, Nat.log2_eq_log_two]
    have := inst.range
    exact Nat.log_pos Nat.one_lt_two (by nlinarith)
  unfold referenceControl
  cases h : (Reference.allocateReferenceLayout P inst ℓ).x.active.qubits with
  | nil => rw [h] at hpos; simp at hpos
  | cons c rest => exact ⟨rest, rfl⟩

/-- The lowering hypothesis of the semiclassical circuit at the reference layout, for every
number of rounds. -/
theorem reference_sc_workspaceOK (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (ℓ m : ℕ) :
    MGate.WorkspaceOK P (orderFindingSemiclassical inst.a inst.N (referenceControl P inst ℓ) m
      (Reference.allocateReferenceLayout P inst ℓ).data
      (Reference.allocateReferenceLayout P inst ℓ).work
      (Reference.allocateReferenceLayout P inst ℓ).scratch
      (Reference.allocateReferenceLayout P inst ℓ).flag
      (Reference.reference_modMulCircuitWorkspaceOK P inst ℓ)
      (Reference.reference_step4Workspace P inst ℓ)) := by
  obtain ⟨rest, hc⟩ := referenceControl_cons P inst ℓ
  have hlay : OrderFindingSpaceLayout (Reference.allocateReferenceLayout P inst ℓ).x
      (Reference.allocateReferenceLayout P inst ℓ).data
      (Reference.allocateReferenceLayout P inst ℓ).work
      (Reference.allocateReferenceLayout P inst ℓ).scratch
      (Reference.allocateReferenceLayout P inst ℓ).flag :=
    ⟨Reference.reference_exponent_data_disjoint P inst ℓ,
     Reference.reference_exponent_work_disjoint P inst ℓ,
     Reference.reference_exponent_scratch_disjoint P inst ℓ,
     Reference.reference_flag_outside_exponent P inst ℓ⟩
  exact (semiclassical_hyps_of_coherent hc
    (Reference.reference_gateWorkspaceOK P inst ℓ) hlay).1 m

/-- The lowered semiclassical circuit at the reference layout, with `m` rounds. -/
def referenceSemiclassicalLow (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance)
    (ℓ m : ℕ) : MLowGate :=
  orderFindingSemiclassicalLow P inst.a inst.N (referenceControl P inst ℓ) m
    (Reference.allocateReferenceLayout P inst ℓ).data
    (Reference.allocateReferenceLayout P inst ℓ).work
    (Reference.allocateReferenceLayout P inst ℓ).scratch
    (Reference.allocateReferenceLayout P inst ℓ).flag
    (Reference.reference_modMulCircuitWorkspaceOK P inst ℓ)
    (Reference.reference_step4Workspace P inst ℓ)
    (reference_sc_workspaceOK P inst ℓ m)

end Shor.Readout.EmitRef

namespace Emit.Lower.Readout

/-- Usage of the `readout` subcommand. Printed by it alone: `forshor_emit`'s `usageText`
is left byte-identical. -/
def readoutUsage : String :=
  "usage: forshor_emit readout <k> <a> <N> <level> <rounds>\n" ++
  "  prints the lowered semiclassical order-finding circuit (forshor.mlowgate/v1) at the\n" ++
  "  reference layout of (a, N) at approximation level <level>, with <rounds> readout rounds\n"

def runReadout (k a N level rounds : ℕ) : IO UInt32 := do
  if hk : 1 < k then
    if hrange : 0 < a ∧ a < N then
      if hcop : Nat.gcd a N = 1 then
        let pol := Shor.standardPolicy k hk
        let inst : Shor.ShorOrderFindingInstance := ⟨a, N, hrange, hcop⟩
        let g := Shor.Readout.EmitRef.referenceSemiclassicalLow pol inst level rounds
        let layout := Shor.Reference.allocateReferenceLayout pol inst level
        let metaJson : Lean.Json :=
          Lean.Json.mkObj [
            ("k", (k : Lean.Json)),
            ("a", (a : Lean.Json)),
            ("N", (N : Lean.Json)),
            ("level", (level : Lean.Json)),
            ("rounds", (rounds : Lean.Json)),
            ("full_rounds", (Shor.Reference.referenceXWidth inst : Lean.Json)),
            ("control", (Shor.Readout.EmitRef.referenceControl pol inst level : Lean.Json)),
            ("source", Lean.Json.str "Shor.orderFindingSemiclassicalLow at Shor.Reference.allocateReferenceLayout"),
            ("layout", Shor.Reference.layoutJson layout)
          ]
        IO.println (Shor.emitMLowGateDoc g metaJson).compress
        return 0
      else
        IO.eprintln s!"error: need gcd a N = 1 (a = {a}, N = {N})"
        return 2
    else
      IO.eprintln s!"error: need 0 < a < N (a = {a}, N = {N})"
      return 2
  else
    IO.eprintln s!"error: need k > 1 (k = {k})"
    return 2

/-- `readout <k> <a> <N> <level> <rounds>`: all five natural numbers, nothing else. -/
def runReadoutArgs : List String → IO UInt32
  | [kStr, aStr, NStr, lStr, rStr] =>
      match kStr.toNat?, aStr.toNat?, NStr.toNat?, lStr.toNat?, rStr.toNat? with
      | some k, some a, some N, some l, some r => runReadout k a N l r
      | _, _, _, _, _ => do
          IO.eprintln "error: k, a, N, level, rounds must all be natural numbers"
          IO.eprint readoutUsage
          return 2
  | _ => do
      IO.eprintln "error: readout takes exactly five arguments"
      IO.eprint readoutUsage
      return 2

end Emit.Lower.Readout
