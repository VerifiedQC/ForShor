import ForShor.Emit.Json.LowGateJson
import ForShor.ShorVerification.Framework.AbstractMachine.MLowGate

/-!
# `MLowGate` JSON printer (`forshor.mlowgate/v1`)

Serializes a lowered measurement-language program (`MLowGate`: unitary `LowGate` blocks,
mid-circuit measurement with reset, record-controlled phases) for consumption outside Lean.
Output-only tooling, no proof obligations, like `LowGateJson.lean`.

A leaf module: nothing that prints `forshor.lowgate/v2` imports it, and it changes no
existing printer, so every existing document is byte-identical. Only the `readout`
subcommand of `forshor_emit` (`Emit/Lower/Readout.lean`) prints this schema.

## Nodes

The circuit is one flat `{"op":"seq","body":[…]}`, in execution order:

* `unitary g` contributes the leaves of `g` (`LowGate.flattenSeq g`), each printed by
  `lowGateJson`, exactly as in `forshor.lowgate/v2` (an `id` contributes nothing);
* `seq a b` contributes the nodes of `a`, then those of `b`;
* `measureReset q` is `{"op":"measureReset","q":q}`: measure qubit `q` in the Z basis,
  append the outcome to the record, reset `q` to `|0⟩`;
* `ffPhase q j` is `{"op":"ffPhase","q":q,"j":j}`: `Phase q θ` with
  `θ = ffAngle j rec` (units of `π`), `rec` the record when the node runs.

The node carries `j` only, not the angle and not a symbolic rule. The angle is not a
constant of the circuit (it depends on outcomes not known when the document is printed),
and `ffAngle` is one fixed rule for every node, so the document states it once, in its
`ff_angle_rule` and `record` fields, and a consumer derives each angle from `j` and the
record. Printing a per-node rule would repeat the same text at every node and invite a
consumer to parse it.
-/

namespace Shor

open Lean (Json)

/-- The schema of a printed `MLowGate` document. Distinct from `forshor.lowgate/v2`, so a
consumer that only knows that schema refuses the document instead of reading it. -/
def mlowgateSchema : String := "forshor.mlowgate/v1"

/-- The record convention, as printed in the `record` field. -/
def recordConventionText : String :=
  "rec[i] = outcome (0 or 1) of the i-th measureReset node executed (absolute slot, " ++
  "oldest first, 0-based); each measureReset appends one slot"

/-- The angle rule of every `ffPhase` node (`ffAngle`, `Framework/AbstractMachine/MGate.lean`),
as printed in the `ff_angle_rule` field. -/
def ffAngleRuleText : String :=
  "ffPhase(q, j) applies Phase(q, theta) with theta = -(sum_{i=0}^{j-1} rec[i] / 2^(j-i)) " ++
  "in units of pi (a dyadic rational; a missing slot counts as 0)"

/-- The nodes of a program, in execution order (see the module docstring). -/
def mlowGateNodes : MLowGate → List Json
  | .unitary g => (LowGate.flattenSeq g).map lowGateJson
  | .seq a b => mlowGateNodes a ++ mlowGateNodes b
  | .measureReset q => [Json.mkObj [("op", Json.str "measureReset"), ("q", (q : Json))]]
  | .ffPhase q j => [Json.mkObj [("op", Json.str "ffPhase"), ("q", (q : Json)), ("j", (j : Json))]]

/-- The number of `measureReset` nodes, i.e. the length of the final record. -/
def MLowGate.numMeas : MLowGate → ℕ
  | .unitary _ => 0
  | .seq a b => a.numMeas + b.numMeas
  | .measureReset _ => 1
  | .ffPhase _ _ => 0

/-- The circuit as one flat `seq`. -/
def mlowGateJson (g : MLowGate) : Json :=
  Json.mkObj [("op", Json.str "seq"), ("body", Json.arr (mlowGateNodes g).toArray)]

/-- Document wrapper for an `MLowGate`. No resource fields: pricing the new nodes is the
consumer's (`ffPhase` is one rotation of a record-dependent angle). -/
def emitMLowGateDoc (g : MLowGate) (metaJson : Json) : Json :=
  Json.mkObj [
    ("schema", Json.str mlowgateSchema),
    ("bit_order", Json.str "lsb_first"),
    ("angle_unit", Json.str "pi"),
    ("record", Json.str recordConventionText),
    ("ff_angle_rule", Json.str ffAngleRuleText),
    ("num_measurements", (g.numMeas : Json)),
    ("circuit", mlowGateJson g),
    ("meta", metaJson)
  ]

end Shor
