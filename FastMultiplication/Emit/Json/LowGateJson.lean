import FastMultiplication.Emit.Json.Common
import FastMultiplication.ShorVerification.Framework.Contract

/-!
# `LowGate` JSON printer

Serializes a lowered Shor circuit (`LowGate`) and its enclosing program
(`ShorOrderFindingProgram`) to JSON, for consumption outside Lean. This file
has no proof obligations: it is output-only tooling, not part of the verified
core.
-/

namespace Shor

open Lean (Json)

-- Flatten nested `seq` nodes into an ordered list of leaves, dropping `id`s.
-- Not `partial`: `.seq a b`'s two recursive calls are on the strictly
-- smaller subterms `a`/`b`, so Lean's ordinary structural-recursion
-- equation compiler accepts this directly (unlike `lowGateJson` below,
-- whose `seq` case calls back into `flattenSeq` first) — and R6
-- (`Emit/Proofs/Correct.lean`) needs `flattenSeq`'s equation lemmas to
-- restate `evalNode`'s output up to "same flattened gate list", the same
-- notion of circuit equality `Tests.lean`'s R2 `native_decide` checks
-- already use via `lowGateJson`.
def LowGate.flattenSeq : LowGate → List LowGate
  | .id => []
  | .seq a b => flattenSeq a ++ flattenSeq b
  | g => [g]

/-- Serialize a lowered gate tree. Op names are exactly the `LowGate`
constructor names. `partial`: this is a plain structural tree traversal with
no proof obligations, and the equation compiler's ordinary termination check
does not see through the `flattenSeq` helper used for the `seq` case. -/
partial def lowGateJson : LowGate → Json
  | .id => Json.mkObj [("op", Json.str "id")]
  | .seq a b =>
      Json.mkObj [
        ("op", Json.str "seq"),
        ("body", Json.arr ((LowGate.flattenSeq (.seq a b)).map lowGateJson).toArray)
      ]
  | .adj g =>
      Json.mkObj [("op", Json.str "adj"), ("body", lowGateJson g)]
  | .H q =>
      Json.mkObj [("op", Json.str "H"), ("q", (q : Json))]
  | .X q =>
      Json.mkObj [("op", Json.str "X"), ("q", (q : Json))]
  | .Phase q a =>
      Json.mkObj [("op", Json.str "Phase"), ("q", (q : Json)), ("angle", angleJson a)]
  | .CNOT ctrl target =>
      Json.mkObj [("op", Json.str "CNOT"), ("ctrl", (ctrl : Json)), ("target", (target : Json))]
  | .Toffoli c1 c2 target =>
      Json.mkObj [
        ("op", Json.str "Toffoli"),
        ("c1", (c1 : Json)), ("c2", (c2 : Json)), ("target", (target : Json))
      ]
  | .ShiftL r n =>
      Json.mkObj [("op", Json.str "ShiftL"), ("r", extRegJson r), ("n", (n : Json))]
  | .ShiftR r n =>
      Json.mkObj [("op", Json.str "ShiftR"), ("r", extRegJson r), ("n", (n : Json))]
  | .Negate r =>
      Json.mkObj [("op", Json.str "Negate"), ("r", extRegJson r)]
  | .AddScaled dst src negSrc shift =>
      Json.mkObj [
        ("op", Json.str "AddScaled"),
        ("dst", extRegJson dst), ("src", extRegJson src),
        ("negSrc", Json.bool negSrc), ("shift", (shift : Json))
      ]
  | .zeroExtend r n =>
      Json.mkObj [("op", Json.str "zeroExtend"), ("r", extRegJson r), ("n", (n : Json))]
  | .signExtend r n =>
      Json.mkObj [("op", Json.str "signExtend"), ("r", extRegJson r), ("n", (n : Json))]
  | .zeroDealloc r n =>
      Json.mkObj [("op", Json.str "zeroDealloc"), ("r", extRegJson r), ("n", (n : Json))]
  | .signDealloc r n =>
      Json.mkObj [("op", Json.str "signDealloc"), ("r", extRegJson r), ("n", (n : Json))]
  | .RadixReverse r m =>
      Json.mkObj [("op", Json.str "RadixReverse"), ("r", regJson r), ("m", (m : Json))]

/-- Document wrapper: a submitted program plus caller-supplied metadata. -/
def emitProgram (P : ShorOrderFindingProgram) (metaJson : Json) : Json :=
  Json.mkObj [
    ("schema", Json.str "forshor.lowgate/v2"),
    ("bit_order", Json.str "lsb_first"),
    ("angle_unit", Json.str "pi"),
    ("output_register", regJson P.output),
    ("gate_count", (LowGate.gateCount shorGateCostModel P.circuit : Json)),
    ("qubit_count", (LowGate.qubitCount shorGateResourceModel P.circuit : Json)),
    ("max_qubit_index", (((LowGate.usedQubits P.circuit).sup id : ℕ) : Json)),
    ("resources", gateResourcesJson (LowGate.resources shorGateResourceModel P.circuit)),
    ("circuit", lowGateJson P.circuit),
    ("meta", metaJson)
  ]

/-- Document wrapper for a bare `LowGate` with no distinguished output
register (`pp`/`cpp`/`qft`'s flat view — there is no single "the" instance
program here, just the lowered circuit itself). Same schema/fields as
`emitProgram` minus `output_register`. -/
def emitLowGateDoc (g : LowGate) (metaJson : Json) : Json :=
  Json.mkObj [
    ("schema", Json.str "forshor.lowgate/v2"),
    ("bit_order", Json.str "lsb_first"),
    ("angle_unit", Json.str "pi"),
    ("gate_count", (LowGate.gateCount shorGateCostModel g : Json)),
    ("qubit_count", (LowGate.qubitCount shorGateResourceModel g : Json)),
    ("max_qubit_index", (((LowGate.usedQubits g).sup id : ℕ) : Json)),
    ("resources", gateResourcesJson (LowGate.resources shorGateResourceModel g)),
    ("circuit", lowGateJson g),
    ("meta", metaJson)
  ]

/-- Document wrapper for an annotated plan (`--annotated`): same envelope,
`forshor.plan/v1` schema, `"plan"` instead of `"circuit"`. -/
def emitPlanDoc (planJ : Json) (metaJson : Json) : Json :=
  Json.mkObj [
    ("schema", Json.str "forshor.plan/v1"),
    ("bit_order", Json.str "lsb_first"),
    ("angle_unit", Json.str "pi"),
    ("plan", planJ),
    ("meta", metaJson)
  ]

end Shor
