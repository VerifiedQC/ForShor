import ForShor.Emit.Json.MLowGateJson
import ForShor.Emit.Lower.Readout
import ForShor.Emit.Lower.Qft

/-!
# Emitter acceptance tests: the measurement-language document

Tests of `forshor.mlowgate/v1` (`Emit/Json/MLowGateJson.lean`) and of the
`readout` entry point's circuit (`Emit/Lower/Readout.lean`). Like `Emit/Tests.lean`
these are acceptance tests, not part of the verified core. They are `#guard`s
(evaluated by the interpreter at build time, so a failing check fails the build)
plus one kernel-checked `theorem`; nothing here uses `native_decide`.

* `emit_old_unchanged`: the `forshor.lowgate/v2` document of a small fixed `LowGate`
  is byte-equal to the string captured from `emitLowGateDoc` at the parent commit
  (ae6171c), before `MLowGateJson` existed; and `forshor_emit qft 2 4 --flat`'s document
  (`buildQFT`) is byte-equal to the parent binary's output.
* `emit_new_nodes_roundtrip`: a small hand-built `MLowGate` and the lowered
  semiclassical circuit at one and two rounds (`a = 2`, `N = 3`, `k = 2`, level 0),
  printed and parsed back with `Json.parse`, carry exactly the expected nodes in order.
* `mlowgate_schema_ne_lowgate`: the new schema string is not `forshor.lowgate/v2`.
-/

namespace Shor.Emit.MTests

open Lean (Json)
open Shor

/-! ## `emit_old_unchanged` -/

def r3 : Reg := ⟨[4, 5, 6], by decide⟩

/-- One leaf of most `LowGate` kinds (a nested `adj` included). -/
def tinyLow : LowGate :=
  .seq (.H 0) (.seq (.X 1) (.seq (.Phase 0 (-3/4)) (.seq (.CNOT 0 1) (.seq (.Toffoli 0 1 2)
    (.seq (.adj (.seq (.H 2) .id)) (.seq (.Negate (ExtReg.ofReg r3)) (.RadixReverse r3 1)))))))

/-- `(emitLowGateDoc tinyLow (Json.mkObj [])).compress`, captured at ae6171c (before this
task) with `lake env lean` on a scratch file. -/
def tinyLowCaptured : String :=
  "{\"angle_unit\":\"pi\",\"bit_order\":\"lsb_first\",\"circuit\":{\"body\":[{\"op\":\"H\",\"q\":0}," ++
  "{\"op\":\"X\",\"q\":1},{\"angle\":{\"den\":4,\"num\":-3,\"unit\":\"pi\"},\"op\":\"Phase\",\"q\":0}," ++
  "{\"ctrl\":0,\"op\":\"CNOT\",\"target\":1},{\"c1\":0,\"c2\":1,\"op\":\"Toffoli\",\"target\":2}," ++
  "{\"body\":{\"body\":[{\"op\":\"H\",\"q\":2}],\"op\":\"seq\"},\"op\":\"adj\"}," ++
  "{\"op\":\"Negate\",\"r\":{\"active\":[4,5,6],\"reserve\":[]}},{\"m\":1,\"op\":\"RadixReverse\",\"r\":[4,5,6]}]," ++
  "\"op\":\"seq\"},\"gate_count\":80,\"max_qubit_index\":6,\"meta\":{},\"negation\":\"oneQubit\"," ++
  "\"qubit_count\":7,\"resources\":{\"cleanAnc\":1,\"cnot\":47,\"h\":2,\"rz\":1,\"toffoli\":13,\"x\":17}," ++
  "\"schema\":\"forshor.lowgate/v2\"}"

-- emit_old_unchanged
#guard (emitLowGateDoc tinyLow (Json.mkObj [])).compress == tinyLowCaptured

-- The unitary part of an `MLowGate` is printed with the old printer, node for node.
#guard mlowGateNodes (.unitary tinyLow) == (LowGate.flattenSeq tinyLow).map lowGateJson

/-! ## `emit_old_unchanged`, one existing entry point -/

/-- `forshor_emit qft 2 4 --flat`'s stdout (newline stripped) from the binary built at the
parent commit ae6171c, before `MLowGateJson` existed. -/
def qftFlatCaptured : String :=
  "{\"angle_unit\":\"pi\",\"bit_order\":\"lsb_first\",\"circuit\":{\"body\":[{\"op\":\"H\",\"q\":3},{\"n\":1,\"op\":\"zero"
  ++ "Extend\",\"r\":{\"active\":[2],\"reserve\":[4]}},{\"n\":1,\"op\":\"zeroExtend\",\"r\":{\"active\":[3],\"reserve\":["
  ++ "5]}},{\"angle\":{\"den\":4,\"num\":1,\"unit\":\"pi\"},\"op\":\"Phase\",\"q\":2},{\"angle\":{\"den\":4,\"num\":1,\"unit\""
  ++ ":\"pi\"},\"op\":\"Phase\",\"q\":3},{\"ctrl\":2,\"op\":\"CNOT\",\"target\":3},{\"angle\":{\"den\":4,\"num\":-1,\"unit\":\""
  ++ "pi\"},\"op\":\"Phase\",\"q\":3},{\"ctrl\":2,\"op\":\"CNOT\",\"target\":3},{\"angle\":{\"den\":2,\"num\":-1,\"unit\":\"pi"
  ++ "\"},\"op\":\"Phase\",\"q\":2},{\"angle\":{\"den\":2,\"num\":-1,\"unit\":\"pi\"},\"op\":\"Phase\",\"q\":5},{\"ctrl\":2,\"op"
  ++ "\":\"CNOT\",\"target\":5},{\"angle\":{\"den\":2,\"num\":1,\"unit\":\"pi\"},\"op\":\"Phase\",\"q\":5},{\"ctrl\":2,\"op\":\""
  ++ "CNOT\",\"target\":5},{\"angle\":{\"den\":2,\"num\":-1,\"unit\":\"pi\"},\"op\":\"Phase\",\"q\":4},{\"angle\":{\"den\":2,"
  ++ "\"num\":-1,\"unit\":\"pi\"},\"op\":\"Phase\",\"q\":3},{\"ctrl\":4,\"op\":\"CNOT\",\"target\":3},{\"angle\":{\"den\":2,\"n"
  ++ "um\":1,\"unit\":\"pi\"},\"op\":\"Phase\",\"q\":3},{\"ctrl\":4,\"op\":\"CNOT\",\"target\":3},{\"angle\":{\"den\":1,\"num\""
  ++ ":1,\"unit\":\"pi\"},\"op\":\"Phase\",\"q\":4},{\"angle\":{\"den\":1,\"num\":1,\"unit\":\"pi\"},\"op\":\"Phase\",\"q\":5},{"
  ++ "\"ctrl\":4,\"op\":\"CNOT\",\"target\":5},{\"angle\":{\"den\":1,\"num\":-1,\"unit\":\"pi\"},\"op\":\"Phase\",\"q\":5},{\"c"
  ++ "trl\":4,\"op\":\"CNOT\",\"target\":5},{\"n\":1,\"op\":\"zeroDealloc\",\"r\":{\"active\":[3],\"reserve\":[5]}},{\"n\":"
  ++ "1,\"op\":\"zeroDealloc\",\"r\":{\"active\":[2],\"reserve\":[4]}},{\"op\":\"H\",\"q\":2},{\"m\":1,\"op\":\"RadixRevers"
  ++ "e\",\"r\":[2,3]},{\"n\":1,\"op\":\"zeroExtend\",\"r\":{\"active\":[0,1],\"reserve\":[4]}},{\"n\":1,\"op\":\"zeroExte"
  ++ "nd\",\"r\":{\"active\":[2,3],\"reserve\":[5]}},{\"angle\":{\"den\":16,\"num\":1,\"unit\":\"pi\"},\"op\":\"Phase\",\"q\""
  ++ ":0},{\"angle\":{\"den\":16,\"num\":1,\"unit\":\"pi\"},\"op\":\"Phase\",\"q\":2},{\"ctrl\":0,\"op\":\"CNOT\",\"target\":2"
  ++ "},{\"angle\":{\"den\":16,\"num\":-1,\"unit\":\"pi\"},\"op\":\"Phase\",\"q\":2},{\"ctrl\":0,\"op\":\"CNOT\",\"target\":2}"
  ++ ",{\"angle\":{\"den\":8,\"num\":1,\"unit\":\"pi\"},\"op\":\"Phase\",\"q\":0},{\"angle\":{\"den\":8,\"num\":1,\"unit\":\"pi"
  ++ "\"},\"op\":\"Phase\",\"q\":3},{\"ctrl\":0,\"op\":\"CNOT\",\"target\":3},{\"angle\":{\"den\":8,\"num\":-1,\"unit\":\"pi\"}"
  ++ ",\"op\":\"Phase\",\"q\":3},{\"ctrl\":0,\"op\":\"CNOT\",\"target\":3},{\"angle\":{\"den\":4,\"num\":-1,\"unit\":\"pi\"},\""
  ++ "op\":\"Phase\",\"q\":0},{\"angle\":{\"den\":4,\"num\":-1,\"unit\":\"pi\"},\"op\":\"Phase\",\"q\":5},{\"ctrl\":0,\"op\":\"C"
  ++ "NOT\",\"target\":5},{\"angle\":{\"den\":4,\"num\":1,\"unit\":\"pi\"},\"op\":\"Phase\",\"q\":5},{\"ctrl\":0,\"op\":\"CNOT"
  ++ "\",\"target\":5},{\"angle\":{\"den\":8,\"num\":1,\"unit\":\"pi\"},\"op\":\"Phase\",\"q\":1},{\"angle\":{\"den\":8,\"num\""
  ++ ":1,\"unit\":\"pi\"},\"op\":\"Phase\",\"q\":2},{\"ctrl\":1,\"op\":\"CNOT\",\"target\":2},{\"angle\":{\"den\":8,\"num\":-1"
  ++ ",\"unit\":\"pi\"},\"op\":\"Phase\",\"q\":2},{\"ctrl\":1,\"op\":\"CNOT\",\"target\":2},{\"angle\":{\"den\":4,\"num\":1,\"u"
  ++ "nit\":\"pi\"},\"op\":\"Phase\",\"q\":1},{\"angle\":{\"den\":4,\"num\":1,\"unit\":\"pi\"},\"op\":\"Phase\",\"q\":3},{\"ctrl"
  ++ "\":1,\"op\":\"CNOT\",\"target\":3},{\"angle\":{\"den\":4,\"num\":-1,\"unit\":\"pi\"},\"op\":\"Phase\",\"q\":3},{\"ctrl\":"
  ++ "1,\"op\":\"CNOT\",\"target\":3},{\"angle\":{\"den\":2,\"num\":-1,\"unit\":\"pi\"},\"op\":\"Phase\",\"q\":1},{\"angle\":{"
  ++ "\"den\":2,\"num\":-1,\"unit\":\"pi\"},\"op\":\"Phase\",\"q\":5},{\"ctrl\":1,\"op\":\"CNOT\",\"target\":5},{\"angle\":{\"d"
  ++ "en\":2,\"num\":1,\"unit\":\"pi\"},\"op\":\"Phase\",\"q\":5},{\"ctrl\":1,\"op\":\"CNOT\",\"target\":5},{\"angle\":{\"den\""
  ++ ":4,\"num\":-1,\"unit\":\"pi\"},\"op\":\"Phase\",\"q\":4},{\"angle\":{\"den\":4,\"num\":-1,\"unit\":\"pi\"},\"op\":\"Phase"
  ++ "\",\"q\":2},{\"ctrl\":4,\"op\":\"CNOT\",\"target\":2},{\"angle\":{\"den\":4,\"num\":1,\"unit\":\"pi\"},\"op\":\"Phase\",\""
  ++ "q\":2},{\"ctrl\":4,\"op\":\"CNOT\",\"target\":2},{\"angle\":{\"den\":2,\"num\":-1,\"unit\":\"pi\"},\"op\":\"Phase\",\"q\""
  ++ ":4},{\"angle\":{\"den\":2,\"num\":-1,\"unit\":\"pi\"},\"op\":\"Phase\",\"q\":3},{\"ctrl\":4,\"op\":\"CNOT\",\"target\":3"
  ++ "},{\"angle\":{\"den\":2,\"num\":1,\"unit\":\"pi\"},\"op\":\"Phase\",\"q\":3},{\"ctrl\":4,\"op\":\"CNOT\",\"target\":3},{"
  ++ "\"angle\":{\"den\":1,\"num\":1,\"unit\":\"pi\"},\"op\":\"Phase\",\"q\":4},{\"angle\":{\"den\":1,\"num\":1,\"unit\":\"pi\"}"
  ++ ",\"op\":\"Phase\",\"q\":5},{\"ctrl\":4,\"op\":\"CNOT\",\"target\":5},{\"angle\":{\"den\":1,\"num\":-1,\"unit\":\"pi\"},\""
  ++ "op\":\"Phase\",\"q\":5},{\"ctrl\":4,\"op\":\"CNOT\",\"target\":5},{\"n\":1,\"op\":\"zeroDealloc\",\"r\":{\"active\":[2,"
  ++ "3],\"reserve\":[5]}},{\"n\":1,\"op\":\"zeroDealloc\",\"r\":{\"active\":[0,1],\"reserve\":[4]}},{\"op\":\"H\",\"q\":1"
  ++ "},{\"n\":1,\"op\":\"zeroExtend\",\"r\":{\"active\":[0],\"reserve\":[4]}},{\"n\":1,\"op\":\"zeroExtend\",\"r\":{\"acti"
  ++ "ve\":[1],\"reserve\":[5]}},{\"angle\":{\"den\":4,\"num\":1,\"unit\":\"pi\"},\"op\":\"Phase\",\"q\":0},{\"angle\":{\"de"
  ++ "n\":4,\"num\":1,\"unit\":\"pi\"},\"op\":\"Phase\",\"q\":1},{\"ctrl\":0,\"op\":\"CNOT\",\"target\":1},{\"angle\":{\"den\":"
  ++ "4,\"num\":-1,\"unit\":\"pi\"},\"op\":\"Phase\",\"q\":1},{\"ctrl\":0,\"op\":\"CNOT\",\"target\":1},{\"angle\":{\"den\":2,"
  ++ "\"num\":-1,\"unit\":\"pi\"},\"op\":\"Phase\",\"q\":0},{\"angle\":{\"den\":2,\"num\":-1,\"unit\":\"pi\"},\"op\":\"Phase\",\""
  ++ "q\":5},{\"ctrl\":0,\"op\":\"CNOT\",\"target\":5},{\"angle\":{\"den\":2,\"num\":1,\"unit\":\"pi\"},\"op\":\"Phase\",\"q\":"
  ++ "5},{\"ctrl\":0,\"op\":\"CNOT\",\"target\":5},{\"angle\":{\"den\":2,\"num\":-1,\"unit\":\"pi\"},\"op\":\"Phase\",\"q\":4}"
  ++ ",{\"angle\":{\"den\":2,\"num\":-1,\"unit\":\"pi\"},\"op\":\"Phase\",\"q\":1},{\"ctrl\":4,\"op\":\"CNOT\",\"target\":1},{"
  ++ "\"angle\":{\"den\":2,\"num\":1,\"unit\":\"pi\"},\"op\":\"Phase\",\"q\":1},{\"ctrl\":4,\"op\":\"CNOT\",\"target\":1},{\"an"
  ++ "gle\":{\"den\":1,\"num\":1,\"unit\":\"pi\"},\"op\":\"Phase\",\"q\":4},{\"angle\":{\"den\":1,\"num\":1,\"unit\":\"pi\"},\"o"
  ++ "p\":\"Phase\",\"q\":5},{\"ctrl\":4,\"op\":\"CNOT\",\"target\":5},{\"angle\":{\"den\":1,\"num\":-1,\"unit\":\"pi\"},\"op\""
  ++ ":\"Phase\",\"q\":5},{\"ctrl\":4,\"op\":\"CNOT\",\"target\":5},{\"n\":1,\"op\":\"zeroDealloc\",\"r\":{\"active\":[1],\"r"
  ++ "eserve\":[5]}},{\"n\":1,\"op\":\"zeroDealloc\",\"r\":{\"active\":[0],\"reserve\":[4]}},{\"op\":\"H\",\"q\":0},{\"m\":"
  ++ "1,\"op\":\"RadixReverse\",\"r\":[0,1]},{\"m\":2,\"op\":\"RadixReverse\",\"r\":[0,1,2,3]}],\"op\":\"seq\"},\"gate_co"
  ++ "unt\":92,\"max_qubit_index\":5,\"meta\":{\"k\":2,\"w\":4},\"negation\":\"oneQubit\",\"qubit_count\":6,\"resource"
  ++ "s\":{\"cleanAnc\":0,\"cnot\":37,\"h\":4,\"rz\":51,\"toffoli\":0,\"x\":0},\"schema\":\"forshor.lowgate/v2\"}"

-- emit_old_unchanged (qft --flat): the builder behind `forshor_emit qft 2 4 --flat` prints the
-- captured document byte for byte. `buildQFT` is an `unsafe` `IO` builder, so this is an `#eval`
-- that throws (failing the build) rather than a `#guard`.
#eval show IO Unit from do
  match ← buildQFT 2 4 false with
  | .ok j =>
      unless j.compress == qftFlatCaptured do
        throw (IO.userError "qft 2 4 --flat document differs from its pre-change capture")
  | .error e => throw (IO.userError s!"buildQFT 2 4 failed: {e}")

/-! ## `emit_new_nodes_roundtrip` -/

/-- The `"circuit"` body of a printed `forshor.mlowgate/v1` document, parsed back from
its compressed string. -/
def bodyOf (doc : Json) : Option (List Json) :=
  match Json.parse doc.compress with
  | .error _ => none
  | .ok j => do
      let c ← (j.getObjVal? "circuit").toOption
      let arr ← ((c.getObjVal? "body").bind Json.getArr?).toOption
      pure arr.toList

def opOf (j : Json) : String := ((j.getObjVal? "op").bind Json.getStr?).toOption.getD ""

def natField (j : Json) (k : String) : Option ℕ := ((j.getObjVal? k).bind Json.getNat?).toOption

/-- A literal node, written as JSON text. -/
def lit (s : String) : Json := (Json.parse s).toOption.getD Json.null

/-- A hand-built program: one round of the readout at toy widths (`H`, a unitary block,
`ffPhase`, `H`, `measureReset`), then a second `ffPhase` reading slot 0. -/
def tinyM : MLowGate :=
  .seq (.unitary (.seq (.H 0) (.CNOT 0 1)))
    (.seq (.ffPhase 0 0) (.seq (.unitary (.H 0)) (.seq (.measureReset 0)
      (.seq (.unitary .id) (.ffPhase 0 1)))))

def tinyMDoc : Json := emitMLowGateDoc tinyM (Json.mkObj [])

#guard bodyOf tinyMDoc == some [
  lit "{\"op\":\"H\",\"q\":0}",
  lit "{\"op\":\"CNOT\",\"ctrl\":0,\"target\":1}",
  lit "{\"op\":\"ffPhase\",\"q\":0,\"j\":0}",
  lit "{\"op\":\"H\",\"q\":0}",
  lit "{\"op\":\"measureReset\",\"q\":0}",
  lit "{\"op\":\"ffPhase\",\"q\":0,\"j\":1}"]

-- The envelope: the new schema, the record count, the angle rule.
#guard ((Json.parse tinyMDoc.compress).toOption.bind fun j =>
    ((j.getObjVal? "schema").bind Json.getStr?).toOption) == some mlowgateSchema
#guard ((Json.parse tinyMDoc.compress).toOption.bind fun j =>
    ((j.getObjVal? "num_measurements").bind Json.getNat?).toOption) == some 1
#guard ((Json.parse tinyMDoc.compress).toOption.bind fun j =>
    ((j.getObjVal? "ff_angle_rule").bind Json.getStr?).toOption) == some ffAngleRuleText

/-! ### The lowered semiclassical circuit at `a = 2`, `N = 3` -/

def tinyInst : ShorOrderFindingInstance := ⟨2, 3, by decide, by decide⟩

def tinyPolicy : ShorLoweringPolicy := standardPolicy 2 (by decide)

/-- The control qubit and the lowest data qubit at the reference layout. -/
def cQ : ℕ := Readout.EmitRef.referenceControl tinyPolicy tinyInst 0
def y0 : ℕ := (Reference.allocateReferenceLayout tinyPolicy tinyInst 0).data.active.qubits.headD 0

def roundsBody (m : ℕ) : List Json :=
  (bodyOf (emitMLowGateDoc (Readout.EmitRef.referenceSemiclassicalLow tinyPolicy tinyInst 0 m)
    (Json.mkObj []))).getD []

def body1 : List Json := roundsBody 1
def body2 : List Json := roundsBody 2

def qNode (op : String) (q : ℕ) : Json := Json.mkObj [("op", Json.str op), ("q", (q : Json))]
def ffNode (q j : ℕ) : Json :=
  Json.mkObj [("op", Json.str "ffPhase"), ("q", (q : Json)), ("j", (j : Json))]

-- One round (`lowerM_one_round`): `X y0` (initY1), `H c`, the lowered multiplier, then
-- exactly `ffPhase c 0`, `H c`, `measureReset c`, and no other new node.
#guard body1.take 2 == [qNode "X" y0, qNode "H" cQ]
#guard body1.drop (body1.length - 3) == [ffNode cQ 0, qNode "H" cQ, qNode "measureReset" cQ]
#guard (body1.filter (opOf · == "measureReset")).length == 1
#guard (body1.filter (opOf · == "ffPhase")).length == 1
-- The multiplier is really there (more than the six fixed nodes).
#guard body1.length > 6

-- Two rounds: the new nodes are `ffPhase c 0, measureReset c, ffPhase c 1, measureReset c`
-- in this order (round `j` reads slots `0..j-1`).
#guard (body2.filter fun n => opOf n == "measureReset" || opOf n == "ffPhase") ==
  [ffNode cQ 0, qNode "measureReset" cQ, ffNode cQ 1, qNode "measureReset" cQ]

/-! ## The schema string -/

theorem mlowgate_schema_ne_lowgate : mlowgateSchema ≠ "forshor.lowgate/v2" := by decide

end Shor.Emit.MTests
