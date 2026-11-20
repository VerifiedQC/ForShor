import ForShor.Emit.Balanced.Verify
import ForShor.Emit.Json.MLowGateJson
import ForShor.ShorVerification.Submission.CorrectSemiclassical

/-!
# Compact semiclassical policy readout

Keep the existing unitary IR and default balanced templates for the arithmetic.
Its entry point is one controlled
multiplication, not the coherent `shor` template. The versioned schedule
instantiates that same template for each round, on the same control qubit.
Only the agreement probes expand the schedule, at small reference instances.
-/

namespace Shor.Reflect.Readout

open IR

/-- The arithmetic dictionary used by the measured loop. The internal QFT
template remains available to the multiplier; the coherent entry points do not. -/
def arithmeticDoc (doc : Doc) (round : Template) : Doc :=
  let d := IR.Balanced.balanceDoc
    { doc with templates := doc.templates.filter (fun t => t.name != "shor" && t.name != "shor_gate") }
  { d with entry := round.name
           templates := d.templates ++ [{ round with body := IR.Balanced.retarget round.body }] }

private inductive Step where
  | h | multiply | ffPhase | measureReset

private def steps : List Step := [.h, .multiply, .ffPhase, .h, .measureReset]

private def Step.name : Step → String
  | .h => "H"
  | .multiply => "multiply"
  | .ffPhase => "ffPhase"
  | .measureReset => "measureReset"

private def Step.gate (c j : ℕ) (mul : LowGate) : Step → MLowGate
  | .h => .unitary (.H c)
  | .multiply => .unitary mul
  | .ffPhase => .ffPhase c j
  | .measureReset => .measureReset c

private def roundCircuit (c j : ℕ) (mul : LowGate) : List Step → MLowGate
  | [] => .unitary .id
  | [s] => s.gate c j mul
  | s :: ss => .seq (s.gate c j mul) (roundCircuit c j mul ss)

/-- Versioned schedule consumed alongside the arithmetic dictionary. `j` runs
from `0` to `rounds - 1`; `multiply` calls that dictionary's entry with `j`,
`rounds`, the control qubit, and the reference arithmetic registers. -/
def scheduleJson : Lean.Json :=
  Lean.Json.mkObj [
    ("schema", Lean.Json.str "forshor.readout-loop/v1"),
    ("mode", Lean.Json.str "semiclassical"),
    ("initialization", Lean.Json.str "initY1"),
    ("control", Lean.Json.str "referenceControl"),
    ("rounds", Lean.Json.str "referenceXWidth"),
    ("steps", Lean.Json.arr (steps.map (Lean.Json.str ∘ Step.name)).toArray),
    ("bit_order", Lean.Json.str "lsb_first"),
    ("angle_unit", Lean.Json.str "pi"),
    ("record", Lean.Json.str recordConventionText),
    ("ff_angle_rule", Lean.Json.str ffAngleRuleText)]

private def instantiateAt (s : ShorPolicySubmission) (doc : Doc)
    (inst : ShorOrderFindingInstance) (m : ℕ) : Except String MLowGate := do
  let layout := Reference.allocateReferenceLayout s.policy inst m
  let rounds := Reference.referenceXWidth inst
  let c := Shor.Readout.referenceControl s.policy inst m
  let env := (policyShorEnv s inst layout).bindW "rounds" rounds
  let env := { env with r := fun name =>
    if name == "ctrl" then some (ExtReg.ofReg (Reg.interval c 1)) else env.r name }
  let init := layout.data.active.qubits.head?.elim LowGate.id LowGate.X
  let run ← (List.range rounds).foldlM (init := MLowGate.unitary .id) fun acc j => do
    let mul ← instantiate doc doc.entry (env.bindW "j" j) policyFuel
    pure (.seq acc (roundCircuit c j mul steps))
  pure (.seq (.unitary init) run)

-- Keep measurement positions and record slots exact; compare unitary blocks
-- with the existing associativity-/identity-insensitive agreement check.
private def agrees : MLowGate → MLowGate → Bool
  | .unitary a, .unitary b => lowGateAgrees a b
  | .seq a b, .seq c d => agrees a c && agrees b d
  | .measureReset a, .measureReset b => a == b
  | .ffPhase a j, .ffPhase b k => a == b && j == k
  | _, _ => false

example (c j : ℕ) (mul : LowGate) : roundCircuit c j mul steps =
    .seq (.unitary (.H c)) (.seq (.unitary mul)
      (.seq (.ffPhase c j) (.seq (.unitary (.H c)) (.measureReset c)))) := rfl

#guard !agrees (roundCircuit 7 2 (.CNOT 7 8) steps) (roundCircuit 7 1 (.CNOT 7 8) steps)
#guard !agrees (roundCircuit 7 2 (.CNOT 7 8) steps)
  (roundCircuit 7 2 (.CNOT 7 8) [.h, .multiply, .ffPhase, .h])

/-- The measured document must instantiate to the same checked balanced circuit
at the existing small submission probes. As with the coherent IR, this is
sampled extraction agreement, not a theorem about all serialized documents. -/
def check (s : ShorPolicySubmission) (doc : Doc) : Except String Unit := do
  if doc.entry != "readout_round" || !doc.wellFormed then
    throw "semiclassical arithmetic IR is not well formed"
  for (inst, m) in submissionShorInstances do
    let g ← instantiateAt s doc inst m
    let certified := Shor.Readout.balancedSemiclassicalProgramAt s.policy Shor.Balanced.defaultRule m inst
    if !agrees g certified.circuit then
      throw s!"semiclassical IR disagrees with the balanced circuit at N={inst.N}, m={m}"

end Shor.Reflect.Readout
