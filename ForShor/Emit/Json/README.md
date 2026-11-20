# `Json/`

JSON printers. Every other folder in `Emit/` builds a value and hands it to
one printer here to turn it into `Lean.Json` — no file outside `Json/`
declares its own spelling for a shared type.

Import order within the folder: `Common.lean → LowGateJson.lean → PlanJson.lean`;
`MLowGateJson.lean` imports `LowGateJson.lean` and is imported by nothing that prints
an older schema.

## `Common.lean`

One printer each for the small value types shared everywhere else in
`Emit/`: rationals, angles, registers, points, and `Prog` ops.

| def | prints |
|---|---|
| `ratJson (r : ℚ)` | `{"num", "den"}` |
| `angleJson (a : Angle)` | `{"num", "den", "unit": "pi"}` (an `Angle` is a rational multiple of `π`) |
| `regJson (r : Reg)` | the ordered list of physical qubit indices, LSB-first |
| `extRegJson (r : ExtReg)` | `{"active": regJson, "reserve": regJson}` |
| `pointJson : Operations.Point → Json` | `{"kind": "int", "z"}` or `{"kind": "frac", "m"}` — a Toom-Cook interpolation point; `frac 0` is the point at infinity |
| `validOpJson {k} : Operations.valid_ops k → Json` | one of the five `Prog k` op spellings (`shiftL`, `shiftR`, `negate`, `addScaled`, `phaseProduct`); `Fin k` indices print as plain `ℕ` |
| `progJson {k} (ops : Prog k)` | the op list, in order |
| `gateResourcesJson (r : GateResources)` | `{"h", "x", "cnot", "toffoli", "rz", "cleanAnc"}` |
| `negationMethodJson (m : NegationMethod)` | `"oneQubit"` or `"scratch"`, the spelling of the `"negation"` field |
| `negateChargeJson (m : NegationMethod)` | `{"method", "formulas", "at_width"}`: the charge of one `Negate` under `m` (`negateResourcesFor`), as closed forms (`formulas`: `clean_ancilla`, `x`, `cnot`, `toffoli`, `note`) and evaluated at widths 8, 9 and 2048 (`at_width`, each a `gateResourcesJson`). `oneQubit`: 1 clean qubit, Toffoli 12w−28 / 10w−18 (w even / odd); `scratch`: w+1 clean qubits, Toffoli 2w−3 |

## `LowGateJson.lean`

The flat `LowGate` printer and the three document envelopes built on top of
it.

- `LowGate.flattenSeq : LowGate → List LowGate` — flattens nested `seq`
  nodes into an ordered leaf list, dropping `id`s. A structural recursion
  on the gate tree (not `partial`), so it has ordinary equation lemmas.
- `lowGateJson : LowGate → Json` — the tree printer. Op names are exactly
  the `LowGate` constructor names. A `.seq` node prints its *entire*
  subtree flattened into one `{"op": "seq", "body": [...]}` array (via
  `flattenSeq`) — nested seqs don't produce nested `"seq"` objects unless
  there's a `.adj` in between. This convention matters: `PlanJson.lean`'s
  `check1_annotatedEqFlat` has to reproduce it exactly to compare an
  annotated tree against a flat one.
- `emitProgram (P : ShorOrderFindingProgram) (metaJson) (m : NegationMethod := .oneQubit) : Json` — the
  `forshor.lowgate/v2` document for a full submitted program (`shor`'s
  document): `schema, bit_order, angle_unit, output_register, gate_count,
  negation, qubit_count, max_qubit_index, resources, circuit, meta`. `gate_count`, `qubit_count`
  and `resources` are priced under `shorGateResourceModelFor m` and `negation`
  names `m` (always printed; the default is `"oneQubit"`, whose figures are those of
  `shorGateResourceModel`). The circuit does not depend on `m`; `gate_count` (the total of `resources` other than `cleanAnc`) and the
  resources do.
- `emitLowGateDoc (g : LowGate) (metaJson) (m : NegationMethod := .oneQubit) : Json` — the same envelope and
  schema, minus `output_register`, for a bare `LowGate` term that has no
  single distinguished output register (`pp`/`cpp`/`qft --flat`'s
  documents).
- `emitPlanDoc (planJ : Json) (metaJson) : Json` — the `forshor.plan/v1`
  envelope for an *annotated* document: `schema, bit_order, angle_unit,
  plan, meta` (`pp`/`cpp`/`qft`'s default, non-`--flat` documents).

## `PlanJson.lean`

The annotated printer: walks the *plan* term (`PhaseLoweringPlan`,
`QFTLoweringPlan`) rather than the flat `LowGate` those plans lower to, so
the recursive structure — where a phase product or QFT split began, and
what its layout/coefficients were — stays visible in the JSON. The flat
`LowGate` term carries no record of where a split began, which is why this
is a separate representation.

- `planJson : PhaseLoweringPlan k hk pts hpts ops initSize U → Json` —
  constructor-for-constructor with `lowerGateRec`, *except*:
  - `signedStep phi x z T layout child` prints `{"op":
    "SignedPhaseProd", "phi", "x", "z", "input_size", "next_width",
    "limb_width", "coeffs", "body": <planJson child>}` (`coeffs` is the
    full `q k`-length list of E2 interpolation weights,
    `loweringPhaseCoeff`, as `ratJson`s).
  - `signedBase phi x z` prints `{"op": "NaiveSignedPhaseProd", "phi",
    "x", "z", "expansion": <lowGateJson of the naive primitive>}` — the
    `expansion` field means a consumer never has to re-derive the flat
    `CPhase` view of a base case to compare gate counts against it.
  - `cSignedStep`/`cSignedBase` are the same, controlled
    (`CSignedPhaseProd`/`NaiveCSignedPhaseProd`, plus a `ctrl` field).
  - Every primitive-gate constructor (`H`, `X`, `ShiftL`, `AddScaled`,
    `zeroExtend`, `RadixReverse`, …) prints identically to `lowGateJson`.
    Unlike `lowGateJson`, a `.seq` node here is *not* flattened — it always
    prints as a plain two-element `{"op": "seq", "body": [left, right]}` —
    which is exactly what `deepFlattenPlanJsonList` below has to undo to
    compare against `lowGateJson`'s output.
- `qftPlanJsonOf : QFTLoweringPlan k hk ops r → Json` — same idea for the
  QFT: `.split` prints the twiddle angle (`qftPhi (regSize r)`), the
  left/right sub-registers, and recurses into both children; the
  phase-product body between them prints through `planJson` directly,
  since it's itself a `StandardPhaseLoweringPlan` (no special case needed).

`pp`/`cpp`'s `annotated_eq_flat` check (`Lower/PhaseProduct.lean`) —
whether the annotated view above and the independently-computed flat
`LowGate` term describe the same circuit — also lives here: it has
nothing to do with the extracted IR (`Reflect/`, `IR/`), only with this
file's own two views of the same real term, so it belongs next to
`planJson`/`lowGateJson`, not in `Lower/` or `Reflect/`.

- `deepFlattenPlanJsonList (j : Json) : List Json` — splices `seq` nodes
  fully (matching `LowGate.flattenSeq`) and substitutes
  `SignedPhaseProd`/`CSignedPhaseProd` annotations with their
  `expansion`/`body` (recursing into `expansion` too — it's itself
  `lowGateJson`'s output for a `LowGate.seq`, not an opaque leaf).
- `wrapFlattened (items : List Json) : Json` — presents a flattened list
  the same way `lowGateJson` would (`id` for `[]`, the item itself for a
  singleton, one `seq` node otherwise).
- `check1_annotatedEqFlat (planJ : Json) (flat : LowGate) : Bool` —
  `wrapFlattened (deepFlattenPlanJsonList planJ) == lowGateJson flat`.

## `MLowGateJson.lean`

The `forshor.mlowgate/v1` printer for the lowered measurement language `MLowGate`
(`Framework/AbstractMachine/MLowGate.lean`: `unitary` `LowGate` blocks, `seq`,
`measureReset`, `ffPhase`). A leaf: it changes no existing printer, and only
`forshor_emit readout` (`Lower/Readout.lean`) prints it, so every `forshor.lowgate/v2`
and `forshor.plan/v1` document is byte-identical to before.

- `mlowGateNodes : MLowGate → List Json` — the nodes in execution order: a `unitary g`
  contributes `(LowGate.flattenSeq g).map lowGateJson` (the old vocabulary, unchanged,
  `id` contributing nothing), `seq a b` the nodes of `a` then of `b`, and the two new
  nodes
  - `{"op":"measureReset","q":q}`: measure qubit `q` in Z, append the outcome to the
    record, reset `q` to `|0⟩`;
  - `{"op":"ffPhase","q":q,"j":j}`: `Phase(q, θ)`, `θ = ffAngle j rec` in units of `π`,
    where `rec` is the record when the node runs.
- `mlowGateJson g` — the circuit as one flat `{"op":"seq","body":[…]}`.
- `emitMLowGateDoc (g) (metaJson)` — the envelope: `schema` (`mlowgateSchema` =
  `"forshor.mlowgate/v1"`), `bit_order`, `angle_unit` (`"pi"`), `record`, `ff_angle_rule`,
  `num_measurements` (the number of `measureReset` nodes = final record length),
  `circuit`, `meta`. No `gate_count`/`qubit_count`/`resources`: pricing the new nodes is
  the consumer's.

**Record and angle.** `rec[i]` is the outcome (0/1) of the `i`-th `measureReset` executed
(absolute slot, 0-based, oldest first). `ffAngle j rec = -(Σ_{i<j} rec[i] / 2^(j-i))`
(units of `π`; a missing slot counts as 0), so every angle is an exact dyadic rational:
slot `j-1` weighs `1/2`, slot `j-1-k` weighs `1/2^(k+1)`. The node carries `j` only, not an
angle (the angle depends on outcomes unknown when the document is printed) and not a
symbolic rule (the rule is the same for every node, so it is stated once, in the
`record`/`ff_angle_rule` fields). A consumer prices an `ffPhase` as one single-qubit
rotation whose angle is a dyadic of denominator up to `2^j`; it must not treat it as a
fixed-angle `Phase`.

**Old consumers.** The schema string differs from `forshor.lowgate/v2`
(`MTests.mlowgate_schema_ne_lowgate`), so a consumer that checks the schema refuses the
document. A consumer that ignores the schema and walks the circuit meets op names it
does not know (`measureReset`, `ffPhase`) and must refuse them. A consumer that silently
flattens or counts unknown nodes would misprice the document, so check that it raises on them before
feeding it an `mlowgate/v1` file.
