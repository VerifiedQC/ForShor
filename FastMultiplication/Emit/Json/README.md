# `Json/`

JSON printers. Every other folder in `Emit/` builds a value and hands it to
one printer here to turn it into `Lean.Json` — no file outside `Json/`
declares its own spelling for a shared type (design principle 6 in the top
`README.md`).

Import order within the folder: `Common.lean → LowGateJson.lean → PlanJson.lean`.

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

## `LowGateJson.lean`

The flat `LowGate` printer and the three document envelopes built on top of
it.

- `LowGate.flattenSeq : LowGate → List LowGate` — flattens nested `seq`
  nodes into an ordered leaf list, dropping `id`s. `partial`: a plain
  structural traversal with no proof obligations.
- `lowGateJson : LowGate → Json` — the tree printer. Op names are exactly
  the `LowGate` constructor names. A `.seq` node prints its *entire*
  subtree flattened into one `{"op": "seq", "body": [...]}` array (via
  `flattenSeq`) — nested seqs don't produce nested `"seq"` objects unless
  there's a `.adj` in between. This convention matters: `PlanJson.lean`'s
  `check1_annotatedEqFlat` has to reproduce it exactly to compare an
  annotated tree against a flat one.
- `emitProgram (P : ShorOrderFindingProgram) (metaJson) : Json` — the
  `forshor.lowgate/v2` document for a full submitted program (`shor`'s
  document): `schema, bit_order, angle_unit, output_register, gate_count,
  qubit_count, max_qubit_index, resources, circuit, meta`.
- `emitLowGateDoc (g : LowGate) (metaJson) : Json` — the same envelope and
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
what its layout/coefficients were — stays visible in the JSON. See the top
`README.md`'s "Key concepts" table for why this is a separate representation
from `LowGate`.

- `planJson : PhaseLoweringPlan k hk pts hpts ops initSize U → Json` —
  constructor-for-constructor with `lowerGateRec`, *except*:
  - `signedStep phi x z layout _ _ child` prints `{"op":
    "SignedPhaseProd", "phi", "x", "z", "input_size", "next_width",
    "limb_width", "coeffs", "body": <planJson child>}` (`coeffs` is the
    full `q k`-length list of E2 interpolation weights,
    `loweringPhaseCoeff`, as `ratJson`s).
  - `signedBase phi x z _` prints `{"op": "NaiveSignedPhaseProd", "phi",
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
`LowGate` term describe the same circuit — also lives here, moved in from
the now-deleted `Lower/Instantiate.lean` (`Emit/PLAN.md` R4): it has
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
