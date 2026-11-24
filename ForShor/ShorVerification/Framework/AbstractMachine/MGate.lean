import ForShor.ShorVerification.Framework.AbstractMachine.Gates

/-!
# Framework/AbstractMachine: the measurement language `MGate`

`MGate` extends the unitary `Gate` language with two non-unitary,
classically controlled steps: a mid-circuit Z-measurement with reset, and a
phase whose angle is a fixed function of the measurement record so far. It is
the language of the semiclassical (one recycled control qubit) readout.

The extension is additive: `Gate` and its semantics are unchanged, and a
`Gate` enters `MGate` only through `MGate.unitary`. The semantics live in
`Framework/Semantics/MSemantics.lean`.

## Record convention

A `Record` is the list of measurement outcomes so far, oldest first: slot `i`
(`rec.getD i false`) is the outcome of the `i`-th `measureReset` executed, with
`true` meaning outcome `1`. Each `measureReset` appends one entry at the end.
-/

namespace Shor

/-- The classical measurement record: the outcomes of the `measureReset` steps
executed so far, in execution order (slot `i` = outcome of the `i`-th one;
`true` = outcome `1`). -/
abbrev Record := List Bool

/-- The angle (units of `π`, an `Angle = ℚ`) of the feed-forward phase in round
`j` given the record `rec`:

  `ffAngle j rec = -(∑ i < j, bit(rec i) / 2^(j-i))`,

where `bit(rec i)` is `1` if slot `i` holds outcome `1` and `0` otherwise (a
missing slot counts as `0`). Slot `j-1`, the most recent outcome when round
`j` starts after `j` measurements, weighs `1/2`; slot `j-1-k` weighs
`1/2^(k+1)`. It is a finite sum of dyadic rationals, so every emitted angle is
an exact rational multiple of `π`. This form, sign included, is the one
fixed by the state-level equivalence of the semiclassical readout with the
inverse-QFT readout (`semiclassical_branch_state` and
`coherent_projected_state` in `Implementation/Readout/Main.lean`).

The slots are ABSOLUTE record positions: round `j` reads slots `0, …, j-1`
whatever else the program measured. These are "the `j` most recent outcomes"
only when every `measureReset` executed before round `j` is a readout round
(a later task may add an offset parameter if that is not the case). -/
def ffAngle (j : ℕ) (rec : Record) : Angle :=
  -(∑ i ∈ Finset.range j, (if rec.getD i false then (1 : ℚ) else 0) / 2 ^ (j - i))

/-- Measurement-based gate language: unitary gates, mid-circuit measurement with
reset, and record-controlled phases.

* `unitary g`: the unitary `g : Gate`, applied whatever the record.
* `seq a b`: `a` then `b`.
* `measureReset q`: measure qubit `q` in the Z basis, append the outcome to the
  record (as `true` for `1`), and reset `q` to `|0⟩` (by an `X q` when the
  outcome was `1`).
* `ffPhase q j`: the single-qubit phase `Phase q (ffAngle j rec)`, i.e.
  `|1⟩ ↦ exp(iπ · ffAngle j rec) |1⟩` on qubit `q`, where `rec` is the record
  at the moment the step runs. It reads the absolute slots `0, …, j-1` of
  `rec` (see `ffAngle`). -/
inductive MGate : Type
  | unitary (g : Gate) : MGate
  | seq (a b : MGate) : MGate
  | measureReset (q : ℕ) : MGate
  | ffPhase (q j : ℕ) : MGate
deriving Inhabited

/-- The number of `measureReset` steps a program executes, i.e. the length of
the record it appends (`seq` adds, `measureReset` counts one, the other
constructors none). -/
def MGate.numMeas : MGate → ℕ
  | .unitary _ => 0
  | .seq a b => a.numMeas + b.numMeas
  | .measureReset _ => 1
  | .ffPhase _ _ => 0

end Shor
