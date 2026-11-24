import ForShor.ShorVerification.Framework.AbstractMachine.LowGate

/-!
# Framework/AbstractMachine: the lowered measurement language `MLowGate`

`MLowGate` is to `LowGate` what `MGate` is to `Gate`: the low-level gate
language extended by the two non-unitary, classically controlled steps of the
semiclassical readout.

* `unitary g`: the low-level circuit `g : LowGate`, applied whatever the record.
* `seq a b`: `a` then `b`.
* `measureReset q`: measure qubit `q` in the Z basis, append the outcome to the
  record, reset `q` to `|0⟩`.
* `ffPhase q j`: `LowGate.Phase q (ffAngle j rec)`, `rec` the record so far.

The extension is additive: `LowGate`, its semantics and its qubit walk are
unchanged. The lowering `MGate → MLowGate` (`Policy.lowerGate` on the unitary
parts, the identity on `measureReset` and `ffPhase`), the branching-record
semantics `MLowGate.eval` and the qubit walk `MLowGate.peakQubitsFor` live in
`Implementation/Readout/Lowering.lean`.
-/

namespace Shor

/-- Lowered measurement language: low-level circuits, sequencing, mid-circuit
measurement with reset, and record-controlled phases (see the module
docstring; the two new constructors mean what they mean in `MGate`). -/
inductive MLowGate : Type
  | unitary (g : LowGate) : MLowGate
  | seq (a b : MLowGate) : MLowGate
  | measureReset (q : ℕ) : MLowGate
  | ffPhase (q j : ℕ) : MLowGate
deriving Inhabited

end Shor
