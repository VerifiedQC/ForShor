/-!
# How a negation is realised

A policy chooses one of two realisations of the gate `LowGate.Negate r` (`r ← −r mod 2^w`). The gate and its
meaning (`negateBasis`) are the same for both; only the resource charge differs, so a policy that picks a method
is priced, and its qubit count is stated, accordingly.

This file has no imports so that `Policy.lean` (which imports only `ToomCookTable.lean`) and the cost model can
both see it.
-/

namespace Shor

/-- How `LowGate.Negate` is built (and charged). Both complement the register and then add one.

* `oneQubit`: the increment is Gidney's single-ancilla increment gate ("Constructing Large Increment Gates",
  2015). It uses the register's own bits and one extra qubit, which may be in any state, charged as one clean
  qubit. Toffoli `12 w - 28` (`w` even) / `10 w - 18` (`w` odd), CNOT `17 w - 22` / `17 w - 5`.
* `scratch`: the increment is a Cuccaro modulo adder against a clean constant-one register as wide as the
  register negated, plus the adder's carry: `w + 1` clean qubits, Toffoli `2 w - 3`.

The default is `oneQubit`. -/
inductive NegationMethod where
  | oneQubit
  | scratch
  deriving DecidableEq, Repr

instance : Inhabited NegationMethod := ⟨.oneQubit⟩

end Shor
