import FastMultiplication.ShorVerification.Framework.Spec.OrderFinding
import FastMultiplication.ShorVerification.Framework.Gatecount.CostModel

namespace Shor
open Gate
open Classical

/-!
# Framework/Spec: the Shor implementation interface

This file is the load-bearing boundary of the framework/implementation split.
It says what it *means* to be a correct Shor implementation as a bundle of
obligations phrased entirely over a bare `LowGate` circuit — **nothing about how
that circuit is built**.  A user supplies a LowGate program together with proofs
of the obligations; the framework hands back order-finding correctness and the
gate-count bound.

Design principles (agreed with the lead):

* **The interface commits only to behaviour, never to a construction.**  The
  obligations mention a plain `prog : ShorOrderFindingInstance → ℕ → LowGate` and
  its measured success probability / gate count.  No `ShorLoweringSetup`, no
  `PhaseProductProgramOK`, no Toom–Cook / table synthesis, no specific Gate-level
  circuit.  A Shor implementation that multiplies a completely different way must
  still be able to satisfy this interface, so none of our particular circuit's
  machinery may appear here — it all lives on the implementation side
  (`Implementations/Reference`, Phase 4).

* **Fixed, globally-clean initial state; no implementation-specific
  preconditions.**  Correctness is judged from `qs.ket RegEncoding.zero` — the
  canonical all-|0⟩ ground state (`RegEncoding.zero`), the qubit analogue of an
  empty EVM memory.  Because the whole register file starts clean, every ancilla
  an implementation uses (active, reserve, private workspace) is zero for free,
  so per-implementation preconditions about workspace cleanliness or size are
  both *unnecessary* (clean-zero covers them) and *unstateable* (the obligation
  is unconditional — there is no hypothesis slot to add them).  The only surviving
  hypotheses are the *domain* facts carried by `ShorOrderFindingInstance` itself
  (`a`, `N`, coprime, the standard exponent/data register widths) — the analogue
  of a challenge's `ValidInput`.

* **Arbitrary closeness, no precision knob.**  Correctness is the
  implementation-neutral `∀ ε > 0, …`: for any target closeness there is a
  precision level `m` whose circuit `prog inst m` succeeds with probability
  `≥ κ / log⁴ N − ε`.  We do **not** expose `η` / `ShorApproxSetup`; those are
  our approximate-QPE implementation's private way of reaching closeness, and a
  different implementation may reach it differently (or exactly).  Because a
  finer `ε` needs more precision bits — hence a larger circuit — `prog` is a
  family indexed by the precision level `m`, not a single fixed circuit.

* **`ContinuedFractionPost` and `MeasureClass` are framework-side assumptions**
  (they live in `Framework/Math` and `Framework/Semantics`), not fields a user
  re-proves.
-/

variable {qs : QSemantics}
variable [instReg : RegEncoding qs.Basis]
variable [instCFP : ContinuedFractionPost]
variable [instMeas : MeasureClass qs]
variable [instLGC : LowerGateClass qs]

/-- The abstract, construction-free correctness obligation on a LowGate Shor
implementation.

`prog inst m` is the user's LowGate circuit for order-finding instance `inst` at
precision level `m`.  The obligation is stated **unconditionally over a fixed,
globally-clean initial state** `qs.ket RegEncoding.zero` — the qubit analogue of
running a candidate from empty memory.  Because the whole register file starts at
|0⟩, every ancilla an implementation uses (active, reserve, or a private
workspace) is clean *for free*, so there are no implementation-specific
preconditions: none are needed, and the fixed obligation gives nowhere to state
them.  The only remaining hypotheses are the *domain* facts carried by
`ShorOrderFindingInstance` itself (coprimality and the standard register widths).

For any `ε > 0` some precision level `m` succeeds with probability
`≥ κ / log⁴ N − ε` (arbitrary closeness; `m` is the resource knob — a finer `ε`
is met by a larger circuit `prog inst m`, exactly as more work is met by more of
the always-clean qubits).  Stated purely over `evalL` (the LowGate semantics);
it names no ancillas, no workspace, and no construction. -/
def ShorImplementsOrderFinding
    (prog : ShorOrderFindingInstance → ℕ → LowGate) : Prop :=
  ∀ (T : ℕ → ℕ), ContinuedFractionSearchComplete T →
  ∀ (inst : ShorOrderFindingInstance),
    ∀ ε : ℝ, 0 < ε → ∃ m : ℕ,
      probability_of_success (qs := qs) (T := T)
          (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
          (x := inst.x.active) (r := ord inst.a inst.N inst.coprime)
          (Q := ASize inst.x.active) (evalC := LowerGateClass.evalL (qs := qs))
          (C := prog inst m) (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis)))
        ≥ κ / (Nat.log2 inst.N : ℝ) ^ 4 - ε

/-- A Shor implementation over the LowGate boundary.

The interface a user instantiates: a LowGate circuit family `prog`, a proof of
the construction-free correctness obligation, a declared concrete gate-count
function `gateBound`, and a proof the circuits meet it under the shared
`shorGateCostModel`.  Everything is phrased over `LowGate`; nothing mentions the
`Gate` front end, the compilation, or any synthesis — which is exactly what makes
the framework independent of any particular implementation. -/
structure ShorImplementation : Type where
  /-- The user's LowGate circuit family, indexed by the order-finding instance
  and a precision level. -/
  prog : ShorOrderFindingInstance → ℕ → LowGate
  /-- Construction-free order-finding correctness (arbitrary closeness). -/
  correct : ShorImplementsOrderFinding (qs := qs) prog
  /-- The implementation's declared concrete gate-count function. -/
  gateBound : ShorOrderFindingInstance → ℕ → ℕ
  /-- Every circuit in the family meets the declared bound under the shared
  cost model.  (A future step tightens `≤` to an exact `=`.) -/
  counted : ∀ (inst : ShorOrderFindingInstance) (m : ℕ),
    LowGate.gateCount shorGateCostModel (prog inst m) ≤ gateBound inst m

namespace ShorImplementation

/-- **Framework correctness theorem.**  Any implementation satisfying the
interface is a correct order finder: to arbitrary closeness, its circuit family
succeeds with probability `≥ κ / log⁴ N`. -/
theorem framework_order_finding_correct (impl : ShorImplementation (qs := qs)) :
    ShorImplementsOrderFinding (qs := qs) impl.prog :=
  impl.correct

/-- **Framework gate-count theorem.**  Any implementation satisfying the
interface meets its own declared concrete gate-count bound. -/
theorem framework_gate_count (impl : ShorImplementation (qs := qs)) :
    ∀ (inst : ShorOrderFindingInstance) (m : ℕ),
      LowGate.gateCount shorGateCostModel (impl.prog inst m) ≤ impl.gateBound inst m :=
  impl.counted

end ShorImplementation

end Shor
