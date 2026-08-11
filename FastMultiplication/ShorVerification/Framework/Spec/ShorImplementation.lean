import FastMultiplication.ShorVerification.ShorCorrectness
import FastMultiplication.ShorVerification.GateCount.Shor_GateCount

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

* **Preconditions are as weak as order-finding itself.**  The only hypotheses are
  an order-finding instance (`a`, `N`, coprime, the exponent/data registers at
  their standard widths) and a clean, disjoint input on those two registers
  (`IdealOrderFindingInput`).  Nothing about ancilla layout, workspace sizing, or
  cleanliness of an implementation's *scratch* — any correct implementation
  allocates and manages its own scratch internally.

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
precision level `m`.  The obligation: for every instance, every clean input, and
every continued-fraction search budget, the circuit family reaches *arbitrary
closeness* to the ideal success probability — for any `ε > 0` some precision
level `m` succeeds with probability `≥ κ / log⁴ N − ε`.  Stated purely over
`evalL` (the LowGate semantics); it names no ancillas, no workspace, and no
construction. -/
def ShorImplementsOrderFinding
    (prog : ShorOrderFindingInstance → ℕ → LowGate) : Prop :=
  ∀ (T : ℕ → ℕ), ContinuedFractionSearchComplete T →
  ∀ (inst : ShorOrderFindingInstance) (b0 : qs.Basis),
    IdealOrderFindingInput qs inst.x inst.y b0 →
    ∀ ε : ℝ, 0 < ε → ∃ m : ℕ,
      probability_of_success (qs := qs) (T := T)
          (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
          (x := inst.x.active) (r := ord inst.a inst.N inst.coprime)
          (Q := ASize inst.x.active) (evalC := LowerGateClass.evalL (qs := qs))
          (C := prog inst m) (ψ := qs.ket b0)
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
