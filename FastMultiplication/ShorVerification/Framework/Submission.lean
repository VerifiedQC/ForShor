import FastMultiplication.ShorVerification.Framework.Math.ShorDefinition
import FastMultiplication.ShorVerification.Framework.Semantics.GateSemantics
import FastMultiplication.ShorVerification.Framework.Quantum.Measurement
import FastMultiplication.ShorVerification.Framework.Semantics.LowerGate
import FastMultiplication.ShorVerification.Framework.Gatecount.CostModel

namespace Shor
open Gate
open Classical

/-!
# Submission Interface

This module is the public framework boundary for Shor order-finding submissions.
It contains the measurement-facing success criterion, the public input instance,
and the construction-free `LowGate` implementation contract.

The interface deliberately mentions only framework concepts. A submission
provides a `LowGate` circuit family together with correctness and gate-count
proofs; allocation, lowering, synthesis, and workspace details remain on the
implementation side.
-/

variable {qs : QSemantics}
variable [RegEncoding qs.Basis]

/-- Evaluate a circuit-like object with `evalC`, then measure register `r`
with outcome `o`. -/
noncomputable def measProbAfter
    [MeasureClass qs]
    {Circuit : Type}
    (evalC : Circuit → qs.State → qs.State)
    (r : Reg)
    (o : ℕ)
    (C : Circuit)
    (ψ : qs.State) : ℝ :=
  MeasureClass.probMeas (qs := qs) r o (evalC C ψ)

/-- Total probability that the measured exponent-register outcome passes the
continued-fraction post-processing check. -/
noncomputable def probability_of_success
    [MeasureClass qs]
    [ContinuedFractionPost]
    {Circuit : Type}
    (evalC : Circuit → qs.State → qs.State)
    (T : ℕ → ℕ)
    (verify : OrderVerifier)
    (x : Reg)
    (r Q : ℕ)
    (C : Circuit)
    (ψ : qs.State) : ℝ :=
  ∑ o : Fin Q,
    (r_found (T := T) verify o.1 Q r) *
      measProbAfter
        (qs := qs) evalC x o.1 C ψ

/-- Public data and domain assumptions for one order-finding run. -/
structure ShorOrderFindingInstance where
  /-- The base whose order is being found. -/
  a : ℕ
  /-- The modulus to factor. -/
  N : ℕ
  /-- The exponent/control register. -/
  x : ExtReg
  /-- The modular-exponentiation data register. -/
  y : ExtReg
  /-- The sampled base is in the valid range. -/
  range : 0 < a ∧ a < N
  /-- The sampled base is coprime to the modulus. -/
  coprime : Nat.gcd a N = 1
  /-- The exponent register has the standard Shor width. -/
  x_width : regSize x.active = Nat.log2 (2 * N^2)
  /-- The data register has enough room for residues modulo `N`. -/
  y_width : regSize y.active = Nat.log2 (2 * N)
  /-- The public exponent and data registers occupy distinct qubits. -/
  xy_disjoint : Disjoint x.active y.active

/-- Ideal clean input predicate used by correctness proofs: both public
registers start at zero and own disjoint qubits. -/
def IdealOrderFindingInput
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (x y : ExtReg)
    (b0 : qs.Basis) : Prop :=
  RegEncoding.toNat x.active b0 = 0 ∧
  RegEncoding.toNat y.active b0 = 0 ∧
  ExtReg.OwnedDisjoint x y

variable [instCFP : ContinuedFractionPost]
variable [instMeas : MeasureClass qs]
variable [instLGC : LowerGateClass qs]

/-- Construction-free correctness obligation for a submitted `LowGate` circuit
family.

For every complete continued-fraction search bound and every valid instance,
the implementation can choose a precision level `m` whose circuit succeeds from
the global all-zero basis state with probability at least
`κ / log₂(N)^4 - ε`. The precision index is the only exposed resource knob; all
implementation-specific choices stay outside the framework interface. -/
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

/-- Bundle supplied by a Shor implementation at the `LowGate` boundary. -/
structure ShorImplementation : Type where
  /-- Circuit family indexed by the order-finding instance and precision level. -/
  prog : ShorOrderFindingInstance → ℕ → LowGate
  /-- Proof that the circuit family satisfies the framework success criterion. -/
  correct : ShorImplementsOrderFinding (qs := qs) prog
  /-- Declared concrete gate-count bound for the circuit family. -/
  gateBound : ShorOrderFindingInstance → ℕ → ℕ
  /-- Proof that each circuit meets its declared bound under the shared cost
  model. -/
  counted : ∀ (inst : ShorOrderFindingInstance) (m : ℕ),
    LowGate.gateCount shorGateCostModel (prog inst m) ≤ gateBound inst m

namespace ShorImplementation

/-- Any submitted implementation satisfying the interface is a correct
order-finder. -/
theorem framework_order_finding_correct (impl : ShorImplementation (qs := qs)) :
    ShorImplementsOrderFinding (qs := qs) impl.prog :=
  impl.correct

/-- Any submitted implementation satisfying the interface meets its declared
gate-count bound. -/
theorem framework_gate_count (impl : ShorImplementation (qs := qs)) :
    ∀ (inst : ShorOrderFindingInstance) (m : ℕ),
      LowGate.gateCount shorGateCostModel (impl.prog inst m) ≤ impl.gateBound inst m :=
  impl.counted

end ShorImplementation

end Shor
