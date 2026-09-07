import FastMultiplication.ShorVerification.Framework.Math.ShorDefinition
import FastMultiplication.ShorVerification.Framework.Quantum.Measurement
import FastMultiplication.ShorVerification.Framework.Semantics.LowGateSemantics
import FastMultiplication.ShorVerification.Framework.Gatecount.ResourceModel

namespace Shor

open Classical

/-!
# Submission Interface

This module is the public framework boundary for Shor order-finding submissions.

A submission provides one `LowGate` circuit for each valid order-finding
instance, declares a lower bound on its single-run success probability,
certifies that bound, declares the number of independent trials used to
amplify success to at least 99%, and certifies the resource count of the
same submitted circuit.

Construction, lowering, synthesis, precision selection, and workspace
details remain entirely on the implementation side.
-/

variable {qs : QSemantics}

variable [RegEncoding qs.Basis]

/-- Total probability that measurement of the exponent register produces
an outcome from which the continued-fraction postprocessing recovers the
correct order. -/
noncomputable def probability_of_success
    [MeasureClass qs]
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
      MeasureClass.probMeas (qs := qs) x o.1 (evalC C ψ)

/-- Public data and domain assumptions for one order-finding instance. -/
structure ShorOrderFindingInstance where
  /-- The base whose order is being found. -/
  a : ℕ
  /-- The modulus. -/
  N : ℕ
  /-- The sampled base lies in the valid range. -/
  range : 0 < a ∧ a < N
  /-- The sampled base is coprime to the modulus. -/
  coprime : Nat.gcd a N = 1

/-- The observable output of a submitted order-finding construction. -/
structure ShorOrderFindingProgram where
  /-- The concrete lowered circuit. -/
  circuit : LowGate
  /-- The register measured for order recovery. -/
  output : Reg

variable [MeasureClass qs]

variable [LowerGateClass qs]

/--
A verified Shor order-finding submission.

The implementation chooses all internal parameters itself and exposes only
the final circuit for each public instance.

`successProbability N` is the submission's declared lower bound on the
success probability of one run for modulus `N`. The correctness field proves
that the actual Born probability of successful order recovery is at least
that declared value.

`trialCount N` is the number of independent runs the submission declares
sufficient to amplify that lower bound to at least 99%.

`gateCount inst` is the declared logical gate count of the same submitted
single-run circuit under the framework's shared cost model.
-/
structure ShorImplementation : Type where
  /-- Concrete submitted circuit family. -/
  program : ShorOrderFindingInstance → ShorOrderFindingProgram

  /-- Declared lower bound on the success probability of one run. -/
  successProbability : ℕ → ℝ

  /--
  The submitted circuit achieves at least the declared single-run success
  probability on every valid order-finding instance.
  -/
  correct :
    ∀ (T : ℕ → ℕ), ContinuedFractionSearchComplete T →
    ∀ (inst : ShorOrderFindingInstance),
      0 ≤ successProbability inst.N ∧ successProbability inst.N ≤ 1 ∧
      successProbability inst.N ≤
        probability_of_success (qs := qs) (evalC := LowerGateClass.evalL (qs := qs))
          (T := T) (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
          (x := (program inst).output)
          (r := ord inst.a inst.N inst.coprime)
          (Q := ASize (program inst).output)
          (C := (program inst).circuit)
          (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis)))

  /-- Declared logical gate count of one run. -/
  gateCount : ShorOrderFindingInstance → ℕ

  /-- The submitted circuit has exactly its declared framework gate count. -/
  gateCount_correct :
    ∀ (inst : ShorOrderFindingInstance),
      LowGate.gateCount
          shorGateCostModel
          (program inst).circuit =
        gateCount inst

  /-- Number of independent trials used for modulus `N`. -/
  trialCount :
    ℕ → ℕ

  /--
  Repeating a trial with the declared lower bound this many times raises
  the probability of at least one success to at least 99%.
  -/
  trialCount_correct :
    ∀ N : ℕ,
      (99 / 100 : ℝ) ≤ 1 - (1 - successProbability N) ^ trialCount N

end Shor
