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
instance and proves that the resulting circuit is correct for every valid
modulus and base.

Correctness is completely general: a submitted implementation must satisfy
the framework's order-finding specification for every valid input instance.

Resource comparison is benchmark-specific.  The competition benchmark is
the family of 2048-bit moduli.  A submission provides one concrete number of
independent trials sufficient to amplify the declared single-run success
probability to at least 99% for every 2048-bit modulus (`trialCount`); the
logical gate count of a single run is not declared by the submission but
computed by the framework itself, via `ShorOrderFindingProgram.frameworkGateCount`,
from the concrete circuit the submission's `program` produces for a given
instance.

The leaderboard score is the product

`trialCount N * (program inst).frameworkGateCount` for a 2048-bit modulus `N`.

Construction, lowering, synthesis, precision selection, workspace layout,
and all other implementation details remain entirely on the implementation
side.
-/

variable {qs : QSemantics}

variable [RegEncoding qs.Basis]

/--
A natural number has exactly 2048 bits.

Equivalently, it lies in the interval `[2^2047, 2^2048)`.
-/
def Is2048Bit (N : ℕ) : Prop :=
  2 ^ 2047 ≤ N ∧ N < 2 ^ 2048

/--
Total probability that measurement of the exponent register produces
an outcome from which continued-fraction postprocessing recovers the
correct order.
-/
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

/--
Public data and domain assumptions for one order-finding instance.
-/
structure ShorOrderFindingInstance where

  /-- The base whose order is being found. -/
  a : ℕ

  /-- The modulus. -/
  N : ℕ

  /-- The sampled base lies in the valid range. -/
  range : 0 < a ∧ a < N

  /-- The sampled base is coprime to the modulus. -/
  coprime : Nat.gcd a N = 1

/--
The observable output of a submitted order-finding construction.
-/
structure ShorOrderFindingProgram where

  /-- The concrete lowered circuit. -/
  circuit : LowGate

  /-- The register measured for order recovery. -/
  output : Reg

/--
The logical gate count of a submitted program under the framework's
shared cost model.

This quantity is computed by the framework.  A submission does not provide
its own gate-count function.
-/
def ShorOrderFindingProgram.frameworkGateCount
    (P : ShorOrderFindingProgram) : ℕ :=
  LowGate.gateCount shorGateCostModel P.circuit

variable [MeasureClass qs]

variable [LowerGateClass qs]

/--
A verified Shor order-finding submission.

Correctness is universal: `program` must correctly implement order finding
for every valid `ShorOrderFindingInstance`.

Resource competition is specialized to 2048-bit moduli.

`trialCount` is one concrete natural number of independent trials that is
sufficient to amplify the declared success lower bound to at least 99% for
every 2048-bit modulus.

There is no separately declared gate-count bound: the logical gate count of a
submitted circuit is computed by the framework itself
(`ShorOrderFindingProgram.frameworkGateCount`), directly from `program`.

The leaderboard score is

`trialCount N * (program inst).frameworkGateCount` for a 2048-bit instance
`inst` with modulus `N`.
-/
structure ShorImplementation : Type where

  /--
  Concrete submitted circuit family.

  The implementation must produce a circuit for every valid order-finding
  instance, not merely for 2048-bit benchmark instances.
  -/
  program : ShorOrderFindingInstance → ShorOrderFindingProgram

  /--
  Declared lower bound on the success probability of one run as a
  function of the modulus.
  -/
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
        probability_of_success
          (qs := qs)
          (evalC := LowerGateClass.evalL (qs := qs))
          (T := T)
          (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
          (x := (program inst).output)
          (r := ord inst.a inst.N inst.coprime)
          (Q := ASize (program inst).output)
          (C := (program inst).circuit)
          (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis)))

  /--
  One concrete number of independent trials used for the 2048-bit
  benchmark.
  -/
  trialCount :
    ℕ → ℕ

  /--
  For every 2048-bit modulus, repeating a run with the submission's
  declared success lower bound `trialCount` times gives probability at
  least 99% of seeing at least one successful run.
  -/
  trialCount_correct :
    ∀ N : ℕ,
      Is2048Bit N →
        (99 / 100 : ℝ) ≤ 1 - (1 - successProbability N) ^ (trialCount N)

end Shor
