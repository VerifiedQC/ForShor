import FastMultiplication.ShorVerification.Framework.Math.ShorDefinition
import FastMultiplication.ShorVerification.Framework.Quantum.Measurement
import FastMultiplication.ShorVerification.Framework.Semantics.LowGateSemantics
import FastMultiplication.ShorVerification.Framework.Gatecount.ResourceModel

namespace Shor

open Classical

/-!
# The framework's correctness contract

What "a correct Shor order-finding construction" means, stated once:
`probability_of_success`, the instance and program records, and
`ShorImplementation`, which bundles a circuit family with a proof that it
meets a declared single-run success bound on every valid instance and a
trial count amplifying that bound past 99% on the 2048-bit benchmark.

**This is no longer what a submitter writes.** `SUBMISSION_PLAN.md` §0/P7
narrowed the challenge: a submission is a Toom-Cook table
(`Shor.ShorSubmission`, in `Framework/ToomCookTable.lean`) — an arithmetic
program and the interpolation points it evaluates at — and the reference
construction turns any admissible table into a circuit family. So
`ShorImplementation` became the framework's *internal* contract rather than
its public boundary: every accepted submission `s` still yields one, as
`Reference.referenceShorImplementation s`, but nobody writes the fields by
hand. The file was called `Framework/Submission.lean` until S3.3; the name
now collides with both `Submission/` and `ShorSubmission`, and "contract" is
what it always was.

Scoring moved out too (decision P4). The leaderboard score is
`Shor.submissionTrialCount N` (`Submission/Score.lean`, fixed for every
submission at the organiser's chosen precision) times the gate count
Qualtran measures on the IR `Emit/` extracts — not a quantity computed in
Lean. `ShorOrderFindingProgram.frameworkGateCount` below is kept, and is
still the count the asymptotic theorems (`GateCount/Shor_GateCount.lean`)
are stated with; it is just no longer the scored number.

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
The logical gate count of a program under the framework's shared cost model.

Computed by the framework, never declared. It is what
`GateCount/Shor_GateCount.lean`'s asymptotic bounds are about; it is *not*
the leaderboard score, which is measured by Qualtran on the emitted IR
(P4).
-/
def ShorOrderFindingProgram.frameworkGateCount
    (P : ShorOrderFindingProgram) : ℕ :=
  LowGate.gateCount shorGateCostModel P.circuit

variable [MeasureClass qs]

variable [LowerGateClass qs]

/--
A verified Shor order-finding construction: the framework's semantic
contract.

Correctness is universal: `program` must correctly implement order finding
for every valid `ShorOrderFindingInstance`. Amplification is
benchmark-specific: `trialCount` is one concrete natural number of
independent trials sufficient to push the declared success lower bound past
99% for every 2048-bit modulus.

Not written by hand any more. An accepted submission is a
`Shor.ShorSubmission` (`Framework/ToomCookTable.lean`), and
`Reference.referenceShorImplementation` builds this record from it, filling
`correct` from `Reference.referenceSubmittedProgram_correct` — the theorem
that is generic in the table, which is what makes the four decidable side
conditions on a table a *complete* acceptance test.

There is no declared gate-count field: the logical gate count of a circuit is
computed by the framework (`ShorOrderFindingProgram.frameworkGateCount`), and
the scored count is measured outside Lean altogether (P4).
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
