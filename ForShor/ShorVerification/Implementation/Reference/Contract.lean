import ForShor.ShorVerification.Implementation.Shor.Statement

/-!
# Reference: the order-finding contract

`ShorImplementation` is what a submitted order-finding construction provides: a
circuit for every instance (`ShorOrderFindingProgram`), a declared success
probability it is proved to meet, and a trial count for the 2048-bit benchmark
(`Is2048Bit`). `Standard/` builds one value of it, and `Balanced/` another.
-/

namespace Shor

/-! ## The order-finding contract -/

section

open Classical

variable {qs : QSemantics}
variable [RegEncoding qs.Basis]

/-- A natural number has exactly 2048 bits: it lies in `[2^2047, 2^2048)`. -/
def Is2048Bit (N : ℕ) : Prop :=
  2 ^ 2047 ≤ N ∧ N < 2 ^ 2048

/-- The observable output of a submitted order-finding construction. -/
structure ShorOrderFindingProgram where
  /-- The concrete lowered circuit. -/
  circuit : LowGate
  /-- The register measured for order recovery. -/
  output : Reg

/-- The logical gate count of a program under the framework's shared cost model.
Computed by the framework, never declared. It is what the asymptotic bounds in
`Shor/Main.lean` are about; it is *not* the leaderboard score, which is measured
outside Lean on the emitted IR. -/
def ShorOrderFindingProgram.frameworkGateCount (P : ShorOrderFindingProgram) : ℕ :=
  LowGate.gateCount shorGateCostModel P.circuit

variable [MeasureClass qs]
variable [LowerGateClass qs]

/-- A verified Shor order-finding construction: the framework's semantic contract.

Correctness is universal: `program` must correctly implement order finding for
every valid `ShorOrderFindingInstance`. Amplification is benchmark-specific:
`trialCount` is one concrete number of independent trials sufficient to push the
declared success lower bound past 99% for every 2048-bit modulus.

Built rather than written by hand: `Reference.referenceShorImplementation`
constructs this record from a policy, filling `correct` from
`Reference.referenceSubmittedProgram_correct`. That theorem is generic in the
table, which is what makes the four decidable side conditions on a submitted
table a complete acceptance test.

There is no declared gate-count field: the logical gate count of a circuit is
computed by the framework (`ShorOrderFindingProgram.frameworkGateCount`), and the
scored count is measured outside Lean altogether. -/
structure ShorImplementation : Type where
  /-- The submitted circuit family, for every valid order-finding instance. -/
  program : ShorOrderFindingInstance → ShorOrderFindingProgram
  /-- Declared lower bound on the success probability of one run. -/
  successProbability : ℕ → ℝ
  /-- The submitted circuit achieves the declared single-run success probability on
  every valid order-finding instance. -/
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
  /-- One concrete number of independent trials used for the 2048-bit benchmark. -/
  trialCount : ℕ → ℕ
  /-- For every 2048-bit modulus, `trialCount` runs at the declared success lower
  bound give probability at least 99% of at least one successful run. -/
  trialCount_correct :
    ∀ N : ℕ, Is2048Bit N →
      (99 / 100 : ℝ) ≤ 1 - (1 - successProbability N) ^ (trialCount N)

end

end Shor
