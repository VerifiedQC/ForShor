import ForShor.ShorVerification.Implementation.Compiler.Statement
import ForShor.ShorVerification.Implementation.Compiler.Proofs.Correctness
import ForShor.ShorVerification.Implementation.Compiler.Proofs.SingleTable

/-!
# Compiler Main Theorem

Proves the correctness claim stated in `Statement.lean`. Importing this file
also brings the single-table forms in `Proofs/SingleTable.lean`.
-/

namespace Shor

/-- The lowering of `Gate` to `LowGate` is correct under any admissible policy. -/
theorem Policy.lowerGate_correct
    (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]
    (P : ShorLoweringPolicy) :
    Policy.LowerGateCorrect qs P :=
  fun hP G hworkspace ψ hclean => Policy.lowerGate_correctness qs P hP G hworkspace ψ hclean

end Shor
