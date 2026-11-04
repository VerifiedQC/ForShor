import ForShor.ShorVerification.Implementation.PhaseProduct.Statement
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.Compile
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Gates.NaiveLeaf
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.PolicyWorkspace
import ForShor.ShorVerification.Framework.Policy

/-!
# Phase-Product Lowering Definitions

This first block names the compiled gates that recursive lowering steps point
to. The actual lowering plan type appears below; these names must come first
because the recursive plan constructors refer to them.
-/

namespace Shor
open Gate
open Operations
open scoped BigOperators

/-! =========================================================
    Standard interpolation-point public interface

    Public helpers specialize the plan machinery to the canonical interpolation
    points used by the phase-product compiler.
========================================================= -/

/-- The generated interpolation-point list has the required size. -/
lemma generatedInterpolationPoints_length (k : ℕ) : (genInterpolationPoints k).length = q k := by
  simp [genInterpolationPoints, q]

end Shor
