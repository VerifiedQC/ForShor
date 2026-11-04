-- This module serves as the root of the `ForShor` library.
-- Only the modules that are not already in another root's transitive closure
-- are listed; each line says what it roots.
import ForShor.ShorVerification.Implementation.Shor.Main                 -- correctness and gate-count theorems
import ForShor.ShorVerification.Implementation.QFT.Main
import ForShor.ShorVerification.Implementation.Compiler.Main
import ForShor.ShorVerification.Implementation.ModularExponentiation.Main
import ForShor.ShorVerification.Implementation.QubitCount.Main           -- qubit-count formula
import ForShor.ShorVerification.Framework.Policy                         -- policy submissions
import ForShor.ShorVerification.Implementation.PhaseProduct.Statement                  -- policy reserve model
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.PolicyWorkspace
import ForShor.ShorVerification.Submission.Decide                        -- submission surface
import ForShor.ShorVerification.Submission.Score
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Math.Table_Generation  -- table generator and its correctness proof
