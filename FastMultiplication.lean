-- This module serves as the root of the `FastMultiplication` library.
-- Only the modules that are not already in another root's transitive closure
-- are listed; each line says what it roots.
import FastMultiplication.ShorVerification.Implementation.Shor.Main                 -- correctness theorems
import FastMultiplication.ShorVerification.Implementation.QFT.Main
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Main
import FastMultiplication.ShorVerification.Implementation.GateCount.Shor_GateCount  -- resource bounds
import FastMultiplication.ShorVerification.Framework.Policy                         -- policy submissions
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.PolicyWorkspace  -- policy reserve model
import FastMultiplication.ShorVerification.Submission.Decide                        -- submission surface
import FastMultiplication.ShorVerification.Submission.Score
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation      -- table generator and its correctness proof
