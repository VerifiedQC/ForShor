-- This module serves as the root of the `ForShor` library.
-- Only the modules that are not already in another root's transitive closure
-- are listed; each line says what it roots.
import ForShor.ShorVerification.Implementation.Shor.Main                 -- correctness and gate-count theorems
import ForShor.ShorVerification.Implementation.QFT.Main
import ForShor.ShorVerification.Implementation.Compiler.Main
import ForShor.ShorVerification.Implementation.ModularExponentiation.Main
import ForShor.ShorVerification.Implementation.QubitCount.Main           -- qubit-count formula
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Main  -- three-register phase product: correctness, gate count, qubit count
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Witness.RecursionWitness  -- its non-vacuity witness
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Witness.ExactFault          -- and its width fault witness
import ForShor.ShorVerification.Framework.Policy                         -- policy submissions
import ForShor.ShorVerification.Framework.Gatecount.PolicyModel          -- the model a policy is priced under (its negation method)
import ForShor.ShorVerification.Implementation.PhaseProduct.Statement                  -- policy reserve model
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.PolicyWorkspace
import ForShor.ShorVerification.Submission.Decide                        -- submission surface
import ForShor.ShorVerification.Submission.Score
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Math.Table_Generation  -- table generator and its correctness proof
import ForShor.ShorVerification.Implementation.QubitCount.Proofs.PolicyNumerals       -- peaks of the sister-repository policies, both negation methods (scan rule)
import ForShor.ShorVerification.Submission.Policies.All                  -- the twelve sister-repository policies as Lean
import ForShor.ShorVerification.Submission.Policies.Board.All           -- the six PhaseTripleProduct board policies
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Peak.BoardNumerals  -- and their single-product peaks, both methods
