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
import ForShor.ShorVerification.Framework.Semantics.MSemanticsTests      -- measurement language MGate: syntax, record semantics, basic laws
import ForShor.ShorVerification.Implementation.Readout.Proofs.DeferredTests  -- semiclassical readout: one-round identity, deferred measurement
import ForShor.ShorVerification.Implementation.Readout.Tests  -- semiclassical readout: semiclassical_eq_iqft (equals the inverse-QFT readout)
import ForShor.ShorVerification.Implementation.Readout.Proofs.ApproxTests  -- semiclassical readout: approximate-gate bound (ℓ¹ ≤ 2 Σ (ε_j + ρ_j), i.e. TV ≤ Σ (ε_j + ρ_j))
import ForShor.ShorVerification.Implementation.Readout.ShorTests  -- semiclassical order finding with the real multiplier: success ≥ κ/(2 log(log₂ N + 1)) at shorPrecision; qubit support; global-phase-tolerant rotation errors
import ForShor.ShorVerification.Implementation.Readout.CostTests  -- semiclassical readout: exact counts (2m H, m measurements, m ffPhase, m-1 nontrivial), qubit formula without x / QFT term, saving ≥ xW - 1
import ForShor.ShorVerification.Implementation.Readout.LoweringTests  -- semiclassical readout: lowering to MLowGate (lowerM_eval), proved peak of the lowered real circuit = orderFindingQubitsSC (direct, balanced, every-site split), lowered qubits vs syntactic support
import ForShor.ShorVerification.Model.Standard.SemiclassicalLoweredModel  -- semiclassical readout: the LOWERED program (lowerM) is clean on every branch (semiclassical_clean), evaluates as the program, and succeeds with prob. >= κ/(2 log(log₂ N + 1)) at shorPrecision; model non-vacuity
import ForShor.ShorVerification.Model.Standard.SemiclassicalMainModel  -- semiclassical readout: success of the BALANCED / every-site-split lowerings (Implementation/Readout/BalancedShor.lean); success AND proved peak conjoined on one lowered circuit at the reference layout (plain, balanced, U)
import ForShor.ShorVerification.Implementation.Readout.GhostFreeTests  -- semiclassical readout WITHOUT the ghost exponent register: success = model-independent successMass, success theorems (high-level, ρ variants, lowered, balanced, U) with no x in any hypothesis
import ForShor.ShorVerification.Implementation.Readout.LocalityTests  -- semiclassical readout: semantic locality, a program (Gate/MGate without idealCtrlModMul) cannot depend on a qubit it never names; ideal (closed form), real and lowered circuits: record probabilities and success unchanged by flipping unnamed qubits; negative sanity
import ForShor.ShorVerification.Model.Standard.SemiclassicalLocalityModel  -- semiclassical readout locality at Model.qs: flipping every exponent qubit but the control leaves the real, lowered and ideal record distributions unchanged; lowered success >= κ/(2 log(log₂ N + 1)) from that nonzero ket
import ForShor.ShorVerification.Model.Standard.SemiclassicalGhostFreeModel  -- semiclassical readout without x: pure successMass_ge; success AND peak on one lowered circuit at the reference layout, no exponent register in the statement
import ForShor.ShorVerification.Implementation.Readout.LocalityReserve  -- semiclassical locality: exact support (qubits the ket laws read or write); unused reserve qubits are spectators of the real circuit
import ForShor.ShorVerification.Implementation.Readout.LocalityIdeal  -- semiclassical locality: ideal readout spectator law on span of kets with data < N (subsumes the data=1, control=0 theorem)
import ForShor.ShorVerification.Implementation.Readout.LocalityIdealTests  -- semiclassical locality on the ideal multiplier's domain: concrete checks and negative sanity
import ForShor.ShorVerification.Model.Standard.SemiclassicalLocalityIdealModel  -- Model.qs instances: unused reserves, non-degenerate ideal witnesses
import ForShor.ShorVerification.Implementation.Readout.LocalityInfinite  -- semiclassical locality: infinitely many differences outside the named qubits (block-matrix normal form)
import ForShor.ShorVerification.Implementation.Readout.LocalityInfiniteSuperpose  -- superpositions with infinite agreement
import ForShor.ShorVerification.Implementation.Readout.LocalityInfiniteTests  -- semiclassical locality for infinitely many differing qubits: concrete checks and negative sanity
import ForShor.ShorVerification.Model.Standard.SemiclassicalLocalityInfiniteModel  -- Model.qs instances: infinite patterns outside the named qubits
import ForShor.ShorVerification.Implementation.Readout.LowLocality  -- low-gate locality: lowered semiclassical circuit, adjoints, record independence
import ForShor.ShorVerification.Implementation.Readout.LowLocalityNamed  -- lowered footprint named by registers (semiclassicalQubits)
import ForShor.ShorVerification.Implementation.Readout.LowLocalityBalanced  -- balanced and U lowerings: footprint and locality; Valid derived from workspace conditions
import ForShor.ShorVerification.Implementation.Readout.LowLocalityTests  -- low-gate locality: adjoint nodes, footprints, negative sanity
import ForShor.ShorVerification.Model.Standard.SemiclassicalLowLocalityModel  -- Model.qs instances: exponent tail outside the lowered footprint; default-rule U instance without hf
import ForShor.ShorVerification.Implementation.Readout.LocalityDirty  -- lowered blocks on dirty reserves: closed forms, no-table faithfulness, proved negatives (dirty comparator unit qubit, lowered QFT pool qubit)
import ForShor.ShorVerification.Model.Standard.SemiclassicalDirtyModel  -- Model.qs instances of the dirty-reserve results
import ForShor.ShorVerification.Implementation.Readout.LocalityTight  -- exact support: refined set (one proved over-count removed), read theorems for named reserve sub-gates and whole Steps 3 and 4, toy record change
import ForShor.ShorVerification.Model.Standard.SemiclassicalLocalityTightModel  -- Model.qs instances of the refined-set and read results
import ForShor.ShorVerification.Implementation.PhaseProduct.Statement                  -- policy reserve model
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.PolicyWorkspace
import ForShor.ShorVerification.Submission.Decide                        -- submission surface
import ForShor.ShorVerification.Submission.Score
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Math.Table_Generation  -- table generator and its correctness proof
import ForShor.ShorVerification.Implementation.QubitCount.Proofs.PolicyNumerals       -- peaks of the sister-repository policies, both negation methods (scan rule)
import ForShor.ShorVerification.Submission.Policies.All                  -- the twelve sister-repository policies as Lean
import ForShor.ShorVerification.Submission.Policies.Board.All           -- the six PhaseTripleProduct board policies
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Peak.BoardNumerals  -- and their single-product peaks, both methods
import ForShor.ShorVerification.Submission.Policies.BoardPP.All     -- the nine PhaseProduct board policies
import ForShor.ShorVerification.Implementation.QubitCount.Proofs.PolicyNumeralsBoard  -- and their order-finding peaks (scan rule)
