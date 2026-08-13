/-
# Table_Generation umbrella

Re-exports the whole table-generation development. Layout:
- `Core/`     — program-agnostic: symbolic registers/state, the op language
                and its partial semantics, coverage/block framework, tactics.
- `Builders/` — reusable program-fragment builders (`computeLocal`,
                `addConstFrom`, …) out of which generators are assembled.
- `Programs/` — concrete generators and their certifications
                (currently `WithProduct` = `genOpsWithProduct`).
- `Generator/` — the parity-reset generator, precomputed small cases, and
                 correctness proof.
-/
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Core.Registers
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Core.RegisterLemmas
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Core.Language
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Core.Coverage
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Core.Tactics
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Core.ListHelpers
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Core.RunLemmas
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Builders.Fragments
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Builders.FragmentLemmas
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Programs.WithProduct
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Generator
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Examples
