/-!
# Table_Generation umbrella

Re-exports the whole table-generation development. Layout:
- `Core/`     — program-agnostic: symbolic registers/state, the op language
                and its partial semantics, coverage/block framework, tactics.
- `Builders/` — reusable program-fragment builders (`computeLocal`,
                `addConstFrom`, …) out of which generators are assembled.
- `Programs/` — concrete generators and their certifications
                (currently `WithProduct` = `genOpsWithProduct`).
-/
import FastMultiplication.ShorVerification.MathBackbone.Table_Generation.Core.Registers
import FastMultiplication.ShorVerification.MathBackbone.Table_Generation.Core.RegisterLemmas
import FastMultiplication.ShorVerification.MathBackbone.Table_Generation.Core.Language
import FastMultiplication.ShorVerification.MathBackbone.Table_Generation.Core.Coverage
import FastMultiplication.ShorVerification.MathBackbone.Table_Generation.Core.Tactics
import FastMultiplication.ShorVerification.MathBackbone.Table_Generation.Builders.Fragments
import FastMultiplication.ShorVerification.MathBackbone.Table_Generation.Programs.WithProduct
import FastMultiplication.ShorVerification.MathBackbone.Table_Generation.Examples
