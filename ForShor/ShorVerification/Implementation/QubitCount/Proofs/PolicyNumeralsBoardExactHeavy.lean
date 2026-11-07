import ForShor.ShorVerification.Implementation.QubitCount.Proofs.PolicyNumeralsBoard.Rowc7f81cb40081Exact
import ForShor.ShorVerification.Implementation.QubitCount.Proofs.PolicyNumeralsBoard.Row6f7d25984ff8K8Exact
import ForShor.ShorVerification.Implementation.QubitCount.Proofs.PolicyNumeralsBoard.Rowf4aff955f16bExact
import ForShor.ShorVerification.Implementation.QubitCount.Proofs.PolicyNumeralsBoard.Rowf0f15fefe959Exact

/-!
# Qubit count: 2048-bit peaks of the PhaseProduct board policies (width rule `exact`, the memory-heavy four)

The board's own width rule, for 4 of the 9 distinct PhaseProduct board policies: `c7f81cb40081`, `6f7d25984ff8K8`, `f4aff955f16b`, `f0f15fefe959`. Each module's kernel evaluation peaks at 13 to 15.4 GB of memory (the eight-way policies and the single-band k = 6 policy), more than a 16 GB runner comfortably gives, so the modules form an import chain (Lake builds them one at a time). The first one imports the last module of the light chain (`PolicyNumeralsBoardExact`), so building this library builds that chain first and never two heavy evaluations at once; they are not part of the `ForShor` umbrella.
-/
