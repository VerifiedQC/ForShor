import FastMultiplication.ShorVerification.Basic.Registers
import FastMultiplication.ShorVerification.Basic.Gates
import FastMultiplication.ShorVerification.Basic.Semantics

/-!
# Shor verification core (umbrella)

Split into `Basic.Registers`, `Basic.Gates`, `Basic.Semantics`; re-exports
all three so existing `import …Basic` lines keep working.
-/
