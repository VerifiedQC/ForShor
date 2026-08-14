import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.Lowering
import FastMultiplication.ShorVerification.Implementation.QFT.Proofs.Lowering
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Budgets
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.OrderFinding
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness

/-!
# Workspace verification index

This module re-exports the workspace-focused Shor verification files.

Suggested reading order:

1. `Workspace.Shor` defines shared budgets and clean-state predicates.
2. `Workspace.QFTLowering` constructs the canonical QFT workspace layout.
3. `Workspace.PhaseProductLowering` proves recursive phase-product allocation
   preserves child workspace cleanliness.
4. `Workspace.ShorOrderFinding` defines the order-finding circuits and setup
   structures.
5. `Workspace.ShorReadiness` proves the static and dynamic workspace readiness
   theorems, ending at `LoweredShorReady.workspace_clean`.
-/
