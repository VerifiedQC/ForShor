import FastMultiplication.ShorVerification.Submission.Template
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.ExactWidthBound

/-!
# Exact-width drop-in: worked instances and a fault challenge (kernel-checked)

On the shipped `k = 2` table (`Submission/Template.lean`, the Karatsuba table
the shipped policy uses on its lower band), at operand width 20:

* the exact width is 12 and the original scan says 13 (`exact_20`, `fold_20`);
* **fault challenge**: one bit below, at 11 bits, some reachable row overflows at
  a point of the limb box (a box corner lies outside the signed 11-bit range) (`exact_20_tight`, via the least-width characterisation), so
  the exact width cannot be lowered;
* at 12 bits every reachable value fits (`exact_20_fits`).

Not part of `PolicySubmission` (its build is the acceptance check for any
policy); built by `lean_lib ExactWidthTests`.
-/

namespace ExactWidthTests

open Shor Operations

abbrev ops : Prog 2 := Submission.ops

theorem exact_20 : exactSignedWidthOfWidths ops 20 20 = 12 := by decide +kernel

theorem tight_20 : tightSignedWidthOfWidths ops 20 20 = 12 := by decide +kernel

theorem floor_20 : floorSignedWidthOfWidths 2 20 20 = 11 := by decide +kernel

/-- The fault challenge: 11 bits do not hold every reachable value (the exact
width is least). -/
theorem exact_20_tight : ¬ ExactFits ops 20 20 11 := by
  intro h
  have := tight_le_of_exactFits (by norm_num) h
  rw [tight_20] at this
  omega

/-- At the exact width every reachable value fits. -/
theorem exact_20_fits : ExactFits ops 20 20 12 := by
  rw [← tight_20]; exact exactFits_tight ops 20 20

end ExactWidthTests
