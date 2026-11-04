import ForShor.ShorVerification.Implementation.PhaseProduct.Statement
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.Coefficients
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.Compile
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.Layout
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.Workspace
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Lowering.Lower
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Lowering.Plan
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Lowering.PlanBuilders
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Math.MasterTheorem
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.NaiveLeaf
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Lowering.Lowerable
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.Support
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.Body.Controlled
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Math.Table_Generation.Programs.WithProduct

/-!
# Phase product: facts about the generated interpolation program

The program `genOpsWithProduct` built from the generated interpolation points
is well formed, consumes the points safely, and has one recursive
phase-product leaf per point. `Reference/StandardLoweringSetup.lean` uses the
consumption fact to build the standard setup.
-/

namespace Shor

/-! ---------------------------------------------------------
    Generated interpolation table facts

This section proves that the automatically generated interpolation program is
well formed, safely consumes the interpolation table, and contributes exactly one
recursive PhaseProduct leaf per generated point.
--------------------------------------------------------- -/

section GeneratedInterpolationFacts

/-- A well-formed PhaseProduct program is safe for the only operation family
whose safety condition is not purely structural: `addScaled`. -/
lemma SafeProg_of_WellFormed {k : ℕ} {ops : Prog k}
    (hWF : Prog.WellFormed ops) :
    SafeProg ops := by
  intro pre rest d s negSrc sh hops
  have hmem : Operations.valid_ops.addScaled d s negSrc sh ∈ ops := by
    rw [hops]
    simp
  simpa [Prog.OpOK] using hWF (Operations.valid_ops.addScaled d s negSrc sh) hmem


/-- A singleton PhaseProduct operation is well formed, serving as the leaf in
each generated interpolation-point block. -/
lemma phaseProduct_singleton_WellFormed {k : ℕ} (i : Fin k) :
    Prog.WellFormed ([Operations.valid_ops.phaseProduct i] : Prog k) := by
  intro op hop
  simp at hop
  subst op
  simp [Prog.OpOK]

/-- The program emitted for one interpolation point is well formed: compute the
local value, emit one PhaseProduct, then uncompute. -/
lemma opsForPointWithProduct_WellFormed {k : ℕ} (hk : 0 < k) (pt : Operations.Point) :
    Prog.WellFormed (opsForPointWithProduct (k := k) hk pt) := by
  cases pt with
  | int z =>
      have hBuild : Prog.WellFormed (computeLocal2 (k := k) hk z) :=
        computeLocal2_Valid (k := k) (z := z) hk
      have hPhase : Prog.WellFormed ([Operations.valid_ops.phaseProduct (finZero hk)] : Prog k) :=
        phaseProduct_singleton_WellFormed (k := k) (finZero hk)
      have hInv : Prog.WellFormed (apply_Op_inverse (computeLocal2 (k := k) hk z)) :=
        Prog.apply_Op_inverse_preserves_WF hBuild
      simpa [opsForPointWithProduct] using
        WellFormed_append (k := k) hBuild (WellFormed_append (k := k) hPhase hInv)
  | frac c =>
      by_cases hc : c = 0
      · have hPhase : Prog.WellFormed ([Operations.valid_ops.phaseProduct (finLast hk)] : Prog k) :=
          phaseProduct_singleton_WellFormed (k := k) (finLast hk)
        simpa [opsForPointWithProduct, hc] using hPhase
      · have hBuild : Prog.WellFormed (computeFracLocal2 (k := k) hk c) :=
          computeFracLocal2_Valid (k := k) (c := c) hk
        have hPhase : Prog.WellFormed ([Operations.valid_ops.phaseProduct (finLast hk)] : Prog k) :=
          phaseProduct_singleton_WellFormed (k := k) (finLast hk)
        have hInv : Prog.WellFormed (apply_Op_inverse (computeFracLocal2 (k := k) hk c)) :=
          Prog.apply_Op_inverse_preserves_WF hBuild
        simpa [opsForPointWithProduct, hc] using
          WellFormed_append (k := k) hBuild (WellFormed_append (k := k) hPhase hInv)

/-- A list of generated point blocks is well formed by appending the
well-formed block for each interpolation point. -/
lemma genOpsWithProduct_WellFormed {k : ℕ} (hk : 0 < k) :
    ∀ pts : List Operations.Point, Prog.WellFormed (genOpsWithProduct (k := k) hk pts)
  | [] => by
      intro op hop
      simp [genOpsWithProduct] at hop
  | pt :: pts => by
      simpa [genOpsWithProduct] using
        WellFormed_append (k := k) (opsForPointWithProduct_WellFormed (k := k) hk pt)
          (genOpsWithProduct_WellFormed (k := k) hk pts)

/-- The generated table safely consumes exactly the interpolation points while
using only well-formed arithmetic operations. -/
lemma genOpsWithProduct_ProgConsumesPtsSafe {k : ℕ} (hk : 0 < k)
    (pts : List Operations.Point) :
    ProgConsumesPtsSafe (k := k) hk State.start_state
      (genOpsWithProduct (k := k) hk pts) pts where
  consumes := genOpsWithProduct_ProgConsumesPts (k := k) hk pts
  safe_add := SafeProg_of_WellFormed
    (genOpsWithProduct_WellFormed (k := k) hk pts)

/-- Integer local-computation blocks contain no PhaseProduct leaves, so they
contribute zero to the PhaseProduct leaf count. -/
lemma computeLocal2_NoPhase {k : ℕ} (hk : 0 < k) (z : ℤ) :
    NoPhase (computeLocal2 (k := k) hk z) := by
  exact NoPhase_of_onlyAddScaled (onlyAddScaled_computeLocal2 (k := k) hk z)

/-- The inverse of an integer local-computation block also contains no
PhaseProduct leaves, keeping uncomputation out of the branching factor. -/
lemma computeLocal2_inverse_NoPhase {k : ℕ} (hk : 0 < k) (z : ℤ) :
    NoPhase (apply_Op_inverse (computeLocal2 (k := k) hk z)) := by
  rw [computeLocal_eq (k := k) (z := z) hk]
  exact (computeLocal_NoPhase_2 (k := k) hk z).2

/-- Each interpolation-point block contributes exactly one recursive
PhaseProduct leaf. -/
lemma phaseProductCount_opsForPointWithProduct {k : ℕ} (hk : 0 < k)
    (pt : Operations.Point) :
    phaseProductCount (opsForPointWithProduct (k := k) hk pt) = 1 := by
  cases pt with
  | int z =>
      have hBuild :
          phaseProductCount (computeLocal2 (k := k) hk z) = 0 :=
        phaseProductCount_eq_zero_of_NoPhase (computeLocal2_NoPhase (k := k) hk z)
      have hInv :
          phaseProductCount (apply_Op_inverse (computeLocal2 (k := k) hk z)) = 0 :=
        phaseProductCount_eq_zero_of_NoPhase (computeLocal2_inverse_NoPhase (k := k) hk z)
      simp [opsForPointWithProduct, phaseProductCount_append,
        phaseProductCount, hBuild, hInv]
  | frac c =>
      by_cases hc : c = 0
      · simp [opsForPointWithProduct, hc, phaseProductCount]
      · have hBuild :
            phaseProductCount (computeFracLocal2 (k := k) hk c) = 0 :=
          phaseProductCount_eq_zero_of_NoPhase (computeFracLocal2_NoPhase (k := k) hk c)
        have hInv :
            phaseProductCount (apply_Op_inverse (computeFracLocal2 (k := k) hk c)) = 0 :=
          phaseProductCount_eq_zero_of_NoPhase ((computeFracLocal2_NoPhase_2 (k := k) hk c).2)
        simp [opsForPointWithProduct, hc, phaseProductCount_append,
          phaseProductCount, hBuild, hInv]

/-- The generated program has one PhaseProduct leaf per interpolation point,
giving the final branching factor `q k `. -/
lemma phaseProductCount_genOpsWithProduct {k : ℕ} (hk : 0 < k) :
    ∀ pts : List Operations.Point,
      phaseProductCount (genOpsWithProduct (k := k) hk pts) = pts.length
  | [] => by
      simp [genOpsWithProduct, phaseProductCount]
  | pt :: pts => by
      simp [genOpsWithProduct, phaseProductCount_append,
        phaseProductCount_opsForPointWithProduct (k := k) hk pt,
        phaseProductCount_genOpsWithProduct (k := k) hk pts, Nat.add_comm]

end GeneratedInterpolationFacts

end Shor
