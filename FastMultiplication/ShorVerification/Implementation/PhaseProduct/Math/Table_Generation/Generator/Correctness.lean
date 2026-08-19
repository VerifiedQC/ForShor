import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Generator.WellFormed
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Core.Coverage

open Operations

namespace Table_Generation

lemma phaseProduct_singleton_WellFormed {k : ℕ} (i : Fin k) :
    Prog.WellFormed ([valid_ops.phaseProduct i] : Prog k) := by
  intro op hop
  simp at hop
  subst op
  simp [Prog.OpOK]

lemma opsForPointWithProduct_WellFormed {k : ℕ} (hk : 0 < k) (pt : Point) :
    Prog.WellFormed (opsForPointWithProduct (k := k) hk pt) := by
  cases pt with
  | int z =>
      have hBuild : Prog.WellFormed (computeLocal2 (k := k) hk z) :=
        computeLocal2_Valid (k := k) (z := z) hk
      have hPhase : Prog.WellFormed ([valid_ops.phaseProduct (finZero hk)] : Prog k) :=
        phaseProduct_singleton_WellFormed (k := k) (finZero hk)
      have hInv : Prog.WellFormed (apply_Op_inverse (computeLocal2 (k := k) hk z)) :=
        Prog.apply_Op_inverse_preserves_WF hBuild
      simpa [opsForPointWithProduct] using
        WellFormed_append (k := k) hBuild (WellFormed_append (k := k) hPhase hInv)
  | frac c =>
      by_cases hc : c = 0
      · have hPhase : Prog.WellFormed ([valid_ops.phaseProduct (finLast hk)] : Prog k) :=
          phaseProduct_singleton_WellFormed (k := k) (finLast hk)
        simpa [opsForPointWithProduct, hc] using hPhase
      · have hBuild : Prog.WellFormed (computeFracLocal2 (k := k) hk c) :=
          computeFracLocal2_Valid (k := k) (c := c) hk
        have hPhase : Prog.WellFormed ([valid_ops.phaseProduct (finLast hk)] : Prog k) :=
          phaseProduct_singleton_WellFormed (k := k) (finLast hk)
        have hInv : Prog.WellFormed (apply_Op_inverse (computeFracLocal2 (k := k) hk c)) :=
          Prog.apply_Op_inverse_preserves_WF hBuild
        simpa [opsForPointWithProduct, hc] using
          WellFormed_append (k := k) hBuild (WellFormed_append (k := k) hPhase hInv)

lemma genOpsWithProduct_WellFormed {k : ℕ} (hk : 0 < k) (pts : List Point) :
    Prog.WellFormed (genOpsWithProduct (k := k) hk pts) := by
  induction pts with
  | nil =>
      simp [genOpsWithProduct, Prog.WellFormed]
  | cons pt pts ih =>
      simp [genOpsWithProduct]
      exact WellFormed_append (opsForPointWithProduct_WellFormed hk pt) ih

/- The generated point list is the protected canonical point list. -/
theorem generatedPoints_valid (mode : ProductMode) (k : ℕ) (_ : k ≥ 2) :
    ValidPointList mode k (generatedPoints mode k) := by
  simp [ValidPointList, generatedPoints]

/- The generated program safely consumes a permutation of the canonical points. -/
theorem generate_ProgConsumesPtsSafe (mode : ProductMode) (k : ℕ) (hk : k ≥ 2) :
    ValidPointOrder mode k (generatePointsInOrder mode k hk) ∧
      ProgConsumesPtsSafe (by omega) State.start_state
        (generate mode k hk) (generatePointsInOrder mode k hk) := by
  constructor
  · simp [ValidPointOrder, generatePointsInOrder, generatedPoints]
  · constructor
    · simp [generate]
      exact
        genOpsWithProduct_ProgConsumesPts (k := k) (by omega)
          (generatePointsInOrder mode k hk)
    · apply SafeProg_of_WellFormed
      simp [generate]
      exact
        genOpsWithProduct_WellFormed (k := k) (by omega)
          (generatePointsInOrder mode k hk)

end Table_Generation
