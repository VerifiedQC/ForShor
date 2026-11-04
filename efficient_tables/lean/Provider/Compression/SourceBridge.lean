import Provider.Compression.Trace

/-!
# Compression bridge to the source program

Connects whole-word compression to source programs: `sourceCompressed` is the
compressed form of a source program `ops`. It proves it preserves rows,
scanner behaviour, trace and charge (`sourceCompressed_rows`,
`sourceCompressed_trace`, `sourceCompressed_charge`), matches the marker
count (`sourceMarkers_eq_phaseProductCount`), and bounds its length and peaks
(`sourceCompressed_length_bound`, `sourceCompressed_peakA`).
-/

namespace Paper.CompressionSource

open Paper.FullDSL Paper.Scanner Paper.SourceBridge
open Paper.WholeCompression Paper.CompressionTrace

def sourceCompressed {k : Nat} (ops : TableGeneration.Prog k) :
    List (Instruction k) := compressWhole (mapToFull ops)

theorem sourceCompressed_rows {k : Nat} (ops : TableGeneration.Prog k)
    (final : TableGeneration.State k)
    (hsafe : TableGeneration.safeProg? ops = true)
    (hsuccess : TableGeneration.run? ops TableGeneration.State.start_state = some final) :
    runRows (sourceCompressed ops) (identity k) = some final := by
  apply compressWhole_runRows
  rw [runRows_from_start_of_safe ops hsafe]
  exact hsuccess

theorem sourceCompressed_scanner {k : Nat} (ops : TableGeneration.Prog k)
    (final : TableGeneration.State k)
    (hsafe : TableGeneration.safeProg? ops = true)
    (hsuccess : TableGeneration.run? ops TableGeneration.State.start_state = some final)
    (s : State k) (hvalid : ∀ i, s.widths i ≤ s.peak) :
    noUnderflow (widthWord (sourceCompressed ops)) s.widths ∧
    (scan (widthWord (sourceCompressed ops)) s).widths =
      (scan (widthWord (mapToFull ops)) s).widths ∧
    (scan (widthWord (sourceCompressed ops)) s).peak ≤
      (scan (widthWord (mapToFull ops)) s).peak := by
  exact compressWhole_scanner (mapToFull ops) s
    (original_safe_noUnderflow s.widths ops final hsafe hsuccess) hvalid

theorem sourceCompressed_trace {k : Nat} (ops : TableGeneration.Prog k)
    (rows final : Rows k) (marks : List (Fin k → Int))
    (htrace : markerTrace (mapToFull ops) rows = some (final, marks)) :
    markerTrace (sourceCompressed ops) rows = some (final, marks) := by
  exact compressWhole_trace (mapToFull ops) rows final marks htrace

theorem sourceCompressed_charge {k : Nat} (ops : TableGeneration.Prog k) :
    wordCharge (sourceCompressed ops) = wordCharge (mapToFull ops) :=
  compressWhole_charge _

theorem sourceMarkers_eq_phaseProductCount {k : Nat}
    (ops : TableGeneration.Prog k) :
    totalMarkers (mapToFull ops) = TableGeneration.phaseProductCount ops := by
  induction ops with
  | nil => rfl
  | cons op rest ih =>
      simp only [totalMarkers, mapToFull, List.map_map] at ih
      cases op with
      | addScaled d s b n =>
          cases b <;> simp [totalMarkers, markerOps, mapToFull, toFull,
            TableGeneration.phaseProductCount, ih]
      | shiftL i n =>
          simp [totalMarkers, markerOps, mapToFull, toFull,
            TableGeneration.phaseProductCount, ih]
      | shiftR i n =>
          simp [totalMarkers, markerOps, mapToFull, toFull,
            TableGeneration.phaseProductCount, ih]
      | negate i =>
          simp [totalMarkers, markerOps, mapToFull, toFull,
            TableGeneration.phaseProductCount, ih]
      | phaseProduct i =>
          simp [totalMarkers, markerOps, mapToFull, toFull,
            TableGeneration.phaseProductCount, ih]
          omega
theorem sourceCompressed_length {k : Nat} (ops : TableGeneration.Prog k) :
    (sourceCompressed ops).length =
      (k + 1) * (Paper.ScannerPotential.totalPaid (mapToFull ops) +
        TableGeneration.phaseProductCount ops) + k := by
  rw [sourceCompressed, compressWhole_length, separatorCount_eq_paid_markers]
  rw [sourceMarkers_eq_phaseProductCount]

theorem sourceCompressed_length_bound {k : Nat} (ops : TableGeneration.Prog k)
    (q : Nat) (hq : TableGeneration.phaseProductCount ops ≤ q) :
    (sourceCompressed ops).length ≤
      (k + 1) * (Paper.ScannerPotential.totalPaid (mapToFull ops) + q) + k := by
  rw [sourceCompressed_length]
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_left _ (Nat.add_le_add_left hq _)) _

theorem sourceCompressed_peakA {k : Nat} (top : Fin k)
    (ops : TableGeneration.Prog k) (final : TableGeneration.State k)
    (hsafe : TableGeneration.safeProg? ops = true)
    (hsuccess : TableGeneration.run? ops TableGeneration.State.start_state = some final) :
    (scan (widthWord (sourceCompressed ops))
      (fresh (balanced top 0 0))).peak ≤ (sourceProfile top ops).peakA := by
  have hvalid : ∀ i, (fresh (balanced top 0 0)).widths i ≤
      (fresh (balanced top 0 0)).peak := by
    intro i
    exact Finset.le_sup (f := balanced top 0 0) (Finset.mem_univ i)
  have h := (sourceCompressed_scanner ops final hsafe hsuccess
    (fresh (balanced top 0 0)) hvalid).2.2
  simpa [sourceProfile] using h

theorem sourceCompressed_peakB {k : Nat} (top : Fin k)
    (ops : TableGeneration.Prog k) (final : TableGeneration.State k)
    (hsafe : TableGeneration.safeProg? ops = true)
    (hsuccess : TableGeneration.run? ops TableGeneration.State.start_state = some final) :
    (scan (widthWord (sourceCompressed ops))
      (fresh (balanced top 0 (k - 1)))).peak - (k - 1) ≤
      (sourceProfile top ops).peakB := by
  have hvalid : ∀ i, (fresh (balanced top 0 (k - 1))).widths i ≤
      (fresh (balanced top 0 (k - 1))).peak := by
    intro i
    exact Finset.le_sup (f := balanced top 0 (k - 1)) (Finset.mem_univ i)
  have h := (sourceCompressed_scanner ops final hsafe hsuccess
    (fresh (balanced top 0 (k - 1))) hvalid).2.2
  exact Nat.sub_le_sub_right (by simpa [sourceProfile] using h) _

end Paper.CompressionSource
