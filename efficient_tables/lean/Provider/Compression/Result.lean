import Provider.Compression.CertificateTransfer

/-!
# Complete compression of an F2 source

Defines `complete t`, the F2 source obtained from `t` by compression and
padding at its original peaks `originalA`, `originalB`. It proves the result has
the exact original profile (`complete_exact_profile`), and records its length,
charge, arity, points, child width, exponents and prefix coefficients
(`complete_length`, `complete_charge`, `complete_childWidth`,
`complete_every_prefix_coefficients`).
-/

namespace Paper.CompressionComplete

open Paper.F2CatalogTransfer Paper.PrefixPaddingStage
open Paper.CompressionF2 Paper.CompressionEncoding
open Paper.SourceBridge Paper.FullDSL Paper.Scanner

def originalA {K : Nat} (t : F2Source K) : Nat := (sourceProfileRaw t).peakA
def originalB {K : Nat} (t : F2Source K) : Nat := (sourceProfileRaw t).peakB

theorem original_profile_canonical {K : Nat} (t : F2Source K) :
    originalB t ≤ originalA t ∧
      originalA t ≤ originalB t + (t.source.k - 1) := by
  let top := TableGeneration.finLast (TableGeneration.positive_of_ge_two t.source.hk)
  have h := Paper.Profile.fresh_peak_profile_intercept_bounds top
    (widthWord (mapToFull t.source.program)) (t.source.k - 1)
  change max 0 (originalA t - (t.source.k - 1)) ≤ originalB t ∧
      originalB t ≤ originalA t at h
  constructor
  · exact h.2
  · have hh := h.1
    omega

def complete {K : Nat} (t : F2Source K) : F2Source K :=
  paddedCompressedF2 t (originalA t) (originalB t)

theorem complete_exact_profile {K : Nat} (t : F2Source K) :
    sourceProfileRaw (complete t) = sourceProfileRaw t := by
  obtain ⟨hBA, hcanon⟩ := original_profile_canonical t
  obtain ⟨hA, hB⟩ := paddedCompressedF2_exactPeaks t
    (originalA t) (originalB t) hBA hcanon (le_refl _) (le_refl _)
  have hc := paddedCompressedF2_profileCharge t (originalA t) (originalB t)
  have hc' : (sourceProfileRaw (complete t)).charge =
      (sourceProfileRaw t).charge := by simpa [complete] using hc
  have hA' : (sourceProfileRaw (complete t)).peakA =
      (sourceProfileRaw t).peakA := by simpa [complete, originalA] using hA
  have hB' : (sourceProfileRaw (complete t)).peakB =
      (sourceProfileRaw t).peakB := by simpa [complete, originalB] using hB
  cases hx : sourceProfileRaw (complete t) with
  | mk c a b =>
      cases hy : sourceProfileRaw t with
      | mk c' a' b' =>
          simp only [hx, hy] at hc' hA' hB' ⊢
          cases hc'
          cases hA'
          cases hB'
          rfl

theorem complete_length {K : Nat} (t : F2Source K) :
    (complete t).source.program.length ≤
      (t.source.k + 1) *
        (min (t.source.k * originalA t)
          (t.source.k * originalB t + (t.source.k - 1)^2) +
          (2 * t.source.k - 1)) + t.source.k + 4 := by
  have hcontract := (source_contract_iff_trace
    (TableGeneration.positive_of_ge_two t.source.hk)
    TableGeneration.State.start_state t.source.program (List.ofFn t.points)).1 t.safe
  have hrun : TableGeneration.run? t.source.program TableGeneration.State.start_state =
      some TableGeneration.State.start_state := by
    have hr : runRows (mapToFull t.source.program)
        TableGeneration.State.start_state = some TableGeneration.State.start_state := by
      rw [← markerTrace_fst]
      simp [hcontract.2]
    simpa [runRows_eq_run_of_safe t.source.program _ hcontract.1] using hr
  have hclosed : runRows (mapToFull t.source.program) (identity t.source.k) =
      some (identity t.source.k) := by
    rw [runRows_from_start_of_safe t.source.program t.safe.safe_add]
    simpa [source_start_eq_identity] using hrun
  have hpaid := (Paper.ScannerPotential.source_charged_bound
    (TableGeneration.finLast (TableGeneration.positive_of_ge_two t.source.hk))
    t.source.program hclosed).1
  have hlen := paddedCompressedF2_lengthF2 t (originalA t) (originalB t)
  rw [complete, hlen]
  have hpaid' : Paper.ScannerPotential.totalPaid (mapToFull t.source.program) ≤
      min (t.source.k * originalA t)
        (t.source.k * originalB t + (t.source.k - 1)^2) := by
    simpa [sourceProfileRaw, originalA, originalB] using hpaid
  have hm := Nat.mul_le_mul_left (t.source.k + 1)
    (Nat.add_le_add_right hpaid' (2 * t.source.k - 1))
  omega

theorem complete_charge {K : Nat} (t : F2Source K) :
    (complete t).charge = t.charge :=
  paddedCompressedF2_charge t (originalA t) (originalB t)

theorem complete_arity {K : Nat} (t : F2Source K) :
    (complete t).source.k = t.source.k := rfl

theorem complete_points {K : Nat} (t : F2Source K) :
    (complete t).points = t.points := rfl

private theorem f2_run_success {K : Nat} (t : F2Source K) :
    TableGeneration.run? t.source.program TableGeneration.State.start_state =
      some TableGeneration.State.start_state := by
  have hr := (returnsToStartCheck_eq_true_iff_model t.source.program
    TableGeneration.State.start_state t.safe.safe_add).1 t.safe.returns_start
  simpa [runRows_eq_run_of_safe t.source.program _ t.safe.safe_add] using hr

theorem f2_childWidth_profile {K : Nat} (t : F2Source K) (w : Nat) :
    t.childWidth w = Paper.Planner.childWidth t.source.k (sourceProfileRaw t) w := by
  let top := TableGeneration.finLast (TableGeneration.positive_of_ge_two t.source.hk)
  have htop : top.val + 1 = t.source.k := by
    change t.source.k - 1 + 1 = t.source.k
    have hk := t.source.hk
    omega
  simpa [F2Source.childWidth, sourceProfileRaw, top] using
    (original_legal_program_childWidth top htop t.source.program
      TableGeneration.State.start_state t.safe.safe_add (f2_run_success t) w)

theorem complete_childWidth {K : Nat} (t : F2Source K) (w : Nat) :
    (complete t).childWidth w = t.childWidth w := by
  rw [f2_childWidth_profile, f2_childWidth_profile, complete_exact_profile]
  rfl

theorem complete_exponents {K : Nat} (t : F2Source K) :
    ∀ op ∈ (complete t).source.program,
      exponentWithin (widthOp (toFull op)) (originalA t) := by
  obtain ⟨hBA, hcanon⟩ := original_profile_canonical t
  exact paddedF2_exponents_within_A t (originalA t) (originalB t)
    hBA hcanon (le_refl _) (le_refl _)

theorem complete_every_prefix_coefficients {K : Nat} (t : F2Source K)
    (pre suffix : List (Instruction t.source.k))
    (hsplit : pre ++ suffix = mapToFull (complete t).source.program) :
    ∃ rows : Rows t.source.k,
      runRows pre (identity t.source.k) = some rows ∧
        ∀ i j, (rows i j).natAbs ≤ 2 ^ originalA t := by
  obtain ⟨hBA, hcanon⟩ := original_profile_canonical t
  exact paddedF2_every_prefix_coefficients t (originalA t) (originalB t)
    hBA hcanon (le_refl _) (le_refl _) pre suffix hsplit

end Paper.CompressionComplete
