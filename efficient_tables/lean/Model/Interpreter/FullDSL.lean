import Model.Scanner.Scanner
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Basic theory of the full instruction language

Lemmas about row-matrix execution of the full instruction language. Includes composition (`runRows_append`, `wordCharge_append`), the `shiftR`/`shiftL` round trip (`shiftR_then_shiftL`), and invertibility facts such as `runRows_det_ne_zero` (successful runs keep a nonzero determinant).
-/

namespace Paper.FullDSL

theorem runRows_append {k : Nat} (first second : List (Instruction k))
    (rows : Rows k) :
    runRows (first ++ second) rows =
      (runRows first rows).bind (runRows second) := by
  induction first generalizing rows with
  | nil => rfl
  | cons op rest ih =>
      simp only [List.cons_append, runRows]
      cases h : rowStep op rows with
      | none => simp
      | some rows' => simpa [h] using ih rows'

theorem wordCharge_append {k : Nat} (first second : List (Instruction k)) :
    wordCharge (first ++ second) = wordCharge first + wordCharge second := by
  simp [wordCharge, List.map_append, List.sum_append]

theorem shiftR_success_iff {k : Nat} (rows : Rows k) (i : Fin k) (n : Nat) :
    (∃ next, rowStep (.shiftR i n) rows = some next) ↔
      ∀ j : Fin k, rows i j % (2 : Int) ^ n = 0 := by
  simp [rowStep]

theorem shiftR_success_exact {k : Nat} (rows next : Rows k)
    (i : Fin k) (n : Nat)
    (h : rowStep (.shiftR i n) rows = some next) :
    ∀ j : Fin k, rows i j = (2 : Int) ^ n * next i j := by
  simp only [rowStep] at h
  split_ifs at h with hd
  · cases Option.some.inj h
    intro j
    have hdiv : (2 : Int) ^ n ∣ rows i j :=
      Int.dvd_iff_emod_eq_zero.mpr (hd j)
    simpa [Matrix.updateRow_self, mul_comm] using
      (Int.ediv_mul_cancel hdiv).symm

theorem shiftR_then_shiftL {k : Nat} (rows next : Rows k)
    (i : Fin k) (n : Nat)
    (h : rowStep (.shiftR i n) rows = some next) :
    rowStep (.shiftL i n) next = some rows := by
  have hexact := shiftR_success_exact rows next i n h
  simp only [rowStep] at h
  split_ifs at h with hd
  · have hn := Option.some.inj h
    subst next
    simp only [rowStep]
    congr 1
    have hrow :
        (fun j => (rows.updateRow i (fun t => rows i t / (2 : Int) ^ n)) i j *
            (2 : Int) ^ n) = rows i := by
      funext j
      simpa [Matrix.updateRow_self, mul_comm] using (hexact j).symm
    rw [hrow, Matrix.updateRow_idem, Matrix.updateRow_eq_self]

theorem runRows_cons_success {k : Nat} {op : Instruction k}
    {word : List (Instruction k)} {rows final : Rows k}
    (h : runRows (op :: word) rows = some final) :
    ∃ next, rowStep op rows = some next ∧ runRows word next = some final := by
  simp only [runRows] at h
  cases hs : rowStep op rows with
  | none => simp [hs] at h
  | some next =>
      simp only [hs, Option.bind_some] at h ⊢
      exact ⟨next, rfl, h⟩

theorem identity_det_ne_zero (k : Nat) : (identity k).det ≠ 0 := by
  simp [identity, Matrix.det_one]

theorem rowStep_det_ne_zero {k : Nat} {op : Instruction k}
    {rows next : Rows k} (hstep : rowStep op rows = some next)
    (hdet : rows.det ≠ 0) : next.det ≠ 0 := by
  cases op with
  | shiftL i n =>
      simp only [rowStep, Option.some.injEq] at hstep
      subst next
      have hrow : (fun j => rows i j * (2 : Int) ^ n) =
          (2 : Int) ^ n • rows i := by
        funext j
        simp [smul_eq_mul, mul_comm]
      rw [hrow, Matrix.det_updateRow_smul]
      simp only [Matrix.updateRow_eq_self]
      exact mul_ne_zero (pow_ne_zero _ (by norm_num : (2 : Int) ≠ 0)) hdet
  | shiftR i n =>
      simp only [rowStep] at hstep
      split_ifs at hstep with hdiv
      · have hnext := Option.some.inj hstep
        subst next
        let q : Fin k → Int := fun j => rows i j / (2 : Int) ^ n
        have hrow : rows i = (2 : Int) ^ n • q := by
          funext j
          have hj : (2 : Int) ^ n ∣ rows i j :=
            Int.dvd_iff_emod_eq_zero.mpr (hdiv j)
          simpa [q, smul_eq_mul, mul_comm] using
            (Int.ediv_mul_cancel hj).symm
        have hfactor :
            rows.det = (2 : Int) ^ n *
              (rows.updateRow i q).det := by
          calc
            rows.det = (rows.updateRow i (rows i)).det := by
              rw [Matrix.updateRow_eq_self]
            _ = (rows.updateRow i ((2 : Int) ^ n • q)).det := by rw [← hrow]
            _ = (2 : Int) ^ n * (rows.updateRow i q).det :=
              Matrix.det_updateRow_smul rows i ((2 : Int) ^ n) q
        intro hz
        apply hdet
        rw [hfactor]
        exact mul_eq_zero_of_right _ hz
  | negate i =>
      simp only [rowStep, Option.some.injEq] at hstep
      subst next
      have hrow : (fun j => -rows i j) = (-1 : Int) • rows i := by
        funext j
        simp [smul_eq_mul]
      rw [hrow, Matrix.det_updateRow_smul]
      simp only [Matrix.updateRow_eq_self]
      simpa using (neg_ne_zero.mpr hdet)
  | addScaled dst src negSrc shift =>
      by_cases heq : dst = src
      · simp [rowStep, heq] at hstep
      · cases negSrc with
        | false =>
            simp [rowStep, heq] at hstep
            subst next
            have hrow : (fun j => rows dst j + (2 : Int) ^ shift * rows src j) =
                rows dst + ((2 : Int) ^ shift) • rows src := by
              funext j
              simp
            rw [hrow, Matrix.det_updateRow_add_smul_self rows heq]
            exact hdet
        | true =>
            simp [rowStep, heq] at hstep
            subst next
            have hrow : (fun j => rows dst j + -((2 : Int) ^ shift * rows src j)) =
                rows dst + (-(2 : Int) ^ shift) • rows src := by
              funext j
              simp [neg_mul]
            rw [hrow, Matrix.det_updateRow_add_smul_self rows heq]
            exact hdet
  | phaseProduct i =>
      simp [rowStep] at hstep
      subst next
      exact hdet

theorem runRows_det_ne_zero {k : Nat} (word : List (Instruction k))
    {rows next : Rows k} (h : runRows word rows = some next)
    (hdet : rows.det ≠ 0) : next.det ≠ 0 := by
  induction word generalizing rows with
  | nil =>
      simp only [runRows, Option.some.injEq] at h
      subst next
      exact hdet
  | cons op rest ih =>
      obtain ⟨mid, hstep, hrest⟩ := runRows_cons_success h
      exact ih hrest (rowStep_det_ne_zero hstep hdet)

theorem rows_nonzero_of_det_ne_zero {k : Nat} {rows : Rows k}
    (hdet : rows.det ≠ 0) (i : Fin k) :
    ∃ j : Fin k, rows i j ≠ 0 := by
  by_contra hn
  have hz : ∀ j : Fin k, rows i j = 0 := by
    intro j
    by_contra hj
    exact hn ⟨j, hj⟩
  exact hdet (Matrix.det_eq_zero_of_row_eq_zero i hz)

theorem runRows_append_prefix_success {k : Nat}
    (pre suffix : List (Instruction k)) {rows final : Rows k}
    (hwhole : runRows (pre ++ suffix) rows = some final) :
    ∃ mid, runRows pre rows = some mid := by
  rw [runRows_append] at hwhole
  cases hp : runRows pre rows with
  | none => simp [hp] at hwhole
  | some mid => exact ⟨mid, rfl⟩

theorem successful_prefix_det_ne_zero {k : Nat}
    (pre suffix : List (Instruction k)) {mid final : Rows k}
    (hp : runRows pre (identity k) = some mid)
    (_hwhole : runRows (pre ++ suffix) (identity k) = some final) :
    mid.det ≠ 0 := by
  exact runRows_det_ne_zero pre hp (identity_det_ne_zero k)

theorem successful_run_prefix_rows_nonzero {k : Nat}
    (pre suffix : List (Instruction k)) {final : Rows k}
    (hwhole : runRows (pre ++ suffix) (identity k) = some final) :
    ∃ mid, runRows pre (identity k) = some mid ∧
      ∀ i : Fin k, ∃ j : Fin k, mid i j ≠ 0 := by
  obtain ⟨mid, hp⟩ := runRows_append_prefix_success pre suffix hwhole
  exact ⟨mid, hp,
    rows_nonzero_of_det_ne_zero
      (runRows_det_ne_zero pre hp (identity_det_ne_zero k))⟩

theorem successful_prefix_row_nonzero {k : Nat}
    (pre : List (Instruction k)) {mid : Rows k}
    (h : runRows pre (identity k) = some mid)
    (i : Fin k) : ∃ j : Fin k, mid i j ≠ 0 := by
  have hd := runRows_det_ne_zero pre h (identity_det_ne_zero k)
  exact rows_nonzero_of_det_ne_zero hd i

end Paper.FullDSL
