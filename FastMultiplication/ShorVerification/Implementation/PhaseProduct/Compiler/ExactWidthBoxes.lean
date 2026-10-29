import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.ExactWidth

/-!
# The exact width over arbitrary limb boxes (interface for other splits)

`ExactWidth.lean` fixes the limb box to ForShor's split (common lower-limb
width `W = min (xw/k) (zw/k)`, top chunk signed). A different split (for
example a balanced split of unequal operands) changes only the boxes. This
leaf module states the exact width as a function of the table's program and
**two arbitrary boxes**, `x` limbs in `[xlo, xhi]` and `z` limbs in
`[zlo, zhi]`, with soundness and minimality, and shows the compiler's width
is its instance at ForShor's boxes (`tightSignedWidthOfWidths_eq_boxes`, by `rfl`).

A split that wants exact widths supplies its boxes and proves that its chunk
readings lie in them (as `WidthSoundness.lean`'s `sourceChunkXInt_box` does for
ForShor's split); `tightOfBoxes_fits` then gives the lowering's fit obligation.
-/

namespace Shor
open Operations
open scoped BigOperators

variable {k : ℕ}

def boxRowLo (lo hi : Fin k → ℤ) (r : Register k) : ℤ :=
  ((List.finRange k).map fun j => min (r j * lo j) (r j * hi j)).sum

def boxRowHi (lo hi : Fin k → ℤ) (r : Register k) : ℤ :=
  ((List.finRange k).map fun j => max (r j * lo j) (r j * hi j)).sum

def boxRowDemand (lo hi : Fin k → ℤ) (r : Register k) : ℕ :=
  max (-boxRowLo lo hi r).toNat (boxRowHi lo hi r + 1).toNat

def InBox (lo hi : Fin k → ℤ) (L : Fin k → ℤ) : Prop := ∀ j, lo j ≤ L j ∧ L j ≤ hi j

/-- Largest demand over the reachable rows on both boxes. -/
def boxDemand (ops : Prog k) (xlo xhi zlo zhi : Fin k → ℤ) : ℕ :=
  exactListMax ((exactReachRows ops).map fun r =>
    max (boxRowDemand xlo xhi r) (boxRowDemand zlo zhi r))

/-- **The tight width over two boxes.** -/
def tightOfBoxes (ops : Prog k) (xlo xhi zlo zhi : Fin k → ℤ) : ℕ :=
  1 + exactLeastExp (boxDemand ops xlo xhi zlo zhi) (boxDemand ops xlo xhi zlo zhi) 0

/-- The compiler's tight width is the instance at ForShor's split boxes. -/
theorem tightSignedWidthOfWidths_eq_boxes (ops : Prog k) (xw zw : ℕ) :
    tightSignedWidthOfWidths ops xw zw =
      tightOfBoxes ops (exactLimbLo xw (exactLimbWidth k xw zw)) (exactLimbHi xw (exactLimbWidth k xw zw))
        (exactLimbLo zw (exactLimbWidth k xw zw)) (exactLimbHi zw (exactLimbWidth k xw zw)) := rfl

theorem tightOfBoxes_spec (ops : Prog k) (xlo xhi zlo zhi : Fin k → ℤ) :
    boxDemand ops xlo xhi zlo zhi ≤ 2 ^ (tightOfBoxes ops xlo xhi zlo zhi - 1) ∧
      ∀ e < tightOfBoxes ops xlo xhi zlo zhi - 1, ¬ boxDemand ops xlo xhi zlo zhi ≤ 2 ^ e := by
  have h := exactLeastExp_spec (boxDemand ops xlo xhi zlo zhi) (boxDemand ops xlo xhi zlo zhi) 0
    (by simpa using Nat.lt_two_pow_self.le) (fun _ h => absurd h (Nat.not_lt_zero _))
  simpa [tightOfBoxes] using h

theorem box_row_bounds {lo hi L : Fin k → ℤ} (r : Register k) (hL : InBox lo hi L) :
    boxRowLo lo hi r ≤ rowVal r L ∧ rowVal r L ≤ boxRowHi lo hi r := by
  unfold boxRowLo boxRowHi
  rw [← Fin.sum_univ_def, ← Fin.sum_univ_def]
  unfold rowVal
  exact ⟨Finset.sum_le_sum fun j _ => (exact_term_bounds (c := r j) (hL j).1 (hL j).2).1,
    Finset.sum_le_sum fun j _ => (exact_term_bounds (c := r j) (hL j).1 (hL j).2).2⟩

/-- **Soundness**: every reachable row fits the tight width on both boxes. -/
theorem tightOfBoxes_fits (ops : Prog k) (xlo xhi zlo zhi : Fin k → ℤ) {r : Register k}
    (hr : r ∈ exactReachRows ops) {E : ℕ} (hE : tightOfBoxes ops xlo xhi zlo zhi ≤ E) :
    (∀ L, InBox xlo xhi L → FitsSignedWidth E (rowVal r L)) ∧
    (∀ L, InBox zlo zhi L → FitsSignedWidth E (rowVal r L)) := by
  have hmem : max (boxRowDemand xlo xhi r) (boxRowDemand zlo zhi r) ≤ boxDemand ops xlo xhi zlo zhi :=
    le_exactListMax (List.mem_map.mpr ⟨r, hr, rfl⟩)
  have hD := le_trans (tightOfBoxes_spec ops xlo xhi zlo zhi).1
    (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le_sub_right hE 1))
  have hpos : 0 < E := lt_of_lt_of_le (by unfold tightOfBoxes; omega) hE
  refine ⟨fun L hL => ?_, fun L hL => ?_⟩
  · obtain ⟨hlo, hhi⟩ := box_row_bounds r hL
    exact fits_of_exactDemand hpos hlo hhi (le_trans (le_trans (le_max_left _ _) hmem) hD)
  · obtain ⟨hlo, hhi⟩ := box_row_bounds r hL
    exact fits_of_exactDemand hpos hlo hhi (le_trans (le_trans (le_max_right _ _) hmem) hD)

/-- **Minimality**: if every reachable row fits `E` on both boxes (boxes
non-empty), the tight width is at most `E`. -/
theorem tightOfBoxes_le (ops : Prog k) {xlo xhi zlo zhi : Fin k → ℤ}
    (hx : ∀ j, xlo j ≤ xhi j) (hz : ∀ j, zlo j ≤ zhi j) {E : ℕ} (hE : 0 < E)
    (h : ∀ r ∈ exactReachRows ops,
      (∀ L, InBox xlo xhi L → FitsSignedWidth E (rowVal r L)) ∧
      (∀ L, InBox zlo zhi L → FitsSignedWidth E (rowVal r L))) :
    tightOfBoxes ops xlo xhi zlo zhi ≤ E := by
  -- corners attain both ends
  have corner : ∀ (lo hi : Fin k → ℤ), (∀ j, lo j ≤ hi j) → ∀ r : Register k,
      (∀ L, InBox lo hi L → FitsSignedWidth E (rowVal r L)) → boxRowDemand lo hi r ≤ 2 ^ (E - 1) := by
    intro lo hi hle r hf
    let cH : Fin k → ℤ := fun j => if 0 ≤ r j then hi j else lo j
    let cL : Fin k → ℤ := fun j => if 0 ≤ r j then lo j else hi j
    have bH : InBox lo hi cH := fun j => by
      have := hle j; simp only [cH]; split <;> constructor <;> omega
    have bL : InBox lo hi cL := fun j => by
      have := hle j; simp only [cL]; split <;> constructor <;> omega
    have eH : rowVal r cH = boxRowHi lo hi r := by
      unfold boxRowHi; rw [← Fin.sum_univ_def]; unfold rowVal
      refine Finset.sum_congr rfl fun j _ => ?_
      have := hle j; simp only [cH]
      split
      · rename_i h0; exact (max_eq_right (mul_le_mul_of_nonneg_left this h0)).symm
      · rename_i h0; exact (max_eq_left (mul_le_mul_of_nonpos_left this (by omega))).symm
    have eL : rowVal r cL = boxRowLo lo hi r := by
      unfold boxRowLo; rw [← Fin.sum_univ_def]; unfold rowVal
      refine Finset.sum_congr rfl fun j _ => ?_
      have := hle j; simp only [cL]
      split
      · rename_i h0; exact (min_eq_left (mul_le_mul_of_nonneg_left this h0)).symm
      · rename_i h0; exact (min_eq_right (mul_le_mul_of_nonpos_left this (by omega))).symm
    obtain ⟨-, -, h2⟩ := hf cH bH
    obtain ⟨-, h1, -⟩ := hf cL bL
    rw [eH] at h2; rw [eL] at h1
    unfold signedMin at h1; unfold signedMax at h2
    unfold boxRowDemand
    refine max_le ?_ ?_
    · have : (-boxRowLo lo hi r).toNat ≤ ((2 ^ (E - 1) : ℕ) : ℤ).toNat := Int.toNat_le_toNat (by omega)
      simpa using this
    · have : (boxRowHi lo hi r + 1).toNat ≤ ((2 ^ (E - 1) : ℕ) : ℤ).toNat := Int.toNat_le_toNat (by omega)
      simpa using this
  have hD : boxDemand ops xlo xhi zlo zhi ≤ 2 ^ (E - 1) := by
    unfold boxDemand
    refine exactListMax_le fun a ha => ?_
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
    exact max_le (corner _ _ hx r (h r hr).1) (corner _ _ hz r (h r hr).2)
  have hmin := (tightOfBoxes_spec ops xlo xhi zlo zhi).2
  by_contra hlt
  exact hmin (E - 1) (by omega) hD

end Shor
