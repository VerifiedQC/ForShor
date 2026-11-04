import ForShor.ShorVerification.Implementation.PhaseProduct.Statement

/-!
# Phase-Product Compiler: facts about the exact working width

`Statement.lean` defines the exact width (`exactSignedWidthOfWidths`): the rows a
table visits (`exactReachRows`), the limb box of each operand, the demand, and
the tight and floor widths. This file proves the integer-level facts about it:
every visited state is reached by a prefix and conversely, a row's range over
the box is attained at a corner, a signed register holds the row iff its
demand fits, and the tight width is the least exponent that fits.
`Proofs/Compiler/WidthSoundness.lean` uses these for the lowering's fit
obligation and `Proofs/Compiler/ExactWidthBound.lean` for the comparison with
the scan.
-/

namespace Shor
open Operations
open scoped BigOperators



/-! ## Tabulation (an evaluation device, extensionally the identity) -/

/-! ## The states and rows a program visits -/

/-- Every state a prefix of the program reaches is visited. -/
theorem mem_exactReachStates {k : ℕ} :
    ∀ (pre rest : Prog k) (σ0 σ : State k),
      run? pre σ0 = some σ → σ ∈ exactReachStates σ0 (pre ++ rest)
  | [], rest, σ0, σ, h => by
      simp only [run?, Option.some.injEq] at h
      subst h
      cases rest <;> simp [exactReachStates]
  | op :: pre, rest, σ0, σ, h => by
      simp only [run?] at h
      cases hs : applyOp? σ0 op with
      | none => rw [hs] at h; cases h
      | some σ1 =>
          rw [hs] at h
          simp only [List.cons_append, exactReachStates, hs, exactTab_eq]
          exact List.mem_cons_of_mem _ (mem_exactReachStates pre rest σ1 σ h)

/-- Conversely, every visited state is reached by a prefix. -/
theorem run_of_mem_exactReachStates {k : ℕ} :
    ∀ (ops : Prog k) (σ0 σ : State k), σ ∈ exactReachStates σ0 ops →
      ∃ pre rest, ops = pre ++ rest ∧ run? pre σ0 = some σ
  | [], σ0, σ, h => by
      simp only [exactReachStates, List.mem_singleton] at h
      subst h
      exact ⟨[], [], rfl, rfl⟩
  | op :: ops, σ0, σ, h => by
      simp only [exactReachStates] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨[], op :: ops, rfl, rfl⟩
      · cases hs : applyOp? σ0 op with
        | none => rw [hs] at h; cases h
        | some σ1 =>
            simp only [hs, exactTab_eq] at h
            obtain ⟨pre, rest, he, hr⟩ := run_of_mem_exactReachStates ops σ1 σ h
            exact ⟨op :: pre, rest, by rw [he]; rfl, by simp only [run?, hs]; exact hr⟩

theorem mem_exactReachRows {k : ℕ} {ops pre rest : Prog k} {σ : State k}
    (hops : ops = pre ++ rest) (hrun : run? pre State.start_state = some σ) (i : Fin k) :
    σ i ∈ exactReachRows ops := by
  unfold exactReachRows
  rw [List.mem_flatMap]
  exact ⟨σ, hops ▸ mem_exactReachStates pre rest _ σ hrun,
    List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩⟩

theorem exists_of_mem_exactReachRows {k : ℕ} {ops : Prog k} {r : Register k}
    (h : r ∈ exactReachRows ops) :
    ∃ pre rest σ i, ops = pre ++ rest ∧ run? pre State.start_state = some σ ∧ σ i = r := by
  unfold exactReachRows at h
  obtain ⟨σ, hσ, hr⟩ := List.mem_flatMap.mp h
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hr
  obtain ⟨pre, rest, hops, hrun⟩ := run_of_mem_exactReachStates _ _ _ hσ
  exact ⟨pre, rest, σ, i, hops, hrun, rfl⟩

/-! ## Fast evaluation (`@[csimp]`: proved equal, used by compiled code)

`exactReachStates` re-tabulates with `exactTab`, whose array the code
generator may recompute inside the returned closure; and `exactRowLo/Hi`
recompute the box bounds (`2^t`) for every row. The definitions above are the
specification; the versions below carry the state as an `Array` value (never a
closure) and take the bounds as arrays computed once per call. The `@[csimp]`
theorems make every compiled caller use them; they are equalities, so nothing
the kernel checks changes. -/

/-! ## The limb box and row ranges -/

/-- The value of row `r` on limbs `L`. -/
def rowVal {k : ℕ} (r : Register k) (L : Fin k → ℤ) : ℤ := ∑ j, r j * L j

/-- `L` lies in the limb box of an operand of width `w` at lower-limb width `W`. -/
def InExactBox (w W : ℕ) {k : ℕ} (L : Fin k → ℤ) : Prop :=
  ∀ j, exactLimbLo w W j ≤ L j ∧ L j ≤ exactLimbHi w W j

theorem exactLimbLo_le_hi (w W : ℕ) {k : ℕ} (j : Fin k) :
    exactLimbLo w W j ≤ exactLimbHi w W j := by
  unfold exactLimbLo exactLimbHi
  split
  · split
    · exact le_rfl
    · have : (1 : ℤ) ≤ 2 ^ (phaseSplitLogicalWidth w W k j - 1) := one_le_pow₀ (by norm_num)
      linarith
  · have : (1 : ℤ) ≤ 2 ^ (phaseSplitLogicalWidth w W k j) := one_le_pow₀ (by norm_num)
    linarith

theorem exactRowLo_eq (w W : ℕ) {k : ℕ} (r : Register k) :
    exactRowLo w W r = ∑ j, min (r j * exactLimbLo w W j) (r j * exactLimbHi w W j) :=
  (Fin.sum_univ_def _).symm

theorem exactRowHi_eq (w W : ℕ) {k : ℕ} (r : Register k) :
    exactRowHi w W r = ∑ j, max (r j * exactLimbLo w W j) (r j * exactLimbHi w W j) :=
  (Fin.sum_univ_def _).symm

theorem exact_term_bounds {c l lo hi : ℤ} (h1 : lo ≤ l) (h2 : l ≤ hi) :
    min (c * lo) (c * hi) ≤ c * l ∧ c * l ≤ max (c * lo) (c * hi) := by
  rcases le_total 0 c with hc | hc
  · exact ⟨le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left h1 hc),
      le_trans (mul_le_mul_of_nonneg_left h2 hc) (le_max_right _ _)⟩
  · exact ⟨le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_left h2 hc),
      le_trans (mul_le_mul_of_nonpos_left h1 hc) (le_max_left _ _)⟩

/-- **Interval soundness**: on the box, a row's value lies in `[rowLo, rowHi]`. -/
theorem exact_row_bounds (w W : ℕ) {k : ℕ} (r : Register k) {L : Fin k → ℤ}
    (hL : InExactBox w W L) :
    exactRowLo w W r ≤ rowVal r L ∧ rowVal r L ≤ exactRowHi w W r := by
  rw [exactRowLo_eq, exactRowHi_eq]
  unfold rowVal
  exact ⟨Finset.sum_le_sum fun j _ => (exact_term_bounds (c := r j) (hL j).1 (hL j).2).1,
    Finset.sum_le_sum fun j _ => (exact_term_bounds (c := r j) (hL j).1 (hL j).2).2⟩

/-- The corner of the box where the row is largest. -/
def exactCornerHi (w W : ℕ) {k : ℕ} (r : Register k) : Fin k → ℤ :=
  fun j => if 0 ≤ r j then exactLimbHi w W j else exactLimbLo w W j

/-- The corner of the box where the row is least. -/
def exactCornerLo (w W : ℕ) {k : ℕ} (r : Register k) : Fin k → ℤ :=
  fun j => if 0 ≤ r j then exactLimbLo w W j else exactLimbHi w W j

theorem exactCornerHi_box (w W : ℕ) {k : ℕ} (r : Register k) :
    InExactBox w W (exactCornerHi w W r) := fun j => by
  have := exactLimbLo_le_hi w W j
  unfold exactCornerHi; split <;> constructor <;> omega

theorem exactCornerLo_box (w W : ℕ) {k : ℕ} (r : Register k) :
    InExactBox w W (exactCornerLo w W r) := fun j => by
  have := exactLimbLo_le_hi w W j
  unfold exactCornerLo; split <;> constructor <;> omega

/-- **Attainment** of the upper end. -/
theorem exact_rowHi_attained (w W : ℕ) {k : ℕ} (r : Register k) :
    rowVal r (exactCornerHi w W r) = exactRowHi w W r := by
  rw [exactRowHi_eq]
  unfold rowVal exactCornerHi
  refine Finset.sum_congr rfl fun j _ => ?_
  have hle := exactLimbLo_le_hi w W j
  split
  · rename_i h; exact (max_eq_right (mul_le_mul_of_nonneg_left hle h)).symm
  · rename_i h; exact (max_eq_left (mul_le_mul_of_nonpos_left hle (by omega))).symm

/-- **Attainment** of the lower end. -/
theorem exact_rowLo_attained (w W : ℕ) {k : ℕ} (r : Register k) :
    rowVal r (exactCornerLo w W r) = exactRowLo w W r := by
  rw [exactRowLo_eq]
  unfold rowVal exactCornerLo
  refine Finset.sum_congr rfl fun j _ => ?_
  have hle := exactLimbLo_le_hi w W j
  split
  · rename_i h; exact (min_eq_left (mul_le_mul_of_nonneg_left hle h)).symm
  · rename_i h; exact (min_eq_right (mul_le_mul_of_nonpos_left hle (by omega))).symm

/-- Demand bound ⇒ fit. -/
theorem fits_of_exactDemand {E : ℕ} {z lo hi : ℤ} (hE : 0 < E) (hlo : lo ≤ z) (hhi : z ≤ hi)
    (hd : max (-lo).toNat (hi + 1).toNat ≤ 2 ^ (E - 1)) : FitsSignedWidth E z := by
  have h1 : (-lo).toNat ≤ 2 ^ (E - 1) := le_trans (le_max_left _ _) hd
  have h2 : (hi + 1).toNat ≤ 2 ^ (E - 1) := le_trans (le_max_right _ _) hd
  have e1 := Int.self_le_toNat (-lo)
  have e2 := Int.self_le_toNat (hi + 1)
  have c1 : ((-lo).toNat : ℤ) ≤ ((2 ^ (E - 1) : ℕ) : ℤ) := by exact_mod_cast h1
  have c2 : ((hi + 1).toNat : ℤ) ≤ ((2 ^ (E - 1) : ℕ) : ℤ) := by exact_mod_cast h2
  refine ⟨hE, ?_, ?_⟩
  · unfold signedMin; omega
  · unfold signedMax; omega

/-- Fit at both attained ends ⇒ demand bound. -/
theorem exactDemand_le_of_fits {E : ℕ} (w W : ℕ) {k : ℕ} (r : Register k)
    (hhi : FitsSignedWidth E (exactRowHi w W r)) (hlo : FitsSignedWidth E (exactRowLo w W r)) :
    exactRowDemand w W r ≤ 2 ^ (E - 1) := by
  obtain ⟨-, -, h2⟩ := hhi
  obtain ⟨-, h1, -⟩ := hlo
  unfold signedMin at h1
  unfold signedMax at h2
  unfold exactRowDemand
  refine max_le ?_ ?_
  · have : (-exactRowLo w W r).toNat ≤ ((2 ^ (E - 1) : ℕ) : ℤ).toNat :=
      Int.toNat_le_toNat (by omega)
    simpa using this
  · have : (exactRowHi w W r + 1).toNat ≤ ((2 ^ (E - 1) : ℕ) : ℤ).toNat :=
      Int.toNat_le_toNat (by omega)
    simpa using this

/-! ## Maxima and the least exponent -/

theorem le_exactListMax : ∀ {l : List ℕ} {a : ℕ}, a ∈ l → a ≤ exactListMax l
  | [], _, h => by cases h
  | b :: l, a, h => by
      simp only [exactListMax]
      rcases List.mem_cons.mp h with rfl | h
      · exact le_max_left _ _
      · exact le_trans (le_exactListMax h) (le_max_right _ _)

theorem exactListMax_le {l : List ℕ} {B : ℕ} (h : ∀ a ∈ l, a ≤ B) : exactListMax l ≤ B := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a l ih =>
      simp only [exactListMax]
      exact max_le (h a List.mem_cons_self) (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem exactLeastExp_spec (D : ℕ) : ∀ (f e : ℕ), D ≤ 2 ^ (e + f) → (∀ e' < e, ¬ D ≤ 2 ^ e') →
    D ≤ 2 ^ exactLeastExp D f e ∧ ∀ e' < exactLeastExp D f e, ¬ D ≤ 2 ^ e'
  | 0, e, h, hm => ⟨by simpa [exactLeastExp] using h, hm⟩
  | f + 1, e, h, hm => by
      simp only [exactLeastExp]
      split
      · exact ⟨‹_›, hm⟩
      · rename_i hne
        refine exactLeastExp_spec D f (e + 1) (by rwa [show e + 1 + f = e + (f + 1) by omega]) ?_
        intro e' he'
        rcases Nat.lt_succ_iff_lt_or_eq.mp he' with h' | rfl
        · exact hm e' h'
        · exact hne

/-! ## The widths -/

theorem tightSignedWidth_spec {k : ℕ} (ops : Prog k) (xw zw : ℕ) :
    exactDemand ops xw zw ≤ 2 ^ (tightSignedWidthOfWidths ops xw zw - 1) ∧
      ∀ e < tightSignedWidthOfWidths ops xw zw - 1, ¬ exactDemand ops xw zw ≤ 2 ^ e := by
  have h := exactLeastExp_spec (exactDemand ops xw zw) (exactDemand ops xw zw) 0
    (by simpa using Nat.lt_two_pow_self.le) (fun _ h => absurd h (Nat.not_lt_zero _))
  simpa [tightSignedWidthOfWidths] using h

theorem tightSignedWidth_pos {k : ℕ} (ops : Prog k) (xw zw : ℕ) :
    0 < tightSignedWidthOfWidths ops xw zw := by
  unfold tightSignedWidthOfWidths; omega

theorem floorSignedWidth_pos (k xw zw : ℕ) : 0 < floorSignedWidthOfWidths k xw zw := by
  unfold floorSignedWidthOfWidths commonNeededWidth; omega

theorem exactSignedWidth_pos {k : ℕ} (ops : Prog k) (xw zw : ℕ) :
    0 < exactSignedWidthOfWidths ops xw zw :=
  lt_of_lt_of_le (tightSignedWidth_pos ops xw zw) (le_max_left _ _)

theorem tight_le_exactSignedWidth {k : ℕ} (ops : Prog k) (xw zw : ℕ) :
    tightSignedWidthOfWidths ops xw zw ≤ exactSignedWidthOfWidths ops xw zw := le_max_left _ _

/-- The demand of a reachable row is at most `2^(E-1)` at the tight width. -/
theorem exactRowDemand_le_tight {k : ℕ} {ops : Prog k} {xw zw : ℕ} {r : Register k}
    (hr : r ∈ exactReachRows ops) :
    exactRowDemand xw (exactLimbWidth k xw zw) r ≤ 2 ^ (tightSignedWidthOfWidths ops xw zw - 1) ∧
    exactRowDemand zw (exactLimbWidth k xw zw) r ≤ 2 ^ (tightSignedWidthOfWidths ops xw zw - 1) := by
  have hmem : max (exactRowDemand xw (exactLimbWidth k xw zw) r)
      (exactRowDemand zw (exactLimbWidth k xw zw) r) ≤ exactDemand ops xw zw :=
    le_exactListMax (List.mem_map.mpr ⟨r, hr, rfl⟩)
  have hD := (tightSignedWidth_spec ops xw zw).1
  exact ⟨le_trans (le_trans (le_max_left _ _) hmem) hD,
    le_trans (le_trans (le_max_right _ _) hmem) hD⟩

/-- `commonNeededWidth` of the uniform record is the exact width (`0 < k`). -/
theorem commonNeededWidth_exactNeeded {k : ℕ} (hk : 0 < k) (ops : Prog k) (xw zw : ℕ) :
    commonNeededWidth (exactNeededWidths ops xw zw) = exactSignedWidthOfWidths ops xw zw := by
  unfold commonNeededWidth exactNeededWidths
  have hne : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  simp only [max_self]
  rw [Finset.sup_const hne]
  have := exactSignedWidth_pos ops xw zw
  omega

end Shor
