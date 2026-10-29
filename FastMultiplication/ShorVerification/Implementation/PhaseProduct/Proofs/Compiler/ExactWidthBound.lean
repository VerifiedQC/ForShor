import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.Support
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.WidthSoundness

/-!
# The exact width: least, and never above the scan

`Compiler/ExactWidth.lean` defines the exact working width (`WidthRule.exact`)
and `WidthSoundness.lean` proves the lowering's fit obligation from it
(`allocated_widths_sound_exact`). This file
proves the two facts that make it the *right* replacement for the scan:

* `tightSignedWidth_le_iff` — **least**: `tight ≤ E` iff `0 < E` and every row
  the program reaches fits signed `E` bits at every point of both operands'
  limb boxes. (`→` is interval soundness; `←` uses the box corners where each
  row attains its least and greatest value.) `exactSignedWidth_le_iff` is the
  same for the compiler's width `max tight floor`, with `floor ≤ E` added: the
  least width that grows every slot and holds every reachable value.
* `nextSignedWidthBy_exact_le_scan` — the exact width never exceeds the scan
  (`nextSignedWidth`). Its proof replays the scan's own invariant
  (`WidthSoundness.lean`'s step lemma) on plain integers over the box.

What "every point of the box" covers: `WidthSoundness.lean`'s
`sourceChunkXInt_box` shows every chunk reading the lowering performs lies in
the box. The converse (every box point is the reading of some basis state)
is not proved here; minimality is therefore minimality over the box, which is
the ForShor chunk value range by construction (`[0, 2^W)` lower chunks,
two's-complement top chunk).
-/

namespace Shor
open Operations
open scoped BigOperators

/-! ## Row values -/

section RowVal

variable {k : ℕ}

theorem rowVal_shiftL (r : Register k) (m : ℕ) (L : Fin k → ℤ) :
    rowVal (Register.shiftL r m) L = 2 ^ m * rowVal r L := by
  simp only [rowVal, Register.shiftL, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem rowVal_negate (r : Register k) (L : Fin k → ℤ) :
    rowVal (Register.negate r) L = -rowVal r L := by
  simp only [rowVal, Register.negate, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem rowVal_addScaled (d s : Register k) (ng : Bool) (sh : ℕ) (L : Fin k → ℤ) :
    rowVal (Register.addScaled d s ng sh) L
      = rowVal d L + (if ng then (-1 : ℤ) else 1) * 2 ^ sh * rowVal s L := by
  simp only [rowVal, Register.addScaled, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem rowVal_shiftR {r r' : Register k} {m : ℕ} (h : Register.shiftR? r m = some r')
    (L : Fin k → ℤ) : rowVal r L = 2 ^ m * rowVal r' L := by
  unfold Register.shiftR? at h
  dsimp only at h
  split at h
  · rename_i hall
    cases h
    simp only [rowVal, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : r j = 2 ^ m * (r j / 2 ^ m) :=
      (Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero (hall j))).symm
    rw [← mul_assoc, ← this]
  · cases h

theorem rowVal_start (i : Fin k) (L : Fin k → ℤ) :
    rowVal (State.start_state i) L = L i := by
  simp [rowVal, State.start_state]

end RowVal

/-! ## The scan's invariant on integers -/

section Fold

variable {k : ℕ}

/-- One side of `updateWidthState`. -/
def updW (w : Fin k → ℕ) : valid_ops k → Fin k → ℕ
  | .shiftL i n => Function.update w i (w i + n)
  | .shiftR i n => Function.update w i (w i - n)
  | .negate i => Function.update w i (w i + 1)
  | .addScaled d s _ sh => Function.update w d (1 + max (w d) (w s + sh))
  | .phaseProduct _ => w

theorem updateWidthState_xw (cur : WidthState k) (op : valid_ops k) :
    (updateWidthState cur op).xw = updW cur.xw op := by cases op <;> rfl

theorem updateWidthState_zw (cur : WidthState k) (op : valid_ops k) :
    (updateWidthState cur op).zw = updW cur.zw op := by cases op <;> rfl

theorem foldl_updateWidthState_xw :
    ∀ (ops : Prog k) (cur : WidthState k),
      (ops.foldl updateWidthState cur).xw = ops.foldl updW cur.xw
  | [], _ => rfl
  | op :: ops, cur => by
      simp only [List.foldl_cons]
      rw [foldl_updateWidthState_xw ops, updateWidthState_xw]

theorem foldl_updateWidthState_zw :
    ∀ (ops : Prog k) (cur : WidthState k),
      (ops.foldl updateWidthState cur).zw = ops.foldl updW cur.zw
  | [], _ => rfl
  | op :: ops, cur => by
      simp only [List.foldl_cons]
      rw [foldl_updateWidthState_zw ops, updateWidthState_zw]

/-- Every register's value fits one sign bit beyond its scanned width. -/
def SideFits (w : Fin k → ℕ) (σ : State k) (L : Fin k → ℤ) : Prop :=
  ∀ i, FitsSignedWidth (w i + 1) (rowVal (σ i) L)

theorem sideFits_step {w : Fin k → ℕ} {σ σ' : State k} {op : valid_ops k}
    {L : Fin k → ℤ} (hstep : applyOp? σ op = some σ') (h : SideFits w σ L) :
    SideFits (updW w op) σ' L := by
  intro j
  cases op with
  | shiftL i m =>
      simp only [applyOp?, Option.some.injEq] at hstep; subst hstep
      by_cases hji : j = i
      · subst hji
        simp only [updW, Function.update_self, State.shiftLReg, State.setReg, ↓reduceIte,
          rowVal_shiftL]
        exact FitsSignedWidth_shiftL_raw (h j)
      · simpa [updW, Function.update_of_ne hji, State.shiftLReg, State.setReg, hji] using h j
  | shiftR i m =>
      simp only [applyOp?, State.shiftRReg?] at hstep
      cases hr : Register.shiftR? (σ i) m with
      | none => rw [hr] at hstep; cases hstep
      | some r' =>
          rw [hr] at hstep
          simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
            Option.some.injEq] at hstep
          subst hstep
          by_cases hji : j = i
          · subst hji
            simp only [updW, Function.update_self, State.setReg, ↓reduceIte]
            exact FitsSignedWidth_shiftR_of_mul (h j) (rowVal_shiftR hr L)
          · simpa [updW, Function.update_of_ne hji, State.setReg, hji] using h j
  | negate i =>
      simp only [applyOp?, Option.some.injEq] at hstep; subst hstep
      by_cases hji : j = i
      · subst hji
        simp only [updW, Function.update_self, State.negateReg, State.setReg, ↓reduceIte,
          rowVal_negate]
        have := FitsSignedWidth_neg_widen (h j)
        simpa [Nat.add_assoc] using this
      · simpa [updW, Function.update_of_ne hji, State.negateReg, State.setReg, hji] using h j
  | addScaled d s ng sh =>
      simp only [applyOp?, Option.some.injEq] at hstep; subst hstep
      by_cases hjd : j = d
      · subst hjd
        simp only [updW, Function.update_self, State.addScaledReg, State.setReg, ↓reduceIte,
          rowVal_addScaled]
        have := FitsSignedWidth_addScaled_widen (sh := sh) ng (h j) (h s)
        have he : 1 + max (w j) (w s + sh) + 1 = max (w j) (w s + sh) + 2 := by omega
        rw [he]; exact this
      · simpa [updW, Function.update_of_ne hjd, State.addScaledReg, State.setReg, hjd] using h j
  | phaseProduct i =>
      simp only [applyOp?, Option.some.injEq] at hstep; subst hstep
      exact h j

theorem sideFits_run {L : Fin k → ℤ} :
    ∀ (ops : Prog k) (w : Fin k → ℕ) (σ σ' : State k),
      run? ops σ = some σ' → SideFits w σ L → SideFits (ops.foldl updW w) σ' L
  | [], w, σ, σ', hrun, h => by
      simp only [run?, Option.some.injEq] at hrun; subst hrun; exact h
  | op :: ops, w, σ, σ', hrun, h => by
      simp only [run?] at hrun
      cases hs : applyOp? σ op with
      | none => rw [hs] at hrun; cases hrun
      | some σ1 =>
          rw [hs] at hrun
          exact sideFits_run ops _ σ1 σ' hrun (sideFits_step hs h)

/-- A box point fits one bit beyond its chunk's logical width. -/
theorem sideFits_start {w W : ℕ} {L : Fin k → ℤ} (hL : InExactBox w W L) :
    SideFits (fun i => phaseSplitLogicalWidth w W k i) State.start_state L := by
  intro i
  rw [rowVal_start]
  obtain ⟨hlo, hhi⟩ := hL i
  unfold exactLimbLo at hlo
  unfold exactLimbHi at hhi
  unfold FitsSignedWidth signedMin signedMax
  set t := phaseSplitLogicalWidth w W k i
  by_cases htop : isTopChunk i
  · simp only [htop, ite_true] at hlo hhi
    by_cases ht : t = 0
    · simp only [ht, ite_true] at hlo hhi
      have h2 : ((2 ^ (t + 1 - 1) : ℕ) : ℤ) = 1 := by rw [ht]; simp
      refine ⟨by omega, ?_, ?_⟩ <;> rw [h2] <;> omega
    · simp only [ht, ite_false] at hlo hhi
      have h2 : ((2 ^ (t + 1 - 1) : ℕ) : ℤ) = 2 * (2 : ℤ) ^ (t - 1) := by
        rw [show t + 1 - 1 = (t - 1) + 1 by omega]; push_cast; ring
      have hp : (0 : ℤ) < (2 : ℤ) ^ (t - 1) := by positivity
      refine ⟨by omega, ?_, ?_⟩ <;> rw [h2] <;> omega
  · simp only [htop, ite_false] at hlo hhi
    have h2 : ((2 ^ (t + 1 - 1) : ℕ) : ℤ) = (2 : ℤ) ^ t := by simp
    refine ⟨by omega, ?_, ?_⟩ <;> rw [h2] <;> omega

end Fold

/-! ## Least -/

section Least

variable {k : ℕ}

/-- Every reachable row fits signed `E` bits on both operands' boxes. -/
def ExactFits (ops : Prog k) (xw zw E : ℕ) : Prop :=
  ∀ r ∈ exactReachRows ops,
    (∀ L, InExactBox xw (exactLimbWidth k xw zw) L → FitsSignedWidth E (rowVal r L)) ∧
    (∀ L, InExactBox zw (exactLimbWidth k xw zw) L → FitsSignedWidth E (rowVal r L))

theorem exactFits_mono {ops : Prog k} {xw zw E E' : ℕ} (hE : E ≤ E') (h : ExactFits ops xw zw E) :
    ExactFits ops xw zw E' := fun r hr =>
  ⟨fun L hL => FitsSignedWidth_mono hE ((h r hr).1 L hL),
    fun L hL => FitsSignedWidth_mono hE ((h r hr).2 L hL)⟩

theorem exactFits_tight (ops : Prog k) (xw zw : ℕ) :
    ExactFits ops xw zw (tightSignedWidthOfWidths ops xw zw) := fun r hr => by
  obtain ⟨hdx, hdz⟩ := exactRowDemand_le_tight (xw := xw) (zw := zw) hr
  refine ⟨fun L hL => ?_, fun L hL => ?_⟩
  · obtain ⟨hlo, hhi⟩ := exact_row_bounds _ _ r hL
    exact fits_of_exactDemand (tightSignedWidth_pos ops xw zw) hlo hhi hdx
  · obtain ⟨hlo, hhi⟩ := exact_row_bounds _ _ r hL
    exact fits_of_exactDemand (tightSignedWidth_pos ops xw zw) hlo hhi hdz

theorem tight_le_of_exactFits {ops : Prog k} {xw zw E : ℕ} (hE : 0 < E)
    (h : ExactFits ops xw zw E) : tightSignedWidthOfWidths ops xw zw ≤ E := by
  have hD : exactDemand ops xw zw ≤ 2 ^ (E - 1) := by
    unfold exactDemand
    refine exactListMax_le fun a ha => ?_
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
    obtain ⟨hx, hz⟩ := h r hr
    refine max_le ?_ ?_
    · exact exactDemand_le_of_fits _ _ r
        (by rw [← exact_rowHi_attained]; exact hx _ (exactCornerHi_box _ _ r))
        (by rw [← exact_rowLo_attained]; exact hx _ (exactCornerLo_box _ _ r))
    · exact exactDemand_le_of_fits _ _ r
        (by rw [← exact_rowHi_attained]; exact hz _ (exactCornerHi_box _ _ r))
        (by rw [← exact_rowLo_attained]; exact hz _ (exactCornerLo_box _ _ r))
  have hmin := (tightSignedWidth_spec ops xw zw).2
  by_contra hlt
  exact hmin (E - 1) (by omega) hD

/-- **The tight width is least**: `tight ≤ E` iff every reachable row fits
signed `E` bits at every point of both operands' limb boxes. -/
theorem tightSignedWidth_le_iff (ops : Prog k) (xw zw E : ℕ) :
    tightSignedWidthOfWidths ops xw zw ≤ E ↔ 0 < E ∧ ExactFits ops xw zw E :=
  ⟨fun h => ⟨lt_of_lt_of_le (tightSignedWidth_pos ops xw zw) h,
      exactFits_mono h (exactFits_tight ops xw zw)⟩,
    fun ⟨hE, h⟩ => tight_le_of_exactFits hE h⟩

/-- **The compiler's width is least** among widths that grow every slot
(`floor ≤ E`) and hold every reachable value. -/
theorem exactSignedWidth_le_iff (ops : Prog k) (xw zw E : ℕ) :
    exactSignedWidthOfWidths ops xw zw ≤ E ↔
      floorSignedWidthOfWidths k xw zw ≤ E ∧ ExactFits ops xw zw E := by
  unfold exactSignedWidthOfWidths
  rw [max_le_iff, tightSignedWidth_le_iff]
  constructor
  · rintro ⟨⟨_, h⟩, hf⟩; exact ⟨hf, h⟩
  · rintro ⟨hf, h⟩; exact ⟨⟨lt_of_lt_of_le (floorSignedWidth_pos k xw zw) hf, h⟩, hf⟩

end Least

/-! ## Never above the scan -/

/-- The original scan holds every reachable value on the box (the scan's own
invariant, replayed on integers). -/
theorem exactFits_scan {k : ℕ} (x z : ExtReg) (ops : Prog k) :
    ExactFits ops x.width z.width (nextSignedWidth x z ops) := by
  intro r hr
  obtain ⟨pre, rest, σ, i, hops, hrun, rfl⟩ := exists_of_mem_exactReachRows hr
  refine ⟨fun L hL => ?_, fun L hL => ?_⟩
  · have h0 : SideFits (initWidthState x z k).xw State.start_state L := sideFits_start hL
    have h1 := sideFits_run pre _ _ _ hrun h0 i
    rw [← foldl_updateWidthState_xw] at h1
    have hpre := prefix_foldl_updateWidthState_x_le_scanNeeded (x := x) (z := z) ops pre rest i hops
    have hc := commonNeededWidth_ge_xneed (scanNeededWidths x z ops) i
    exact FitsSignedWidth_mono (by unfold nextSignedWidth; omega) h1
  · have h0 : SideFits (initWidthState x z k).zw State.start_state L := sideFits_start hL
    have h1 := sideFits_run pre _ _ _ hrun h0 i
    rw [← foldl_updateWidthState_zw] at h1
    have hpre := prefix_foldl_updateWidthState_z_le_scanNeeded (x := x) (z := z) ops pre rest i hops
    have hc := commonNeededWidth_ge_zneed (scanNeededWidths x z ops) i
    exact FitsSignedWidth_mono (by unfold nextSignedWidth; omega) h1

/-- The floor never exceeds the scan. -/
theorem floor_le_scan {k : ℕ} (x z : ExtReg) (ops : Prog k) :
    floorSignedWidthOfWidths k x.width z.width ≤ nextSignedWidth x z ops := by
  unfold floorSignedWidthOfWidths nextSignedWidth commonNeededWidth
  have : Finset.univ.sup (fun i : Fin k =>
        max ((exactInitNeed k x.width z.width).xneed i) ((exactInitNeed k x.width z.width).zneed i))
      ≤ Finset.univ.sup (fun i : Fin k =>
        max ((scanNeededWidths x z ops).xneed i) ((scanNeededWidths x z ops).zneed i)) :=
    Finset.sup_mono_fun fun i _ =>
      max_le_max (scanNeededWidths_x_ge_init x z ops i) (scanNeededWidths_z_ge_init x z ops i)
  omega

/-- **The exact width never exceeds the original scan.** -/
theorem exactSignedWidth_le_scan {k : ℕ} (x z : ExtReg) (ops : Prog k) :
    exactSignedWidthOfWidths ops x.width z.width ≤ nextSignedWidth x z ops :=
  (exactSignedWidth_le_iff ops x.width z.width _).mpr ⟨floor_le_scan x z ops, exactFits_scan x z ops⟩

/-- **The exact child width never exceeds the scan's** (`0 < k`). -/
theorem nextSignedWidthBy_exact_le_scan {k : ℕ} (hk : 0 < k) (x z : ExtReg) (ops : Prog k) :
    nextSignedWidthBy .exact x z ops ≤ nextSignedWidth x z ops := by
  rw [nextSignedWidthBy_exact hk]
  exact exactSignedWidth_le_scan x z ops

/-- Under either rule the child width is at most the scan's (`0 < k`). -/
theorem nextSignedWidthBy_le_scan (R : WidthRule) {k : ℕ} (hk : 0 < k) (x z : ExtReg)
    (ops : Prog k) : nextSignedWidthBy R x z ops ≤ nextSignedWidth x z ops := by
  cases R
  · exact le_rfl
  · exact nextSignedWidthBy_exact_le_scan hk x z ops

end Shor
