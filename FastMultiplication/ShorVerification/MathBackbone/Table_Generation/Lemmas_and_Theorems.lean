import FastMultiplication.ShorVerification.MathBackbone.Table_Generation.Tactics

/-!
# Table-generation example theorems and state helpers

This file uses the tactics from `Tactics` to certify the running examples and
records a few state-update lemmas that are used by the synthesis proofs.
-/

/-! =========================================================
    Section 1: Example return and coverage theorems
========================================================= -/

open Operations

/-- Start state entry (usable by `simp`). -/
@[simp] lemma start_state_entry {k} (i j : Fin k) :
  State.start_state i j = (if j = i then 1 else 0) := by
  simp [State.start_state]


theorem example_prog_2_returns:
  run? example_prog_2 State.start_state = some State.start_state:=by {
    unfold example_prog_2 State.start_state
    simp [ run?_append,
         applyOp?,
         State.addScaledReg, State.negateReg, State.shiftLReg, State.shiftRReg?,
         State.setReg,
         Register.addScaled, Register.negate, Register.shiftL, Register.shiftR?]
    split_ifs with h
    simp
    funext j k
    have h2:=h j
    fin_cases j<;>fin_cases k<;>simp
    simp
    apply h
    intro j
    fin_cases j<;>simp
  }


theorem example_prog_2_phase_converage_2:
  phaseProduct_coverage_check example_prog_2 State.start_state [Point.int 0,Point.inf,Point.int 1,Point.int (-1),Point.int (-2)]:=by {
    unfold example_prog_2
    prove_coverage 3
  }



theorem example_prog_4_phase_coverage :
  phaseProduct_coverage_check example_prog_3 State.start_state [Point.int 0,Point.inf,Point.int 1,Point.int (-1)] := by
    unfold example_prog_3
    prove_coverage 4

theorem example_prog_2_returns_2:
  run? example_prog_2 State.start_state = some State.start_state:=by {
    unfold example_prog_2
    returns_to_original?
  }



open State

/-! =========================================================
    Section 2: State-update helper lemmas
========================================================= -/

/-- If `dst ≠ src`, `addScaledReg dst src ...` does not change register `src`. -/
lemma addScaledReg_src_unchanged
  {k : ℕ} (σ : State k) (dst src : Fin k) (negSrc : Bool) (sh : ℕ)
  (hds : dst ≠ src) :
  (σ.addScaledReg dst src negSrc sh) src = σ src := by
  unfold State.addScaledReg State.setReg
  simp;intro s;simp_all

/-- If `dst ≠ src`, `addScaledReg dst src ...` does not change register `src`. -/
lemma addScaledReg_nondst_unchanged
  {k : ℕ} (σ : State k) (dst src j : Fin k) (negSrc : Bool) (sh : ℕ) (hjs: j ≠ dst):
  (σ.addScaledReg dst src negSrc sh) j = σ j := by
  unfold State.addScaledReg State.setReg
  simp;intro s;simp_all
/-- If `i ≠ j`, then `setReg σ i r` leaves register `j` unchanged. -/
lemma setReg_ne
  {k : ℕ} (σ : State k) (i j : Fin k) (r : Register k) (h : j ≠ i) :
  (setReg σ i r) j = σ j := by
  unfold setReg
  simp [h]

/-- If `j = i`, then `setReg σ i r` sets register `j` to `r`. -/
lemma setReg_eq
  {k : ℕ} (σ : State k) (i : Fin k) (r : Register k) :
  (setReg σ i r) i = r := by
  unfold setReg
  simp

/-- A helper: `shiftLReg` changes only register `i`. -/
lemma shiftLReg_ne
  {k : ℕ} (σ : State k) (i j : Fin k) (n : ℕ) (h : j ≠ i) :
  (σ.shiftLReg i n) j = σ j := by
  unfold shiftLReg
  exact setReg_ne σ i j _ h

/-- A helper: `negateReg` changes only register `i`. -/
lemma negateReg_ne
  {k : ℕ} (σ : State k) (i j : Fin k) (h : j ≠ i) :
  (σ.negateReg i) j = σ j := by
  unfold negateReg
  exact setReg_ne σ i j _ h

lemma setReg_negateReg_pipeline_eq_addScaled
  {k : ℕ} (σ : State k) (dst src : Fin k) (sh : ℕ) (hds : dst ≠ src) :
  let σA : State k :=
    ((σ.negateReg src).shiftLReg src sh).addScaledReg dst src false 0
  (σA.setReg src ((σ.negateReg src) src)).negateReg src
    =
  σ.addScaledReg dst src true sh := by
  classical
  intro σA
  -- extensionality over registers and coefficients
  ext r j
  by_cases hr_src : r = src
  · subst hr_src
    unfold State.negateReg State.setReg State.addScaledReg
    simp [Register.negate, Register.addScaled, State.setReg];have:¬r=dst:=by intros a;simp_all
    simp[this]
  · by_cases hr_dst : r = dst
    · subst hr_dst
      unfold State.negateReg State.setReg at *
      have hdst_ne_src : (r : Fin k) ≠ src := hds
      simp [hdst_ne_src]
      unfold σA
      unfold State.addScaledReg State.shiftLReg State.negateReg State.setReg
      simp [hds, Register.addScaled, Register.shiftL, Register.negate, pow_zero, mul_left_comm, mul_comm]
    ·
      -- r is neither src nor dst: everything is unchanged on both sides
      unfold State.negateReg State.setReg State.addScaledReg
      simp [hr_src, hr_dst]
      unfold σA State.shiftLReg State.negateReg
      rw[addScaledReg_nondst_unchanged,setReg_ne,setReg_ne]
      simp[hr_src]
      simp[hr_src]
      simp[hr_dst]
