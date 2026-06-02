import FastMultiplication.ShorVerification.AlgorithmCorrectness.PhaseProduct.AllocationCorrectness

namespace Shor
open Gate
open Operations
open scoped BigOperators

/-!
# Phase-Product Body Correctness

This file handles the compiled annotated operation list after allocation.  It
shows one-step encoded-state preservation, then lifts that to phase blocks and
the final deallocation step.
-/

/-! =========================================================
    Section: One-step encoded-state preservation
========================================================= -/

/-- These lemmas prove correctness of a single compiled annotated operation on a
basis state, assuming the next symbolic state already fits the target layout
widths. -/
lemma encodesFrom_after_shiftL_ket
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ} (hk : 1 < k)
  (phi : ℝ)
  (coeff : Fin (q k) → ℚ)
  (src dst : LayoutState k)
  (hdisj : LayoutSlotsDisjoint dst)
  (i : Fin k) (m : ℕ)
  (σ σ1 : State k)
  (bRef bCur : qs.Basis)
  (hstep : applyOp? σ (.shiftL i m) = some σ1)
  (hEnc : EncodesStateFromFits (qs := qs) src dst σ bRef bCur)
  (hFit1x : ∀ j : Fin k,
    FitsSignedWidth (ExtReg.width (dst.xslot j))
      (evalRowX (qs := qs) src (σ1 j) bRef))
  (hFit1z : ∀ j : Fin k,
    FitsSignedWidth (ExtReg.width (dst.zslot j))
      (evalRowZ (qs := qs) src (σ1 j) bRef)) :
  ∃ b1 : qs.Basis,
    qs.eval
        (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst
          [{ op := .shiftL i m, phaseTerm? := none }])
        (qs.ket bCur)
      =
    qs.ket b1 ∧
    EncodesStateFromFits (qs := qs) src dst σ1 bRef b1 := by
  rcases hdisj with ⟨hxx, hzz, hxz⟩

  have disjoint_symm {a b : Reg} : Disjoint a b → Disjoint b a := by
    intro h
    cases h with
    | inl hab => exact Or.inr hab
    | inr hba => exact Or.inl hba

  have hσ1 : σ1 = State.shiftLReg σ i m := by
    simp [applyOp?] at hstep
    simpa using hstep.symm
  subst hσ1

  have hrow_shift_x :
      evalRowX (qs := qs) src ((σ i).shiftL m) bRef
        =
      ((2 : ℤ)^m) * evalRowX (qs := qs) src (σ i) bRef := by
    simpa using
      (evalRowX_shiftL_raw
        (qs := qs) (src := src) (r := σ i) (m := m) (b := bRef))

  have hfit_shift_x :
      FitsSignedWidth (ExtReg.width (dst.xslot i))
        (((2 : ℤ)^m) * ExtRegEncoding.extToInt (dst.xslot i) bCur) := by
    have hfit_post :
        FitsSignedWidth (ExtReg.width (dst.xslot i))
          (((2 : ℤ)^m) * evalRowX (qs := qs) src (σ i) bRef) := by
      simpa [State.shiftLReg, hrow_shift_x] using hFit1x i
    rw [hEnc.1.1 i]
    exact hfit_post

  rcases ArithmeticSemantics.eval_ShiftL_ket_exact
      (qs := qs) (r := dst.xslot i) (n := m) (b := bCur) hfit_shift_x with
    ⟨bx, hbx_eval, hbx_val, hbx_keep⟩

  have hz_same_on_bx :
      ExtRegEncoding.extToInt (dst.zslot i) bx
        = ExtRegEncoding.extToInt (dst.zslot i) bCur := by
    exact hbx_keep (dst.zslot i) (disjoint_symm (hxz i i))

  have hrow_shift_z :
      evalRowZ (qs := qs) src ((σ i).shiftL m) bRef
        =
      ((2 : ℤ)^m) * evalRowZ (qs := qs) src (σ i) bRef := by
    simpa using
      (evalRowZ_shiftL_raw
        (qs := qs) (src := src) (r := σ i) (m := m) (b := bRef))

  have hfit_shift_z :
      FitsSignedWidth (ExtReg.width (dst.zslot i))
        (((2 : ℤ)^m) * ExtRegEncoding.extToInt (dst.zslot i) bx) := by
    have hfit_post :
        FitsSignedWidth (ExtReg.width (dst.zslot i))
          (((2 : ℤ)^m) * evalRowZ (qs := qs) src (σ i) bRef) := by
      simpa [State.shiftLReg, hrow_shift_z] using hFit1z i
    rw [hz_same_on_bx, hEnc.1.2 i]
    exact hfit_post

  rcases ArithmeticSemantics.eval_ShiftL_ket_exact
      (qs := qs) (r := dst.zslot i) (n := m) (b := bx) hfit_shift_z with
    ⟨bz, hbz_eval, hbz_val, hbz_keep⟩

  refine ⟨bz, ?_, ?_⟩
  · simp [compileAnnotatedOpsToSignedGateAux, qs.eval_seq, hbx_eval, hbz_eval, qs.eval_id]
  ·
    refine ⟨?_, hFit1x, hFit1z⟩
    constructor
    · intro j
      by_cases hji : i = j
      · subst hji
        calc
          ExtRegEncoding.extToInt (dst.xslot i) bz
              = ExtRegEncoding.extToInt (dst.xslot i) bx := by
                  exact hbz_keep (dst.xslot i) (hxz i i)
          _   = ((2 : ℤ)^m) * ExtRegEncoding.extToInt (dst.xslot i) bCur := by
                  simpa using hbx_val
          _   = ((2 : ℤ)^m) * evalRowX (qs := qs) src (σ i) bRef := by
                  rw [hEnc.1.1 i]
          _   = evalRowX (qs := qs) src ((State.shiftLReg σ i m) i) bRef := by
                  symm
                  simpa [State.shiftLReg] using hrow_shift_x
      ·
        have hkeep1 :
            ExtRegEncoding.extToInt (dst.xslot j) bx
              = ExtRegEncoding.extToInt (dst.xslot j) bCur := by
          exact hbx_keep (dst.xslot j)
            (hxx j i (by simpa [eq_comm] using hji))
        have hkeep2 :
            ExtRegEncoding.extToInt (dst.xslot j) bz
              = ExtRegEncoding.extToInt (dst.xslot j) bx := by
          exact hbz_keep (dst.xslot j) (hxz j i)
        have hji' : j ≠ i := by
          intro h
          exact hji h.symm
        calc
          ExtRegEncoding.extToInt (dst.xslot j) bz
              = ExtRegEncoding.extToInt (dst.xslot j) bx := hkeep2
          _   = ExtRegEncoding.extToInt (dst.xslot j) bCur := hkeep1
          _   = evalRowX (qs := qs) src (σ j) bRef := by
                  simpa [EncodesStateFrom] using hEnc.1.1 j
          _   = evalRowX (qs := qs) src ((State.shiftLReg σ i m) j) bRef := by
                  simp [State.shiftLReg, State.setReg, hji']
    · intro j
      by_cases hji : i = j
      · subst hji
        calc
          ExtRegEncoding.extToInt (dst.zslot i) bz
              = ((2 : ℤ)^m) * ExtRegEncoding.extToInt (dst.zslot i) bx := by
                    simpa using hbz_val
          _   = ((2 : ℤ)^m) * ExtRegEncoding.extToInt (dst.zslot i) bCur := by
                    rw [hz_same_on_bx]
          _   = ((2 : ℤ)^m) * evalRowZ (qs := qs) src (σ i) bRef := by
                    rw [hEnc.1.2 i]
          _   = evalRowZ (qs := qs) src ((State.shiftLReg σ i m) i) bRef := by
                    symm
                    simpa [State.shiftLReg] using hrow_shift_z
      ·
        have hkeep1 :
            ExtRegEncoding.extToInt (dst.zslot j) bx
              = ExtRegEncoding.extToInt (dst.zslot j) bCur := by
          exact hbx_keep (dst.zslot j)
            (disjoint_symm (hxz i j))
        have hkeep2 :
            ExtRegEncoding.extToInt (dst.zslot j) bz
              = ExtRegEncoding.extToInt (dst.zslot j) bx := by
          exact hbz_keep (dst.zslot j)
            (hzz j i (by simpa [eq_comm] using hji))
        have hji' : j ≠ i := by
          intro h
          exact hji h.symm
        calc
          ExtRegEncoding.extToInt (dst.zslot j) bz
              = ExtRegEncoding.extToInt (dst.zslot j) bx := hkeep2
          _   = ExtRegEncoding.extToInt (dst.zslot j) bCur := hkeep1
          _   = evalRowZ (qs := qs) src (σ j) bRef := by
                  simpa [EncodesStateFrom] using hEnc.1.2 j
          _   = evalRowZ (qs := qs) src ((State.shiftLReg σ i m) j) bRef := by
                  simp [State.shiftLReg, State.setReg, hji']

lemma encodesFrom_after_shiftR_ket
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ} (hk : 1 < k)
  (phi : ℝ)
  (coeff : Fin (q k) → ℚ)
  (src dst : LayoutState k)
  (hdisj : LayoutSlotsDisjoint dst)
  (i : Fin k) (m : ℕ)
  (σ σ1 : State k)
  (bRef bCur : qs.Basis)
  (hstep : applyOp? σ (.shiftR i m)  = some σ1)
  (hEnc : EncodesStateFromFits (qs := qs) src dst σ bRef bCur)
  (hFit1x : ∀ j : Fin k,
    FitsSignedWidth (ExtReg.width (dst.xslot j))
      (evalRowX (qs := qs) src (σ1 j) bRef))
  (hFit1z : ∀ j : Fin k,
    FitsSignedWidth (ExtReg.width (dst.zslot j))
      (evalRowZ (qs := qs) src (σ1 j) bRef)) :
  ∃ b1 : qs.Basis,
    qs.eval
        (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst
          [{ op := .shiftR i m, phaseTerm? := none }])
        (qs.ket bCur)
      =
    qs.ket b1
    ∧
    EncodesStateFromFits (qs := qs) src dst σ1 bRef b1 := by
  rcases hdisj with ⟨hxx, hzz, hxz⟩

  have disjoint_symm {a b : Reg} : Disjoint a b → Disjoint b a := by
    intro h
    cases h with
    | inl hab => exact Or.inr hab
    | inr hba => exact Or.inl hba

  cases hreg : Register.shiftR? (σ i) m with
  | none =>
      have : False := by
        simp [applyOp?, State.shiftRReg?, hreg] at hstep
      exact False.elim this
  | some r' =>
      have hσ1 : State.setReg σ i r' = σ1 := by
        simpa [applyOp?, State.shiftRReg?, hreg] using hstep
      subst hσ1

      have hx_pre :
          ExtRegEncoding.extToInt (dst.xslot i) bCur
            =
          ((2 : ℤ)^m) * evalRowX (qs := qs) src r' bRef := by
        calc
          ExtRegEncoding.extToInt (dst.xslot i) bCur
              = evalRowX (qs := qs) src (σ i) bRef := by
                  simpa [EncodesStateFrom] using hEnc.1.1 i
          _   = ((2 : ℤ)^m) * evalRowX (qs := qs) src r' bRef := by
                  simpa using
                    (evalRowX_shiftR_exact
                      (qs := qs) (src := src) (r := σ i) (r' := r')
                      (m := m) (b := bRef) hreg)

      rcases ArithmeticSemantics.eval_ShiftR_ket_exact
          (qs := qs) (r := dst.xslot i) (n := m) (b := bCur)
          (q := evalRowX (qs := qs) src r' bRef)
          hx_pre
          (by simpa [State.setReg] using hFit1x i) with
        ⟨bx, hbx_eval, hbx_val, hbx_keep⟩

      have hz_pre :
          ExtRegEncoding.extToInt (dst.zslot i) bx
            =
          ((2 : ℤ)^m) * evalRowZ (qs := qs) src r' bRef := by
        calc
          ExtRegEncoding.extToInt (dst.zslot i) bx
              = ExtRegEncoding.extToInt (dst.zslot i) bCur := by
                  exact hbx_keep (dst.zslot i) (disjoint_symm (hxz i i))
          _   = evalRowZ (qs := qs) src (σ i) bRef := by
                  simpa [EncodesStateFrom] using hEnc.1.2 i
          _   = ((2 : ℤ)^m) * evalRowZ (qs := qs) src r' bRef := by
                  simpa using
                    (evalRowZ_shiftR_exact
                      (qs := qs) (src := src) (r := σ i) (r' := r')
                      (m := m) (b := bRef) hreg)

      rcases ArithmeticSemantics.eval_ShiftR_ket_exact
          (qs := qs) (r := dst.zslot i) (n := m) (b := bx)
          (q := evalRowZ (qs := qs) src r' bRef)
          hz_pre
          (by simpa [State.setReg] using hFit1z i) with
        ⟨bz, hbz_eval, hbz_val, hbz_keep⟩

      refine ⟨bz, ?_, ?_⟩
      ·
        simp [compileAnnotatedOpsToSignedGateAux, qs.eval_seq, hbx_eval, hbz_eval, qs.eval_id]
      ·
        refine ⟨?_, hFit1x, hFit1z⟩
        constructor
        · intro j
          by_cases hji : i = j
          · subst hji
            calc
              ExtRegEncoding.extToInt (dst.xslot i) bz
                  = ExtRegEncoding.extToInt (dst.xslot i) bx := by
                      exact hbz_keep (dst.xslot i) (hxz i i)
              _   = evalRowX (qs := qs) src r' bRef := hbx_val
              _   = evalRowX (qs := qs) src ((State.setReg σ i r') i) bRef := by
                      simp [State.setReg]
          ·
            have hji' : j ≠ i := by
              intro h
              exact hji h.symm
            have hkeep1 :
                ExtRegEncoding.extToInt (dst.xslot j) bx
                  = ExtRegEncoding.extToInt (dst.xslot j) bCur := by
              exact hbx_keep (dst.xslot j)
                (hxx j i (by simpa [eq_comm] using hji))
            have hkeep2 :
                ExtRegEncoding.extToInt (dst.xslot j) bz
                  = ExtRegEncoding.extToInt (dst.xslot j) bx := by
              exact hbz_keep (dst.xslot j) (hxz j i)
            calc
              ExtRegEncoding.extToInt (dst.xslot j) bz
                  = ExtRegEncoding.extToInt (dst.xslot j) bx := hkeep2
              _   = ExtRegEncoding.extToInt (dst.xslot j) bCur := hkeep1
              _   = evalRowX (qs := qs) src (σ j) bRef := by
                      simpa [EncodesStateFrom] using hEnc.1.1 j
              _   = evalRowX (qs := qs) src ((State.setReg σ i r') j) bRef := by
                      simp [State.setReg, hji']

        · intro j
          by_cases hji : i = j
          · subst hji
            calc
              ExtRegEncoding.extToInt (dst.zslot i) bz
                  = evalRowZ (qs := qs) src r' bRef := hbz_val
              _   = evalRowZ (qs := qs) src ((State.setReg σ i r') i) bRef := by
                      simp [State.setReg]
          ·
            have hji' : j ≠ i := by
              intro h
              exact hji h.symm
            have hkeep1 :
                ExtRegEncoding.extToInt (dst.zslot j) bx
                  = ExtRegEncoding.extToInt (dst.zslot j) bCur := by
              exact hbx_keep (dst.zslot j)
                (disjoint_symm (hxz i j))
            have hkeep2 :
                ExtRegEncoding.extToInt (dst.zslot j) bz
                  = ExtRegEncoding.extToInt (dst.zslot j) bx := by
              exact hbz_keep (dst.zslot j)
                (hzz j i (by simpa [eq_comm] using hji))
            calc
              ExtRegEncoding.extToInt (dst.zslot j) bz
                  = ExtRegEncoding.extToInt (dst.zslot j) bx := hkeep2
              _   = ExtRegEncoding.extToInt (dst.zslot j) bCur := hkeep1
              _   = evalRowZ (qs := qs) src (σ j) bRef := by
                      simpa [EncodesStateFrom] using hEnc.1.2 j
              _   = evalRowZ (qs := qs) src ((State.setReg σ i r') j) bRef := by
                      simp [State.setReg, hji']

lemma encodesFrom_after_negate_ket
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ} (hk : 1 < k)
  (phi : ℝ)
  (coeff : Fin (q k) → ℚ)
  (src dst : LayoutState k)
  (hdisj : LayoutSlotsDisjoint dst)
  (i : Fin k)
  (σ σ1 : State k)
  (bRef bCur : qs.Basis)
  (hstep : applyOp? σ (.negate i) = some σ1)
  (hEnc : EncodesStateFromFits (qs := qs) src dst σ bRef bCur)
  (hFit1x : ∀ j : Fin k,
    FitsSignedWidth (ExtReg.width (dst.xslot j))
      (evalRowX (qs := qs) src (σ1 j) bRef))
  (hFit1z : ∀ j : Fin k,
    FitsSignedWidth (ExtReg.width (dst.zslot j))
      (evalRowZ (qs := qs) src (σ1 j) bRef)) :
  ∃ b1 : qs.Basis,
    qs.eval
        (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst
          [{ op := .negate i, phaseTerm? := none }])
        (qs.ket bCur)
      =
    qs.ket b1
    ∧
    EncodesStateFromFits (qs := qs) src dst σ1 bRef b1 := by
  rcases hdisj with ⟨hxx, hzz, hxz⟩

  have disjoint_symm {a b : Reg} : Disjoint a b → Disjoint b a := by
    intro h
    cases h with
    | inl hab => exact Or.inr hab
    | inr hba => exact Or.inl hba

  rcases ArithmeticSemantics.eval_Negate_ket_mod
      (qs := qs) (r := dst.xslot i) (b := bCur) with
    ⟨bx, hbx_eval, hbx_val, hbx_keep⟩

  rcases ArithmeticSemantics.eval_Negate_ket_mod
      (qs := qs) (r := dst.zslot i) (b := bx) with
    ⟨bz, hbz_eval, hbz_val, hbz_keep⟩

  refine ⟨bz, ?_, ?_⟩
  ·
    simp [compileAnnotatedOpsToSignedGateAux, qs.eval_seq, hbx_eval, hbz_eval, qs.eval_id]
  ·
    have hσ1 : σ1 = State.negateReg σ i := by
      simp [applyOp?] at hstep
      simp[hstep]
    subst hσ1
    refine ⟨?_, hFit1x, hFit1z⟩
    constructor
    · intro j
      by_cases hji : i = j
      · subst hji
        have hrow_neg :
            evalRowX (qs := qs) src (Register.negate (σ i)) bRef
              =
            - evalRowX (qs := qs) src (σ i) bRef := by
          simpa using
            (evalRowX_negate_raw
              (qs := qs) (src := src) (r := σ i) (b := bRef))
        have hfit_post :
            FitsSignedWidth (ExtReg.width (dst.xslot i))
              (- evalRowX (qs := qs) src (σ i) bRef) := by
          simpa [State.negateReg, hrow_neg] using hFit1x i
        calc
          ExtRegEncoding.extToInt (dst.xslot i) bz
              = ExtRegEncoding.extToInt (dst.xslot i) bx := by
                  exact hbz_keep (dst.xslot i) (hxz i i)
          _   = tcWrapInt (ExtReg.width (dst.xslot i))
                    (- ExtRegEncoding.extToInt (dst.xslot i) bCur) := by
                  simpa using hbx_val
          _   = tcWrapInt (ExtReg.width (dst.xslot i))
                    (- evalRowX (qs := qs) src (σ i) bRef) := by
                  rw [hEnc.1.1 i]
          _   = evalRowX (qs := qs) src ((State.negateReg σ i) i) bRef := by
                  rw [show ((State.negateReg σ i) i) = Register.negate (σ i) by
                        simp [State.negateReg]]
                  rw [hrow_neg]
                  symm
                  exact (tcWrapInt_eq_of_fits hfit_post.1 hfit_post).symm
      ·
        have hji' : j ≠ i := by
          intro h
          exact hji h.symm
        have hkeep1 :
            ExtRegEncoding.extToInt (dst.xslot j) bx
              = ExtRegEncoding.extToInt (dst.xslot j) bCur := by
          exact hbx_keep (dst.xslot j)
            (hxx j i (by simpa [eq_comm] using hji))
        have hkeep2 :
            ExtRegEncoding.extToInt (dst.xslot j) bz
              = ExtRegEncoding.extToInt (dst.xslot j) bx := by
          exact hbz_keep (dst.xslot j) (hxz j i)
        calc
          ExtRegEncoding.extToInt (dst.xslot j) bz
              = ExtRegEncoding.extToInt (dst.xslot j) bx := hkeep2
          _   = ExtRegEncoding.extToInt (dst.xslot j) bCur := hkeep1
          _   = evalRowX (qs := qs) src (σ j) bRef := by
                  simpa [EncodesStateFrom] using hEnc.1.1 j
          _   = evalRowX (qs := qs) src ((State.negateReg σ i) j) bRef := by
                  simp [State.negateReg, State.setReg, hji']

    · intro j
      by_cases hji : i = j
      · subst hji
        have hz_same_on_bx :
            ExtRegEncoding.extToInt (dst.zslot i) bx
              = ExtRegEncoding.extToInt (dst.zslot i) bCur := by
          exact hbx_keep (dst.zslot i) (disjoint_symm (hxz i i))
        have hrow_neg :
            evalRowZ (qs := qs) src (Register.negate (σ i)) bRef
              =
            - evalRowZ (qs := qs) src (σ i) bRef := by
          simpa using
            (evalRowZ_negate_raw
              (qs := qs) (src := src) (r := σ i) (b := bRef))
        have hfit_post :
            FitsSignedWidth (ExtReg.width (dst.zslot i))
              (- evalRowZ (qs := qs) src (σ i) bRef) := by
          simpa [State.negateReg, hrow_neg] using hFit1z i
        calc
          ExtRegEncoding.extToInt (dst.zslot i) bz
              = tcWrapInt (ExtReg.width (dst.zslot i))
                  (- ExtRegEncoding.extToInt (dst.zslot i) bx) := by
                    simpa using hbz_val
          _   = tcWrapInt (ExtReg.width (dst.zslot i))
                  (- ExtRegEncoding.extToInt (dst.zslot i) bCur) := by
                    rw [hz_same_on_bx]
          _   = tcWrapInt (ExtReg.width (dst.zslot i))
                  (- evalRowZ (qs := qs) src (σ i) bRef) := by
                    rw [hEnc.1.2 i]
          _   = evalRowZ (qs := qs) src ((State.negateReg σ i) i) bRef := by
                  rw [show ((State.negateReg σ i) i) = Register.negate (σ i) by
                        simp [State.negateReg]]
                  rw [hrow_neg]
                  symm
                  exact (tcWrapInt_eq_of_fits hfit_post.1 hfit_post).symm
      ·
        have hji' : j ≠ i := by
          intro h
          exact hji h.symm
        have hkeep1 :
            ExtRegEncoding.extToInt (dst.zslot j) bx
              = ExtRegEncoding.extToInt (dst.zslot j) bCur := by
          exact hbx_keep (dst.zslot j)
            (disjoint_symm (hxz i j))
        have hkeep2 :
            ExtRegEncoding.extToInt (dst.zslot j) bz
              = ExtRegEncoding.extToInt (dst.zslot j) bx := by
          exact hbz_keep (dst.zslot j)
            (hzz j i (by simpa [eq_comm] using hji))
        calc
          ExtRegEncoding.extToInt (dst.zslot j) bz
              = ExtRegEncoding.extToInt (dst.zslot j) bx := hkeep2
          _   = ExtRegEncoding.extToInt (dst.zslot j) bCur := hkeep1
          _   = evalRowZ (qs := qs) src (σ j) bRef := by
                  simpa [EncodesStateFrom] using hEnc.1.2 j
          _   = evalRowZ (qs := qs) src ((State.negateReg σ i) j) bRef := by
                  simp [State.negateReg, State.setReg, hji']

lemma encodesFrom_after_addScaled_ket
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ} (hk : 1 < k)
  (phi : ℝ)
  (coeff : Fin (q k) → ℚ)
  (src dst : LayoutState k)
  (hdisj : LayoutSlotsDisjoint dst)
  (dsti srci : Fin k) (negSrc : Bool) (sh : ℕ)
  (hds : dsti ≠ srci)
  (σ σ1 : State k)
  (bRef bCur : qs.Basis)
  (hstep : applyOp? σ (.addScaled dsti srci negSrc sh) = some σ1)
  (hEnc : EncodesStateFromFits (qs := qs) src dst σ bRef bCur)
  (hFit1x : ∀ j : Fin k,
    FitsSignedWidth (ExtReg.width (dst.xslot j))
      (evalRowX (qs := qs) src (σ1 j) bRef))
  (hFit1z : ∀ j : Fin k,
    FitsSignedWidth (ExtReg.width (dst.zslot j))
      (evalRowZ (qs := qs) src (σ1 j) bRef)) :
  ∃ b1 : qs.Basis,
    qs.eval
        (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst
          [{ op := .addScaled dsti srci negSrc sh, phaseTerm? := none }])
        (qs.ket bCur)
      =
    qs.ket b1
    ∧
    EncodesStateFromFits (qs := qs) src dst σ1 bRef b1 := by
  rcases hdisj with ⟨hxx, hzz, hxz⟩

  have disjoint_symm {a b : Reg} : Disjoint a b → Disjoint b a := by
    intro h
    cases h with
    | inl hab => exact Or.inr hab
    | inr hba => exact Or.inl hba

  have hxx_ds : Disjoint (dst.xslot dsti).base (dst.xslot srci).base := by
    exact hxx dsti srci hds

  have hzz_ds : Disjoint (dst.zslot dsti).base (dst.zslot srci).base := by
    exact hzz dsti srci hds

  rcases ArithmeticSemantics.eval_AddScaled_ket_mod
      (qs := qs)
      (dst := dst.xslot dsti) (src := dst.xslot srci)
      (negSrc := negSrc) (sh := sh) (b := bCur) hxx_ds with
    ⟨bx, hbx_eval, hbx_val, hbx_src, hbx_keep⟩

  rcases ArithmeticSemantics.eval_AddScaled_ket_mod
      (qs := qs)
      (dst := dst.zslot dsti) (src := dst.zslot srci)
      (negSrc := negSrc) (sh := sh) (b := bx) hzz_ds with
    ⟨bz, hbz_eval, hbz_val, hbz_src, hbz_keep⟩

  refine ⟨bz, ?_, ?_⟩
  ·
    simp [compileAnnotatedOpsToSignedGateAux, qs.eval_seq, hbx_eval, hbz_eval, qs.eval_id]
  ·
    have hσ1 : σ1 = State.addScaledReg σ dsti srci negSrc sh := by
      simp [applyOp?] at hstep
      simp [hstep]
    subst hσ1
    refine ⟨?_, hFit1x, hFit1z⟩
    constructor
    · intro j
      by_cases hjd : j = dsti
      · subst j
        have hraw :
            evalRowX (qs := qs) src (Register.addScaled (σ dsti) (σ srci) negSrc sh) bRef
              =
            evalRowX (qs := qs) src (σ dsti) bRef
              + (if negSrc then (-1 : ℤ) else 1)
                  * ((2 : ℤ)^sh)
                  * evalRowX (qs := qs) src (σ srci) bRef := by
          simpa using
            (evalRowX_addScaled_raw
              (qs := qs) (src := src)
              (dstReg := σ dsti) (srcReg := σ srci)
              (negSrc := negSrc) (sh := sh) (b := bRef))
        have hfit_post :
            FitsSignedWidth (ExtReg.width (dst.xslot dsti))
              (evalRowX (qs := qs) src
                (Register.addScaled (σ dsti) (σ srci) negSrc sh) bRef) := by
          simpa [State.addScaledReg] using hFit1x dsti
        have hfit_post_lin :
            FitsSignedWidth (ExtReg.width (dst.xslot dsti))
              (evalRowX (qs := qs) src (σ dsti) bRef
                + (if negSrc then (-1 : ℤ) else 1)
                    * ((2 : ℤ)^sh)
                    * evalRowX (qs := qs) src (σ srci) bRef) := by
          simpa [hraw] using hfit_post
        calc
          ExtRegEncoding.extToInt (dst.xslot dsti) bz
              = ExtRegEncoding.extToInt (dst.xslot dsti) bx := by
                  exact hbz_keep (dst.xslot dsti) (hxz dsti dsti) (hxz dsti srci)
          _   = tcWrapInt (ExtReg.width (dst.xslot dsti))
                  (ExtRegEncoding.extToInt (dst.xslot dsti) bCur
                    + (if negSrc then (-1 : ℤ) else 1)
                        * ((2 : ℤ)^sh)
                        * ExtRegEncoding.extToInt (dst.xslot srci) bCur) := by
                  simpa using hbx_val
          _   = tcWrapInt (ExtReg.width (dst.xslot dsti))
                  (evalRowX (qs := qs) src (σ dsti) bRef
                    + (if negSrc then (-1 : ℤ) else 1)
                        * ((2 : ℤ)^sh)
                        * evalRowX (qs := qs) src (σ srci) bRef) := by
                  rw [hEnc.1.1 dsti, hEnc.1.1 srci]
          _   = evalRowX (qs := qs) src ((State.addScaledReg σ dsti srci negSrc sh) dsti) bRef := by
                  rw [show ((State.addScaledReg σ dsti srci negSrc sh) dsti)
                        =
                      Register.addScaled (σ dsti) (σ srci) negSrc sh by
                        simp [State.addScaledReg]]
                  rw [hraw]
                  symm
                  exact (tcWrapInt_eq_of_fits hfit_post_lin.1 hfit_post_lin).symm
      ·
        by_cases hjs : j = srci
        · subst j
          have hsd : srci ≠ dsti := by
            exact hds.symm
          have hkeep2 :
              ExtRegEncoding.extToInt (dst.xslot srci) bz
                = ExtRegEncoding.extToInt (dst.xslot srci) bx := by
            exact hbz_keep (dst.xslot srci) (hxz srci dsti) (hxz srci srci)
          calc
            ExtRegEncoding.extToInt (dst.xslot srci) bz
                = ExtRegEncoding.extToInt (dst.xslot srci) bx := hkeep2
            _   = ExtRegEncoding.extToInt (dst.xslot srci) bCur := hbx_src
            _   = evalRowX (qs := qs) src (σ srci) bRef := by
                    simpa [EncodesStateFrom] using hEnc.1.1 srci
            _   = evalRowX (qs := qs) src ((State.addScaledReg σ dsti srci negSrc sh) srci) bRef := by
                    simp [State.addScaledReg, State.setReg, hsd]
        ·
          have hkeep1 :
              ExtRegEncoding.extToInt (dst.xslot j) bx
                = ExtRegEncoding.extToInt (dst.xslot j) bCur := by
            exact hbx_keep (dst.xslot j) (hxx j dsti hjd) (hxx j srci hjs)
          have hkeep2 :
              ExtRegEncoding.extToInt (dst.xslot j) bz
                = ExtRegEncoding.extToInt (dst.xslot j) bx := by
            exact hbz_keep (dst.xslot j) (hxz j dsti) (hxz j srci)
          calc
            ExtRegEncoding.extToInt (dst.xslot j) bz
                = ExtRegEncoding.extToInt (dst.xslot j) bx := hkeep2
            _   = ExtRegEncoding.extToInt (dst.xslot j) bCur := hkeep1
            _   = evalRowX (qs := qs) src (σ j) bRef := by
                    simpa [EncodesStateFrom] using hEnc.1.1 j
            _   = evalRowX (qs := qs) src ((State.addScaledReg σ dsti srci negSrc sh) j) bRef := by
                    simp [State.addScaledReg, State.setReg, hjd]

    · intro j
      by_cases hjd : j = dsti
      · subst j
        have hz_dst_on_bx :
            ExtRegEncoding.extToInt (dst.zslot dsti) bx
              = ExtRegEncoding.extToInt (dst.zslot dsti) bCur := by
          exact hbx_keep (dst.zslot dsti)
            (disjoint_symm (hxz dsti dsti))
            (disjoint_symm (hxz srci dsti))
        have hz_src_on_bx :
            ExtRegEncoding.extToInt (dst.zslot srci) bx
              = ExtRegEncoding.extToInt (dst.zslot srci) bCur := by
          exact hbx_keep (dst.zslot srci)
            (disjoint_symm (hxz dsti srci))
            (disjoint_symm (hxz srci srci))
        have hraw :
            evalRowZ (qs := qs) src (Register.addScaled (σ dsti) (σ srci) negSrc sh) bRef
              =
            evalRowZ (qs := qs) src (σ dsti) bRef
              + (if negSrc then (-1 : ℤ) else 1)
                  * ((2 : ℤ)^sh)
                  * evalRowZ (qs := qs) src (σ srci) bRef := by
          simpa using
            (evalRowZ_addScaled_raw
              (qs := qs) (src := src)
              (dstReg := σ dsti) (srcReg := σ srci)
              (negSrc := negSrc) (sh := sh) (b := bRef))
        have hfit_post :
            FitsSignedWidth (ExtReg.width (dst.zslot dsti))
              (evalRowZ (qs := qs) src
                (Register.addScaled (σ dsti) (σ srci) negSrc sh) bRef) := by
          simpa [State.addScaledReg] using hFit1z dsti
        have hfit_post_lin :
            FitsSignedWidth (ExtReg.width (dst.zslot dsti))
              (evalRowZ (qs := qs) src (σ dsti) bRef
                + (if negSrc then (-1 : ℤ) else 1)
                    * ((2 : ℤ)^sh)
                    * evalRowZ (qs := qs) src (σ srci) bRef) := by
          simpa [hraw] using hfit_post
        calc
          ExtRegEncoding.extToInt (dst.zslot dsti) bz
              = tcWrapInt (ExtReg.width (dst.zslot dsti))
                  (ExtRegEncoding.extToInt (dst.zslot dsti) bx
                    + (if negSrc then (-1 : ℤ) else 1)
                        * ((2 : ℤ)^sh)
                        * ExtRegEncoding.extToInt (dst.zslot srci) bx) := by
                    simpa using hbz_val
          _   = tcWrapInt (ExtReg.width (dst.zslot dsti))
                  (ExtRegEncoding.extToInt (dst.zslot dsti) bCur
                    + (if negSrc then (-1 : ℤ) else 1)
                        * ((2 : ℤ)^sh)
                        * ExtRegEncoding.extToInt (dst.zslot srci) bCur) := by
                    rw [hz_dst_on_bx, hz_src_on_bx]
          _   = tcWrapInt (ExtReg.width (dst.zslot dsti))
                  (evalRowZ (qs := qs) src (σ dsti) bRef
                    + (if negSrc then (-1 : ℤ) else 1)
                        * ((2 : ℤ)^sh)
                        * evalRowZ (qs := qs) src (σ srci) bRef) := by
                    rw [hEnc.1.2 dsti, hEnc.1.2 srci]
          _   = evalRowZ (qs := qs) src ((State.addScaledReg σ dsti srci negSrc sh) dsti) bRef := by
                  rw [show ((State.addScaledReg σ dsti srci negSrc sh) dsti)
                        =
                      Register.addScaled (σ dsti) (σ srci) negSrc sh by
                        simp [State.addScaledReg]]
                  rw [hraw]
                  symm
                  exact (tcWrapInt_eq_of_fits hfit_post_lin.1 hfit_post_lin).symm
      ·
        by_cases hjs : j = srci
        · subst j
          have hsd : srci ≠ dsti := by
            exact hds.symm
          have hkeep1 :
              ExtRegEncoding.extToInt (dst.zslot srci) bx
                = ExtRegEncoding.extToInt (dst.zslot srci) bCur := by
            exact hbx_keep (dst.zslot srci)
              (disjoint_symm (hxz dsti srci))
              (disjoint_symm (hxz srci srci))
          calc
            ExtRegEncoding.extToInt (dst.zslot srci) bz
                = ExtRegEncoding.extToInt (dst.zslot srci) bx := hbz_src
            _   = ExtRegEncoding.extToInt (dst.zslot srci) bCur := hkeep1
            _   = evalRowZ (qs := qs) src (σ srci) bRef := by
                    simpa [EncodesStateFrom] using hEnc.1.2 srci
            _   = evalRowZ (qs := qs) src ((State.addScaledReg σ dsti srci negSrc sh) srci) bRef := by
                    simp [State.addScaledReg, State.setReg, hsd]
        ·
          have hkeep1 :
              ExtRegEncoding.extToInt (dst.zslot j) bx
                = ExtRegEncoding.extToInt (dst.zslot j) bCur := by
            exact hbx_keep (dst.zslot j)
              (disjoint_symm (hxz dsti j))
              (disjoint_symm (hxz srci j))
          have hkeep2 :
              ExtRegEncoding.extToInt (dst.zslot j) bz
                = ExtRegEncoding.extToInt (dst.zslot j) bx := by
            exact hbz_keep (dst.zslot j) (hzz j dsti hjd) (hzz j srci hjs)
          calc
            ExtRegEncoding.extToInt (dst.zslot j) bz
                = ExtRegEncoding.extToInt (dst.zslot j) bx := hkeep2
            _   = ExtRegEncoding.extToInt (dst.zslot j) bCur := hkeep1
            _   = evalRowZ (qs := qs) src (σ j) bRef := by
                    simpa [EncodesStateFrom] using hEnc.1.2 j
            _   = evalRowZ (qs := qs) src ((State.addScaledReg σ dsti srci negSrc sh) j) bRef := by
                      simp [State.addScaledReg, State.setReg, hjd]


lemma sameOutside_after_shiftL_single
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ} (hk : 1 < k)
  (phi : ℝ)
  (coeff : Fin (q k) → ℚ)
  (dst : LayoutState k)
  (hdisj : LayoutSlotsDisjoint dst)
  (i : Fin k) (m : ℕ)
  (bCur b1 : qs.Basis)
  (hFitX :
    FitsSignedWidth (ExtReg.width (dst.xslot i))
      (((2 : ℤ)^m) * ExtRegEncoding.extToInt (dst.xslot i) bCur))
  (hFitZ :
    FitsSignedWidth (ExtReg.width (dst.zslot i))
      (((2 : ℤ)^m) * ExtRegEncoding.extToInt (dst.zslot i) bCur))
  (heval :
    qs.eval
      (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst
        [{ op := .shiftL i m, phaseTerm? := none }])
      (qs.ket bCur)
    =
    qs.ket b1) :
  SameOutsideLayout qs dst bCur b1 := by
  rcases hdisj with ⟨hxx, hzz, hxz⟩
  have disjoint_symm {a b : Reg} : Disjoint a b → Disjoint b a := by
    intro h
    cases h with
    | inl hab => exact Or.inr hab
    | inr hba => exact Or.inl hba
  rcases ArithmeticSemantics.eval_ShiftL_ket_exact
      (qs := qs) (r := dst.xslot i) (n := m) (b := bCur) hFitX with
    ⟨bx, hbx_eval, _hbx_val, hbx_keep⟩
  have hz_same_on_bx :
      ExtRegEncoding.extToInt (dst.zslot i) bx
        = ExtRegEncoding.extToInt (dst.zslot i) bCur := by
    exact hbx_keep (dst.zslot i) (disjoint_symm (hxz i i))
  have hFitZ' :
      FitsSignedWidth (ExtReg.width (dst.zslot i))
        (((2 : ℤ)^m) * ExtRegEncoding.extToInt (dst.zslot i) bx) := by
    simpa [hz_same_on_bx] using hFitZ
  rcases ArithmeticSemantics.eval_ShiftL_ket_exact
      (qs := qs) (r := dst.zslot i) (n := m) (b := bx) hFitZ' with
    ⟨bz, hbz_eval, _hbz_val, hbz_keep⟩

  have hbz : bz = b1 := by
    apply qs.ket_inj
    simpa [compileAnnotatedOpsToSignedGateAux, qs.eval_seq, qs.eval_id,
      hbx_eval, hbz_eval] using heval
  subst hbz

  intro e he
  calc
    ExtRegEncoding.extToInt e bCur
        = ExtRegEncoding.extToInt e bx := by
            symm
            exact hbx_keep e (he.1 i)
    _   = ExtRegEncoding.extToInt e bz := by
            symm
            exact hbz_keep e (he.2 i)

lemma sameOutside_after_shiftR_single
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ} (hk : 1 < k)
  (phi : ℝ)
  (coeff : Fin (q k) → ℚ)
  (src dst : LayoutState k)
  (hdisj : LayoutSlotsDisjoint dst)
  (i : Fin k) (m : ℕ)
  (σ σ1 : State k)
  (bRef bCur b1 : qs.Basis)
  (hstep : applyOp? σ (.shiftR i m) = some σ1)
  (hEnc : EncodesStateFromFits (qs := qs) src dst σ bRef bCur)
  (hFit1x : ∀ j : Fin k,
    FitsSignedWidth (ExtReg.width (dst.xslot j))
      (evalRowX (qs := qs) src (σ1 j) bRef))
  (hFit1z : ∀ j : Fin k,
    FitsSignedWidth (ExtReg.width (dst.zslot j))
      (evalRowZ (qs := qs) src (σ1 j) bRef))
  (heval :
    qs.eval
      (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst
        [{ op := .shiftR i m, phaseTerm? := none }])
      (qs.ket bCur)
    =
    qs.ket b1) :
  SameOutsideLayout qs dst bCur b1 := by
  rcases hdisj with ⟨hxx, hzz, hxz⟩

  have disjoint_symm {a b : Reg} : Disjoint a b → Disjoint b a := by
    intro h
    cases h with
    | inl hab => exact Or.inr hab
    | inr hba => exact Or.inl hba

  cases hreg : Register.shiftR? (σ i) m with
  | none =>
      have : False := by
        simp [applyOp?, State.shiftRReg?, hreg] at hstep
      exact False.elim this
  | some r' =>
      have hσ1 : State.setReg σ i r' = σ1 := by
        simpa [applyOp?, State.shiftRReg?, hreg] using hstep
      have hx_pre :
          ExtRegEncoding.extToInt (dst.xslot i) bCur
            =
          ((2 : ℤ)^m) * evalRowX (qs := qs) src r' bRef := by
        calc
          ExtRegEncoding.extToInt (dst.xslot i) bCur
              = evalRowX (qs := qs) src (σ i) bRef := by
                  simpa [EncodesStateFrom] using hEnc.1.1 i
          _   = ((2 : ℤ)^m) * evalRowX (qs := qs) src r' bRef := by
                  simpa using
                    (evalRowX_shiftR_exact
                      (qs := qs) (src := src) (r := σ i) (r' := r')
                      (m := m) (b := bRef) hreg)

      rcases ArithmeticSemantics.eval_ShiftR_ket_exact
          (qs := qs) (r := dst.xslot i) (n := m) (b := bCur)
          (q := evalRowX (qs := qs) src r' bRef) hx_pre
          (by
            have hFitXi :
                FitsSignedWidth (ExtReg.width (dst.xslot i))
                  (evalRowX (qs := qs) src ((State.setReg σ i r') i) bRef) := by
              simpa [← hσ1] using hFit1x i
            simpa [State.setReg] using hFitXi) with
        ⟨bx, hbx_eval, _hbx_val, hbx_keep⟩

      have hz_pre :
          ExtRegEncoding.extToInt (dst.zslot i) bx
            =
          ((2 : ℤ)^m) * evalRowZ (qs := qs) src r' bRef := by
        calc
          ExtRegEncoding.extToInt (dst.zslot i) bx
              = ExtRegEncoding.extToInt (dst.zslot i) bCur := by
                  exact hbx_keep (dst.zslot i) (disjoint_symm (hxz i i))
          _   = evalRowZ (qs := qs) src (σ i) bRef := by
                  simpa [EncodesStateFrom] using hEnc.1.2 i
          _   = ((2 : ℤ)^m) * evalRowZ (qs := qs) src r' bRef := by
                  simpa using
                    (evalRowZ_shiftR_exact
                      (qs := qs) (src := src) (r := σ i) (r' := r')
                      (m := m) (b := bRef) hreg)

      rcases ArithmeticSemantics.eval_ShiftR_ket_exact
          (qs := qs) (r := dst.zslot i) (n := m) (b := bx)
          (q := evalRowZ (qs := qs) src r' bRef) hz_pre
          (by
            have hFitZi :
                FitsSignedWidth (ExtReg.width (dst.zslot i))
                  (evalRowZ (qs := qs) src ((State.setReg σ i r') i) bRef) := by
              simpa [← hσ1] using hFit1z i
            simpa [State.setReg] using hFitZi) with
        ⟨bz, hbz_eval, _hbz_val, hbz_keep⟩

      have hbz : bz = b1 := by
        apply qs.ket_inj
        simpa [compileAnnotatedOpsToSignedGateAux, qs.eval_seq, qs.eval_id,
          hbx_eval, hbz_eval] using heval
      subst hbz

      intro e he
      calc
        ExtRegEncoding.extToInt e bCur
            = ExtRegEncoding.extToInt e bx := by
                symm
                exact hbx_keep e (he.1 i)
        _   = ExtRegEncoding.extToInt e bz := by
                symm
                exact hbz_keep e (he.2 i)

lemma sameOutside_after_negate_single
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ} (hk : 1 < k)
  (phi : ℝ)
  (coeff : Fin (q k) → ℚ)
  (dst : LayoutState k)
  (hdisj : LayoutSlotsDisjoint dst)
  (i : Fin k)
  (bCur b1 : qs.Basis)
  (heval :
    qs.eval
      (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst
        [{ op := .negate i, phaseTerm? := none }])
      (qs.ket bCur)
    =
    qs.ket b1) :
  SameOutsideLayout qs dst bCur b1 := by
  rcases hdisj with ⟨hxx, hzz, hxz⟩
  rcases ArithmeticSemantics.eval_Negate_ket_mod
      (qs := qs) (r := dst.xslot i) (b := bCur) with
    ⟨bx, hbx_eval, _hbx_val, hbx_keep⟩
  rcases ArithmeticSemantics.eval_Negate_ket_mod
      (qs := qs) (r := dst.zslot i) (b := bx) with
    ⟨bz, hbz_eval, _hbz_val, hbz_keep⟩

  have hbz : bz = b1 := by
    apply qs.ket_inj
    simpa [compileAnnotatedOpsToSignedGateAux, qs.eval_seq, qs.eval_id,
      hbx_eval, hbz_eval] using heval
  subst hbz

  intro e he
  calc
    ExtRegEncoding.extToInt e bCur
        = ExtRegEncoding.extToInt e bx := by
            symm
            exact hbx_keep e (he.1 i)
    _   = ExtRegEncoding.extToInt e bz := by
            symm
            exact hbz_keep e (he.2 i)

lemma sameOutside_after_addScaled_single
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ} (hk : 1 < k)
  (phi : ℝ)
  (coeff : Fin (q k) → ℚ)
  (dst : LayoutState k)
  (hdisj : LayoutSlotsDisjoint dst)
  (dsti srci : Fin k) (negSrc : Bool) (sh : ℕ)
  (hds : dsti ≠ srci)
  (bCur b1 : qs.Basis)
  (heval :
    qs.eval
      (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst
        [{ op := .addScaled dsti srci negSrc sh, phaseTerm? := none }])
      (qs.ket bCur)
    =
    qs.ket b1) :
  SameOutsideLayout qs dst bCur b1 := by
  rcases hdisj with ⟨hxx, hzz, hxz⟩
  have hxx_ds : Disjoint (dst.xslot dsti).base (dst.xslot srci).base := hxx dsti srci hds
  have hzz_ds : Disjoint (dst.zslot dsti).base (dst.zslot srci).base := hzz dsti srci hds

  rcases ArithmeticSemantics.eval_AddScaled_ket_mod
      (qs := qs)
      (dst := dst.xslot dsti) (src := dst.xslot srci)
      (negSrc := negSrc) (sh := sh) (b := bCur) hxx_ds with
    ⟨bx, hbx_eval, _hbx_val, _hbx_src, hbx_keep⟩

  rcases ArithmeticSemantics.eval_AddScaled_ket_mod
      (qs := qs)
      (dst := dst.zslot dsti) (src := dst.zslot srci)
      (negSrc := negSrc) (sh := sh) (b := bx) hzz_ds with
    ⟨bz, hbz_eval, _hbz_val, _hbz_src, hbz_keep⟩

  have hbz : bz = b1 := by
    apply qs.ket_inj
    simpa [compileAnnotatedOpsToSignedGateAux, qs.eval_seq, qs.eval_id,
      hbx_eval, hbz_eval] using heval
  subst hbz

  intro e he
  calc
    ExtRegEncoding.extToInt e bCur
        = ExtRegEncoding.extToInt e bx := by
            symm
            exact hbx_keep e (he.1 dsti) (he.1 srci)
    _   = ExtRegEncoding.extToInt e bz := by
            symm
            exact hbz_keep e (he.2 dsti) (he.2 srci)

lemma sameOutside_after_noPhase_run_ket_gen_aux
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ} (hk : 1 < k)
  (phi : ℝ)
  (coeff : Fin (q k) → ℚ)
  (src dst : LayoutState k)
  (ops : Prog k)
  (σ σ' : State k)
  (bRef bCur : qs.Basis)
  (n : ℕ)
  (hdisj : LayoutSlotsDisjoint dst)
  (hFits :
    ∀ {τ : State k},
      (∃ pre rest, ops = pre ++ rest ∧ run? pre σ = some τ) →
      (∀ j : Fin k,
        FitsSignedWidth (ExtReg.width (dst.xslot j))
          (evalRowX (qs := qs) src (τ j) bRef)) ∧
      (∀ j : Fin k,
        FitsSignedWidth (ExtReg.width (dst.zslot j))
          (evalRowZ (qs := qs) src (τ j) bRef)))
  (hSafeAdd :
    ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
      ops = pre ++ (.addScaled d s negSrc sh :: rest) →
      d ≠ s)
  (hNP : NoPhase ops)
  (hrun : run? ops σ = some σ')
  (hEnc : EncodesStateFromFits (qs := qs) src dst σ bRef bCur) :
  ∃ bNext : qs.Basis,
    qs.eval
        (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst
          (annotatePhaseTermsAux k n ops))
        (qs.ket bCur)
      =
    qs.ket bNext ∧
    SameOutsideLayout qs dst bCur bNext := by
  induction ops generalizing σ σ' bCur n with
  | nil =>
      have hσ : σ = σ' := by
        simpa [run?] using hrun
      subst hσ
      refine ⟨bCur, ?_, SameOutsideLayout.refl qs dst bCur⟩
      simp [annotatePhaseTermsAux, compileAnnotatedOpsToSignedGateAux, qs.eval_id]

  | cons op ops ih =>
      have hNoTail : NoPhase ops := by
        intro i hi
        exact hNP i (by simp [hi])

      cases op with
      | shiftL i m =>
          cases hstep : applyOp? σ (.shiftL i m) with
          | none =>
              simp [run?, hstep] at hrun
          | some σ1 =>
              have hrunTail : run? ops σ1 = some σ' := by
                simpa [run?, hstep] using hrun

              have hFit1 :
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.xslot j))
                      (evalRowX (qs := qs) src (σ1 j) bRef)) ∧
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.zslot j))
                      (evalRowZ (qs := qs) src (σ1 j) bRef)) := by
                apply hFits
                refine ⟨[.shiftL i m], ops, ?_, ?_⟩
                · simp
                · simp [run?, hstep]

              rcases encodesFrom_after_shiftL_ket
                  (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
                  (src := src) (dst := dst) (hdisj := hdisj)
                  (i := i) (m := m)
                  (σ := σ) (σ1 := σ1)
                  (bRef := bRef) (bCur := bCur)
                  hstep hEnc hFit1.1 hFit1.2 with
                ⟨b1, hEval1, hEnc1⟩

              have hSO1 :
                  SameOutsideLayout qs dst bCur b1 := by
                have hσ1 : σ1 = State.shiftLReg σ i m := by
                  simp [applyOp?] at hstep
                  simpa using hstep.symm
                have hrow_shift_x :
                    evalRowX (qs := qs) src ((σ i).shiftL m) bRef
                      =
                    ((2 : ℤ)^m) * evalRowX (qs := qs) src (σ i) bRef := by
                  simpa using
                    (evalRowX_shiftL_raw
                      (qs := qs) (src := src) (r := σ i) (m := m) (b := bRef))
                have hFitX :
                    FitsSignedWidth (ExtReg.width (dst.xslot i))
                      (((2 : ℤ)^m) * ExtRegEncoding.extToInt (dst.xslot i) bCur) := by
                  have hfit_post :
                      FitsSignedWidth (ExtReg.width (dst.xslot i))
                        (((2 : ℤ)^m) * evalRowX (qs := qs) src (σ i) bRef) := by
                    simpa [hσ1, State.shiftLReg, hrow_shift_x] using hFit1.1 i
                  rw [hEnc.1.1 i]
                  exact hfit_post
                have hrow_shift_z :
                    evalRowZ (qs := qs) src ((σ i).shiftL m) bRef
                      =
                    ((2 : ℤ)^m) * evalRowZ (qs := qs) src (σ i) bRef := by
                  simpa using
                    (evalRowZ_shiftL_raw
                      (qs := qs) (src := src) (r := σ i) (m := m) (b := bRef))
                have hFitZ :
                    FitsSignedWidth (ExtReg.width (dst.zslot i))
                      (((2 : ℤ)^m) * ExtRegEncoding.extToInt (dst.zslot i) bCur) := by
                  have hfit_post :
                      FitsSignedWidth (ExtReg.width (dst.zslot i))
                        (((2 : ℤ)^m) * evalRowZ (qs := qs) src (σ i) bRef) := by
                    simpa [hσ1, State.shiftLReg, hrow_shift_z] using hFit1.2 i
                  rw [hEnc.1.2 i]
                  exact hfit_post
                exact sameOutside_after_shiftL_single
                  (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
                  (dst := dst) (hdisj := hdisj)
                  (i := i) (m := m) (bCur := bCur) (b1 := b1)
                  hFitX hFitZ hEval1

              have hFitsTail :
                ∀ {τ : State k},
                  (∃ pre rest, ops = pre ++ rest ∧ run? pre σ1 = some τ) →
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.xslot j))
                      (evalRowX (qs := qs) src (τ j) bRef)) ∧
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.zslot j))
                      (evalRowZ (qs := qs) src (τ j) bRef)) := by
                intro τ hτ
                rcases hτ with ⟨pre, rest, hsplit, hrunpre⟩
                apply hFits
                refine ⟨(.shiftL i m) :: pre, rest, ?_, ?_⟩
                · simp [hsplit]
                · simp [run?, hstep, hrunpre]

              have hSafeAddTail :
                ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
                  ops = pre ++ (.addScaled d s negSrc sh :: rest) →
                  d ≠ s := by
                intro pre rest d s negSrc sh hadd
                exact hSafeAdd
                  (pre := (.shiftL i m) :: pre)
                  (rest := rest)
                  (d := d) (s := s) (negSrc := negSrc) (sh := sh)
                  (by simp [hadd])

              rcases ih (σ := σ1) (σ' := σ') (bCur := b1) (n := n)
                  hFitsTail hSafeAddTail hNoTail hrunTail hEnc1 with
                ⟨bNext, hEvalTail, hSOTail⟩

              refine ⟨bNext, ?_, SameOutsideLayout.trans (qs := qs) hSO1 hSOTail⟩
              rw [show annotatePhaseTermsAux k n (.shiftL i m :: ops)
                    = [{ op := .shiftL i m, phaseTerm? := none }]
                        ++ annotatePhaseTermsAux k n ops by
                    simp [annotatePhaseTermsAux]]
              rw [eval_compileAnnotatedOpsToSignedGateAux_append
                    (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
                    (st := dst)
                    (xs := [{ op := .shiftL i m, phaseTerm? := none }])
                    (ys := annotatePhaseTermsAux k n ops)
                    (ψ := qs.ket bCur)]
              simpa [hEval1] using hEvalTail

      | shiftR i m =>
          cases hstep : applyOp? σ (.shiftR i m) with
          | none =>
              simp [run?, hstep] at hrun
          | some σ1 =>
              have hrunTail : run? ops σ1 = some σ' := by
                simpa [run?, hstep] using hrun

              have hFit1 :
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.xslot j))
                      (evalRowX (qs := qs) src (σ1 j) bRef)) ∧
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.zslot j))
                      (evalRowZ (qs := qs) src (σ1 j) bRef)) := by
                apply hFits
                refine ⟨[.shiftR i m], ops, ?_, ?_⟩
                · simp
                · simp [run?, hstep]

              rcases encodesFrom_after_shiftR_ket
                  (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
                  (src := src) (dst := dst) (hdisj := hdisj)
                  (i := i) (m := m)
                  (σ := σ) (σ1 := σ1)
                  (bRef := bRef) (bCur := bCur)
                  hstep hEnc hFit1.1 hFit1.2 with
                ⟨b1, hEval1, hEnc1⟩

              have hSO1 :
                  SameOutsideLayout qs dst bCur b1 := by
                exact sameOutside_after_shiftR_single
                  (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
                  (src := src) (dst := dst) (hdisj := hdisj)
                  (i := i) (m := m)
                  (σ := σ) (σ1 := σ1)
                  (bRef := bRef) (bCur := bCur) (b1 := b1)
                  hstep hEnc hFit1.1 hFit1.2 hEval1

              have hFitsTail :
                ∀ {τ : State k},
                  (∃ pre rest, ops = pre ++ rest ∧ run? pre σ1 = some τ) →
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.xslot j))
                      (evalRowX (qs := qs) src (τ j) bRef)) ∧
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.zslot j))
                      (evalRowZ (qs := qs) src (τ j) bRef)) := by
                intro τ hτ
                rcases hτ with ⟨pre, rest, hsplit, hrunpre⟩
                apply hFits
                refine ⟨(.shiftR i m) :: pre, rest, ?_, ?_⟩
                · simp [hsplit]
                · simp [run?, hstep, hrunpre]

              have hSafeAddTail :
                ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
                  ops = pre ++ (.addScaled d s negSrc sh :: rest) →
                  d ≠ s := by
                intro pre rest d s negSrc sh hadd
                exact hSafeAdd
                  (pre := (.shiftR i m) :: pre)
                  (rest := rest)
                  (d := d) (s := s) (negSrc := negSrc) (sh := sh)
                  (by simp [hadd])

              rcases ih (σ := σ1) (σ' := σ') (bCur := b1) (n := n)
                  hFitsTail hSafeAddTail hNoTail hrunTail hEnc1 with
                ⟨bNext, hEvalTail, hSOTail⟩

              refine ⟨bNext, ?_, SameOutsideLayout.trans (qs := qs) hSO1 hSOTail⟩
              rw [show annotatePhaseTermsAux k n (.shiftR i m :: ops)
                    = [{ op := .shiftR i m, phaseTerm? := none }]
                        ++ annotatePhaseTermsAux k n ops by
                    simp [annotatePhaseTermsAux]]
              rw [eval_compileAnnotatedOpsToSignedGateAux_append
                    (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
                    (st := dst)
                    (xs := [{ op := .shiftR i m, phaseTerm? := none }])
                    (ys := annotatePhaseTermsAux k n ops)
                    (ψ := qs.ket bCur)]
              simpa [hEval1] using hEvalTail

      | negate i =>
          cases hstep : applyOp? σ (.negate i) with
          | none =>
              simp [run?, hstep] at hrun
          | some σ1 =>
              have hrunTail : run? ops σ1 = some σ' := by
                simpa [run?, hstep] using hrun

              have hFit1 :
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.xslot j))
                      (evalRowX (qs := qs) src (σ1 j) bRef)) ∧
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.zslot j))
                      (evalRowZ (qs := qs) src (σ1 j) bRef)) := by
                apply hFits
                refine ⟨[.negate i], ops, ?_, ?_⟩
                · simp
                · simp [run?, hstep]

              rcases encodesFrom_after_negate_ket
                  (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
                  (src := src) (dst := dst) (hdisj := hdisj)
                  (i := i)
                  (σ := σ) (σ1 := σ1)
                  (bRef := bRef) (bCur := bCur)
                  hstep hEnc hFit1.1 hFit1.2 with
                ⟨b1, hEval1, hEnc1⟩

              have hSO1 :
                  SameOutsideLayout qs dst bCur b1 := by
                exact sameOutside_after_negate_single
                  (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
                  (dst := dst) (hdisj := hdisj)
                  (i := i) (bCur := bCur) (b1 := b1) hEval1

              have hFitsTail :
                ∀ {τ : State k},
                  (∃ pre rest, ops = pre ++ rest ∧ run? pre σ1 = some τ) →
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.xslot j))
                      (evalRowX (qs := qs) src (τ j) bRef)) ∧
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.zslot j))
                      (evalRowZ (qs := qs) src (τ j) bRef)) := by
                intro τ hτ
                rcases hτ with ⟨pre, rest, hsplit, hrunpre⟩
                apply hFits
                refine ⟨(.negate i) :: pre, rest, ?_, ?_⟩
                · simp [hsplit]
                · simp [run?, hstep, hrunpre]

              have hSafeAddTail :
                ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
                  ops = pre ++ (.addScaled d s negSrc sh :: rest) →
                  d ≠ s := by
                intro pre rest d s negSrc sh hadd
                exact hSafeAdd
                  (pre := (.negate i) :: pre)
                  (rest := rest)
                  (d := d) (s := s) (negSrc := negSrc) (sh := sh)
                  (by simp [hadd])

              rcases ih (σ := σ1) (σ' := σ') (bCur := b1) (n := n)
                  hFitsTail hSafeAddTail hNoTail hrunTail hEnc1 with
                ⟨bNext, hEvalTail, hSOTail⟩

              refine ⟨bNext, ?_, SameOutsideLayout.trans (qs := qs) hSO1 hSOTail⟩
              rw [show annotatePhaseTermsAux k n (.negate i :: ops)
                    = [{ op := .negate i, phaseTerm? := none }]
                        ++ annotatePhaseTermsAux k n ops by
                    simp [annotatePhaseTermsAux]]
              rw [eval_compileAnnotatedOpsToSignedGateAux_append
                    (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
                    (st := dst)
                    (xs := [{ op := .negate i, phaseTerm? := none }])
                    (ys := annotatePhaseTermsAux k n ops)
                    (ψ := qs.ket bCur)]
              simpa [hEval1] using hEvalTail

      | addScaled d s negSrc sh =>
          cases hstep : applyOp? σ (.addScaled d s negSrc sh) with
          | none =>
              simp [run?, hstep] at hrun
          | some σ1 =>
              have hrunTail : run? ops σ1 = some σ' := by
                simpa [run?, hstep] using hrun

              have hds : d ≠ s := by
                have:=hSafeAdd (pre := []) (rest := ops) (sh:=sh) (negSrc:=negSrc) (s:=s) (d:=d)
                simp at this;simp[this]
              have hFit1 :
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.xslot j))
                      (evalRowX (qs := qs) src (σ1 j) bRef)) ∧
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.zslot j))
                      (evalRowZ (qs := qs) src (σ1 j) bRef)) := by
                apply hFits
                refine ⟨[.addScaled d s negSrc sh], ops, ?_, ?_⟩
                · simp
                · simp [run?, hstep]

              rcases encodesFrom_after_addScaled_ket
                  (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
                  (src := src) (dst := dst) (hdisj := hdisj)
                  (dsti := d) (srci := s) (negSrc := negSrc) (sh := sh)
                  hds
                  (σ := σ) (σ1 := σ1)
                  (bRef := bRef) (bCur := bCur)
                  hstep hEnc hFit1.1 hFit1.2 with
                ⟨b1, hEval1, hEnc1⟩

              have hSO1 :
                  SameOutsideLayout qs dst bCur b1 := by
                exact sameOutside_after_addScaled_single
                  (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
                  (dst := dst) (hdisj := hdisj)
                  (dsti := d) (srci := s) (negSrc := negSrc) (sh := sh)
                  hds
                  (bCur := bCur) (b1 := b1) hEval1

              have hFitsTail :
                ∀ {τ : State k},
                  (∃ pre rest, ops = pre ++ rest ∧ run? pre σ1 = some τ) →
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.xslot j))
                      (evalRowX (qs := qs) src (τ j) bRef)) ∧
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.zslot j))
                      (evalRowZ (qs := qs) src (τ j) bRef)) := by
                intro τ hτ
                rcases hτ with ⟨pre, rest, hsplit, hrunpre⟩
                apply hFits
                refine ⟨(.addScaled d s negSrc sh) :: pre, rest, ?_, ?_⟩
                · simp [hsplit]
                · simp [run?, hstep, hrunpre]

              have hSafeAddTail :
                ∀ {pre rest : Prog k} {d' s' : Fin k} {negSrc' : Bool} {sh' : ℕ},
                  ops = pre ++ (.addScaled d' s' negSrc' sh' :: rest) →
                  d' ≠ s' := by
                intro pre rest d' s' negSrc' sh' hadd
                exact hSafeAdd
                  (pre := (.addScaled d s negSrc sh) :: pre)
                  (rest := rest)
                  (d := d') (s := s') (negSrc := negSrc') (sh := sh')
                  (by simp [hadd])

              rcases ih (σ := σ1) (σ' := σ') (bCur := b1) (n := n)
                  hFitsTail hSafeAddTail hNoTail hrunTail hEnc1 with
                ⟨bNext, hEvalTail, hSOTail⟩

              refine ⟨bNext, ?_, SameOutsideLayout.trans (qs := qs) hSO1 hSOTail⟩
              rw [show annotatePhaseTermsAux k n (.addScaled d s negSrc sh :: ops)
                    = [{ op := .addScaled d s negSrc sh, phaseTerm? := none }]
                        ++ annotatePhaseTermsAux k n ops by
                    simp [annotatePhaseTermsAux]]
              rw [eval_compileAnnotatedOpsToSignedGateAux_append
                    (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
                    (st := dst)
                    (xs := [{ op := .addScaled d s negSrc sh, phaseTerm? := none }])
                    (ys := annotatePhaseTermsAux k n ops)
                    (ψ := qs.ket bCur)]
              simpa [hEval1] using hEvalTail

      | phaseProduct i =>
          exfalso
          exact hNP i (by simp)


lemma encodesFrom_after_noPhase_run_ket_gen_aux
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ} (hk : 1 < k)
  (phi : ℝ)
  (coeff : Fin (q k) → ℚ)
  (src dst : LayoutState k)
  (ops : Prog k)
  (σ σ' : State k)
  (bRef bCur : qs.Basis)
  (n : ℕ)
  (hdisj : LayoutSlotsDisjoint dst)
  (hFits :
    ∀ {τ : State k},
      (∃ pre rest, ops = pre ++ rest ∧ run? pre σ = some τ) →
      (∀ j : Fin k,
        FitsSignedWidth (ExtReg.width (dst.xslot j))
          (evalRowX (qs := qs) src (τ j) bRef)) ∧
      (∀ j : Fin k,
        FitsSignedWidth (ExtReg.width (dst.zslot j))
          (evalRowZ (qs := qs) src (τ j) bRef)))
  (hSafeAdd :
    ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
      ops = pre ++ (.addScaled d s negSrc sh :: rest) →
      d ≠ s)
  (hNP : NoPhase ops)
  (hrun : run? ops σ = some σ')
  (hEnc : EncodesStateFromFits (qs := qs) src dst σ bRef bCur) :
  ∃ bNext : qs.Basis,
    qs.eval
        (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst
          (annotatePhaseTermsAux k n ops))
        (qs.ket bCur)
      =
    qs.ket bNext ∧
    EncodesStateFromFits (qs := qs) src dst σ' bRef bNext := by
  induction ops generalizing σ σ' bCur n with
  | nil =>
      have hσ : σ = σ' := by
        simpa [run?] using hrun
      subst hσ
      refine ⟨bCur, ?_, hEnc⟩
      simp [annotatePhaseTermsAux, compileAnnotatedOpsToSignedGateAux, qs.eval_id]

  | cons op ops ih =>
      have hNoTail : NoPhase ops := by
        intro i hi
        exact hNP i (by simp [hi])

      cases op with
      | shiftL i m =>
          cases hstep : applyOp? σ (.shiftL i m) with
          | none =>
              simp [run?, hstep] at hrun
          | some σ1 =>
              have hrunTail : run? ops σ1 = some σ' := by
                simpa [run?, hstep] using hrun

              have hFit1 :
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.xslot j))
                      (evalRowX (qs := qs) src (σ1 j) bRef)) ∧
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.zslot j))
                      (evalRowZ (qs := qs) src (σ1 j) bRef)) := by
                apply hFits
                refine ⟨[.shiftL i m], ops, ?_, ?_⟩
                · simp
                · simp [run?, hstep]

              rcases encodesFrom_after_shiftL_ket
                  (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
                  (src := src) (dst := dst)
                  (hdisj := hdisj)
                  (i := i) (m := m)
                  (σ := σ) (σ1 := σ1)
                  (bRef := bRef) (bCur := bCur)
                  hstep hEnc hFit1.1 hFit1.2 with
                ⟨b1, hEval1, hEnc1⟩

              have hFitsTail :
                ∀ {τ : State k},
                  (∃ pre rest, ops = pre ++ rest ∧ run? pre σ1 = some τ) →
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.xslot j))
                      (evalRowX (qs := qs) src (τ j) bRef)) ∧
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.zslot j))
                      (evalRowZ (qs := qs) src (τ j) bRef)) := by
                intro τ hτ
                rcases hτ with ⟨pre, rest, hsplit, hrunpre⟩
                apply hFits
                refine ⟨(.shiftL i m) :: pre, rest, ?_, ?_⟩
                · simp [hsplit]
                · simp [run?, hstep, hrunpre]

              have hSafeAddTail :
                  ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
                    ops = pre ++ valid_ops.addScaled d s negSrc sh :: rest → d ≠ s := by
                intro pre rest d s negSrc sh hmem
                exact hSafeAdd
                  (pre := valid_ops.shiftL i m :: pre)
                  (rest := rest)
                  (d := d) (s := s) (negSrc := negSrc) (sh := sh)
                  (by simp [hmem])

              rcases ih σ1 σ' b1 n hFitsTail hSafeAddTail hNoTail hrunTail hEnc1 with
                ⟨bNext, hEvalTail, hEncTail⟩

              refine ⟨bNext, ?_, hEncTail⟩

              have hAnn :
                  annotatePhaseTermsAux k n (valid_ops.shiftL i m :: ops) =
                    [{ op := valid_ops.shiftL i m, phaseTerm? := none }] ++
                      annotatePhaseTermsAux k n ops := by
                simp [annotatePhaseTermsAux]

              rw [hAnn]
              rw [eval_compileAnnotatedOpsToSignedGateAux_append
                    (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
                    (st := dst)
                    (xs := [{ op := valid_ops.shiftL i m, phaseTerm? := none }])
                    (ys := annotatePhaseTermsAux k n ops)
                    (ψ := qs.ket bCur)]
              rw [hEval1]
              exact hEvalTail

      | shiftR i m =>
          cases hstep : applyOp? σ (.shiftR i m) with
          | none =>
              simp [run?, hstep] at hrun

          | some σ1 =>
              have hrunTail : run? ops σ1 = some σ' := by
                simpa [run?, hstep] using hrun

              have hFit1 :
                  (∀ (j : Fin k), FitsSignedWidth (dst.xslot j).width (evalRowX qs src (σ1 j) bRef)) ∧
                    ∀ (j : Fin k), FitsSignedWidth (dst.zslot j).width (evalRowZ qs src (σ1 j) bRef) := by
                apply hFits
                refine ⟨[.shiftR i m], ops, ?_, ?_⟩
                · simp
                · simp [run?, hstep]

              rcases encodesFrom_after_shiftR_ket
                  (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
                  (src := src) (dst := dst)
                  (hdisj := hdisj)
                  (i := i) (m := m)
                  (σ := σ) (σ1 := σ1)
                  (bRef := bRef) (bCur := bCur)
                  hstep hEnc hFit1.1 hFit1.2 with
                ⟨b1, hEval1, hEnc1⟩

              have hFitsTail :
                ∀ {τ : State k},
                  (∃ pre rest, ops = pre ++ rest ∧ run? pre σ1 = some τ) →
                    (∀ (j : Fin k), FitsSignedWidth (dst.xslot j).width (evalRowX qs src (τ j) bRef)) ∧
                      ∀ (j : Fin k), FitsSignedWidth (dst.zslot j).width (evalRowZ qs src (τ j) bRef) := by
                intro τ hτ
                rcases hτ with ⟨pre, rest, hsplit, hrunpre⟩
                apply hFits
                refine ⟨.shiftR i m :: pre, rest, ?_, ?_⟩
                · simp [hsplit]
                · simp [run?, hstep, hrunpre]

              have hSafeAddTail :
                ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
                  ops = pre ++ valid_ops.addScaled d s negSrc sh :: rest → d ≠ s := by
                intro pre rest d s negSrc sh hmem
                exact hSafeAdd
                  (pre := .shiftR i m :: pre)
                  (rest := rest)
                  (d := d) (s := s) (negSrc := negSrc) (sh := sh)
                  (by simp [hmem])

              rcases ih σ1 σ' b1 n hFitsTail hSafeAddTail hNoTail hrunTail hEnc1 with
                ⟨bNext, hEvalTail, hEncTail⟩

              refine ⟨bNext, ?_, hEncTail⟩

              have hAnn :
                  annotatePhaseTermsAux k n (.shiftR i m :: ops) =
                    [{ op := .shiftR i m, phaseTerm? := none }] ++
                      annotatePhaseTermsAux k n ops := by
                simp [annotatePhaseTermsAux]

              rw [hAnn]
              rw [eval_compileAnnotatedOpsToSignedGateAux_append
                    (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
                    (st := dst)
                    (xs := [{ op := .shiftR i m, phaseTerm? := none }])
                    (ys := annotatePhaseTermsAux k n ops)
                    (ψ := qs.ket bCur)]
              rw [hEval1]
              exact hEvalTail

      | negate i =>
          have hstep : applyOp? σ (.negate i) = some (State.negateReg σ i) := by
            simp [applyOp?, State.negateReg]

          have hrunTail : run? ops (State.negateReg σ i) = some σ' := by
            simpa [run?, hstep] using hrun

          have hFit1 :
              (∀ (j : Fin k), FitsSignedWidth (dst.xslot j).width (evalRowX qs src ((State.negateReg σ i) j) bRef)) ∧
                ∀ (j : Fin k), FitsSignedWidth (dst.zslot j).width (evalRowZ qs src ((State.negateReg σ i) j) bRef) := by
            apply hFits
            refine ⟨[.negate i], ops, ?_, ?_⟩
            · simp
            · simp [run?, hstep]

          rcases encodesFrom_after_negate_ket
              (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
              (src := src) (dst := dst)
              (hdisj := hdisj)
              (i := i)
              (σ := σ) (σ1 := State.negateReg σ i)
              (bRef := bRef) (bCur := bCur)
              hstep hEnc hFit1.1 hFit1.2 with
            ⟨b1, hEval1, hEnc1⟩

          have hFitsTail :
            ∀ {τ : State k},
              (∃ pre rest, ops = pre ++ rest ∧ run? pre (State.negateReg σ i) = some τ) →
                (∀ (j : Fin k), FitsSignedWidth (dst.xslot j).width (evalRowX qs src (τ j) bRef)) ∧
                  ∀ (j : Fin k), FitsSignedWidth (dst.zslot j).width (evalRowZ qs src (τ j) bRef) := by
            intro τ hτ
            rcases hτ with ⟨pre, rest, hsplit, hrunpre⟩
            apply hFits
            refine ⟨.negate i :: pre, rest, ?_, ?_⟩
            · simp [hsplit]
            · simp [run?, hstep, hrunpre]

          have hSafeAddTail :
            ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
              ops = pre ++ valid_ops.addScaled d s negSrc sh :: rest → d ≠ s := by
            intro pre rest d s negSrc sh hmem
            exact hSafeAdd
              (pre := .negate i :: pre)
              (rest := rest)
              (d := d) (s := s) (negSrc := negSrc) (sh := sh)
              (by simp [hmem])

          rcases ih (State.negateReg σ i) σ' b1 n hFitsTail hSafeAddTail hNoTail hrunTail hEnc1 with
            ⟨bNext, hEvalTail, hEncTail⟩

          refine ⟨bNext, ?_, hEncTail⟩

          have hAnn :
              annotatePhaseTermsAux k n (.negate i :: ops) =
                [{ op := .negate i, phaseTerm? := none }] ++
                  annotatePhaseTermsAux k n ops := by
            simp [annotatePhaseTermsAux]

          rw [hAnn]
          rw [eval_compileAnnotatedOpsToSignedGateAux_append
                (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
                (st := dst)
                (xs := [{ op := .negate i, phaseTerm? := none }])
                (ys := annotatePhaseTermsAux k n ops)
                (ψ := qs.ket bCur)]
          rw [hEval1]
          exact hEvalTail

      | addScaled dsti srci negSrc sh =>
          cases hstep : applyOp? σ (.addScaled dsti srci negSrc sh) with
          | none =>
              simp [run?, hstep] at hrun
          | some σ1 =>
              have hrunTail : run? ops σ1 = some σ' := by
                simpa [run?, hstep] using hrun

              have hFit1 :
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.xslot j))
                      (evalRowX (qs := qs) src (σ1 j) bRef)) ∧
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.zslot j))
                      (evalRowZ (qs := qs) src (σ1 j) bRef)) := by
                apply hFits
                refine ⟨[.addScaled dsti srci negSrc sh], ops, ?_, ?_⟩
                · simp
                · simp [run?, hstep]
              have hds : dsti ≠ srci := by
                exact hSafeAdd
                  (pre := [])
                  (rest := ops)
                  (d := dsti) (s := srci) (negSrc := negSrc) (sh := sh)
                  (by simp)

              rcases encodesFrom_after_addScaled_ket
                  (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
                  (src := src) (dst := dst)
                  (hdisj := hdisj)
                  (dsti := dsti) (srci := srci) (negSrc := negSrc) (sh := sh)
                  (hds := hds)
                  (σ := σ) (σ1 := σ1)
                  (bRef := bRef) (bCur := bCur)
                  hstep hEnc hFit1.1 hFit1.2 with
                ⟨b1, hEval1, hEnc1⟩

              have hFitsTail :
                ∀ {τ : State k},
                  (∃ pre rest, ops = pre ++ rest ∧ run? pre σ1 = some τ) →
                    (∀ (j : Fin k), FitsSignedWidth (dst.xslot j).width (evalRowX qs src (τ j) bRef)) ∧
                      ∀ (j : Fin k), FitsSignedWidth (dst.zslot j).width (evalRowZ qs src (τ j) bRef) := by
                intro τ hτ
                rcases hτ with ⟨pre, rest, hsplit, hrunpre⟩
                apply hFits
                refine ⟨valid_ops.addScaled dsti srci negSrc sh :: pre, rest, ?_, ?_⟩
                · simp [hsplit]
                · simp [run?, hstep, hrunpre]

              have hSafeAddTail :
                ∀ {pre rest : Prog k} {d s : Fin k} {negSrc_1 : Bool} {sh_1 : ℕ},
                  ops = pre ++ valid_ops.addScaled d s negSrc_1 sh_1 :: rest → d ≠ s := by
                intro pre rest d s negSrc_1 sh_1 hmem
                exact hSafeAdd
                  (pre := valid_ops.addScaled dsti srci negSrc sh :: pre)
                  (rest := rest)
                  (d := d) (s := s) (negSrc := negSrc_1) (sh := sh_1)
                  (by simp [hmem])

              rcases ih σ1 σ' b1 n hFitsTail hSafeAddTail hNoTail hrunTail hEnc1 with
                ⟨bNext, hEvalTail, hEncTail⟩

              refine ⟨bNext, ?_, hEncTail⟩

              have hAnn :
                  annotatePhaseTermsAux k n (valid_ops.addScaled dsti srci negSrc sh :: ops) =
                    [{ op := valid_ops.addScaled dsti srci negSrc sh, phaseTerm? := none }] ++
                      annotatePhaseTermsAux k n ops := by
                simp [annotatePhaseTermsAux]

              rw [hAnn]
              rw [eval_compileAnnotatedOpsToSignedGateAux_append
                    (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
                    (st := dst)
                    (xs := [{ op := valid_ops.addScaled dsti srci negSrc sh, phaseTerm? := none }])
                    (ys := annotatePhaseTermsAux k n ops)
                    (ψ := qs.ket bCur)]
              rw [hEval1]
              exact hEvalTail

      | phaseProduct i =>
          exfalso
          exact hNP i (by simp)

lemma encodesFrom_after_noPhase_run_ket_gen
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ} (hk : 1 < k)
  (phi : ℝ)
  (coeff : Fin (q k) → ℚ)
  (src dst : LayoutState k)
  (ops : Prog k)
  (σ σ' : State k)
  (bRef bCur : qs.Basis)
  (n : ℕ)
  (hdisj : LayoutSlotsDisjoint dst)
  (hFits :
    ∀ {τ : State k},
      (∃ pre rest, ops = pre ++ rest ∧ run? pre σ = some τ) →
      (∀ j : Fin k,
        FitsSignedWidth (ExtReg.width (dst.xslot j))
          (evalRowX (qs := qs) src (τ j) bRef)) ∧
      (∀ j : Fin k,
        FitsSignedWidth (ExtReg.width (dst.zslot j))
          (evalRowZ (qs := qs) src (τ j) bRef)))
  (hSafeAdd :
    ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
      ops = pre ++ (.addScaled d s negSrc sh :: rest) →
      d ≠ s)
  (hNP : NoPhase ops)
  (hrun : run? ops σ = some σ')
  (hEnc : EncodesStateFromFits (qs := qs) src dst σ bRef bCur) :
  ∃ bNext : qs.Basis,
    qs.eval
        (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst
          (annotatePhaseTermsAux k n ops))
        (qs.ket bCur)
      =
    qs.ket bNext
    ∧
    EncodesStateFromFits (qs := qs) src dst σ' bRef bNext := by
  exact encodesFrom_after_noPhase_run_ket_gen_aux
    (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
    (src := src) (dst := dst) (ops := ops)
    (σ := σ) (σ' := σ') (bRef := bRef) (bCur := bCur) (n := n)
    hdisj hFits hSafeAdd hNP hrun hEnc

/-! =========================================================
    Section: Phase-block helpers
========================================================= -/

lemma eval_matched_phase_ket_from
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ}
  (src dst : LayoutState k)
  (σ : State k)
  (b0 b1 : qs.Basis)
  (hk0 : 0 < k)
  (i : Fin k)
  (pt : Point)
  (phi : ℝ)
  (hEnc : EncodesStateFrom (qs := qs) src dst σ b0 b1)
  (hmatch : matchesAt_pointRow_state (k := k) hk0 σ i pt = true) :
  qs.eval
      (Gate.SignedPhaseProd phi (dst.xslot i) (dst.zslot i))
      (qs.ket b1)
    =
  (Complex.exp
      (phi * Complex.I *
        (((evalRowX (qs := qs) src (expectedRow (k := k) pt) b0 : ℤ) : ℂ) *
         (((evalRowZ (qs := qs) src (expectedRow (k := k) pt) b0 : ℤ) : ℂ))))) •
    qs.ket b1 := by
  simp[PhaseSemantics.eval_SignedPhaseProd_ket]
  have hσi : σ i = expectedRow (k := k) pt := by
    unfold matchesAt_pointRow_state regEqExpected at hmatch
    have hall : ∀ j : Fin k, σ i j = expectedRow (k := k) pt j := by
      intro j
      have hmem : j ∈ List.finRange k := List.mem_finRange j
      have := List.all_eq_true.mp hmatch j hmem
      simpa using of_decide_eq_true this
    funext j
    exact hall j
  rw [hEnc.1 i, hσi]
  rw [hEnc.2 i, hσi]

@[simp] lemma phaseProductCount_eq_zero_of_NoPhase
  {k : ℕ} {ops : Prog k} (hNo : NoPhase ops) :
  phaseProductCount ops = 0 := by
  induction ops with
  | nil =>
      simp [phaseProductCount]
  | cons op ops ih =>
      have hNoTail : NoPhase ops := by
        intro i hi
        exact hNo i (by simp [hi])
      cases op with
      | shiftL i n =>
          simpa [phaseProductCount] using ih hNoTail
      | shiftR i n =>
          simpa [phaseProductCount] using ih hNoTail
      | negate i =>
          simpa [phaseProductCount] using ih hNoTail
      | addScaled dst src negSrc sh =>
          simpa [phaseProductCount] using ih hNoTail
      | phaseProduct i =>
          exfalso
          exact hNo i (by simp)

/- Induction-friendly existential body theorem for the phase-block proof stack. -/

lemma eval_compileAnnotatedOpsToSignedGateAux_of_blocks_from
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ)
  (coeff : Fin (q k) → ℚ)
  (src dst : LayoutState k) :
  ∀ {σ : State k} {ops : Prog k} {pts : List Point},
    BlockDecomposition (k := k) (by omega) σ ops pts →
    ∀ (n : ℕ) (hn : n + pts.length = q k) (b0 bCur : qs.Basis),
      (hdisj : LayoutSlotsDisjoint dst) →
      (hFits :
        ∀ {τ : State k},
          (∃ pre rest, ops = pre ++ rest ∧ run? pre σ = some τ) →
            (∀ j : Fin k,
              FitsSignedWidth (ExtReg.width (dst.xslot j))
                (evalRowX (qs := qs) src (τ j) b0)) ∧
            (∀ j : Fin k,
              FitsSignedWidth (ExtReg.width (dst.zslot j))
                (evalRowZ (qs := qs) src (τ j) b0))) →
      (hSafeAdd :
        ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
          ops = pre ++ valid_ops.addScaled d s negSrc sh :: rest → d ≠ s) →
      EncodesStateFromFits (qs := qs) src dst σ b0 bCur →
      ∃ σf bNext,
        run? ops σ = some σf ∧
        qs.eval
            (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst
              (annotatePhaseTermsAux k n ops))
            (qs.ket bCur)
          =
        phaseScalarFrom (qs := qs) k phi coeff src b0 pts n hn •
          qs.ket bNext
        ∧
        EncodesStateFromFits (qs := qs) src dst σf b0 bNext := by
  intro σ ops pts hB
  induction hB with
  | nil σ σ' tail hNP hrun =>
      intro n hn b0 bCur hdisj hFits hSafeAdd hEnc
      rcases encodesFrom_after_noPhase_run_ket_gen
          (qs := qs)
          (hk := hk)
          (phi := phi)
          (coeff := coeff)
          (src := src)
          (dst := dst)
          (ops := tail)
          (σ := σ)
          (σ' := σ')
          (bRef := b0)
          (bCur := bCur)
          (n := n)
          hdisj
          hFits
          hSafeAdd
          hNP
          hrun
          hEnc with
        ⟨bNext, hEval, hEncNext⟩
      refine ⟨σ', bNext, hrun, ?_, hEncNext⟩
      simpa [phaseScalarFrom] using hEval

  | cons B hrest ih =>
      intro n hn b0 bCur hdisj hFits hSafeAdd hEnc
      rename_i σ2 pt pts2 oprest

      have hlt : n < q k := by
        simp at hn;omega

      have hnTail : n + 1 + pts2.length = q k := by
        simp at hn; simp[← hn]; simp[add_assoc]; rw[add_comm]

      have hcount : phaseProductCount B.toProg = 1 := by
        rw [PhaseBlock.toProg, phaseProductCount_append]
        simp [phaseProductCount_eq_zero_of_NoPhase, B.noPhase_pre, phaseProductCount]

      have hAnnAll :
          annotatePhaseTermsAux k n (B.toProg ++ oprest) =
            annotatePhaseTermsAux k n B.toProg ++
            annotatePhaseTermsAux k (n + 1) oprest := by
        rw [annotatePhaseTermsAux_append]
        simp [hcount]

      have hAnnBlock :
          annotatePhaseTermsAux k n B.toProg =
            annotatePhaseTermsAux k n B.arith ++
            [{ op := .phaseProduct B.i, phaseTerm? := some ⟨n, hlt⟩ }] := by
        rw [PhaseBlock.toProg, annotatePhaseTermsAux_append]
        simp [annotatePhaseTermsAux, hlt,
          phaseProductCount_eq_zero_of_NoPhase, B.noPhase_pre]

      have hFitsArith :
          ∀ {τ : State k},
            (∃ pre rest, B.arith = pre ++ rest ∧ run? pre σ2 = some τ) →
              (∀ j : Fin k,
                FitsSignedWidth (ExtReg.width (dst.xslot j))
                  (evalRowX (qs := qs) src (τ j) b0)) ∧
              (∀ j : Fin k,
                FitsSignedWidth (ExtReg.width (dst.zslot j))
                  (evalRowZ (qs := qs) src (τ j) b0)) := by
        intro τ hτ
        rcases hτ with ⟨pre, rest, hsplit, hrunpre⟩
        apply hFits
        refine ⟨pre, rest ++ [.phaseProduct B.i] ++ oprest, ?_, ?_⟩
        · simp [PhaseBlock.toProg, hsplit, List.append_assoc]
        · exact hrunpre

      have hSafeAddArith :
          ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
            B.arith = pre ++ valid_ops.addScaled d s negSrc sh :: rest → d ≠ s := by
        intro pre rest d s negSrc sh hmem
        exact hSafeAdd
          (pre := pre)
          (rest := rest ++ [valid_ops.phaseProduct B.i] ++ oprest)
          (d := d) (s := s) (negSrc := negSrc) (sh := sh)
          (by
            rw [PhaseBlock.toProg]
            simp [hmem, List.append_assoc])

      rcases encodesFrom_after_noPhase_run_ket_gen
          (qs := qs)
          (hk := hk)
          (phi := phi)
          (coeff := coeff)
          (src := src)
          (dst := dst)
          (ops := B.arith)
          (σ := σ2)
          (σ' := B.σmid)
          (bRef := b0)
          (bCur := bCur)
          (n := n)
          hdisj
          hFitsArith
          hSafeAddArith
          B.noPhase_pre
          B.run_pre
          hEnc with
        ⟨bMid, hArithEval, hArithEnc⟩

      have hRunBlock : run? B.toProg σ2 = some B.σmid := by
        simp[PhaseBlock.toProg, run?_append, B.run_pre, applyOp?]

      have hFitsTail :
          ∀ {τ : State k},
            (∃ pre rest, oprest = pre ++ rest ∧ run? pre B.σmid = some τ) →
              (∀ j : Fin k,
                FitsSignedWidth (ExtReg.width (dst.xslot j))
                  (evalRowX (qs := qs) src (τ j) b0)) ∧
              (∀ j : Fin k,
                FitsSignedWidth (ExtReg.width (dst.zslot j))
                  (evalRowZ (qs := qs) src (τ j) b0)) := by
        intro τ hτ
        rcases hτ with ⟨pre, rest, hsplit, hrunpre⟩
        apply hFits
        refine ⟨B.toProg ++ pre, rest, ?_, ?_⟩
        · simp [PhaseBlock.toProg, hsplit, List.append_assoc]
        · rw [run?_append, hRunBlock];simp[hrunpre]

      have hSafeAddTail :
          ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
            oprest = pre ++ valid_ops.addScaled d s negSrc sh :: rest → d ≠ s := by
        intro pre rest d s negSrc sh hmem
        exact hSafeAdd
          (pre := B.toProg ++ pre)
          (rest := rest)
          (d := d) (s := s) (negSrc := negSrc) (sh := sh)
          (by simp [hmem, List.append_assoc])

      rcases ih (n + 1) hnTail b0 bMid hdisj hFitsTail hSafeAddTail hArithEnc with
        ⟨σf, bNext, hRunTail, hEvalTail, hEncTail⟩

      refine ⟨σf, bNext, ?_, ?_, hEncTail⟩
      · simpa [PhaseBlock.toProg, run?_append, B.run_pre, applyOp?] using hRunTail

      · rw [hAnnAll]
        rw [eval_compileAnnotatedOpsToSignedGateAux_append
              (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
              (st := dst)
              (xs := annotatePhaseTermsAux k n B.toProg)
              (ys := annotatePhaseTermsAux k (n + 1) oprest)
              (ψ := qs.ket bCur)]

        rw [hAnnBlock]
        rw [eval_compileAnnotatedOpsToSignedGateAux_append
              (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
              (st := dst)
              (xs := annotatePhaseTermsAux k n B.arith)
              (ys := [{ op := .phaseProduct B.i, phaseTerm? := some ⟨n, hlt⟩ }])
              (ψ := qs.ket bCur)]

        rw [hArithEval]

        have hPhase :
            qs.eval
                (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst
                  [{ op := .phaseProduct B.i, phaseTerm? := some ⟨n, hlt⟩ }])
                (qs.ket bMid)
              =
            (Complex.exp
              ((phi * ((coeff ⟨n, hlt⟩ : ℚ) : ℝ)) * Complex.I *
                (((evalRowX (qs := qs) src (expectedRow (k := k) pt) b0 : ℤ) : ℂ) *
                 (((evalRowZ (qs := qs) src (expectedRow (k := k) pt) b0 : ℤ) : ℂ))))) •
              qs.ket bMid := by
          simp [compileAnnotatedOpsToSignedGateAux, qs.eval_seq, qs.eval_id]
          simpa using
            (eval_matched_phase_ket_from
              (qs := qs)
              (src := src)
              (dst := dst)
              (σ := B.σmid)
              (b0 := b0)
              (b1 := bMid)
              (hk0 := by omega)
              (i := B.i)
              (pt := pt)
              (phi := phi * ((coeff ⟨n, hlt⟩ : ℚ) : ℝ))
              hArithEnc.1
              B.match_pt)

        rw [hPhase]
        rw [qs.eval_smul]
        rw [hEvalTail]
        simp [phaseScalarFrom, mul_assoc, smul_smul]

lemma eval_compileAnnotatedOpsToSignedGateAux_of_blocks_from_sameOutside
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ)
  (coeff : Fin (q k) → ℚ)
  (src dst : LayoutState k) :
  ∀ {σ : State k} {ops : Prog k} {pts : List Point},
    BlockDecomposition (k := k) (by omega) σ ops pts →
    ∀ (n : ℕ) (hn : n + pts.length = q k) (b0 bCur : qs.Basis),
      (hdisj : LayoutSlotsDisjoint dst) →
      (hFits :
        ∀ {τ : State k},
          (∃ pre rest, ops = pre ++ rest ∧ run? pre σ = some τ) →
            (∀ j : Fin k,
              FitsSignedWidth (ExtReg.width (dst.xslot j))
                (evalRowX (qs := qs) src (τ j) b0)) ∧
            (∀ j : Fin k,
              FitsSignedWidth (ExtReg.width (dst.zslot j))
                (evalRowZ (qs := qs) src (τ j) b0))) →
      (hSafeAdd :
        ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
          ops = pre ++ valid_ops.addScaled d s negSrc sh :: rest → d ≠ s) →
      EncodesStateFromFits (qs := qs) src dst σ b0 bCur →
      ∃ bNext,
        qs.eval
            (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst
              (annotatePhaseTermsAux k n ops))
            (qs.ket bCur)
          =
        phaseScalarFrom (qs := qs) k phi coeff src b0 pts n hn •
          qs.ket bNext
        ∧
        SameOutsideLayout qs dst bCur bNext := by
  intro σ ops pts hB
  induction hB with
  | nil σ σ' tail hNP hrun =>
      intro n hn b0 bCur hdisj hFits hSafeAdd hEnc
      rcases sameOutside_after_noPhase_run_ket_gen_aux
          (qs := qs)
          (hk := hk)
          (phi := phi)
          (coeff := coeff)
          (src := src) (dst := dst)
          (ops := tail)
          (σ := σ) (σ' := σ')
          (bRef := b0) (bCur := bCur)
          (n := n)
          hdisj hFits hSafeAdd hNP hrun hEnc with
        ⟨bNext, hEval, hSO⟩
      refine ⟨bNext, ?_, hSO⟩
      simpa [phaseScalarFrom] using hEval

  | cons B hrest ih =>
      intro n hn b0 bCur hdisj hFits hSafeAdd hEnc
      rename_i σ2 pt pts2 oprest

      have hlt : n < q k := by
        simp at hn
        omega

      have hFitsArith :
          ∀ {τ : State k},
            (∃ pre rest, B.arith = pre ++ rest ∧ run? pre σ2 = some τ) →
              (∀ j : Fin k,
                FitsSignedWidth (ExtReg.width (dst.xslot j))
                  (evalRowX (qs := qs) src (τ j) b0)) ∧
              (∀ j : Fin k,
                FitsSignedWidth (ExtReg.width (dst.zslot j))
                  (evalRowZ (qs := qs) src (τ j) b0)) := by
        intro τ hτ
        rcases hτ with ⟨pre, rest, hsplit, hrunpre⟩
        apply hFits
        refine ⟨pre, rest ++ [.phaseProduct B.i] ++ oprest, ?_, ?_⟩
        · simp [PhaseBlock.toProg, hsplit, List.append_assoc]
        · exact hrunpre

      have hSafeAddArith :
          ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
            B.arith = pre ++ valid_ops.addScaled d s negSrc sh :: rest → d ≠ s := by
        intro pre rest d s negSrc sh hadd
        exact hSafeAdd
          (pre := pre)
          (rest := rest ++ [valid_ops.phaseProduct B.i] ++ oprest)
          (d := d) (s := s) (negSrc := negSrc) (sh := sh)
          (by
            rw [PhaseBlock.toProg]
            simp [hadd, List.append_assoc])

      rcases encodesFrom_after_noPhase_run_ket_gen
          (qs := qs)
          (hk := hk)
          (phi := phi)
          (coeff := coeff)
          (src := src) (dst := dst)
          (ops := B.arith)
          (σ := σ2) (σ' := B.σmid)
          (bRef := b0) (bCur := bCur)
          (n := n)
          hdisj hFitsArith hSafeAddArith
          B.noPhase_pre B.run_pre hEnc with
        ⟨bMid, hArithEval, hArithEnc⟩

      rcases sameOutside_after_noPhase_run_ket_gen_aux
          (qs := qs)
          (hk := hk)
          (phi := phi)
          (coeff := coeff)
          (src := src) (dst := dst)
          (ops := B.arith)
          (σ := σ2) (σ' := B.σmid)
          (bRef := b0) (bCur := bCur)
          (n := n)
          hdisj hFitsArith hSafeAddArith
          B.noPhase_pre B.run_pre hEnc with
        ⟨bMid', hArithEval', hArithSO'⟩

      have hbMid' : bMid' = bMid := by
        apply qs.ket_inj
        simp [hArithEval] at hArithEval';simp[hArithEval']

      have hArithSO : SameOutsideLayout qs dst bCur bMid := by
        simpa [hbMid'] using hArithSO'

      have hRunBlock : run? B.toProg σ2 = some B.σmid := by
        simp [PhaseBlock.toProg, run?_append, B.run_pre, applyOp?]

      have hFitsTail :
          ∀ {τ : State k},
            (∃ pre rest, oprest = pre ++ rest ∧ run? pre B.σmid = some τ) →
              (∀ j : Fin k,
                FitsSignedWidth (ExtReg.width (dst.xslot j))
                  (evalRowX (qs := qs) src (τ j) b0)) ∧
              (∀ j : Fin k,
                FitsSignedWidth (ExtReg.width (dst.zslot j))
                  (evalRowZ (qs := qs) src (τ j) b0)) := by
        intro τ hτ
        rcases hτ with ⟨pre, rest, hsplit, hrunpre⟩
        apply hFits
        refine ⟨B.toProg ++ pre, rest, ?_, ?_⟩
        · simp [PhaseBlock.toProg, hsplit, List.append_assoc]
        · rw [run?_append, hRunBlock]
          simpa using hrunpre

      have hSafeAddTail :
          ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
            oprest = pre ++ valid_ops.addScaled d s negSrc sh :: rest → d ≠ s := by
        intro pre rest d s negSrc sh hadd
        exact hSafeAdd
          (pre := B.toProg ++ pre)
          (rest := rest)
          (d := d) (s := s) (negSrc := negSrc) (sh := sh)
          (by simp [hadd, List.append_assoc])

      have hnTail : n + 1 + pts2.length = q k := by
        simp at hn
        omega

      rcases ih (n + 1) hnTail b0 bMid hdisj hFitsTail hSafeAddTail hArithEnc with
        ⟨bNext, hEvalTail, hTailSO⟩

      refine ⟨bNext, ?_, SameOutsideLayout.trans (qs := qs) hArithSO hTailSO⟩

      have hAnnAll :
          annotatePhaseTermsAux k n (B.toProg ++ oprest) =
            annotatePhaseTermsAux k n B.toProg ++
              annotatePhaseTermsAux k (n + 1) oprest := by
        have hCountBlock : phaseProductCount B.toProg = 1 := by
          simp [PhaseBlock.toProg, phaseProductCount, B.noPhase_pre]

        have hAnnAll :
            annotatePhaseTermsAux k n (B.toProg ++ oprest) =
              annotatePhaseTermsAux k n B.toProg ++
                annotatePhaseTermsAux k (n + 1) oprest := by
          rw [annotatePhaseTermsAux_append]
          simp [hCountBlock]
        rw[hAnnAll]

      have hAnnBlock :
          annotatePhaseTermsAux k n B.toProg =
            annotatePhaseTermsAux k n B.arith ++
              [{ op := .phaseProduct B.i, phaseTerm? := some ⟨n, hlt⟩ }] := by
        simp [PhaseBlock.toProg]
        rw [annotatePhaseTermsAux_append]
        simp [annotatePhaseTermsAux, hlt,
          phaseProductCount_eq_zero_of_NoPhase, B.noPhase_pre]

      rw [hAnnAll]
      rw [eval_compileAnnotatedOpsToSignedGateAux_append
            (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
            (st := dst)
            (xs := annotatePhaseTermsAux k n B.toProg)
            (ys := annotatePhaseTermsAux k (n + 1) oprest)
            (ψ := qs.ket bCur)]

      rw [hAnnBlock]
      rw [eval_compileAnnotatedOpsToSignedGateAux_append
            (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
            (st := dst)
            (xs := annotatePhaseTermsAux k n B.arith)
            (ys := [{ op := .phaseProduct B.i, phaseTerm? := some ⟨n, hlt⟩ }])
            (ψ := qs.ket bCur)]

      rw [hArithEval]

      have hPhase :
          qs.eval
              (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst
                [{ op := .phaseProduct B.i, phaseTerm? := some ⟨n, hlt⟩ }])
              (qs.ket bMid)
            =
          (Complex.exp
            ((phi * ((coeff ⟨n, hlt⟩ : ℚ) : ℝ)) * Complex.I *
              (((evalRowX (qs := qs) src (expectedRow (k := k) pt) b0 : ℤ) : ℂ) *
               (((evalRowZ (qs := qs) src (expectedRow (k := k) pt) b0 : ℤ) : ℂ))))) •
            qs.ket bMid := by
        simp [compileAnnotatedOpsToSignedGateAux, qs.eval_seq, qs.eval_id]
        simpa using
          (eval_matched_phase_ket_from
            (qs := qs)
            (src := src)
            (dst := dst)
            (σ := B.σmid)
            (b0 := b0)
            (b1 := bMid)
            (hk0 := by omega)
            (i := B.i)
            (pt := pt)
            (phi := phi * ((coeff ⟨n, hlt⟩ : ℚ) : ℝ))
            hArithEnc.1
            B.match_pt)

      rw [hPhase]
      rw [qs.eval_smul]
      rw [hEvalTail]
      simp [phaseScalarFrom, mul_assoc, smul_smul]


lemma eval_compileAnnotatedOpsToSignedGateAux_of_blocks
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ)
  (pts : List Point)
  (hpts : pts.length = q k)
  (coeff : Fin (q k) → ℚ)
  (src dst : LayoutState k)
  (b0 bMid : qs.Basis)
  (ops : Prog k)
  (hdisj : LayoutSlotsDisjoint dst)
  (hFits :
    ∀ {τ : State k},
      (∃ pre rest, ops = pre ++ rest ∧ run? pre State.start_state = some τ) →
        (∀ j : Fin k,
          FitsSignedWidth (ExtReg.width (dst.xslot j))
            (evalRowX (qs := qs) src (τ j) b0)) ∧
        (∀ j : Fin k,
          FitsSignedWidth (ExtReg.width (dst.zslot j))
            (evalRowZ (qs := qs) src (τ j) b0)))
  (hSafeAdd :
    ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
      ops = pre ++ valid_ops.addScaled d s negSrc sh :: rest → d ≠ s)
  (hEnc : EncodesStateFromFits (qs := qs) src dst State.start_state b0 bMid)
  (hB : BlockDecomposition (k := k) (by omega) State.start_state ops pts)
  (run_ops_start_state : run? ops State.start_state = some State.start_state) :
  qs.eval
      (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst
        (annotatePhaseTermsAux k 0 ops))
      (qs.ket bMid)
    =
  phaseScalarFrom (qs := qs) k phi coeff src b0 pts 0 (by simpa using hpts) •
    qs.ket bMid := by
  rcases eval_compileAnnotatedOpsToSignedGateAux_of_blocks_from
      (qs := qs)
      (k := k) (hk := hk)
      (phi := phi)
      (coeff := coeff)
      (src := src) (dst := dst)
      (σ := State.start_state)
      (ops := ops)
      (pts := pts)
      hB
      0
      (by simp [hpts])
      b0
      bMid
      hdisj
      hFits
      hSafeAdd
      hEnc with
    ⟨σf, bNext, hRun, hBody, hEncNextFits⟩

  rcases hEncNextFits with ⟨hEncNext, hOutX, hOutZ⟩

  rcases eval_compileAnnotatedOpsToSignedGateAux_of_blocks_from_sameOutside
      (qs := qs)
      (k := k) (hk := hk)
      (phi := phi)
      (coeff := coeff)
      (src := src) (dst := dst)
      (σ := State.start_state)
      (ops := ops)
      (pts := pts)
      hB
      0
      (by simp [hpts])
      b0
      bMid
      hdisj
      hFits
      hSafeAdd
      hEnc with
    ⟨bSO, hBodySO, hSO⟩

  have hσf : σf = State.start_state := by
    have hs : some σf = some State.start_state := by
      calc
        some σf = run? ops State.start_state := by simp [hRun]
        _ = some State.start_state := run_ops_start_state
    exact Option.some.inj hs

  subst hσf

  have hscalar_ne :
      phaseScalarFrom (qs := qs) k phi coeff src b0 pts 0 (by simpa using hpts) ≠ 0 := by
    exact phaseScalarFrom_ne_zero
      (qs := qs) (k := k) (phi := phi) (coeff := coeff)
      (src := src) (b0 := b0)
      pts 0 (by simpa using hpts)

  have hbSO : bSO = bNext := by
    apply ket_eq_of_same_nonzero_smul
      (qs := qs)
      (a := phaseScalarFrom (qs := qs) k phi coeff src b0 pts 0 (by simpa using hpts))
      hscalar_ne
    calc
      phaseScalarFrom (qs := qs) k phi coeff src b0 pts 0 (by simpa using hpts) • qs.ket bSO
          = qs.eval
              (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst
                (annotatePhaseTermsAux k 0 ops))
              (qs.ket bMid) := by
                simpa using hBodySO.symm
      _   = phaseScalarFrom (qs := qs) k phi coeff src b0 pts 0 (by simpa using hpts) •
              qs.ket bNext := by
                simpa using hBody

  have hSO' : SameOutsideLayout qs dst bMid bNext := by
    simpa [hbSO] using hSO

  have hXslots :
      ∀ i : Fin k,
        ExtRegEncoding.extToInt (dst.xslot i) bNext =
          ExtRegEncoding.extToInt (dst.xslot i) bMid := by
    intro i
    calc
      ExtRegEncoding.extToInt (dst.xslot i) bNext
          = evalRowX (qs := qs) src (State.start_state i) b0 := by
              simpa [EncodesStateFrom] using hEncNext.1 i
      _   = ExtRegEncoding.extToInt (dst.xslot i) bMid := by
              symm
              simpa [EncodesStateFrom] using hEnc.1.1 i

  have hZslots :
      ∀ i : Fin k,
        ExtRegEncoding.extToInt (dst.zslot i) bNext =
          ExtRegEncoding.extToInt (dst.zslot i) bMid := by
    intro i
    calc
      ExtRegEncoding.extToInt (dst.zslot i) bNext
          = evalRowZ (qs := qs) src (State.start_state i) b0 := by
              simpa [EncodesStateFrom] using hEncNext.2 i
      _   = ExtRegEncoding.extToInt (dst.zslot i) bMid := by
              symm
              simpa [EncodesStateFrom] using hEnc.1.2 i

  have hbNext_eq : bNext = bMid := by
    exact basis_eq_of_sameOutside_and_slots
      (qs := qs)
      (dst := dst)
      (bMid := bMid)
      (bNext := bNext)
      hSO'
      hXslots
      hZslots
      (qubit_in_layout_or_outside dst)
      (fun e b1 b2 q hInt hqlo hqhi =>
        ExtRegEncoding.hbit_of_ext (e := e) (b1 := b1) (b2 := b2) (q := q) hInt hqlo hqhi)


  subst hbNext_eq
  simpa using hBody


/- Allocation/deallocation cancellation lemmas used when closing the compiled
body back to the original allocated basis state. -/
lemma allocChunkGate_deallocChunkGate_cancel
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ} (i : Fin k) (src dst : ExtReg) (ψ : qs.State) :
  qs.eval
    (allocChunkGate i src dst ;; deallocChunkGate i src dst)
    ψ = ψ := by
  unfold allocChunkGate deallocChunkGate
  set n := extraDelta src dst
  by_cases h0 : n = 0
  · simp [h0, qs.eval_seq, qs.eval_id]
  · by_cases htop : isTopChunk i
    · simp [h0, htop, qs.eval_seq]
      have:=ExtensionSemantics.eval_signExtend_signDealloc
        (qs := qs) src n ψ
      simp_all
    · simp [h0, htop, qs.eval_seq]
      have:= ExtensionSemantics.eval_zeroExtend_zeroDealloc
        (qs := qs) src n ψ
      simp_all

lemma alloc_dealloc_aux_cancel
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ}
  (src dst : LayoutState k)
  (n : ℕ) (hn : n ≤ k)
  (ψ : qs.State) :
  qs.eval
    (compileSignedAllocationsAux src dst n hn ;;
     compileSignedDeallocationsAux src dst n hn)
    ψ = ψ := by
  induction n with
  | zero =>
      simp [compileSignedAllocationsAux_zero, compileSignedDeallocationsAux_zero,
            qs.eval_seq, qs.eval_id]
  | succ n ih =>
      have hn' : n ≤ k := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn
      rw [compileSignedAllocationsAux_succ, compileSignedDeallocationsAux_succ]
      set i:Fin k:=⟨n,by omega⟩
      have:=allocChunkGate_deallocChunkGate_cancel qs i
      simp at *
      simp[this,ih]

lemma eval_compileSignedDeallocations_alloc_id
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ}
  (src dst : LayoutState k)
  (ψ : qs.State) :
  qs.eval
    (compileSignedAllocations k src dst ;; compileSignedDeallocations k src dst)
    ψ = ψ:=by
    have := alloc_dealloc_aux_cancel qs (k:=k) src dst (n:=k) (by simp) ψ
    simp at this
    simp[compileSignedAllocations,compileSignedDeallocations,this]

lemma eval_compileSignedDeallocations_ket_from_alloc
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ}
  (src dst : LayoutState k)
  (b0 bCur : qs.Basis)
  (hAlloc : qs.eval (compileSignedAllocations k src dst) (qs.ket b0)
              = qs.ket bCur) :
  qs.eval (compileSignedDeallocations k src dst) (qs.ket bCur)
    = qs.ket b0:=by
    have:=eval_compileSignedDeallocations_alloc_id qs (k:=k) src dst (QSemantics.ket b0)
    rw[← hAlloc]; simp at this
    simp[this]

lemma eval_compileSignedDeallocations_ket
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ}
  (src dst : LayoutState k)
  (b bAlloc : qs.Basis)
  (hAlloc : qs.eval (compileSignedAllocations k src dst) (qs.ket b) = qs.ket bAlloc) :
  qs.eval (compileSignedDeallocations k src dst) (qs.ket bAlloc) = qs.ket b := by
  have:=eval_compileSignedDeallocations_ket_from_alloc qs (k:=k) src dst b bAlloc hAlloc
  apply this

lemma eval_compileAnnotatedOpsToSignedGateAux_of_blocks_then_dealloc
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ)
  (pts : List Point)
  (hpts : pts.length = q k)
  (coeff : Fin (q k) → ℚ)
  (src dst : LayoutState k)
  (b0 bMid : qs.Basis)
  (ops : Prog k)
  (hdisj : LayoutSlotsDisjoint dst)
  (hFits :
    ∀ {τ : State k},
      (∃ pre rest, ops = pre ++ rest ∧ run? pre State.start_state = some τ) →
        (∀ j : Fin k,
          FitsSignedWidth (ExtReg.width (dst.xslot j))
            (evalRowX (qs := qs) src (τ j) b0)) ∧
        (∀ j : Fin k,
          FitsSignedWidth (ExtReg.width (dst.zslot j))
            (evalRowZ (qs := qs) src (τ j) b0)))
  (hSafeAdd :
    ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
      ops = pre ++ valid_ops.addScaled d s negSrc sh :: rest → d ≠ s)
  (hEnc : EncodesStateFromFits (qs := qs) src dst State.start_state b0 bMid)
  (hAlloc :
    qs.eval (compileSignedAllocations k src dst) (qs.ket b0) = qs.ket bMid)
  (hB : BlockDecomposition (k := k) (by omega) State.start_state ops pts)
  (run_ops_start_state : run? ops State.start_state = some State.start_state) :
  qs.eval
      (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst
        (annotatePhaseTermsAux k 0 ops) ;;
       compileSignedDeallocations k src dst)
      (qs.ket bMid)
    =
  phaseScalarFrom (qs := qs) k phi coeff src b0 pts 0 (by simpa using hpts) •
    qs.ket b0 := by
  have hBody :
      qs.eval
          (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst
            (annotatePhaseTermsAux k 0 ops))
          (qs.ket bMid)
        =
      phaseScalarFrom (qs := qs) k phi coeff src b0 pts 0 (by simpa using hpts) •
        qs.ket bMid := by
    exact eval_compileAnnotatedOpsToSignedGateAux_of_blocks
      (qs := qs)
      (k := k) (hk := hk)
      (phi := phi)
      (pts := pts)
      (hpts := hpts)
      (coeff := coeff)
      (src := src) (dst := dst)
      (b0 := b0) (bMid := bMid)
      (ops := ops)
      hdisj
      hFits
      hSafeAdd
      hEnc
      hB
      run_ops_start_state

  have hDealloc :
      qs.eval (compileSignedDeallocations k src dst) (qs.ket bMid) = qs.ket b0 := by
    exact eval_compileSignedDeallocations_ket
      (qs := qs)
      (src := src) (dst := dst)
      (b := b0) (bAlloc := bMid)
      hAlloc

  rw [qs.eval_seq]
  rw [hBody]
  rw [qs.eval_smul]
  rw [hDealloc]


end Shor
