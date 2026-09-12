import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.Allocation

namespace Shor
open Gate
open Operations
open scoped BigOperators

/-! =========================================================
    Slot Disjointness And Single-Step Correctness
    The body gates update one logical row at a time. These helpers turn layout
    disjointness into active-register disjointness and prove that each compiled
    arithmetic instruction preserves the encoded symbolic state.
========================================================= -/

/-- Active disjointness is symmetric, matching the direction often needed by primitive gate locality facts. -/
lemma activeDisjoint_symm
    {a b : ExtReg}
    (h : ExtReg.ActiveDisjoint a b) :
    ExtReg.ActiveDisjoint b a := by
  exact Disjoint.symm h

/-- Convert owned slot-disjointness of a layout into active disjointness for all `x/x`, `z/z`, and `x/z` slots. -/
lemma layoutSlotsActiveDisjoint
    {k : ℕ}
    {dst : LayoutState k}
    (h : LayoutSlotsDisjoint dst) :
    (∀ i j, i ≠ j →
      ExtReg.ActiveDisjoint (dst.xslot i) (dst.xslot j)) ∧
    (∀ i j, i ≠ j →
      ExtReg.ActiveDisjoint (dst.zslot i) (dst.zslot j)) ∧
    (∀ i j,
      ExtReg.ActiveDisjoint (dst.xslot i) (dst.zslot j)) := by
  rcases h with ⟨hxx, hzz, hxz⟩
  exact ⟨fun i j hij => ExtReg.activeDisjoint_of_ownedDisjoint (hxx i j hij),
    fun i j hij => ExtReg.activeDisjoint_of_ownedDisjoint (hzz i j hij),
    fun i j => ExtReg.activeDisjoint_of_ownedDisjoint (hxz i j)⟩

/-- Correctness of a single compiled left-shift operation on an encoded basis state. -/
lemma encodesFrom_after_shiftL_ket
  (qs : QSemantics)
  [RegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ} (hk : 1 < k)
  (phi : Angle)
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
  rcases layoutSlotsActiveDisjoint hdisj with ⟨hxx, hzz, hxz⟩
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
        (((2 : ℤ)^m) * extToInt (dst.xslot i) bCur) := by
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
      extToInt (dst.zslot i) bx
        = extToInt (dst.zslot i) bCur := by
    exact hbx_keep (dst.zslot i) (activeDisjoint_symm (hxz i i))
  have hrow_shift_z :
      evalRowZ (qs := qs) src ((σ i).shiftL m) bRef
        =
      ((2 : ℤ)^m) * evalRowZ (qs := qs) src (σ i) bRef := by
    simpa using
      (evalRowZ_shiftL_raw
        (qs := qs) (src := src) (r := σ i) (m := m) (b := bRef))
  have hfit_shift_z :
      FitsSignedWidth (ExtReg.width (dst.zslot i))
        (((2 : ℤ)^m) * extToInt (dst.zslot i) bx) := by
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
          extToInt (dst.xslot i) bz
              = extToInt (dst.xslot i) bx := by
                  exact hbz_keep (dst.xslot i) (hxz i i)
          _   = ((2 : ℤ)^m) * extToInt (dst.xslot i) bCur := by
                  simpa using hbx_val
          _   = ((2 : ℤ)^m) * evalRowX (qs := qs) src (σ i) bRef := by
                  rw [hEnc.1.1 i]
          _   = evalRowX (qs := qs) src ((State.shiftLReg σ i m) i) bRef := by
                  symm
                  simpa [State.shiftLReg] using hrow_shift_x
      ·
        have hkeep1 :
            extToInt (dst.xslot j) bx
              = extToInt (dst.xslot j) bCur := by
          exact hbx_keep (dst.xslot j)
            (hxx j i (by simpa [eq_comm] using hji))
        have hkeep2 :
            extToInt (dst.xslot j) bz
              = extToInt (dst.xslot j) bx := by
          exact hbz_keep (dst.xslot j) (hxz j i)
        have hji' : j ≠ i := by intro h; exact hji h.symm
        calc
          extToInt (dst.xslot j) bz
              = extToInt (dst.xslot j) bx := hkeep2
          _   = extToInt (dst.xslot j) bCur := hkeep1
          _   = evalRowX (qs := qs) src (σ j) bRef := by
                  simpa [EncodesStateFrom] using hEnc.1.1 j
          _   = evalRowX (qs := qs) src ((State.shiftLReg σ i m) j) bRef := by
                  simp [State.shiftLReg, State.setReg, hji']
    · intro j
      by_cases hji : i = j
      · subst hji
        calc
          extToInt (dst.zslot i) bz
              = ((2 : ℤ)^m) * extToInt (dst.zslot i) bx := by
                    simpa using hbz_val
          _   = ((2 : ℤ)^m) * extToInt (dst.zslot i) bCur := by
                    rw [hz_same_on_bx]
          _   = ((2 : ℤ)^m) * evalRowZ (qs := qs) src (σ i) bRef := by
                    rw [hEnc.1.2 i]
          _   = evalRowZ (qs := qs) src ((State.shiftLReg σ i m) i) bRef := by
                    symm
                    simpa [State.shiftLReg] using hrow_shift_z
      ·
        have hkeep1 :
            extToInt (dst.zslot j) bx
              = extToInt (dst.zslot j) bCur := by
          exact hbx_keep (dst.zslot j)
            (activeDisjoint_symm (hxz i j))
        have hkeep2 :
            extToInt (dst.zslot j) bz
              = extToInt (dst.zslot j) bx := by
          exact hbz_keep (dst.zslot j)
            (hzz j i (by simpa [eq_comm] using hji))
        have hji' : j ≠ i := by intro h; exact hji h.symm
        calc
          extToInt (dst.zslot j) bz
              = extToInt (dst.zslot j) bx := hkeep2
          _   = extToInt (dst.zslot j) bCur := hkeep1
          _   = evalRowZ (qs := qs) src (σ j) bRef := by
                  simpa [EncodesStateFrom] using hEnc.1.2 j
          _   = evalRowZ (qs := qs) src ((State.shiftLReg σ i m) j) bRef := by
                  simp [State.shiftLReg, State.setReg, hji']

/-- Correctness of a single compiled right-shift operation on an encoded basis state. -/
lemma encodesFrom_after_shiftR_ket
  (qs : QSemantics)
  [RegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ} (hk : 1 < k)
  (phi : Angle)
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
  rcases layoutSlotsActiveDisjoint hdisj with ⟨hxx, hzz, hxz⟩
  cases hreg : Register.shiftR? (σ i) m with
  | none =>
      simp [applyOp?, State.shiftRReg?, hreg] at hstep
  | some r' =>
      have hσ1 : State.setReg σ i r' = σ1 := by
        simpa [applyOp?, State.shiftRReg?, hreg] using hstep
      subst hσ1
      have hx_pre :
          extToInt (dst.xslot i) bCur
            =
          ((2 : ℤ)^m) * evalRowX (qs := qs) src r' bRef := by
        calc
          extToInt (dst.xslot i) bCur
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
          extToInt (dst.zslot i) bx
            =
          ((2 : ℤ)^m) * evalRowZ (qs := qs) src r' bRef := by
        calc
          extToInt (dst.zslot i) bx
              = extToInt (dst.zslot i) bCur := by
                  exact hbx_keep (dst.zslot i) (activeDisjoint_symm (hxz i i))
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
      · simp [compileAnnotatedOpsToSignedGateAux, qs.eval_seq, hbx_eval, hbz_eval, qs.eval_id]
      ·
        refine ⟨?_, hFit1x, hFit1z⟩
        constructor
        · intro j
          by_cases hji : i = j
          · subst hji
            calc
              extToInt (dst.xslot i) bz
                  = extToInt (dst.xslot i) bx := by
                      exact hbz_keep (dst.xslot i) (hxz i i)
              _   = evalRowX (qs := qs) src r' bRef := hbx_val
              _   = evalRowX (qs := qs) src ((State.setReg σ i r') i) bRef := by
                      simp [State.setReg]
          ·
            have hji' : j ≠ i := by intro h; exact hji h.symm
            have hkeep1 :
                extToInt (dst.xslot j) bx
                  = extToInt (dst.xslot j) bCur := by
              exact hbx_keep (dst.xslot j)
                (hxx j i (by simpa [eq_comm] using hji))
            have hkeep2 :
                extToInt (dst.xslot j) bz
                  = extToInt (dst.xslot j) bx := by
              exact hbz_keep (dst.xslot j) (hxz j i)
            calc
              extToInt (dst.xslot j) bz
                  = extToInt (dst.xslot j) bx := hkeep2
              _   = extToInt (dst.xslot j) bCur := hkeep1
              _   = evalRowX (qs := qs) src (σ j) bRef := by
                      simpa [EncodesStateFrom] using hEnc.1.1 j
              _   = evalRowX (qs := qs) src ((State.setReg σ i r') j) bRef := by
                      simp [State.setReg, hji']
        · intro j
          by_cases hji : i = j
          · subst hji
            calc
              extToInt (dst.zslot i) bz
                  = evalRowZ (qs := qs) src r' bRef := hbz_val
              _   = evalRowZ (qs := qs) src ((State.setReg σ i r') i) bRef := by
                      simp [State.setReg]
          ·
            have hji' : j ≠ i := by intro h; exact hji h.symm
            have hkeep1 :
                extToInt (dst.zslot j) bx
                  = extToInt (dst.zslot j) bCur := by
              exact hbx_keep (dst.zslot j)
                (activeDisjoint_symm (hxz i j))
            have hkeep2 :
                extToInt (dst.zslot j) bz
                  = extToInt (dst.zslot j) bx := by
              exact hbz_keep (dst.zslot j)
                (hzz j i (by simpa [eq_comm] using hji))
            calc
              extToInt (dst.zslot j) bz
                  = extToInt (dst.zslot j) bx := hkeep2
              _   = extToInt (dst.zslot j) bCur := hkeep1
              _   = evalRowZ (qs := qs) src (σ j) bRef := by
                      simpa [EncodesStateFrom] using hEnc.1.2 j
              _   = evalRowZ (qs := qs) src ((State.setReg σ i r') j) bRef := by
                      simp [State.setReg, hji']

/-- Correctness of a single compiled negation operation on an encoded basis state. -/
lemma encodesFrom_after_negate_ket
  (qs : QSemantics)
  [RegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ} (hk : 1 < k)
  (phi : Angle)
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
  rcases layoutSlotsActiveDisjoint hdisj with ⟨hxx, hzz, hxz⟩
  rcases ArithmeticSemantics.eval_Negate_ket_mod
      (qs := qs) (r := dst.xslot i) (b := bCur) with
    ⟨bx, hbx_eval, hbx_val, hbx_keep⟩
  rcases ArithmeticSemantics.eval_Negate_ket_mod
      (qs := qs) (r := dst.zslot i) (b := bx) with
    ⟨bz, hbz_eval, hbz_val, hbz_keep⟩
  refine ⟨bz, ?_, ?_⟩
  · simp [compileAnnotatedOpsToSignedGateAux, qs.eval_seq, hbx_eval, hbz_eval, qs.eval_id]
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
          extToInt (dst.xslot i) bz
              = extToInt (dst.xslot i) bx := by
                  exact hbz_keep (dst.xslot i) (hxz i i)
          _   = tcWrapInt (ExtReg.width (dst.xslot i))
                    (- extToInt (dst.xslot i) bCur) := by
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
        have hji' : j ≠ i := by intro h; exact hji h.symm
        have hkeep1 :
            extToInt (dst.xslot j) bx
              = extToInt (dst.xslot j) bCur := by
          exact hbx_keep (dst.xslot j)
            (hxx j i (by simpa [eq_comm] using hji))
        have hkeep2 :
            extToInt (dst.xslot j) bz
              = extToInt (dst.xslot j) bx := by
          exact hbz_keep (dst.xslot j) (hxz j i)
        calc
          extToInt (dst.xslot j) bz
              = extToInt (dst.xslot j) bx := hkeep2
          _   = extToInt (dst.xslot j) bCur := hkeep1
          _   = evalRowX (qs := qs) src (σ j) bRef := by
                  simpa [EncodesStateFrom] using hEnc.1.1 j
          _   = evalRowX (qs := qs) src ((State.negateReg σ i) j) bRef := by
                  simp [State.negateReg, State.setReg, hji']
    · intro j
      by_cases hji : i = j
      · subst hji
        have hz_same_on_bx :
            extToInt (dst.zslot i) bx
              = extToInt (dst.zslot i) bCur := by
          exact hbx_keep (dst.zslot i) (activeDisjoint_symm (hxz i i))
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
          extToInt (dst.zslot i) bz
              = tcWrapInt (ExtReg.width (dst.zslot i))
                  (- extToInt (dst.zslot i) bx) := by
                    simpa using hbz_val
          _   = tcWrapInt (ExtReg.width (dst.zslot i))
                  (- extToInt (dst.zslot i) bCur) := by
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
        have hji' : j ≠ i := by intro h; exact hji h.symm
        have hkeep1 :
            extToInt (dst.zslot j) bx
              = extToInt (dst.zslot j) bCur := by
          exact hbx_keep (dst.zslot j)
            (activeDisjoint_symm (hxz i j))
        have hkeep2 :
            extToInt (dst.zslot j) bz
              = extToInt (dst.zslot j) bx := by
          exact hbz_keep (dst.zslot j)
            (hzz j i (by simpa [eq_comm] using hji))
        calc
          extToInt (dst.zslot j) bz
              = extToInt (dst.zslot j) bx := hkeep2
          _   = extToInt (dst.zslot j) bCur := hkeep1
          _   = evalRowZ (qs := qs) src (σ j) bRef := by
                  simpa [EncodesStateFrom] using hEnc.1.2 j
          _   = evalRowZ (qs := qs) src ((State.negateReg σ i) j) bRef := by
                  simp [State.negateReg, State.setReg, hji']

/-- Correctness of a single compiled scaled-addition operation on an encoded basis state. -/
lemma encodesFrom_after_addScaled_ket
  (qs : QSemantics)
  [RegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ} (hk : 1 < k)
  (phi : Angle)
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
  rcases layoutSlotsActiveDisjoint hdisj with ⟨hxx, hzz, hxz⟩
  have hxx_ds : ExtReg.ActiveDisjoint (dst.xslot dsti) (dst.xslot srci) := by
    exact hxx dsti srci hds
  have hzz_ds : ExtReg.ActiveDisjoint (dst.zslot dsti) (dst.zslot srci) := by
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
  · simp [compileAnnotatedOpsToSignedGateAux, qs.eval_seq, hbx_eval, hbz_eval, qs.eval_id]
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
          extToInt (dst.xslot dsti) bz
              = extToInt (dst.xslot dsti) bx := by
                  exact hbz_keep (dst.xslot dsti) (hxz dsti dsti) (hxz dsti srci)
          _   = tcWrapInt (ExtReg.width (dst.xslot dsti))
                  (extToInt (dst.xslot dsti) bCur
                    + (if negSrc then (-1 : ℤ) else 1)
                        * ((2 : ℤ)^sh)
                        * extToInt (dst.xslot srci) bCur) := by
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
          have hsd : srci ≠ dsti := hds.symm
          have hkeep2 :
              extToInt (dst.xslot srci) bz
                = extToInt (dst.xslot srci) bx := by
            exact hbz_keep (dst.xslot srci) (hxz srci dsti) (hxz srci srci)
          calc
            extToInt (dst.xslot srci) bz
                = extToInt (dst.xslot srci) bx := hkeep2
            _   = extToInt (dst.xslot srci) bCur := hbx_src
            _   = evalRowX (qs := qs) src (σ srci) bRef := by
                    simpa [EncodesStateFrom] using hEnc.1.1 srci
            _   = evalRowX (qs := qs) src ((State.addScaledReg σ dsti srci negSrc sh) srci) bRef := by
                    simp [State.addScaledReg, State.setReg, hsd]
        ·
          have hkeep1 :
              extToInt (dst.xslot j) bx
                = extToInt (dst.xslot j) bCur := by
            exact hbx_keep (dst.xslot j) (hxx j dsti hjd) (hxx j srci hjs)
          have hkeep2 :
              extToInt (dst.xslot j) bz
                = extToInt (dst.xslot j) bx := by
            exact hbz_keep (dst.xslot j) (hxz j dsti) (hxz j srci)
          calc
            extToInt (dst.xslot j) bz
                = extToInt (dst.xslot j) bx := hkeep2
            _   = extToInt (dst.xslot j) bCur := hkeep1
            _   = evalRowX (qs := qs) src (σ j) bRef := by
                    simpa [EncodesStateFrom] using hEnc.1.1 j
            _   = evalRowX (qs := qs) src ((State.addScaledReg σ dsti srci negSrc sh) j) bRef := by
                    simp [State.addScaledReg, State.setReg, hjd]
    · intro j
      by_cases hjd : j = dsti
      · subst j
        have hz_dst_on_bx :
            extToInt (dst.zslot dsti) bx
              = extToInt (dst.zslot dsti) bCur := by
          exact hbx_keep (dst.zslot dsti)
            (activeDisjoint_symm (hxz dsti dsti))
            (activeDisjoint_symm (hxz srci dsti))
        have hz_src_on_bx :
            extToInt (dst.zslot srci) bx
              = extToInt (dst.zslot srci) bCur := by
          exact hbx_keep (dst.zslot srci)
            (activeDisjoint_symm (hxz dsti srci))
            (activeDisjoint_symm (hxz srci srci))
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
          extToInt (dst.zslot dsti) bz
              = tcWrapInt (ExtReg.width (dst.zslot dsti))
                  (extToInt (dst.zslot dsti) bx
                    + (if negSrc then (-1 : ℤ) else 1)
                        * ((2 : ℤ)^sh)
                        * extToInt (dst.zslot srci) bx) := by
                    simpa using hbz_val
          _   = tcWrapInt (ExtReg.width (dst.zslot dsti))
                  (extToInt (dst.zslot dsti) bCur
                    + (if negSrc then (-1 : ℤ) else 1)
                        * ((2 : ℤ)^sh)
                        * extToInt (dst.zslot srci) bCur) := by
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
          have hsd : srci ≠ dsti := hds.symm
          have hkeep1 :
              extToInt (dst.zslot srci) bx
                = extToInt (dst.zslot srci) bCur := by
            exact hbx_keep (dst.zslot srci)
              (activeDisjoint_symm (hxz dsti srci))
              (activeDisjoint_symm (hxz srci srci))
          calc
            extToInt (dst.zslot srci) bz
                = extToInt (dst.zslot srci) bx := hbz_src
            _   = extToInt (dst.zslot srci) bCur := hkeep1
            _   = evalRowZ (qs := qs) src (σ srci) bRef := by
                    simpa [EncodesStateFrom] using hEnc.1.2 srci
            _   = evalRowZ (qs := qs) src ((State.addScaledReg σ dsti srci negSrc sh) srci) bRef := by
                    simp [State.addScaledReg, State.setReg, hsd]
        ·
          have hkeep1 :
              extToInt (dst.zslot j) bx
                = extToInt (dst.zslot j) bCur := by
            exact hbx_keep (dst.zslot j)
              (activeDisjoint_symm (hxz dsti j))
              (activeDisjoint_symm (hxz srci j))
          have hkeep2 :
              extToInt (dst.zslot j) bz
                = extToInt (dst.zslot j) bx := by
            exact hbz_keep (dst.zslot j) (hzz j dsti hjd) (hzz j srci hjs)
          calc
            extToInt (dst.zslot j) bz
                = extToInt (dst.zslot j) bx := hkeep2
            _   = extToInt (dst.zslot j) bCur := hkeep1
            _   = evalRowZ (qs := qs) src (σ j) bRef := by
                    simpa [EncodesStateFrom] using hEnc.1.2 j
            _   = evalRowZ (qs := qs) src ((State.addScaledReg σ dsti srci negSrc sh) j) bRef := by
                      simp [State.addScaledReg, State.setReg, hjd]

/-! =========================================================
    Outside-Layout Preservation For One Arithmetic Step
    These lemmas replay the same primitive gate evaluations as the encoding
    lemmas, but only record that registers outside the final layout are unchanged.
========================================================= -/

/-- A compiled left shift preserves every register outside the destination layout. -/
lemma sameOutside_after_shiftL_single
  (qs : QSemantics)
  [RegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ} (hk : 1 < k)
  (phi : Angle)
  (coeff : Fin (q k) → ℚ)
  (dst : LayoutState k)
  (hdisj : LayoutSlotsDisjoint dst)
  (i : Fin k) (m : ℕ)
  (bCur b1 : qs.Basis)
  (hFitX :
    FitsSignedWidth (ExtReg.width (dst.xslot i))
      (((2 : ℤ)^m) * extToInt (dst.xslot i) bCur))
  (hFitZ :
    FitsSignedWidth (ExtReg.width (dst.zslot i))
      (((2 : ℤ)^m) * extToInt (dst.zslot i) bCur))
  (heval :
    qs.eval
      (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst
        [{ op := .shiftL i m, phaseTerm? := none }])
      (qs.ket bCur)
    =
    qs.ket b1) :
  SameOutsideLayout qs dst bCur b1 := by
  rcases layoutSlotsActiveDisjoint hdisj with ⟨hxx, hzz, hxz⟩
  rcases ArithmeticSemantics.eval_ShiftL_ket_exact
      (qs := qs) (r := dst.xslot i) (n := m) (b := bCur) hFitX with
    ⟨bx, hbx_eval, _hbx_val, hbx_keep⟩
  have hz_same_on_bx :
      extToInt (dst.zslot i) bx
        = extToInt (dst.zslot i) bCur := by
    exact hbx_keep (dst.zslot i) (activeDisjoint_symm (hxz i i))
  have hFitZ' :
      FitsSignedWidth (ExtReg.width (dst.zslot i))
        (((2 : ℤ)^m) * extToInt (dst.zslot i) bx) := by
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
    extToInt e bCur
        = extToInt e bx := by
            symm
            exact hbx_keep e (he.1 i)
    _   = extToInt e bz := by
            symm
            exact hbz_keep e (he.2 i)

/-- A compiled right shift preserves every register outside the destination layout. -/
lemma sameOutside_after_shiftR_single
  (qs : QSemantics)
  [RegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ} (hk : 1 < k)
  (phi : Angle)
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
  rcases layoutSlotsActiveDisjoint hdisj with ⟨hxx, hzz, hxz⟩
  cases hreg : Register.shiftR? (σ i) m with
  | none =>
      simp [applyOp?, State.shiftRReg?, hreg] at hstep
  | some r' =>
      have hσ1 : State.setReg σ i r' = σ1 := by
        simpa [applyOp?, State.shiftRReg?, hreg] using hstep
      have hx_pre :
          extToInt (dst.xslot i) bCur
            =
          ((2 : ℤ)^m) * evalRowX (qs := qs) src r' bRef := by
        calc
          extToInt (dst.xslot i) bCur
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
          extToInt (dst.zslot i) bx
            =
          ((2 : ℤ)^m) * evalRowZ (qs := qs) src r' bRef := by
        calc
          extToInt (dst.zslot i) bx
              = extToInt (dst.zslot i) bCur := by
                  exact hbx_keep (dst.zslot i) (activeDisjoint_symm (hxz i i))
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
        extToInt e bCur
            = extToInt e bx := by
                symm
                exact hbx_keep e (he.1 i)
        _   = extToInt e bz := by
                symm
                exact hbz_keep e (he.2 i)

/-- A compiled negation preserves every register outside the destination layout. -/
lemma sameOutside_after_negate_single
  (qs : QSemantics)
  [RegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ} (hk : 1 < k)
  (phi : Angle)
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
  rcases layoutSlotsActiveDisjoint hdisj with ⟨hxx, hzz, hxz⟩
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
    extToInt e bCur
        = extToInt e bx := by
            symm
            exact hbx_keep e (he.1 i)
    _   = extToInt e bz := by
            symm
            exact hbz_keep e (he.2 i)

/-- A compiled scaled addition preserves every register outside the destination layout. -/
lemma sameOutside_after_addScaled_single
  (qs : QSemantics)
  [RegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ} (hk : 1 < k)
  (phi : Angle)
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
  rcases layoutSlotsActiveDisjoint hdisj with ⟨hxx, hzz, hxz⟩
  have hxx_ds : ExtReg.ActiveDisjoint (dst.xslot dsti) (dst.xslot srci) := hxx dsti srci hds
  have hzz_ds : ExtReg.ActiveDisjoint (dst.zslot dsti) (dst.zslot srci) := hzz dsti srci hds
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
    extToInt e bCur
        = extToInt e bx := by
            symm
            exact hbx_keep e (he.1 dsti) (he.1 srci)
    _   = extToInt e bz := by
            symm
            exact hbz_keep e (he.2 dsti) (he.2 srci)


end Shor
