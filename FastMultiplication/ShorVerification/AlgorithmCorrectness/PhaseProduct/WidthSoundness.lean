import FastMultiplication.ShorVerification.AlgorithmCorrectness.PhaseProduct.SupportLemmas

namespace Shor
open Gate
open Operations
open scoped BigOperators

/-!
# Phase-Product Width Soundness

This file proves that the width scan computed from a symbolic phase-product
program is large enough for every symbolic row value reached during execution.
The final theorem feeds directly into allocation and body correctness.
-/

/-! =========================================================
    Section 1: Width-state preservation through symbolic execution
========================================================= -/

lemma widthStateSoundPlus_step
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k)
  (cur : WidthState k)
  (σ σ1 : State k)
  (op : valid_ops k)
  (b : qs.Basis)
  (hstep : applyOp? σ op = some σ1)
  (hfit : WidthStateSoundPlus (qs := qs) src cur σ b) :
  WidthStateSoundPlus
    (qs := qs) src (updateWidthState cur op) σ1 b := by
  rcases hfit with ⟨hx, hz⟩
  cases op with
  | shiftL i n =>
      have hσ1 : σ1 = State.shiftLReg σ i n := by
        simp [applyOp?] at  hstep
        simp[hstep]
      subst hσ1
      constructor
      · intro j
        by_cases hji : i = j
        · subst hji
          have hrow :
              evalRowX (qs := qs) src ((σ i).shiftL n) b
                =
              ((2 : ℤ)^n) * evalRowX (qs := qs) src (σ i) b := by
            simpa using
              (evalRowX_shiftL_raw
                (qs := qs) (src := src) (r := σ i) (m := n) (b := b))
          have hnew :
              FitsSignedWidth (cur.xw i + n + 1)
                (((2 : ℤ)^n) * evalRowX (qs := qs) src (σ i) b) := by
            exact FitsSignedWidth_shiftL_raw (w := cur.xw i) (n := n) (hfit := hx i)
          simpa [updateWidthState, State.shiftLReg, State.setReg, hrow]
            using hnew
        · have hji' : j ≠ i := by omega
          simpa [updateWidthState, State.shiftLReg, State.setReg, hji', Function.update]
            using hx j
      · intro j
        by_cases hji : i = j
        · subst hji
          have hrow :
              evalRowZ (qs := qs) src ((σ i).shiftL n) b
                =
              ((2 : ℤ)^n) * evalRowZ (qs := qs) src (σ i) b := by
            simpa using
              (evalRowZ_shiftL_raw
                (qs := qs) (src := src) (r := σ i) (m := n) (b := b))
          have hnew :
              FitsSignedWidth (cur.zw i + n + 1)
                (((2 : ℤ)^n) * evalRowZ (qs := qs) src (σ i) b) := by
            exact FitsSignedWidth_shiftL_raw (w := cur.zw i) (n := n) (hfit := hz i)
          simpa [updateWidthState, State.shiftLReg, State.setReg, hrow]
            using hnew
        · have hji' : j ≠ i := by omega
          simpa [updateWidthState, State.shiftLReg, State.setReg, hji', Function.update]
            using hz j

  | shiftR i n =>
      cases hreg : Register.shiftR? (σ i) n with
      | none =>
          simp [applyOp?, State.shiftRReg?, hreg] at hstep
      | some r' =>
          have hσ1 : σ1 = State.setReg σ i r' := by
            have:σ.setReg i r' = σ1:=by simpa [applyOp?, State.shiftRReg?, hreg] using hstep
            rw[this]
          subst hσ1
          constructor
          · intro j
            by_cases hji : i = j
            · subst hji
              have hrow :
                  evalRowX (qs := qs) src (σ i) b
                    =
                  ((2 : ℤ)^n) * evalRowX (qs := qs) src r' b := by
                simpa using
                  (evalRowX_shiftR_exact
                    (qs := qs) (src := src) (r := σ i) (r' := r')
                    (m := n) (b := b) hreg)
              have hnew :
                  FitsSignedWidth (cur.xw i - n + 1)
                    (evalRowX (qs := qs) src r' b) := by
                exact FitsSignedWidth_shiftR_of_mul
                  (w := cur.xw i) (n := n)
                  (z := evalRowX (qs := qs) src (σ i) b)
                  (q := evalRowX (qs := qs) src r' b)
                  (hfit := hx i) hrow
              simpa [updateWidthState, State.setReg, Function.update]
                using hnew
            · have hji' : j ≠ i := by omega
              simpa [updateWidthState, State.setReg, hji', Function.update]
                using hx j
          · intro j
            by_cases hji : i = j
            · subst hji
              have hrow :
                  evalRowZ (qs := qs) src (σ i) b
                    =
                  ((2 : ℤ)^n) * evalRowZ (qs := qs) src r' b := by
                simpa using
                  (evalRowZ_shiftR_exact
                    (qs := qs) (src := src) (r := σ i) (r' := r')
                    (m := n) (b := b) hreg)
              have hnew :
                  FitsSignedWidth (cur.zw i - n + 1)
                    (evalRowZ (qs := qs) src r' b) := by
                exact FitsSignedWidth_shiftR_of_mul
                  (w := cur.zw i) (n := n)
                  (z := evalRowZ (qs := qs) src (σ i) b)
                  (q := evalRowZ (qs := qs) src r' b)
                  (hfit := hz i) hrow
              simpa [updateWidthState, State.setReg, Function.update]
                using hnew
            · have hji' : j ≠ i := by omega
              simpa [updateWidthState, State.setReg, hji', Function.update]
                using hz j

  | negate i =>
      have hσ1 : σ1 = State.negateReg σ i := by
        simp [applyOp?] at hstep
        simp[hstep]
      subst hσ1
      constructor
      · intro j
        by_cases hji : i=j
        · subst hji
          have hrow :
              evalRowX (qs := qs) src (Register.negate (σ i)) b
                =
              - evalRowX (qs := qs) src (σ i) b := by
            simpa using
              (evalRowX_negate_raw
                (qs := qs) (src := src) (r := σ i) (b := b))
          have hnew :
              FitsSignedWidth (cur.xw i + 2)
                (- evalRowX (qs := qs) src (σ i) b) := by
            exact FitsSignedWidth_neg_widen (w := cur.xw i) (hfit := hx i)
          simpa [updateWidthState, State.negateReg, State.setReg, Function.update, hrow]
            using hnew
        · have hji' : j ≠ i := by omega
          simpa [updateWidthState, State.negateReg, State.setReg, hji', Function.update]
            using hx j
      · intro j
        by_cases hji : i=j
        · subst hji
          have hrow :
              evalRowZ (qs := qs) src (Register.negate (σ i)) b
                =
              - evalRowZ (qs := qs) src (σ i) b := by
            simpa using
              (evalRowZ_negate_raw
                (qs := qs) (src := src) (r := σ i) (b := b))
          have hnew :
              FitsSignedWidth (cur.zw i + 2)
                (- evalRowZ (qs := qs) src (σ i) b) := by
            exact FitsSignedWidth_neg_widen (w := cur.zw i) (hfit := hz i)
          simpa [updateWidthState, State.negateReg, State.setReg, Function.update, hrow]
            using hnew
        · have hji' : j ≠ i := by omega
          simpa [updateWidthState, State.negateReg, State.setReg, hji', Function.update]
            using hz j

  | addScaled dsti srci negSrc sh =>
      have hσ1 : σ1 = State.addScaledReg σ dsti srci negSrc sh := by
        simp [applyOp?] at hstep
        simp[hstep]
      subst hσ1
      constructor
      · intro j
        by_cases hjd : dsti = j
        · subst hjd
          have hrow :
              evalRowX (qs := qs) src
                (Register.addScaled (σ dsti) (σ srci) negSrc sh) b
                  =
              evalRowX (qs := qs) src (σ dsti) b
                + (if negSrc then (-1 : ℤ) else 1)
                    * ((2 : ℤ)^sh)
                    * evalRowX (qs := qs) src (σ srci) b := by
            simpa using
              (evalRowX_addScaled_raw
                (qs := qs) (src := src)
                (dstReg := σ dsti) (srcReg := σ srci)
                (negSrc := negSrc) (sh := sh) (b := b))
          have hnew :
              FitsSignedWidth (max (cur.xw dsti) (cur.xw srci + sh) + 2)
                (evalRowX (qs := qs) src (σ dsti) b
                  + (if negSrc then (-1 : ℤ) else 1)
                      * ((2 : ℤ)^sh)
                      * evalRowX (qs := qs) src (σ srci) b) := by
            exact FitsSignedWidth_addScaled_widen
              (wd := cur.xw dsti) (ws := cur.xw srci) (sh := sh)
              (negSrc := negSrc) (hdst := hx dsti) (hsrc := hx srci)
          simp [updateWidthState, State.addScaledReg, State.setReg, Function.update, hrow] at *
          rw[add_comm,← add_assoc, add_comm];simp[hnew]
        · have hjd' : j ≠ dsti := by omega
          simpa [updateWidthState, State.addScaledReg, State.setReg, hjd', Function.update]
            using hx j
      · intro j
        by_cases hjd : dsti = j
        · subst hjd
          have hrow :
              evalRowZ (qs := qs) src
                (Register.addScaled (σ dsti) (σ srci) negSrc sh) b
                  =
              evalRowZ (qs := qs) src (σ dsti) b
                + (if negSrc then (-1 : ℤ) else 1)
                    * ((2 : ℤ)^sh)
                    * evalRowZ (qs := qs) src (σ srci) b := by
            simpa using
              (evalRowZ_addScaled_raw
                (qs := qs) (src := src)
                (dstReg := σ dsti) (srcReg := σ srci)
                (negSrc := negSrc) (sh := sh) (b := b))
          have hnew :
              FitsSignedWidth (max (cur.zw dsti) (cur.zw srci + sh) + 2)
                (evalRowZ (qs := qs) src (σ dsti) b
                  + (if negSrc then (-1 : ℤ) else 1)
                      * ((2 : ℤ)^sh)
                      * evalRowZ (qs := qs) src (σ srci) b) := by
            exact FitsSignedWidth_addScaled_widen
              (wd := cur.zw dsti) (ws := cur.zw srci) (sh := sh)
              (negSrc := negSrc) (hdst := hz dsti) (hsrc := hz srci)
          simp [updateWidthState, State.addScaledReg, State.setReg, Function.update, hrow] at *
          rw[add_comm,← add_assoc, add_comm];simp[hnew]
        · have hjd' : j ≠ dsti := by omega
          simpa [updateWidthState, State.addScaledReg, State.setReg, hjd', Function.update]
            using hz j

  | phaseProduct i =>
      have hσ1 : σ1 = σ := by
        simp [applyOp?] at hstep
        simp[hstep]
      subst hσ1
      simp [updateWidthState,WidthStateSoundPlus] at *
      simp_all

/-- Folded run preservation of the proof-only invariant. -/
lemma widthStateSoundPlus_run
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k)
  (cur : WidthState k)
  (σ σf : State k)
  (ops : Prog k)
  (b : qs.Basis)
  (hrun : run? ops σ = some σf)
  (hfit : WidthStateSoundPlus (qs := qs) src cur σ b) :
  WidthStateSoundPlus
    (qs := qs)
    src
    (ops.foldl updateWidthState cur)
    σf
    b := by
  induction ops generalizing cur σ σf with
  | nil =>
      simp
      simp at hrun;aesop
  | cons op ops ih =>
      cases hstep : applyOp? σ op with
      | none =>
          simp [run?, hstep] at hrun
      | some σ1 =>
          have hrunTail : run? ops σ1 = some σf := by
            simpa [run?, hstep] using hrun
          have hfit1 :
              WidthStateSoundPlus (qs := qs) src (updateWidthState cur op) σ1 b := by
            exact widthStateSoundPlus_step
              (qs := qs) (src := src) (cur := cur)
              (σ := σ) (σ1 := σ1) (op := op) (b := b)
              hstep hfit
          simpa [List.foldl] using
            ih (cur := updateWidthState cur op) (σ := σ1) (σf := σf) hrunTail hfit1

/-! =========================================================
    Section 2: Prefix/scan bound lemmas
========================================================= -/

/-- Prefix-folded x-widths are bounded by the full scan result. -/
lemma prefix_foldl_updateWidthState_x_le_scanAux
  {k : ℕ} (i : Fin k) :
  ∀ (pre rest : List (valid_ops k)) (cur : WidthState k) (mx : NeededWidths k),
    cur.xw i ≤ mx.xneed i →
    (pre.foldl updateWidthState cur).xw i
      ≤
    (scanNeededWidthsAux cur mx (pre ++ rest)).xneed i
  | [], rest, cur, mx, hcur => by
      exact le_trans hcur (scanNeededWidthsAux_x_ge (i := i) rest cur mx)
  | op :: pre, rest, cur, mx, hcur => by
      let cur' := updateWidthState cur op
      let mx' := mergeNeededWidths mx (widthsOfState cur')
      have hcur' : cur'.xw i ≤ mx'.xneed i := by
        simp [cur', mx', mergeNeededWidths, widthsOfState]
      simpa [scanNeededWidthsAux, cur', mx'] using
        prefix_foldl_updateWidthState_x_le_scanAux
          (i := i) pre rest cur' mx' hcur'

/-- Prefix-folded z-widths are bounded by the full scan result. -/
lemma prefix_foldl_updateWidthState_z_le_scanAux
  {k : ℕ} (i : Fin k) :
  ∀ (pre rest : List (valid_ops k)) (cur : WidthState k) (mx : NeededWidths k),
    cur.zw i ≤ mx.zneed i →
    (pre.foldl updateWidthState cur).zw i
      ≤
    (scanNeededWidthsAux cur mx (pre ++ rest)).zneed i
  | [], rest, cur, mx, hcur => by
      exact le_trans hcur (scanNeededWidthsAux_z_ge (i := i) rest cur mx)
  | op :: pre, rest, cur, mx, hcur => by
      let cur' := updateWidthState cur op
      let mx' := mergeNeededWidths mx (widthsOfState cur')
      have hcur' : cur'.zw i ≤ mx'.zneed i := by
        simp [cur', mx', mergeNeededWidths, widthsOfState]
      simpa [scanNeededWidthsAux, cur', mx'] using
        prefix_foldl_updateWidthState_z_le_scanAux
          (i := i) pre rest cur' mx' hcur'

lemma prefix_foldl_updateWidthState_x_le_scanNeeded
  {k : ℕ}
  (x z : ExtReg) (ops pre rest : Prog k) (i : Fin k)
  (hops : ops = pre ++ rest) :
  (pre.foldl updateWidthState (initWidthState x z k)).xw i
    ≤
  (scanNeededWidths x z ops).xneed i := by
  rw [hops, scanNeededWidths_eq_aux]
  exact prefix_foldl_updateWidthState_x_le_scanAux
    (i := i)
    pre rest
    (initWidthState x z k)
    (widthsOfState (initWidthState x z k))
    (by simp [widthsOfState])

lemma prefix_foldl_updateWidthState_z_le_scanNeeded
  {k : ℕ}
  (x z : ExtReg) (ops pre rest : Prog k) (i : Fin k)
  (hops : ops = pre ++ rest) :
  (pre.foldl updateWidthState (initWidthState x z k)).zw i
    ≤
  (scanNeededWidths x z ops).zneed i := by
  rw [hops, scanNeededWidths_eq_aux]
  exact prefix_foldl_updateWidthState_z_le_scanAux
    (i := i)
    pre rest
    (initWidthState x z k)
    (widthsOfState (initWidthState x z k))
    (by simp [widthsOfState])

lemma widthStateSoundPlus_start_state
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [ExtRegEncoding qs.Basis]
  [ExtRegSplitSemantics qs.Basis]
  [GateSemanticsFacts qs]
  {k : ℕ}
  (x z : ExtReg)
  (b : qs.Basis) :
  WidthStateSoundPlus
    (qs := qs)
    (initSignedLayoutState (Basis := qs.Basis) x z k)
    (initWidthState x z k)
    State.start_state
    b := by
  constructor
  · intro i
    let st : LayoutState k :=
      initSignedLayoutState (Basis := qs.Basis) x z k

    have hfit :
        FitsSignedWidth (ExtReg.width (st.xslot i) + 1)
          (sourceChunkXInt (qs := qs) st i b) :=
      sourceChunkXInt_fits_width_succ qs st i b

    have hwidth :
        ExtReg.width (st.xslot i) =
          (initWidthState x z k).xw i := by
      simpa [st] using
        stInit_xslot_width
          (Basis := qs.Basis) x z i

    have hrow :
        evalRowX (qs := qs) st (State.start_state i) b =
          sourceChunkXInt (qs := qs) st i b := by
      simpa using
        evalRowX_start_state
          (qs := qs) st i b

    rw [hwidth] at hfit
    rw [← hrow] at hfit
    simpa [st] using hfit

  · intro i
    let st : LayoutState k :=
      initSignedLayoutState (Basis := qs.Basis) x z k

    have hfit :
        FitsSignedWidth (ExtReg.width (st.zslot i) + 1)
          (sourceChunkZInt (qs := qs) st i b) :=
      sourceChunkZInt_fits_width_succ qs st i b

    have hwidth :
        ExtReg.width (st.zslot i) =
          (initWidthState x z k).zw i := by
      simpa [st] using
        stInit_zslot_width
          (Basis := qs.Basis) x z i

    have hrow :
        evalRowZ (qs := qs) st (State.start_state i) b =
          sourceChunkZInt (qs := qs) st i b := by
      simpa using
        evalRowZ_start_state
          (qs := qs) st i b

    rw [hwidth] at hfit
    rw [← hrow] at hfit
    simpa [st] using hfit

/-! =========================================================
    Section 3: Final theorem
========================================================= -/

lemma allocated_widths_sound
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [ExtRegEncoding qs.Basis]
  [ExtRegSplitSemantics qs.Basis]
  [GateSemanticsFacts qs]
  {k : ℕ}
  (x z : ExtReg)
  (ops : Prog k)
  (b : qs.Basis) :
  let src := initSignedLayoutState (Basis := qs.Basis) x z k
  let dst := targetSignedLayoutState
    (Basis := qs.Basis) x z k (scanNeededWidths x z ops)
  ∀ {σ : State k},
    (∃ pre rest,
      ops = pre ++ rest ∧
      run? pre State.start_state = some σ) →
    (∀ i : Fin k,
      FitsSignedWidth (ExtReg.width (dst.xslot i))
        (evalRowX (qs := qs) src (σ i) b)) ∧
    (∀ i : Fin k,
      FitsSignedWidth (ExtReg.width (dst.zslot i))
        (evalRowZ (qs := qs) src (σ i) b)) := by
  dsimp
  intro σ hprefix
  rcases hprefix with ⟨pre, rest, hops, hrun⟩

  let src : LayoutState k :=
    initSignedLayoutState (Basis := qs.Basis) x z k
  let dst : LayoutState k :=
    targetSignedLayoutState
      (Basis := qs.Basis) x z k (scanNeededWidths x z ops)

  let cur0 : WidthState k := initWidthState x z k
  let curPre : WidthState k := pre.foldl updateWidthState cur0

  have hstart :
      WidthStateSoundPlus
        (qs := qs)
        src
        cur0
        State.start_state
        b := by
    simpa [src, cur0] using
      widthStateSoundPlus_start_state
        (qs := qs) (x := x) (z := z) (b := b)

  have hpre :
      WidthStateSoundPlus
        (qs := qs)
        src
        curPre
        σ
        b := by
    simpa [src, cur0, curPre] using
      widthStateSoundPlus_run
        (qs := qs)
        (src := src)
        (cur := cur0)
        (σ := State.start_state)
        (σf := σ)
        (ops := pre)
        (b := b)
        hrun
        hstart

  rcases hpre with ⟨hpreX, hpreZ⟩

  constructor
  · intro i
    have hcur :
        curPre.xw i + 1
          ≤ commonNeededWidth (scanNeededWidths x z ops) := by
      have hprefix_le :
          curPre.xw i ≤ (scanNeededWidths x z ops).xneed i := by
        simpa [curPre, cur0] using
          prefix_foldl_updateWidthState_x_le_scanNeeded
            (x := x) (z := z)
            (ops := ops) (pre := pre) (rest := rest)
            (i := i) hops
      have hW :
          (scanNeededWidths x z ops).xneed i + 1
            ≤ commonNeededWidth (scanNeededWidths x z ops) :=
        commonNeededWidth_ge_xneed (scanNeededWidths x z ops) i
      omega

    have hdst :
        ExtReg.width (dst.xslot i)
          =
        commonNeededWidth (scanNeededWidths x z ops) := by
      simpa [dst] using
        targetSignedLayoutState_xslot_width_scan
          (Basis := qs.Basis) x z ops i

    exact FitsSignedWidth_mono
      (by rw [hdst]; exact hcur)
      (hpreX i)

  · intro i
    have hcur :
        curPre.zw i + 1
          ≤ commonNeededWidth (scanNeededWidths x z ops) := by
      have hprefix_le :
          curPre.zw i ≤ (scanNeededWidths x z ops).zneed i := by
        simpa [curPre, cur0] using
          prefix_foldl_updateWidthState_z_le_scanNeeded
            (x := x) (z := z)
            (ops := ops) (pre := pre) (rest := rest)
            (i := i) hops
      have hW :
          (scanNeededWidths x z ops).zneed i + 1
            ≤ commonNeededWidth (scanNeededWidths x z ops) :=
        commonNeededWidth_ge_zneed (scanNeededWidths x z ops) i
      omega

    have hdst :
        ExtReg.width (dst.zslot i)
          =
        commonNeededWidth (scanNeededWidths x z ops) := by
      simpa [dst] using
        targetSignedLayoutState_zslot_width_scan
          (Basis := qs.Basis) x z ops i

    exact FitsSignedWidth_mono
      (by rw [hdst]; exact hcur)
      (hpreZ i)

end Shor
