import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.Support

/-!
# Phase-Product Width Soundness

This file proves that the width scan computed from a symbolic phase-product
program is large enough for every symbolic row value reached during execution.
The proof proceeds from one-step preservation, through scan domination for
prefixes, to the final allocation-facing soundness theorem.

The last section proves the same for the exact width (`allocated_widths_sound_exact`,
by interval arithmetic over the limb box) and states it for either width rule
(`allocated_widths_sound_by`).
-/

namespace Shor
open Gate
open Operations
open scoped BigOperators

/-! =========================================================
    Scanner Unfolding

    The public scanner is a wrapper around the auxiliary fold; this local
    equation keeps later width proofs pointed at the fold form.
========================================================= -/

/-- Unfolding lemma for the public width scanner. -/
lemma scanNeededWidths_eq_aux {k : ℕ} (x z : ExtReg) (ops : List (valid_ops k)) :
  scanNeededWidths x z ops = scanNeededWidthsAux (initWidthState x z k) (widthsOfState (initWidthState x z k)) ops := by
  simp [scanNeededWidths]

/-! =========================================================
    One-Step Symbolic Width Preservation

    `WidthStateSoundPlus` tracks a proof-only signed-fit invariant for the
    symbolic row values of every register. This section proves that each
    `valid_ops` constructor preserves that invariant while `updateWidthState`
    performs the matching width transition.
========================================================= -/

/-- One symbolic operation preserves signed-fit soundness under the matching width update. -/
lemma widthStateSoundPlus_step
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k)
  (cur : WidthState k)
  (σ σ1 : State k)
  (op : valid_ops k)
  (b : qs.Basis)
  (hstep : applyOp? σ op = some σ1)
  (hfit : WidthStateSoundPlus (qs := qs) src cur σ b) :
  WidthStateSoundPlus (qs := qs) src (updateWidthState cur op) σ1 b := by
  rcases hfit with ⟨hx, hz⟩
  cases op with
  | shiftL i n =>
      have hσ1 : σ1 = State.shiftLReg σ i n := by simp [applyOp?] at hstep; simp [hstep]
      subst hσ1
      constructor
      · intro j
        by_cases hji : i = j
        · subst hji
          have hrow : evalRowX (qs := qs) src ((σ i).shiftL n) b
              = ((2 : ℤ)^n) * evalRowX (qs := qs) src (σ i) b := by
            simpa using (evalRowX_shiftL_raw (qs := qs) (src := src) (r := σ i) (m := n) (b := b))
          have hnew : FitsSignedWidth (cur.xw i + n + 1)
              (((2 : ℤ)^n) * evalRowX (qs := qs) src (σ i) b) := by
            exact FitsSignedWidth_shiftL_raw (w := cur.xw i) (n := n) (hfit := hx i)
          simpa [updateWidthState, State.shiftLReg, State.setReg, hrow] using hnew
        · have hji' : j ≠ i := by omega
          simpa [updateWidthState, State.shiftLReg, State.setReg, hji', Function.update] using hx j
      · intro j
        by_cases hji : i = j
        · subst hji
          have hrow : evalRowZ (qs := qs) src ((σ i).shiftL n) b
              = ((2 : ℤ)^n) * evalRowZ (qs := qs) src (σ i) b := by
            simpa using (evalRowZ_shiftL_raw (qs := qs) (src := src) (r := σ i) (m := n) (b := b))
          have hnew : FitsSignedWidth (cur.zw i + n + 1)
              (((2 : ℤ)^n) * evalRowZ (qs := qs) src (σ i) b) := by
            exact FitsSignedWidth_shiftL_raw (w := cur.zw i) (n := n) (hfit := hz i)
          simpa [updateWidthState, State.shiftLReg, State.setReg, hrow] using hnew
        · have hji' : j ≠ i := by omega
          simpa [updateWidthState, State.shiftLReg, State.setReg, hji', Function.update] using hz j

  | shiftR i n =>
      cases hreg : Register.shiftR? (σ i) n with
      | none =>
          simp [applyOp?, State.shiftRReg?, hreg] at hstep
      | some r' =>
          have hσ1 : σ1 = State.setReg σ i r' := by
            have h : σ.setReg i r' = σ1 := by
              simpa [applyOp?, State.shiftRReg?, hreg] using hstep
            rw [h]
          subst hσ1
          constructor
          · intro j
            by_cases hji : i = j
            · subst hji
              have hrow : evalRowX (qs := qs) src (σ i) b
                  = ((2 : ℤ)^n) * evalRowX (qs := qs) src r' b := by
                simpa using
                  (evalRowX_shiftR_exact
                    (qs := qs) (src := src)
                    (r := σ i) (r' := r')
                    (m := n) (b := b) hreg)
              have hnew : FitsSignedWidth (cur.xw i - n + 1)
                  (evalRowX (qs := qs) src r' b) := by
                exact FitsSignedWidth_shiftR_of_mul
                  (w := cur.xw i)
                  (n := n)
                  (z := evalRowX (qs := qs) src (σ i) b)
                  (q := evalRowX (qs := qs) src r' b)
                  (hfit := hx i)
                  hrow
              simpa [updateWidthState, State.setReg, Function.update] using hnew
            · have hji' : j ≠ i := by omega
              simpa [updateWidthState, State.setReg, hji', Function.update] using hx j
          · intro j
            by_cases hji : i = j
            · subst hji
              have hrow : evalRowZ (qs := qs) src (σ i) b
                  = ((2 : ℤ)^n) * evalRowZ (qs := qs) src r' b := by
                simpa using
                  (evalRowZ_shiftR_exact
                    (qs := qs) (src := src)
                    (r := σ i) (r' := r')
                    (m := n) (b := b) hreg)
              have hnew : FitsSignedWidth (cur.zw i - n + 1)
                  (evalRowZ (qs := qs) src r' b) := by
                exact FitsSignedWidth_shiftR_of_mul
                  (w := cur.zw i)
                  (n := n)
                  (z := evalRowZ (qs := qs) src (σ i) b)
                  (q := evalRowZ (qs := qs) src r' b)
                  (hfit := hz i)
                  hrow
              simpa [updateWidthState, State.setReg, Function.update] using hnew
            · have hji' : j ≠ i := by omega
              simpa [updateWidthState, State.setReg, hji', Function.update] using hz j

  | negate i =>
      have hσ1 : σ1 = State.negateReg σ i := by simp [applyOp?] at hstep; simp [hstep]
      subst hσ1
      constructor
      · intro j
        by_cases hji : i = j
        · subst hji
          have hrow : evalRowX (qs := qs) src (Register.negate (σ i)) b
              = -evalRowX (qs := qs) src (σ i) b := by
            simpa using (evalRowX_negate_raw (qs := qs) (src := src) (r := σ i) (b := b))
          have hnew : FitsSignedWidth (cur.xw i + 2)
              (-evalRowX (qs := qs) src (σ i) b) := by
            exact FitsSignedWidth_neg_widen (w := cur.xw i) (hfit := hx i)
          simpa [updateWidthState, State.negateReg, State.setReg, Function.update, hrow] using hnew
        · have hji' : j ≠ i := by omega
          simpa [updateWidthState, State.negateReg, State.setReg, hji', Function.update] using hx j
      · intro j
        by_cases hji : i = j
        · subst hji
          have hrow : evalRowZ (qs := qs) src (Register.negate (σ i)) b
              = -evalRowZ (qs := qs) src (σ i) b := by
            simpa using (evalRowZ_negate_raw (qs := qs) (src := src) (r := σ i) (b := b))
          have hnew : FitsSignedWidth (cur.zw i + 2)
              (-evalRowZ (qs := qs) src (σ i) b) := by
            exact FitsSignedWidth_neg_widen (w := cur.zw i) (hfit := hz i)
          simpa [updateWidthState, State.negateReg, State.setReg, Function.update, hrow] using hnew
        · have hji' : j ≠ i := by omega
          simpa [updateWidthState, State.negateReg, State.setReg, hji', Function.update] using hz j

  | addScaled dsti srci negSrc sh =>
      have hσ1 : σ1 = State.addScaledReg σ dsti srci negSrc sh := by
        simp [applyOp?] at hstep; simp [hstep]
      subst hσ1
      constructor
      · intro j
        by_cases hjd : dsti = j
        · subst hjd
          have hrow :
              evalRowX (qs := qs) src
                (Register.addScaled
                  (σ dsti) (σ srci) negSrc sh) b
                =
              evalRowX (qs := qs) src (σ dsti) b
                + (if negSrc then (-1 : ℤ) else 1)
                    * ((2 : ℤ)^sh)
                    * evalRowX (qs := qs) src (σ srci) b := by
            simpa using
              (evalRowX_addScaled_raw
                (qs := qs)
                (src := src)
                (dstReg := σ dsti)
                (srcReg := σ srci)
                (negSrc := negSrc)
                (sh := sh)
                (b := b))
          have hnew :
              FitsSignedWidth
                (max (cur.xw dsti) (cur.xw srci + sh) + 2)
                (evalRowX (qs := qs) src (σ dsti) b
                  + (if negSrc then (-1 : ℤ) else 1)
                      * ((2 : ℤ)^sh)
                      * evalRowX (qs := qs) src (σ srci) b) := by
            exact FitsSignedWidth_addScaled_widen
              (wd := cur.xw dsti)
              (ws := cur.xw srci)
              (sh := sh)
              (negSrc := negSrc)
              (hdst := hx dsti)
              (hsrc := hx srci)
          simp [updateWidthState, State.addScaledReg, State.setReg, Function.update, hrow] at *
          rw [add_comm, ← add_assoc, add_comm]
          simp [hnew]
        · have hjd' : j ≠ dsti := by omega
          simpa [updateWidthState, State.addScaledReg, State.setReg, hjd', Function.update] using hx j
      · intro j
        by_cases hjd : dsti = j
        · subst hjd
          have hrow :
              evalRowZ (qs := qs) src
                (Register.addScaled
                  (σ dsti) (σ srci) negSrc sh) b
                =
              evalRowZ (qs := qs) src (σ dsti) b
                + (if negSrc then (-1 : ℤ) else 1)
                    * ((2 : ℤ)^sh)
                    * evalRowZ (qs := qs) src (σ srci) b := by
            simpa using
              (evalRowZ_addScaled_raw
                (qs := qs)
                (src := src)
                (dstReg := σ dsti)
                (srcReg := σ srci)
                (negSrc := negSrc)
                (sh := sh)
                (b := b))
          have hnew :
              FitsSignedWidth
                (max (cur.zw dsti) (cur.zw srci + sh) + 2)
                (evalRowZ (qs := qs) src (σ dsti) b
                  + (if negSrc then (-1 : ℤ) else 1)
                      * ((2 : ℤ)^sh)
                      * evalRowZ (qs := qs) src (σ srci) b) := by
            exact FitsSignedWidth_addScaled_widen
              (wd := cur.zw dsti)
              (ws := cur.zw srci)
              (sh := sh)
              (negSrc := negSrc)
              (hdst := hz dsti)
              (hsrc := hz srci)
          simp [updateWidthState, State.addScaledReg, State.setReg, Function.update, hrow] at *
          rw [add_comm, ← add_assoc, add_comm]
          simp [hnew]
        · have hjd' : j ≠ dsti := by omega
          simpa [updateWidthState, State.addScaledReg, State.setReg, hjd', Function.update] using hz j

  | phaseProduct i =>
      have hσ1 : σ1 = σ := by simp [applyOp?] at hstep; simp [hstep]
      subst hσ1
      simp [updateWidthState, WidthStateSoundPlus] at *
      simp_all

/-- Folded run preservation of the proof-only invariant. -/
lemma widthStateSoundPlus_run
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k)
  (cur : WidthState k)
  (σ σf : State k)
  (ops : Prog k)
  (b : qs.Basis)
  (hrun : run? ops σ = some σf)
  (hfit : WidthStateSoundPlus (qs := qs) src cur σ b) :
  WidthStateSoundPlus (qs := qs) src (ops.foldl updateWidthState cur) σf b := by
  induction ops generalizing cur σ σf with
  | nil =>
      simp; simp at hrun; aesop
  | cons op ops ih =>
      cases hstep : applyOp? σ op with
      | none =>
          simp [run?, hstep] at hrun
      | some σ1 =>
          have hrunTail : run? ops σ1 = some σf := by
            simpa [run?, hstep] using hrun
          have hfit1 : WidthStateSoundPlus (qs := qs) src (updateWidthState cur op) σ1 b := by
            exact widthStateSoundPlus_step
              (qs := qs)
              (src := src)
              (cur := cur)
              (σ := σ)
              (σ1 := σ1)
              (op := op)
              (b := b)
              hstep
              hfit
          simpa [List.foldl] using
            ih
              (cur := updateWidthState cur op)
              (σ := σ1)
              (σf := σf)
              hrunTail
              hfit1

/-! =========================================================
    Prefix Widths Are Dominated By The Full Scan

    These lemmas compare an arbitrary executed prefix against the complete
    `scanNeededWidths` result. They are the bridge from local step preservation
    to a final fixed target layout chosen before execution.
========================================================= -/

/-- Prefix-folded x-widths are bounded by the full scan result. -/
lemma prefix_foldl_updateWidthState_x_le_scanAux
  {k : ℕ}
  (i : Fin k) :
  ∀ (pre rest : List (valid_ops k))
    (cur : WidthState k)
    (mx : NeededWidths k),
    cur.xw i ≤ mx.xneed i →
    (pre.foldl updateWidthState cur).xw i ≤ (scanNeededWidthsAux cur mx (pre ++ rest)).xneed i
  | [], rest, cur, mx, hcur => by
      exact le_trans hcur (scanNeededWidthsAux_x_ge (i := i) rest cur mx)
  | op :: pre, rest, cur, mx, hcur => by
      let cur' := updateWidthState cur op
      let mx' := mergeNeededWidths mx (widthsOfState cur')
      have hcur' : cur'.xw i ≤ mx'.xneed i := by
        simp [cur', mx', mergeNeededWidths, widthsOfState]
      simpa [scanNeededWidthsAux, cur', mx'] using
        prefix_foldl_updateWidthState_x_le_scanAux
          (i := i)
          pre
          rest
          cur'
          mx'
          hcur'

/-- Prefix-folded z-widths are bounded by the full scan result. -/
lemma prefix_foldl_updateWidthState_z_le_scanAux
  {k : ℕ}
  (i : Fin k) :
  ∀ (pre rest : List (valid_ops k))
    (cur : WidthState k)
    (mx : NeededWidths k),
    cur.zw i ≤ mx.zneed i →
    (pre.foldl updateWidthState cur).zw i ≤ (scanNeededWidthsAux cur mx (pre ++ rest)).zneed i
  | [], rest, cur, mx, hcur => by
      exact le_trans hcur (scanNeededWidthsAux_z_ge (i := i) rest cur mx)
  | op :: pre, rest, cur, mx, hcur => by
      let cur' := updateWidthState cur op
      let mx' := mergeNeededWidths mx (widthsOfState cur')
      have hcur' : cur'.zw i ≤ mx'.zneed i := by
        simp [cur', mx', mergeNeededWidths, widthsOfState]
      simpa [scanNeededWidthsAux, cur', mx'] using
        prefix_foldl_updateWidthState_z_le_scanAux
          (i := i)
          pre
          rest
          cur'
          mx'
          hcur'

/-- Prefix-folded `x` widths are bounded by the public scanner. -/
lemma prefix_foldl_updateWidthState_x_le_scanNeeded
  {k : ℕ}
  (x z : ExtReg)
  (ops pre rest : Prog k)
  (i : Fin k)
  (hops : ops = pre ++ rest) :
  (pre.foldl updateWidthState (initWidthState x z k)).xw i ≤ (scanNeededWidths x z ops).xneed i := by
  rw [hops, scanNeededWidths_eq_aux]
  exact prefix_foldl_updateWidthState_x_le_scanAux
    (i := i)
    pre
    rest
    (initWidthState x z k)
    (widthsOfState (initWidthState x z k))
    (by simp [widthsOfState])

/-- Prefix-folded `z` widths are bounded by the public scanner. -/
lemma prefix_foldl_updateWidthState_z_le_scanNeeded
  {k : ℕ}
  (x z : ExtReg)
  (ops pre rest : Prog k)
  (i : Fin k)
  (hops : ops = pre ++ rest) :
  (pre.foldl updateWidthState (initWidthState x z k)).zw i ≤ (scanNeededWidths x z ops).zneed i := by
  rw [hops, scanNeededWidths_eq_aux]
  exact prefix_foldl_updateWidthState_z_le_scanAux
    (i := i)
    pre
    rest
    (initWidthState x z k)
    (widthsOfState (initWidthState x z k))
    (by simp [widthsOfState])

/-- Initial chunks fit the symbolic initial width state when read from the start state. -/
lemma widthStateSoundPlus_start_state
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  {k : ℕ}
  {x z : ExtReg}
  (layout : Gate.PhaseProductLayout x z k)
  (b : qs.Basis) :
  WidthStateSoundPlus (qs := qs) (initSignedLayoutState layout) (initWidthState x z k) State.start_state b := by
  constructor
  · intro i
    let st : LayoutState k := initSignedLayoutState layout

    have hfit : FitsSignedWidth (ExtReg.width (st.xslot i) + 1) (sourceChunkXInt (qs := qs) st i b) := by
      unfold sourceChunkXInt
      by_cases htop : isTopChunk i
      · simp [htop]
        exact extToInt_fits_width_succ qs (st.xslot i) b
      · simp [htop]
        exact FitsSignedWidth_of_nonneg_lt_pow (ExtReg.toNat_lt (st.xslot i) b)

    have hwidth : ExtReg.width (st.xslot i) = (initWidthState x z k).xw i := by
      simpa [st] using stInit_xslot_width layout i

    have hrow : evalRowX (qs := qs) st (State.start_state i) b = sourceChunkXInt (qs := qs) st i b := by
      simpa using evalRowX_start_state (qs := qs) st i b

    rw [hwidth] at hfit
    rw [← hrow] at hfit
    simpa [st] using hfit

  · intro i
    let st : LayoutState k := initSignedLayoutState layout

    have hfit : FitsSignedWidth (ExtReg.width (st.zslot i) + 1) (sourceChunkZInt (qs := qs) st i b) := by
      unfold sourceChunkZInt
      by_cases htop : isTopChunk i
      · simp [htop]
        exact extToInt_fits_width_succ qs (st.zslot i) b
      · simp [htop]
        exact FitsSignedWidth_of_nonneg_lt_pow (ExtReg.toNat_lt (st.zslot i) b)

    have hwidth : ExtReg.width (st.zslot i) = (initWidthState x z k).zw i := by
      simpa [st] using stInit_zslot_width layout i

    have hrow : evalRowZ (qs := qs) st (State.start_state i) b = sourceChunkZInt (qs := qs) st i b := by
      simpa using evalRowZ_start_state (qs := qs) st i b

    rw [hwidth] at hfit
    rw [← hrow] at hfit
    simpa [st] using hfit

/-! =========================================================
    Allocation-Facing Width Soundness

    The final theorem packages the scan result into the exact form used by
    allocation and body correctness: every state reachable by a prefix has row
    values that fit in the already-grown target slots.
========================================================= -/

/-- Every prefix-reachable symbolic state fits in the target layout chosen by the full scan. -/
lemma allocated_widths_sound
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  {k : ℕ}
  {x z : ExtReg}
  (layout : Gate.PhaseProductLayout x z k)
  (ops : Prog k)
  (hcap : (initSignedLayoutState layout).CanGrowToNeeds (scanNeededWidths x z ops))
  (b : qs.Basis) :
  let src := initSignedLayoutState layout
  let dst :=  targetSignedLayoutState src (scanNeededWidths x z ops)
  ∀ {σ : State k},
    (∃ pre rest, ops = pre ++ rest ∧ run? pre State.start_state = some σ) →
    (∀ i : Fin k, FitsSignedWidth (ExtReg.width (dst.xslot i))
      (evalRowX (qs := qs) src (σ i) b)) ∧
    (∀ i : Fin k, FitsSignedWidth (ExtReg.width (dst.zslot i))
        (evalRowZ (qs := qs) src (σ i) b)) := by
  dsimp
  intro σ hprefix
  rcases hprefix with ⟨pre, rest, hops, hrun⟩

  let src : LayoutState k := initSignedLayoutState layout

  let dst : LayoutState k := targetSignedLayoutState src (scanNeededWidths x z ops)

  let cur0 : WidthState k := initWidthState x z k

  let curPre : WidthState k := pre.foldl updateWidthState cur0

  have hstart : WidthStateSoundPlus (qs := qs) src cur0 State.start_state b := by
    simpa [src, cur0] using widthStateSoundPlus_start_state (qs := qs) layout b

  have hpre : WidthStateSoundPlus (qs := qs) src curPre σ b := by
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
    have hcur : curPre.xw i + 1 ≤ commonNeededWidth (scanNeededWidths x z ops) := by
      have hprefix_le : curPre.xw i ≤ (scanNeededWidths x z ops).xneed i := by
        simpa [curPre, cur0] using
          prefix_foldl_updateWidthState_x_le_scanNeeded
            (x := x)
            (z := z)
            (ops := ops)
            (pre := pre)
            (rest := rest)
            (i := i)
            hops

      have hW : (scanNeededWidths x z ops).xneed i + 1 ≤ commonNeededWidth (scanNeededWidths x z ops) :=
        commonNeededWidth_ge_xneed (scanNeededWidths x z ops) i

      omega

    have hdst : ExtReg.width (dst.xslot i) = commonNeededWidth (scanNeededWidths x z ops) := by
      simpa [dst] using targetSignedLayoutState_xslot_width_scan layout ops i hcap

    exact FitsSignedWidth_mono
      (by
        rw [hdst]
        exact hcur)
      (hpreX i)

  · intro i
    have hcur : curPre.zw i + 1 ≤ commonNeededWidth (scanNeededWidths x z ops) := by
      have hprefix_le : curPre.zw i ≤ (scanNeededWidths x z ops).zneed i := by
        simpa [curPre, cur0] using
          prefix_foldl_updateWidthState_z_le_scanNeeded
            (x := x)
            (z := z)
            (ops := ops)
            (pre := pre)
            (rest := rest)
            (i := i)
            hops

      have hW : (scanNeededWidths x z ops).zneed i + 1 ≤ commonNeededWidth (scanNeededWidths x z ops) :=
        commonNeededWidth_ge_zneed (scanNeededWidths x z ops) i

      omega

    have hdst : ExtReg.width (dst.zslot i) = commonNeededWidth (scanNeededWidths x z ops) := by
      simpa [dst] using targetSignedLayoutState_zslot_width_scan layout ops i hcap

    exact FitsSignedWidth_mono
      (by
        rw [hdst]
        exact hcur)
      (hpreZ i)

/-! =========================================================
    Width soundness at the exact width

    The source chunks lie in the limb box, so every reachable row's value lies
    in its interval, and the exact width covers that interval.
========================================================= -/

/-- `tcDecodeWidth t` reads a `t`-bit pattern into the signed `t`-bit range
(`[0, 0]` at `t = 0`). -/
lemma tcDecodeWidth_exactBox (t n : ℕ) (h : n < 2 ^ t) :
    (if t = 0 then (0 : ℤ) else -(2 : ℤ) ^ (t - 1)) ≤ tcDecodeWidth t n ∧
    tcDecodeWidth t n ≤ (if t = 0 then (0 : ℤ) else (2 : ℤ) ^ (t - 1) - 1) := by
  cases t with
  | zero => simp [tcDecodeWidth]
  | succ s =>
      simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, tcDecodeWidth]
      have hp : (0 : ℤ) < (2 : ℤ) ^ s := by positivity
      have h2 : ((2 ^ (s + 1) : ℕ) : ℤ) = 2 * (2 : ℤ) ^ s := by push_cast; ring
      have hn : ((n : ℕ) : ℤ) < 2 * (2 : ℤ) ^ s := by
        have : ((n : ℕ) : ℤ) < ((2 ^ (s + 1) : ℕ) : ℤ) := by exact_mod_cast h
        rwa [h2] at this
      split
      · rename_i hs
        have : ((n : ℕ) : ℤ) < (2 : ℤ) ^ s := by exact_mod_cast hs
        constructor <;> omega
      · rename_i hs
        have : (2 : ℤ) ^ s ≤ ((n : ℕ) : ℤ) := by
          have := Nat.le_of_not_lt hs
          exact_mod_cast this
        rw [h2]
        constructor <;> omega

/-- The source `x` chunks, read as `evalRowX` reads them, lie in the limb box. -/
lemma sourceChunkXInt_box
    (qs : QSemantics) [RegEncoding qs.Basis] {k : ℕ} {x z : ExtReg}
    (layout : Gate.PhaseProductLayout x z k) (b : qs.Basis) :
    InExactBox x.width (exactLimbWidth k x.width z.width)
      (fun j => sourceChunkXInt (qs := qs) (initSignedLayoutState layout) j b) := by
  intro j
  have hw : ((initSignedLayoutState layout).xslot j).width
      = phaseSplitLogicalWidth x.width (exactLimbWidth k x.width z.width) k j :=
    stInit_xslot_width layout j
  have hlt := ExtReg.toNat_lt (Basis := qs.Basis) ((initSignedLayoutState layout).xslot j) b
  rw [hw] at hlt
  unfold sourceChunkXInt exactLimbLo exactLimbHi
  by_cases htop : isTopChunk j
  · simp only [htop, ite_true]
    unfold extToInt
    rw [hw]
    exact tcDecodeWidth_exactBox _ _ hlt
  · simp only [htop, ite_false]
    have h1 : ((ExtReg.toNat ((initSignedLayoutState layout).xslot j) b : ℕ) : ℤ)
        < (2 : ℤ) ^ (phaseSplitLogicalWidth x.width (exactLimbWidth k x.width z.width) k j) := by
      exact_mod_cast hlt
    constructor <;> omega

/-- The source `z` chunks lie in the limb box. -/
lemma sourceChunkZInt_box
    (qs : QSemantics) [RegEncoding qs.Basis] {k : ℕ} {x z : ExtReg}
    (layout : Gate.PhaseProductLayout x z k) (b : qs.Basis) :
    InExactBox z.width (exactLimbWidth k x.width z.width)
      (fun j => sourceChunkZInt (qs := qs) (initSignedLayoutState layout) j b) := by
  intro j
  have hw : ((initSignedLayoutState layout).zslot j).width
      = phaseSplitLogicalWidth z.width (exactLimbWidth k x.width z.width) k j :=
    stInit_zslot_width layout j
  have hlt := ExtReg.toNat_lt (Basis := qs.Basis) ((initSignedLayoutState layout).zslot j) b
  rw [hw] at hlt
  unfold sourceChunkZInt exactLimbLo exactLimbHi
  by_cases htop : isTopChunk j
  · simp only [htop, ite_true]
    unfold extToInt
    rw [hw]
    exact tcDecodeWidth_exactBox _ _ hlt
  · simp only [htop, ite_false]
    have h1 : ((ExtReg.toNat ((initSignedLayoutState layout).zslot j) b : ℕ) : ℤ)
        < (2 : ℤ) ^ (phaseSplitLogicalWidth z.width (exactLimbWidth k x.width z.width) k j) := by
      exact_mod_cast hlt
    constructor <;> omega

/-- Every prefix-reachable symbolic state fits in the target layout chosen by
the exact width (`WidthRule.exact`). -/
lemma allocated_widths_sound_exact
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  {k : ℕ}
  {x z : ExtReg}
  (layout : Gate.PhaseProductLayout x z k)
  (ops : Prog k)
  (hcap : (initSignedLayoutState layout).CanGrowToNeeds (neededWidthsBy .exact x z ops))
  (b : qs.Basis) :
  let src := initSignedLayoutState layout
  let dst :=  targetSignedLayoutState src (neededWidthsBy .exact x z ops)
  ∀ {σ : State k},
    (∃ pre rest, ops = pre ++ rest ∧ run? pre State.start_state = some σ) →
    (∀ i : Fin k, FitsSignedWidth (ExtReg.width (dst.xslot i))
      (evalRowX (qs := qs) src (σ i) b)) ∧
    (∀ i : Fin k, FitsSignedWidth (ExtReg.width (dst.zslot i))
        (evalRowZ (qs := qs) src (σ i) b)) := by
  dsimp only
  intro σ hprefix
  rcases hprefix with ⟨pre, rest, hops, hrun⟩
  have hE : ∀ (hk : 0 < k),
      2 ^ (tightSignedWidthOfWidths ops x.width z.width - 1)
        ≤ 2 ^ (commonNeededWidth (neededWidthsBy .exact x z ops) - 1) := fun hk => by
    change 2 ^ _ ≤ 2 ^ (nextSignedWidthBy .exact x z ops - 1)
    rw [nextSignedWidthBy_exact hk]
    have := tight_le_exactSignedWidth ops x.width z.width
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpos : ∀ (hk : 0 < k), 0 < commonNeededWidth (neededWidthsBy .exact x z ops) := fun hk => by
    change 0 < nextSignedWidthBy .exact x z ops
    rw [nextSignedWidthBy_exact hk]
    exact exactSignedWidth_pos ops x.width z.width
  have hr : ∀ i : Fin k, σ i ∈ exactReachRows ops := fun i => mem_exactReachRows hops hrun i
  constructor
  · intro i
    have hk : 0 < k := Fin.pos i
    rw [targetSignedLayoutState_xslot_width_by .exact layout ops i hcap]
    obtain ⟨hlo, hhi⟩ := exact_row_bounds _ _ (σ i) (sourceChunkXInt_box qs layout b)
    exact fits_of_exactDemand (hpos hk) hlo hhi
      (le_trans (exactRowDemand_le_tight (zw := z.width) (hr i)).1 (hE hk))
  · intro i
    have hk : 0 < k := Fin.pos i
    rw [targetSignedLayoutState_zslot_width_by .exact layout ops i hcap]
    obtain ⟨hlo, hhi⟩ := exact_row_bounds _ _ (σ i) (sourceChunkZInt_box qs layout b)
    exact fits_of_exactDemand (hpos hk) hlo hhi
      (le_trans (exactRowDemand_le_tight (xw := x.width) (hr i)).2 (hE hk))

/-- `allocated_widths_sound` under either width rule. -/
lemma allocated_widths_sound_by
  (R : WidthRule)
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  {k : ℕ}
  {x z : ExtReg}
  (layout : Gate.PhaseProductLayout x z k)
  (ops : Prog k)
  (hcap : (initSignedLayoutState layout).CanGrowToNeeds (neededWidthsBy R x z ops))
  (b : qs.Basis) :
  let src := initSignedLayoutState layout
  let dst :=  targetSignedLayoutState src (neededWidthsBy R x z ops)
  ∀ {σ : State k},
    (∃ pre rest, ops = pre ++ rest ∧ run? pre State.start_state = some σ) →
    (∀ i : Fin k, FitsSignedWidth (ExtReg.width (dst.xslot i))
      (evalRowX (qs := qs) src (σ i) b)) ∧
    (∀ i : Fin k, FitsSignedWidth (ExtReg.width (dst.zslot i))
        (evalRowZ (qs := qs) src (σ i) b)) := by
  cases R
  · exact allocated_widths_sound qs layout ops hcap b
  · exact allocated_widths_sound_exact qs layout ops hcap b

end Shor
