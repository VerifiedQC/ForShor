import FastMultiplication.ShorVerification.AlgorithmCorrectness.PhaseProduct.WidthSoundness

namespace Shor
open Gate
open Operations
open scoped BigOperators

/-!
# Phase-Product Allocation Correctness

This file proves that the allocation half of the compiled phase-product circuit
copies each symbolic source chunk into the widened target layout while
preserving the values needed by the remaining slots.
-/

/-! =========================================================
    Section 1: Single-chunk allocation correctness
========================================================= -/

/-- These lemmas show that allocating one `x`/`z` chunk sends a basis state to
another basis state, installs the correct target value on the allocated slot,
and preserves all other target slots and source-chunk interpretations. -/
lemma eval_allocChunkGate_x_ket
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [ExtRegEncoding qs.Basis]
  [ExtRegSplitSemantics qs.Basis]
  [GateSemanticsFacts qs]
  {k : ℕ}
  (x z : ExtReg)
  (hxz : Disjoint x.base z.base)
  (ops : Prog k)
  (i : Fin k)
  (bcur : qs.Basis) :
  let need : NeededWidths k := scanNeededWidths x z ops
  let stInit : LayoutState k :=
    initSignedLayoutState (Basis := qs.Basis) x z k
  let stFinal : LayoutState k :=
    targetSignedLayoutState (Basis := qs.Basis) x z k need
  ∃ bX : qs.Basis,
    qs.eval (allocChunkGate i (stInit.xslot i) (stFinal.xslot i)) (qs.ket bcur) = qs.ket bX ∧
    ExtRegEncoding.extToInt (stFinal.xslot i) bX = sourceChunkXInt (qs := qs) stInit i bcur ∧
    (∀ j : Fin k, j ≠ i →
      ExtRegEncoding.extToInt (stFinal.xslot j) bX =
        ExtRegEncoding.extToInt (stFinal.xslot j) bcur) ∧
    (∀ j : Fin k,
      ExtRegEncoding.extToInt (stFinal.zslot j) bX =
        ExtRegEncoding.extToInt (stFinal.zslot j) bcur) ∧
    (∀ j : Fin k,
      sourceChunkXInt (qs := qs) stInit j bX =
        sourceChunkXInt (qs := qs) stInit j bcur) ∧
    (∀ j : Fin k,
      sourceChunkZInt (qs := qs) stInit j bX =
        sourceChunkZInt (qs := qs) stInit j bcur) := by
  dsimp
  set need : NeededWidths k := scanNeededWidths x z ops
  set stInit : LayoutState k :=
    initSignedLayoutState (Basis := qs.Basis) x z k
  set stFinal : LayoutState k :=
    targetSignedLayoutState (Basis := qs.Basis) x z k need
  set δ : ℕ := extraDelta (stInit.xslot i) (stFinal.xslot i)

  have disjoint_symm {a b : Reg} : Disjoint a b → Disjoint b a := by
    intro h
    cases h with
    | inl hab => exact Or.inr hab
    | inr hba => exact Or.inl hba

  have hδpos : 0 < δ := by
    simpa [δ, need, stInit, stFinal] using
      (extraDelta_xslot_pos
        (qs := qs) (x := x) (z := z) (ops := ops) (i := i))

  have hslot :
      stFinal.xslot i = ExtReg.addExtra (stInit.xslot i) δ := by
    simpa [δ, need, stInit, stFinal] using
      (stFinal_xslot_eq_addExtra
        (Basis := qs.Basis) (x := x) (z := z) (ops := ops) (i := i))

  have hδne : δ ≠ 0 := Nat.ne_of_gt hδpos

  have hdisj_xx_src (j : Fin k) (hji : j ≠ i) :
      Disjoint (stInit.xslot i).base (stInit.xslot j).base := by
    simpa [stInit, initSignedLayoutState] using
      splitExtReg_disjoint
        (Basis := qs.Basis)
        x k (phaseLimbWidth x z k)
        i j (Ne.symm hji)

  have hdisj_xx_tgt (j : Fin k) (hji : j ≠ i) :
      Disjoint (stInit.xslot i).base (stFinal.xslot j).base := by
    have hsrc : Disjoint (stInit.xslot i).base (stInit.xslot j).base :=
      hdisj_xx_src j hji
    have hbase :
        (stFinal.xslot j).base = (stInit.xslot j).base := by
      simp [stFinal, targetSignedLayoutState, widenExtRegTo, initSignedLayoutState, stInit]
    simpa [hbase] using hsrc

  have hdisj_xz_src (j : Fin k) :
      Disjoint (stInit.xslot i).base (stInit.zslot j).base := by
    simpa [stInit, initSignedLayoutState] using
      splitExtReg_disjoint_of_disjoint
        (Basis := qs.Basis)
        x z k (phaseLimbWidth x z k)
        i j hxz

  have hdisj_xz_tgt (j : Fin k) :
      Disjoint (stInit.xslot i).base (stFinal.zslot j).base := by
    have hsrc : Disjoint (stInit.xslot i).base (stInit.zslot j).base :=
      hdisj_xz_src j
    have hbase :
        (stFinal.zslot j).base = (stInit.zslot j).base := by
      simp [stFinal, targetSignedLayoutState, widenExtRegTo, initSignedLayoutState, stInit]
    simpa [hbase] using hsrc

  by_cases htop : isTopChunk i
  ·
    have hgate :
        allocChunkGate i (stInit.xslot i) (stFinal.xslot i)
          = Gate.signExtend (stInit.xslot i) δ := by
      unfold allocChunkGate
      simp [δ, hδne, htop]

    rcases ExtensionSemantics.eval_signExtend_ket
        (qs := qs) (r := stInit.xslot i) (n := δ) (b := bcur) with
      ⟨bX, hEval0, hToNat, hWide, hLoc⟩

    have hEval :
        qs.eval (allocChunkGate i (stInit.xslot i) (stFinal.xslot i)) (qs.ket bcur)
          = qs.ket bX := by
      rw [hgate]
      exact hEval0

    refine ⟨bX, hEval, ?_, ?_, ?_, ?_, ?_⟩

    ·
      calc
        ExtRegEncoding.extToInt (stFinal.xslot i) bX
            = ExtRegEncoding.extToInt (ExtReg.addExtra (stInit.xslot i) δ) bX := by
                rw [hslot]
        _ = ExtRegEncoding.extToInt (stInit.xslot i) bcur := hWide
        _ = sourceChunkXInt (qs := qs) stInit i bcur := by
              unfold sourceChunkXInt
              simp [htop]

    ·
      intro j hji
      exact signExtend_preserves_disjoint_extToInt
        (qs := qs)
        (r := stInit.xslot i) (e := stFinal.xslot j)
        (n := δ) (b := bcur) (b' := bX)
        (hdisj_xx_tgt j hji) hEval0

    ·
      intro j
      exact signExtend_preserves_disjoint_extToInt
        (qs := qs)
        (r := stInit.xslot i) (e := stFinal.zslot j)
        (n := δ) (b := bcur) (b' := bX)
        (hdisj_xz_tgt j) hEval0

    ·
      intro j
      unfold sourceChunkXInt
      by_cases hjtop : isTopChunk j
      ·
        simp [hjtop]
        by_cases hji : j = i
        ·
          subst hji
          unfold ExtRegEncoding.extToInt ExtReg.toNat
          have := congrArg (tcDecodeWidth (ExtReg.width (stInit.xslot j))) hToNat
          simpa [ExtReg.toNat] using this
        ·
          exact signExtend_preserves_disjoint_extToInt
            (qs := qs)
            (r := stInit.xslot i) (e := stInit.xslot j)
            (n := δ) (b := bcur) (b' := bX)
            (hdisj_xx_src j hji) hEval0
      ·
        simp [hjtop]
        by_cases hji : j = i
        ·
          subst hji
          simpa using hToNat
        ·
          exact hLoc (stInit.xslot j)
            (disjoint_symm (hdisj_xx_src j hji))

    ·
      intro j
      unfold sourceChunkZInt
      by_cases hjtop : isTopChunk j
      ·
        simp [hjtop]
        exact signExtend_preserves_disjoint_extToInt
          (qs := qs)
          (r := stInit.xslot i) (e := stInit.zslot j)
          (n := δ) (b := bcur) (b' := bX)
          (hdisj_xz_src j) hEval0
      ·
        simp [hjtop]
        exact hLoc (stInit.zslot j)
          (disjoint_symm (hdisj_xz_src j))

  ·
    have hgate :
        allocChunkGate i (stInit.xslot i) (stFinal.xslot i)
          = Gate.zeroExtend (stInit.xslot i) δ := by
      unfold allocChunkGate
      simp [δ, hδne, htop]

    rcases ExtensionSemantics.eval_zeroExtend_ket
        (qs := qs) (r := stInit.xslot i) (n := δ) (b := bcur) with
      ⟨bX, hEval0, hToNat, hWideNat, hLoc⟩

    have hEval :
        qs.eval (allocChunkGate i (stInit.xslot i) (stFinal.xslot i)) (qs.ket bcur)
          = qs.ket bX := by
      rw [hgate]
      exact hEval0

    have hWide :
        ExtRegEncoding.extToInt (ExtReg.addExtra (stInit.xslot i) δ) bX
          = (ExtReg.toNat (stInit.xslot i) bcur : ℤ) := by
      exact zeroExtend_extToInt
        (qs := qs)
        (r := stInit.xslot i) (n := δ)
        (b := bcur) (b' := bX)
        hδpos hEval0

    refine ⟨bX, hEval, ?_, ?_, ?_, ?_, ?_⟩

    ·
      calc
        ExtRegEncoding.extToInt (stFinal.xslot i) bX
            = ExtRegEncoding.extToInt (ExtReg.addExtra (stInit.xslot i) δ) bX := by
                rw [hslot]
        _ = (ExtReg.toNat (stInit.xslot i) bcur : ℤ) := hWide
        _ = sourceChunkXInt (qs := qs) stInit i bcur := by
              unfold sourceChunkXInt
              simp [htop]

    ·
      intro j hji
      exact zeroExtend_preserves_disjoint_extToInt
        (qs := qs)
        (r := stInit.xslot i) (e := stFinal.xslot j)
        (n := δ) (b := bcur) (b' := bX)
        (hdisj_xx_tgt j hji) hEval0

    ·
      intro j
      exact zeroExtend_preserves_disjoint_extToInt
        (qs := qs)
        (r := stInit.xslot i) (e := stFinal.zslot j)
        (n := δ) (b := bcur) (b' := bX)
        (hdisj_xz_tgt j) hEval0

    ·
      intro j
      unfold sourceChunkXInt
      by_cases hjtop : isTopChunk j
      ·
        simp [hjtop]
        by_cases hji : j = i
        ·
          subst hji
          exfalso
          exact htop hjtop
        ·
          exact zeroExtend_preserves_disjoint_extToInt
            (qs := qs)
            (r := stInit.xslot i) (e := stInit.xslot j)
            (n := δ) (b := bcur) (b' := bX)
            (hdisj_xx_src j hji) hEval0
      ·
        simp [hjtop]
        by_cases hji : j = i
        ·
          subst hji
          simpa using hToNat
        ·
          exact hLoc (stInit.xslot j)
            (disjoint_symm (hdisj_xx_src j hji))

    ·
      intro j
      unfold sourceChunkZInt
      by_cases hjtop : isTopChunk j
      ·
        simp [hjtop]
        exact zeroExtend_preserves_disjoint_extToInt
          (qs := qs)
          (r := stInit.xslot i) (e := stInit.zslot j)
          (n := δ) (b := bcur) (b' := bX)
          (hdisj_xz_src j) hEval0
      ·
        simp [hjtop]
        exact hLoc (stInit.zslot j)
          (disjoint_symm (hdisj_xz_src j))

lemma eval_allocChunkGate_z_ket
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [ExtRegEncoding qs.Basis]
  [ExtRegSplitSemantics qs.Basis]
  [GateSemanticsFacts qs]
  {k : ℕ}
  (x z : ExtReg)
  (hxz : Disjoint x.base z.base)
  (ops : Prog k)
  (i : Fin k)
  (bcur : qs.Basis) :
  let need : NeededWidths k := scanNeededWidths x z ops
  let stInit : LayoutState k :=
    initSignedLayoutState (Basis := qs.Basis) x z k
  let stFinal : LayoutState k :=
    targetSignedLayoutState (Basis := qs.Basis) x z k need
  ∃ bZ : qs.Basis,
    qs.eval (allocChunkGate i (stInit.zslot i) (stFinal.zslot i)) (qs.ket bcur) = qs.ket bZ ∧
    ExtRegEncoding.extToInt (stFinal.zslot i) bZ = sourceChunkZInt (qs := qs) stInit i bcur ∧
    (∀ j : Fin k,
      ExtRegEncoding.extToInt (stFinal.xslot j) bZ =
        ExtRegEncoding.extToInt (stFinal.xslot j) bcur) ∧
    (∀ j : Fin k, j ≠ i →
      ExtRegEncoding.extToInt (stFinal.zslot j) bZ =
        ExtRegEncoding.extToInt (stFinal.zslot j) bcur) ∧
    (∀ j : Fin k,
      sourceChunkXInt (qs := qs) stInit j bZ =
        sourceChunkXInt (qs := qs) stInit j bcur) ∧
    (∀ j : Fin k,
      sourceChunkZInt (qs := qs) stInit j bZ =
        sourceChunkZInt (qs := qs) stInit j bcur) := by
  dsimp
  set need : NeededWidths k := scanNeededWidths x z ops
  set stInit : LayoutState k :=
    initSignedLayoutState (Basis := qs.Basis) x z k
  set stFinal : LayoutState k :=
    targetSignedLayoutState (Basis := qs.Basis) x z k need
  set δ : ℕ := extraDelta (stInit.zslot i) (stFinal.zslot i)

  have hxz' : Disjoint z.base x.base := by
    cases hxz with
    | inl h => exact Or.inr h
    | inr h => exact Or.inl h

  have hδpos : 0 < δ := by
    simpa [δ, need, stInit, stFinal] using
      (extraDelta_zslot_pos
        (qs := qs) (x := x) (z := z) (ops := ops) (i := i))

  have hslot :
      stFinal.zslot i = ExtReg.addExtra (stInit.zslot i) δ := by
    simpa [δ, need, stInit, stFinal] using
      (stFinal_zslot_eq_addExtra
        (Basis := qs.Basis) (x := x) (z := z) (ops := ops) (i := i))

  have hδne : δ ≠ 0 := Nat.ne_of_gt hδpos
  have hdisj_zx_src (j : Fin k) :
      Disjoint (stInit.zslot i).base (stInit.xslot j).base := by
    simpa [stInit, initSignedLayoutState] using
      splitExtReg_disjoint_of_disjoint
        (Basis := qs.Basis)
        z x k (phaseLimbWidth x z k)
        i j hxz'

  have hdisj_zx_tgt (j : Fin k) :
      Disjoint (stInit.zslot i).base (stFinal.xslot j).base := by
    have hsrc : Disjoint (stInit.zslot i).base (stInit.xslot j).base :=
      hdisj_zx_src j
    have hbase :
        (stFinal.xslot j).base = (stInit.xslot j).base := by
      simp [stFinal, targetSignedLayoutState, widenExtRegTo, initSignedLayoutState, stInit]
    simpa [hbase] using hsrc

  have hdisj_xz_src_rev (j : Fin k) :
      Disjoint (stInit.xslot j).base (stInit.zslot i).base := by
    simpa [stInit, initSignedLayoutState] using
      splitExtReg_disjoint_of_disjoint
        (Basis := qs.Basis)
        x z k (phaseLimbWidth x z k)
        j i hxz

  have hdisj_zz_src (j : Fin k) (hji : j ≠ i) :
      Disjoint (stInit.zslot i).base (stInit.zslot j).base := by
    simpa [stInit, initSignedLayoutState] using
      splitExtReg_disjoint
        (Basis := qs.Basis)
        z k (phaseLimbWidth x z k)
        i j (Ne.symm hji)

  have hdisj_zz_src_rev (j : Fin k) (hji : j ≠ i) :
      Disjoint (stInit.zslot j).base (stInit.zslot i).base := by
    simpa [stInit, initSignedLayoutState] using
      splitExtReg_disjoint
        (Basis := qs.Basis)
        z k (phaseLimbWidth x z k)
        j i hji

  have hdisj_zz_tgt (j : Fin k) (hji : j ≠ i) :
      Disjoint (stInit.zslot i).base (stFinal.zslot j).base := by
    have hsrc : Disjoint (stInit.zslot i).base (stInit.zslot j).base :=
      hdisj_zz_src j hji
    have hbase :
        (stFinal.zslot j).base = (stInit.zslot j).base := by
      simp [stFinal, targetSignedLayoutState, widenExtRegTo, initSignedLayoutState,stInit]
    simpa [hbase] using hsrc

  by_cases htop : isTopChunk i
  ·
    have hgate :
        allocChunkGate i (stInit.zslot i) (stFinal.zslot i)
          = Gate.signExtend (stInit.zslot i) δ := by
      unfold allocChunkGate
      simp [δ, hδne, htop]

    rcases ExtensionSemantics.eval_signExtend_ket
        (qs := qs) (r := stInit.zslot i) (n := δ) (b := bcur) with
      ⟨bZ, hEval0, hToNat, hWide, hLoc⟩

    have hEval :
        qs.eval (allocChunkGate i (stInit.zslot i) (stFinal.zslot i)) (qs.ket bcur)
          = qs.ket bZ := by
      rw [hgate]
      exact hEval0

    refine ⟨bZ, hEval, ?_, ?_, ?_, ?_, ?_⟩

    ·
      calc
        ExtRegEncoding.extToInt (stFinal.zslot i) bZ
            = ExtRegEncoding.extToInt (ExtReg.addExtra (stInit.zslot i) δ) bZ := by
                rw [hslot]
        _ = ExtRegEncoding.extToInt (stInit.zslot i) bcur := hWide
        _ = sourceChunkZInt (qs := qs) stInit i bcur := by
              unfold sourceChunkZInt
              simp [htop]

    ·
      intro j
      exact signExtend_preserves_disjoint_extToInt
        (qs := qs)
        (r := stInit.zslot i) (e := stFinal.xslot j)
        (n := δ) (b := bcur) (b' := bZ)
        (hdisj_zx_tgt j) hEval0

    ·
      intro j hji
      exact signExtend_preserves_disjoint_extToInt
        (qs := qs)
        (r := stInit.zslot i) (e := stFinal.zslot j)
        (n := δ) (b := bcur) (b' := bZ)
        (hdisj_zz_tgt j hji) hEval0

    ·
      intro j
      unfold sourceChunkXInt
      by_cases hjtop : isTopChunk j
      ·
        simp [hjtop]
        exact signExtend_preserves_disjoint_extToInt
          (qs := qs)
          (r := stInit.zslot i) (e := stInit.xslot j)
          (n := δ) (b := bcur) (b' := bZ)
          (hdisj_zx_src j) hEval0
      ·
        simp [hjtop]
        exact hLoc (stInit.xslot j) (hdisj_xz_src_rev j)

    ·
      intro j
      unfold sourceChunkZInt
      by_cases hjtop : isTopChunk j
      ·
        simp [hjtop]
        by_cases hji : j = i
        ·
          subst hji
          have := congrArg (tcDecodeWidth (ExtReg.width (stInit.zslot j))) hToNat
          simpa [ExtReg.toNat] using this
        ·
          exact signExtend_preserves_disjoint_extToInt
            (qs := qs)
            (r := stInit.zslot i) (e := stInit.zslot j)
            (n := δ) (b := bcur) (b' := bZ)
            (hdisj_zz_src j hji) hEval0
      ·
        simp [hjtop]
        by_cases hji : j = i
        ·
          subst hji
          exfalso
          exact hjtop htop
        ·
          exact hLoc (stInit.zslot j) (hdisj_zz_src_rev j hji)

  ·
    have hgate :
        allocChunkGate i (stInit.zslot i) (stFinal.zslot i)
          = Gate.zeroExtend (stInit.zslot i) δ := by
      unfold allocChunkGate
      simp [δ, hδne, htop]

    rcases ExtensionSemantics.eval_zeroExtend_ket
        (qs := qs) (r := stInit.zslot i) (n := δ) (b := bcur) with
      ⟨bZ, hEval0, hToNat, hWideNat, hLoc⟩

    have hEval :
        qs.eval (allocChunkGate i (stInit.zslot i) (stFinal.zslot i)) (qs.ket bcur)
          = qs.ket bZ := by
      rw [hgate]
      exact hEval0

    have hWide :
        ExtRegEncoding.extToInt (ExtReg.addExtra (stInit.zslot i) δ) bZ
          = (ExtReg.toNat (stInit.zslot i) bcur : ℤ) := by
      exact zeroExtend_extToInt
        (qs := qs)
        (r := stInit.zslot i) (n := δ)
        (b := bcur) (b' := bZ)
        hδpos hEval0

    refine ⟨bZ, hEval, ?_, ?_, ?_, ?_, ?_⟩

    ·
      calc
        ExtRegEncoding.extToInt (stFinal.zslot i) bZ
            = ExtRegEncoding.extToInt (ExtReg.addExtra (stInit.zslot i) δ) bZ := by
                rw [hslot]
        _ = (ExtReg.toNat (stInit.zslot i) bcur : ℤ) := hWide
        _ = sourceChunkZInt (qs := qs) stInit i bcur := by
              unfold sourceChunkZInt
              simp [htop]

    ·
      intro j
      exact zeroExtend_preserves_disjoint_extToInt
        (qs := qs)
        (r := stInit.zslot i) (e := stFinal.xslot j)
        (n := δ) (b := bcur) (b' := bZ)
        (hdisj_zx_tgt j) hEval0

    ·
      intro j hji
      exact zeroExtend_preserves_disjoint_extToInt
        (qs := qs)
        (r := stInit.zslot i) (e := stFinal.zslot j)
        (n := δ) (b := bcur) (b' := bZ)
        (hdisj_zz_tgt j hji) hEval0

    ·
      intro j
      unfold sourceChunkXInt
      by_cases hjtop : isTopChunk j
      ·
        simp [hjtop]
        exact zeroExtend_preserves_disjoint_extToInt
          (qs := qs)
          (r := stInit.zslot i) (e := stInit.xslot j)
          (n := δ) (b := bcur) (b' := bZ)
          (hdisj_zx_src j) hEval0
      ·
        simp [hjtop]
        exact hLoc (stInit.xslot j) (hdisj_xz_src_rev j)

    ·
      intro j
      unfold sourceChunkZInt
      by_cases hjtop : isTopChunk j
      ·
        simp [hjtop]
        by_cases hji : j = i
        ·
          subst hji
          exfalso
          exact htop hjtop
        ·
          exact zeroExtend_preserves_disjoint_extToInt
            (qs := qs)
            (r := stInit.zslot i) (e := stInit.zslot j)
            (n := δ) (b := bcur) (b' := bZ)
            (hdisj_zz_src j hji) hEval0
      ·
        simp [hjtop]
        by_cases hji : j = i
        ·
          subst hji
          simpa using hToNat
        ·
          exact hLoc (stInit.zslot j) (hdisj_zz_src_rev j hji)

/-! =========================================================
    Section 2: Full allocation correctness
========================================================= -/

/-- The auxiliary allocation lemma establishes the encoding invariant after
allocating the first `n` chunks. The specialized full-allocation lemmas then
package the `n = k` case and combine it with `allocated_widths_sound`. -/
lemma eval_compileSignedAllocationsAux_ket
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [ExtRegEncoding qs.Basis]
  [ExtRegSplitSemantics qs.Basis]
  [GateSemanticsFacts qs]
  {k : ℕ}
  (x z : ExtReg)
  (hxz : Disjoint x.base z.base)
  (ops : Prog k)
  (b : qs.Basis) :
  let need : NeededWidths k := scanNeededWidths x z ops
  let stInit : LayoutState k :=
    initSignedLayoutState (Basis := qs.Basis) x z k
  let stFinal : LayoutState k :=
    targetSignedLayoutState (Basis := qs.Basis) x z k need
  ∀ (n : ℕ) (hn : n ≤ k),
    ∃ bAlloc : qs.Basis,
      qs.eval (compileSignedAllocationsAux stInit stFinal n hn) (qs.ket b) = qs.ket bAlloc ∧
      (∀ i : Fin k, i.1 < n →
        ExtRegEncoding.extToInt (stFinal.xslot i) bAlloc =
          evalRowX (qs := qs) stInit (State.start_state i) b) ∧
      (∀ i : Fin k, i.1 < n →
        ExtRegEncoding.extToInt (stFinal.zslot i) bAlloc =
          evalRowZ (qs := qs) stInit (State.start_state i) b) ∧
      (∀ i : Fin k, n ≤ i.1 →
        sourceChunkXInt (qs := qs) stInit i bAlloc =
          sourceChunkXInt (qs := qs) stInit i b) ∧
      (∀ i : Fin k, n ≤ i.1 →
        sourceChunkZInt (qs := qs) stInit i bAlloc =
          sourceChunkZInt (qs := qs) stInit i b) := by
  dsimp
  set need : NeededWidths k := scanNeededWidths x z ops
  set stInit : LayoutState k :=
    initSignedLayoutState (Basis := qs.Basis) x z k
  set stFinal : LayoutState k :=
    targetSignedLayoutState (Basis := qs.Basis) x z k need
  intro n hn
  induction n generalizing b with
  | zero =>
      refine ⟨b, ?_, ?_, ?_, ?_, ?_⟩
      · simp [compileSignedAllocationsAux_zero, QSemantics.eval_id]
      · intro i hi
        omega
      · intro i hi
        omega
      · intro i hi
        rfl
      · intro i hi
        rfl
  | succ n ih =>
      let hk' : n ≤ k := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn
      let idx : Fin k := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩

      rcases ih b hk' with
        ⟨bMid, hMidEval, hMidX, hMidZ, hKeepX, hKeepZ⟩

      rcases
        (eval_allocChunkGate_x_ket
          (qs := qs)
          (x := x) (z := z)
          (hxz := hxz)
          (ops := ops)
          (i := idx)
          (bcur := bMid))
        with ⟨bX, hXEval, hXVal, hXKeepX, hXKeepZTarget, hXKeepSrcX, hXKeepSrcZ⟩

      rcases
        (eval_allocChunkGate_z_ket
          (qs := qs)
          (x := x) (z := z)
          (hxz := hxz)
          (ops := ops)
          (i := idx)
          (bcur := bX))
        with ⟨bAlloc, hZEval, hZVal, hZKeepX, hZKeepZ, hZKeepSrcX, hZKeepSrcZ⟩

      refine ⟨bAlloc, ?_, ?_, ?_, ?_, ?_⟩
      ·
        rw [compileSignedAllocationsAux_succ
          (src := stInit) (dst := stFinal) (n := n) (hn := hn)]
        rw [QSemantics.eval_seq]
        rw [hMidEval]
        rw [QSemantics.eval_seq]
        rw [hXEval]
        simpa [QSemantics.eval_seq, hk', idx] using hZEval

      ·
        intro j hj
        by_cases hji : j = idx
        ·
          subst hji
          calc
            ExtRegEncoding.extToInt (stFinal.xslot idx) bAlloc
                = ExtRegEncoding.extToInt (stFinal.xslot idx) bX := by
                    simpa using hZKeepX idx
            _ = sourceChunkXInt (qs := qs) stInit idx bMid := hXVal
            _ = sourceChunkXInt (qs := qs) stInit idx b := by
                  exact hKeepX idx (by change n ≤ n; exact Nat.le_refl n)
            _ = evalRowX (qs := qs) stInit (State.start_state idx) b := by
                  symm
                  simpa using evalRowX_start_state (qs := qs) stInit idx b
        ·
          have hjn : j.1 < n := by
            have hjne : j.1 ≠ n := by
              intro hEq
              apply hji
              apply Fin.ext
              simpa [idx] using hEq
            omega
          calc
            ExtRegEncoding.extToInt (stFinal.xslot j) bAlloc
                = ExtRegEncoding.extToInt (stFinal.xslot j) bX := by
                    simpa using hZKeepX j
            _ = ExtRegEncoding.extToInt (stFinal.xslot j) bMid := by
                  exact hXKeepX j hji
            _ = evalRowX (qs := qs) stInit (State.start_state j) b := hMidX j hjn

      ·
        intro j hj
        by_cases hji : j = idx
        ·
          subst hji
          calc
            ExtRegEncoding.extToInt (stFinal.zslot idx) bAlloc
                = sourceChunkZInt (qs := qs) stInit idx bX := hZVal
            _ = sourceChunkZInt (qs := qs) stInit idx bMid := by
                  simpa using hXKeepSrcZ idx
            _ = sourceChunkZInt (qs := qs) stInit idx b := by
                  exact hKeepZ idx (by change n ≤ n; exact Nat.le_refl n)
            _ = evalRowZ (qs := qs) stInit (State.start_state idx) b := by
                  symm
                  simpa using evalRowZ_start_state (qs := qs) stInit idx b
        ·
          have hjn : j.1 < n := by
            have hjne : j.1 ≠ n := by
              intro hEq
              apply hji
              apply Fin.ext
              simpa [idx] using hEq
            omega
          calc
            ExtRegEncoding.extToInt (stFinal.zslot j) bAlloc
                = ExtRegEncoding.extToInt (stFinal.zslot j) bX := by
                    exact hZKeepZ j hji
            _ = ExtRegEncoding.extToInt (stFinal.zslot j) bMid := by
                  simpa using hXKeepZTarget j
            _ = evalRowZ (qs := qs) stInit (State.start_state j) b := hMidZ j hjn

      ·
        intro j hj
        calc
          sourceChunkXInt (qs := qs) stInit j bAlloc
              = sourceChunkXInt (qs := qs) stInit j bX := by
                  simpa using hZKeepSrcX j
          _ = sourceChunkXInt (qs := qs) stInit j bMid := by
                simpa using hXKeepSrcX j
          _ = sourceChunkXInt (qs := qs) stInit j b := hKeepX j (by omega)

      ·
        intro j hj
        calc
          sourceChunkZInt (qs := qs) stInit j bAlloc
              = sourceChunkZInt (qs := qs) stInit j bX := by
                  simpa using hZKeepSrcZ j
          _ = sourceChunkZInt (qs := qs) stInit j bMid := by
                simpa using hXKeepSrcZ j
          _ = sourceChunkZInt (qs := qs) stInit j b := hKeepZ j (by omega)

lemma eval_compileSignedAllocations_ket
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [ExtRegEncoding qs.Basis]
  [ExtRegSplitSemantics qs.Basis]
  [GateSemanticsFacts qs]
  {k : ℕ}
  (x z : ExtReg)
  (hxz : Disjoint x.base z.base)
  (ops : Prog k)
  (b : qs.Basis) :
  let need : NeededWidths k := scanNeededWidths x z ops
  let stInit : LayoutState k :=
    initSignedLayoutState (Basis := qs.Basis) x z k
  let stFinal : LayoutState k :=
    targetSignedLayoutState (Basis := qs.Basis) x z k need
  ∃ bAlloc : qs.Basis,
    qs.eval (compileSignedAllocations k stInit stFinal) (qs.ket b) = qs.ket bAlloc ∧
    EncodesStateFrom (qs := qs) stInit stFinal State.start_state b bAlloc := by
  dsimp [compileSignedAllocations]
  rcases
    (eval_compileSignedAllocationsAux_ket
      (qs := qs)
      (x := x) (z := z)
      (hxz := hxz)
      (ops := ops) (b := b)
      k le_rfl)
    with ⟨bAlloc, hEval, hX, hZ, _hKeepX, _hKeepZ⟩
  refine ⟨bAlloc, hEval, ?_⟩
  constructor
  · intro i
    exact hX i i.is_lt
  · intro i
    exact hZ i i.is_lt

lemma eval_compileSignedAllocations_ket_fits
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [ExtRegEncoding qs.Basis]
  [ExtRegSplitSemantics qs.Basis]
  [GateSemanticsFacts qs]
  {k : ℕ}
  (x z : ExtReg)
  (hxz : Disjoint x.base z.base)
  (ops : Prog k)
  (b : qs.Basis) :
  let need : NeededWidths k := scanNeededWidths x z ops
  let stInit : LayoutState k :=
    initSignedLayoutState (Basis := qs.Basis) x z k
  let stFinal : LayoutState k :=
    targetSignedLayoutState (Basis := qs.Basis) x z k need
  ∃ bAlloc : qs.Basis,
    qs.eval (compileSignedAllocations k stInit stFinal) (qs.ket b) = qs.ket bAlloc ∧
    EncodesStateFromFits (qs := qs) stInit stFinal State.start_state b bAlloc := by
  have hAlloc :=
    eval_compileSignedAllocations_ket
      (qs := qs)
      (x := x) (z := z)
      (hxz := hxz)
      (ops := ops)
      (b := b)

  rcases hAlloc with ⟨bAlloc, hEval, hEnc⟩

  have hFits :
      let src := initSignedLayoutState (Basis := qs.Basis) x z k
      let dst := targetSignedLayoutState
        (Basis := qs.Basis) x z k (scanNeededWidths x z ops)
      (∀ i : Fin k,
        FitsSignedWidth (ExtReg.width (dst.xslot i))
          (evalRowX (qs := qs) src (State.start_state i) b)) ∧
      (∀ i : Fin k,
        FitsSignedWidth (ExtReg.width (dst.zslot i))
          (evalRowZ (qs := qs) src (State.start_state i) b)) := by
    exact allocated_widths_sound
      (qs := qs) (x := x) (z := z) (ops := ops) (b := b)
      (σ := State.start_state)
      ⟨[], ops, by simp, by simp [run?]⟩

  refine ⟨bAlloc, hEval, ?_⟩
  dsimp at hFits
  exact ⟨hEnc, hFits.1, hFits.2⟩


end Shor
