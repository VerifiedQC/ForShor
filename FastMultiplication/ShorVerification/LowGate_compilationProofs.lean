import FastMultiplication.ShorVerification.LowGate_compilationCore
import FastMultiplication.ShorVerification.Toom_Cook_formula

namespace Shor
open Gate
open Operations
open scoped BigOperators

/-!
This file proves semantic correctness helpers for signed allocation and for
compiled annotated operation blocks. It builds on the core compiler and layout
definitions from `LowGate_compilationCore`, and it uses the Toom-Cook / phase
formula interface developed in `Toom_Cook_formula`.
-/

/-! =========================================================
    Section 1: Setup and global assumptions
========================================================= -/

variable (qs : QSemantics)
variable [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
variable [ExtRegSplitSemantics qs.Basis]
variable [GateSemanticsFacts qs]

/-! =========================================================
    Section 2: Basic register and layout helpers
========================================================= -/

def WellFormedReg (r : Reg) : Prop :=
  r.lo ≤ r.hi


/-! =========================================================
    Section 3: Width-scan and extra-delta facts
========================================================= -/

/-- The initial x width is included in the full width scan. -/
lemma scanNeededWidths_x_ge_init
    {k : ℕ} (x z : ExtReg) (ops : List (valid_ops k)) (i : Fin k) :
    (initWidthState x z k).xw i ≤ (scanNeededWidths x z ops).xneed i := by
  simp [scanNeededWidths]
  exact
    scanNeededWidthsAux_x_ge
      (i := i)
      ops
      (initWidthState x z k)
      (widthsOfState (initWidthState x z k))

/-- The initial z width is included in the full width scan. -/
lemma scanNeededWidths_z_ge_init
    {k : ℕ} (x z : ExtReg) (ops : List (valid_ops k)) (i : Fin k) :
    (initWidthState x z k).zw i ≤ (scanNeededWidths x z ops).zneed i := by
  simp [scanNeededWidths]
  exact
    scanNeededWidthsAux_z_ge
      (i := i)
      ops
      (initWidthState x z k)
      (widthsOfState (initWidthState x z k))

lemma extraDelta_xslot_pos
    (qs : QSemantics)
    [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
    [ExtRegSplitSemantics qs.Basis]
    {k : ℕ} (x z : ExtReg) (ops : Prog k) (i : Fin k) :
    let stInit := initSignedLayoutState (Basis := qs.Basis) x z k
    let stFinal := targetSignedLayoutState
      (Basis := qs.Basis) x z k (scanNeededWidths x z ops)
    0 < extraDelta (stInit.xslot i) (stFinal.xslot i) := by
  dsimp
  let stInit := initSignedLayoutState (Basis := qs.Basis) x z k
  let Wwork := commonNeededWidth (scanNeededWidths x z ops)

  have hinit :
      ExtReg.width (stInit.xslot i) = (initWidthState x z k).xw i := by
    simpa [stInit] using
      stInit_xslot_width (Basis := qs.Basis) x z i

  have hscan :
      (initWidthState x z k).xw i ≤
        (scanNeededWidths x z ops).xneed i :=
    scanNeededWidths_x_ge_init x z ops i

  have hW :
      (scanNeededWidths x z ops).xneed i + 1 ≤ Wwork :=
    commonNeededWidth_ge_xneed (scanNeededWidths x z ops) i

  have hlt : ExtReg.width (stInit.xslot i) < Wwork := by
    rw [hinit]
    omega

  simpa [targetSignedLayoutState, stInit, Wwork] using
    extraDelta_widenExtRegTo_pos (stInit.xslot i) Wwork hlt

lemma extraDelta_zslot_pos
    (qs : QSemantics)
    [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
    [ExtRegSplitSemantics qs.Basis]
    {k : ℕ} (x z : ExtReg) (ops : Prog k) (i : Fin k) :
    let stInit := initSignedLayoutState (Basis := qs.Basis) x z k
    let stFinal := targetSignedLayoutState
      (Basis := qs.Basis) x z k (scanNeededWidths x z ops)
    0 < extraDelta (stInit.zslot i) (stFinal.zslot i) := by
  dsimp
  let stInit := initSignedLayoutState (Basis := qs.Basis) x z k
  let Wwork := commonNeededWidth (scanNeededWidths x z ops)

  have hinit :
      ExtReg.width (stInit.zslot i) = (initWidthState x z k).zw i := by
    simpa [stInit] using
      stInit_zslot_width (Basis := qs.Basis) x z i

  have hscan :
      (initWidthState x z k).zw i ≤
        (scanNeededWidths x z ops).zneed i :=
    scanNeededWidths_z_ge_init x z ops i

  have hW :
      (scanNeededWidths x z ops).zneed i + 1 ≤ Wwork :=
    commonNeededWidth_ge_zneed (scanNeededWidths x z ops) i

  have hlt : ExtReg.width (stInit.zslot i) < Wwork := by
    rw [hinit]
    omega

  simpa [targetSignedLayoutState, stInit, Wwork] using
    extraDelta_widenExtRegTo_pos (stInit.zslot i) Wwork hlt

/-! =========================================================
    Section 4: Single-chunk allocation correctness
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
    Section 5: Full allocation correctness
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

/-! =========================================================
    Section 6: Sequencing compiled annotated programs
========================================================= -/

lemma eval_compileAnnotatedOpsToSignedGateAux_append
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ} (hk : 1 < k)
  (phi : ℝ)
  (coeff : Fin (q k) → ℚ)
  (st : LayoutState k)
  (xs ys : List (AnnotatedOp k))
  (ψ : qs.State) :
  qs.eval
      (compileAnnotatedOpsToSignedGateAux k hk phi coeff st (xs ++ ys))
      ψ
    =
  qs.eval
      (compileAnnotatedOpsToSignedGateAux k hk phi coeff st ys)
      (qs.eval
        (compileAnnotatedOpsToSignedGateAux k hk phi coeff st xs)
        ψ) := by
  induction xs generalizing ψ with
  | nil =>
      simp [compileAnnotatedOpsToSignedGateAux, qs.eval_id]
  | cons a xs ih =>
      cases a with
      | mk op term? =>
          cases op <;>
            simp [compileAnnotatedOpsToSignedGateAux, qs.eval_seq, ih]
          aesop

/-! =========================================================
    Section 7: Layout disjointness
========================================================= -/

def LayoutSlotsDisjoint {k : ℕ} (st : LayoutState k) : Prop :=
  (∀ i j : Fin k, i ≠ j → Disjoint (st.xslot i).base (st.xslot j).base) ∧
  (∀ i j : Fin k, i ≠ j → Disjoint (st.zslot i).base (st.zslot j).base) ∧
  (∀ i j : Fin k, Disjoint (st.xslot i).base (st.zslot j).base)

/-! =========================================================
    Section 8: One-step encoded-state preservation
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

/-! =========================================================
    Section 9: Arithmetic-prefix and no-phase helpers
========================================================= -/

def OutsideLayout {k : ℕ} (dst : LayoutState k) (e : ExtReg) : Prop :=
  (∀ i : Fin k, Disjoint e.base (dst.xslot i).base) ∧
  (∀ i : Fin k, Disjoint e.base (dst.zslot i).base)

def SameOutsideLayout
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ}
  (dst : LayoutState k) (b1 b2 : qs.Basis) : Prop :=
  ∀ e : ExtReg, OutsideLayout dst e →
    ExtRegEncoding.extToInt e b1 = ExtRegEncoding.extToInt e b2

lemma SameOutsideLayout.refl
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ} (dst : LayoutState k) (b : qs.Basis) :
  SameOutsideLayout qs dst b b := by
  intro e he
  rfl

lemma SameOutsideLayout.symm
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ} {dst : LayoutState k} {b1 b2 : qs.Basis}
  (h : SameOutsideLayout qs dst b1 b2) :
  SameOutsideLayout qs dst b2 b1 := by
  intro e he
  symm
  exact h e he

lemma SameOutsideLayout.trans
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ} {dst : LayoutState k} {b1 b2 b3 : qs.Basis}
  (h12 : SameOutsideLayout qs dst b1 b2)
  (h23 : SameOutsideLayout qs dst b2 b3) :
  SameOutsideLayout qs dst b1 b3 := by
  intro e he
  calc
    ExtRegEncoding.extToInt e b1 = ExtRegEncoding.extToInt e b2 := h12 e he
    _ = ExtRegEncoding.extToInt e b3 := h23 e he

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

def CoversLayoutBits {k : ℕ} (dst : LayoutState k) : Prop :=
  ∀ q : ℕ,
    (∃ i : Fin k, (dst.xslot i).base.lo ≤ q ∧ q < (dst.xslot i).base.hi) ∨
    (∃ i : Fin k, (dst.zslot i).base.lo ≤ q ∧ q < (dst.zslot i).base.hi) ∨
    OutsideLayout dst (ExtReg.ofReg (qubitReg q))

lemma bit_eq_of_toNat_eq_on_reg
  {Basis : Type u} [RegEncoding Basis]
  {r : Reg} {b1 b2 : Basis} {q : ℕ}
  (hNat : RegEncoding.toNat r b1 = RegEncoding.toNat r b2)
  (hqlo : r.lo ≤ q) (hqhi : q < r.hi) :
  RegEncoding.bit q b1 = RegEncoding.bit q b2 := by
  calc
    RegEncoding.bit q b1
        = RegEncoding.bit q (RegEncoding.writeNat r (RegEncoding.toNat r b1) b1) := by
            rw [RegEncoding.writeNat_toNat]
    _   = RegEncoding.bit q (RegEncoding.writeNat r (RegEncoding.toNat r b2) b2) := by
            simpa [hNat] using
              (RegEncoding.bit_writeNat_in
                (r := r) (v := RegEncoding.toNat r b1)
                (b1 := b1) (b2 := b2) (q := q) hqlo hqhi)
    _   = RegEncoding.bit q b2 := by
            rw [RegEncoding.writeNat_toNat]

lemma basis_eq_of_sameOutside_and_slots
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ}
  (dst : LayoutState k)
  (bMid bNext : qs.Basis)
  (hSO : SameOutsideLayout qs dst bMid bNext)
  (hXslots :
    ∀ i : Fin k,
      ExtRegEncoding.extToInt (dst.xslot i) bNext
        = ExtRegEncoding.extToInt (dst.xslot i) bMid)
  (hZslots :
    ∀ i : Fin k,
      ExtRegEncoding.extToInt (dst.zslot i) bNext
        = ExtRegEncoding.extToInt (dst.zslot i) bMid)
  (hcover : CoversLayoutBits dst)
  (hbit_of_ext :
    ∀ (e : ExtReg) (b1 b2 : qs.Basis) (q : ℕ),
      ExtRegEncoding.extToInt e b1 = ExtRegEncoding.extToInt e b2 →
      e.base.lo ≤ q → q < e.base.hi →
      RegEncoding.bit q b1 = RegEncoding.bit q b2) :
  bNext = bMid := by
  apply RegEncoding.basis_ext
  intro q
  rcases hcover q with hx | hz | hout
  · rcases hx with ⟨i, hqlo, hqhi⟩
    exact hbit_of_ext (dst.xslot i) bNext bMid q (hXslots i) hqlo hqhi
  · rcases hz with ⟨i, hqlo, hqhi⟩
    exact hbit_of_ext (dst.zslot i) bNext bMid q (hZslots i) hqlo hqhi
  · exact hbit_of_ext (ExtReg.ofReg (qubitReg q)) bNext bMid q
      (by
        symm
        exact hSO (ExtReg.ofReg (qubitReg q)) hout)
      (by simp [qubitReg, ExtReg.ofReg])
      (by simp [qubitReg, ExtReg.ofReg])

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
    Section 10: Phase-block helpers
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

lemma qubit_in_layout_or_outside
  {k : ℕ} (dst : LayoutState k) (q : ℕ) :
  (∃ i : Fin k, (dst.xslot i).base.lo ≤ q ∧ q < (dst.xslot i).base.hi) ∨
  (∃ i : Fin k, (dst.zslot i).base.lo ≤ q ∧ q < (dst.zslot i).base.hi) ∨
  OutsideLayout dst (ExtReg.ofReg (qubitReg q)) := by
  by_cases hx : ∃ i : Fin k, (dst.xslot i).base.lo ≤ q ∧ q < (dst.xslot i).base.hi
  · exact Or.inl hx
  · by_cases hz : ∃ i : Fin k, (dst.zslot i).base.lo ≤ q ∧ q < (dst.zslot i).base.hi
    · exact Or.inr (Or.inl hz)
    · exact Or.inr (Or.inr (by
        constructor
        · intro i
          have hnot : ¬ ((dst.xslot i).base.lo ≤ q ∧ q < (dst.xslot i).base.hi) := by
            intro hqi
            exact hx ⟨i, hqi.1, hqi.2⟩
          unfold Disjoint qubitReg
          simp at *; simp[ExtReg.ofReg]
          omega
        · intro i
          have hnot : ¬ ((dst.zslot i).base.lo ≤ q ∧ q < (dst.zslot i).base.hi) := by
            intro hqi
            exact hz ⟨i, hqi.1, hqi.2⟩
          unfold Disjoint qubitReg
          simp at *; simp[ExtReg.ofReg]
          omega))

lemma phaseScalarFrom_ne_zero
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  (k : ℕ) (phi : ℝ) (coeff : Fin (q k) → ℚ)
  (src : LayoutState k) (b0 : qs.Basis) :
  ∀ (pts : List Point) (n : ℕ) (hn : n + pts.length = q k),
    phaseScalarFrom (qs := qs) k phi coeff src b0 pts n hn ≠ 0 := by
  intro pts
  induction pts with
  | nil =>
      intro n hn
      simp [phaseScalarFrom]
  | cons pt pts ih =>
      intro n hn
      simp [phaseScalarFrom]
      have htail :
          phaseScalarFrom (qs := qs) k phi coeff src b0 pts (n + 1)
            (by
              simp at hn
              omega) ≠ 0 := by
        exact ih (n + 1) (by
          simp at hn
          omega)
      aesop

lemma ket_eq_of_same_nonzero_smul
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  [GateSemanticsFacts qs]
  {a : ℂ} {b1 b2 : qs.Basis}
  (ha : a ≠ 0)
  (h : a • qs.ket b1 = a • qs.ket b2) :
  b1 = b2 := by
  have hket : qs.ket b1 = qs.ket b2 := by
    simp_all only [ne_eq, not_false_eq_true, smul_right_inj]
  exact qs.ket_inj hket

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

lemma encodesStateFrom_start_unique_of_ext
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ}
  (src dst : LayoutState k)
  (b0 b1 b2 : qs.Basis)
  (h1 : EncodesStateFrom (qs := qs) src dst State.start_state b0 b1)
  (h2 : EncodesStateFrom (qs := qs) src dst State.start_state b0 b2)
  (hdet :
    (∀ i : Fin k,
      ExtRegEncoding.extToInt (dst.xslot i) b1 =
      ExtRegEncoding.extToInt (dst.xslot i) b2) ∧
    (∀ i : Fin k,
      ExtRegEncoding.extToInt (dst.zslot i) b1 =
      ExtRegEncoding.extToInt (dst.zslot i) b2) →
    b1 = b2) :
  b1 = b2 := by
  apply hdet
  constructor
  · intro i
    calc
      ExtRegEncoding.extToInt (dst.xslot i) b1
          = evalRowX (qs := qs) src (State.start_state i) b0 := h1.1 i
      _ = ExtRegEncoding.extToInt (dst.xslot i) b2 := (h2.1 i).symm
  · intro i
    calc
      ExtRegEncoding.extToInt (dst.zslot i) b1
          = evalRowZ (qs := qs) src (State.start_state i) b0 := h1.2 i
      _ = ExtRegEncoding.extToInt (dst.zslot i) b2 := (h2.2 i).symm

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

/-- Use the standalone math definition as the real meaning of good Toom-Cook points. -/
def GoodToomCookPoints
  (k : ℕ)
  (pts : List Point)
  (hpts : pts.length = q k) : Prop :=
  ToomCookMath.GoodInterpolationPoints
    (row := interpEntry k)
    (pts := ToomCookMath.listToFin pts hpts)

/--
This is the rational version of the integer phase term already appearing in
`phaseScalarFrom`.
-/
def tcPointTerm
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ}
  (st : LayoutState k)
  (b : qs.Basis)
  (pts : List Point)
  (hpts : pts.length = q k) :
  Fin (q k) → ℚ :=
  fun i =>
    ((evalRowX (qs := qs) st
        (expectedRow (k := k) ((ToomCookMath.listToFin pts hpts) i)) b
      *
      evalRowZ (qs := qs) st
        (expectedRow (k := k) ((ToomCookMath.listToFin pts hpts) i)) b : ℤ) : ℚ)

/-- The final target product, as a rational number. -/
def tcTarget
  (qs : QSemantics)
  [RegEncoding QSemantics.Basis]
  [ExtRegEncoding qs.Basis]
  (x z : ExtReg)
  (b : qs.Basis) : ℚ :=
  (((ExtRegEncoding.extToInt x b) *
    (ExtRegEncoding.extToInt z b) : ℤ) : ℚ)

def tcProductCoeff
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ}
  (st : LayoutState k)
  (b : qs.Basis) :
  Fin (q k) → ℚ :=
  fun l =>
    ∑ ij : Fin k × Fin k,
      if _h : ij.1.1 + ij.2.1 = l.1 then
        ((sourceChunkXInt (qs := qs) st ij.1 b *
          sourceChunkZInt (qs := qs) st ij.2 b : ℤ) : ℚ)
      else
        0

lemma phaseCoeffFromPtsWidth_eq_interpCoeff
  {k W : ℕ}
  (pts : List Point)
  (hpts : pts.length = q k) :
  phaseCoeffFromPtsWidth k W pts hpts
    =
  ToomCookMath.interpCoeff
    (row := interpEntry k)
    (pts := ToomCookMath.listToFin pts hpts)
    ((2 : ℚ) ^ W) := by
  funext i
  simp [ phaseCoeffFromPtsWidth, phaseCoeffFromPts, ToomCookMath.interpCoeff]
  unfold ToomCookMath.interpMatrix ToomCookMath.radixRow interpMatrix radixRow ptsToFin ToomCookMath.listToFin
  simp


lemma phaseScalarFrom_eq_phaseScalarFromList_aux
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ}
  (phi : ℝ)
  (coeff : Fin (q k) → ℚ)
  (st : LayoutState k)
  (b : qs.Basis)
  (full : List Point)
  (hfull : full.length = q k) :
  ∀ (rest : List Point) (n : ℕ)
    (hn : n + rest.length = q k),
    full.drop n = rest →
    phaseScalarFrom (qs := qs) k phi coeff st b rest n hn
      =
    ToomCookMath.phaseScalarFromList
      phi coeff (tcPointTerm qs st b full hfull) rest n hn := by
  intro rest
  induction rest with
  | nil =>
      intro n hn hdrop
      simp [phaseScalarFrom, ToomCookMath.phaseScalarFromList]

  | cons pt rest ih =>
      intro n hn hdrop

      have hnlt : n < full.length := by
        rw [hfull]
        simp at hn
        omega

      have hget :
          (ToomCookMath.listToFin full hfull)
            ⟨n, by simpa [hfull] using hnlt⟩ = pt := by
        unfold ToomCookMath.listToFin
        simp_all
        have hget? : full[n]? = some pt := by
          have h0 := congrArg (fun xs : List Point => xs[0]?) hdrop
          simpa [List.getElem?_drop, Nat.zero_add] using h0

        have hget?₂ : some full[n] = some pt := by
          simpa [List.getElem?_eq_getElem hnlt] using hget?

        exact Option.some.inj hget?₂

      have htail_drop :
          full.drop (n + 1) = rest := by
        have := congrArg List.tail hdrop
        have htail : (List.drop n full).tail = rest := by
          simpa using this

        have hdrop_tail :
            ∀ (xs : List Point) (m : ℕ),
              (List.drop m xs).tail = List.drop (m + 1) xs := by
          simp

        have htail : (List.drop n full).tail = rest := by
          simpa using this

        rw [← hdrop_tail full n]
        exact htail

      simp [phaseScalarFrom, ToomCookMath.phaseScalarFromList]

      have hterm :
          tcPointTerm qs st b full hfull
            ⟨n, by
              rw [← hn]
              simp
            ⟩
          =
          ((evalRowX (qs := qs) st (expectedRow (k := k) pt) b *
            evalRowZ (qs := qs) st (expectedRow (k := k) pt) b : ℤ) : ℚ) := by
        unfold tcPointTerm
        simp [hget]

      rw [hterm]

      have htail :
          phaseScalarFrom (qs := qs) k phi coeff st b rest (n + 1)
            (by
              simp at hn
              omega)
          =
          ToomCookMath.phaseScalarFromList
            phi coeff (tcPointTerm qs st b full hfull) rest (n + 1)
            (by
              simp at hn
              omega) := by
        exact ih (n + 1) (by
          simp at hn
          omega) htail_drop

      rw [htail]
      unfold ToomCookMath.phaseFactor

      have hprodC :
          (((evalRowX (qs := qs) st (expectedRow (k := k) pt) b *
              evalRowZ (qs := qs) st (expectedRow (k := k) pt) b : ℤ) : ℚ) : ℂ)
            =
          ((evalRowX (qs := qs) st (expectedRow (k := k) pt) b : ℂ) *
          (evalRowZ (qs := qs) st (expectedRow (k := k) pt) b : ℂ)) := by
        norm_num

      rw [hprodC]
      simp[mul_comm]

lemma phaseScalarFrom_eq_phaseScalarFromList
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ}
  (phi : ℝ)
  (coeff : Fin (q k) → ℚ)
  (st : LayoutState k)
  (b : qs.Basis)
  (pts : List Point)
  (hpts : pts.length = q k) :
  phaseScalarFrom (qs := qs) k phi coeff st b pts 0 (by simpa using hpts)
    =
  ToomCookMath.phaseScalarFromList phi coeff (tcPointTerm qs st b pts hpts) pts 0
    (by simpa using hpts) := by
  simpa using
    phaseScalarFrom_eq_phaseScalarFromList_aux
      (qs := qs)
      (phi := phi)
      (coeff := coeff)
      (st := st)
      (b := b)
      (full := pts)
      (hfull := hpts)
      (rest := pts)
      (n := 0)
      (hn := by simpa using hpts)
      (by simp)

lemma expectedRow_mul_expectedRow_eq_interpEntry
  {k : ℕ}
  (hk : 1 < k)
  (pt : Point)
  (i j : Fin k) :
  (((expectedRow (k := k) pt i) *
    (expectedRow (k := k) pt j) : ℤ) : ℚ)
    =
  interpEntry k pt
    ⟨i.1 + j.1, by
      simp [q]
      omega
    ⟩ := by
  cases pt with
  | int z =>
      simp [expectedRow, interpEntry]
      norm_cast
      rw [pow_add]
  | inf =>
      simp [expectedRow, interpEntry, q]
      by_cases hi : i.1 + 1 = k
      · by_cases hj : j.1 + 1 = k
        · have hij : i.1 + j.1 = 2 * k - 2 := by omega
          cases k with
          | zero =>
              omega

          | succ k' =>
              have hi_last : i = ⟨k', by omega⟩ := by
                apply Fin.ext
                exact Nat.succ_injective hi

              have hj_last : j = ⟨k', by omega⟩ := by
                apply Fin.ext
                exact Nat.succ_injective hj

              have hdeg : i.1 + j.1 = 2 * (k' + 1) - 1 - 1 := by
                omega
              simp [hdeg]
              simp_all only [lt_add_iff_pos_left, ↓reduceIte]
        · have hij : i.1 + j.1 ≠ 2 * k - 2 := by omega

          cases k with
          | zero =>
              omega

          | succ k' =>
              have hi_last : i = ⟨k', by omega⟩ := by
                apply Fin.ext
                exact Nat.succ_injective hi

              have hj_not_last : j ≠ ⟨k', by omega⟩ := by
                intro hj_last
                apply hj
                rw [hj_last]
              have hdeg : k' + j.1 ≠ 2 * (k' + 1) - 1 - 1 := by
                omega
              aesop

      · by_cases hj : j.1 + 1 = k
        · have hij : i.1 + j.1 ≠ 2 * k - 2 := by omega
          cases k with
          | zero =>
              omega

          | succ k' =>
              have hj_last : j = ⟨k', by omega⟩ := by
                apply Fin.ext
                exact Nat.succ_injective hj

              have hi_not_last : i ≠ ⟨k', by omega⟩ := by
                intro hi_last
                apply hi
                rw [hi_last]

              aesop
        · have hij : i.1 + j.1 ≠ 2 * k - 2 := by omega

          cases k with
          | zero =>
              omega

          | succ k' =>
              have hi_not_last : i ≠ ⟨k', by omega⟩ := by
                intro hi_last
                apply hi
                rw [hi_last]
              have hj_not_last : j ≠ ⟨k', by omega⟩ := by
                intro hj_last
                apply hj
                rw [hj_last]
              have hdeg : i.1 + j.1 ≠ 2 * (k' + 1) - 1 - 1 := by
                omega
              simp [hi_not_last, hj_not_last, hdeg]

lemma sum_degree_group
  {k : ℕ}
  (hk : 1 < k)
  (A : Fin k × Fin k → ℚ)
  (row : Fin (q k) → ℚ) :
  (∑ l : Fin (q k),
      (∑ ij : Fin k × Fin k,
        if _h : ij.1.1 + ij.2.1 = l.1 then
          A ij
        else
          0) * row l)
    =
  ∑ ij : Fin k × Fin k,
    A ij * row
      ⟨ij.1.1 + ij.2.1, by
        simp [q]
        omega
      ⟩ := by
  classical
  calc
    (∑ l : Fin (q k),
        (∑ ij : Fin k × Fin k,
          if _h : ij.1.1 + ij.2.1 = l.1 then
            A ij
          else
            0) * row l)
        =
      ∑ l : Fin (q k),
        ∑ ij : Fin k × Fin k,
          (if _h : ij.1.1 + ij.2.1 = l.1 then
            A ij
          else
            0) * row l := by
          simp [Finset.sum_mul]
    _ =
      ∑ ij : Fin k × Fin k,
        ∑ l : Fin (q k),
          (if _h : ij.1.1 + ij.2.1 = l.1 then
            A ij
          else
            0) * row l := by
          rw [Finset.sum_comm]
    _ =
      ∑ ij : Fin k × Fin k,
        A ij * row
          ⟨ij.1.1 + ij.2.1, by
            simp [q]
            omega
          ⟩ := by
          apply Finset.sum_congr rfl
          intro ij hij
          let d : Fin (q k) :=
            ⟨ij.1.1 + ij.2.1, by
              simp [q]
              omega
            ⟩
          have hsingle :
              (∑ l : Fin (q k),
                (if _h : ij.1.1 + ij.2.1 = l.1 then
                  A ij
                else
                  0) * row l)
              =
              A ij * row d := by
            trans
              ((if _h : ij.1.1 + ij.2.1 = d.1 then A ij else 0) * row d)
            · refine Finset.sum_eq_single d ?_ ?_
              · intro l hl hld
                have hne : ij.1.1 + ij.2.1 ≠ l.1 := by
                  intro h
                  apply hld
                  apply Fin.ext
                  dsimp [d]
                  rw[h]
                simp [hne]
              · intro hd
                exfalso
                exact hd (Finset.mem_univ d)
            · dsimp [d]
              simp
          simpa [d] using hsingle

lemma tcPointTerm_eq_evalAtPoint_tcProductCoeff
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ}
  (hk : 1 < k)
  (st : LayoutState k)
  (b : qs.Basis)
  (pts : List Point)
  (hpts : pts.length = q k) :
  tcPointTerm qs st b pts hpts =
    fun i : Fin (q k) =>
      ToomCookMath.evalAtPoint
        (q k)
        (interpEntry k)
        (tcProductCoeff qs st b)
        ((ptsToFin k pts hpts) i) := by
  funext i
  unfold ToomCookMath.evalAtPoint

  let pt : Point := ptsToFin k pts hpts i
  let X : Fin k → ℤ := fun a => sourceChunkXInt (qs := qs) st a b
  let Z : Fin k → ℤ := fun a => sourceChunkZInt (qs := qs) st a b

  have hlist :
      (ToomCookMath.listToFin pts hpts) i = ptsToFin k pts hpts i := by
    unfold ToomCookMath.listToFin ptsToFin
    rfl

  unfold tcPointTerm tcProductCoeff evalRowX evalRowZ

  change
    (((∑ a : Fin k,
          expectedRow (k := k) pt a * X a) *
       (∑ b : Fin k,
          expectedRow (k := k) pt b * Z b) : ℤ) : ℚ)
      =
    ∑ l : Fin (q k),
      (∑ ij : Fin k × Fin k,
        if _h : ij.1.1 + ij.2.1 = l.1 then
          ((X ij.1 * Z ij.2 : ℤ) : ℚ)
        else
          0) *
        interpEntry k pt l

  calc
    (((∑ a : Fin k,
          expectedRow (k := k) pt a * X a) *
       (∑ b : Fin k,
          expectedRow (k := k) pt b * Z b) : ℤ) : ℚ)
        =
      ∑ ij : Fin k × Fin k,
        (((expectedRow (k := k) pt ij.1 * X ij.1) *
          (expectedRow (k := k) pt ij.2 * Z ij.2) : ℤ) : ℚ) := by
          norm_cast
          calc
            (∑ a : Fin k, expectedRow pt a * X a) *
                (∑ b : Fin k, expectedRow pt b * Z b)
                =
              ∑ a : Fin k,
                (expectedRow pt a * X a) *
                  (∑ b : Fin k, expectedRow pt b * Z b) := by
                rw [Finset.sum_mul]
            _ =
              ∑ a : Fin k,
                ∑ b : Fin k,
                  (expectedRow pt a * X a) *
                    (expectedRow pt b * Z b) := by
                apply Finset.sum_congr rfl
                intro a ha
                rw [Finset.mul_sum]
            _ =
              ∑ ij : Fin k × Fin k,
                (expectedRow pt ij.1 * X ij.1) *
                  (expectedRow pt ij.2 * Z ij.2) := by
                  simpa using
                    (Finset.sum_product
                      (s := (Finset.univ : Finset (Fin k)))
                      (t := (Finset.univ : Finset (Fin k)))
                      (f := fun ij : Fin k × Fin k =>
                        expectedRow pt ij.1 * X ij.1 *
                          (expectedRow pt ij.2 * Z ij.2))).symm
            _ =
              ∑ ij : Fin k × Fin k,
                expectedRow pt ij.1 * X ij.1 *
                  (expectedRow pt ij.2 * Z ij.2) := by
                apply Finset.sum_congr rfl
                intro ij hij
                ring

    _ =
      ∑ ij : Fin k × Fin k,
        ((X ij.1 * Z ij.2 : ℤ) : ℚ) *
          interpEntry k pt
            ⟨ij.1.1 + ij.2.1, by
              simp [q]
              omega
            ⟩ := by
          apply Finset.sum_congr rfl
          intro ij _
          have hrow :=
            expectedRow_mul_expectedRow_eq_interpEntry
              (k := k) hk pt ij.1 ij.2
          calc
            (((expectedRow (k := k) pt ij.1 * X ij.1) *
              (expectedRow (k := k) pt ij.2 * Z ij.2) : ℤ) : ℚ)
                =
              (((expectedRow (k := k) pt ij.1 *
                 expectedRow (k := k) pt ij.2) *
                (X ij.1 * Z ij.2) : ℤ) : ℚ) := by
                  norm_num
                  ring
            _ =
              (((expectedRow (k := k) pt ij.1 *
                 expectedRow (k := k) pt ij.2 : ℤ) : ℚ) *
                ((X ij.1 * Z ij.2 : ℤ) : ℚ)) := by
                  norm_num
            _ =
              ((X ij.1 * Z ij.2 : ℤ) : ℚ) *
                interpEntry k pt
                  ⟨ij.1.1 + ij.2.1, by
                    simp [q]
                    omega
                  ⟩ := by
                    rw [hrow]
                    ring
    _ =
      ∑ l : Fin (q k),
        (∑ ij : Fin k × Fin k,
          if _h : ij.1.1 + ij.2.1 = l.1 then
            ((X ij.1 * Z ij.2 : ℤ) : ℚ)
          else
            0) *
          interpEntry k pt l := by
          symm
          exact sum_degree_group
            (k := k)
            hk
            (fun ij => ((X ij.1 * Z ij.2 : ℤ) : ℚ))
            (fun l => interpEntry k pt l)

lemma GoodToomCookPoints.to_GoodInterpolationPoints
  {k : ℕ}
  {pts : List Point}
  (hpts : pts.length = q k)
  (hInterp : GoodToomCookPoints k pts hpts) :
  ToomCookMath.GoodInterpolationPoints
    (interpEntry k)
    (ptsToFin k pts hpts) := by
  -- probably by unfolding GoodToomCookPoints
  simpa [GoodToomCookPoints, ptsToFin]

lemma evalAtRadix_tcProductCoeff_eq_chunk_product
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ}
  (hk : 1 < k)
  (st : LayoutState k)
  (b : qs.Basis)
  (B : ℚ) :
  ToomCookMath.evalAtRadix
      (q k)
      (tcProductCoeff qs st b)
      B
    =
  (∑ i : Fin k,
      ((sourceChunkXInt (qs := qs) st i b : ℤ) : ℚ) * B ^ (i : ℕ))
    *
  (∑ j : Fin k,
      ((sourceChunkZInt (qs := qs) st j b : ℤ) : ℚ) * B ^ (j : ℕ)) := by
  classical

  let X : Fin k → ℚ :=
    fun i => ((sourceChunkXInt (qs := qs) st i b : ℤ) : ℚ)

  let Z : Fin k → ℚ :=
    fun i => ((sourceChunkZInt (qs := qs) st i b : ℤ) : ℚ)

  unfold ToomCookMath.evalAtRadix tcProductCoeff

  calc
    (∑ l : Fin (q k),
        (∑ ij : Fin k × Fin k,
          if _h : ij.1.1 + ij.2.1 = l.1 then
            ((sourceChunkXInt (qs := qs) st ij.1 b *
              sourceChunkZInt (qs := qs) st ij.2 b : ℤ) : ℚ)
          else
            0) *
          B ^ (l : ℕ))
        =
      ∑ ij : Fin k × Fin k,
        (X ij.1 * Z ij.2) *
          B ^ (ij.1.1 + ij.2.1) := by
        simpa [X, Z] using
          sum_degree_group
            (k := k)
            hk
            (fun ij : Fin k × Fin k => X ij.1 * Z ij.2)
            (fun l : Fin (q k) => B ^ (l : ℕ))

    _ =
      ∑ ij : Fin k × Fin k,
        (X ij.1 * B ^ (ij.1 : ℕ)) *
          (Z ij.2 * B ^ (ij.2 : ℕ)) := by
        apply Finset.sum_congr rfl
        intro ij _
        have hp :
            B ^ (ij.1.1 + ij.2.1)
              =
            B ^ (ij.1 : ℕ) * B ^ (ij.2 : ℕ) := by
          rw [pow_add]
        rw [hp]
        ring

    _ =
      (∑ i : Fin k, X i * B ^ (i : ℕ)) *
      (∑ j : Fin k, Z j * B ^ (j : ℕ)) := by
        symm
        calc
          (∑ i : Fin k, X i * B ^ (i : ℕ)) *
          (∑ j : Fin k, Z j * B ^ (j : ℕ))
              =
            ∑ i : Fin k,
              (X i * B ^ (i : ℕ)) *
              (∑ j : Fin k, Z j * B ^ (j : ℕ)) := by
              rw [Finset.sum_mul]

          _ =
            ∑ i : Fin k,
              ∑ j : Fin k,
                (X i * B ^ (i : ℕ)) *
                (Z j * B ^ (j : ℕ)) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.mul_sum]

          _ =
            ∑ ij : Fin k × Fin k,
              (X ij.1 * B ^ (ij.1 : ℕ)) *
              (Z ij.2 * B ^ (ij.2 : ℕ)) := by
              simpa using
                (Finset.sum_product
                  (s := (Finset.univ : Finset (Fin k)))
                  (t := (Finset.univ : Finset (Fin k)))
                  (f := fun ij : Fin k × Fin k =>
                    X ij.1 * B ^ (ij.1 : ℕ) * (Z ij.2 * B ^ (ij.2 : ℕ)))).symm
    _ =
      (∑ i : Fin k,
          ((sourceChunkXInt (qs := qs) st i b : ℤ) : ℚ) * B ^ (i : ℕ))
        *
      (∑ j : Fin k,
          ((sourceChunkZInt (qs := qs) st j b : ℤ) : ℚ) * B ^ (j : ℕ)) := by
        simp [X, Z]

lemma sourceChunks_reconstruct_x
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [ExtRegEncoding qs.Basis]
  [ExtRegSplitSemantics qs.Basis]
  {k : ℕ}
  (hk : 0 < k)
  (x z : ExtReg)
  (b : qs.Basis) :
  let stInit : LayoutState k :=
    initSignedLayoutState (Basis := qs.Basis) x z k
  let W : ℕ := phaseLimbWidth x z k
  let B : ℚ := (2 : ℚ) ^ W
  ((ExtRegEncoding.extToInt x b : ℤ) : ℚ)
    =
  ∑ i : Fin k,
    ((sourceChunkXInt (qs := qs) stInit i b : ℤ) : ℚ) * B ^ (i : ℕ) := by
  dsimp
  let W : ℕ := phaseLimbWidth x z k
  have hValid : ValidPhaseSplit x k W := by
    dsimp [W]
    exact phaseLimbWidth_valid_left x z hk
  have hrec :
      ((ExtRegEncoding.extToInt x b : ℤ) : ℚ)
        =
      ∑ i : Fin k,
        ((splitChunkInt x W i b : ℤ) : ℚ)
          * ((2 : ℚ) ^ W) ^ (i : ℕ) := by
    exact
      splitExtReg_reconstruct_int
        (Basis := qs.Basis)
        x k W b hValid
  simpa [initSignedLayoutState, sourceChunkXInt, splitChunkInt, W] using hrec

lemma sourceChunks_reconstruct_z
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [ExtRegEncoding qs.Basis]
  [ExtRegSplitSemantics qs.Basis]
  {k : ℕ}
  (hk : 0 < k)
  (x z : ExtReg)
  (b : qs.Basis) :
  let stInit : LayoutState k :=
    initSignedLayoutState (Basis := qs.Basis) x z k
  let W : ℕ := phaseLimbWidth x z k
  let B : ℚ := (2 : ℚ) ^ W
  ((ExtRegEncoding.extToInt z b : ℤ) : ℚ)
    =
  ∑ i : Fin k,
    ((sourceChunkZInt (qs := qs) stInit i b : ℤ) : ℚ) * B ^ (i : ℕ) := by
  dsimp
  let W : ℕ := phaseLimbWidth x z k
  have hValid : ValidPhaseSplit z k W := by
    dsimp [W]
    exact phaseLimbWidth_valid_right x z hk
  have hrec :
      ((ExtRegEncoding.extToInt z b : ℤ) : ℚ)
        =
      ∑ i : Fin k,
        ((splitChunkInt z W i b : ℤ) : ℚ)
          * ((2 : ℚ) ^ W) ^ (i : ℕ) := by
    exact
      splitExtReg_reconstruct_int
        (Basis := qs.Basis)
        z k W b hValid
  simpa [initSignedLayoutState, sourceChunkZInt, splitChunkInt, W] using hrec

lemma evalAtRadix_tcProductCoeff_eq_ext_product
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [ExtRegEncoding qs.Basis]
  [ExtRegSplitSemantics qs.Basis]
  {k : ℕ}
  (hk : 1 < k)
  (x z : ExtReg)
  (b : qs.Basis) :
  let stInit : LayoutState k :=
    initSignedLayoutState (Basis := qs.Basis) x z k
  let W : ℕ := phaseLimbWidth x z k
  let B : ℚ := (2 : ℚ) ^ W
  ToomCookMath.evalAtRadix
      (q k)
      (tcProductCoeff qs stInit b)
      B
    =
  (((ExtRegEncoding.extToInt x b *
     ExtRegEncoding.extToInt z b : ℤ) : ℚ)) := by
  dsimp

  set stInit : LayoutState k :=
    initSignedLayoutState (Basis := qs.Basis) x z k
  set W : ℕ := phaseLimbWidth x z k
  set B : ℚ := (2 : ℚ) ^ W

  have hChunk :
      ToomCookMath.evalAtRadix
          (q k)
          (tcProductCoeff qs stInit b)
          B
        =
      (∑ i : Fin k,
          ((sourceChunkXInt (qs := qs) stInit i b : ℤ) : ℚ) * B ^ (i : ℕ))
        *
      (∑ j : Fin k,
          ((sourceChunkZInt (qs := qs) stInit j b : ℤ) : ℚ) * B ^ (j : ℕ)) := by
    exact evalAtRadix_tcProductCoeff_eq_chunk_product
      (qs := qs)
      (hk := hk)
      (st := stInit)
      (b := b)
      (B := B)

  have hx :
      ((ExtRegEncoding.extToInt x b : ℤ) : ℚ)
        =
      ∑ i : Fin k,
        ((sourceChunkXInt (qs := qs) stInit i b : ℤ) : ℚ) * B ^ (i : ℕ) := by
    simpa [stInit, W, B] using
      sourceChunks_reconstruct_x
        (qs := qs)
        (x := x)
        (z := z)
        (b := b)
        (by omega)

  have hz :
      ((ExtRegEncoding.extToInt z b : ℤ) : ℚ)
        =
      ∑ i : Fin k,
        ((sourceChunkZInt (qs := qs) stInit i b : ℤ) : ℚ) * B ^ (i : ℕ) := by
    simpa [stInit, W, B] using
      sourceChunks_reconstruct_z
        (qs := qs)
        (x := x)
        (z := z)
        (b := b)
        (by omega)

  calc
    ToomCookMath.evalAtRadix
        (q k)
        (tcProductCoeff qs stInit b)
        B
        =
      (∑ i : Fin k,
          ((sourceChunkXInt (qs := qs) stInit i b : ℤ) : ℚ) * B ^ (i : ℕ))
        *
      (∑ j : Fin k,
          ((sourceChunkZInt (qs := qs) stInit j b : ℤ) : ℚ) * B ^ (j : ℕ)) := hChunk
    _ =
      ((ExtRegEncoding.extToInt x b : ℤ) : ℚ) *
      ((ExtRegEncoding.extToInt z b : ℤ) : ℚ) := by
        rw [← hx, ← hz]
    _ =
      (((ExtRegEncoding.extToInt x b *
         ExtRegEncoding.extToInt z b : ℤ) : ℚ)) := by
        norm_num

lemma toom_cook_interpolation
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [ExtRegEncoding qs.Basis]
  [ExtRegSplitSemantics qs.Basis]
  [GateSemanticsFacts qs]
  {k : ℕ}
  (hk : 1 < k)
  (phi : ℝ)
  (x z : ExtReg)
  (pts : List Point)
  (hpts : pts.length = q k)
  (hInterp : GoodToomCookPoints k pts hpts)
  (b : qs.Basis) :
  let stInit : LayoutState k :=
    initSignedLayoutState (Basis := qs.Basis) x z k
  let coeff : Fin (q k) → ℚ := phaseCoeffFromPtsForRegs k x z pts hpts
  phaseScalarFrom (qs := qs) k phi coeff stInit b pts 0 (by simpa using hpts)
    =
  Complex.exp
    (phi * Complex.I *
      (((ExtRegEncoding.extToInt x b : ℤ) : ℂ) *
       (((ExtRegEncoding.extToInt z b : ℤ) : ℂ)))) := by
  dsimp

  set stInit : LayoutState k :=
    initSignedLayoutState (Basis := qs.Basis) x z k
  set W : ℕ := phaseLimbWidth x z k
  set B : ℚ := (2 : ℚ) ^ W
  set coeff : Fin (q k) → ℚ := phaseCoeffFromPtsForRegs k x z pts hpts
  set polyCoeff : Fin (q k) → ℚ := tcProductCoeff qs stInit b

  have hCoeff :
      coeff =
        ToomCookMath.interpCoeff
          (interpEntry k)
          (ptsToFin k pts hpts)
          B := by
    simpa [coeff, phaseCoeffFromPtsForRegs, W, B] using
      phaseCoeffFromPtsWidth_eq_interpCoeff
        (k := k)
        (W := W)
        (pts := pts)
        (hpts := hpts)

  have hPoint :
      tcPointTerm qs stInit b pts hpts =
        fun i : Fin (q k) =>
          ToomCookMath.evalAtPoint
            (q k)
            (interpEntry k)
            polyCoeff
            ((ptsToFin k pts hpts) i) := by
    simpa [polyCoeff] using
      tcPointTerm_eq_evalAtPoint_tcProductCoeff
        (qs := qs)
        (hk := hk)
        (st := stInit)
        (b := b)
        (pts := pts)
        (hpts := hpts)

  have hInterpSum :
      (∑ i : Fin (q k),
          coeff i *
            ToomCookMath.evalAtPoint
              (q k)
              (interpEntry k)
              polyCoeff
              ((ptsToFin k pts hpts) i))
        =
      ToomCookMath.evalAtRadix
        (q k)
        polyCoeff
        B := by
    rw [hCoeff]
    exact ToomCookMath.interpCoeff_correct
      (row := interpEntry k)
      (pts := ptsToFin k pts hpts)
      (B := B)
      (polyCoeff := polyCoeff)
      (hGood :=
        GoodToomCookPoints.to_GoodInterpolationPoints
          (hpts := hpts)
          hInterp)

  have hRadix :
      ToomCookMath.evalAtRadix
          (q k)
          polyCoeff
          B
        =
      (((ExtRegEncoding.extToInt x b *
         ExtRegEncoding.extToInt z b : ℤ) : ℚ)) := by
    simpa [polyCoeff, stInit, W, B] using
      evalAtRadix_tcProductCoeff_eq_ext_product
        (qs := qs)
        (hk := hk)
        (x := x)
        (z := z)
        (b := b)

  have hScalar :
      phaseScalarFrom (qs := qs) k phi coeff stInit b pts 0 (by simpa using hpts)
        =
      Complex.exp
        (phi * Complex.I *
          (((∑ i : Fin (q k),
              coeff i *
                ToomCookMath.evalAtPoint
                  (q k)
                  (interpEntry k)
                  polyCoeff
                  ((ptsToFin k pts hpts) i) : ℚ) : ℂ))) := by
      have hScalarList :
          phaseScalarFrom (qs := qs) k phi coeff stInit b pts 0 (by simpa using hpts)
            =
          ToomCookMath.phaseScalarFromList
            phi coeff (tcPointTerm qs stInit b pts hpts) pts 0
            (by simpa using hpts) := by
        simpa using
          phaseScalarFrom_eq_phaseScalarFromList
            (qs := qs)
            (phi := phi)
            (coeff := coeff)
            (st := stInit)
            (b := b)
            (pts := pts)
            (hpts := hpts)

      rw [hScalarList]

      have hTerms :
          (tcPointTerm qs stInit b pts hpts)
            =
          fun i : Fin (q k) =>
            ToomCookMath.evalAtPoint
              (q k)
              (interpEntry k)
              polyCoeff
              (ptsToFin k pts hpts i) := hPoint

      rw [hTerms]

      exact
        ToomCookMath.phaseScalarFromList_eq_exp_sum
          (k := k)
          (phi := phi)
          (coeff := coeff)
          (terms := fun i : Fin (q k) =>
            ToomCookMath.evalAtPoint
              (q k)
              (interpEntry k)
              polyCoeff
              (ptsToFin k pts hpts i))
          (pts := pts)
          (hpts := hpts)

  calc
    phaseScalarFrom (qs := qs) k phi coeff stInit b pts 0 (by simpa using hpts)
        =
      Complex.exp
        (phi * Complex.I *
          (((∑ i : Fin (q k),
              coeff i *
                ToomCookMath.evalAtPoint
                  (q k)
                  (interpEntry k)
                  polyCoeff
                  ((ptsToFin k pts hpts) i) : ℚ) : ℂ))) := hScalar
    _ =
      Complex.exp
        (phi * Complex.I *
          (((ToomCookMath.evalAtRadix (q k) polyCoeff B : ℚ) : ℂ))) := by
        rw [hInterpSum]
    _ =
      Complex.exp
        (phi * Complex.I *
          (((((ExtRegEncoding.extToInt x b *
               ExtRegEncoding.extToInt z b : ℤ) : ℚ)) : ℂ))) := by
        rw [hRadix]
    _ =
      Complex.exp
        (phi * Complex.I *
          (((ExtRegEncoding.extToInt x b : ℤ) : ℂ) *
           (((ExtRegEncoding.extToInt z b : ℤ) : ℂ)))) := by
        congr 2
        norm_num

/-! =========================================================
    Section 11: Main compiled-body correctness theorem
========================================================= -/

lemma eval_compileOpsToSignedGate_correct_ket_of_blocks
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [ExtRegEncoding qs.Basis]
  [ExtRegSplitSemantics qs.Basis]
  [GateSemanticsFacts qs]
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ)
  (x z : ExtReg)
  (hxz : Disjoint x.base z.base)
  (pts : List Point)
  (hpts : List.length pts = q k)
  (hInterp : GoodToomCookPoints k pts hpts)
  (b : qs.Basis)
  (ops : Prog k)
  (hB : BlockDecomposition (k := k) (by omega) State.start_state ops pts)
  (run_ops_start_state : run? ops State.start_state = some State.start_state)
  (hSafeAdd :
    ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
      ops = pre ++ valid_ops.addScaled d s negSrc sh :: rest → d ≠ s) :
  let Wphase : ℕ := phaseLimbWidth x z k
  let coeff : Fin (q k) → ℚ := phaseCoeffFromPtsWidth k Wphase pts hpts
  qs.eval
      (compileOpsToSignedGate
        (Basis := qs.Basis) k hk phi x z coeff ops)
      (qs.ket b)
    =
  qs.eval
      (Gate.SignedPhaseProd phi x z)
      (qs.ket b) := by
  dsimp

  set need : NeededWidths k := scanNeededWidths x z ops
  set stInit : LayoutState k :=
    initSignedLayoutState (Basis := qs.Basis) x z k
  set stFinal : LayoutState k :=
    targetSignedLayoutState (Basis := qs.Basis) x z k need

  set Wphase : ℕ := phaseLimbWidth x z k
  set coeff : Fin (q k) → ℚ := phaseCoeffFromPtsWidth k Wphase pts hpts

  rcases eval_compileSignedAllocations_ket_fits
      (qs := qs)
      (x := x) (z := z)
      (hxz := hxz)
      (ops := ops) (b := b) with
    ⟨bAlloc, hAllocEval, hEncAlloc⟩

  have hFitsFinal :
    ∀ {τ : State k},
      (∃ pre rest, ops = pre ++ rest ∧ run? pre State.start_state = some τ) →
        (∀ j : Fin k,
          FitsSignedWidth (ExtReg.width (stFinal.xslot j))
            (evalRowX (qs := qs) stInit (τ j) b)) ∧
        (∀ j : Fin k,
          FitsSignedWidth (ExtReg.width (stFinal.zslot j))
            (evalRowZ (qs := qs) stInit (τ j) b)) := by
    intro τ hτ
    simpa [stInit, stFinal, need] using
      (allocated_widths_sound
        (qs := qs) (x := x) (z := z) (ops := ops) (b := b)
        (σ := τ) hτ)

  have hLayoutDisjoint : LayoutSlotsDisjoint stFinal := by
    subst stFinal
    unfold LayoutSlotsDisjoint
    constructor
    · intro i j hij
      have hsrc :
          Disjoint
            ((initSignedLayoutState (Basis := qs.Basis) x z k).xslot i).base
            ((initSignedLayoutState (Basis := qs.Basis) x z k).xslot j).base := by
        simpa [initSignedLayoutState] using
          splitExtReg_disjoint
            (Basis := qs.Basis)
            x k (phaseLimbWidth x z k)
            i j hij
      simpa [targetSignedLayoutState, widenExtRegTo] using hsrc
    · constructor
      · intro i j hij
        have hsrc :
            Disjoint
              ((initSignedLayoutState (Basis := qs.Basis) x z k).zslot i).base
              ((initSignedLayoutState (Basis := qs.Basis) x z k).zslot j).base := by
          simpa [initSignedLayoutState] using
            splitExtReg_disjoint
              (Basis := qs.Basis)
              z k (phaseLimbWidth x z k)
              i j hij
        simpa [targetSignedLayoutState, widenExtRegTo] using hsrc
      · intro i j
        have hsrc :
            Disjoint
              ((initSignedLayoutState (Basis := qs.Basis) x z k).xslot i).base
              ((initSignedLayoutState (Basis := qs.Basis) x z k).zslot j).base := by
          simpa [initSignedLayoutState] using
            splitExtReg_disjoint_of_disjoint
              (Basis := qs.Basis)
              x z k (phaseLimbWidth x z k)
              i j hxz
        simpa [targetSignedLayoutState, widenExtRegTo] using hsrc

  have hBodyDealloc :
    qs.eval
        (compileAnnotatedOpsToSignedGateAux k hk phi coeff stFinal
          (annotatePhaseTermsAux k 0 ops) ;;
         compileSignedDeallocations k stInit stFinal)
        (qs.ket bAlloc)
      =
    phaseScalarFrom (qs := qs) k phi coeff stInit b pts 0 (by simpa using hpts) •
      qs.ket b := by
    exact eval_compileAnnotatedOpsToSignedGateAux_of_blocks_then_dealloc
      (qs := qs)
      (k := k) (hk := hk)
      (phi := phi)
      (pts := pts)
      (hpts := hpts)
      (coeff := coeff)
      (src := stInit)
      (dst := stFinal)
      (b0 := b)
      (bMid := bAlloc)
      (ops := ops)
      hLayoutDisjoint
      hFitsFinal
      hSafeAdd
      hEncAlloc
      hAllocEval
      hB
      run_ops_start_state

  have hScalar :
      phaseScalarFrom (qs := qs) k phi coeff stInit b pts 0 (by simpa using hpts)
        =
      Complex.exp
        (phi * Complex.I *
          (((ExtRegEncoding.extToInt x b : ℤ) : ℂ) *
          (((ExtRegEncoding.extToInt z b : ℤ) : ℂ)))) := by
    simpa [stInit, Wphase, coeff] using
      toom_cook_interpolation
        (qs := qs)
        (hk := hk)
        (phi := phi)
        (x := x)
        (z := z)
        (pts := pts)
        (hpts := hpts)
        (hInterp := hInterp)
        (b := b)

  calc
    qs.eval
        (compileOpsToSignedGate
          (Basis := qs.Basis) k hk phi x z coeff ops)
        (qs.ket b)
        =
      qs.eval
        (compileAnnotatedOpsToSignedGateAux k hk phi coeff stFinal
          (annotatePhaseTermsAux k 0 ops) ;;
         compileSignedDeallocations k stInit stFinal)
        (qs.ket bAlloc) := by
          simp [
            compileOpsToSignedGate,
            stInit,
            stFinal,
            need,
            hAllocEval,
            qs.eval_seq
          ]
    _ =
      phaseScalarFrom (qs := qs) k phi coeff stInit b pts 0 (by simpa using hpts) •
        qs.ket b := hBodyDealloc
    _ =
      Complex.exp
        (phi * Complex.I *
          (((ExtRegEncoding.extToInt x b : ℤ) : ℂ) *
          (((ExtRegEncoding.extToInt z b : ℤ) : ℂ)))) •
        qs.ket b := by
          rw [hScalar]
    _ =
      qs.eval (SignedPhaseProd phi x z) (qs.ket b) := by
        symm
        simpa using
          (PhaseSemantics.eval_SignedPhaseProd_ket
            (qs := qs) (phi := phi) (x := x) (z := z) (b := b))

lemma eval_compileOpsToSignedGate_correct_ket
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [ExtRegEncoding qs.Basis]
  [ExtRegSplitSemantics qs.Basis]
  [GateSemanticsFacts qs]
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ)
  (x z : ExtReg)
  (hxz : Disjoint x.base z.base)
  (pts : List Point)
  (hpts : List.length pts = q k)
  (hInterp : GoodToomCookPoints k pts hpts)
  (b : qs.Basis)
  (ops : Prog k)
  (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops pts)
  (run_ops_start_state : run? ops State.start_state = some State.start_state) :
  let Wphase : ℕ := phaseLimbWidth x z k
  let coeff : Fin (q k) → ℚ := phaseCoeffFromPtsWidth k Wphase pts hpts
  qs.eval
      (compileOpsToSignedGate
        (Basis := qs.Basis) k hk phi x z coeff ops)
      (qs.ket b)
    =
  qs.eval
      (Gate.SignedPhaseProd phi x z)
      (qs.ket b) := by
  have hB :
      BlockDecomposition (k := k) (by omega) State.start_state ops pts :=
    progConsumesPts_has_blockDecomposition
      (k := k) (by omega) ops State.start_state pts hC.1
  simpa using
    (eval_compileOpsToSignedGate_correct_ket_of_blocks
      (qs := qs)
      (k := k) (hk := hk)
      (phi := phi)
      (x := x) (z := z)
      (hxz := hxz)
      (pts := pts) (hpts := hpts)
      (hInterp := hInterp)
      (b := b)
      (ops := ops)
      (hB := hB)
      (run_ops_start_state := run_ops_start_state)
      (hSafeAdd := hC.2))

lemma eval_compileOpsToSignedGate_correct
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [ExtRegEncoding qs.Basis]
  [ExtRegSplitSemantics qs.Basis]
  [GateSemanticsFacts qs]
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ)
  (x z : ExtReg)
  (hxz : Disjoint x.base z.base)
  (pts : List Point)
  (hpts : List.length pts = q k)
  (hInterp : GoodToomCookPoints k pts hpts)
  (ψ : qs.State)
  (ops : Prog k)
  (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops pts)
  (run_ops_start_state : run? ops State.start_state = some State.start_state) :
  let Wphase : ℕ := phaseLimbWidth x z k
  let coeff : Fin (q k) → ℚ := phaseCoeffFromPtsWidth k Wphase pts hpts
  qs.eval
      (compileOpsToSignedGate
        (Basis := qs.Basis) k hk phi x z coeff ops)
      ψ
    =
  qs.eval
      (Gate.SignedPhaseProd phi x z)
      ψ := by
  have hket :
      ∀ b : qs.Basis,
        let Wphase : ℕ := phaseLimbWidth x z k
        let coeff : Fin (q k) → ℚ := phaseCoeffFromPtsWidth k Wphase pts hpts
        qs.eval
            (compileOpsToSignedGate
              (Basis := qs.Basis) k hk phi x z coeff ops)
            (qs.ket b)
          =
        qs.eval
            (Gate.SignedPhaseProd phi x z)
            (qs.ket b) := by
    intro b
    exact
      eval_compileOpsToSignedGate_correct_ket
        (qs := qs)
        (k := k) (hk := hk)
        (phi := phi)
        (x := x) (z := z)
        (hxz := hxz)
        (pts := pts)
        (hpts := hpts)
        (hInterp := hInterp)
        (b := b)
        (ops := ops)
        (hC := hC)
        (run_ops_start_state := run_ops_start_state)

  exact gate_eq_of_ket_eq qs (by intro b; simpa using hket b) ψ

end Shor
