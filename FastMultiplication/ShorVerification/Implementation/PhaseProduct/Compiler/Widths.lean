import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Layout

/-!
# Phase-Product Compiler: Widths

Width scanning over a source operation program (`scanNeededWidths`), the
recursion-size parameters (`phaseInputSize`, `nextSignedWidth`), and the
lemmas connecting a scan's result back to the concrete layout it was scanned
from. Split out of `DefsCore.lean`.
-/

namespace Shor
open Gate
open Operations
open scoped BigOperators

/-! =========================================================
    Width scanning
========================================================= -/


/-- Initial width bookkeeping now uses the uniform lower-limb phase layout. -/
def initWidthState (x z : ExtReg) (k : ℕ) : WidthState k :=
  let W := phaseLimbWidth x z k
  { xw := fun i => phaseSplitLogicalWidth (ExtReg.width x) W k i
    zw := fun i => phaseSplitLogicalWidth (ExtReg.width z) W k i }

/-- Pull the recursion in `scanNeededWidths` out to a top-level helper. -/
def scanNeededWidthsAux {k : ℕ} (cur : WidthState k) (mx : NeededWidths k) : List (valid_ops k) → NeededWidths k
  | [] => mx
  | op :: rest =>
      let cur' := updateWidthState cur op
      let mx' := mergeNeededWidths mx (widthsOfState cur')
      scanNeededWidthsAux cur' mx' rest

/-- Scan needed widths using the new initial width state. -/
def scanNeededWidths {k : ℕ} (x z : ExtReg) (ops : List (valid_ops k)) : NeededWidths k :=
  scanNeededWidthsAux (initWidthState x z k) (widthsOfState (initWidthState x z k)) ops

/-- The size parameter used when deciding whether a signed phase product
    should recurse again. -/

def phaseInputSize (x z : ExtReg) : ℕ := max x.width z.width

/-- The actual width of the recursively compiled chunk phase products. -/
def nextSignedWidth {k : ℕ} (x z : ExtReg) (ops : Prog k) : ℕ := commonNeededWidth (scanNeededWidths x z ops)

/-- The scan result dominates the incoming `x` width lower bound. -/
lemma scanNeededWidthsAux_x_ge
  {k : ℕ} (i : Fin k) :
  ∀ (ops : List (valid_ops k)) (cur : WidthState k) (mx : NeededWidths k),
    mx.xneed i ≤ (scanNeededWidthsAux cur mx ops).xneed i
  | [], cur, mx => by
      simp [scanNeededWidthsAux]
  | op :: rest, cur, mx => by
      simp [scanNeededWidthsAux]
      have htail :
          (mergeNeededWidths mx (widthsOfState (updateWidthState cur op))).xneed i
            ≤
          (scanNeededWidthsAux
              (updateWidthState cur op)
              (mergeNeededWidths mx (widthsOfState (updateWidthState cur op)))
              rest).xneed i :=
        scanNeededWidthsAux_x_ge
          (i := i)
          rest
          (updateWidthState cur op)
          (mergeNeededWidths mx (widthsOfState (updateWidthState cur op)))
      exact le_trans (le_max_left _ _) htail

/-- The scan result dominates the incoming `z` width lower bound. -/
lemma scanNeededWidthsAux_z_ge
  {k : ℕ} (i : Fin k) :
  ∀ (ops : List (valid_ops k)) (cur : WidthState k) (mx : NeededWidths k),
    mx.zneed i ≤ (scanNeededWidthsAux cur mx ops).zneed i
  | [], cur, mx => by
      simp [scanNeededWidthsAux]
  | op :: rest, cur, mx => by
      simp [scanNeededWidthsAux]
      have htail :
          (mergeNeededWidths mx (widthsOfState (updateWidthState cur op))).zneed i
            ≤
          (scanNeededWidthsAux
              (updateWidthState cur op)
              (mergeNeededWidths mx (widthsOfState (updateWidthState cur op)))
              rest).zneed i :=
        scanNeededWidthsAux_z_ge
          (i := i)
          rest
          (updateWidthState cur op)
          (mergeNeededWidths mx (widthsOfState (updateWidthState cur op)))
      exact le_trans (le_max_left _ _) htail

/-- Initial `x` slot width agrees with the symbolic initial width state. -/
lemma stInit_xslot_width
    {x z : ExtReg}
    {k : ℕ}
    (layout : Gate.PhaseProductLayout x z k)
    (i : Fin k) :
    ((initSignedLayoutState layout).xslot i).width
      =
    (initWidthState x z k).xw i := by
  change
    (layout.xSplit.child i).width
      =
    phaseSplitLogicalWidth
      x.width
      (phaseLimbWidth x z k)
      k i
  exact layout.xSplit.child_width i

/-- Initial `z` slot width agrees with the symbolic initial width state. -/
lemma stInit_zslot_width
    {x z : ExtReg}
    {k : ℕ}
    (layout : Gate.PhaseProductLayout x z k)
    (i : Fin k) :
    ((initSignedLayoutState layout).zslot i).width
      =
    (initWidthState x z k).zw i := by
  change
    (layout.zSplit.child i).width
      =
    phaseSplitLogicalWidth
      z.width
      (phaseLimbWidth x z k)
      k i
  exact layout.zSplit.child_width i

/-- The common target width dominates every scanned `x` need. -/
lemma commonNeededWidth_ge_xneed {k : ℕ} (need : NeededWidths k) (i : Fin k) :
  need.xneed i + 1 ≤ commonNeededWidth need := by
  unfold commonNeededWidth
  have h :
      max (need.xneed i) (need.zneed i)
        ≤ Finset.univ.sup (fun j : Fin k => max (need.xneed j) (need.zneed j)) :=
    Finset.le_sup (f := fun j : Fin k => max (need.xneed j) (need.zneed j))
      (Finset.mem_univ i)
  have h' : need.xneed i ≤ _ := le_trans (le_max_left _ _) h
  omega

/-- The common target width dominates every scanned `z` need. -/
lemma commonNeededWidth_ge_zneed {k : ℕ} (need : NeededWidths k) (i : Fin k) :
  need.zneed i + 1 ≤ commonNeededWidth need := by
  unfold commonNeededWidth
  have h :
      max (need.xneed i) (need.zneed i)
        ≤ Finset.univ.sup (fun j : Fin k => max (need.xneed j) (need.zneed j)) :=
    Finset.le_sup (f := fun j : Fin k => max (need.xneed j) (need.zneed j))
      (Finset.mem_univ i)
  have h' : need.zneed i ≤ _ := le_trans (le_max_right _ _) h
  omega

/-! =========================================================
    Section 6: Scan consequences for target layouts
========================================================= -/

/-- The initial `x` width is included in the full width scan. -/
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

/-- A grown target `x` slot has exactly the common scanned width. -/
lemma targetSignedLayoutState_xslot_width_scan
    {x z : ExtReg}
    {k : ℕ}
    (layout : Gate.PhaseProductLayout x z k)
    (ops : Prog k)
    (i : Fin k)
    (hcap :
      (initSignedLayoutState layout).CanGrowToNeeds
        (scanNeededWidths x z ops)) :
    ((targetSignedLayoutState
      (initSignedLayoutState layout)
      (scanNeededWidths x z ops)).xslot i).width
      =
    commonNeededWidth (scanNeededWidths x z ops) := by
  let stInit := initSignedLayoutState layout
  let need := scanNeededWidths x z ops
  let Wwork := commonNeededWidth need
  have hinit :
      (stInit.xslot i).width =
        (initWidthState x z k).xw i := by
    simpa [stInit] using stInit_xslot_width layout i
  have hscan :
      (initWidthState x z k).xw i ≤ need.xneed i := by
    simpa [need] using
      scanNeededWidths_x_ge_init x z ops i
  have hneed :
      need.xneed i + 1 ≤ Wwork :=
    commonNeededWidth_ge_xneed need i
  have hle : (stInit.xslot i).width ≤ Wwork := by
    rw [hinit]
    omega
  have hgrow :
      (stInit.xslot i).CanGrow
        (Wwork - (stInit.xslot i).width) := by
    exact hcap.1 i
  simpa [stInit, need, Wwork, targetSignedLayoutState] using
    width_growExtRegTo
      (stInit.xslot i) Wwork hle hgrow

/-- A grown target `z` slot has exactly the common scanned width. -/
lemma targetSignedLayoutState_zslot_width_scan
    {x z : ExtReg}
    {k : ℕ}
    (layout : Gate.PhaseProductLayout x z k)
    (ops : Prog k)
    (i : Fin k)
    (hcap :
      (initSignedLayoutState layout).CanGrowToNeeds
        (scanNeededWidths x z ops)) :
    ((targetSignedLayoutState
      (initSignedLayoutState layout)
      (scanNeededWidths x z ops)).zslot i).width
      =
    commonNeededWidth (scanNeededWidths x z ops) := by
  let stInit := initSignedLayoutState layout
  let need := scanNeededWidths x z ops
  let Wwork := commonNeededWidth need
  have hinit :
      (stInit.zslot i).width =
        (initWidthState x z k).zw i := by
    simpa [stInit] using stInit_zslot_width layout i
  have hscan :
      (initWidthState x z k).zw i ≤ need.zneed i := by
    simpa [need] using
      scanNeededWidths_z_ge_init x z ops i
  have hneed :
      need.zneed i + 1 ≤ Wwork :=
    commonNeededWidth_ge_zneed need i
  have hle : (stInit.zslot i).width ≤ Wwork := by
    rw [hinit]
    omega
  have hgrow :
      (stInit.zslot i).CanGrow
        (Wwork - (stInit.zslot i).width) := by
    exact hcap.2 i
  simpa [stInit, need, Wwork, targetSignedLayoutState] using
    width_growExtRegTo
      (stInit.zslot i) Wwork hle hgrow


end Shor
