import ForShor.ShorVerification.Implementation.PhaseProduct.Statement
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.Layout
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.ExactWidth

/-!
# Widths lemmas

Theorems about the definitions in `Statement.lean` that no definition needs.
-/

/-! ---------------------------------------------------------
    Phase-Product Compiler: Widths (moved from `Statement.lean`)
--------------------------------------------------------- -/

namespace Shor
open Gate
open Operations
open scoped BigOperators

/-! =========================================================
    Width scanning
========================================================= -/

/-- Initial `x` slot width agrees with the symbolic initial width state. -/
lemma stInit_xslot_width
    {x z : ExtReg} {k : ℕ} (layout : Gate.PhaseProductLayout x z k) (i : Fin k) :
    ((initSignedLayoutState layout).xslot i).width = (initWidthState x z k).xw i := by
  change (layout.xSplit.child i).width = phaseSplitLogicalWidth x.width (phaseLimbWidth x z k) k i
  exact layout.xchild_width i

/-- Initial `z` slot width agrees with the symbolic initial width state. -/
lemma stInit_zslot_width
    {x z : ExtReg} {k : ℕ} (layout : Gate.PhaseProductLayout x z k) (i : Fin k) :
    ((initSignedLayoutState layout).zslot i).width = (initWidthState x z k).zw i := by
  change (layout.zSplit.child i).width = phaseSplitLogicalWidth z.width (phaseLimbWidth x z k) k i
  exact layout.zchild_width i

/-! =========================================================
    Scan consequences for target layouts
========================================================= -/

/-- A grown target `x` slot has exactly the common scanned width. -/
lemma targetSignedLayoutState_xslot_width_scan
    {x z : ExtReg}
    {k : ℕ}
    (layout : Gate.PhaseProductLayout x z k)
    (ops : Prog k)
    (i : Fin k)
    (hcap : (initSignedLayoutState layout).CanGrowToNeeds (scanNeededWidths x z ops)) :
    ((targetSignedLayoutState (initSignedLayoutState layout) (scanNeededWidths x z ops)).xslot i).width
      = commonNeededWidth (scanNeededWidths x z ops) := by
  let stInit := initSignedLayoutState layout
  let need := scanNeededWidths x z ops
  let Wwork := commonNeededWidth need
  have hinit : (stInit.xslot i).width = (initWidthState x z k).xw i := by
    simpa [stInit] using stInit_xslot_width layout i
  have hscan : (initWidthState x z k).xw i ≤ need.xneed i := by
    simpa [need] using (scanNeededWidths_ge_init x z ops i).1
  have hneed : need.xneed i + 1 ≤ Wwork := (commonNeededWidth_gt need i).1
  have hle : (stInit.xslot i).width ≤ Wwork := by
    rw [hinit]
    omega
  have hgrow : (stInit.xslot i).CanGrow (Wwork - (stInit.xslot i).width) := hcap.1 i
  simpa [stInit, need, Wwork, targetSignedLayoutState] using
    width_growExtRegTo (stInit.xslot i) Wwork hle hgrow

/-- A grown target `z` slot has exactly the common scanned width. -/
lemma targetSignedLayoutState_zslot_width_scan
    {x z : ExtReg}
    {k : ℕ}
    (layout : Gate.PhaseProductLayout x z k)
    (ops : Prog k)
    (i : Fin k)
    (hcap : (initSignedLayoutState layout).CanGrowToNeeds (scanNeededWidths x z ops)) :
    ((targetSignedLayoutState (initSignedLayoutState layout) (scanNeededWidths x z ops)).zslot i).width
      = commonNeededWidth (scanNeededWidths x z ops) := by
  let stInit := initSignedLayoutState layout
  let need := scanNeededWidths x z ops
  let Wwork := commonNeededWidth need
  have hinit : (stInit.zslot i).width = (initWidthState x z k).zw i := by
    simpa [stInit] using stInit_zslot_width layout i
  have hscan : (initWidthState x z k).zw i ≤ need.zneed i := by
    simpa [need] using (scanNeededWidths_ge_init x z ops i).2
  have hneed : need.zneed i + 1 ≤ Wwork := (commonNeededWidth_gt need i).2
  have hle : (stInit.zslot i).width ≤ Wwork := by
    rw [hinit]
    omega
  have hgrow : (stInit.zslot i).CanGrow (Wwork - (stInit.zslot i).width) := hcap.2 i
  simpa [stInit, need, Wwork, targetSignedLayoutState] using
    width_growExtRegTo (stInit.zslot i) Wwork hle hgrow

/-! =========================================================
    Width rules
========================================================= -/

/-- The exact child width is the exact width of the operands' active widths (`0 < k`). -/
theorem nextSignedWidthBy_exact {k : ℕ} (hk : 0 < k) (x z : ExtReg) (ops : Prog k) :
    nextSignedWidthBy .exact x z ops = exactSignedWidthOfWidths ops x.width z.width :=
  commonNeededWidth_exactNeeded hk ops x.width z.width

/-- A grown target `x` slot has exactly the common width, under either rule. -/
lemma targetSignedLayoutState_xslot_width_by (R : WidthRule)
    {x z : ExtReg} {k : ℕ} (layout : Gate.PhaseProductLayout x z k) (ops : Prog k) (i : Fin k)
    (hcap : (initSignedLayoutState layout).CanGrowToNeeds (neededWidthsBy R x z ops)) :
    ((targetSignedLayoutState (initSignedLayoutState layout) (neededWidthsBy R x z ops)).xslot i).width
      = commonNeededWidth (neededWidthsBy R x z ops) := by
  let stInit := initSignedLayoutState layout
  let need := neededWidthsBy R x z ops
  let Wwork := commonNeededWidth need
  have hinit : (stInit.xslot i).width = (initWidthState x z k).xw i := by
    simpa [stInit] using stInit_xslot_width layout i
  have hscan : (initWidthState x z k).xw i ≤ need.xneed i := by
    simpa [need] using (neededWidthsBy_ge_init R x z ops i).1
  have hneed : need.xneed i + 1 ≤ Wwork := (commonNeededWidth_gt need i).1
  have hle : (stInit.xslot i).width ≤ Wwork := by
    rw [hinit]
    omega
  have hgrow : (stInit.xslot i).CanGrow (Wwork - (stInit.xslot i).width) := hcap.1 i
  simpa [stInit, need, Wwork, targetSignedLayoutState] using
    width_growExtRegTo (stInit.xslot i) Wwork hle hgrow

/-- A grown target `z` slot has exactly the common width, under either rule. -/
lemma targetSignedLayoutState_zslot_width_by (R : WidthRule)
    {x z : ExtReg} {k : ℕ} (layout : Gate.PhaseProductLayout x z k) (ops : Prog k) (i : Fin k)
    (hcap : (initSignedLayoutState layout).CanGrowToNeeds (neededWidthsBy R x z ops)) :
    ((targetSignedLayoutState (initSignedLayoutState layout) (neededWidthsBy R x z ops)).zslot i).width
      = commonNeededWidth (neededWidthsBy R x z ops) := by
  let stInit := initSignedLayoutState layout
  let need := neededWidthsBy R x z ops
  let Wwork := commonNeededWidth need
  have hinit : (stInit.zslot i).width = (initWidthState x z k).zw i := by
    simpa [stInit] using stInit_zslot_width layout i
  have hscan : (initWidthState x z k).zw i ≤ need.zneed i := by
    simpa [need] using (neededWidthsBy_ge_init R x z ops i).2
  have hneed : need.zneed i + 1 ≤ Wwork := (commonNeededWidth_gt need i).2
  have hle : (stInit.zslot i).width ≤ Wwork := by
    rw [hinit]
    omega
  have hgrow : (stInit.zslot i).CanGrow (Wwork - (stInit.zslot i).width) := hcap.2 i
  simpa [stInit, need, Wwork, targetSignedLayoutState] using
    width_growExtRegTo (stInit.zslot i) Wwork hle hgrow

end Shor
