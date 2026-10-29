import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Layout
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.ExactWidth
import FastMultiplication.ShorVerification.Framework.Policy

/-!
# Phase-Product Compiler: Widths

Width scanning over a source operation program (`scanNeededWidths`), the
recursion-size parameters (`phaseInputSize`, `nextSignedWidth`), and the
lemmas connecting a scan's result back to the concrete layout it was scanned
from.

**Width rules.** The last section adds `neededWidthsBy R` / `nextSignedWidthBy R`
for a `WidthRule` (`Framework/Policy.lean`): `.scan` is `scanNeededWidths` /
`nextSignedWidth` above, unchanged; `.exact` is the exact width
(`ExactWidth.lean`). The compiler takes the rule from the policy, and every
policy uses the scan unless it says otherwise.
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
lemma scanNeededWidthsAux_x_ge {k : ℕ} (i : Fin k) :
    ∀ (ops : List (valid_ops k)) (cur : WidthState k) (mx : NeededWidths k),
      mx.xneed i ≤ (scanNeededWidthsAux cur mx ops).xneed i
  | [], cur, mx => by simp [scanNeededWidthsAux]
  | op :: rest, cur, mx => by
      simp [scanNeededWidthsAux]
      have htail :
          (mergeNeededWidths mx (widthsOfState (updateWidthState cur op))).xneed i ≤
          (scanNeededWidthsAux (updateWidthState cur op)
            (mergeNeededWidths mx (widthsOfState (updateWidthState cur op))) rest).xneed i :=
        scanNeededWidthsAux_x_ge (i := i) rest (updateWidthState cur op)
          (mergeNeededWidths mx (widthsOfState (updateWidthState cur op)))
      exact le_trans (le_max_left _ _) htail

/-- The scan result dominates the incoming `z` width lower bound. -/
lemma scanNeededWidthsAux_z_ge {k : ℕ} (i : Fin k) :
    ∀ (ops : List (valid_ops k)) (cur : WidthState k) (mx : NeededWidths k),
      mx.zneed i ≤ (scanNeededWidthsAux cur mx ops).zneed i
  | [], cur, mx => by simp [scanNeededWidthsAux]
  | op :: rest, cur, mx => by
      simp [scanNeededWidthsAux]
      have htail :
          (mergeNeededWidths mx (widthsOfState (updateWidthState cur op))).zneed i ≤
          (scanNeededWidthsAux (updateWidthState cur op)
            (mergeNeededWidths mx (widthsOfState (updateWidthState cur op))) rest).zneed i :=
        scanNeededWidthsAux_z_ge (i := i) rest (updateWidthState cur op)
          (mergeNeededWidths mx (widthsOfState (updateWidthState cur op)))
      exact le_trans (le_max_left _ _) htail

/-- Initial `x` slot width agrees with the symbolic initial width state. -/
lemma stInit_xslot_width
    {x z : ExtReg} {k : ℕ} (layout : Gate.PhaseProductLayout x z k) (i : Fin k) :
    ((initSignedLayoutState layout).xslot i).width = (initWidthState x z k).xw i := by
  change (layout.xSplit.child i).width = phaseSplitLogicalWidth x.width (phaseLimbWidth x z k) k i
  exact layout.xSplit.child_width i

/-- Initial `z` slot width agrees with the symbolic initial width state. -/
lemma stInit_zslot_width
    {x z : ExtReg} {k : ℕ} (layout : Gate.PhaseProductLayout x z k) (i : Fin k) :
    ((initSignedLayoutState layout).zslot i).width = (initWidthState x z k).zw i := by
  change (layout.zSplit.child i).width = phaseSplitLogicalWidth z.width (phaseLimbWidth x z k) k i
  exact layout.zSplit.child_width i

/-- The common target width dominates every scanned `x` need. -/
lemma commonNeededWidth_ge_xneed {k : ℕ} (need : NeededWidths k) (i : Fin k) :
  need.xneed i + 1 ≤ commonNeededWidth need := by
  unfold commonNeededWidth
  have h :
      max (need.xneed i) (need.zneed i)
        ≤ Finset.univ.sup (fun j : Fin k => max (need.xneed j) (need.zneed j)) :=
    Finset.le_sup (f := fun j : Fin k => max (need.xneed j) (need.zneed j)) (Finset.mem_univ i)
  have h' : need.xneed i ≤ _ := le_trans (le_max_left _ _) h
  omega

/-- The common target width dominates every scanned `z` need. -/
lemma commonNeededWidth_ge_zneed {k : ℕ} (need : NeededWidths k) (i : Fin k) :
  need.zneed i + 1 ≤ commonNeededWidth need := by
  unfold commonNeededWidth
  have h :
      max (need.xneed i) (need.zneed i)
        ≤ Finset.univ.sup (fun j : Fin k => max (need.xneed j) (need.zneed j)) :=
    Finset.le_sup (f := fun j : Fin k => max (need.xneed j) (need.zneed j)) (Finset.mem_univ i)
  have h' : need.zneed i ≤ _ := le_trans (le_max_right _ _) h
  omega

/-! =========================================================
    Scan consequences for target layouts
========================================================= -/

/-- The initial `x` width is included in the full width scan. -/
lemma scanNeededWidths_x_ge_init
    {k : ℕ} (x z : ExtReg) (ops : List (valid_ops k)) (i : Fin k) :
    (initWidthState x z k).xw i ≤ (scanNeededWidths x z ops).xneed i := by
  simp [scanNeededWidths]
  exact scanNeededWidthsAux_x_ge (i := i) ops (initWidthState x z k)
    (widthsOfState (initWidthState x z k))

/-- The initial z width is included in the full width scan. -/
lemma scanNeededWidths_z_ge_init
    {k : ℕ} (x z : ExtReg) (ops : List (valid_ops k)) (i : Fin k) :
    (initWidthState x z k).zw i ≤ (scanNeededWidths x z ops).zneed i := by
  simp [scanNeededWidths]
  exact scanNeededWidthsAux_z_ge (i := i) ops (initWidthState x z k)
    (widthsOfState (initWidthState x z k))

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
    simpa [need] using scanNeededWidths_x_ge_init x z ops i
  have hneed : need.xneed i + 1 ≤ Wwork := commonNeededWidth_ge_xneed need i
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
    simpa [need] using scanNeededWidths_z_ge_init x z ops i
  have hneed : need.zneed i + 1 ≤ Wwork := commonNeededWidth_ge_zneed need i
  have hle : (stInit.zslot i).width ≤ Wwork := by
    rw [hinit]
    omega
  have hgrow : (stInit.zslot i).CanGrow (Wwork - (stInit.zslot i).width) := hcap.2 i
  simpa [stInit, need, Wwork, targetSignedLayoutState] using
    width_growExtRegTo (stInit.zslot i) Wwork hle hgrow

/-! =========================================================
    Width rules: the scan, or the exact width
========================================================= -/

/-- The width needs the compiler grows every slot to, under rule `R`: the
scan (`scanNeededWidths`), or the exact width as a uniform record
(`exactNeededWidths`). -/
def neededWidthsBy (R : WidthRule) {k : ℕ} (x z : ExtReg) (ops : List (valid_ops k)) :
    NeededWidths k :=
  match R with
  | .scan => scanNeededWidths x z ops
  | .exact => exactNeededWidths ops x.width z.width

/-! Evaluation-only memo for the exact rule (declared before anything that
calls `neededWidthsBy`, so that every compiled caller goes through the
`@[csimp]` below). The compiled circuit generator
and the evaluation tier ask for the exact width at the same `(table, xw, zw)`
very many times; the scan was cheap per call, the exact rule recomputes the
reachable rows. `exactWidthMemo` is *defined* as the exact width (every proof
sees `exactSignedWidthOfWidths`) and *implemented* by a cache keyed on `k`,
the program object's address and the two widths; the cache holds the program,
so an address is not reused while its entry exists. Trusted code for compiled
evaluation only, never for a kernel proof. The `.scan` branch is untouched, so
compiled code on the scan rule runs exactly what it ran before. -/

initialize exactWidthCache : IO.Ref (Std.HashMap (ℕ × USize × ℕ × ℕ) (NonScalar × ℕ)) ← IO.mkRef {}

private unsafe def exactWidthMemoImpl {k : ℕ} (ops : Prog k) (xw zw : ℕ) : ℕ :=
  unsafeBaseIO do
    let key := (k, ptrAddrUnsafe ops, xw, zw)
    match (← exactWidthCache.get)[key]? with
    | some (_, v) => return v
    | none =>
      let v := exactSignedWidthOfWidths ops xw zw
      exactWidthCache.modify (·.insert key (unsafeCast ops, v))
      return v

/-- The exact width (memoised in compiled code; see above). -/
@[implemented_by exactWidthMemoImpl]
def exactWidthMemo {k : ℕ} (ops : Prog k) (xw zw : ℕ) : ℕ := exactSignedWidthOfWidths ops xw zw

/-- A uniform record from an already computed width (`noinline` keeps the
argument evaluated once, before the call). -/
@[noinline] def uniformNeededWidths (k E : ℕ) : NeededWidths k where
  xneed := fun _ => E - 1
  zneed := fun _ => E - 1

/-- `neededWidthsBy`, with the exact branch evaluated once through the memo. -/
def neededWidthsByFast (R : WidthRule) {k : ℕ} (x z : ExtReg) (ops : List (valid_ops k)) :
    NeededWidths k :=
  match R with
  | .scan => scanNeededWidths x z ops
  | .exact => uniformNeededWidths k (exactWidthMemo ops x.width z.width)

@[csimp] theorem neededWidthsBy_eq_fast : @neededWidthsBy = @neededWidthsByFast := by
  funext R k x z ops; cases R <;> rfl

/-- The child width under rule `R`. -/
def nextSignedWidthBy (R : WidthRule) {k : ℕ} (x z : ExtReg) (ops : Prog k) : ℕ :=
  commonNeededWidth (neededWidthsBy R x z ops)

@[simp] theorem neededWidthsBy_scan {k : ℕ} (x z : ExtReg) (ops : List (valid_ops k)) :
    neededWidthsBy .scan x z ops = scanNeededWidths x z ops := rfl

@[simp] theorem nextSignedWidthBy_scan {k : ℕ} (x z : ExtReg) (ops : Prog k) :
    nextSignedWidthBy .scan x z ops = nextSignedWidth x z ops := rfl

theorem neededWidthsBy_exact {k : ℕ} (x z : ExtReg) (ops : List (valid_ops k)) :
    neededWidthsBy .exact x z ops = exactNeededWidths ops x.width z.width := rfl

/-- The exact child width is the exact width of the operands' active widths (`0 < k`). -/
theorem nextSignedWidthBy_exact {k : ℕ} (hk : 0 < k) (x z : ExtReg) (ops : Prog k) :
    nextSignedWidthBy .exact x z ops = exactSignedWidthOfWidths ops x.width z.width :=
  commonNeededWidth_exactNeeded hk ops x.width z.width

/-- The initial `x` width is included in the width needs, under either rule. -/
lemma neededWidthsBy_x_ge_init (R : WidthRule)
    {k : ℕ} (x z : ExtReg) (ops : List (valid_ops k)) (i : Fin k) :
    (initWidthState x z k).xw i ≤ (neededWidthsBy R x z ops).xneed i := by
  cases R
  · exact scanNeededWidths_x_ge_init x z ops i
  · exact (exactInit_le ops x.width z.width i).1

/-- The initial `z` width is included in the width needs, under either rule. -/
lemma neededWidthsBy_z_ge_init (R : WidthRule)
    {k : ℕ} (x z : ExtReg) (ops : List (valid_ops k)) (i : Fin k) :
    (initWidthState x z k).zw i ≤ (neededWidthsBy R x z ops).zneed i := by
  cases R
  · exact scanNeededWidths_z_ge_init x z ops i
  · exact (exactInit_le ops x.width z.width i).2

/-- A grown target `x` slot has exactly the common width, under either rule. -/
lemma targetSignedLayoutState_xslot_width_by (R : WidthRule)
    {x z : ExtReg}
    {k : ℕ}
    (layout : Gate.PhaseProductLayout x z k)
    (ops : Prog k)
    (i : Fin k)
    (hcap : (initSignedLayoutState layout).CanGrowToNeeds (neededWidthsBy R x z ops)) :
    ((targetSignedLayoutState (initSignedLayoutState layout) (neededWidthsBy R x z ops)).xslot i).width
      = commonNeededWidth (neededWidthsBy R x z ops) := by
  let stInit := initSignedLayoutState layout
  let need := neededWidthsBy R x z ops
  let Wwork := commonNeededWidth need
  have hinit : (stInit.xslot i).width = (initWidthState x z k).xw i := by
    simpa [stInit] using stInit_xslot_width layout i
  have hscan : (initWidthState x z k).xw i ≤ need.xneed i := by
    simpa [need] using neededWidthsBy_x_ge_init R x z ops i
  have hneed : need.xneed i + 1 ≤ Wwork := commonNeededWidth_ge_xneed need i
  have hle : (stInit.xslot i).width ≤ Wwork := by
    rw [hinit]
    omega
  have hgrow : (stInit.xslot i).CanGrow (Wwork - (stInit.xslot i).width) := hcap.1 i
  simpa [stInit, need, Wwork, targetSignedLayoutState] using
    width_growExtRegTo (stInit.xslot i) Wwork hle hgrow

/-- A grown target `z` slot has exactly the common width, under either rule. -/
lemma targetSignedLayoutState_zslot_width_by (R : WidthRule)
    {x z : ExtReg}
    {k : ℕ}
    (layout : Gate.PhaseProductLayout x z k)
    (ops : Prog k)
    (i : Fin k)
    (hcap : (initSignedLayoutState layout).CanGrowToNeeds (neededWidthsBy R x z ops)) :
    ((targetSignedLayoutState (initSignedLayoutState layout) (neededWidthsBy R x z ops)).zslot i).width
      = commonNeededWidth (neededWidthsBy R x z ops) := by
  let stInit := initSignedLayoutState layout
  let need := neededWidthsBy R x z ops
  let Wwork := commonNeededWidth need
  have hinit : (stInit.zslot i).width = (initWidthState x z k).zw i := by
    simpa [stInit] using stInit_zslot_width layout i
  have hscan : (initWidthState x z k).zw i ≤ need.zneed i := by
    simpa [need] using neededWidthsBy_z_ge_init R x z ops i
  have hneed : need.zneed i + 1 ≤ Wwork := commonNeededWidth_ge_zneed need i
  have hle : (stInit.zslot i).width ≤ Wwork := by
    rw [hinit]
    omega
  have hgrow : (stInit.zslot i).CanGrow (Wwork - (stInit.zslot i).width) := hcap.2 i
  simpa [stInit, need, Wwork, targetSignedLayoutState] using
    width_growExtRegTo (stInit.zslot i) Wwork hle hgrow

end Shor
