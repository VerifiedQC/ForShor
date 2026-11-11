import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import ForShor.ShorVerification.Framework.AbstractMachine.Gates
import ForShor.ShorVerification.Framework.AbstractMachine.LowGate
import ForShor.ShorVerification.Framework.Semantics.GateSemantics
import ForShor.ShorVerification.Framework.Semantics.LowGateSemantics
import ForShor.ShorVerification.Framework.ToomCookTable
import Mathlib.Tactic
import ForShor.ShorVerification.Framework.Policy
import ForShor.ShorVerification.Framework.Gatecount.CostModel
import ForShor.ShorVerification.Framework.Gatecount.ResourceModel
import ForShor.ShorVerification.Framework.Gatecount.PolicyModel

/-!
# Phase product: statement

Everything needed to state what `Main.lean` proves: the compiler from a Toom-Cook table to a
recursive circuit, the plans built from it, the workspace conditions, and the four assertions.
The definitions are plain data; their invariants are stated and proved in `Proofs/`.
-/

/-! ---------------------------------------------------------
    Phase-Product Compiler: Layout
--------------------------------------------------------- -/

namespace Shor

open Gate Operations
open scoped BigOperators Matrix

/-! =========================================================
    Layout states and width bookkeeping
========================================================= -/

/-- Current chunk-to-register assignment for the paired `x` and `z` work arrays. -/
structure LayoutState (k : ℕ) where
  xslot : Fin k → ExtReg
  zslot : Fin k → ExtReg

/-- Width bookkeeping only: current logical widths of each chunk. -/
structure WidthState (k : ℕ) where
  xw : Fin k → ℕ
  zw : Fin k → ℕ

/-- Symbolic width transition for one source operation. -/
def updateWidthState {k : ℕ} (st : WidthState k) : valid_ops k → WidthState k
  | .shiftL i n =>
      { xw := Function.update st.xw i (st.xw i + n)
        zw := Function.update st.zw i (st.zw i + n) }
  | .shiftR i n =>
      { xw := Function.update st.xw i (st.xw i - n)
        zw := Function.update st.zw i (st.zw i - n) }
  | .negate i =>
      { xw := Function.update st.xw i (st.xw i + 1)
        zw := Function.update st.zw i (st.zw i + 1) }
  | .addScaled dst src _negsrc sh =>
      let newX := 1 + max (st.xw dst) (st.xw src + sh)
      let newZ := 1 + max (st.zw dst) (st.zw src + sh)
      { xw := Function.update st.xw dst newX
        zw := Function.update st.zw dst newZ }
  | .phaseProduct _ =>
      st

/-- Per-slot maximum widths discovered by scanning the source program. -/
structure NeededWidths (k : ℕ) where
  xneed : Fin k → ℕ
  zneed : Fin k → ℕ

/-- Pointwise maximum of two width-demand records. -/
def mergeNeededWidths {k : ℕ} (a b : NeededWidths k) : NeededWidths k where
  xneed := fun i => max (a.xneed i) (b.xneed i)
  zneed := fun i => max (a.zneed i) (b.zneed i)

/-- Regard current widths as the current lower bound on needed widths. -/
def widthsOfState {k : ℕ} (st : WidthState k) : NeededWidths k where
  xneed := st.xw
  zneed := st.zw

/-- Common lower-limb width for both operands (`min`, so the limbs fit in both); the top
chunk takes the rest. -/
def phaseLimbWidth (x z : ExtReg) (k : ℕ) : ℕ :=
  min (x.width / k) (z.width / k)

/-! =========================================================
    Top-heavy phase splitting parameters
========================================================= -/

/-- The most significant chunk is the last chunk. -/
def isTopChunk {k : ℕ} (i : Fin k) : Prop := i.1 + 1 = k
instance {k : ℕ} (i : Fin k) : Decidable (isTopChunk i) := by
  unfold isTopChunk
  infer_instance

/-- Logical width of chunk `i`; the last chunk absorbs the remainder. -/
def phaseSplitLogicalWidth (w W k : ℕ) (i : Fin k) : ℕ := if isTopChunk i then w - i.1 * W else W

/-- Concrete active register slice corresponding to chunk `i`. -/
def phaseChunkActive (e : ExtReg) (k W : ℕ) (i : Fin k) : Reg :=
  (e.active.drop (i.1 * W)).take (phaseSplitLogicalWidth e.width W k i)

/-! =========================================================
    Abstract `ExtReg` split interface
========================================================= -/

/-- Split of one extendable register into active chunks, each with a reserve
register. Only the fact that `child` needs to form an `ExtReg` is recorded
here; the remaining invariants are stated and proved in `Proofs/`. -/
structure PhaseSplitLayout (parent : ExtReg) (k W : ℕ) where
  reserve : Fin k → Reg
  active_reserve_disjoint : ∀ i, Disjoint (phaseChunkActive parent k W i) (reserve i)

/-- The `i`th child extendable register induced by a split layout. -/
def PhaseSplitLayout.child {parent : ExtReg} {k W : ℕ} (layout : PhaseSplitLayout parent k W)
    (i : Fin k) : ExtReg :=
  ExtReg.withReserve (phaseChunkActive parent k W i) (layout.reserve i) (layout.active_reserve_disjoint i)

/-- Pair of compatible split layouts for the two operands of a phase product. -/
structure Gate.PhaseProductLayout (x z : ExtReg) (k : ℕ) where
  xSplit : PhaseSplitLayout x k (phaseLimbWidth x z k)
  zSplit : PhaseSplitLayout z k (phaseLimbWidth x z k)

/-- Uniform target width chosen to dominate every scanned `x` and `z` need, plus a sign bit. -/
def commonNeededWidth {k : ℕ} (need : NeededWidths k) : ℕ :=
  1 + Finset.univ.sup (fun i : Fin k => max (need.xneed i) (need.zneed i))

/-- Number of high bits added when growing `src` into `dst`. -/
def extraDelta (src dst : ExtReg) : ℕ := dst.width - src.width

/-- Grow an extendable register just enough to reach target width `W`. -/
def growExtRegTo (e : ExtReg) (W : ℕ) : ExtReg := e.grow (W - e.width)

/-- Initial signed compiler layout obtained by taking the split children as slots. -/
def initSignedLayoutState {x z : ExtReg} {k : ℕ} (layout : Gate.PhaseProductLayout x z k) : LayoutState k :=
  { xslot := fun i => layout.xSplit.child i, zslot := fun i => layout.zSplit.child i }

/-- Final widened chunk views for the compiled signed body.
Each final slot is obtained by widening the corresponding abstract initial
split chunk. No concrete register splitting is used here.
-/
def targetSignedLayoutState {k : ℕ} (src : LayoutState k) (need : NeededWidths k) : LayoutState k :=
  let Wwork := commonNeededWidth need
  { xslot := fun i => growExtRegTo (src.xslot i) Wwork, zslot := fun i => growExtRegTo (src.zslot i) Wwork }

/-- Child reserve sizes for a parent reserve split into `k` consecutive slices. -/
structure ReserveBudget (parent : ExtReg) (k : ℕ) where
  size : Fin k → ℕ

/-- Starting reserve offset for child `i`. -/
def ReserveBudget.offset {parent : ExtReg} {k : ℕ} (budget : ReserveBudget parent k) (i : Fin k) : ℕ :=
  ((List.ofFn budget.size).take i.1).sum

/-- Concrete reserve slice assigned to child `i`. -/
def ReserveBudget.childReserve {parent : ExtReg} {k : ℕ} (budget : ReserveBudget parent k) (i : Fin k) : Reg :=
  (parent.reserve.drop (budget.offset i)).take (budget.size i)

/-! ---------------------------------------------------------
    Phase-Product Compiler: Widths
--------------------------------------------------------- -/

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

/-- Scanning only raises each slot's need. -/
lemma scanNeededWidthsAux_ge {k : ℕ} (i : Fin k) :
    ∀ (ops : List (valid_ops k)) (cur : WidthState k) (mx : NeededWidths k),
      mx.xneed i ≤ (scanNeededWidthsAux cur mx ops).xneed i ∧
        mx.zneed i ≤ (scanNeededWidthsAux cur mx ops).zneed i
  | [], _, _ => ⟨le_rfl, le_rfl⟩
  | op :: rest, cur, mx =>
      have h := scanNeededWidthsAux_ge i rest (updateWidthState cur op)
        (mergeNeededWidths mx (widthsOfState (updateWidthState cur op)))
      ⟨le_trans (le_max_left _ _) h.1, le_trans (le_max_left _ _) h.2⟩

/-- The scan's needs dominate the initial chunk widths. -/
lemma scanNeededWidths_ge_init {k : ℕ} (x z : ExtReg) (ops : List (valid_ops k)) (i : Fin k) :
    (initWidthState x z k).xw i ≤ (scanNeededWidths x z ops).xneed i ∧
      (initWidthState x z k).zw i ≤ (scanNeededWidths x z ops).zneed i :=
  scanNeededWidthsAux_ge i ops (initWidthState x z k) (widthsOfState (initWidthState x z k))

/-- The common target width exceeds every scanned need. -/
lemma commonNeededWidth_gt {k : ℕ} (need : NeededWidths k) (i : Fin k) :
    need.xneed i < commonNeededWidth need ∧ need.zneed i < commonNeededWidth need := by
  have h : max (need.xneed i) (need.zneed i) ≤
      Finset.univ.sup (fun j : Fin k => max (need.xneed j) (need.zneed j)) :=
    Finset.le_sup (f := fun j : Fin k => max (need.xneed j) (need.zneed j)) (Finset.mem_univ i)
  have := le_max_left (need.xneed i) (need.zneed i)
  have := le_max_right (need.xneed i) (need.zneed i)
  unfold commonNeededWidth
  omega

/-- A child of the target layout is never wider than the next recursive width.
This is what makes the planner's recursion terminate. -/
theorem phaseInputSize_target_le {x z : ExtReg} {k : ℕ} (layout : Gate.PhaseProductLayout x z k)
    (ops : Prog k) (i : Fin k) :
    phaseInputSize
        ((targetSignedLayoutState (initSignedLayoutState layout) (scanNeededWidths x z ops)).xslot i)
        ((targetSignedLayoutState (initSignedLayoutState layout) (scanNeededWidths x z ops)).zslot i)
      ≤ nextSignedWidth x z ops := by
  have grow_le : ∀ (e : ExtReg) (W : ℕ), e.width ≤ W → (growExtRegTo e W).width ≤ W := by
    intro e W h
    have : (e.grow (W - e.width)).width ≤ e.width + (W - e.width) := by
      simp [ExtReg.grow, ExtReg.width, ExtReg.newBits, Reg.append, Reg.take, regSize, Reg.width]
    unfold growExtRegTo
    omega
  have chunk_le : ∀ (e : ExtReg) (j : Fin k), regSize (phaseChunkActive e k (phaseLimbWidth x z k) j)
      ≤ phaseSplitLogicalWidth e.width (phaseLimbWidth x z k) k j := by
    intro e j
    simp [phaseChunkActive, regSize, Reg.width, Reg.take]
  obtain ⟨hx, hz⟩ := scanNeededWidths_ge_init x z ops i
  obtain ⟨hcx, hcz⟩ := commonNeededWidth_gt (scanNeededWidths x z ops) i
  have h1 := chunk_le x i
  have h2 := chunk_le z i
  simp only [initWidthState, ExtReg.width] at hx hz h1 h2
  refine max_le (grow_le _ _ ?_) (grow_le _ _ ?_)
  · show regSize (phaseChunkActive x k (phaseLimbWidth x z k) i) ≤ commonNeededWidth (scanNeededWidths x z ops)
    omega
  · show regSize (phaseChunkActive z k (phaseLimbWidth x z k) i) ≤ commonNeededWidth (scanNeededWidths x z ops)
    omega


/-! ---------------------------------------------------------
    Phase-Product Compiler: the exact working width
--------------------------------------------------------- -/

/-! The scan above grows a slot by one bit at every `addScaled` and `negate`,
whether or not the value grows. The **exact** width is computed from the values
the table actually reaches: every row of every state the program visits
(`exactReachRows`), read on the limb box of each operand (lower chunks
unsigned, the top chunk signed), gives a demand, and the tight width is
`1 + ⌈log₂ D⌉` for the largest demand `D`. `exactSignedWidthOfWidths` is the
larger of that and the floor `commonNeededWidth` of the initial widths, so every
slot still grows by at least one bit. The facts about it are in
`Proofs/Compiler/ExactWidth.lean` and `Proofs/Compiler/ExactWidthBound.lean`. -/


/-! ## Tabulation (an evaluation device, extensionally the identity) -/

/-- `σ`, with every entry computed once into arrays. -/
def exactTab {k : ℕ} (σ : State k) : State k :=
  let a : Array (Array ℤ) := Array.ofFn fun i => Array.ofFn (σ i)
  fun i j => (a.getD i.1 #[]).getD j.1 0

theorem exactTab_eq {k : ℕ} (σ : State k) : exactTab σ = σ := by
  funext i j
  simp [exactTab, Array.getD_eq_getD_getElem?]

/-! ## The states and rows a program visits -/

/-- The states a run visits: the state before each operation and the final one.
Stops at an inexact right shift (where `run?` fails); a table satisfying C4 has
none. -/
def exactReachStates {k : ℕ} : State k → Prog k → List (State k)
  | σ, [] => [σ]
  | σ, op :: ops =>
      σ :: (match applyOp? σ op with
        | none => []
        | some σ' => exactReachStates (exactTab σ') ops)

/-- Every row any register holds in any visited state. -/
def exactReachRows {k : ℕ} (ops : Prog k) : List (Register k) :=
  (exactReachStates State.start_state ops).flatMap fun σ => (List.finRange k).map σ

/-! ## Fast evaluation (`@[csimp]`: proved equal, used by compiled code)

`exactReachStates` re-tabulates with `exactTab`, whose array the code
generator may recompute inside the returned closure; and `exactRowLo/Hi`
recompute the box bounds (`2^t`) for every row. The definitions above are the
specification; the versions below carry the state as an `Array` value (never a
closure) and take the bounds as arrays computed once per call. The `@[csimp]`
theorems make every compiled caller use them; they are equalities, so nothing
the kernel checks changes. -/

/-- A state as arrays. -/
def stArr {k : ℕ} (σ : State k) : Array (Array ℤ) := Array.ofFn fun i => Array.ofFn (σ i)

/-- Arrays read back as a state. -/
def arrState {k : ℕ} (a : Array (Array ℤ)) : State k := fun i j => (a.getD i.1 #[]).getD j.1 0

theorem arrState_stArr {k : ℕ} (σ : State k) : arrState (stArr σ) = σ := by
  funext i j
  simp [arrState, stArr, Array.getD_eq_getD_getElem?]

/-- `exactReachStates`, carrying array states. -/
def exactReachArr {k : ℕ} : Array (Array ℤ) → Prog k → List (Array (Array ℤ))
  | a, [] => [a]
  | a, op :: ops =>
      a :: (match applyOp? (arrState a) op with
        | none => []
        | some σ' => exactReachArr (stArr σ') ops)

theorem exactReachArr_eq {k : ℕ} :
    ∀ (ops : Prog k) (σ : State k),
      (exactReachArr (stArr σ) ops).map arrState = exactReachStates σ ops
  | [], σ => by simp [exactReachArr, exactReachStates, arrState_stArr]
  | op :: ops, σ => by
      simp only [exactReachArr, exactReachStates, List.map_cons, arrState_stArr]
      congr 1
      cases applyOp? σ op with
      | none => rfl
      | some σ' => simp only [exactTab_eq]; exact exactReachArr_eq ops σ'

/-- `exactReachRows`, through array states. -/
def exactReachRowsFast {k : ℕ} (ops : Prog k) : List (Register k) :=
  (exactReachArr (stArr (State.start_state (k := k))) ops).flatMap fun a => (List.finRange k).map (arrState a)

@[csimp] theorem exactReachRows_eq_fast : @exactReachRows = @exactReachRowsFast := by
  funext k ops
  unfold exactReachRows exactReachRowsFast
  rw [← exactReachArr_eq ops State.start_state, List.flatMap_map]

/-! ## The limb box and row ranges -/

/-- Least value of chunk `j` of an operand of width `w` at lower-limb width `W`. -/
def exactLimbLo (w W : ℕ) {k : ℕ} (j : Fin k) : ℤ :=
  if isTopChunk j then
    (if phaseSplitLogicalWidth w W k j = 0 then 0
     else -(2 : ℤ) ^ (phaseSplitLogicalWidth w W k j - 1))
  else 0

/-- Greatest value of chunk `j`. -/
def exactLimbHi (w W : ℕ) {k : ℕ} (j : Fin k) : ℤ :=
  if isTopChunk j then
    (if phaseSplitLogicalWidth w W k j = 0 then 0
     else (2 : ℤ) ^ (phaseSplitLogicalWidth w W k j - 1) - 1)
  else (2 : ℤ) ^ (phaseSplitLogicalWidth w W k j) - 1

/-- Least value of the row over the box (a list sum, so it evaluates). -/
def exactRowLo (w W : ℕ) {k : ℕ} (r : Register k) : ℤ :=
  ((List.finRange k).map fun j => min (r j * exactLimbLo w W j) (r j * exactLimbHi w W j)).sum

/-- Greatest value of the row over the box. -/
def exactRowHi (w W : ℕ) {k : ℕ} (r : Register k) : ℤ :=
  ((List.finRange k).map fun j => max (r j * exactLimbLo w W j) (r j * exactLimbHi w W j)).sum

/-- The magnitude the row demands: a signed `E`-bit register holds every value
of the row over the box iff `exactRowDemand ≤ 2^(E-1)` (`0 < E`). -/
def exactRowDemand (w W : ℕ) {k : ℕ} (r : Register k) : ℕ :=
  max (-exactRowLo w W r).toNat (exactRowHi w W r + 1).toNat

/-! ## Maxima and the least exponent -/

/-- The largest entry of a list of naturals (`0` for the empty list). -/
def exactListMax : List ℕ → ℕ
  | [] => 0
  | a :: as => max a (exactListMax as)

/-- Least `e ≥ e₀` with `D ≤ 2^e`, searching at most `f` steps. -/
def exactLeastExp (D : ℕ) : ℕ → ℕ → ℕ
  | 0, e => e
  | f + 1, e => if D ≤ 2 ^ e then e else exactLeastExp D f (e + 1)

/-! ## The widths -/

/-- The lower-limb width the compiler splits two operands of widths `xw`, `zw`
at (`phaseLimbWidth`, from widths alone). -/
def exactLimbWidth (k xw zw : ℕ) : ℕ := min (xw / k) (zw / k)

/-- The largest demand over the reachable rows, on both operands' boxes. -/
def exactDemand {k : ℕ} (ops : Prog k) (xw zw : ℕ) : ℕ :=
  exactListMax ((exactReachRows ops).map fun r =>
    max (exactRowDemand xw (exactLimbWidth k xw zw) r) (exactRowDemand zw (exactLimbWidth k xw zw) r))

/-- Row demand with the box bounds passed as arrays. -/
def rowDemandArr {k : ℕ} (lo hi : Array ℤ) (r : Register k) : ℕ :=
  max (-((List.finRange k).map fun j => min (r j * lo.getD j.1 0) (r j * hi.getD j.1 0)).sum).toNat
    (((List.finRange k).map fun j => max (r j * lo.getD j.1 0) (r j * hi.getD j.1 0)).sum + 1).toNat

/-- The demand, bounds computed once. -/
def exactDemandWith {k : ℕ} (rows : List (Register k)) (xlo xhi zlo zhi : Array ℤ) : ℕ :=
  exactListMax (rows.map fun r => max (rowDemandArr xlo xhi r) (rowDemandArr zlo zhi r))

def exactDemandFast {k : ℕ} (ops : Prog k) (xw zw : ℕ) : ℕ :=
  exactDemandWith (exactReachRows ops)
    (Array.ofFn (exactLimbLo xw (exactLimbWidth k xw zw) (k := k)))
    (Array.ofFn (exactLimbHi xw (exactLimbWidth k xw zw) (k := k)))
    (Array.ofFn (exactLimbLo zw (exactLimbWidth k xw zw) (k := k)))
    (Array.ofFn (exactLimbHi zw (exactLimbWidth k xw zw) (k := k)))

theorem rowDemandArr_ofFn {k : ℕ} (w W : ℕ) (r : Register k) :
    rowDemandArr (Array.ofFn (exactLimbLo w W (k := k))) (Array.ofFn (exactLimbHi w W (k := k))) r
      = exactRowDemand w W r := by
  simp [rowDemandArr, exactRowDemand, exactRowLo, exactRowHi, Array.getD_eq_getD_getElem?]

@[csimp] theorem exactDemand_eq_fast : @exactDemand = @exactDemandFast := by
  funext k ops xw zw
  simp only [exactDemand, exactDemandFast, exactDemandWith, rowDemandArr_ofFn]

/-- **The tight width**: `1 + ⌈log₂ D⌉`, the least `E ≥ 1` with `D ≤ 2^(E-1)`. -/
def tightSignedWidthOfWidths {k : ℕ} (ops : Prog k) (xw zw : ℕ) : ℕ :=
  1 + exactLeastExp (exactDemand ops xw zw) (exactDemand ops xw zw) 0

/-- The initial chunk widths, as the compiler's initial width state records them. -/
def exactInitNeed (k xw zw : ℕ) : NeededWidths k where
  xneed := fun i => phaseSplitLogicalWidth xw (exactLimbWidth k xw zw) k i
  zneed := fun i => phaseSplitLogicalWidth zw (exactLimbWidth k xw zw) k i

/-- **The floor**: one bit above the widest initial chunk, the least width
that grows every slot (ForShor's allocation sign- or zero-extends each slot by at
least one bit). -/
def floorSignedWidthOfWidths (k xw zw : ℕ) : ℕ := commonNeededWidth (exactInitNeed k xw zw)

/-- **The exact working width** the compiler uses: the tight width, or the
floor if that is larger. -/
def exactSignedWidthOfWidths {k : ℕ} (ops : Prog k) (xw zw : ℕ) : ℕ :=
  max (tightSignedWidthOfWidths ops xw zw) (floorSignedWidthOfWidths k xw zw)

/-- The exact width as a uniform `NeededWidths` record: every slot is asked
for `E - 1`, so `commonNeededWidth` of it is `E` (`commonNeededWidth_exactNeeded`). -/
def exactNeededWidths {k : ℕ} (ops : Prog k) (xw zw : ℕ) : NeededWidths k where
  xneed := fun _ => exactSignedWidthOfWidths ops xw zw - 1
  zneed := fun _ => exactSignedWidthOfWidths ops xw zw - 1

theorem floor_le_exactSignedWidth {k : ℕ} (ops : Prog k) (xw zw : ℕ) :
    floorSignedWidthOfWidths k xw zw ≤ exactSignedWidthOfWidths ops xw zw := le_max_right _ _

/-- Every initial chunk is at most `E - 1`, so every slot grows by at least one bit. -/
theorem exactInit_le {k : ℕ} (ops : Prog k) (xw zw : ℕ) (i : Fin k) :
    (exactInitNeed k xw zw).xneed i ≤ exactSignedWidthOfWidths ops xw zw - 1 ∧
    (exactInitNeed k xw zw).zneed i ≤ exactSignedWidthOfWidths ops xw zw - 1 := by
  have hsup : max ((exactInitNeed k xw zw).xneed i) ((exactInitNeed k xw zw).zneed i)
      ≤ Finset.univ.sup (fun j : Fin k =>
          max ((exactInitNeed k xw zw).xneed j) ((exactInitNeed k xw zw).zneed j)) :=
    Finset.le_sup (f := fun j : Fin k =>
      max ((exactInitNeed k xw zw).xneed j) ((exactInitNeed k xw zw).zneed j)) (Finset.mem_univ i)
  have hfl := floor_le_exactSignedWidth ops xw zw
  unfold floorSignedWidthOfWidths commonNeededWidth at hfl
  constructor <;> omega

/-! =========================================================
    Width rules: the scan, or the exact width
    A policy carries a `WidthRule` (`Framework/Policy.lean`). `.scan` is
    `scanNeededWidths` / `nextSignedWidth`, unchanged; `.exact` is the exact
    width above.
========================================================= -/

/-- The width needs the compiler grows every slot to, under rule `R`: the
scan (`scanNeededWidths`), or the exact width as a uniform record
(`exactNeededWidths`). -/
def neededWidthsBy (R : WidthRule) {k : ℕ} (x z : ExtReg) (ops : List (valid_ops k)) :
    NeededWidths k :=
  match R with
  | .scan => scanNeededWidths x z ops
  | .exact => exactNeededWidths ops x.width z.width

/-! Evaluation-only memo for the exact rule, declared before anything that calls
`neededWidthsBy` so that every compiled caller goes through the `@[csimp]`
below. `exactWidthMemo` is *defined* as the exact width (every proof sees
`exactSignedWidthOfWidths`) and *implemented* by a cache keyed on `k`, the
program object's address and the two widths; the cache holds the program, so
an address is not reused while its entry exists. Trusted code for compiled
evaluation only, never for a kernel proof. The `.scan` branch is untouched. -/

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

/-- The initial widths are included in the width needs, under either rule. -/
lemma neededWidthsBy_ge_init (R : WidthRule)
    {k : ℕ} (x z : ExtReg) (ops : List (valid_ops k)) (i : Fin k) :
    (initWidthState x z k).xw i ≤ (neededWidthsBy R x z ops).xneed i ∧
      (initWidthState x z k).zw i ≤ (neededWidthsBy R x z ops).zneed i := by
  cases R
  · exact scanNeededWidths_ge_init x z ops i
  · exact exactInit_le ops x.width z.width i

/-- `phaseInputSize_target_le` under either rule: this is what makes the
planner's recursion terminate when the policy uses the exact width. -/
theorem phaseInputSize_target_le_by (R : WidthRule) {x z : ExtReg} {k : ℕ}
    (layout : Gate.PhaseProductLayout x z k) (ops : Prog k) (i : Fin k) :
    phaseInputSize
        ((targetSignedLayoutState (initSignedLayoutState layout) (neededWidthsBy R x z ops)).xslot i)
        ((targetSignedLayoutState (initSignedLayoutState layout) (neededWidthsBy R x z ops)).zslot i)
      ≤ nextSignedWidthBy R x z ops := by
  have grow_le : ∀ (e : ExtReg) (W : ℕ), e.width ≤ W → (growExtRegTo e W).width ≤ W := by
    intro e W h
    have : (e.grow (W - e.width)).width ≤ e.width + (W - e.width) := by
      simp [ExtReg.grow, ExtReg.width, ExtReg.newBits, Reg.append, Reg.take, regSize, Reg.width]
    unfold growExtRegTo
    omega
  have chunk_le : ∀ (e : ExtReg) (j : Fin k), regSize (phaseChunkActive e k (phaseLimbWidth x z k) j)
      ≤ phaseSplitLogicalWidth e.width (phaseLimbWidth x z k) k j := by
    intro e j
    simp [phaseChunkActive, regSize, Reg.width, Reg.take]
  obtain ⟨hx, hz⟩ := neededWidthsBy_ge_init R x z ops i
  obtain ⟨hcx, hcz⟩ := commonNeededWidth_gt (neededWidthsBy R x z ops) i
  have h1 := chunk_le x i
  have h2 := chunk_le z i
  simp only [initWidthState, ExtReg.width] at hx hz h1 h2
  refine max_le (grow_le _ _ ?_) (grow_le _ _ ?_)
  · show regSize (phaseChunkActive x k (phaseLimbWidth x z k) i)
      ≤ commonNeededWidth (neededWidthsBy R x z ops)
    omega
  · show regSize (phaseChunkActive z k (phaseLimbWidth x z k) i)
      ≤ commonNeededWidth (neededWidthsBy R x z ops)
    omega

/-! ---------------------------------------------------------
    Phase-Product Compiler: Coefficients
--------------------------------------------------------- -/

/-! =========================================================
    Interpolation weights
    `cramerCoeffFromPts` is Cramer's rule, which the proofs reason about but
    which sums over all `(2k-1)!` permutations when evaluated. The `@[csimp]`
    lemma below has compiled code compute the same weights by Gauss-Jordan
    elimination with a verified inverse. A `@[csimp]` lemma rewrites only code
    compiled after it, so it precedes every caller of `cramerCoeffFromPts`.
========================================================= -/

/-- Interpolation matrix built from the chosen point set. -/
def interpMatrix (k : ℕ) (pts : Fin (q k) → Point) : Matrix (Fin (q k)) (Fin (q k)) ℚ :=
  fun i j => interpEntry k (pts i) j

/-- Convert a point list of the right length into a `Fin`-indexed family. -/
def ptsToFin (k : ℕ) (pts : List Point) (hpts : pts.length = q k) : Fin (q k) → Point :=
  fun i => pts.get ⟨i.val, by have hi : i.val < q k := i.is_lt; simp [hpts]⟩

/-- The interpolation weights by Cramer's rule, which (unlike `Matrix.inv`) is computable. -/
def cramerCoeffFromPts (k : ℕ) (pts : Fin (q k) → Point) (b : ℚ) : Fin (q k) → ℚ :=
  let M : Matrix (Fin (q k)) (Fin (q k)) ℚ := interpMatrix k pts
  let radixVec : Fin (q k) → ℚ := fun j => b ^ (j : ℕ)
  fun i => Matrix.cramer M.transpose radixVec i / M.det

/-- For an invertible interpolation matrix, Cramer's rule is the inverse transpose applied to
the radix vector: from `Mᵀ *ᵥ cramer Mᵀ v = det Mᵀ • v` (`Matrix.mulVec_cramer`). -/
lemma cramerCoeffFromPts_eq_inv_mulVec {k : ℕ} (pts : Fin (q k) → Point) (b : ℚ)
    (hgood : (interpMatrix k pts).det ≠ 0) (i : Fin (q k)) :
    cramerCoeffFromPts k pts b i
      = ((interpMatrix k pts).transpose⁻¹ *ᵥ fun j : Fin (q k) => b ^ (j : ℕ)) i := by
  set M : Matrix (Fin (q k)) (Fin (q k)) ℚ := interpMatrix k pts with hM
  set radixVec : Fin (q k) → ℚ := fun j => b ^ (j : ℕ) with hradixVec
  have hUnitT : IsUnit M.transpose.det := by
    rw [Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr hgood
  have hkey :
      Matrix.cramer M.transpose radixVec = M.transpose.det • (M.transpose⁻¹ *ᵥ radixVec) := by
    calc Matrix.cramer M.transpose radixVec
        = M.transpose⁻¹ *ᵥ (M.transpose *ᵥ Matrix.cramer M.transpose radixVec) := by
          rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M.transpose hUnitT, Matrix.one_mulVec]
      _ = M.transpose⁻¹ *ᵥ (M.transpose.det • radixVec) := by rw [Matrix.mulVec_cramer]
      _ = M.transpose.det • (M.transpose⁻¹ *ᵥ radixVec) := Matrix.mulVec_smul _ _ _
  have hdet_ne : M.transpose.det ≠ 0 := by rw [Matrix.det_transpose]; exact hgood
  have hcomp : Matrix.cramer M.transpose radixVec i
      = M.transpose.det * (M.transpose⁻¹ *ᵥ radixVec) i := by
    simpa [Pi.smul_apply, smul_eq_mul] using congrFun hkey i
  rw [eq_comm, ← mul_div_cancel_left₀ ((M.transpose⁻¹ *ᵥ radixVec) i) hdet_ne, ← hcomp]
  simp [cramerCoeffFromPts, hM, hradixVec, Matrix.det_transpose]

/-! ### Gauss-Jordan elimination with a verified inverse -/

/-- Row-major dense form of an `n × n` `Matrix`, for the eliminator below. -/
def matrixToRows {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) : Array (Array ℚ) :=
  ((List.finRange n).map fun i => ((List.finRange n).map fun j => M i j).toArray).toArray

/-- Row-major dense rows read back as a `Matrix`; a missing entry is `0`. The
inverse of `matrixToRows` on well-formed input, and the bridge that lets the
verified check below be stated as a `Matrix` equation. -/
def rowsToMatrix {n : ℕ} (rows : Array (Array ℚ)) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => (rows.getD i.val #[]).getD j.val 0

/-- Exact Gauss-Jordan elimination over `ℚ`: given the `n` rows of `M`,
returns the `n` rows of `M⁻¹`, or `none` if no pivot is found. Unverified;
its output is only used after `isRightInverseRows` has re-multiplied it. -/
def gaussJordanInverseRows (n : ℕ) (rows : Array (Array ℚ)) : Option (Array (Array ℚ)) :=
  Id.run do
    let mut aug : Array (Array ℚ) :=
      (Array.range n).map fun i =>
        (rows.getD i #[]) ++ (Array.range n).map (fun j => if i = j then (1 : ℚ) else 0)
    for col in [0:n] do
      let mut pivot : Option ℕ := none
      for r in [col:n] do
        if pivot.isNone then
          if (aug.getD r #[]).getD col 0 ≠ 0 then
            pivot := some r
      match pivot with
      | none => return none
      | some p =>
          if p ≠ col then
            let rowCol := aug.getD col #[]
            let rowP := aug.getD p #[]
            aug := aug.set! col rowP
            aug := aug.set! p rowCol
          let pv := (aug.getD col #[]).getD col 0
          aug := aug.set! col ((aug.getD col #[]).map (· / pv))
          for r in [0:n] do
            if r ≠ col then
              let factor := (aug.getD r #[]).getD col 0
              if factor ≠ 0 then
                let rowR := aug.getD r #[]
                let rowColNow := aug.getD col #[]
                aug := aug.set! r
                  ((Array.range (2 * n)).map fun c => rowR.getD c 0 - factor * rowColNow.getD c 0)
    return some ((Array.range n).map fun i => (aug.getD i #[]).extract n (2 * n))

/-- `M · rowsToMatrix inv = I`, decided entrywise over `ℚ`. This is the
trusted computation. -/
def isRightInverseRows {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) (inv : Array (Array ℚ)) : Bool :=
  decide (∀ i j : Fin n,
    (∑ r : Fin n, M i r * rowsToMatrix (n := n) inv r j) = if i = j then (1 : ℚ) else 0)

/-- A `true` from `isRightInverseRows` is a right inverse, as a `Matrix`
equation. -/
theorem mul_rowsToMatrix_eq_one_of_isRightInverseRows
    {n : ℕ} {M : Matrix (Fin n) (Fin n) ℚ} {inv : Array (Array ℚ)}
    (h : isRightInverseRows M inv = true) :
    M * rowsToMatrix (n := n) inv = 1 := by
  have h' := of_decide_eq_true h
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  exact h' i j

/-! ### The weights by elimination, and the `@[csimp]` lemma -/

/--
`cramerCoeffFromPts` computed by Gauss-Jordan elimination. The interpolation
matrix is inverted by `gaussJordanInverseRows`, the result is verified by
re-multiplication (`isRightInverseRows`), and the weights are
`radixVec ᵥ* M⁻¹` read off the verified rows. If elimination fails or the
verification does not pass, the value is `cramerCoeffFromPts` itself, so the
function equals Cramer's rule with no assumption on the eliminator.

Declared before the `@[csimp]` lemma so that its fallback branches compile
to the genuine Cramer code.
-/
def gjCoeffFromPts (k : ℕ) (pts : Fin (q k) → Point) (b : ℚ) : Fin (q k) → ℚ :=
  let M : Matrix (Fin (q k)) (Fin (q k)) ℚ := interpMatrix k pts
  match gaussJordanInverseRows (q k) (matrixToRows M) with
  | some inv =>
      if isRightInverseRows M inv then
        fun i => ∑ j : Fin (q k), b ^ (j : ℕ) * rowsToMatrix (n := q k) inv j i
      else cramerCoeffFromPts k pts b
  | none => cramerCoeffFromPts k pts b

/-- `gjCoeffFromPts` equals Cramer's rule. In the verified branch `M * inv = 1` gives
`det M ≠ 0` and `M⁻¹ = inv`, and `cramerCoeffFromPts_eq_inv_mulVec` identifies the two;
the fallback branches are definitional. -/
theorem gjCoeffFromPts_eq_cramerCoeffFromPts (k : ℕ) (pts : Fin (q k) → Point) (b : ℚ) :
    gjCoeffFromPts k pts b = cramerCoeffFromPts k pts b := by
  unfold gjCoeffFromPts
  dsimp only
  rcases hgj : gaussJordanInverseRows (q k) (matrixToRows (interpMatrix k pts)) with _ | inv
  · rfl
  · dsimp only
    by_cases hchk : isRightInverseRows (interpMatrix k pts) inv = true
    · rw [ite_eq_left hchk]
      have hmul : interpMatrix k pts * rowsToMatrix (n := q k) inv = 1 :=
        mul_rowsToMatrix_eq_one_of_isRightInverseRows hchk
      have hdet : (interpMatrix k pts).det ≠ 0 :=
        (Matrix.isUnit_det_of_right_inverse hmul).ne_zero
      funext i
      rw [cramerCoeffFromPts_eq_inv_mulVec pts b hdet i, ← Matrix.transpose_nonsing_inv,
        Matrix.inv_eq_right_inv hmul]
      simp [Matrix.mulVec, dotProduct, mul_comm]
    · rw [ite_eq_right hchk]

/-- Compiled code evaluates `cramerCoeffFromPts` as `gjCoeffFromPts`; the
kernel, and every proof, sees Cramer's rule. -/
@[csimp] theorem cramerCoeffFromPts_eq_gjCoeffFromPts_csimp :
    @cramerCoeffFromPts = @gjCoeffFromPts := by
  funext k pts b
  exact (gjCoeffFromPts_eq_cramerCoeffFromPts k pts b).symm

/-- `cramerCoeffFromPts` at radix `2 ^ W`. -/
def cramerCoeffFromPtsWidth (k W : ℕ) (pts : List Point) (hpts : pts.length = q k) : Fin (q k) → ℚ :=
  cramerCoeffFromPts k (ptsToFin k pts hpts) ((2 : ℚ) ^ W)

/-! ---------------------------------------------------------
    Phase-Product Compiler: Compilation
--------------------------------------------------------- -/

/-! =========================================================
    Annotated operations and phase-product counting
========================================================= -/

/-- A source operation plus the interpolation term assigned to a phase-product leaf, if any. -/
structure AnnotatedOp (k : ℕ) where
  op : valid_ops k
  phaseTerm? : Option (Fin (q k))

/-- Attach interpolation-term indices to phase-product operations in source order. -/
def annotatePhaseTermsAux (k n : ℕ) (ops : List (valid_ops k)) : List (AnnotatedOp k) :=
  match ops with
  | [] => []
  | op :: rest =>
      match op with
      | .phaseProduct _i =>
          let ann : Option (Fin (q k)) := if h : n < q k then some ⟨n, h⟩ else none
          ⟨op, ann⟩ :: annotatePhaseTermsAux k (n+1) rest
      | _ =>
          ⟨op, none⟩ :: annotatePhaseTermsAux k n rest

/-- Allocation gate for a single chunk. Lower chunks are zero-extended;
    the top chunk is sign-extended. -/
def allocChunkGate {k : ℕ} (i : Fin k) (src dst : ExtReg) : Gate :=
  let n := extraDelta src dst
  if _h0 : n = 0 then
    Gate.id
  else if _htop : isTopChunk i then
    Gate.signExtend src n
  else
    Gate.zeroExtend src n

/-- Matching deallocation gate for a single chunk. -/
def deallocChunkGate {k : ℕ} (i : Fin k) (src dst : ExtReg) : Gate :=
  let n := extraDelta src dst
  if _h0 : n = 0 then
    Gate.id
  else if _htop : isTopChunk i then
    Gate.signDealloc src n
  else
    Gate.zeroDealloc src n

/-- Allocation program for the first `n` chunks, in increasing order `0,1,...,n-1`. -/
def compileSignedAllocationsAux {k : ℕ} (src dst : LayoutState k) :
    ∀ (n : ℕ), n ≤ k → Gate
  | 0, _ => Gate.id
  | n + 1, hn =>
      let hk' : n ≤ k := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn
      let i : Fin k := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
      compileSignedAllocationsAux src dst n hk' ;;
      allocChunkGate i (src.xslot i) (dst.xslot i) ;;
      allocChunkGate i (src.zslot i) (dst.zslot i)

/-- Emit all chunk allocations before the signed arithmetic body. -/
def compileSignedAllocations (k : ℕ) (src dst : LayoutState k) : Gate :=
  compileSignedAllocationsAux src dst k (le_rfl)

/-- Deallocation program for the first `n` chunks, in decreasing order `n-1,...,1,0`. -/
def compileSignedDeallocationsAux {k : ℕ} (src dst : LayoutState k) :
    ∀ (n : ℕ), n ≤ k → Gate
  | 0, _ => Gate.id
  | n + 1, hn =>
      let hk' : n ≤ k := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn
      let i : Fin k := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
      deallocChunkGate i (src.zslot i) (dst.zslot i) ;;
      deallocChunkGate i (src.xslot i) (dst.xslot i) ;;
      compileSignedDeallocationsAux src dst n hk'

/-- Emit all chunk deallocations after the signed arithmetic body. -/
def compileSignedDeallocations (k : ℕ) (src dst : LayoutState k) : Gate :=
  compileSignedDeallocationsAux src dst k (le_rfl)

/-! =========================================================
    Compilation from `valid_ops` to `Gate`
========================================================= -/

/-- Signed compiler for annotated ops.  The layout state already contains
    enough extra width in each slot, so compilation only emits gates and does
    not resize the state further. -/
def compileAnnotatedOpsToSignedGateAux (k : ℕ) (hk : 1 < k) (phi : Angle)
    (phaseCoeff : Fin (q k) → ℚ) (st : LayoutState k) (ops : List (AnnotatedOp k)) : Gate :=
  match ops with
  | [] => Gate.id
  | ⟨op, term?⟩ :: rest =>
      let tail := compileAnnotatedOpsToSignedGateAux k hk phi phaseCoeff st rest
      match op with
      | .shiftL i n =>
          Gate.ShiftL (st.xslot i) n ;;
          Gate.ShiftL (st.zslot i) n ;; tail
      | .shiftR i n =>
          Gate.ShiftR (st.xslot i) n ;;
          Gate.ShiftR (st.zslot i) n ;; tail
      | .negate i =>
          Gate.Negate (st.xslot i) ;;
          Gate.Negate (st.zslot i) ;; tail
      | .addScaled dst src negsrc sh =>
          Gate.AddScaled (st.xslot dst) (st.xslot src) negsrc sh ;;
          Gate.AddScaled (st.zslot dst) (st.zslot src) negsrc sh ;; tail
      | .phaseProduct i =>
          match term? with
          | some l =>
              Gate.SignedPhaseProd (phi * phaseCoeff l) (st.xslot i) (st.zslot i) ;; tail
          | none =>
              tail

/-- Full signed phase-product lowering: allocate widths, compile the annotated body, then deallocate. -/
def compileOpsToSignedGate
    (k : ℕ) (hk : 1 < k) (phi : Angle) (x z : ExtReg) (layout : Gate.PhaseProductLayout x z k)
    (phaseCoeff : Fin (q k) → ℚ) (ops : List (valid_ops k)) : Gate :=
  let annOps : List (AnnotatedOp k) := annotatePhaseTermsAux k 0 ops
  let need : NeededWidths k := scanNeededWidths x z ops
  let stInit : LayoutState k := initSignedLayoutState layout
  let stFinal : LayoutState k := targetSignedLayoutState stInit need
  let allocs : Gate := compileSignedAllocations k stInit stFinal
  let body : Gate := compileAnnotatedOpsToSignedGateAux k hk phi phaseCoeff stFinal annOps
  let deallocs : Gate := compileSignedDeallocations k stInit stFinal
  allocs ;; body ;; deallocs

/-- `compileOpsToSignedGate` under width rule `R`: the same compiler, with the
slots grown to `neededWidthsBy R x z ops`. At `.scan` it is
`compileOpsToSignedGate` (`compileOpsToSignedGateBy_scan`, `rfl`). -/
def compileOpsToSignedGateBy (R : WidthRule)
    (k : ℕ) (hk : 1 < k) (phi : Angle) (x z : ExtReg) (layout : Gate.PhaseProductLayout x z k)
    (phaseCoeff : Fin (q k) → ℚ) (ops : List (valid_ops k)) : Gate :=
  let annOps : List (AnnotatedOp k) := annotatePhaseTermsAux k 0 ops
  let need : NeededWidths k := neededWidthsBy R x z ops
  let stInit : LayoutState k := initSignedLayoutState layout
  let stFinal : LayoutState k := targetSignedLayoutState stInit need
  let allocs : Gate := compileSignedAllocations k stInit stFinal
  let body : Gate := compileAnnotatedOpsToSignedGateAux k hk phi phaseCoeff stFinal annOps
  let deallocs : Gate := compileSignedDeallocations k stInit stFinal
  allocs ;; body ;; deallocs

/-- Add a shared control to phase-product leaves while leaving structural and arithmetic gates unchanged. -/
def controlPhaseLeaves (ctrl : ℕ) : Gate → Gate
  | .id => .id
  | .seq U V => controlPhaseLeaves ctrl U ;; controlPhaseLeaves ctrl V
  | .SignedPhaseProd phi x z => .CSignedPhaseProd ctrl phi x z
  | .ShiftL r n => .ShiftL r n
  | .ShiftR r n => .ShiftR r n
  | .Negate r => .Negate r
  | .AddScaled dst src negSrc sh => .AddScaled dst src negSrc sh
  | .zeroExtend r n => .zeroExtend r n
  | .signExtend r n => .signExtend r n
  | .zeroDealloc r n => .zeroDealloc r n
  | .signDealloc r n => .signDealloc r n
  | U => U

/-- The controlled compiler under width rule `R`: the leaves of
`compileOpsToSignedGateBy` get the control. -/
def compileOpsToCSignedGateBy (R : WidthRule)
    (k : ℕ) (hk : 1 < k) (ctrl : ℕ) (phi : Angle) (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z k) (coeff : Fin (q k) → ℚ) (ops : Prog k) : Gate :=
  controlPhaseLeaves ctrl (compileOpsToSignedGateBy R k hk phi x z layout coeff ops)

/-! =========================================================
    Control wrappers for allocation and deallocation
    Allocation and deallocation contain no phase product, so
    `controlPhaseLeaves` fixes them. `Policy.cStepPlan` casts along these two
    equations.
========================================================= -/

/-- Control-phase wrapping leaves allocation unchanged. -/
lemma controlPhaseLeaves_compileSignedAllocations {k : ℕ} (ctrl : ℕ) (src dst : LayoutState k) :
    controlPhaseLeaves ctrl (compileSignedAllocations k src dst) =
      compileSignedAllocations k src dst := by
  have chunk : ∀ (i : Fin k) (s d : ExtReg),
      controlPhaseLeaves ctrl (allocChunkGate i s d) = allocChunkGate i s d := by
    intro i s d
    unfold allocChunkGate
    by_cases h0 : extraDelta s d = 0 <;> by_cases htop : isTopChunk i <;>
      simp [h0, htop, controlPhaseLeaves]
  suffices h : ∀ n hn, controlPhaseLeaves ctrl (compileSignedAllocationsAux src dst n hn) =
      compileSignedAllocationsAux src dst n hn from h k le_rfl
  intro n hn
  induction n with
  | zero => rfl
  | succ n ih => simp only [compileSignedAllocationsAux, controlPhaseLeaves, ih, chunk]

/-- Control-phase wrapping leaves deallocation unchanged. -/
lemma controlPhaseLeaves_compileSignedDeallocations {k : ℕ} (ctrl : ℕ) (src dst : LayoutState k) :
    controlPhaseLeaves ctrl (compileSignedDeallocations k src dst) =
      compileSignedDeallocations k src dst := by
  have chunk : ∀ (i : Fin k) (s d : ExtReg),
      controlPhaseLeaves ctrl (deallocChunkGate i s d) = deallocChunkGate i s d := by
    intro i s d
    unfold deallocChunkGate
    by_cases h0 : extraDelta s d = 0 <;> by_cases htop : isTopChunk i <;>
      simp [h0, htop, controlPhaseLeaves]
  suffices h : ∀ n hn, controlPhaseLeaves ctrl (compileSignedDeallocationsAux src dst n hn) =
      compileSignedDeallocationsAux src dst n hn from h k le_rfl
  intro n hn
  induction n with
  | zero => rfl
  | succ n ih => simp only [compileSignedDeallocationsAux, controlPhaseLeaves, ih, chunk]

/-! ---------------------------------------------------------
    Workspace preservation and reserve-budget construction
--------------------------------------------------------- -/

/-- The split layout whose child reserves are the budget's consecutive slices. -/
def PhaseSplitLayout.ofBudget (parent : ExtReg) (k W : ℕ) (budget : ReserveBudget parent k) :
    PhaseSplitLayout parent k W where
  reserve := budget.childReserve
  active_reserve_disjoint i := by
    -- the chunk lies in the parent's active register and the slice in its reserve
    have ha : (phaseChunkActive parent k W i).qubits.Sublist parent.active.qubits :=
      (List.take_sublist _ _).trans (List.drop_sublist _ _)
    have hr : (budget.childReserve i).qubits.Sublist parent.reserve.qubits :=
      (List.take_sublist _ _).trans (List.drop_sublist _ _)
    have hparent : parent.active.qubits.Disjoint parent.reserve.qubits := by
      simpa [Disjoint] using parent.active_reserve_disjoint
    simpa [Disjoint] using
      List.disjoint_of_subset_left ha.subset (List.disjoint_of_subset_right hr.subset hparent)

/-! =========================================================
    Recursive workspace size model
    The recursive compiler needs reserve space for current-level chunk growth and
    for each descendant phase-product call. These width-only definitions compute
    conservative reserve requirements from logical operand widths.
========================================================= -/

namespace RecursivePhaseWorkspace

/-- The phase-limb width determined by a pair of logical operand widths. -/
def limbWidth (k wx wz : ℕ) : ℕ := phaseLimbWidth (ExtReg.ofReg (Reg.interval 0 wx)) (ExtReg.ofReg (Reg.interval wx wz)) k

/-- The common width required after compiling one level of the operation program. -/
def nextWidth {k : ℕ} (ops : Prog k) (wx wz : ℕ) : ℕ := nextSignedWidth (ExtReg.ofReg (Reg.interval 0 wx)) (ExtReg.ofReg (Reg.interval wx wz)) ops

/-- The operand side (`x` or `z`) a reserve formula is about. -/
inductive PhaseSide where
  | x
  | z

namespace PhaseSide

/-- Select the logical width for one operand side. -/
def width (side : PhaseSide) (wx wz : ℕ) : ℕ :=
  match side with
  | .x => wx
  | .z => wz

/-- Select the corresponding component from an `(x, z)` reserve pair. -/
def reserveComponent (side : PhaseSide) (need : ℕ × ℕ) : ℕ :=
  match side with
  | .x => need.1
  | .z => need.2

end PhaseSide

/-- The reserve needed to grow one side's chunks at this level (not the descendants). -/
def immediateNeed {k : ℕ} (side : PhaseSide) (ops : Prog k) (wx wz : ℕ) : ℕ :=
  let Wphase := limbWidth k wx wz
  let Wnext := nextWidth ops wx wz
  ∑ i : Fin k,
    (Wnext - phaseSplitLogicalWidth (side.width wx wz) Wphase k i)

/-- The reserve needed merely to grow all `x` chunks at this level. -/
abbrev immediateXNeed {k : ℕ} (ops : Prog k) (wx wz : ℕ) : ℕ :=
  immediateNeed PhaseSide.x ops wx wz

/-- The reserve needed merely to grow all `z` chunks at this level. -/
abbrev immediateZNeed {k : ℕ} (ops : Prog k) (wx wz : ℕ) : ℕ :=
  immediateNeed PhaseSide.z ops wx wz

/-- `nextWidth` under rule `R`. -/
def nextWidthBy (R : WidthRule) {k : ℕ} (ops : Prog k) (wx wz : ℕ) : ℕ :=
  nextSignedWidthBy R (ExtReg.ofReg (Reg.interval 0 wx)) (ExtReg.ofReg (Reg.interval wx wz)) ops

@[simp] theorem nextWidthBy_scan {k : ℕ} (ops : Prog k) (wx wz : ℕ) :
    nextWidthBy .scan ops wx wz = nextWidth ops wx wz := rfl

/-- `immediateNeed` under rule `R`. -/
def immediateNeedBy (R : WidthRule) {k : ℕ} (side : PhaseSide) (ops : Prog k) (wx wz : ℕ) : ℕ :=
  let Wphase := limbWidth k wx wz
  let Wnext := nextWidthBy R ops wx wz
  ∑ i : Fin k,
    (Wnext - phaseSplitLogicalWidth (side.width wx wz) Wphase k i)

@[simp] theorem immediateNeedBy_scan {k : ℕ} (side : PhaseSide) (ops : Prog k) (wx wz : ℕ) :
    immediateNeedBy .scan side ops wx wz = immediateNeed side ops wx wz := rfl

/-- `immediateXNeed` under rule `R`. -/
abbrev immediateXNeedBy (R : WidthRule) {k : ℕ} (ops : Prog k) (wx wz : ℕ) : ℕ :=
  immediateNeedBy R PhaseSide.x ops wx wz

/-- `immediateZNeed` under rule `R`. -/
abbrev immediateZNeedBy (R : WidthRule) {k : ℕ} (ops : Prog k) (wx wz : ℕ) : ℕ :=
  immediateNeedBy R PhaseSide.z ops wx wz

/-- Reserve `(x side, z side)` for the whole recursion: each of the `k` chunks gets its growth
plus a full child's reserve; nothing once the width stops shrinking. -/
def reserveNeed {k : ℕ} (ops : Prog k) (wx wz : ℕ) : ℕ × ℕ :=
  let Wnext := nextWidth ops wx wz
  if _hrec : Wnext < max wx wz then
    let childNeed :=
      reserveNeed ops Wnext Wnext
    (
      immediateXNeed ops wx wz + k * childNeed.1,
      immediateZNeed ops wx wz + k * childNeed.2
    )
  else
    (0, 0)
termination_by max wx wz
decreasing_by
  simpa using _hrec

end RecursivePhaseWorkspace

/-! =========================================================
    Static workspace-sufficiency predicates
========================================================= -/

/-- The operands are disjoint and their reserves fit the whole recursion. -/
structure SignedRecursiveWorkspaceOK {k : ℕ} (ops : Prog k) (x z : ExtReg) : Prop where
  /-- The complete owned regions of `x` and `z` do not overlap. -/
  owned_disjoint : ExtReg.OwnedDisjoint x z
  /-- `x.reserve` is large enough for the complete recursive compilation. -/
  x_reserve_sufficient : (RecursivePhaseWorkspace.reserveNeed ops x.width z.width).1 ≤ x.capacity
  /-- `z.reserve` is large enough for the complete recursive compilation. -/
  z_reserve_sufficient : (RecursivePhaseWorkspace.reserveNeed ops x.width z.width).2 ≤ z.capacity

/-! =========================================================
    Canonical recursive step construction
    The canonical step builds a phase-product layout whose child chunks have
    exactly the next recursive width and enough reserve for all descendant calls.
========================================================= -/

namespace ReserveBudget

/-- Last child index, used as the deterministic recipient for reserve slack. -/
def topIndex {k : ℕ} (hk : 0 < k) : Fin k := ⟨k - 1, by omega⟩

/-- Add all unused parent reserve to the top child while keeping other child requirements fixed. -/
def fillSlack {k : ℕ} (hk : 0 < k) (capacity : ℕ) (required : Fin k → ℕ) : Fin k → ℕ :=
  let top := topIndex hk
  let used := (List.ofFn required).sum
  Function.update
    required
    top
    (required top + (capacity - used))

/-- The reserve budget giving each child its requirement and the top child all
remaining slack. -/
def ofRequirements {parent : ExtReg} {k : ℕ} (hk : 0 < k) (required : Fin k → ℕ) :
    ReserveBudget parent k where
  size := fillSlack hk parent.capacity required

end ReserveBudget

/-- As `SignedRecursiveWorkspaceOK`, with the control outside both operands. -/
structure CSignedRecursiveWorkspaceOK {k : ℕ} (ops : Prog k) (ctrl : ℕ) (x z : ExtReg) :
    Prop extends SignedRecursiveWorkspaceOK ops x z where
  control_disjoint : ExtReg.CtrlDisjoint ctrl x z

/-! ---------------------------------------------------------
    The workspace model under a policy
--------------------------------------------------------- -/

namespace Policy

open ShorLoweringPolicy
open RecursivePhaseWorkspace
  (limbWidth nextWidth PhaseSide
   immediateNeed immediateXNeed immediateZNeed
   nextWidthBy immediateNeedBy immediateXNeedBy immediateZNeedBy)

/-! =========================================================
    The reserve recurrence
========================================================= -/

/-- `RecursivePhaseWorkspace.reserveNeed` with the table chosen by the policy at each level;
it stops where the policy has no table or the width stops shrinking. -/
def reserveNeed (P : ShorLoweringPolicy) (wx wz : ℕ) : ℕ × ℕ :=
  match P.choose (max wx wz) with
  | none => (0, 0)
  | some T =>
    let Wnext := nextWidthBy P.widthRule T.ops wx wz
    if _hrec : Wnext < max wx wz then
      let childNeed := reserveNeed P Wnext Wnext
      (immediateXNeedBy P.widthRule T.ops wx wz + T.k * childNeed.1,
       immediateZNeedBy P.widthRule T.ops wx wz + T.k * childNeed.2)
    else
      (0, 0)
termination_by max wx wz
decreasing_by simpa using _hrec

/-! Evaluation-only memo of `reserveNeed`, exact rule only. The compiled
circuit generator asks for the same `(P, wx, wz)` once per child slot of every
node; on the exact rule each answer recomputes exact widths down the whole
recursion. `reserveNeedFast` is `reserveNeed` on the scan rule (the same
compiled code as before) and, on the exact rule, a cache keyed on the policy
object's address (the cache holds the object) and the widths
(`reserveNeedMemo`, `@[implemented_by]`). `@[csimp]` routes compiled callers
through it. Trusted for compiled evaluation only, never for a kernel proof. -/

initialize reserveNeedCache : IO.Ref (Std.HashMap (USize × ℕ × ℕ) (NonScalar × (ℕ × ℕ))) ← IO.mkRef {}

private unsafe def reserveNeedMemoImpl (P : ShorLoweringPolicy) (wx wz : ℕ) : ℕ × ℕ :=
  unsafeBaseIO do
    let key := (ptrAddrUnsafe P, wx, wz)
    match (← reserveNeedCache.get)[key]? with
    | some (_, v) => return v
    | none =>
      let v := reserveNeed P wx wz
      reserveNeedCache.modify (·.insert key (unsafeCast P, v))
      return v

/-- `reserveNeed`, memoised in compiled code (see above). -/
@[implemented_by reserveNeedMemoImpl]
def reserveNeedMemo (P : ShorLoweringPolicy) (wx wz : ℕ) : ℕ × ℕ := reserveNeed P wx wz

/-- `reserveNeed` on the scan rule, the memo on the exact rule. -/
def reserveNeedFast (P : ShorLoweringPolicy) (wx wz : ℕ) : ℕ × ℕ :=
  match P.widthRule with
  | .scan => reserveNeed P wx wz
  | .exact => reserveNeedMemo P wx wz

@[csimp] theorem reserveNeed_eq_fast : @reserveNeed = @reserveNeedFast := by
  funext P wx wz
  unfold reserveNeedFast reserveNeedMemo
  cases P.widthRule <;> rfl

/-- The constant policy's reserve is the fixed-table reserve: the lookup
succeeds at every width with the same table, so the two recurrences take the
same branch at every level. -/
theorem reserveNeed_const (T : ToomCookTable) (wx wz : ℕ) :
    reserveNeed (constPolicy T) wx wz = RecursivePhaseWorkspace.reserveNeed T.ops wx wz := by
  -- Fuel induction on `max wx wz`, which is the measure both recurrences use.
  suffices h : ∀ n wx wz, max wx wz ≤ n →
      reserveNeed (constPolicy T) wx wz = RecursivePhaseWorkspace.reserveNeed T.ops wx wz from
    h (max wx wz) wx wz le_rfl
  intro n
  induction n with
  | zero =>
    intro wx wz hn
    rw [reserveNeed, constPolicy_choose, RecursivePhaseWorkspace.reserveNeed]
    simp only [constPolicy_widthRule, RecursivePhaseWorkspace.nextWidthBy_scan, RecursivePhaseWorkspace.immediateNeedBy_scan]
    have : ¬ nextWidth T.ops wx wz < max wx wz := by omega
    simp [this]
  | succ n ih =>
    intro wx wz hn
    rw [reserveNeed, constPolicy_choose, RecursivePhaseWorkspace.reserveNeed]
    simp only [constPolicy_widthRule, RecursivePhaseWorkspace.nextWidthBy_scan, RecursivePhaseWorkspace.immediateNeedBy_scan]
    by_cases hrec : nextWidth T.ops wx wz < max wx wz
    · have hchild : max (nextWidth T.ops wx wz) (nextWidth T.ops wx wz) ≤ n := by
        simp only [max_self]; omega
      simp only [hrec, ↓reduceDIte]
      rw [ih _ _ hchild]
    · simp [hrec]

/-! =========================================================
    Static workspace-sufficiency predicates
========================================================= -/

/-- `SignedRecursiveWorkspaceOK` with the policy in place of the single table.
Identical in shape; only the reserve recurrence it quantifies over changes. -/
structure WorkspaceOK (P : ShorLoweringPolicy) (x z : ExtReg) : Prop where
  /-- The complete owned regions of `x` and `z` do not overlap. -/
  owned_disjoint : ExtReg.OwnedDisjoint x z
  /-- `x.reserve` is large enough for the complete recursive compilation. -/
  x_reserve_sufficient : (reserveNeed P x.width z.width).1 ≤ x.capacity
  /-- `z.reserve` is large enough for the complete recursive compilation. -/
  z_reserve_sufficient : (reserveNeed P x.width z.width).2 ≤ z.capacity

/-- The controlled form: the control qubit must also sit outside both
operands' complete owned regions. -/
structure CWorkspaceOK (P : ShorLoweringPolicy) (ctrl : ℕ) (x z : ExtReg) : Prop
    extends WorkspaceOK P x z where
  /-- The control is outside both operands, workspace included. -/
  control_disjoint : ExtReg.CtrlDisjoint ctrl x z

/-! =========================================================
    Per-child reserve requirements
========================================================= -/

/-- Reserve for the `i`th child on one side: its growth now plus the policy's reserve for
the child's own recursion. -/
def requiredChildReserve (P : ShorLoweringPolicy) (T : ToomCookTable)
    (side : PhaseSide) (wx wz : ℕ) (i : Fin T.k) : ℕ :=
  let Wphase := limbWidth T.k wx wz
  let Wnext := nextWidthBy P.widthRule T.ops wx wz
  let childNeed := side.reserveComponent (reserveNeed P Wnext Wnext)
  (Wnext - phaseSplitLogicalWidth (side.width wx wz) Wphase T.k i) + childNeed

/-- The layout of one recursive step for the table `T` the policy chose: budgets are the
chunks' requirements, slack on the top chunk. Its soundness is proved in `Proofs/`. -/
def canonicalStep (P : ShorLoweringPolicy) (T : ToomCookTable) (x z : ExtReg) :
    Gate.PhaseProductLayout x z T.k :=
  have hkpos : 0 < T.k := by have := T.hk; omega
  let reqX : Fin T.k → ℕ := (requiredChildReserve P T PhaseSide.x x.width z.width)
  let reqZ : Fin T.k → ℕ := (requiredChildReserve P T PhaseSide.z x.width z.width)
  let xBudget : ReserveBudget x T.k := ReserveBudget.ofRequirements hkpos reqX
  let zBudget : ReserveBudget z T.k := ReserveBudget.ofRequirements hkpos reqZ
  { xSplit := PhaseSplitLayout.ofBudget x T.k (phaseLimbWidth x z T.k) xBudget
    zSplit := PhaseSplitLayout.ofBudget z T.k (phaseLimbWidth x z T.k) zBudget }

end Policy

/-! ---------------------------------------------------------
    Naive phase-product leaf: gate definitions
--------------------------------------------------------- -/

/-! The reference circuits used at the base of the recursion. Their
correctness lemmas live in `Proofs/NaiveLeaf.lean`. -/

def signedBitWeight (width i : ℕ) : ℤ :=
  if i + 1 = width then -((2 : ℤ) ^ i) else (2 : ℤ) ^ i

def signedTermsAux : ℕ → ℕ → List ℕ → List (ℕ × ℤ)
  | _, _, [] => []
  | width, i, q :: qs => (q, signedBitWeight width i) :: signedTermsAux width (i + 1) qs

def signedTerms (r : ExtReg) : List (ℕ × ℤ) :=
  signedTermsAux r.width 0 r.active.qubits

namespace LowGate

def sequence : List LowGate → LowGate
  | [] => LowGate.id
  | g :: gs => g ;; sequence gs

def CPhase (ctrl target : ℕ) (theta : Angle) : LowGate :=
  if ctrl = target then
    LowGate.Phase ctrl theta
  else
    LowGate.Phase ctrl (theta / 2) ;;
    LowGate.Phase target (theta / 2) ;;
    LowGate.CNOT ctrl target ;;
    LowGate.Phase target (-theta / 2) ;;
    LowGate.CNOT ctrl target

def naiveSignedPhaseGates (phi : Angle) (x z : ExtReg) : List LowGate :=
  (signedTerms x).flatMap fun xTerm =>
    (signedTerms z).map fun zTerm =>
      LowGate.CPhase xTerm.1 zTerm.1 (phi * (xTerm.2 : ℚ) * (zTerm.2 : ℚ))

def Naive_SignedPhaseProd (phi : Angle) (x z : ExtReg) : LowGate :=
  LowGate.sequence (naiveSignedPhaseGates phi x z)

def CCPhase (a b c : ℕ) (theta : Angle) : LowGate :=
  if a = b then
    LowGate.CPhase a c theta
  else if a = c then
    LowGate.CPhase a b theta
  else if b = c then
    LowGate.CPhase a b theta
  else
    LowGate.CPhase a b (theta / 2) ;;
    LowGate.Phase c (theta / 2) ;;
    LowGate.Toffoli a b c ;;
    LowGate.Phase c (-theta / 2) ;;
    LowGate.Toffoli a b c

def naiveCSignedPhaseGates (ctrl : ℕ) (phi : Angle) (x z : ExtReg) : List LowGate :=
  (signedTerms x).flatMap fun xTerm =>
    (signedTerms z).map fun zTerm =>
      LowGate.CCPhase ctrl xTerm.1 zTerm.1 (phi * (xTerm.2 : ℚ) * (zTerm.2 : ℚ))

def Naive_CSignedPhaseProd (ctrl : ℕ) (phi : Angle) (x z : ExtReg) : LowGate :=
  LowGate.sequence (naiveCSignedPhaseGates ctrl phi x z)

end LowGate

/-! ---------------------------------------------------------
    Phase-Product Lowering Definitions
--------------------------------------------------------- -/

/-! =========================================================
    Compiled gate packages
    These definitions package the phase coefficients and compiled signed gates
    that the lowering proof treats as the replacement for primitive phase-product
    gates.
========================================================= -/

/-- Compiled replacement for an uncontrolled signed phase-product gate. -/
def compiledSignedPhaseGate (k : ℕ) (hk : 1 < k) (pts : List Point) (hpts : pts.length = q k)
    (ops : Prog k) (phi : Angle) (x z : ExtReg) (layout : Gate.PhaseProductLayout x z k) : Gate :=
  compileOpsToSignedGate k hk phi x z layout (cramerCoeffFromPtsWidth k (phaseLimbWidth x z k) pts hpts) ops

/-- Compiled replacement for a controlled signed phase-product gate. -/
def compiledCSignedPhaseGate (k : ℕ) (hk : 1 < k) (pts : List Point) (hpts : pts.length = q k)
    (ops : Prog k) (ctrl : ℕ) (phi : Angle) (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z k) : Gate :=
  controlPhaseLeaves ctrl (compileOpsToSignedGate k hk phi x z layout (cramerCoeffFromPtsWidth k (phaseLimbWidth x z k) pts hpts) ops)

/-- `compiledSignedPhaseGate` under width rule `R` (`rfl` at `.scan`). -/
def compiledSignedPhaseGateBy (R : WidthRule) (k : ℕ) (hk : 1 < k) (pts : List Point)
    (hpts : pts.length = q k) (ops : Prog k) (phi : Angle) (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z k) : Gate :=
  compileOpsToSignedGateBy R k hk phi x z layout (cramerCoeffFromPtsWidth k (phaseLimbWidth x z k) pts hpts) ops

/-- `compiledCSignedPhaseGate` under width rule `R` (`rfl` at `.scan`). -/
def compiledCSignedPhaseGateBy (R : WidthRule) (k : ℕ) (hk : 1 < k) (pts : List Point)
    (hpts : pts.length = q k) (ops : Prog k) (ctrl : ℕ) (phi : Angle) (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z k) : Gate :=
  compileOpsToCSignedGateBy R k hk ctrl phi x z layout (cramerCoeffFromPtsWidth k (phaseLimbWidth x z k) pts hpts) ops

/-! =========================================================
    The lowering-plan language
    A `PhaseLoweringPlan` is a finite certificate explaining how to replace a
    high-level gate with low-level gates. Primitive arithmetic gates lower
    directly, while signed phase products either stop at a naive base gate or
    recurse through a concrete compiled phase-product layout.
========================================================= -/

/-- Finite, structurally recursive plan for lowering one high-level gate. -/
inductive PhaseLoweringPlan
    (P : ShorLoweringPolicy) :
    ℕ → Gate → Type
  | id (initSize : ℕ) : PhaseLoweringPlan P initSize Gate.id
  | seq {initSize : ℕ} {U V : Gate} (left : PhaseLoweringPlan P initSize U)
      (right : PhaseLoweringPlan P initSize V) : PhaseLoweringPlan P initSize (U ;; V)
  | H (initSize : ℕ) (qbit : ℕ) : PhaseLoweringPlan P initSize (Gate.H qbit)
  | X (initSize : ℕ) (qbit : ℕ) : PhaseLoweringPlan P initSize (Gate.X qbit)
  | ShiftL (initSize : ℕ) (r : ExtReg) (n : ℕ) : PhaseLoweringPlan P initSize (Gate.ShiftL r n)
  | ShiftR (initSize : ℕ) (r : ExtReg) (n : ℕ) : PhaseLoweringPlan P initSize (Gate.ShiftR r n)
  | Negate (initSize : ℕ) (r : ExtReg) : PhaseLoweringPlan P initSize (Gate.Negate r)
  | AddScaled (initSize : ℕ) (dst src : ExtReg) (negSrc : Bool) (shift : ℕ) :
      PhaseLoweringPlan P initSize (Gate.AddScaled dst src negSrc shift)
  | zeroExtend (initSize : ℕ) (r : ExtReg) (n : ℕ) :
      PhaseLoweringPlan P initSize (Gate.zeroExtend r n)
  | signExtend (initSize : ℕ) (r : ExtReg) (n : ℕ) :
      PhaseLoweringPlan P initSize (Gate.signExtend r n)
  | zeroDealloc (initSize : ℕ) (r : ExtReg) (n : ℕ) :
      PhaseLoweringPlan P initSize (Gate.zeroDealloc r n)
  | signDealloc (initSize : ℕ) (r : ExtReg) (n : ℕ) :
      PhaseLoweringPlan P initSize (Gate.signDealloc r n)
  | RadixReverse (initSize : ℕ) (r : Reg) (m : ℕ) :
      PhaseLoweringPlan P initSize (Gate.RadixReverse r m)

  /-- Base case: the naive circuit. -/
  | signedBase {initSize : ℕ} (phi : Angle) (x z : ExtReg) :
      PhaseLoweringPlan P initSize (Gate.SignedPhaseProd phi x z)
  /-- One recursive level: its table `T`, its `layout`, and the plan for the compiled circuit. -/
  | signedStep
      {initSize : ℕ}
      (phi : Angle)
      (x z : ExtReg)
      (T : ToomCookTable)
      (layout : Gate.PhaseProductLayout x z T.k)
      (child : PhaseLoweringPlan P (nextSignedWidthBy P.widthRule x z T.ops)
          (compiledSignedPhaseGateBy P.widthRule T.k T.hk T.pts T.hpts T.ops phi x z layout)) :
      PhaseLoweringPlan P initSize (Gate.SignedPhaseProd phi x z)
  /-- The controlled phase-product recursion has reached its base case. -/
  | cSignedBase {initSize : ℕ} (ctrl : ℕ) (phi : Angle) (x z : ExtReg) :
      PhaseLoweringPlan P initSize (Gate.CSignedPhaseProd ctrl phi x z)
  /-- A recursive controlled signed phase-product step. -/
  | cSignedStep
      {initSize : ℕ}
      (ctrl : ℕ)
      (phi : Angle)
      (x z : ExtReg)
      (T : ToomCookTable)
      (layout : Gate.PhaseProductLayout x z T.k)
      (child : PhaseLoweringPlan P (nextSignedWidthBy P.widthRule x z T.ops)
          (compiledCSignedPhaseGateBy P.widthRule T.k T.hk T.pts T.hpts T.ops ctrl phi x z layout)) :
      PhaseLoweringPlan P initSize (Gate.CSignedPhaseProd ctrl phi x z)

/-! =========================================================
    Plan-directed recursive lowering
    Interpreting a plan returns the low-level gate chosen by the plan.
========================================================= -/

/-- The low-level circuit a plan describes. -/
def lowerGateRec {P : ShorLoweringPolicy} {initSize : ℕ} {U : Gate}
    (plan : PhaseLoweringPlan P initSize U) : LowGate :=
  match plan with
  | .id _ => LowGate.id
  | .seq left right => LowGate.seq (lowerGateRec left) (lowerGateRec right)
  | .H _ qbit => LowGate.H qbit
  | .X _ qbit => LowGate.X qbit
  | .ShiftL _ r n => LowGate.ShiftL r n
  | .ShiftR _ r n => LowGate.ShiftR r n
  | .Negate _ r => LowGate.Negate r
  | .AddScaled _ dst src negSrc shift => LowGate.AddScaled dst src negSrc shift
  | .zeroExtend _ r n => LowGate.zeroExtend r n
  | .signExtend _ r n => LowGate.signExtend r n
  | .zeroDealloc _ r n => LowGate.zeroDealloc r n
  | .signDealloc _ r n => LowGate.signDealloc r n
  | .RadixReverse _ r m => LowGate.RadixReverse r m
  | .signedBase phi x z => LowGate.Naive_SignedPhaseProd phi x z
  | .signedStep _ _ _ _T _layout child => lowerGateRec child
  | .cSignedBase ctrl phi x z => LowGate.Naive_CSignedPhaseProd ctrl phi x z
  | .cSignedStep _ _ _ _ _T _layout child => lowerGateRec child

/-- A lowering plan that uses one table at every level: the plan type at the
constant policy of that table. -/
abbrev StandardPhaseLoweringPlan (k : ℕ) (hk : 1 < k) (pts : List Point) (hpts : pts.length = q k)
    (ops : Prog k) (initSize : ℕ) (U : Gate) : Type :=
  PhaseLoweringPlan (ShorLoweringPolicy.constPolicy ⟨k, hk, pts, hpts, ops⟩) initSize U

/-! ---------------------------------------------------------
    Phase-Product Lowering: plan builders
--------------------------------------------------------- -/

/-! =========================================================
    Allocation and deallocation plan builders
    These definitions mirror the compiler constructors for moving values into
    and out of a recursive phase-product layout. Each allocation or deallocation
    gate is replaced by the corresponding primitive plan node.
========================================================= -/

/-- Plan for the allocation gate generated for one chunk. -/
def planAllocChunkGate {P : ShorLoweringPolicy} {k : ℕ} (initSize : ℕ) (i : Fin k)
    (src dst : ExtReg) : PhaseLoweringPlan P initSize (allocChunkGate i src dst) := by
  unfold allocChunkGate
  dsimp
  split
  · exact PhaseLoweringPlan.id initSize
  · split
    · exact PhaseLoweringPlan.signExtend initSize src (extraDelta src dst)
    · exact PhaseLoweringPlan.zeroExtend initSize src (extraDelta src dst)

/-- Plan for the deallocation gate generated for one chunk. -/
def planDeallocChunkGate {P : ShorLoweringPolicy} {k : ℕ} (initSize : ℕ) (i : Fin k)
    (src dst : ExtReg) : PhaseLoweringPlan P initSize (deallocChunkGate i src dst) := by
  unfold deallocChunkGate
  dsimp
  split
  · exact PhaseLoweringPlan.id initSize
  · split
    · exact PhaseLoweringPlan.signDealloc initSize src (extraDelta src dst)
    · exact PhaseLoweringPlan.zeroDealloc initSize src (extraDelta src dst)

/-- Plan for an allocation prefix. -/
def planCompileSignedAllocationsAux
    {P : ShorLoweringPolicy}
    {k : ℕ}
    (initSize : ℕ)
    (src dst : LayoutState k) :
    ∀ (n : ℕ) (hn : n ≤ k),
      PhaseLoweringPlan P initSize (compileSignedAllocationsAux src dst n hn)
  | 0, _ =>
      PhaseLoweringPlan.id initSize
  | n + 1, hn =>
      let hn' : n ≤ k := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn
      let i : Fin k := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
      let previous := planCompileSignedAllocationsAux initSize src dst n hn'
      let planX := planAllocChunkGate (initSize := initSize) i (src.xslot i) (dst.xslot i)
      let planZ := planAllocChunkGate (initSize := initSize) i (src.zslot i) (dst.zslot i)
      PhaseLoweringPlan.seq previous (PhaseLoweringPlan.seq planX planZ)

/-- Plan for the full signed allocation circuit. -/
def planCompileSignedAllocations
    {P : ShorLoweringPolicy}
    {k : ℕ}
    (initSize : ℕ)
    (src dst : LayoutState k) :
    PhaseLoweringPlan P initSize
      (compileSignedAllocations k src dst) := by
  unfold compileSignedAllocations
  exact planCompileSignedAllocationsAux initSize src dst k le_rfl

/-- Plan for a deallocation prefix. -/
def planCompileSignedDeallocationsAux
    {P : ShorLoweringPolicy}
    {k : ℕ}
    (initSize : ℕ)
    (src dst : LayoutState k) :
    ∀ (n : ℕ) (hn : n ≤ k),
      PhaseLoweringPlan P initSize
        (compileSignedDeallocationsAux src dst n hn)
  | 0, _ =>
      PhaseLoweringPlan.id initSize
  | n + 1, hn =>
      let hn' : n ≤ k := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn
      let i : Fin k := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
      let planZ := planDeallocChunkGate (initSize := initSize) i (src.zslot i) (dst.zslot i)
      let planX := planDeallocChunkGate (initSize := initSize) i (src.xslot i) (dst.xslot i)
      let previous := planCompileSignedDeallocationsAux initSize src dst n hn'
      PhaseLoweringPlan.seq planZ (PhaseLoweringPlan.seq planX previous)

/-- Plan for the full signed deallocation circuit. -/
def planCompileSignedDeallocations
    {P : ShorLoweringPolicy}
    {k : ℕ}
    (initSize : ℕ)
    (src dst : LayoutState k) :
    PhaseLoweringPlan P initSize
      (compileSignedDeallocations k src dst) := by
  unfold compileSignedDeallocations
  exact planCompileSignedDeallocationsAux initSize src dst k le_rfl

/-! =========================================================
    Annotated body plan builders
    The annotated body compiler contains ordinary arithmetic operations plus
    phase-product leaves. The caller supplies the recursive plan used at each
    leaf; these builders thread that callback through the generated body.

========================================================= -/

/-- Plan for the annotated body circuit, using `recurse` at phase-product leaves. -/
def planCompileAnnotatedOpsToSignedGateAux
    {P : ShorLoweringPolicy}
    {k : ℕ}
    {hk : 1 < k}
    (initSize : ℕ)
    (phi : Angle)
    (phaseCoeff : Fin (q k) → ℚ)
    (st : LayoutState k)
    (recurse :
      ∀ (i : Fin k) (theta : Angle),
        PhaseLoweringPlan P initSize
          (Gate.SignedPhaseProd theta (st.xslot i) (st.zslot i))) :
    ∀ annotatedOps : List (AnnotatedOp k),
      PhaseLoweringPlan P initSize
        (compileAnnotatedOpsToSignedGateAux k hk phi phaseCoeff st annotatedOps)
  | [] =>
      PhaseLoweringPlan.id initSize
  | ⟨op, phaseTerm?⟩ :: rest =>
      let tail :=
        planCompileAnnotatedOpsToSignedGateAux (hk := hk) initSize phi phaseCoeff st recurse rest
      match op with
      | .shiftL i n =>
          PhaseLoweringPlan.seq (PhaseLoweringPlan.ShiftL initSize (st.xslot i) n)
            (PhaseLoweringPlan.seq (PhaseLoweringPlan.ShiftL initSize (st.zslot i) n) tail)
      | .shiftR i n =>
          PhaseLoweringPlan.seq
            (PhaseLoweringPlan.ShiftR initSize (st.xslot i) n)
            (PhaseLoweringPlan.seq (PhaseLoweringPlan.ShiftR initSize (st.zslot i) n) tail)
      | .negate i =>
          PhaseLoweringPlan.seq
            (PhaseLoweringPlan.Negate initSize (st.xslot i))
            (PhaseLoweringPlan.seq (PhaseLoweringPlan.Negate initSize (st.zslot i)) tail)
      | .addScaled dst src negSrc shift =>
          PhaseLoweringPlan.seq
            (PhaseLoweringPlan.AddScaled initSize (st.xslot dst) (st.xslot src) negSrc shift)
            (PhaseLoweringPlan.seq
              (PhaseLoweringPlan.AddScaled initSize
                (st.zslot dst) (st.zslot src) negSrc shift)
              tail)
      | .phaseProduct i =>
          match phaseTerm? with
          | some l =>
              PhaseLoweringPlan.seq (recurse i (phi * phaseCoeff l)) tail
          | none =>
              tail

/-- Plan for the controlled annotated body circuit, using `recurse` at controlled phase-product leaves. -/
def planCompileAnnotatedOpsToCSignedGateAux
    {P : ShorLoweringPolicy}
    {k : ℕ}
    {hk : 1 < k}
    (initSize : ℕ)
    (ctrl : ℕ)
    (phi : Angle)
    (phaseCoeff : Fin (q k) → ℚ)
    (st : LayoutState k)
    (recurse :
      ∀ (i : Fin k) (theta : Angle),
        PhaseLoweringPlan P initSize
          (Gate.CSignedPhaseProd ctrl theta (st.xslot i) (st.zslot i))) :
    ∀ annotatedOps : List (AnnotatedOp k),
      PhaseLoweringPlan P initSize
        (controlPhaseLeaves ctrl
          (compileAnnotatedOpsToSignedGateAux k hk phi phaseCoeff st annotatedOps))
  | [] =>
      PhaseLoweringPlan.id initSize
  | ⟨op, phaseTerm?⟩ :: rest =>
      let tail :=
        planCompileAnnotatedOpsToCSignedGateAux (hk := hk)
          initSize ctrl phi phaseCoeff st recurse rest
      match op with
      | .shiftL i n =>
          PhaseLoweringPlan.seq (PhaseLoweringPlan.ShiftL initSize (st.xslot i) n)
            (PhaseLoweringPlan.seq (PhaseLoweringPlan.ShiftL initSize (st.zslot i) n) tail)
      | .shiftR i n =>
          PhaseLoweringPlan.seq (PhaseLoweringPlan.ShiftR initSize (st.xslot i) n)
            (PhaseLoweringPlan.seq (PhaseLoweringPlan.ShiftR initSize (st.zslot i) n) tail)
      | .negate i =>
          PhaseLoweringPlan.seq (PhaseLoweringPlan.Negate initSize (st.xslot i))
            (PhaseLoweringPlan.seq (PhaseLoweringPlan.Negate initSize (st.zslot i)) tail)
      | .addScaled dst src negSrc shift =>
          PhaseLoweringPlan.seq
            (PhaseLoweringPlan.AddScaled initSize (st.xslot dst) (st.xslot src) negSrc shift)
            (PhaseLoweringPlan.seq
              (PhaseLoweringPlan.AddScaled initSize (st.zslot dst) (st.zslot src) negSrc shift)
              tail)
      | .phaseProduct i =>
          match phaseTerm? with
          | some l =>
              PhaseLoweringPlan.seq (recurse i (phi * phaseCoeff l)) tail
          | none =>
              tail

/-! =========================================================
    One-level compiled phase-product plans — the per-table step
    A recursive step consists of allocation, the annotated body, and
    deallocation. `Policy.stepPlan` assembles those three pieces for **one**
    table, taking the children as a `recurse` argument. It performs no lookup:
    that is the dispatcher's job below.
    The split is deliberate. If the lookup were inlined here, the extracted
    per-table IR body would carry the policy's threshold tests, and the
    per-table IR split would be lost.
========================================================= -/

/-- Plan for the compiled signed phase-product replacement at one recursive
level, under the table `T` the policy chose at this node. -/
def Policy.stepPlan
    (P : ShorLoweringPolicy)
    (T : ToomCookTable)
    (phi : Angle)
    (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z T.k)
    (recurse :
      let src := initSignedLayoutState layout
      let dst := targetSignedLayoutState src (neededWidthsBy P.widthRule x z T.ops)
      ∀ (i : Fin T.k) (theta : Angle),
        PhaseLoweringPlan P (nextSignedWidthBy P.widthRule x z T.ops)
          (Gate.SignedPhaseProd theta (dst.xslot i) (dst.zslot i))) :
    PhaseLoweringPlan P (nextSignedWidthBy P.widthRule x z T.ops)
      (compiledSignedPhaseGateBy P.widthRule T.k T.hk T.pts T.hpts T.ops phi x z layout) :=
  -- allocation, then the annotated body with `recurse` at its leaves, then deallocation
  let src : LayoutState T.k := initSignedLayoutState layout
  let dst : LayoutState T.k := targetSignedLayoutState src (neededWidthsBy P.widthRule x z T.ops)
  PhaseLoweringPlan.seq (planCompileSignedAllocations (nextSignedWidthBy P.widthRule x z T.ops) src dst)
    (PhaseLoweringPlan.seq
      (planCompileAnnotatedOpsToSignedGateAux (hk := T.hk) (nextSignedWidthBy P.widthRule x z T.ops) phi
        (cramerCoeffFromPtsWidth T.k (phaseLimbWidth x z T.k) T.pts T.hpts) dst recurse (annotatePhaseTermsAux T.k 0 T.ops))
      (planCompileSignedDeallocations (nextSignedWidthBy P.widthRule x z T.ops) src dst))

/-- Plan for the compiled controlled signed phase-product replacement at one
recursive level, under the table `T` the policy chose at this node. -/
def Policy.cStepPlan
    (P : ShorLoweringPolicy)
    (T : ToomCookTable)
    (ctrl : ℕ)
    (phi : Angle)
    (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z T.k)
    (recurse :
      let src := initSignedLayoutState layout
      let dst := targetSignedLayoutState src (neededWidthsBy P.widthRule x z T.ops)
      ∀ (i : Fin T.k) (theta : Angle),
        PhaseLoweringPlan P (nextSignedWidthBy P.widthRule x z T.ops)
          (Gate.CSignedPhaseProd ctrl theta (dst.xslot i) (dst.zslot i))) :
    PhaseLoweringPlan P (nextSignedWidthBy P.widthRule x z T.ops)
      (compiledCSignedPhaseGateBy P.widthRule T.k T.hk T.pts T.hpts T.ops ctrl phi x z layout) := by
  -- as `Policy.stepPlan`, cast along `controlPhaseLeaves` fixing the allocations
  let src : LayoutState T.k := initSignedLayoutState layout
  let dst : LayoutState T.k := targetSignedLayoutState src (neededWidthsBy P.widthRule x z T.ops)
  have plan :
      PhaseLoweringPlan P (nextSignedWidthBy P.widthRule x z T.ops)
        (compileSignedAllocations T.k src dst ;;
          controlPhaseLeaves ctrl (compileAnnotatedOpsToSignedGateAux T.k T.hk phi
            (cramerCoeffFromPtsWidth T.k (phaseLimbWidth x z T.k) T.pts T.hpts) dst (annotatePhaseTermsAux T.k 0 T.ops)) ;;
          compileSignedDeallocations T.k src dst) :=
    PhaseLoweringPlan.seq (planCompileSignedAllocations (nextSignedWidthBy P.widthRule x z T.ops) src dst)
      (PhaseLoweringPlan.seq
        (planCompileAnnotatedOpsToCSignedGateAux (hk := T.hk) (nextSignedWidthBy P.widthRule x z T.ops) ctrl phi
          (cramerCoeffFromPtsWidth T.k (phaseLimbWidth x z T.k) T.pts T.hpts) dst recurse (annotatePhaseTermsAux T.k 0 T.ops))
        (planCompileSignedDeallocations (nextSignedWidthBy P.widthRule x z T.ops) src dst))
  simpa [compiledCSignedPhaseGateBy, compileOpsToCSignedGateBy, compileOpsToSignedGateBy,
    controlPhaseLeaves, controlPhaseLeaves_compileSignedAllocations,
    controlPhaseLeaves_compileSignedDeallocations, src, dst] using plan

/-! =========================================================
    The dispatcher
    `Policy.signedPlanOf` is the only recursive definition: it consults the
    policy at the node's input width, applies the shrink test, and calls the
    per-table step with itself as `recurse`. `choose = none` and a
    non-shrinking table both land on the base case, which is exactly what
    `ShorLoweringPolicy.Stops` says.
========================================================= -/

/-- The dispatcher, with the lookup result `o` passed in (so its equation lemmas reduce by
`cases o`). `n` labels the plan; children are labelled `nextSignedWidthBy P.widthRule` and terminate by
`phaseInputSize_target_le`. -/
def Policy.signedPlanOf
    (P : ShorLoweringPolicy)
    (phi : Angle)
    (x z : ExtReg)
    (n : ℕ) :
    ∀ (o : Option ToomCookTable), P.choose (phaseInputSize x z) = o →
      PhaseLoweringPlan P n (Gate.SignedPhaseProd phi x z)
  | none, _ =>
      PhaseLoweringPlan.signedBase phi x z
  | some T, _ =>
      if _hrec : nextSignedWidthBy P.widthRule x z T.ops < phaseInputSize x z then
        let layout : Gate.PhaseProductLayout x z T.k := Policy.canonicalStep P T x z
        let src : LayoutState T.k := initSignedLayoutState layout
        let dst : LayoutState T.k := targetSignedLayoutState src (neededWidthsBy P.widthRule x z T.ops)
        let recurse : ∀ (i : Fin T.k) (theta : Angle),
            PhaseLoweringPlan P (nextSignedWidthBy P.widthRule x z T.ops)
              (Gate.SignedPhaseProd theta (dst.xslot i) (dst.zslot i)) := fun i theta =>
          Policy.signedPlanOf P theta (dst.xslot i) (dst.zslot i) (nextSignedWidthBy P.widthRule x z T.ops) _ rfl
        PhaseLoweringPlan.signedStep phi x z T layout
          (Policy.stepPlan P T phi x z layout recurse)
      else
        PhaseLoweringPlan.signedBase phi x z
termination_by phaseInputSize x z
decreasing_by
  exact lt_of_le_of_lt (phaseInputSize_target_le_by P.widthRule layout T.ops i) _hrec

/-- Canonical recursive plan for a signed phase product under a policy. -/
def Policy.signedPlan (P : ShorLoweringPolicy) (phi : Angle) (x z : ExtReg) :
    PhaseLoweringPlan P (phaseInputSize x z) (Gate.SignedPhaseProd phi x z) :=
  Policy.signedPlanOf P phi x z (phaseInputSize x z) _ rfl

/-- The controlled dispatcher body. Same shape as `Policy.signedPlanOf`. -/
def Policy.cSignedPlanOf
    (P : ShorLoweringPolicy)
    (ctrl : ℕ)
    (phi : Angle)
    (x z : ExtReg)
    (n : ℕ) :
    ∀ (o : Option ToomCookTable), P.choose (phaseInputSize x z) = o →
      PhaseLoweringPlan P n (Gate.CSignedPhaseProd ctrl phi x z)
  | none, _ =>
      PhaseLoweringPlan.cSignedBase ctrl phi x z
  | some T, _ =>
      if _hrec : nextSignedWidthBy P.widthRule x z T.ops < phaseInputSize x z then
        let layout : Gate.PhaseProductLayout x z T.k := Policy.canonicalStep P T x z
        let src : LayoutState T.k := initSignedLayoutState layout
        let dst : LayoutState T.k := targetSignedLayoutState src (neededWidthsBy P.widthRule x z T.ops)
        let recurse : ∀ (i : Fin T.k) (theta : Angle),
            PhaseLoweringPlan P (nextSignedWidthBy P.widthRule x z T.ops)
              (Gate.CSignedPhaseProd ctrl theta (dst.xslot i) (dst.zslot i)) := fun i theta =>
          Policy.cSignedPlanOf P ctrl theta (dst.xslot i) (dst.zslot i)
            (nextSignedWidthBy P.widthRule x z T.ops) _ rfl
        PhaseLoweringPlan.cSignedStep ctrl phi x z T layout
          (Policy.cStepPlan P T ctrl phi x z layout recurse)
      else
        PhaseLoweringPlan.cSignedBase ctrl phi x z
termination_by phaseInputSize x z
decreasing_by
  exact lt_of_le_of_lt (phaseInputSize_target_le_by P.widthRule layout T.ops i) _hrec

/-- Canonical recursive plan for a controlled signed phase product under a
policy. -/
def Policy.cSignedPlan (P : ShorLoweringPolicy) (ctrl : ℕ) (phi : Angle) (x z : ExtReg) :
    PhaseLoweringPlan P (phaseInputSize x z) (Gate.CSignedPhaseProd ctrl phi x z) :=
  Policy.cSignedPlanOf P ctrl phi x z (phaseInputSize x z) _ rfl

/-! =========================================================
    The fixed-table planners
    Each is the dispatcher at the constant policy.
========================================================= -/

/-- Canonical recursive plan for a signed phase product from static recursive workspace data. -/
def standardSignedPhaseLoweringPlan (k : ℕ) (hk : 1 < k) (phi : Angle) (x z : ExtReg) (ops : Prog k)
    (pts : List Point) (hpts : pts.length = q k) :
    StandardPhaseLoweringPlan k hk pts hpts ops (phaseInputSize x z) (Gate.SignedPhaseProd phi x z) :=
  Policy.signedPlanOf (ShorLoweringPolicy.constPolicy ⟨k, hk, pts, hpts, ops⟩) phi x z
    (phaseInputSize x z) _ rfl

/-- Canonical recursive plan for a controlled signed phase product from static recursive workspace data. -/
def standardCSignedPhaseLoweringPlan (k : ℕ) (hk : 1 < k) (ctrl : ℕ) (phi : Angle) (x z : ExtReg)
    (ops : Prog k) (pts : List Point) (hpts : pts.length = q k) :
    StandardPhaseLoweringPlan k hk pts hpts ops (phaseInputSize x z) (Gate.CSignedPhaseProd ctrl phi x z) :=
  Policy.cSignedPlanOf (ShorLoweringPolicy.constPolicy ⟨k, hk, pts, hpts, ops⟩) ctrl phi x z
    (phaseInputSize x z) _ rfl

/-! ---------------------------------------------------------
    Phase-Product Lowering: entry points
--------------------------------------------------------- -/

/-- The lowered circuit of the canonical fixed-table plan. -/
def lowerSignedPhaseProd (k : ℕ) (hk : 1 < k) (phi : Angle) (x z : ExtReg)
    (ops : Prog k) (pts : List Point) (hpts : pts.length = q k) : LowGate :=
  lowerGateRec (standardSignedPhaseLoweringPlan k hk phi x z ops pts hpts)

/-- The controlled form. -/
def lowerCSignedPhaseProd (k : ℕ) (hk : 1 < k) (ctrl : ℕ) (phi : Angle)
    (x z : ExtReg) (ops : Prog k) (pts : List Point) (hpts : pts.length = q k) : LowGate :=
  lowerGateRec (standardCSignedPhaseLoweringPlan k hk ctrl phi x z ops pts hpts)

/-! =========================================================
    The policy-level lowerers
    The names the Shor layer calls when it lowers through a policy.
    The fixed-table lowerers above are these at `constPolicy`, which is what
    `Policy.workspaceOK_const_iff` says.
========================================================= -/

/-- The lowered circuit for a signed phase product under a policy: the dispatcher's
plan, erased to a `LowGate`. -/
def Policy.lowerSignedPhaseProd (P : ShorLoweringPolicy) (phi : Angle) (x z : ExtReg) : LowGate :=
  lowerGateRec (Policy.signedPlan P phi x z)

/-- The lowered controlled circuit for a signed phase product under a policy. -/
def Policy.lowerCSignedPhaseProd (P : ShorLoweringPolicy) (ctrl : ℕ) (phi : Angle) (x z : ExtReg) :
    LowGate :=
  lowerGateRec (Policy.cSignedPlan P ctrl phi x z)

/-! ---------------------------------------------------------
    Phase-Product Cleanliness Predicates
--------------------------------------------------------- -/

/-! ### Basis-clean linear closure -/

/-- The set of states reachable from `P`-clean basis kets by `+` and `•`:
    a `zero/ket/add/smul` linear closure parameterized by the per-basis
    predicate `P`. -/
inductive CleanClosure {qs : QSemantics} [RegEncoding qs.Basis]
    (P : qs.Basis → Prop) : qs.State → Prop
  | zero : CleanClosure P 0
  | ket (b : qs.Basis) (h : P b) : CleanClosure P (qs.ket b)
  | add {ψ φ : qs.State} (hψ : CleanClosure P ψ) (hφ : CleanClosure P φ) :
      CleanClosure P (ψ + φ)
  | smul (a : ℂ) {ψ : qs.State} (hψ : CleanClosure P ψ) :
      CleanClosure P (a • ψ)


/-! =========================================================
    Cleanliness of the complete reserves
========================================================= -/

/-- Both whole reserves are zero in a basis state. -/
def RecursiveWorkspaceCleanBasis
    {Basis : Type u} [RegEncoding Basis] (x z : ExtReg) (b : Basis) : Prop :=
  ExtReg.FreshFor x x.capacity b ∧ ExtReg.FreshFor z z.capacity b

/-- A state supported on basis states whose `x` and `z` reserves are zero. -/
abbrev RecursiveWorkspaceCleanState
    (qs : QSemantics) [RegEncoding qs.Basis] (x z : ExtReg) : qs.State → Prop :=
  CleanClosure (fun b => RecursiveWorkspaceCleanBasis x z b)

/-! =========================================================
    Combined public workspace preconditions
========================================================= -/

/-- The complete public workspace precondition for an uncontrolled signed phase
product. -/
structure SignedRecursiveWorkspaceStateOK (qs : QSemantics) [RegEncoding qs.Basis] {k : ℕ}
    (ops : Prog k) (x z : ExtReg) (ψ : qs.State) : Prop where
  static : SignedRecursiveWorkspaceOK ops x z
  clean : RecursiveWorkspaceCleanState qs x z ψ

/-- The complete public workspace precondition for a controlled signed phase
product. -/
structure CSignedRecursiveWorkspaceStateOK (qs : QSemantics) [RegEncoding qs.Basis] {k : ℕ}
    (ops : Prog k) (ctrl : ℕ) (x z : ExtReg) (ψ : qs.State) : Prop where
  static : CSignedRecursiveWorkspaceOK ops ctrl x z
  clean : RecursiveWorkspaceCleanState qs x z ψ

/-! =========================================================
    The policy forms
    Same two records with the policy's static predicate in place of the fixed
    table's. The cleanliness half is unchanged: it is about the registers, not
    about which table will be used on them.
========================================================= -/

/-- The complete public workspace precondition for an uncontrolled signed phase
product lowered through a policy. -/
structure Policy.WorkspaceStateOK (qs : QSemantics) [RegEncoding qs.Basis]
    (P : ShorLoweringPolicy) (x z : ExtReg) (ψ : qs.State) : Prop where
  /-- The reserves are large enough for the whole policy-driven recursion. -/
  static : Policy.WorkspaceOK P x z
  /-- Every reserve qubit is zero. -/
  clean : RecursiveWorkspaceCleanState qs x z ψ

/-- The complete public workspace precondition for a controlled signed phase
product lowered through a policy. -/
structure Policy.CWorkspaceStateOK (qs : QSemantics) [RegEncoding qs.Basis]
    (P : ShorLoweringPolicy) (ctrl : ℕ) (x z : ExtReg) (ψ : qs.State) : Prop where
  /-- The reserves are large enough, and the control is outside both operands. -/
  static : Policy.CWorkspaceOK P ctrl x z
  /-- Every reserve qubit is zero. -/
  clean : RecursiveWorkspaceCleanState qs x z ψ

/-! ---------------------------------------------------------
    Phase-Product Public Assertions
--------------------------------------------------------- -/

/-- The lowered signed phase product equals `Gate.SignedPhaseProd` on clean valid workspace. -/
def LowerSignedPhaseProductCorrect
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (k : ℕ) (hk : 1 < k)
    (phi : Angle)
    (x z : ExtReg)
    (ops : Prog k) : Prop :=
  ∀ (ψ : qs.State) (pts : List Point) (hpts : pts.length = q k)
    (hworkspace : SignedRecursiveWorkspaceStateOK qs ops x z ψ)
    (hInterp : GoodToomCookPoints k pts hpts)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops pts)
    (hRun : run? ops State.start_state = some State.start_state),
    LowerGateClass.evalL (qs := qs)
        (lowerSignedPhaseProd k hk phi x z ops pts hpts) ψ
      =
    qs.eval (Gate.SignedPhaseProd phi x z) ψ

/-- The controlled form. -/
def LowerCSignedPhaseProductCorrect
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (k : ℕ) (hk : 1 < k)
    (ctrl : ℕ)
    (phi : Angle)
    (x z : ExtReg)
    (ops : Prog k) : Prop :=
  ∀ (ψ : qs.State) (pts : List Point) (hpts : pts.length = q k)
    (hworkspace : CSignedRecursiveWorkspaceStateOK qs ops ctrl x z ψ)
    (hInterp : GoodToomCookPoints k pts hpts)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops pts)
    (hRun : run? ops State.start_state = some State.start_state),
    LowerGateClass.evalL (qs := qs)
        (lowerCSignedPhaseProd k hk ctrl phi x z ops pts hpts) ψ
      =
    qs.eval (Gate.CSignedPhaseProd ctrl phi x z) ψ

/-! =========================================================
    The policy forms
    The claim a policy submission receives. The admissibility of the policy is
    a hypothesis here, exactly as C2–C4 of the single table are hypotheses of
    the fixed-table claims above — the plan type is indexed by data, and the
    proofs enter at the correctness statement.
========================================================= -/

/-- The policy form: correct whenever every table the policy can choose is admissible. -/
def Policy.LowerSignedPhaseProductCorrect
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (P : ShorLoweringPolicy)
    (phi : Angle)
    (x z : ExtReg) : Prop :=
  ∀ (ψ : qs.State), Policy.WorkspaceStateOK qs P x z ψ →
    P.Admissible →
    LowerGateClass.evalL (qs := qs)
        (Policy.lowerSignedPhaseProd P phi x z) ψ
      =
    qs.eval (Gate.SignedPhaseProd phi x z) ψ

/-- The controlled form. -/
def Policy.LowerCSignedPhaseProductCorrect
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (P : ShorLoweringPolicy)
    (ctrl : ℕ)
    (phi : Angle)
    (x z : ExtReg) : Prop :=
  ∀ (ψ : qs.State), Policy.CWorkspaceStateOK qs P ctrl x z ψ →
    P.Admissible →
    LowerGateClass.evalL (qs := qs)
        (Policy.lowerCSignedPhaseProd P ctrl phi x z) ψ
      =
    qs.eval (Gate.CSignedPhaseProd ctrl phi x z) ψ

/-! =========================================================
    Gate count

    The asymptotic gate count of the signed phase product for a fixed
    Toom-Cook table: above some width, the lowered gate count is at most a
    constant times `n^(log_k (2k - 1))`, `n` the wider operand's width;
    `q k = 2k - 1` is the number of recursive products a level runs.
========================================================= -/

/-- The conditions a table's program needs: good interpolation points (C1/C2),
safe point consumption (C3), and a program that returns to its start state
(C4). They are the fields of a `ShorLoweringSetup` and the conjuncts of
`ToomCookTable.Admissible`. -/
def PhaseProductProgramOK
    (k : ℕ) (hk : 1 < k) (pts : List Point) (hpts : pts.length = q k) (ops : Prog k) : Prop :=
  GoodToomCookPoints k pts hpts ∧
  ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops pts ∧
  run? ops State.start_state = some State.start_state

/-- Gate count of the lowered signed phase product for a fixed table. -/
noncomputable def signedPhaseProductGateCount
    {Basis : Type u} [RegEncoding Basis]
    (k : ℕ) (hk : 1 < k) (ops : Prog k) (pts : List Point) (hpts : pts.length = q k)
    (φ : Angle) (x z : ExtReg) : ℕ :=
  LowGate.gateCount shorGateCostModel
    (lowerSignedPhaseProd k hk φ x z ops pts hpts)

/-- Gate count of the lowered controlled signed phase product for a fixed table. -/
noncomputable def cSignedPhaseProductGateCount
    {Basis : Type u} [RegEncoding Basis]
    (k : ℕ) (hk : 1 < k) (ops : Prog k) (pts : List Point) (hpts : pts.length = q k)
    (ctrl : ℕ) (φ : Angle) (x z : ExtReg) : ℕ :=
  LowGate.gateCount shorGateCostModel
    (lowerCSignedPhaseProd k hk ctrl φ x z ops pts hpts)

/-- **The signed phase-product gate-count bound** for a fixed table: there are
a constant `C` and a width `n₀` such that every signed phase product whose
operands have the workspace the recursion needs, each at least one bit wide
and the wider at least `n₀` bits wide, lowers to at most `C · n^(log_k (2k - 1))`
gates, `n` the wider operand's width. -/
def SignedPhaseProductGateCountBound
    {Basis : Type u} [RegEncoding Basis] (k : ℕ) (hk : 1 < k) (ops : Prog k)
    (pts : List Point) (hpts : pts.length = q k) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 1 ≤ n₀ ∧
    ∀ (φ : Angle) (x z : ExtReg), SignedRecursiveWorkspaceOK ops x z →
      1 ≤ ExtReg.width x → 1 ≤ ExtReg.width z →
      let n := max (ExtReg.width x) (ExtReg.width z)
      n₀ ≤ n →
      (signedPhaseProductGateCount (Basis := Basis) k hk ops pts hpts φ x z : ℝ)
        ≤ C * Real.rpow n (Real.log (q k : ℝ) / Real.log (k : ℝ))

/-- **The controlled signed phase-product gate-count bound**: the same, for
the controlled product, with the control outside both operands. -/
def CSignedPhaseProductGateCountBound
    {Basis : Type u} [RegEncoding Basis] (k : ℕ) (hk : 1 < k) (ops : Prog k)
    (pts : List Point) (hpts : pts.length = q k) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 1 ≤ n₀ ∧
    ∀ (ctrl : ℕ) (φ : Angle) (x z : ExtReg), CSignedRecursiveWorkspaceOK ops ctrl x z →
      1 ≤ ExtReg.width x → 1 ≤ ExtReg.width z →
      let n := max (ExtReg.width x) (ExtReg.width z)
      n₀ ≤ n →
      (cSignedPhaseProductGateCount (Basis := Basis) k hk ops pts hpts ctrl φ x z : ℝ)
        ≤ C * Real.rpow n (Real.log (q k : ℝ) / Real.log (k : ℝ))

/-- **Assertion: the signed phase-product gate count of a table.** A table
satisfying C1–C4 has the bound `SignedPhaseProductGateCountBound`.
(`Main.lean`: `signedPhaseProductGateCountBound_of_programOK`.) -/
def SignedPhaseProductGateCountBoundOfProgramOK
    {Basis : Type u} [RegEncoding Basis] (k : ℕ) (hk : 1 < k) (ops : Prog k)
    (pts : List Point) (hpts : pts.length = q k) : Prop :=
  PhaseProductProgramOK k hk pts hpts ops →
    SignedPhaseProductGateCountBound (Basis := Basis) k hk ops pts hpts

/-- **Assertion: the controlled signed phase-product gate count of a table.**
A table satisfying C1–C4 has the bound `CSignedPhaseProductGateCountBound`.
(`Main.lean`: `cSignedPhaseProductGateCountBound_of_programOK`.) -/
def CSignedPhaseProductGateCountBoundOfProgramOK
    {Basis : Type u} [RegEncoding Basis] (k : ℕ) (hk : 1 < k) (ops : Prog k)
    (pts : List Point) (hpts : pts.length = q k) : Prop :=
  PhaseProductProgramOK k hk pts hpts ops →
    CSignedPhaseProductGateCountBound (Basis := Basis) k hk ops pts hpts

/-! =========================================================
    Gate count under a policy

    The same bound for a policy. Every width at or above the first band's
    threshold uses the first band's table, so the exponent is that table's
    `log_k (2k - 1)`; the narrower bands change the constant. A policy with
    no bands is the schoolbook leaf at every width, with exponent `2`. The
    count is priced by the policy's own resource model, so by its negation
    method.
========================================================= -/

/-- The gate-count exponent of a policy: `log_k (2k - 1)` for the arity `k` of
its first band, and `2` for the policy with no bands. -/
noncomputable def ShorLoweringPolicy.gateExponent (P : ShorLoweringPolicy) : ℝ :=
  match P.bands.head? with
  | some b => Real.log ((2 * b.table.k - 1 : ℕ) : ℝ) / Real.log (b.table.k : ℝ)
  | none => 2

/-- Gate count of the lowered signed phase product under a policy. -/
noncomputable def Policy.signedPhaseProductGateCount
    (P : ShorLoweringPolicy) (φ : Angle) (x z : ExtReg) : ℕ :=
  LowGate.gateCount P.resourceModel.toCostModel (Policy.lowerSignedPhaseProd P φ x z)

/-- Gate count of the lowered controlled signed phase product under a policy. -/
noncomputable def Policy.cSignedPhaseProductGateCount
    (P : ShorLoweringPolicy) (ctrl : ℕ) (φ : Angle) (x z : ExtReg) : ℕ :=
  LowGate.gateCount P.resourceModel.toCostModel (Policy.lowerCSignedPhaseProd P ctrl φ x z)

/-- **The signed phase-product gate-count bound under a policy**: if the
policy is admissible, there are a constant `C` and a width `n₀` such that every
signed phase product whose operands have the workspace the policy's recursion
needs, the wider at least `n₀` bits wide, lowers to at most
`C · n^P.gateExponent` gates, `n` the wider operand's width. -/
def Policy.SignedPhaseProductGateCountBound (P : ShorLoweringPolicy) : Prop :=
  P.Admissible →
  ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 1 ≤ n₀ ∧
    ∀ (φ : Angle) (x z : ExtReg), Policy.WorkspaceOK P x z →
      let n := max (ExtReg.width x) (ExtReg.width z)
      n₀ ≤ n →
      (Policy.signedPhaseProductGateCount P φ x z : ℝ) ≤ C * Real.rpow n P.gateExponent

/-- **The controlled signed phase-product gate-count bound under a policy**:
the same, for the controlled product, with the control outside both operands. -/
def Policy.CSignedPhaseProductGateCountBound (P : ShorLoweringPolicy) : Prop :=
  P.Admissible →
  ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 1 ≤ n₀ ∧
    ∀ (ctrl : ℕ) (φ : Angle) (x z : ExtReg), Policy.CWorkspaceOK P ctrl x z →
      let n := max (ExtReg.width x) (ExtReg.width z)
      n₀ ≤ n →
      (Policy.cSignedPhaseProductGateCount P ctrl φ x z : ℝ) ≤ C * Real.rpow n P.gateExponent

end Shor
