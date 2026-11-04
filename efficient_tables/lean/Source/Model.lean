import Source.Metrics
namespace TableGeneration.RecursiveCost

open Operations

/-!
# Recursive PhaseProduct cost model

This file mirrors the width scan and conservative logical-gate cost definitions
used by ForShor's PhaseProduct implementation. It is intentionally independent
of the submission interface and contains no policy selection.
-/

/-- Logical widths of the two PhaseProduct operand arrays. -/
structure WidthState (k : Nat) where
  xw : Fin k → Nat
  zw : Fin k → Nat

/-- Maximum widths encountered while scanning a table-generation program. -/
structure NeededWidths (k : Nat) where
  xneed : Fin k → Nat
  zneed : Fin k → Nat

/-- Replace one entry of a finite width vector. -/
def updateWidth {k : Nat}
    (widths : Fin k → Nat) (index : Fin k) (width : Nat) : Fin k → Nat :=
  fun i => if i = index then width else widths i

/-- Width of each non-top limb before the most-significant remainder limb. -/
def phaseLimbWidthOfWidth (width k : Nat) : Nat :=
  width / k

/-- Common lower-limb width used to split both operands. -/
def phaseLimbWidth (xWidth zWidth k : Nat) : Nat :=
  min (phaseLimbWidthOfWidth xWidth k) (phaseLimbWidthOfWidth zWidth k)

/-- The final limb absorbs every bit not assigned to a lower limb. -/
def phaseSplitLogicalWidth
    (width commonWidth k : Nat) (i : Fin k) : Nat :=
  if i.val + 1 = k then width - i.val * commonWidth else commonWidth

/-- Initial top-heavy split for both PhaseProduct operands. -/
def initWidthState (xWidth zWidth k : Nat) : WidthState k :=
  let commonWidth := phaseLimbWidth xWidth zWidth k
  { xw := fun i => phaseSplitLogicalWidth xWidth commonWidth k i
    zw := fun i => phaseSplitLogicalWidth zWidth commonWidth k i }

/-- ForShor's conservative width transition for one symbolic operation. -/
def updateWidthState {k : Nat}
    (state : WidthState k) : valid_ops k → WidthState k
  | .shiftL i amount =>
      { xw := updateWidth state.xw i (state.xw i + amount)
        zw := updateWidth state.zw i (state.zw i + amount) }
  | .shiftR i amount =>
      { xw := updateWidth state.xw i (state.xw i - amount)
        zw := updateWidth state.zw i (state.zw i - amount) }
  | .negate i =>
      { xw := updateWidth state.xw i (state.xw i + 1)
        zw := updateWidth state.zw i (state.zw i + 1) }
  | .addScaled dst src _negSrc shift =>
      let newX := 1 + max (state.xw dst) (state.xw src + shift)
      let newZ := 1 + max (state.zw dst) (state.zw src + shift)
      { xw := updateWidth state.xw dst newX
        zw := updateWidth state.zw dst newZ }
  | .phaseProduct _ => state

/-- Regard current widths as lower bounds on the required capacities. -/
def widthsOfState {k : Nat} (state : WidthState k) : NeededWidths k where
  xneed := state.xw
  zneed := state.zw

/-- Pointwise maximum of two capacity records. -/
def mergeNeededWidths {k : Nat}
    (left right : NeededWidths k) : NeededWidths k where
  xneed := fun i => max (left.xneed i) (right.xneed i)
  zneed := fun i => max (left.zneed i) (right.zneed i)

/-- Scan a program while retaining the maximum width of every slot. -/
def scanNeededWidthsAux {k : Nat}
    (current : WidthState k) (needed : NeededWidths k) :
    Prog k → NeededWidths k
  | [] => needed
  | op :: rest =>
      let current' := updateWidthState current op
      let needed' := mergeNeededWidths needed (widthsOfState current')
      scanNeededWidthsAux current' needed' rest

/-- Required capacities for a program at the supplied operand widths. -/
def scanNeededWidths {k : Nat}
    (xWidth zWidth : Nat) (ops : Prog k) : NeededWidths k :=
  let initial := initWidthState xWidth zWidth k
  scanNeededWidthsAux initial (widthsOfState initial) ops

/-- Largest required width across all operand slots. -/
def maximumNeededWidth {k : Nat} (needed : NeededWidths k) : Nat :=
  (List.finRange k).foldl
    (fun width i => max width (max (needed.xneed i) (needed.zneed i))) 0

/-- Common signed width used by ForShor for every recursive child. -/
def commonNeededWidth {k : Nat} (needed : NeededWidths k) : Nat :=
  1 + maximumNeededWidth needed

/-- Width of the recursively compiled PhaseProduct children. -/
def nextSignedWidth {k : Nat}
    (xWidth zWidth : Nat) (ops : Prog k) : Nat :=
  commonNeededWidth (scanNeededWidths xWidth zWidth ops)

/-!
The website profile uses balanced operands. The following array scan is an
evaluation-oriented form of the same transitions above. It avoids retaining a
long chain of function updates when large promoted programs are interpreted.
-/

/-- Top-heavy split represented as a compact array for balanced inputs. -/
def initBalancedWidths (width k : Nat) : Array Nat :=
  let commonWidth := phaseLimbWidth width width k
  Array.ofFn (fun i : Fin k =>
    phaseSplitLogicalWidth width commonWidth k i)

/-- Safe lookup for an index originating from the same `k` as the array. -/
def balancedWidthAt {k : Nat} (widths : Array Nat) (index : Fin k) : Nat :=
  widths[index.val]?.getD 0

/-- Array form of one balanced ForShor width transition. -/
def updateBalancedWidths {k : Nat}
    (widths : Array Nat) : valid_ops k → Array Nat
  | .shiftL index amount =>
      widths.setIfInBounds index.val (balancedWidthAt widths index + amount)
  | .shiftR index amount =>
      widths.setIfInBounds index.val (balancedWidthAt widths index - amount)
  | .negate index =>
      widths.setIfInBounds index.val (balancedWidthAt widths index + 1)
  | .addScaled destination source _negative shift =>
      let newWidth := 1 + max (balancedWidthAt widths destination)
        (balancedWidthAt widths source + shift)
      widths.setIfInBounds destination.val newWidth
  | .phaseProduct _ => widths

/-- Largest entry in a compact balanced width state. -/
def maximumBalancedWidth (widths : Array Nat) : Nat :=
  widths.foldl max 0

/-- Scan a balanced program and retain the maximum capacity ever requested. -/
def scanBalancedMaximumAux {k : Nat}
    (current : Array Nat) (maximum : Nat) : Prog k → Nat
  | [] => maximum
  | op :: rest =>
      let current' := updateBalancedWidths current op
      let maximum' := max maximum (maximumBalancedWidth current')
      scanBalancedMaximumAux current' maximum' rest

/-- Fast balanced-input form of `nextSignedWidth width width ops`. -/
def nextBalancedSignedWidth {k : Nat} (width : Nat) (ops : Prog k) : Nat :=
  let initial := initBalancedWidths width k
  1 + scanBalancedMaximumAux initial (maximumBalancedWidth initial) ops

/-- Conservative ForShor bound for one ripple-carry addition. -/
def rippleAdderGateBound (width : Nat) : Nat :=
  9 * width + 2

/-- Conservative ForShor bound for two's-complement negation. -/
def negateGateBound (width : Nat) : Nat :=
  width + rippleAdderGateBound width

/-- Direct signed PhaseProduct base-case cost. -/
def directSignedPhaseProductGateCount (xWidth zWidth : Nat) : Nat :=
  xWidth * zWidth

/--
Nonrecursive arithmetic cost of one table operation at the common working
width. Arithmetic is applied once to each of the two PhaseProduct operands.
-/
def phaseArithmeticOpCost {k : Nat}
    (workingWidth : Nat) : valid_ops k → Nat
  | .shiftL _ _ => 0
  | .shiftR _ _ => 0
  | .negate _ => 2 * negateGateBound workingWidth
  | .addScaled _ _ _ _ => 2 * rippleAdderGateBound workingWidth
  | .phaseProduct _ => 0

/-- Total nonrecursive gate cost of a table-generation program. -/
def phaseProgramOverhead {k : Nat}
    (workingWidth : Nat) (ops : Prog k) : Nat :=
  ops.foldr (fun op total => phaseArithmeticOpCost workingWidth op + total) 0

/-- Width and local-cost information for one recursive policy candidate. -/
structure ProgramAnalysis where
  childWidth : Nat
  arithmeticGateCount : Nat
  arithmeticOperationCount : Nat
  recursiveCallCount : Nat
deriving Repr, DecidableEq

/-- Analyze a verified program at the supplied PhaseProduct operand widths. -/
def analyzeProgram {k : Nat}
    (xWidth zWidth : Nat) (ops : Prog k) : ProgramAnalysis :=
  let childWidth := nextSignedWidth xWidth zWidth ops
  { childWidth
    arithmeticGateCount := phaseProgramOverhead childWidth ops
    arithmeticOperationCount := TableGeneration.arithmeticOperationCount ops
    recursiveCallCount := TableGeneration.phaseProductCount ops }

/-- Planner-oriented balanced analysis using the compact array width scan. -/
def analyzeBalancedProgram {k : Nat}
    (width : Nat) (ops : Prog k) : ProgramAnalysis :=
  let childWidth := nextBalancedSignedWidth width ops
  { childWidth
    arithmeticGateCount := phaseProgramOverhead childWidth ops
    arithmeticOperationCount := TableGeneration.arithmeticOperationCount ops
    recursiveCallCount := TableGeneration.phaseProductCount ops }

@[simp] theorem analyzeProgram_recursiveCallCount {k : Nat}
    (xWidth zWidth : Nat) (ops : Prog k) :
    (analyzeProgram xWidth zWidth ops).recursiveCallCount =
      TableGeneration.phaseProductCount ops := by
  rfl

@[simp] theorem analyzeProgram_arithmeticOperationCount {k : Nat}
    (xWidth zWidth : Nat) (ops : Prog k) :
    (analyzeProgram xWidth zWidth ops).arithmeticOperationCount =
      TableGeneration.arithmeticOperationCount ops := by
  rfl

theorem commonNeededWidth_pos {k : Nat} (needed : NeededWidths k) :
    0 < commonNeededWidth needed := by
  simpa [commonNeededWidth, Nat.add_comm] using
    (Nat.zero_lt_succ (maximumNeededWidth needed))

theorem nextSignedWidth_pos {k : Nat}
    (xWidth zWidth : Nat) (ops : Prog k) :
    0 < nextSignedWidth xWidth zWidth ops :=
  commonNeededWidth_pos _

end TableGeneration.RecursiveCost
