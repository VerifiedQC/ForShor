import Mathlib.Analysis.SpecialFunctions.Log.Base
import Source.Baseline
import Source.RecursivePlanner
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.LinearAlgebra.Lagrange
import Source.Model
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Core definitions of the exact model

Collects the core definitions used by the later model files: the width scanner (`Scanner.Op`, `Scanner.scan`), the verified C11 table (`C11.word`), the planner profile (`Planner.Profile`, `Planner.planCost`), the full instruction language with row-based interpretation, and the bridge from the source-level language to these models.
-/

namespace Paper.Scanner

/-- The width-relevant instructions of the existing balanced-width scanner. The
sign of an addition and the marker payload are irrelevant to width updates. -/
inductive Op (k : Nat) where
  | shiftL (row : Fin k) (amount : Nat)
  | shiftR (row : Fin k) (amount : Nat)
  | negate (row : Fin k)
  | addScaled (destination source : Fin k) (shift : Nat)
  | marker

abbrev Widths (k : Nat) := Fin k → Nat

/-- One literal natural-width scanner transition. -/
def step {k : Nat} (op : Op k) (w : Widths k) : Widths k :=
  match op with
  | .shiftL i n => Function.update w i (w i + n)
  | .shiftR i n => Function.update w i (w i - n)
  | .negate i => Function.update w i (w i + 1)
  | .addScaled d s n => Function.update w d (1 + max (w d) (w s + n))
  | .marker => w

/-- The current maximum across all rows, including the zero-row case. -/
def maximum {k : Nat} (w : Widths k) : Nat := Finset.univ.sup w

structure State (k : Nat) where
  widths : Widths k
  peak : Nat

/-- The previous peak is retained after every instruction. -/
def advance {k : Nat} (op : Op k) (s : State k) : State k :=
  let next := step op s.widths
  ⟨next, max s.peak (maximum next)⟩

/-- Complete finite-word scanner, with arbitrary incoming history. -/
def scan {k : Nat} : List (Op k) → State k → State k
  | [], s => s
  | op :: rest, s => scan rest (advance op s)

/-- Fresh initial history includes the initial widths. -/
def fresh {k : Nat} (w : Widths k) : State k := ⟨w, maximum w⟩

def joinWidths {k : Nat} (u v : Widths k) : Widths k := fun i => max (u i) (v i)

def joinState {k : Nat} (s t : State k) : State k :=
  ⟨joinWidths s.widths t.widths, max s.peak t.peak⟩

def LE {k : Nat} (s t : State k) : Prop :=
  s.peak ≤ t.peak ∧ ∀ i, s.widths i ≤ t.widths i

/-- Top-heavy input widths for quotient `L` and remainder `r`. -/
def balanced {k : Nat} (top : Fin k) (L r : Nat) : Widths k :=
  fun i => L + if i = top then r else 0

/-- Current widths alone; the historical peak has no effect on later widths. -/
def runWidths {k : Nat} : List (Op k) → Widths k → Widths k
  | [], w => w
  | op :: rest, w => runWidths rest (step op w)

/-- Precisely the guard needed to replace natural subtraction by ordinary
subtraction at every right-shift step of this particular run. -/
def stepNoUnderflow {k : Nat} (op : Op k) (w : Widths k) : Prop :=
  match op with
  | .shiftR i n => n ≤ w i
  | _ => True

def noUnderflow {k : Nat} : List (Op k) → Widths k → Prop
  | [], _ => True
  | op :: rest, w =>
      stepNoUnderflow op w ∧ noUnderflow rest (step op w)

def translate {k : Nat} (w : Widths k) (L : Nat) : Widths k := fun i => w i + L

end Paper.Scanner



namespace Paper.C11

abbrev Index := Fin 3
abbrev Row := Index → Int
abbrev Matrix := Index → Row
abbrev Widths := Index → Nat

inductive Target where
  | zero | infinity | plusOne | minusOne | minusHalf
deriving DecidableEq, Repr

-- Repository F.2 normalization at k = 3: int z has coefficients z^j;
-- frac m has coefficients m^(2-j), including frac (-2) = (4,-2,1).
def targetRow : Target → Row
  | .zero => fun j => if j.val = 0 then 1 else 0
  | .infinity => fun j => if j.val = 2 then 1 else 0
  | .plusOne => fun _ => 1
  | .minusOne => fun j => if j.val = 1 then -1 else 1
  | .minusHalf => fun j =>
      if j.val = 0 then 4 else if j.val = 1 then -2 else 1

def identity : Matrix := fun i j => if i = j then 1 else 0

def rowMatches (row : Row) (p : Target) : Bool :=
  (List.finRange 3).all (fun j => decide (row j = targetRow p j))

inductive Instruction where
  | add (destination source : Index) (negative : Bool) (shift : Nat)
  | negate (destination : Index)
  | mark (row : Index) (target : Target)
deriving DecidableEq, Repr

structure State where
  rows : Matrix
  widths0 : Widths
  widths2 : Widths
  peak0 : Nat
  peak2 : Nat
  charge : Nat
  acquired : List Target

def updateRow (rows : Matrix) (destination : Index) (row : Row) : Matrix :=
  fun i => if i = destination then row else rows i

def updateWidth (widths : Widths) (destination : Index) (width : Nat) : Widths :=
  fun i => if i = destination then width else widths i

-- A faithful sublanguage of the full table DSL. This word needs no standalone shifts.
-- Option.none means a malformed addition or an incorrect/repeated marker.
def step (s : State) : Instruction → Option State
  | .add destination source negative shift =>
      if destination = source then none else
      let coefficient : Int := if negative then -((2 : Int) ^ shift) else (2 : Int) ^ shift
      let row : Row := fun j => s.rows destination j + coefficient * s.rows source j
      let next0 := 1 + max (s.widths0 destination) (s.widths0 source + shift)
      let next2 := 1 + max (s.widths2 destination) (s.widths2 source + shift)
      some { s with
        rows := updateRow s.rows destination row
        widths0 := updateWidth s.widths0 destination next0
        widths2 := updateWidth s.widths2 destination next2
        peak0 := max s.peak0 next0
        peak2 := max s.peak2 next2
        charge := s.charge + (if negative then 3 else 1) }
  | .negate destination =>
      let next0 := s.widths0 destination + 1
      let next2 := s.widths2 destination + 1
      some { s with
        rows := updateRow s.rows destination (fun j => -s.rows destination j)
        widths0 := updateWidth s.widths0 destination next0
        widths2 := updateWidth s.widths2 destination next2
        peak0 := max s.peak0 next0
        peak2 := max s.peak2 next2
        charge := s.charge + 1 }
  | .mark row target =>
      if rowMatches (s.rows row) target && !(target ∈ s.acquired) then
        some { s with acquired := s.acquired ++ [target] }
      else none

def run : List Instruction → State → Option State
  | [], s => some s
  | instruction :: rest, s =>
      (step s instruction).bind (run rest)

def initial : State where
  rows := identity
  widths0 := fun _ => 0
  widths2 := fun i => if i.val = 2 then 2 else 0
  peak0 := 0
  peak2 := 2
  charge := 0
  acquired := []

-- Two initial markers and eleven paid operations, with three markers inside.
def word : List Instruction :=
  [ .mark 0 .zero,
    .mark 2 .infinity,
    .add 2 1 false 0,
    .negate 1,
    .add 2 0 false 0,
    .mark 2 .plusOne,
    .add 2 1 false 1,
    .mark 2 .minusOne,
    .add 1 0 false 1,
    .add 0 1 false 0,
    .negate 1,
    .add 2 0 false 0,
    .mark 2 .minusHalf,
    .add 0 1 false 0,
    .add 2 1 false 1,
    .add 1 0 false 1 ]

def result : State := (run word initial).getD initial

end Paper.C11



namespace Paper.Planner

/-- A single table's charge and its two complete scanner peaks. -/
structure Profile where
  charge : Nat
  peakA : Nat
  peakB : Nat
  deriving DecidableEq, Repr

/-- The retained child-width recurrence for one arity and one shared profile. -/
def childWidth (k : Nat) (p : Profile) (w : Nat) : Nat :=
  w / k + 1 + max p.peakA (p.peakB + w % k)

/-- The width trace includes the incoming width and every subsequent width. -/
def widthTrace (tables : Nat → Profile) : List Nat → Nat → List Nat
  | [], w => [w]
  | k :: ks, w => w :: widthTrace tables ks (childWidth k (tables k) w)

/-- Final multiplicity and width after the fixed finite arity sequence. -/
def finalState (tables : Nat → Profile) : List Nat → Nat → Nat → Nat × Nat
  | [], n, w => (n, w)
  | k :: ks, n, w =>
      finalState tables ks (n * (2 * k - 1)) (childWidth k (tables k) w)

/--
Finite recursive planner objective. `terminal` is intentionally arbitrary:
profile-preserving transfer compares it at an identical terminal argument.
-/
def planCost (tables : Nat → Profile) (terminal : Nat → Nat) :
    List Nat → Nat → Nat → Nat
  | [], n, w => terminal (n * w ^ 2)
  | k :: ks, n, w =>
      let w' := childWidth k (tables k) w
      8 * n * (w' - 1) * (tables k).charge +
        planCost tables terminal ks (n * (2 * k - 1)) w'

/-- Every chosen step strictly contracts the width entering that occurrence. -/
def StrictlyContracts (tables : Nat → Profile) : List Nat → Nat → Prop
  | [], _ => True
  | k :: ks, w =>
      childWidth k (tables k) w < w ∧
        StrictlyContracts tables ks (childWidth k (tables k) w)

end Paper.Planner



namespace Paper.FullDSL

abbrev Rows (k : Nat) := Matrix (Fin k) (Fin k) Int

inductive Instruction (k : Nat) where
  | shiftL (i : Fin k) (n : Nat)
  | shiftR (i : Fin k) (n : Nat)
  | negate (i : Fin k)
  | addScaled (dst src : Fin k) (negSrc : Bool) (shift : Nat)
  | phaseProduct (i : Fin k)
deriving DecidableEq, Repr

def identity (k : Nat) : Rows k := 1

def rowStep {k : Nat} (op : Instruction k) (rows : Rows k) : Option (Rows k) :=
  match op with
  | .shiftL i n =>
      some (rows.updateRow i (fun j => rows i j * (2 : Int) ^ n))
  | .shiftR i n =>
      if h : ∀ j : Fin k, rows i j % (2 : Int) ^ n = 0 then
        some (rows.updateRow i (fun j => rows i j / (2 : Int) ^ n))
      else none
  | .negate i => some (rows.updateRow i (fun j => -rows i j))
  | .addScaled dst src negSrc shift =>
      if dst = src then none
      else
        let c : Int := (if negSrc then -1 else 1) * (2 : Int) ^ shift
        some (rows.updateRow dst (fun j => rows dst j + c * rows src j))
  | .phaseProduct _ => some rows

def runRows {k : Nat} : List (Instruction k) → Rows k → Option (Rows k)
  | [], rows => some rows
  | op :: ops, rows => (rowStep op rows).bind (runRows ops)

def widthOp {k : Nat} : Instruction k → Scanner.Op k
  | .shiftL i n => .shiftL i n
  | .shiftR i n => .shiftR i n
  | .negate i => .negate i
  | .addScaled dst src _ shift => .addScaled dst src shift
  | .phaseProduct _ => .marker

def widthWord {k : Nat} (word : List (Instruction k)) : List (Scanner.Op k) :=
  word.map widthOp

def charge {k : Nat} : Instruction k → Nat
  | .shiftL _ _ => 0
  | .shiftR _ _ => 0
  | .negate _ => 1
  | .addScaled _ _ negSrc _ => if negSrc then 3 else 1
  | .phaseProduct _ => 0

def wordCharge {k : Nat} (word : List (Instruction k)) : Nat :=
  (word.map charge).sum

end Paper.FullDSL


namespace Paper.Profile

open Paper.Scanner

/-- Pointwise clipped join: `v` is lowered by `c`, with natural saturation. -/
def combineWidths {k : Nat} (c : Nat) (u v : Widths k) : Widths k :=
  fun i => max (u i) (v i - c)

/-- The same clipped join applied to both current widths and saved peak. -/
def combineState {k : Nat} (c : Nat) (s t : State k) : State k :=
  ⟨combineWidths c s.widths t.widths, max s.peak (t.peak - c)⟩

/-- Translate both the current widths and historical peak. -/
def translateState {k : Nat} (s : State k) (L : Nat) : State k :=
  ⟨translate s.widths L, s.peak + L⟩

end Paper.Profile



namespace Paper.RowMass

/-- Column-weighted ℓ₁ mass of one integer row. -/
def weightedMass {k : Nat} (weights : Fin k → Nat) (row : Fin k → Int) : Nat :=
  ∑ j : Fin k, (row j).natAbs * 2 ^ weights j

/-- Every executed row fits the scanner's current width. -/
def Bounded {k : Nat} (weights : Fin k → Nat)
    (rows : Paper.FullDSL.Rows k) (widths : Paper.Scanner.Widths k) : Prop :=
  ∀ i, weightedMass weights (rows i) ≤ 2 ^ widths i

/-- Every integer row has at least one nonzero component. -/
def NonzeroRows {k : Nat} (rows : Paper.FullDSL.Rows k) : Prop :=
  ∀ i, ∃ j, rows i j ≠ 0

end Paper.RowMass



namespace Paper.FullDSL

def fromC11 : C11.Instruction → Instruction 3
  | .add d s neg shift => .addScaled d s neg shift
  | .negate d => .negate d
  | .mark row _ => .phaseProduct row

def c11Word : List (Instruction 3) := C11.word.map fromC11

def c11Profile : Planner.Profile :=
  ⟨11, 6, 5⟩

end Paper.FullDSL


namespace Paper.SourceBridge

/-- Constructor-for-constructor translation of the protected table language. -/
def toFull {k : Nat} : TableGeneration.Operations.valid_ops k → FullDSL.Instruction k
  | .shiftL i n => .shiftL i n
  | .shiftR i n => .shiftR i n
  | .negate i => .negate i
  | .addScaled d s neg n => .addScaled d s neg n
  | .phaseProduct i => .phaseProduct i

def toOriginal {k : Nat} : FullDSL.Instruction k → TableGeneration.Operations.valid_ops k
  | .shiftL i n => .shiftL i n
  | .shiftR i n => .shiftR i n
  | .negate i => .negate i
  | .addScaled d s neg n => .addScaled d s neg n
  | .phaseProduct i => .phaseProduct i

def mapToFull {k : Nat} (ops : TableGeneration.Prog k) : List (FullDSL.Instruction k) :=
  ops.map toFull

def mapToOriginal {k : Nat} (ops : List (FullDSL.Instruction k)) : TableGeneration.Prog k :=
  ops.map toOriginal

def originalC11Word : TableGeneration.Prog 3 := mapToOriginal FullDSL.c11Word

def sourceProfile {k : Nat} (top : Fin k) (ops : TableGeneration.Prog k) :
    Planner.Profile :=
  let word := mapToFull ops
  ⟨FullDSL.wordCharge word,
    (Scanner.scan (FullDSL.widthWord word)
      (Scanner.fresh (Scanner.balanced top 0 0))).peak,
    (Scanner.scan (FullDSL.widthWord word)
      (Scanner.fresh (Scanner.balanced top 0 (k - 1)))).peak - (k - 1)⟩

end Paper.SourceBridge


namespace Paper.ArrayBridge

/-- The exact top-heavy balanced split supplied to the original array scan. -/
def literalSourceSplit (width k : Nat) : Scanner.Widths k :=
  fun i => TableGeneration.RecursiveCost.phaseSplitLogicalWidth width
    (TableGeneration.RecursiveCost.phaseLimbWidth width width k) k i

/-- Interpret the original width-relevant instruction in the Paper scanner. -/
def toScanner {k : Nat} : TableGeneration.Operations.valid_ops k → Scanner.Op k
  | .shiftL i n => .shiftL i n
  | .shiftR i n => .shiftR i n
  | .negate i => .negate i
  | .addScaled dst src _ shift => .addScaled dst src shift
  | .phaseProduct _ => .marker

/-- Read every valid array entry through the original safe lookup. -/
def widthView {k : Nat} (a : Array Nat) : Scanner.Widths k :=
  fun i => TableGeneration.RecursiveCost.balancedWidthAt a i

end Paper.ArrayBridge


namespace Paper.SourceBridge

/-- Independently execute arithmetic rows and record the actual row seen at
each phase marker, in marker order. An illegal arithmetic step returns none. -/
def markerTrace {k : Nat} :
    List (FullDSL.Instruction k) → FullDSL.Rows k →
      Option (FullDSL.Rows k × List (Fin k → Int))
  | [], rows => some (rows, [])
  | op :: rest, rows =>
      match op with
      | .phaseProduct i => do
          let (final, marks) ← markerTrace rest rows
          pure (final, rows i :: marks)
      | _ => do
          let next ← FullDSL.rowStep op rows
          markerTrace rest next

/-- The five protected source points in the certified C11 marker order. -/
def c11Points : List TableGeneration.Operations.Point :=
  [.int 0, .frac 0, .int 1, .int (-1), .frac (-2)]

end Paper.SourceBridge


namespace Paper.CostBridge

/-- Operation counts in the independent full-language model. -/
structure Counts where
  shiftL : Nat
  shiftR : Nat
  negate : Nat
  plusAdd : Nat
  minusAdd : Nat
  markers : Nat
deriving Repr, DecidableEq

def wordCounts {k : Nat} : List (FullDSL.Instruction k) → Counts
  | [] => ⟨0, 0, 0, 0, 0, 0⟩
  | op :: rest =>
      let c := wordCounts rest
      match op with
      | .shiftL _ _ => { c with shiftL := c.shiftL + 1 }
      | .shiftR _ _ => { c with shiftR := c.shiftR + 1 }
      | .negate _ => { c with negate := c.negate + 1 }
      | .addScaled _ _ false _ => { c with plusAdd := c.plusAdd + 1 }
      | .addScaled _ _ true _ => { c with minusAdd := c.minusAdd + 1 }
      | .phaseProduct _ => { c with markers := c.markers + 1 }

/-- Count maximal contiguous marker layers in the independent full language. -/
def markerLayerCountAux {k : Nat} : Bool → List (FullDSL.Instruction k) → Nat
  | _, [] => 0
  | inLayer, op :: rest =>
      match op with
      | .phaseProduct _ =>
          (if inLayer then 0 else 1) + markerLayerCountAux true rest
      | _ => markerLayerCountAux false rest

def markerLayerCount {k : Nat} (word : List (FullDSL.Instruction k)) : Nat :=
  markerLayerCountAux false word

/-- Full-language balanced analysis expressed through the independent scanner
and constructor counts. The gate bound remains the source's conservative bound. -/
def balancedAnalysis {k : Nat} (width : Nat)
    (word : List (FullDSL.Instruction k)) :
    TableGeneration.RecursiveCost.ProgramAnalysis :=
  let child := 1 + (Scanner.scan (FullDSL.widthWord word)
    (Scanner.fresh (ArrayBridge.literalSourceSplit width k))).peak
  let c := wordCounts word
  { childWidth := child
    arithmeticGateCount :=
      2 * TableGeneration.RecursiveCost.rippleAdderGateBound child *
        (c.plusAdd + c.minusAdd) +
      2 * TableGeneration.RecursiveCost.negateGateBound child * c.negate
    arithmeticOperationCount :=
      c.shiftL + c.shiftR + c.negate + c.plusAdd + c.minusAdd
    recursiveCallCount := c.markers }

end Paper.CostBridge


namespace Paper.ValueSemantics

abbrev Values (k : Nat) := Fin k → Int

def evalRow {k : Nat} (row : Fin k → Int) (x : Values k) : Int :=
  ∑ j : Fin k, row j * x j

def evalRows {k : Nat} (rows : FullDSL.Rows k) (x : Values k) : Values k :=
  fun i => evalRow (rows i) x

/-- Exact integer operations, checked on the register values themselves. -/
def valueStep {k : Nat} (op : FullDSL.Instruction k) (v : Values k) : Option (Values k) :=
  match op with
  | .shiftL i n => some (Function.update v i (v i * (2 : Int) ^ n))
  | .shiftR i n =>
      if v i % (2 : Int) ^ n = 0 then
        some (Function.update v i (v i / (2 : Int) ^ n))
      else none
  | .negate i => some (Function.update v i (-v i))
  | .addScaled dst src negSrc shift =>
      if dst = src then none
      else some (Function.update v dst
        (v dst + (if negSrc then -1 else 1) * (2 : Int) ^ shift * v src))
  | .phaseProduct _ => some v

/-- Execute on concrete integers and record exactly the marked values. -/
def valueTrace {k : Nat} : List (FullDSL.Instruction k) → Values k →
    Option (Values k × List Int)
  | [], v => some (v, [])
  | .phaseProduct i :: ops, v =>
      (valueTrace ops v).map (fun r => (r.1, v i :: r.2))
  | op :: ops, v => (valueStep op v).bind (valueTrace ops)

end Paper.ValueSemantics


namespace Paper.PhaseIdentity

def linearForm {k : Nat} (row x : Fin k → ℚ) : ℚ := ∑ j, row j * x j

/-- Finite coefficient identities sufficient and necessary for PP decomposition. -/
def PairCertificate {k q : Nat} (weight : Fin q → ℚ)
    (row : Fin q → Fin k → ℚ) (base : Fin k → ℚ) : Prop :=
  ∀ i j, (∑ l, weight l * row l i * row l j) = base i * base j

/-- Finite coefficient identities sufficient and necessary for PTP decomposition. -/
def TripleCertificate {k q : Nat} (weight : Fin q → ℚ)
    (row : Fin q → Fin k → ℚ) (base : Fin k → ℚ) : Prop :=
  ∀ i j t, (∑ l, weight l * row l i * row l j * row l t) =
    base i * base j * base t

/-- The normalized five target rows of the verified C11 table, in marker order. -/
def c11Rows : Fin 5 → Fin 3 → ℚ :=
  ![![1, 0, 0], ![0, 0, 1], ![1, 1, 1], ![1, -1, 1], ![4, -2, 1]]

/-- Interpolation weights for the scaled reciprocal row `(4,-2,1)`. -/
def c11Weights (b : ℚ) : Fin 5 → ℚ :=
  ![1 - b^2 - 2*b^3 + 2*b,
    b^4 - b^2 + (b^3-b)/2,
    b^2/2 + b^3/3 + b/6,
    b^2/2 - b^3 + b/2,
    (b^3-b)/6]

def c11Base (b : ℚ) : Fin 3 → ℚ := ![1, b, b^2]

/-- Four evaluations suffice for a product of three degree-one polynomials. -/
def ptp2Rows : Fin 4 → Fin 2 → ℚ := ![![1, 0], ![0, 1], ![1, 1], ![1, -1]]

def ptp2Weights (b : ℚ) : Fin 4 → ℚ := ![1-b^2, b^3-b, (b+b^2)/2, (b^2-b)/2]

def ptp2Base (b : ℚ) : Fin 2 → ℚ := ![1, b]

def ptp2Points : List TableGeneration.Operations.Point :=
  [.int 0, .frac 0, .int 1, .int (-1)]

/-- Reversible row program visiting the four degree-three interpolation points. -/
def ptp2Word : TableGeneration.Prog 2 :=
  [.phaseProduct 0, .phaseProduct 1,
   .addScaled 0 1 false 0, .phaseProduct 0,
   .addScaled 0 1 true 1, .phaseProduct 0,
   .addScaled 0 1 false 0]

def observations {k : Nat} (pts : List TableGeneration.Operations.Point)
    (x : ValueSemantics.Values k) : List Int :=
  pts.map (fun p => ValueSemantics.evalRow (TableGeneration.expectedRow p) x)

end Paper.PhaseIdentity


namespace Paper.GenericPhase

/-- Protected source target rows indexed by the supplied finite marker family. -/
def indexedSourceRows {k q : Nat}
    (pts : Fin q → TableGeneration.Operations.Point) :
    Fin q → Fin k → ℚ :=
  fun l j => (TableGeneration.expectedRow (k := k) (pts l) j : ℚ)

end Paper.GenericPhase


namespace Paper.Interpolation

noncomputable def finiteWeight {d : Nat} (v : Fin d → ℚ) (b : ℚ) (i : Fin d) : ℚ :=
  Polynomial.eval b (Lagrange.basis Finset.univ v i)

noncomputable def infinityWeight {d : Nat} (v : Fin d → ℚ) (b : ℚ) : ℚ :=
  b ^ d - ∑ i, finiteWeight v b i * v i ^ d

end Paper.Interpolation


namespace Paper.Normalization

def sourcePoint : TableGeneration.Operations.Point → Option ℚ
  | .int z => some (z : ℚ)
  | .frac m => if m = 0 then none else some ((m : ℚ)⁻¹)

def sourceScale (k : Nat) : TableGeneration.Operations.Point → ℚ
  | .int _ => 1
  | .frac m => if m = 0 then 1 else (m : ℚ) ^ (k - 1)

/-- At infinity, an observation is the coefficient of the supplied degree. -/
def projectiveMonomial (degree : Nat) (pt : Option ℚ) (exponent : Nat) : ℚ :=
  match pt with
  | some z => z ^ exponent
  | none => if exponent = degree then 1 else 0

def MomentCertificate {q : Nat} (degree : Nat) (pt : Fin q → Option ℚ)
    (weight : Fin q → ℚ) (b : ℚ) : Prop :=
  ∀ m, m ≤ degree → (∑ l, weight l * projectiveMonomial degree (pt l) m) = b ^ m

def normalizedWeights {q : Nat} (k power : Nat)
    (pts : Fin q → TableGeneration.Operations.Point) (weight : Fin q → ℚ) : Fin q → ℚ :=
  fun l => weight l / sourceScale k (pts l) ^ power

end Paper.Normalization


namespace Paper.GeneralConstruction

noncomputable def projectiveWeights {d : Nat} (v : Fin d → ℚ) (b : ℚ) : Fin (d+1) → ℚ :=
  Fin.lastCases (Interpolation.infinityWeight v b) (Interpolation.finiteWeight v b)

/-- The equivalence sends interpolation order (infinity last) to source marker order. -/
noncomputable def phaseWeights {d : Nat} (k power : Nat)
    (pts : Fin (d+1) → TableGeneration.Operations.Point) (v : Fin d → ℚ) (b : ℚ)
    (order : Fin (d+1) ≃ Fin (d+1)) : Fin (d+1) → ℚ :=
  Normalization.normalizedWeights k power pts (fun l => projectiveWeights v b (order.symm l))

end Paper.GeneralConstruction

namespace Paper.PlannerOptimality

open TableGeneration.RecursiveCost

/-- Modeled gate costs of uniform recursive policy chains drawn from `candidates`. -/
inductive LegalCost (candidates : List Candidate) : Nat → Nat → Prop where
  | base (width : Nat) : LegalCost candidates width (width * width)
  | step (width : Nat) (candidate : Candidate)
      (hmem : candidate ∈ candidates)
      (hcontract : (candidate.analyze width).childWidth < width)
      (childCost : Nat)
      (hchild : LegalCost candidates (candidate.analyze width).childWidth childCost) :
      LegalCost candidates width
        ((candidate.analyze width).arithmeticGateCount +
          (candidate.analyze width).recursiveCallCount * childCost)

end Paper.PlannerOptimality

namespace Paper.ValueBounds

/-- A value lies strictly inside the magnitude cap assigned to each register. -/
def Fits {k : Nat} (w : Paper.Scanner.Widths k)
    (v : Paper.ValueSemantics.Values k) : Prop :=
  ∀ i, Int.natAbs (v i) < 2 ^ (w i)

end Paper.ValueBounds

namespace Paper.ValuePhase

/-- Real phase angle obtained by scaling a rational exponent. -/
def phaseAngle (theta : ℝ) (q : ℚ) : ℝ := theta * (q : ℝ)

/-- Unit-circle character for a rational exponent at arbitrary real scale. -/
noncomputable def phaseCharacter (theta : ℝ) (q : ℚ) : ℂ :=
  Complex.exp ((phaseAngle theta q : ℂ) * Complex.I)

/-- Unbounded pair-input basis labels for the value semantics. -/
abbrev PairBasis (k : Nat) := ValueSemantics.Values k × ValueSemantics.Values k

/-- Unbounded triple-input basis labels for the value semantics. -/
abbrev TripleBasis (k : Nat) :=
  ValueSemantics.Values k × ValueSemantics.Values k × ValueSemantics.Values k

/-- Complex amplitudes over an explicitly chosen basis index type. -/
abbrev Amplitude (Basis : Type) := Basis → ℂ

/-- Pointwise action of a diagonal phase function on an amplitude function. -/
def diagonalApply {Basis : Type} (phase : Basis → ℂ)
    (amplitude : Amplitude Basis) : Amplitude Basis :=
  fun b => phase b * amplitude b

end Paper.ValuePhase
namespace Paper.BitStep

abbrev Regs (k B : Nat) := Fin k → BitVec B

def encode {k B : Nat} (v : Paper.ValueSemantics.Values k) : Regs k B :=
  fun i => BitVec.ofInt B (v i)

def decode {k B : Nat} (r : Regs k B) : Paper.ValueSemantics.Values k :=
  fun i => (r i).toInt

/-- The unbounded interpreter's one-step marker payload, sampled before update. -/
def markerValues {k : Nat} (op : Paper.FullDSL.Instruction k)
    (v : Paper.ValueSemantics.Values k) : List Int :=
  match op with
  | .phaseProduct i => [v i]
  | _ => []

/-- Literal fixed-width execution: arithmetic operates on BitVec registers.
The right-shift guard inspects the signed decoded register value, as in
ValueSemantics.valueStep. -/
def bitStep {k B : Nat} (op : Paper.FullDSL.Instruction k) (r : Regs k B) :
    Option (Regs k B × List (BitVec B)) :=
  match op with
  | .shiftL i n => some (Function.update r i (r i <<< n), [])
  | .shiftR i n =>
      if (r i).toInt % (2 : Int) ^ n = 0 then
        some (Function.update r i ((r i).sshiftRight n), [])
      else none
  | .negate i => some (Function.update r i (-r i), [])
  | .addScaled dst src negSrc shift =>
      if dst = src then none
      else some (Function.update r dst
        (r dst + ((if negSrc then -r src else r src) <<< shift)), [])
  | .phaseProduct i => some (r, [r i])

end Paper.BitStep

namespace Paper.BitStep

/-- Fixed-width execution through the actual BitVec step, preserving the order
of native BitVec marker payloads. -/
def bitTrace {k B : Nat} : List (Paper.FullDSL.Instruction k) → Regs k B →
    Option (Regs k B × List (BitVec B))
  | [], r => some (r, [])
  | op :: rest, r =>
      (bitStep op r).bind (fun step =>
        (bitTrace rest step.1).map (fun tail =>
          (tail.1, step.2 ++ tail.2)))

end Paper.BitStep

namespace Paper.RawInterpreter

/-- Source-compatible row semantics, including aliased additions. -/
def rowStep {k : Nat} (op : FullDSL.Instruction k)
    (rows : FullDSL.Rows k) : Option (FullDSL.Rows k) :=
  match op with
  | .shiftL i n =>
      some (rows.updateRow i (fun j => rows i j * (2 : Int) ^ n))
  | .shiftR i n =>
      if ∀ j : Fin k, rows i j % (2 : Int) ^ n = 0 then
        some (rows.updateRow i (fun j => rows i j / (2 : Int) ^ n))
      else none
  | .negate i => some (rows.updateRow i (fun j => -rows i j))
  | .addScaled dst src negSrc shift =>
      let c : Int := (if negSrc then -1 else 1) * (2 : Int) ^ shift
      some (rows.updateRow dst (fun j => rows dst j + c * rows src j))
  | .phaseProduct _ => some rows

def runRows {k : Nat} :
    List (FullDSL.Instruction k) → FullDSL.Rows k → Option (FullDSL.Rows k)
  | [], rows => some rows
  | op :: ops, rows => (rowStep op rows).bind (runRows ops)

end Paper.RawInterpreter


namespace Paper.SignedLimbs

def radix (W k : Nat) : Nat := 2 ^ (W / k)

def magLimb (W k m : Nat) (i : Fin k) : Nat :=
  let B := radix W k
  if i.val + 1 = k then m / B ^ i.val else (m / B ^ i.val) % B

def limbs (W : Nat) {k : Nat} (_hk : 0 < k) (n : Int) (i : Fin k) : Int :=
  (if n < 0 then -1 else 1) * (magLimb W k n.natAbs i : Int)

end Paper.SignedLimbs

namespace Coupled.Formal

structure Prob (ι : Type) where
  child : ι → ℕ → ℕ
  own : ι → ℕ → ℕ → ℕ
  calls : ι → ℕ
  leaf : ℕ → ℕ → ℕ

inductive CostL {ι : Type} (P : Prob ι) : List ι → ℕ → ℕ → ℕ → Prop
  | base (w N : ℕ) : CostL P [] w N (P.leaf N w)
  | step (c : ι) (l : List ι) (w N v : ℕ) : P.child c w < w → CostL P l (P.child c w) (N * P.calls c) v →
      CostL P (c :: l) w N (N * P.own c w (P.child c w) + v)

def ArityInj {ι : Type} (arity : ι → ℕ) (l : List ι) : Prop := ∀ c ∈ l, ∀ d ∈ l, arity c = arity d → c = d

end Coupled.Formal

namespace Paper.PolicyOptimality

open Coupled.Formal

variable {ι : Type}

/-- Every list of exactly `length` entries from a supplied finite catalog. -/
def listsOfLength : Nat → List ι → List (List ι)
  | 0, _ => [[]]
  | n + 1, catalog =>
      catalog.flatMap (fun c => (listsOfLength n catalog).map (c :: ·))

/-- Exactly the supplied candidate entries whose arity lies between two and `K`. -/
def cappedCatalog (catalog : List ι) (arity : ι → Nat) (K : Nat) : List ι :=
  catalog.filter (fun c => decide (2 ≤ arity c ∧ arity c ≤ K))

/-- A finite decidable check for one shared candidate per arity. -/
def sharedB [DecidableEq ι] (arity : ι → Nat) (l : List ι) : Bool :=
  l.all (fun c => l.all (fun d => decide (arity c ≠ arity d ∨ c = d)))

/-- Evaluate the exact coupled cost of one displayed trace, rejecting noncontracting steps. -/
def traceCost? (P : Prob ι) : List ι → Nat → Nat → Option Nat
  | [], w, N => some (P.leaf N w)
  | c :: rest, w, N =>
      if P.child c w < w then
        (traceCost? P rest (P.child c w) (N * P.calls c)).map
          (fun v => N * P.own c w (P.child c w) + v)
      else none

/-- All traces short enough for strict width descent from `width`. -/
def finiteTraces (catalog : List ι) (arity : ι → Nat) (K width : Nat) : List (List ι) :=
  (List.range (width + 1)).flatMap
    (fun n => listsOfLength n (cappedCatalog catalog arity K))

/-- Explicit scored finite traces satisfying the shared-arity rule. -/
def scoredTraces [DecidableEq ι] (P : Prob ι) (catalog : List ι)
    (arity : ι → Nat) (K width N : Nat) : List (List ι × Nat) :=
  (finiteTraces catalog arity K width).filterMap fun l =>
    if sharedB arity l then
      (traceCost? P l width N).map (fun v => (l, v))
    else none

/-- Stable tie rule: keep the earlier trace when costs are equal. -/
def lowerCost (current candidate : List ι × Nat) : List ι × Nat :=
  if candidate.2 < current.2 then candidate else current

/-- The selected concrete ladder and exact mathematical coupled cost. -/
def select [DecidableEq ι] (P : Prob ι) (catalog : List ι)
    (arity : ι → Nat) (K width N : Nat) : List ι × Nat :=
  (scoredTraces P catalog arity K width N).foldl lowerCost ([], P.leaf N width)

def chosenTrace [DecidableEq ι] (P : Prob ι) (catalog : List ι)
    (arity : ι → Nat) (K width N : Nat) : List ι :=
  (select P catalog arity K width N).1

def chosenCost [DecidableEq ι] (P : Prob ι) (catalog : List ι)
    (arity : ι → Nat) (K width N : Nat) : Nat :=
  (select P catalog arity K width N).2

/-- Explicit per-arity lookup of the selected shared policy. -/
def chosenAtArity [DecidableEq ι] (P : Prob ι) (catalog : List ι)
    (arity : ι → Nat) (K width N a : Nat) : Option ι :=
  (chosenTrace P catalog arity K width N).find? (fun c => arity c == a)

/-- A finite table of the selected program index at each used arity. -/
def chosenTable [DecidableEq ι] (P : Prob ι) (catalog : List ι)
    (arity : ι → Nat) (K width N : Nat) : List (Nat × ι) :=
  (List.range (K + 1)).filterMap fun a =>
    (chosenAtArity P catalog arity K width N a).map (fun c => (a, c))

end Paper.PolicyOptimality


namespace Paper.PPEndToEnd

/-- A single source candidate reusable at every width. Its exact ordered
source points, safe restoration contract and interpolation weights are
certified for every radix `2^(W/k)`. The policy optimizer may share this same
element at repeated occurrences of its arity. -/
structure VerifiedPPCandidate (K : Nat) where
  source : TableGeneration.RecursiveCost.Candidate
  cap : source.k ≤ K
  points : Fin (2 * (source.k - 1) + 1) → TableGeneration.Operations.Point
  safe : TableGeneration.ProgConsumesPtsSafe
    (TableGeneration.positive_of_ge_two source.hk)
    TableGeneration.State.start_state source.program (List.ofFn points)
  weights : (W : Nat) → Fin (2 * (source.k - 1) + 1) → ℚ
  certificate : ∀ W, Paper.PhaseIdentity.PairCertificate (weights W)
    (Paper.GenericPhase.indexedSourceRows (k := source.k) points)
    (fun j : Fin source.k => (Paper.SignedLimbs.radix W source.k : ℚ) ^ j.val)

namespace VerifiedPPCandidate

def arity {K : Nat} (t : VerifiedPPCandidate K) : Nat := t.source.k

def calls {K : Nat} (t : VerifiedPPCandidate K) : Nat :=
  2 * (t.source.k - 1) + 1

def childWidth {K : Nat} (t : VerifiedPPCandidate K) (W : Nat) : Nat :=
  TableGeneration.RecursiveCost.nextBalancedSignedWidth W t.source.program

end VerifiedPPCandidate

/-- A finite explicit recursion ladder. Every node uses its source-verified
table and a child at the actual signed scanner width. -/
inductive PPPolicy (K : Nat) : Nat → Type
  | leaf (W : Nat) : PPPolicy K W
  | node {W : Nat} (table : VerifiedPPCandidate K)
      (contracting : table.childWidth W < W)
      (child : PPPolicy K (table.childWidth W)) : PPPolicy K W

/-- The leaf implementation is supplied separately; the parent lane proves
that its schoolbook bit-pair rotations satisfy the PP phase contract. -/
abbrev LeafAction := (W : Nat) → ℝ → Int → Int → Option ℂ

def optionProduct : List (Option ℂ) → Option ℂ
  | [] => some 1
  | p :: rest => do
      let z ← p
      let tail ← optionProduct rest
      pure (z * tail)

/-- Native table execution followed by actual recursive calls on decoded
marker pairs, with the interpolation angle scale applied to each child. -/
noncomputable def nodeEval {K : Nat} (W : Nat) (table : VerifiedPPCandidate K)
    (childEval : ℝ → Int → Int → Option ℂ)
    (theta : ℝ) (a c : Int) : Option ℂ := by
  classical
  let hpos : 0 < table.source.k :=
    TableGeneration.positive_of_ge_two table.source.hk
  let x := Paper.SignedLimbs.limbs W hpos a
  let z := Paper.SignedLimbs.limbs W hpos c
  let B := table.childWidth W
  let word := Paper.SourceBridge.mapToFull table.source.program
  match Paper.BitStep.bitTrace word (Paper.BitStep.encode (B := B) x),
      Paper.BitStep.bitTrace word (Paper.BitStep.encode (B := B) z) with
  | some (rx, mx), some (rz, mz) =>
      if rx = Paper.BitStep.encode (B := B) x ∧
          rz = Paper.BitStep.encode (B := B) z then
        exact optionProduct ((List.finRange table.calls).map (fun l =>
          childEval (theta * (table.weights W l : ℝ))
            ((mx.map BitVec.toInt).getD l.val 0)
            ((mz.map BitVec.toInt).getD l.val 0)))
      else exact none
  | _, _ => exact none

noncomputable def PPPolicy.eval {K W : Nat} (leafAction : LeafAction)
    (policy : PPPolicy K W) : ℝ → Int → Int → Option ℂ :=
  match policy with
  | .leaf W => leafAction W
  | .node table _ child => nodeEval W table (PPPolicy.eval leafAction child)

end Paper.PPEndToEnd

namespace Paper.PPEndToEnd


def signedDigits : (W : Nat) → BitVec W → List ℚ
  | 0, _ => []
  | w + 1, x =>
      if w = 0 then [-(x.getLsb 0).toInt]
      else ((x.getLsb 0).toInt : ℚ) ::
        (signedDigits w (x.extractLsb' 1 w)).map (fun q => 2*q)

def schoolbookCells {W : Nat} (a c : BitVec W) : List ℚ :=
  (signedDigits W a).flatMap (fun x => (signedDigits W c).map (fun z => x*z))

noncomputable def schoolbookPhase {W : Nat} (theta : ℝ) (a c : BitVec W) : ℂ :=
  ((schoolbookCells a c).map (Paper.ValuePhase.phaseCharacter theta)).prod

noncomputable def schoolbookLeaf (W : Nat) (theta : ℝ) (a c : Int) : Option ℂ :=
  if (BitVec.ofInt W a).toInt = a ∧ (BitVec.ofInt W c).toInt = c then
    some (schoolbookPhase theta (BitVec.ofInt W a) (BitVec.ofInt W c))
  else none


end Paper.PPEndToEnd

namespace Paper.PPEndToEnd

/-- The locally stipulated PP benchmark price, identical to packet17 tauRS. -/
noncomputable def tauRS (R : Nat) : Nat :=
  (round ((3.075 : ℝ) * Real.logb 2 ((R : ℝ) / (1 / 100)) + 0.86)).toNat

def chargedOp {k : Nat} : TableGeneration.Operations.valid_ops k → Nat
  | .addScaled _ _ neg _ => if neg then 3 else 1
  | .negate _ => 1
  | _ => 0

def chargedCount {k : Nat} (ops : TableGeneration.Prog k) : Nat :=
  (ops.map chargedOp).sum

def ownPP (charge width : Nat) : Nat := 4 * (2 * (width - 1) * charge)

def leafPP (price : Nat → Nat) (N W : Nat) : Nat :=
  4 * (N * W^2) + (N * W^2) * price (N * W^2)

def PPPolicy.adderAnds {K W : Nat} (policy : PPPolicy K W) (N : Nat) : Nat :=
  match policy with
  | .leaf _ => 0
  | .node table _ child =>
      N * (2 * (table.childWidth W - 1) * chargedCount table.source.program) +
      child.adderAnds (N * table.calls)

def PPPolicy.leafRotations {K W : Nat} (policy : PPPolicy K W) (N : Nat) : Nat :=
  match policy with
  | .leaf W => N * W^2
  | .node table _ child => child.leafRotations (N * table.calls)

/-- Exact PP benchmark recurrence; price is evaluated once at the total leaf
rotation count, because multiplicity N propagates to the common leaf level. -/
def PPPolicy.benchmarkCost {K W : Nat} (price : Nat → Nat)
    (policy : PPPolicy K W) (N : Nat) : Nat :=
  match policy with
  | .leaf W => leafPP price N W
  | .node table _ child =>
      N * ownPP (chargedCount table.source.program) (table.childWidth W) +
      child.benchmarkCost price (N * table.calls)

def ppProblem {K : Nat} {ι : Type} (price : Nat → Nat)
    (entry : ι → VerifiedPPCandidate K) : Coupled.Formal.Prob ι where
  child := fun c => (entry c).childWidth
  own := fun c _ W => ownPP (chargedCount (entry c).source.program) W
  calls := fun c => (entry c).calls
  leaf := leafPP price

/-- Constructs the actual recursive policy, rejecting any noncontracting level. -/
def policyFromTrace {K : Nat} {ι : Type} (entry : ι → VerifiedPPCandidate K) :
    (l : List ι) → (W : Nat) → Option (PPPolicy K W)
  | [], W => some (.leaf W)
  | c :: rest, W =>
      if h : (entry c).childWidth W < W then
        (policyFromTrace entry rest ((entry c).childWidth W)).map
          (fun child => .node (entry c) h child)
      else none

end Paper.PPEndToEnd
