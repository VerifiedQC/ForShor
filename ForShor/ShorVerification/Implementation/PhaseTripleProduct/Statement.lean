import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecialFunctions.Log.Base
import ForShor.ShorVerification.Framework.AbstractMachine.Gates
import ForShor.ShorVerification.Framework.AbstractMachine.LowGate
import ForShor.ShorVerification.Framework.Quantum.QSemantics
import ForShor.ShorVerification.Framework.Quantum.Registers
import ForShor.ShorVerification.Framework.Semantics.GateSemantics
import ForShor.ShorVerification.Framework.Semantics.LowGateSemantics
import ForShor.ShorVerification.Framework.Gatecount.ResourceModel
import ForShor.ShorVerification.Framework.Gatecount.PolicyModel
import ForShor.ShorVerification.Framework.ToomCookTable
import ForShor.ShorVerification.Implementation.PhaseProduct.Statement

/-!
# Phase triple product: statement

Everything needed to state what `Main.lean` proves about the **phase triple product** (PTP): the
operator that multiplies a basis state by `exp(iπφ·x·y·z)` on three registers. This is the
three-operand analogue of `PhaseProduct`: each operand is cut into `k` limbs, the product phase
is rebuilt from `3k - 2` smaller phase triple products plus classical arithmetic, and the
recursion bottoms out in a leaf that multiplies out bit by bit.

The definitions are plain data; their invariants are stated and proved in `Proofs/`. A reader who
wants to know what is claimed needs only this file and `Main.lean`.

The file is laid out in the order a reader needs it:

1. **Tables and policies**: what a PTP table and a banded policy are, and the contract that
   decides whether they are admissible (`PTPTable.contract`, `PTPPolicy.check`).
2. **Widths**: the conservative magnitude scan (`childWidth`) and the exact width
   (`ptpTightWidth`) each node's registers are allocated at.
3. **Circuits**: the leaf, one recursion level, the split of three registers into limbs, and the
   recursion `PolicyImpl` / `PolicyImplD` that follows a policy.
4. **Census**: the closed-form gate and qubit counts the circuits are claimed to have.
5. **Specification**: the operators the circuits are compared with, independent of any circuit.
6. **Claims**: the propositions `Main.lean` proves.

This file imports only `Mathlib`, `Framework/` and `PhaseProduct/Statement.lean`.
It reuses `Framework/ToomCookTable.lean` for registers, states, points, `valid_ops`, `Prog`,
`applyOp?`, `run?` and `expectedRow`. The Boolean checkers that a decision procedure needs
(`progConsumesPts?`, `safeProg?`, `returnsToStartCheck`, `validPoint?`) are defined here,
because the Framework states the same conditions as propositions; `Proofs/` relates the two.
-/

namespace Shor
namespace PTP

open Operations
open scoped Matrix

/-! =========================================================
    Tables: Boolean checkers
========================================================= -/

/-- The operation never adds a register to itself. -/
def opOK? {k : ℕ} : valid_ops k → Bool
  | .addScaled dst src _ _ => decide (Not (dst = src))
  | _ => true

/-- Every operation of the program is `opOK?`. -/
def wellFormed? {k : ℕ} : Prog k → Bool
  | [] => true
  | op :: ops => opOK? op && wellFormed? ops

/-- Boolean form of the Framework's `SafeProg` (C3, safety): no `addScaled` adds a register to
itself. -/
def safeProg? {k : ℕ} (ops : Prog k) : Bool :=
  wellFormed? ops

/-- Boolean form of the Framework's `ProgConsumesPts` (C3, consumption): running the program, the
`i`-th `phaseProduct r` checkpoint finds register `r` holding exactly the row of the `i`-th point,
and every point is consumed. -/
def progConsumesPts? {k : ℕ} (hk : k > 0) : State k → Prog k → List Point → Bool
  | _σ, [], [] => true
  | _σ, [], _ :: _ => false
  | σ, op :: ops, pts =>
      match op with
      | .phaseProduct i =>
          match pts with
          | [] => false
          | pt :: rest =>
              matchesAt_pointRow_state (k := k) hk σ i pt &&
                progConsumesPts? hk σ ops rest
      | _ =>
          match applyOp? σ op with
          | none => false
          | some σ' => progConsumesPts? hk σ' ops pts

/-- Equality of two states, as a `Bool`. -/
def statesEqual {k : ℕ} (left right : State k) : Bool :=
  (List.finRange k).all fun i =>
    (List.finRange k).all fun j => decide (left i j = right i j)

/-- Boolean form of C4: the program returns the state it started from, and every right shift is
exact. -/
def returnsToStartCheck {k : ℕ} (ops : Prog k) (σ : State k) : Bool :=
  match run? ops σ with
  | none => false
  | some σ' => statesEqual σ' σ

/-- Thresholds strictly decrease. -/
def sortedDesc : List ℕ → Bool
  | a :: b :: rest => decide (b < a) && sortedDesc (b :: rest)
  | _ => true

/-- `n` is a power of two, with `fuel` halvings allowed. -/
def natPowerOfTwoFuel : ℕ → ℕ → Bool
  | 0, n => n == 1
  | fuel + 1, n =>
      if n == 0 then
        false
      else if n == 1 then
        true
      else if n % 2 == 0 then
        natPowerOfTwoFuel fuel (n / 2)
      else
        false

/-- `n` is a power of two. -/
def natPowerOfTwo? (n : ℕ) : Bool :=
  natPowerOfTwoFuel n n

/-- `±2^e`. -/
def signedPowerOfTwo? (z : ℤ) : Bool :=
  if z = 0 then false else natPowerOfTwo? (Int.natAbs z)

/-- A point the benchmark admits: `0`, `∞` (`frac 0`) or a signed power of two, or its
reciprocal. -/
def validPoint? : Point → Bool
  | .int z => decide (z = 0) || signedPowerOfTwo? z
  | .frac m => decide (m = 0) || signedPowerOfTwo? m

/-- The canonical representative of a projective point (`frac 1 = int 1`, `frac (-1) = int (-1)`). -/
def normalizePoint : Point → Point
  | .frac m =>
      if m = 1 then
        .int 1
      else if m = -1 then
        .int (-1)
      else
        .frac m
  | pt => pt

/-! =========================================================
    Tables and policies
========================================================= -/

/-- One PTP table: `k` limb registers, the interpolation points in the order the
program's `phaseProduct` checkpoints consume them, and the program. -/
structure PTPTable where
  k : Nat
  pts : List Point
  ops : Prog k

/-- PTP point count: `3 k - 2`. -/
def pointCount (k : Nat) : Nat := 3 * k - 2

namespace PTPTable
/-- The PTP table contract as one kernel-reducible `Bool`. -/
def contract (T : PTPTable) : Bool :=
  if hk : 2 ≤ T.k then
    decide (T.pts.length = pointCount T.k) &&
    decide ((T.pts.map normalizePoint).Nodup) &&
    T.pts.all validPoint? &&
    progConsumesPts? (k := T.k) (by omega) State.start_state T.ops T.pts &&
    safeProg? T.ops &&
    returnsToStartCheck T.ops State.start_state
  else false

end PTPTable
/-- Magnitude-bit bounds of the `k` limb registers of one operand, as a list
indexed by register (length `k`; see `wStep_length`). A list rather than a
function so that both the kernel and compiled reports evaluate the scan in
linear time (a closure chain re-evaluates the new bound on every lookup). -/
abbrev Widths := List Nat

/-- The bound of register `i`. -/
def wget {k : Nat} (w : Widths) (i : Fin k) : Nat := w.getD i.1 0

/-- One transition of the PTP magnitude scan (per operand). -/
def wStep {k : Nat} (w : Widths) : valid_ops k → Widths
  | .shiftL i n => w.set i.1 (wget w i + n)
  | .shiftR i n => w.set i.1 (wget w i - n)
  | .negate _ => w
  | .addScaled d s _ sh => w.set d.1 (1 + max (wget w d) (wget w s + sh))
  | .phaseProduct _ => w

/-- Largest bound in a state. -/
def wMax (w : Widths) : Nat := w.foldl max 0

/-- Largest bound reached anywhere along the program (initial state included). -/
def scanMax {k : Nat} : Widths → Prog k → Nat
  | w, [] => wMax w
  | w, op :: ops => max (wMax w) (scanMax (wStep w op) ops)

/-- Common lower-limb width of three operands: `min (n₀/k) (n₁/k) (n₂/k)`. -/
def limbWidth3 (n : Fin 3 → Nat) (k : Nat) : Nat :=
  min (n 0 / k) (min (n 1 / k) (n 2 / k))

/-- Initial bounds of a width-`nW` operand split top-heavy at lower width `W`. -/
def initW (nW W k : Nat) : Widths :=
  List.ofFn (n := k) fun i => if i.1 + 1 = k then nW - (k - 1) * W else W

/-- **PTP child width** for operand widths `n` (three, possibly unequal). -/
def childWidth3 {k : Nat} (n : Fin 3 → Nat) (ops : Prog k) : Nat :=
  let W := limbWidth3 n k
  1 + max (scanMax (initW (n 0) W k) ops)
        (max (scanMax (initW (n 1) W k) ops) (scanMax (initW (n 2) W k) ops))

/-- Balanced PTP child width (all three operands of width `n`). -/
def childWidth {k : Nat} (n : Nat) (ops : Prog k) : Nat := childWidth3 (fun _ => n) ops

/-- Balanced lower-limb width `n / k`. -/
def limbWidth (n k : Nat) : Nat := limbWidth3 (fun _ => n) k

structure PTPBand where
  threshold : Nat
  table : PTPTable

/-- A banded PhaseTripleProduct policy (the mode is fixed). -/
structure PTPPolicy where
  bands : List PTPBand
  /-- How a negation is built and charged; one qubit unless asked (modular swap 002). -/
  negation : NegationMethod := .oneQubit

namespace PTPPolicy

/-- The resource model a PTP policy is priced under (its negation method). -/
def resourceModel (P : PTPPolicy) : LowGateResourceModel := shorGateResourceModelFor P.negation

theorem resourceModel_of_oneQubit {P : PTPPolicy} (h : P.negation = .oneQubit) :
    P.resourceModel = shorGateResourceModel := by
  simp [resourceModel, h]

/-- The same bands under another negation method. -/
def withNegation (P : PTPPolicy) (m : NegationMethod) : PTPPolicy := { P with negation := m }

@[simp] theorem withNegation_bands (P : PTPPolicy) (m : NegationMethod) :
    (P.withNegation m).bands = P.bands := rfl

@[simp] theorem withNegation_negation (P : PTPPolicy) (m : NegationMethod) :
    (P.withNegation m).negation = m := rfl

/-- First band with `threshold ≤ n` (ForShor's `choose`). -/
def choose (P : PTPPolicy) (n : Nat) : Option PTPTable :=
  (P.bands.find? (fun b => decide (b.threshold ≤ n))).map PTPBand.table

/-- **The PTP policy check**: thresholds strictly decrease and every band's
table passes the PTP contract. -/
def check (P : PTPPolicy) : Bool :=
  sortedDesc (P.bands.map PTPBand.threshold) &&
    P.bands.all (fun b => b.table.contract)

end PTPPolicy
/-! ## The interpolation weights -/

/-- The interpolation row of a point in an `N`-coefficient system: `z ^ j` for `int z`,
`c ^ (N - 1 - j)` for `frac c`. -/
def pointRowQ (N : ℕ) (p : Point) (j : Fin N) : ℚ :=
  match p with
  | .int z => (z : ℚ) ^ (j : ℕ)
  | .frac c => (c : ℚ) ^ (N - 1 - (j : ℕ))

/-- Interpolation weight of declared point `t` at radix `2 ^ limbWidth n k`: the row
`[1, B, B², …]` times the inverse of the interpolation matrix of the table's `3k - 2` points.
The product of three degree-`(k - 1)` limb polynomials has degree `3 (k - 1)`, so its value at
the radix is `Σₜ weightₜ · (value at pointₜ)`. -/
noncomputable def PTPTable.coeff (T : PTPTable) (n : ℕ) (t : Fin T.pts.length) : ℚ :=
  ((fun j : Fin T.pts.length => ((2 : ℚ) ^ limbWidth n T.k) ^ (j : ℕ)) ᵥ*
      (ToomCookMath.interpMatrix (pointRowQ T.pts.length)
        (fun i : Fin T.pts.length => T.pts.get i))⁻¹) t

/-! ## The leaf: a sandwich of Toffolis around one rotation per cell -/

/-- One cell: a signed bit term of each operand. -/
abbrev Cell := (ℕ × ℤ) × (ℕ × ℤ) × (ℕ × ℤ)

/-- Angle of one cell: `φ · wₐ · w_c · w_d`. -/
def cellAngle (φ : Angle) (t : Cell) : Angle :=
  φ * (t.1.2 : ℚ) * (t.2.1.2 : ℚ) * (t.2.2.2 : ℚ)

/-- Active-qubit disjointness of the three leaf operands. -/
def LeafActiveDisjoint (x y z : ExtReg) : Prop :=
  ExtReg.ActiveDisjoint x y ∧ ExtReg.ActiveDisjoint x z ∧ ExtReg.ActiveDisjoint y z

/-- One cell of a row: `u ← t ∧ z_d`, one rotation on `u`, uncompute `u`. -/
def sandCell (φ : Angle) (t u : ℕ) (a c d : ℕ × ℤ) : LowGate :=
  LowGate.Toffoli t d.1 u ;; LowGate.Phase u (cellAngle φ (a, c, d)) ;;
    LowGate.adj (LowGate.Toffoli t d.1 u)

/-- One row: `t ← x_a ∧ y_c`, the cells over `z`, uncompute `t`. -/
def sandRow (φ : Angle) (t u : ℕ) (zs : List (ℕ × ℤ)) (a c : ℕ × ℤ) : LowGate :=
  LowGate.Toffoli a.1 c.1 t ;; LowGate.sequence (zs.map (sandCell φ t u a c)) ;;
    LowGate.adj (LowGate.Toffoli a.1 c.1 t)

/-- All pairs from two lists, first-major. -/
def pairsOf {α β : Type} (as : List α) (bs : List β) : List (α × β) :=
  as.flatMap fun a => bs.map fun c => (a, c)

/-- The `(x, y)` bit-term pairs: one row each. -/
def leafPairs (x y : ExtReg) : List ((ℕ × ℤ) × (ℕ × ℤ)) := pairsOf (signedTerms x) (signedTerms y)

/-- The rows of the sandwich leaf, `x`-major. -/
def sandRows (φ : Angle) (x y z : ExtReg) (t u : ℕ) : List LowGate :=
  (leafPairs x y).map fun p => sandRow φ t u (signedTerms z) p.1 p.2

/-- **The PTP sandwich leaf** (ancillas `t`, `u`). -/
def ptpLeafSandwich (φ : Angle) (x y z : ExtReg) (t u : ℕ) : LowGate :=
  LowGate.sequence (sandRows φ x y z t u)

/-- The two leaf ancillas are distinct and off the three operands. -/
def SandwichAnc (x y z : ExtReg) (t u : ℕ) : Prop :=
  t ≠ u ∧ t ∉ x.active.qubits ∧ t ∉ y.active.qubits ∧ t ∉ z.active.qubits ∧
    u ∉ x.active.qubits ∧ u ∉ y.active.qubits ∧ u ∉ z.active.qubits

/-- Number of uncomputing Toffolis (`† Toffoli`): the And† of the Qualtran leaf. -/
def adjToffCount : LowGate → ℕ
  | .seq U V => adjToffCount U + adjToffCount V
  | .adj (.Toffoli _ _ _) => 1
  | _ => 0

/-! ## One recursion level -/

/-- Slot layout of one PTP node. -/
structure NodeLayout (k : ℕ) where
  slot : Fin 3 → Fin k → ExtReg
  width : ℕ
  slot_width : ∀ s i, (slot s i).width = width
  disjoint : ∀ s i s' i', (s, i) ≠ (s', i') → ExtReg.ActiveDisjoint (slot s i) (slot s' i')

/-- The gate one operation applies to operand `s`. -/
def opGate {k : ℕ} (Lay : NodeLayout k) (s : Fin 3) : valid_ops k → LowGate
  | .shiftL i n => LowGate.ShiftL (Lay.slot s i) n
  | .shiftR i n => LowGate.ShiftR (Lay.slot s i) n
  | .negate i => LowGate.Negate (Lay.slot s i)
  | .addScaled d src neg sh => LowGate.AddScaled (Lay.slot s d) (Lay.slot s src) neg sh
  | .phaseProduct _ => LowGate.id

/-- The three gates of one operation. -/
def opGates {k : ℕ} (Lay : NodeLayout k) (op : valid_ops k) : LowGate :=
  opGate Lay 0 op ;; opGate Lay 1 op ;; opGate Lay 2 op

/-- Node body: `child t i` is called at the `t`-th checkpoint, on limb `i`. -/
def body {k : ℕ} (Lay : NodeLayout k) (child : ℕ → Fin k → LowGate) : ℕ → Prog k → LowGate
  | _, [] => LowGate.id
  | t, .phaseProduct i :: ops => child t i ;; body Lay child (t + 1) ops
  | t, .shiftL i n :: ops => opGates Lay (.shiftL i n) ;; body Lay child t ops
  | t, .shiftR i n :: ops => opGates Lay (.shiftR i n) ;; body Lay child t ops
  | t, .negate i :: ops => opGates Lay (.negate i) ;; body Lay child t ops
  | t, .addScaled d s neg sh :: ops => opGates Lay (.addScaled d s neg sh) ;; body Lay child t ops

/-- Weight of checkpoint `t` (zero past the last point). -/
noncomputable def coeffN (T : PTPTable) (n t : ℕ) : ℚ :=
  if h : t < T.pts.length then T.coeff n ⟨t, h⟩ else 0

/-- Number of checkpoints. -/
def cpCount {k : ℕ} : Prog k → ℕ
  | [] => 0
  | .phaseProduct _ :: ops => cpCount ops + 1
  | _ :: ops => cpCount ops

/-! ## Exact widths -/

section ExactWidths

variable {k : ℕ}

/-- Every register row of every state an STO run visits (state before each
operation and the final one; stops at an inexact shift). -/
def reachRows : State k → Prog k → List (Register k)
  | σ, [] => List.ofFn σ
  | σ, op :: ops =>
      List.ofFn σ ++ (match applyOp? σ op with
        | none => []
        | some σ' => reachRows σ' ops)

/-- Width of the top limb field at operand width `n`. -/
def topWidth (k n : ℕ) : ℕ := n - (k - 1) * (n / k)

def limbLo (k n : ℕ) (j : Fin k) : ℤ :=
  if (j : ℕ) + 1 = k then -2 ^ (topWidth k n - 1) else 0

def limbHi (k n : ℕ) (j : Fin k) : ℤ :=
  if (j : ℕ) + 1 = k then 2 ^ (topWidth k n - 1) - 1 else 2 ^ (n / k) - 1

def rowLo (k n : ℕ) (r : Register k) : ℤ :=
  ((List.finRange k).map fun j => min (r j * limbLo k n j) (r j * limbHi k n j)).sum

def rowHi (k n : ℕ) (r : Register k) : ℤ :=
  ((List.finRange k).map fun j => max (r j * limbLo k n j) (r j * limbHi k n j)).sum

/-- A signed `W`-bit register holds the row iff `rowDemand ≤ 2^(W-1)`. -/
def rowDemand (k n : ℕ) (r : Register k) : ℕ :=
  max (-rowLo k n r).toNat (rowHi k n r + 1).toNat

def maxDemand (k n : ℕ) : List (Register k) → ℕ
  | [] => 0
  | r :: rs => max (rowDemand k n r) (maxDemand k n rs)

/-- Least `e ≥ e₀` with `D ≤ 2^e`, searching at most `f` steps. -/
def leastExp (D : ℕ) : ℕ → ℕ → ℕ
  | 0, e => e
  | f + 1, e => if D ≤ 2 ^ e then e else leastExp D f (e + 1)

/-- The largest demand over the rows a PTP table's program reaches, at width `n`. -/
def ptpDemand (T : PTPTable) (n : ℕ) : ℕ :=
  maxDemand T.k n (reachRows State.start_state T.ops)

/-- **The exact PTP width** at operand width `n`: the least `W ≥ 1` with
`ptpDemand ≤ 2^(W-1)` (`ptpTightWidth_spec`). -/
def ptpTightWidth (T : PTPTable) (n : ℕ) : ℕ := 1 + leastExp (ptpDemand T n) (ptpDemand T n) 0

namespace PTPPolicy

/-- Fuelled walk down the exact-width recursion, recording each width and the arity chosen there. -/
def ladderFuelX (P : PTPPolicy) : ℕ → ℕ → List (ℕ × Option ℕ)
  | 0, n => [(n, none)]
  | f + 1, n =>
      match P.choose n with
      | none => [(n, none)]
      | some T =>
          if ptpTightWidth T n < n then (n, some T.k) :: ladderFuelX P f (ptpTightWidth T n)
          else [(n, none)]

/-- The exact-width ladder. -/
def ladderX (P : PTPPolicy) (n : ℕ) : List (ℕ × Option ℕ) := ladderFuelX P (n + 1) n

end PTPPolicy

end ExactWidths

/-! ## The recursion and the census -/

/-- Numbers of `addScaled` and `negate` operations. -/
def addCount {k : ℕ} : Prog k → ℕ
  | [] => 0
  | .addScaled _ _ _ _ :: ops => addCount ops + 1
  | _ :: ops => addCount ops

def negCount {k : ℕ} : Prog k → ℕ
  | [] => 0
  | .negate _ :: ops => negCount ops + 1
  | _ :: ops => negCount ops

/-- Additive census record (H, X, CNOT, Toffoli, Rz). -/
structure Census where
  h : ℕ
  x : ℕ
  cnot : ℕ
  toffoli : ℕ
  rz : ℕ
deriving Repr, DecidableEq

/-- Sandwich-leaf census at width `w` (three operands of width `w`):
`Toffoli = 2 (w² + w³)`, `Rz = w³` (`ptpLeafSandwich_resources`). -/
def leafCensus (w : ℕ) : Census :=
  ⟨0, 0, 0, 2 * (w * w + w * w * w), w * w * w⟩

/-! ### The negation charge, by method

The numbers a negation of a `w`-bit register is charged, as plain functions of `w`, so that the census formulas
can be written once for both `NegationMethod`s. `negateResourcesFor_eq` (in `Proofs/Recursion/Census.lean`) ties
them to the Framework's `negateResourcesFor`.

* `oneQubit`: complement plus Gidney's single-ancilla increment (`negateXGates` ...); one clean qubit.
* `scratch`: complement plus a Cuccaro adder against a clean constant-one register (the construction before
  modular swap 001): `X = w + (2 w - 6) + 2`, `CNOT = 5 w - 7`, `Toffoli = 2 w - 3`, and `w + 1` clean qubits
  (the constant-one register and the adder's carry). -/

/-- X gates of a `w`-bit negation under method `m`. -/
def negateXGatesFor : NegationMethod → ℕ → ℕ
  | .oneQubit, w => negateXGates w
  | .scratch, w => w + (2 * w - 6) + 2

/-- CNOT gates of a `w`-bit negation under method `m`. -/
def negateCnotGatesFor : NegationMethod → ℕ → ℕ
  | .oneQubit, w => negateCnotGates w
  | .scratch, w => 5 * w - 7

/-- Toffoli gates of a `w`-bit negation under method `m`. -/
def negateToffoliGatesFor : NegationMethod → ℕ → ℕ
  | .oneQubit, w => negateToffoliGates w
  | .scratch, w => 2 * w - 3

/-- Clean qubits a `w`-bit negation holds while it runs under method `m`: one, or `w + 1`. -/
def negateCleanAncFor : NegationMethod → ℕ → ℕ
  | .oneQubit, _ => 1
  | .scratch, w => w + 1

/-- Node census at working width `C` for a table with `A` adds, `N` negates and
`P` checkpoints, children costing `ch` each, with negations charged by method `m`. -/
def nodeCensusFor (m : NegationMethod) (C A N P : ℕ) (ch : Census) : Census :=
  ⟨P * ch.h,
   3 * (A * (2 * C - 6) + N * negateXGatesFor m C) + P * ch.x,
   3 * (A * (5 * C - 7) + N * negateCnotGatesFor m C) + P * ch.cnot,
   3 * (A * (2 * C - 3) + N * negateToffoliGatesFor m C) + P * ch.toffoli,
   P * ch.rz⟩

/-- Node census under the default (`oneQubit`) negation method. -/
def nodeCensus (C A N P : ℕ) (ch : Census) : Census := nodeCensusFor .oneQubit C A N P ch

/-- Clean scratch qubits one node holds at working width `C` with `A` adds and `N` negates: an addition holds
one (the carry), a negation `negateCleanAncFor m C`, and the node holds them one at a time. -/
def nodeCleanAncFor (m : NegationMethod) (C A N : ℕ) : ℕ :=
  if N = 0 then (if A = 0 then 0 else 1) else negateCleanAncFor m C

/-- Per-operand reserve (ForShor `reserveNeed`, three operands): growing the
`k` chunks to `C` at this level, plus a private workspace for each of the `k`
child slots. -/
def ptpReserveNeed (P : PTPPolicy) (n : ℕ) : ℕ :=
  match P.choose n with
  | none => 0
  | some T =>
      if _h : childWidth n T.ops < n then
        (T.k * childWidth n T.ops - n) + T.k * ptpReserveNeed P (childWidth n T.ops)
      else 0
termination_by n

/-- **Peak clean scratch qubits along the ladder**, under the policy's own negation method `P.negation`: the
largest number of clean qubits the resource model `P.resourceModel` holds at once in one node of the recursion
(`nodeCleanAncFor`). A node with no addition and no negation holds none; one with only additions holds one (the
Cuccaro carry); one with a negation holds `negateCleanAncFor P.negation C`, where `C` is the node's working width.
So for `oneQubit` (complement plus a single-ancilla increment) the peak is `1`, and for `scratch` (a clean
constant-one register plus the Cuccaro carry) it is `C + 1` at the widest node that negates. The sandwich leaves
hold none: their two ancillas are explicit qubits, not model scratch. -/
def ptpCleanAnc (P : PTPPolicy) (n : ℕ) : ℕ :=
  match P.choose n with
  | none => 0
  | some T =>
      if _h : childWidth n T.ops < n then
        max (nodeCleanAncFor P.negation (childWidth n T.ops) (addCount T.ops) (negCount T.ops))
          (ptpCleanAnc P (childWidth n T.ops))
      else 0
termination_by n

/-- Logical qubits of one PTP call at width `n`: three operands, three
per-operand reserves, peak clean scratch, where the sandwich leaves' two ancillas
(`ptpNode_qubits_le`) are needed only while a leaf runs, so they share the scratch
peak: `max (ptpCleanAnc) 2`. The scratch is the one of the policy's negation method
(`ptpCleanAnc`: `1` for `oneQubit`, up to `C + 1` for `scratch`). It bounds the qubits the circuit names
(`PTPQubitsLePtpQubits`), not the framework's `LowGate.qubitCount`, which holds the leaf ancillas and the scratch
at once; for that, see `ptpPeakQubits` and `PTPPeakQubits`. -/
def ptpQubits (P : PTPPolicy) (n : ℕ) : ℕ :=
  3 * n + 3 * ptpReserveNeed P n + max (ptpCleanAnc P n) 2

/-! ### Splitting three registers into limbs, and the recursion itself -/

/-- Floor-limb chunk `j` of a register at lower width `L`: bits `[jL, jL + L)`;
the top chunk (`j = k - 1`) is everything from `(k-1)L` on. -/
def chunkReg (r : Reg) (k L : ℕ) (j : Fin k) : Reg :=
  if (j : ℕ) + 1 = k then r.drop (j * L) else (r.drop (j * L)).take L

/-- **A split layout** (ForShor's `PhaseSplitLayout`, three operands): child slot `(s, j)`
is chunk `j` of parent register `X s` (as an `ExtReg` `pre s j` whose active part is the
chunk and whose reserve supplies the extension), grown by `ext s j` qubits to the child
width `C'`. The `newBits` of all slots form the level's reserve `R`; lower chunks are
zero-extended, the top chunk sign-extended. Here it is an arbitrary layout satisfying the
fields; `Build.lean` (`mkSplit`) constructs one from fresh reserve qubits. -/
structure SplitLayout (X : Fin 3 → ExtReg) (k C' : ℕ) where
  pre : Fin 3 → Fin k → ExtReg
  ext : Fin 3 → Fin k → ℕ
  two_le : 2 ≤ k
  pre_active : ∀ s j, (pre s j).active = chunkReg (X s).active k ((X s).width / k) j
  can_grow : ∀ s j, (pre s j).CanGrow (ext s j)
  ext_width : ∀ s j, (pre s j).width + ext s j = C'
  ext_pos : ∀ (s : Fin 3) (j : Fin k), (j : ℕ) + 1 ≠ k → 0 < ext s j
  disjoint : ∀ s j s' j', (s, j) ≠ (s', j') →
    ExtReg.ActiveDisjoint ((pre s j).grow (ext s j)) ((pre s' j').grow (ext s' j'))

namespace SplitLayout
variable {X : Fin 3 → ExtReg} {k C' : ℕ} (SL : SplitLayout X k C')
/-- The child slots as a `NodeLayout` of width `C'`. -/
def lay : NodeLayout k where
  slot s j := (SL.pre s j).grow (SL.ext s j)
  width := C'
  slot_width s j := by
    have hcap := SL.can_grow s j
    have hw := SL.ext_width s j
    simp only [ExtReg.width, ExtReg.grow, ExtReg.CanGrow, ExtReg.capacity, ExtReg.newBits,
      ExtReg.remainingReserve, regSize, Reg.append, Reg.take, Reg.width, List.length_append,
      List.length_take] at hcap hw ⊢
    omega
  disjoint := SL.disjoint

/-- The top chunk index. -/
def top : Fin k := ⟨k - 1, by have := SL.two_le; omega⟩

/-- The level's reserve: all extension qubits. -/
def R : List ℕ :=
  (List.finRange 3).flatMap fun s => (List.finRange k).flatMap fun j =>
    ((SL.pre s j).newBits (SL.ext s j)).qubits

/-- The allocation: zero-extend every lower chunk (identity on basis states) and
sign-extend the three top chunks. -/
def alloc : LowGate :=
  LowGate.sequence ((List.finRange 3).flatMap fun s => (List.finRange k).map fun j =>
      LowGate.zeroExtend (SL.pre s j) (SL.ext s j)) ;;
    LowGate.signExtend (SL.pre 0 SL.top) (SL.ext 0 SL.top) ;;
    LowGate.signExtend (SL.pre 1 SL.top) (SL.ext 1 SL.top) ;;
    LowGate.signExtend (SL.pre 2 SL.top) (SL.ext 2 SL.top)

end SplitLayout
/-- **A PTP node acting on three parent registers**: allocate the child slots (split +
zero/sign extension into the level reserve), run the node body with children `gc`, and
undo the allocation (`† alloc`). -/
noncomputable def ptpSubNode {X : Fin 3 → ExtReg} (T : PTPTable) (SL : SplitLayout X T.k C')
    (gc : ℕ → Fin T.k → LowGate) : LowGate :=
  SL.alloc ;; body SL.lay gc 0 T.ops ;; LowGate.adj SL.alloc

/-- **A gate-level PTP recursion following policy `P`** at width `C` on parent registers `X`,
with workspace `W`, as a family of circuits `G θ`:

* `leaf`: where `P` stops at `C` (no table, or no shrink), the sandwich leaf with its two
  ancillas;
* `node`: where `P` chooses `T` and `C' = childWidth C T.ops < C`, a split layout `SL`
  of `X` into child slots of width `C'`, and for every child slot triple `j` a recursion
  `G j` at `C'` whose workspace `Wc j` lies in a common `W'` off all child slots; the
  node's workspace is `R ++ W'`.

Children at the same level run one after another and each returns its workspace clean,
so all of them share `W'` (one reserve per level, not per child). -/
inductive PolicyImpl (P : PTPPolicy) :
    (Fin 3 → ExtReg) → ℕ → List ℕ → (Angle → LowGate) → Prop
  | leaf (X : Fin 3 → ExtReg) (C t u : ℕ) (hX : ∀ s, (X s).width = C)
      (hstop : ∀ T, P.choose C = some T → C ≤ childWidth C T.ops)
      (hD : LeafActiveDisjoint (X 0) (X 1) (X 2)) (hA : SandwichAnc (X 0) (X 1) (X 2) t u) :
      PolicyImpl P X C [t, u] (fun θ => ptpLeafSandwich θ (X 0) (X 1) (X 2) t u)
  | node (X : Fin 3 → ExtReg) (C : ℕ) (T : PTPTable) (hX : ∀ s, (X s).width = C) (hC : 0 < C)
      (hc : P.choose C = some T) (hlt : childWidth C T.ops < C)
      (SL : SplitLayout X T.k (childWidth C T.ops)) (G : Fin T.k → Angle → LowGate)
      (W' : List ℕ) (Wc : Fin T.k → List ℕ) (hWc : ∀ j, ∀ q ∈ Wc j, q ∈ W')
      (hW' : ∀ q ∈ W', ∀ s j, q ∉ (SL.lay.slot s j).active.qubits)
      (hsub : ∀ j, PolicyImpl P (fun s => SL.lay.slot s j) (childWidth C T.ops) (Wc j) (G j)) :
      PolicyImpl P X C (SL.R ++ W') (fun θ => ptpSubNode T SL (fun t j => G j (θ * coeffN T C t)))

/-- Three pairwise disjoint `C`-qubit registers below `base`. -/
def Good (X : Fin 3 → ExtReg) (C base : ℕ) : Prop :=
  (∀ s, (X s).width = C) ∧ (∀ s s', s ≠ s' → ExtReg.ActiveDisjoint (X s) (X s')) ∧
    (∀ s, ∀ q ∈ (X s).active.qubits, q < base)

/-- Width of the top limb at width `n`. -/
def topLimbWidth (n k : ℕ) : ℕ := n - (k - 1) * (n / k)

/-! ## The acceptance rule at exact widths -/

namespace PTPPolicy

/-- One rung of the exact ladder is admissible: a `none` rung is a genuine leaf (no band is
chosen there, rather than a chosen band failing to shrink), and a `some k` rung has `k ≤ w`. -/
def rungOK (P : PTPPolicy) : ℕ × Option ℕ → Bool
  | (w, none) => (P.choose w).isNone
  | (w, some k) => decide (k ≤ w)

/-- **The threshold acceptance rule at exact widths.** Every band chosen on the exact-width
recursion from `n` strictly shrinks the width and is applied at a width `≥ k`. -/
def chainContractsTight (P : PTPPolicy) (n : ℕ) : Bool :=
  (P.ladderX n).all P.rungOK

/-- Widths the exact-width recursion from `n` visits (every chosen table, shrinking or not). -/
inductive ExactReach (P : PTPPolicy) (n : ℕ) : ℕ → Prop
  | refl : ExactReach P n n
  | step {m : ℕ} {T : PTPTable} : ExactReach P n m → P.choose m = some T →
      ExactReach P n (ptpTightWidth T m)

end PTPPolicy

/-! ## The recursion at a given width rule (exact board and scan board) -/

/-- A node width rule: `wd T n` = working width of the children of the node with table `T` at
parent width `n`. -/
abbrev WidthRule := PTPTable → ℕ → ℕ

/-- The exact board: every node at its exact width. -/
abbrev exactRule : WidthRule := fun T n => ptpTightWidth T n

/-- A rule is admissible for `P` when every band's node width is at least the exact width. -/
def Admissible (P : PTPPolicy) (wd : WidthRule) : Prop :=
  ∀ b ∈ P.bands, ∀ n, 0 < n → ptpTightWidth b.table n ≤ wd b.table n

/-- **A gate-level PTP recursion following `P` with node widths `wd`** (as `PolicyImpl`, with
`childWidth C T.ops` replaced by `wd T C`). -/
inductive PolicyImplD (P : PTPPolicy) (wd : WidthRule) :
    (Fin 3 → ExtReg) → ℕ → List ℕ → (Angle → LowGate) → Prop
  | leaf (X : Fin 3 → ExtReg) (C t u : ℕ) (hX : ∀ s, (X s).width = C)
      (hstop : ∀ T, P.choose C = some T → C ≤ wd T C)
      (hD : LeafActiveDisjoint (X 0) (X 1) (X 2)) (hA : SandwichAnc (X 0) (X 1) (X 2) t u) :
      PolicyImplD P wd X C [t, u] (fun θ => ptpLeafSandwich θ (X 0) (X 1) (X 2) t u)
  | node (X : Fin 3 → ExtReg) (C : ℕ) (T : PTPTable) (hX : ∀ s, (X s).width = C) (hC : 0 < C)
      (hc : P.choose C = some T) (hlt : wd T C < C)
      (SL : SplitLayout X T.k (wd T C)) (G : Fin T.k → Angle → LowGate)
      (W' : List ℕ) (Wc : Fin T.k → List ℕ) (hWc : ∀ j, ∀ q ∈ Wc j, q ∈ W')
      (hW' : ∀ q ∈ W', ∀ s j, q ∉ (SL.lay.slot s j).active.qubits)
      (hsub : ∀ j, PolicyImplD P wd (fun s => SL.lay.slot s j) (wd T C) (Wc j) (G j)) :
      PolicyImplD P wd X C (SL.R ++ W') (fun θ => ptpSubNode T SL (fun t j => G j (θ * coeffN T C t)))

/-- The exact-board recursion. -/
abbrev PolicyImplX (P : PTPPolicy) := PolicyImplD P exactRule

/-- `ptpResources` with node widths `wd`. -/
def ptpResourcesD (P : PTPPolicy) (wd : WidthRule) (n : ℕ) : Census :=
  match P.choose n with
  | none => leafCensus n
  | some T =>
      if _h : wd T n < n then
        nodeCensusFor P.negation (wd T n) (addCount T.ops) (negCount T.ops) (cpCount T.ops)
          (ptpResourcesD P wd (wd T n))
      else leafCensus n
termination_by n

/-- `ptpAndDag` with node widths `wd`. -/
def ptpAndDagD (P : PTPPolicy) (wd : WidthRule) (n : ℕ) : ℕ :=
  match P.choose n with
  | none => n * n + n * n * n
  | some T =>
      if _h : wd T n < n then cpCount T.ops * ptpAndDagD P wd (wd T n)
      else n * n + n * n * n
termination_by n

/-- `ptpCnotFull` with node widths `wd`. -/
def ptpCnotFullD (P : PTPPolicy) (wd : WidthRule) (n : ℕ) : ℕ :=
  match P.choose n with
  | none => 0
  | some T =>
      if _h : wd T n < n then
        3 * (addCount T.ops * (5 * wd T n - 7) + negCount T.ops * negateCnotGatesFor P.negation (wd T n)) +
          6 * (wd T n - topLimbWidth n T.k) +
          cpCount T.ops * ptpCnotFullD P wd (wd T n)
      else 0
termination_by n

/-- `ptpWorkspace` with node widths `wd`. -/
def ptpWorkspaceD (P : PTPPolicy) (wd : WidthRule) (n : ℕ) : ℕ :=
  match P.choose n with
  | none => 2
  | some T =>
      if _h : wd T n < n then 3 * T.k * wd T n + ptpWorkspaceD P wd (wd T n)
      else 2
termination_by n

/-- Exact-board census (Rz/Toffoli/X/H/CNOT-without-extension), CNOT with extension, And†,
workspace. -/
abbrev ptpResourcesX (P : PTPPolicy) := ptpResourcesD P exactRule

abbrev ptpCnotFullX (P : PTPPolicy) := ptpCnotFullD P exactRule

abbrev ptpAndDagX (P : PTPPolicy) := ptpAndDagD P exactRule

abbrev ptpWorkspaceX (P : PTPPolicy) := ptpWorkspaceD P exactRule

/-- Workspace actually used by the construction. -/
def ptpWsTD (P : PTPPolicy) (wd : WidthRule) (n : ℕ) : ℕ :=
  match P.choose n with
  | none => 2
  | some T =>
      if _h : wd T n < n then 3 * (T.k * wd T n - n) + ptpWsTD P wd (wd T n) else 2
termination_by n

/-- `ptpReserveNeed` with node widths `wd`. -/
def ptpReserveNeedD (P : PTPPolicy) (wd : WidthRule) (n : ℕ) : ℕ :=
  match P.choose n with
  | none => 0
  | some T =>
      if _h : wd T n < n then (T.k * wd T n - n) + T.k * ptpReserveNeedD P wd (wd T n) else 0
termination_by n

/-- `ptpCleanAnc` with node widths `wd`. -/
def ptpCleanAncD (P : PTPPolicy) (wd : WidthRule) (n : ℕ) : ℕ :=
  match P.choose n with
  | none => 0
  | some T =>
      if _h : wd T n < n then
        max (nodeCleanAncFor P.negation (wd T n) (addCount T.ops) (negCount T.ops))
          (ptpCleanAncD P wd (wd T n))
      else 0
termination_by n

/-- Growth of the width scan contributed by one operation. -/
def opGrowth {k : ℕ} : valid_ops k → ℕ
  | .shiftL _ n => n
  | .shiftR _ _ => 0
  | .negate _ => 0
  | .addScaled _ _ _ sh => 1 + sh
  | .phaseProduct _ => 0

/-- Total growth of a program. -/
def growth {k : ℕ} : Prog k → ℕ
  | [] => 0
  | op :: ops => opGrowth op + growth ops

/-- Gate count of the exact-board circuit: Rz + Toffoli + X + H of the census plus the full CNOT
count (extension included), as `LowGate.resources` reports for `ptp_gate_full_exact`'s circuit. -/
def ptpGateTotalD (P : PTPPolicy) (wd : WidthRule) (n : ℕ) : ℕ :=
  let r := ptpResourcesD P wd n
  r.h + r.x + r.toffoli + r.rz + ptpCnotFullD P wd n

/-- The PTP Toom–Cook exponent `log_k (3k - 2)`. -/
noncomputable def ptpExponent (k : ℕ) : ℝ := Real.logb (k : ℝ) (((3 * k - 2 : ℕ)) : ℝ)

/-- The constant policy: one table `T` at every width `≥ t`. -/
def constPTPPolicy (t : ℕ) (T : PTPTable) : PTPPolicy := { bands := [⟨t, T⟩] }

/-! ## What a circuit must do: the specification operators -/

/-- The PTP phase on a basis ket: `exp(iπφ · ⟦X₀⟧⟦X₁⟧⟦X₂⟧)`. -/
noncomputable def ptpEigenphase {qs : QSemantics} [RegEncoding qs.Basis]
    (φ : Angle) (X : Fin 3 → ExtReg) (b : qs.Basis) : ℂ :=
  Complex.exp (((Angle.toReal φ : ℝ) : ℂ) * Complex.I *
    (((extToInt (X 0) b : ℤ) : ℂ) * ((extToInt (X 1) b : ℤ) : ℂ) * ((extToInt (X 2) b : ℤ) : ℂ)))

/-- A linear state map acting as the PTP phase on every basis ket (the specification operator;
cf. ForShor's `Gate.SignedPhaseProd` evaluation). -/
structure PTPPhaseOp (qs : QSemantics) [RegEncoding qs.Basis] (X : Fin 3 → ExtReg) (φ : Angle) where
  op : qs.State → qs.State
  op_add : ∀ ψ χ, op (ψ + χ) = op ψ + op χ
  op_smul : ∀ (a : ℂ) ψ, op (a • ψ) = a • op ψ
  op_ket : ∀ b : qs.Basis, op (qs.ket b) = ptpEigenphase φ X b • qs.ket b

/-- The basis-level precondition of the PTP gate: the three operands fit signed `n` bits and the
workspace `W` holds `|0⟩`. -/
def PTPCleanBasis (qs : QSemantics) [RegEncoding qs.Basis] (X : Fin 3 → ExtReg) (n : ℕ)
    (W : List ℕ) (b : qs.Basis) : Prop :=
  (∀ s, FitsSignedWidth n (extToInt (X s) b)) ∧ ∀ q ∈ W, RegEncoding.bit q b = false

/-- A state with a clean workspace: the linear closure of the clean basis kets. -/
abbrev PTPCleanState (qs : QSemantics) [RegEncoding qs.Basis] (X : Fin 3 → ExtReg) (n : ℕ)
    (W : List ℕ) : qs.State → Prop :=
  CleanClosure (PTPCleanBasis qs X n W)

/-- `Toffoli c x y` for every pair `(x, y)`. -/
def maskGate (c : ℕ) : List (ℕ × ℕ) → LowGate
  | [] => LowGate.id
  | p :: ps => LowGate.Toffoli c p.1 p.2 ;; maskGate c ps

/-- The uncomputation of `maskGate`: the same Toffolis as `†Toffoli`, in reverse order. -/
def unmaskGate (c : ℕ) : List (ℕ × ℕ) → LowGate
  | [] => LowGate.id
  | p :: ps => unmaskGate c ps ;; LowGate.adj (LowGate.Toffoli c p.1 p.2)

/-- Mask `X` into `Y`: `Toffoli c xᵢ yᵢ` for every bit position. -/
def maskReg (c : ℕ) (X Y : Reg) : LowGate := maskGate c (X.qubits.zip Y.qubits)

def unmaskReg (c : ℕ) (X Y : Reg) : LowGate := unmaskGate c (X.qubits.zip Y.qubits)

/-- The controlled gate: mask, run `G`, unmask. -/
def ctlGate (c : ℕ) (X Y : Reg) (G : LowGate) : LowGate :=
  maskReg c X Y ;; G ;; unmaskReg c X Y

/-- The controlled PTP phase on a basis ket: `exp(iπφ·⟦X₀⟧⟦X₁⟧⟦X₂⟧)` if the control bit is set,
`1` otherwise (cf. ForShor's `eval_CSignedPhaseProd_ket`). -/
noncomputable def ptpCtlEigenphase {qs : QSemantics} [RegEncoding qs.Basis]
    (φ : Angle) (c : ℕ) (X : Fin 3 → ExtReg) (b : qs.Basis) : ℂ :=
  if RegEncoding.bit c b then ptpEigenphase φ X b else 1

/-- A linear state map acting as the controlled PTP phase on every basis ket. -/
structure PTPCtlPhaseOp (qs : QSemantics) [RegEncoding qs.Basis] (c : ℕ) (X : Fin 3 → ExtReg)
    (φ : Angle) where
  op : qs.State → qs.State
  op_add : ∀ ψ χ, op (ψ + χ) = op ψ + op χ
  op_smul : ∀ (a : ℂ) ψ, op (a • ψ) = a • op ψ
  op_ket : ∀ b : qs.Basis, op (qs.ket b) = ptpCtlEigenphase φ c X b • qs.ket b

/-- Sign-extend the three operands by `d s` bits each, in place. -/
def padGate (X : Fin 3 → ExtReg) (d : Fin 3 → ℕ) : LowGate :=
  LowGate.signExtend (X 0) (d 0) ;; LowGate.signExtend (X 1) (d 1) ;; LowGate.signExtend (X 2) (d 2)

/-- The padded circuit: extend, run `G` on the grown registers, undo. -/
def padCtl (X : Fin 3 → ExtReg) (d : Fin 3 → ℕ) (G : LowGate) : LowGate :=
  padGate X d ;; G ;; LowGate.adj (padGate X d)

/-- Reserves can grow and the grown registers are pairwise active-disjoint. -/
structure PadOK (X : Fin 3 → ExtReg) (d : Fin 3 → ℕ) : Prop where
  cap : ∀ s, (X s).CanGrow (d s)
  disj : ∀ s s', s ≠ s' → ExtReg.ActiveDisjoint ((X s).grow (d s)) ((X s').grow (d s'))

/-- The grown registers. -/
abbrev padReg (X : Fin 3 → ExtReg) (d : Fin 3 → ℕ) : Fin 3 → ExtReg := fun s => (X s).grow (d s)

/-- The reserve qubits consumed by the padding. -/
def padNew (X : Fin 3 → ExtReg) (d : Fin 3 → ℕ) : List ℕ :=
  (List.finRange 3).flatMap fun s => ((X s).newBits (d s)).qubits

/-- Basis predicate for the padded circuit: operand `s` fits its **own** width `(X s).width`,
the reserves and the recursion workspace are zero. -/
def PTPCleanBasisU (qs : QSemantics) [RegEncoding qs.Basis] (X : Fin 3 → ExtReg) (W : List ℕ)
    (b : qs.Basis) : Prop :=
  (∀ s, FitsSignedWidth (X s).width (extToInt (X s) b)) ∧ ∀ q ∈ W, RegEncoding.bit q b = false

/-! ## The claims -/

/-- The gate-level census of a circuit equals the exact-board formulas for `P` at width `n`. -/
def PTPExactCensus (P : PTPPolicy) (n : ℕ) (G : LowGate) : Prop :=
  let R := LowGate.resources P.resourceModel G
  R.rz = (ptpResourcesX P n).rz ∧ R.toffoli = (ptpResourcesX P n).toffoli ∧
    R.x = (ptpResourcesX P n).x ∧ R.h = (ptpResourcesX P n).h ∧
    R.cnot = ptpCnotFullX P n ∧ adjToffCount G = ptpAndDagX P n ∧
    (LowGate.usedQubits G).card ≤ 3 * n + ptpWorkspaceX P n

/-- **Assertion (state level, exact board).** For a checked policy `P` and three pairwise disjoint `n`-qubit
registers below `base`, there is a circuit family following `P` at exact widths, with workspace
`W` above `base`, which acts as the PTP phase operator on every clean state (for every
specification operator `U`) and has the exact-board gate counts (equalities) and a qubit upper bound. For `n = 0` no basis ket is
clean (`FitsSignedWidth` needs `0 < n`), so the state-level conjunct is vacuous there (the circuit, the
workspace bound and the census are still required). -/
def PTPLowerExactCorrect (qs : QSemantics) [RegEncoding qs.Basis] [LowerGateClass qs]
    (P : PTPPolicy) (n : ℕ) (X : Fin 3 → ExtReg) (base : ℕ) : Prop :=
  P.check = true → Good X n base →
    ∃ (W : List ℕ) (G : Angle → LowGate), PolicyImplX P X n W G ∧
      (∀ q ∈ W, base ≤ q ∧ q < base + ptpWorkspaceX P n) ∧
      (∀ (φ : Angle) (U : PTPPhaseOp qs X φ) (ψ : qs.State), PTPCleanState qs X n W ψ →
        LowerGateClass.evalL (qs := qs) (G φ) ψ = U.op ψ) ∧
      (∀ φ : Angle, PTPExactCensus P n (G φ))

/-- The gate-level census of a controlled circuit: the exact-board census of the uncontrolled
recursion plus `2n` Toffoli (`n` of them `†Toffoli`) and `n + 1` qubits. -/
def PTPCtlExactCensus (P : PTPPolicy) (n : ℕ) (G : LowGate) : Prop :=
  let R := LowGate.resources P.resourceModel G
  R.rz = (ptpResourcesX P n).rz ∧ R.toffoli = (ptpResourcesX P n).toffoli + 2 * n ∧
    R.x = (ptpResourcesX P n).x ∧ R.h = (ptpResourcesX P n).h ∧
    R.cnot = ptpCnotFullX P n ∧ adjToffCount G = ptpAndDagX P n + n ∧
    (LowGate.usedQubits G).card ≤ 4 * n + ptpWorkspaceX P n + 1

/-- **Assertion: controlled PTP at exact widths** (clean subspace; `n ≥ 1`; gate counts are
equalities, the qubit count is an upper bound). Degenerate placements are allowed and proved: if `c`
lies in the recursion workspace `W` it is `0` on every clean ket (the gate is the identity there), if
it lies in `X₁` or `X₂` it controls on an operand bit. For a checked policy `P`, `n`-bit operands
`X₀, X₁, X₂`, a fresh `n`-bit register `Y`, and a control `c`, there is a circuit that acts as the
controlled PTP phase operator on every clean state (with `Y` and the recursion workspace zero)
and whose census is the exact-board census plus the mask. -/
def PTPCtlLowerExactCorrect (qs : QSemantics) [RegEncoding qs.Basis] [LowerGateClass qs]
    (P : PTPPolicy) (n : ℕ) (X : Fin 3 → ExtReg) (Y : ExtReg) (c base : ℕ) : Prop :=
  P.check = true → (∀ s, (X s).width = n) → Good (Function.update X 0 Y) n base →
  (∀ s, ∀ q ∈ (X s).active.qubits, q ∉ Y.active.qubits) →
  c ∉ (X 0).active.qubits → c ∉ Y.active.qubits →
  ∃ (W : List ℕ) (G : Angle → LowGate),
    PolicyImplX P (Function.update X 0 Y) n W G ∧
    (∀ q ∈ W, base ≤ q ∧ q < base + ptpWorkspaceX P n) ∧
    (∀ (φ : Angle) (U : PTPCtlPhaseOp qs c X φ) (ψ : qs.State),
      PTPCleanState qs X n (Y.active.qubits ++ W) ψ →
      LowerGateClass.evalL (qs := qs) (ctlGate c (X 0).active Y.active (G φ)) ψ = U.op ψ) ∧
    (∀ φ : Angle, PTPCtlExactCensus P n (ctlGate c (X 0).active Y.active (G φ)))

/-- Census of the padded circuit: the balanced exact-board census, with the CNOT count raised by
the extensions (`2 (d₀ + d₁ + d₂)`: extend and undo); `usedQubits` at most `3n + workspace` (the
framework's `cleanAnc` scratch is not included). Vacuous if some operand has width `0`. -/
def PTPPadExactCensus (P : PTPPolicy) (n : ℕ) (d : Fin 3 → ℕ) (G : LowGate) : Prop :=
  let R := LowGate.resources P.resourceModel G
  R.rz = (ptpResourcesX P n).rz ∧ R.toffoli = (ptpResourcesX P n).toffoli ∧
    R.x = (ptpResourcesX P n).x ∧ R.h = (ptpResourcesX P n).h ∧
    R.cnot = ptpCnotFullX P n + 2 * (d 0 + d 1 + d 2) ∧ adjToffCount G = ptpAndDagX P n ∧
    (LowGate.usedQubits G).card ≤ 3 * n + ptpWorkspaceX P n

/-- **Assertion: PTP on operands of unequal widths, exact board** (padding construction; clean
subspace). Operand `s` has width `(X s).width` and a clean reserve of at least `d s` bits, so that all
three grown registers have the common width `n`. -/
def PTPPadLowerExactCorrect (qs : QSemantics) [RegEncoding qs.Basis] [LowerGateClass qs]
    (P : PTPPolicy) (n : ℕ) (X : Fin 3 → ExtReg) (d : Fin 3 → ℕ) (base : ℕ) : Prop :=
  P.check = true → PadOK X d → Good (padReg X d) n base →
  ∃ (W : List ℕ) (G : Angle → LowGate),
    PolicyImplX P (padReg X d) n W G ∧
    (∀ q ∈ W, base ≤ q ∧ q < base + ptpWorkspaceX P n) ∧
    (∀ (φ : Angle) (U : PTPPhaseOp qs X φ) (ψ : qs.State),
      CleanClosure (PTPCleanBasisU qs X (padNew X d ++ W)) ψ →
      LowerGateClass.evalL (qs := qs) (padCtl X d (G φ)) ψ = U.op ψ) ∧
    (∀ φ : Angle, PTPPadExactCensus P n d (padCtl X d (G φ)))

/-- **Claim (gate count of the width-rule census, constant policy).** For one table `T` used at
every width `≥ t`, if `T` passes the contract and the node width rule contracts like the PTP scan
(`wd T n ≤ n / k + k + growth ops`), the census total `ptpGateTotalD` is `O(n ^ log_k (3k - 2))`, whichever
negation method the policy is priced under (`oneQubit` or `scratch`; the constant may depend on the method).
(`Main.lean`: `ptp_gateTotal_bound`.) -/
def PTPGateTotalBound (t : ℕ) (T : PTPTable) (wd : WidthRule) : Prop :=
  T.contract = true →
  (∀ n, 0 < n → wd T n ≤ n / T.k + T.k + growth T.ops) →
    ∀ m : NegationMethod, ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (ptpGateTotalD ((constPTPPolicy t T).withNegation m) wd n : ℝ) ≤
        C * Real.rpow (n : ℝ) (ptpExponent T.k)

/-- **Claim (gate count of a constructed circuit, constant policy).** For a constant policy, under either
negation method, there is a circuit following it (a `PolicyImplX`, the family `PTPLowerExactCorrect` is about)
with at most `C · n ^ log_k (3k - 2)` gates, counted by the policy's resource model
(`PTPPolicy.resourceModel`: `shorGateResourceModel` for `oneQubit`, the same with the pre-swap negation for
`scratch`). The claim is existential: it does
not itself say the circuit is correct (that is `PTPLowerExactCorrect`), nor that it is the circuit
that claim produces. (`Main.lean`: `ptp_circuit_gateCount_bound`.) -/
def PTPCircuitGateCountBound (qs : QSemantics) [RegEncoding qs.Basis] [LowerGateClass qs]
    (t : ℕ) (T : PTPTable) : Prop :=
  T.contract = true → (constPTPPolicy t T).check = true →
    ∀ m : NegationMethod, ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ (X : Fin 3 → ExtReg) (base : ℕ), Good X n base →
      ∃ (W : List ℕ) (G : Angle → LowGate),
        PolicyImplX ((constPTPPolicy t T).withNegation m) X n W G ∧
        ∀ φ : Angle,
          ((LowGate.resources ((constPTPPolicy t T).withNegation m).resourceModel (G φ)).totalGates : ℝ) ≤
            C * Real.rpow (n : ℝ) (ptpExponent T.k)

/-- **Claim (tight qubit count, any admissible width rule).** There is a circuit following `P`
with node widths `wd` (existential: not tied to the circuit of `PTPLowerExactCorrect`) that touches at most `3 n + ptpWsTD P wd n` qubits, which is at most the
`ptpQubits`-shaped bound `3 n + 3 ptpReserveNeedD + max ptpCleanAncD 2`. This counts the qubits
the gates name (`LowGate.usedQubits`), not the framework's `qubitCount`, which adds the scratch
`cleanAnc`; that total is `PTPPeakQubits`. (`Main.lean`: `ptp_qubits_tight`.) -/
def PTPQubitsTight (P : PTPPolicy) (wd : WidthRule) (n : ℕ) (X : Fin 3 → ExtReg) (base : ℕ) : Prop :=
  P.check = true → Admissible P wd → Good X n base →
    ∃ (W : List ℕ) (G : Angle → LowGate), PolicyImplD P wd X n W G ∧
      ∀ φ, (LowGate.usedQubits (G φ)).card ≤ 3 * n + ptpWsTD P wd n ∧
        3 * n + ptpWsTD P wd n ≤
          3 * n + (3 * ptpReserveNeedD P wd n + max (ptpCleanAncD P wd n) 2)

/-- **Claim (tight qubit count, exact board).** As `PTPQubitsTight` at the exact rule, with
`ptpWsTD ≤ ptpWorkspaceX`. (`Main.lean`: `ptp_qubits_tight_exact`.) -/
def PTPQubitsTightExact (P : PTPPolicy) (n : ℕ) (X : Fin 3 → ExtReg) (base : ℕ) : Prop :=
  P.check = true → Good X n base →
    ∃ (W : List ℕ) (G : Angle → LowGate), PolicyImplX P X n W G ∧
      ∀ φ, (LowGate.usedQubits (G φ)).card ≤ 3 * n + ptpWsTD P exactRule n ∧
        ptpWsTD P exactRule n ≤ ptpWorkspaceX P n

/-- **Claim (`ptpQubits` is an upper bound, scan board).** There is a circuit following `P` at the
scan widths touching at most `ptpQubits P n` qubits. (`Main.lean`: `ptp_qubits_le_ptpQubits`.) -/
def PTPQubitsLePtpQubits (P : PTPPolicy) (n : ℕ) (X : Fin 3 → ExtReg) (base : ℕ) : Prop :=
  P.check = true → Good X n base →
    ∃ (W : List ℕ) (G : Angle → LowGate), PolicyImpl P X n W G ∧
      ∀ φ, (LowGate.usedQubits (G φ)).card ≤ ptpQubits P n

/-- The scan widths as a width rule: a node's children get `childWidth n T.ops`. (Proofs call it `scanRule`;
they are the same function.) -/
abbrev ptpScanWidth : WidthRule := fun T n => childWidth n T.ops

/-- **The single-product peak**: `3 n` for the three operand registers, `ptpWsTD` for the workspace qubits
the circuit names (the shared pool), and `ptpCleanAncD` for the clean scratch the resource model holds on top
of the named qubits (`1` under `oneQubit`, `C + 1` at the widest negating node under `scratch`). It is the
bound `PTPPeakQubits` proves on the framework's own `LowGate.qubitCount`. -/
def ptpPeakQubits (P : PTPPolicy) (wd : WidthRule) (n : ℕ) : ℕ :=
  3 * n + ptpWsTD P wd n + ptpCleanAncD P wd n

/-- **Claim (the single-product peak, any admissible width rule).** There is a circuit following `P` with node
widths `wd` whose framework qubit count `LowGate.qubitCount P.resourceModel` (the distinct qubits the gates name
plus the peak clean scratch, in the policy's own resource model, so under its negation method `P.negation`) is at
most `ptpPeakQubits P wd n = 3 n + ptpWsTD P wd n + ptpCleanAncD P wd n`. The two summands are bounded
separately, and both bounds are part of the claim: the named qubits by `3 n + ptpWsTD P wd n`, the scratch by
`ptpCleanAncD P wd n`. The claim is existential, like `PTPQubitsTight`: some circuit following the policy,
the one the construction builds, not every one; and an upper bound, not an equality. Unlike `ptpQubits` it is not
a bound shape of the form `max (ptpCleanAnc) 2` (the sandwich leaves' two ancillas are named qubits, so they count
in `ptpWsTD`, not in the scratch). (`Main.lean`: `ptp_peak_qubits`.) -/
def PTPPeakQubits (P : PTPPolicy) (wd : WidthRule) (n : ℕ) (X : Fin 3 → ExtReg) (base : ℕ) : Prop :=
  P.check = true → Admissible P wd → Good X n base →
    ∃ (W : List ℕ) (G : Angle → LowGate), PolicyImplD P wd X n W G ∧
      ∀ φ, (LowGate.usedQubits (G φ)).card ≤ 3 * n + ptpWsTD P wd n ∧
        (LowGate.resources P.resourceModel (G φ)).cleanAnc ≤ ptpCleanAncD P wd n ∧
        LowGate.qubitCount P.resourceModel (G φ) ≤ ptpPeakQubits P wd n

/-- **Claim (the single-product peak, exact board).** As `PTPPeakQubits` at the exact rule (`PolicyImplX`, the
family `PTPLowerExactCorrect` is about), with no admissibility hypothesis. (`Main.lean`: `ptp_peak_qubits_exact`.) -/
def PTPPeakQubitsExact (P : PTPPolicy) (n : ℕ) (X : Fin 3 → ExtReg) (base : ℕ) : Prop :=
  P.check = true → Good X n base →
    ∃ (W : List ℕ) (G : Angle → LowGate), PolicyImplX P X n W G ∧
      ∀ φ, (LowGate.usedQubits (G φ)).card ≤ 3 * n + ptpWsTD P exactRule n ∧
        (LowGate.resources P.resourceModel (G φ)).cleanAnc ≤ ptpCleanAncD P exactRule n ∧
        LowGate.qubitCount P.resourceModel (G φ) ≤ ptpPeakQubits P exactRule n

/-- **Claim (the single-product peak, scan board).** As `PTPPeakQubits` at the scan rule
(`PolicyImpl`), with no admissibility hypothesis; here `ptpWsTD` and `ptpCleanAncD` are at the scan rule.
(`Main.lean`: `ptp_peak_qubits_scan`.) -/
def PTPPeakQubitsScan (P : PTPPolicy) (n : ℕ) (X : Fin 3 → ExtReg) (base : ℕ) : Prop :=
  P.check = true → Good X n base →
    ∃ (W : List ℕ) (G : Angle → LowGate), PolicyImpl P X n W G ∧
      ∀ φ, (LowGate.usedQubits (G φ)).card ≤ 3 * n + ptpWsTD P ptpScanWidth n ∧
        (LowGate.resources P.resourceModel (G φ)).cleanAnc ≤ ptpCleanAnc P n ∧
        LowGate.qubitCount P.resourceModel (G φ) ≤ ptpPeakQubits P ptpScanWidth n

/-- **Claim (the peak against the `ptpQubits` formula, scan board).** For a checked policy,
`ptpPeakQubits P ptpScanWidth n ≤ ptpQubits P n + ptpCleanAnc P n`: the peak exceeds the formula
`ptpQubits` (`3 n + 3 ptpReserveNeed + max (ptpCleanAnc) 2`) by at most the scratch. It is a comparison of two
numbers, not a bound on a circuit; `ptpQubits` itself does not bound `qubitCount` (it counts the leaf ancillas
and the scratch as one `max`). (`Main.lean`: `ptp_peak_le_ptpQubits_add`.) -/
def PTPPeakLePtpQubitsAdd (P : PTPPolicy) (n : ℕ) : Prop :=
  P.check = true → ptpPeakQubits P ptpScanWidth n ≤ ptpQubits P n + ptpCleanAnc P n

/-- **Claim (the acceptance rule, without the ladder).** `chainContractsTight P n` holds iff every
table chosen at every width the exact recursion from `n` reaches has `k ≤ m` and strictly shrinks
the width. (`Main.lean`: `PTPPolicy.chainContractsTight_iff_reach`.) -/
def PTPChainContractsTightIffReach (P : PTPPolicy) (n : ℕ) : Prop :=
  P.chainContractsTight n = true ↔
    ∀ (m : ℕ) (T : PTPTable), P.ExactReach n m → P.choose m = some T →
      T.k ≤ m ∧ ptpTightWidth T m < m

end PTP
end Shor
