import Mathlib.Data.Int.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
# What a Toom-Cook table is, and what makes one admissible

`SUBMISSION_PLAN.md` P8/S2.0. This file is the *rules* of the submission
challenge: the minimal vocabulary needed to state `Shor.ShorLoweringSetup`,
plus the record itself. It imports Mathlib and nothing else — no compiler, no
plan builders, no generator, no proofs — so a submissions repo can read the
specification without reading the implementation that satisfies it.

A submission is a Toom-Cook table: an arithmetic program `ops : Prog k` over
`k` limb registers, together with the interpolation points `pts` its
`phaseProduct` checkpoints evaluate at. Four side conditions make the pair
admissible, all decidable at a concrete `k`, `ops`, `pts`
(`Submission/Decide.lean`):

| | condition | meaning |
|---|---|---|
| C1 | `pts.length = q k` (`= 2k - 1`) | one point per product coefficient |
| C2 | `GoodToomCookPoints k pts hpts` | `det (interpMatrix …) ≠ 0`: the points interpolate a degree-`2k-2` polynomial. The row for `int z` is `[1, z, …, z^(2k-2)]`; `frac c` means the point `1/c`, row `[c^(2k-2), …, c, 1]`; `frac 0` is the point at infinity |
| C3 | `ProgConsumesPtsSafe … ops pts` | running `ops` from `State.start_state`, the `i`-th `phaseProduct r` checkpoint finds register `r` holding exactly the `k`-entry row of `pts[i]`, all points are consumed, and no `addScaled` has `dst = src`. **Order matters**: leaf `l` receives coefficient `l` |
| C4 | `run? ops State.start_state = some State.start_state` | the table uncomputes itself; every right shift is exact |

Everything here was moved verbatim from `Implementation/` (the tables in
`SUBMISSION_PLAN.md` §6 say from where) and keeps its fully-qualified name,
so no use site changed except for an added import. The lemmas about these
definitions, the point generator, the compiler and the correctness proofs all
stayed behind and import this file back.
-/

/-! =========================================================
    Registers and states (`Table_Generation/Core/Registers.lean`)
========================================================= -/

/-- A register is a linear combo of `x₀,…,x_{k-1}` with **integer** coefficients. -/
abbrev Register (k : ℕ) := Fin k → ℤ

/-- A state is `k` registers. -/
abbrev State (k : ℕ) := Fin k → Register k

namespace Register

/-- Zero register. -/
def zero (k : ℕ) : Register k := fun _ => 0

/-- Negate all coefficients in a register. -/
def negate {k : ℕ} (r : Register k) : Register k :=
  fun j => - (r j)

/-- Left shift every coefficient by `n` (multiply by `2^n`). -/
def shiftL {k : ℕ} (r : Register k) (n : ℕ) : Register k :=
  fun j => (r j) * (2 : ℤ) ^ n

/-- Right shift every coefficient by `n`, **iff each coeff is divisible by `2^n`**.
    Returns `none` if any coefficient would be fractional. -/
def shiftR? {k : ℕ} (r : Register k) (n : ℕ) : Option (Register k) :=
  let m : ℤ := (2 : ℤ) ^ n
  if ∀ j, (r j) % m = 0 then
    some (fun j => (r j) / m)
  else
    none

/-- `dst ← dst + (±1) * (src << shift)` (no implicit right shifts). -/
def addScaled {k : ℕ} (dst src : Register k) (negSrc : Bool) (shift : ℕ) : Register k :=
  let sgn : ℤ := if negSrc then -1 else 1
  fun j => (dst j) + sgn * (src j) * (2 : ℤ) ^ shift

end Register

namespace State
open Register

/-- Basis state: register `i` = `x_i`. -/
def start_state {k : ℕ} : State k :=
  fun i => fun j => if j = i then (1 : ℤ) else 0

/-- Overwrite register `i`. -/
def setReg {k : ℕ} (σ : State k) (i : Fin k) (r : Register k) : State k :=
  fun j => if j = i then r else σ j

/-- Negate register `i`. -/
def negateReg {k : ℕ} (σ : State k) (i : Fin k) : State k :=
  setReg σ i (Register.negate (σ i))

/-- Left shift register `i` by `n`. -/
def shiftLReg {k : ℕ} (σ : State k) (i : Fin k) (n : ℕ) : State k :=
  setReg σ i (Register.shiftL (σ i) n)

/-- Right shift register `i` by `n` *iff* all coeffs are divisible by `2^n`. -/
def shiftRReg? {k : ℕ} (σ : State k) (i : Fin k) (n : ℕ) : Option (State k) := do
  let r' ← Register.shiftR? (σ i) n
  pure (setReg σ i r')

/-- `dst ← dst + (±1) * (src << shift)`. -/
def addScaledReg {k : ℕ} (σ : State k)
    (dst src : Fin k) (negSrc : Bool) (shift : ℕ) : State k :=
  setReg σ dst (Register.addScaled (σ dst) (σ src) negSrc shift)

end State

/-! =========================================================
    The operation language (`Table_Generation/Core/Registers.lean`)
========================================================= -/

namespace Operations

inductive Point where
  | int  (z : Int)
  | frac (m : Int)
deriving Repr, DecidableEq

/-- Valid operations on registers. -/
inductive valid_ops (k : ℕ) where
  | shiftL    (i : Fin k) (n : ℕ)
  | shiftR    (i : Fin k) (n : ℕ)
  | negate    (i : Fin k)
  | addScaled (dst src : Fin k) (negSrc : Bool) (shift : ℕ)
  | phaseProduct (i : Fin k)

end Operations

/-! =========================================================
    Programs and execution, C4 (`Table_Generation/Core/Language.lean`)
========================================================= -/

open Operations

/-- A program is just a list of valid operations. -/
abbrev Prog (k : ℕ) := List (valid_ops k)

/-- Execute one operation. Right shift may fail if division is inexact. -/
def applyOp? {k : ℕ} (σ : State k) : valid_ops k → Option (State k)
| .shiftL i n           => some (State.shiftLReg σ i n)
| .shiftR i n           => State.shiftRReg? σ i n
| .negate i             => some (State.negateReg σ i)
| .addScaled i j s sh   => some (State.addScaledReg σ i j s sh)
| .phaseProduct _       => some σ

/-- Execute a program left→right. Fails if any right shift is inexact. -/
def run? {k : ℕ} : Prog k → State k → Option (State k)
| [],       σ => some σ
| op :: ps, σ =>
  match applyOp? σ op with
  | none    => none
  | some σ' => run? ps σ'

/-! =========================================================
    Point rows and ordered consumption, C3
    (`Core/Language.lean`, `Core/Coverage.lean`)
========================================================= -/

/-- A matcher that can inspect the whole state and the destination register. -/
abbrev MatchesAtState (k : Nat) := State k → Fin k → Point → Bool

/--
The integral row stored for an interpolation point.

For `int z`, this is `[1, z, z², ..., z^(k-1)]`.

For `frac m`, representing `1/m`, this is the rescaled row

  `m^(k-1) * [1, 1/m, ..., 1/m^(k-1)]`

namely `[m^(k-1), m^(k-2), ..., m, 1]`.

At `m = 0`, this becomes the leading-coefficient selector.
-/
def expectedRow {k : Nat} : Point → Register k
| .int z  => fun j => z ^ j.val
| .frac m => fun j => m ^ (k - 1 - j.val)

/-- Pointwise equality check between a register and `expectedRow pt`. -/
def regEqExpected {k : Nat} (r : Register k) (pt : Point) : Bool :=
  (List.finRange k).all (fun j => decide (r j = expectedRow (k := k) pt j))

def matchesAt_pointRow_state {k : Nat} (_:k>0): MatchesAtState k :=
  fun σ i pt => regEqExpected (k := k) (σ i) pt

/-- Ordered point consumption for a program with `phaseProduct` checkpoints.
    Unlike `PhaseProductCoverage`, this proposition consumes the supplied points
    from left to right. -/
def ProgConsumesPts {k : ℕ} (hk : k > 0) : State k → Prog k → List Point → Prop
| _σ, [], pts => pts = []
| σ, op :: ops, pts =>
  match op with
  | valid_ops.phaseProduct i =>
      ∃ pt ptsTail,
        pts = pt :: ptsTail ∧
        matchesAt_pointRow_state (k := k) hk σ i pt = true ∧
        ProgConsumesPts hk σ ops ptsTail
  | _ =>
      ∃ σ', applyOp? (k := k) σ op = some σ' ∧
            ProgConsumesPts hk σ' ops pts

def SafeProg {k : ℕ} (ops : Prog k) : Prop :=
  ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
    ops = pre ++ valid_ops.addScaled d s negSrc sh :: rest →
      d ≠ s

structure ProgConsumesPtsSafe {k : ℕ} (hk : k > 0) (σ : State k) (ops : Prog k) (pts : List Point) : Prop where
  consumes : ProgConsumesPts hk σ ops pts
  safe_add : SafeProg ops

/-! =========================================================
    Interpolation, C1 and C2
    (`Math/ToomCook.lean`, `Compiler/Coefficients.lean`)
========================================================= -/

namespace ToomCookMath

universe u

/-- Convert a list of length `m` into a `Fin m`-indexed function. -/
def listToFin {α : Type u} {m : ℕ} (pts : List α) (hpts : pts.length = m) : Fin m → α :=
  fun i => pts.get ⟨i.1, by simp [hpts]⟩

def interpMatrix {Point : Type u} {m : ℕ} (row : Point → Fin m → ℚ) (pts : Fin m → Point) :
    Matrix (Fin m) (Fin m) ℚ :=
  fun i j => row (pts i) j

def GoodInterpolationPoints {Point : Type u} {m : ℕ} (row : Point → Fin m → ℚ)
    (pts : Fin m → Point) : Prop :=
  Matrix.det (interpMatrix row pts) ≠ 0

end ToomCookMath

namespace Shor
open Operations

/-- Number of interpolation points used for radix-`k` phase decomposition. -/
def q (k : ℕ) : ℕ := 2 * k - 1

/-- One entry of the interpolation matrix. -/
def interpEntry (k : ℕ) (p : Point) (j : Fin (q k)) : ℚ :=
  match p with
  | .int z =>
      (z : ℚ) ^ (j : ℕ)
  | .frac c =>
      (c : ℚ) ^ (q k - 1 - (j : ℕ))

def GoodToomCookPoints (k : ℕ) (pts : List Point) (hpts : pts.length = q k) : Prop :=
  ToomCookMath.GoodInterpolationPoints (row := interpEntry k) (pts := ToomCookMath.listToFin pts hpts)

/-! =========================================================
    The submission (`Implementation/Shor/Spec/Setup.lean`)
========================================================= -/

/-- Low-level lowering assumptions shared by lowered Shor statements — and,
since `SUBMISSION_PLAN.md` P1/P7, exactly what a submission *is*: the table
(`ops`), the points it evaluates at (`pts`), and the four conditions C1–C4
relating them. -/
structure ShorLoweringSetup where
  /-- Number of synthesis registers used by the lowering program. -/
  k : ℕ
  /-- At least two synthesis registers are available. -/
  hk : 1 < k
  /-- Interpolation points the submission's table is built against. -/
  pts : List Point
  /-- One point per product coefficient. (C1) -/
  hpts : pts.length = q k
  /-- The chosen points interpolate a degree-`2k - 2` polynomial. (C2) -/
  good : GoodToomCookPoints k pts hpts
  /-- Program that consumes the interpolation points used by lowering. -/
  ops : Prog k
  /-- The point-consuming program is safe. (C3) -/
  consumes :
    ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops pts
  /-- The point-consuming program uncomputes back to the start state. (C4) -/
  returns : run? ops State.start_state = some State.start_state

/-- The submitter-facing spelling of `ShorLoweringSetup`. The same record: a
submission is the table plus its proofs, not a data-only wrapper a checker
converts (`SUBMISSION_PLAN.md` P7). -/
abbrev ShorSubmission := ShorLoweringSetup

end Shor
