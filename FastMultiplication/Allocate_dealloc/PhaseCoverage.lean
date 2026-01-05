import FastMultiplication.Allocate_dealloc.Basic

open Operations

/-- Bool-valued matcher (so everything is computable). -/
abbrev MatchesAtStateBit (k : ℕ) := St k → Fin k → Operations.Point → Bool

/-- Remove the first element satisfying a Bool predicate; fail if none. -/
def eraseFirstMatchB {α : Type} (p : α → Bool) : List α → Option (List α)
  | []      => none
  | x :: xs =>
      if p x then
        some xs
      else
        match eraseFirstMatchB p xs with
        | none      => none
        | some xs'  => some (x :: xs')

/--
Run the “coverage checker”:
- returns `none` if a phaseProduct cannot consume a matching point
- otherwise returns `some (finalState, remainingPts)`
-/
def runPhaseCoverage {k : ℕ} (M : MatchesAtStateBit k) :
    List (prim_ops k) → St k → List Operations.Point → Option (St k × List Operations.Point)
  | [], σ, pts => some (σ, pts)
  | op :: ps, σ, pts =>
      match op with
      | prim_ops.phaseProduct i =>
          match eraseFirstMatchB (fun pt => M σ i pt) pts with
          | none      => none
          | some pts' => runPhaseCoverage M ps σ pts'
      | _ =>
          -- your semantics are total, so we always step
          let σ' := eval_prim_op_single (k := k) op σ
          runPhaseCoverage M ps σ' pts

/-- Bool check: true iff all points get consumed by phaseProduct steps. -/
def phaseProductCoverage? {k : ℕ} (M : MatchesAtStateBit k)
    (prog : List (prim_ops k)) (σ : St k) (pts : List Operations.Point) : Bool :=
  match runPhaseCoverage (k := k) M prog σ pts with
  | some (_, []) => true
  | _            => false

/-- Prop version (often nicer to use in theorems). -/
def PhaseProductCoverage_Bit {k : ℕ} (M : MatchesAtStateBit k)
    (prog : List (prim_ops k)) (σ : St k) (pts : List Operations.Point) : Prop :=
  ∃ τ, runPhaseCoverage (k := k) M prog σ pts = some (τ, [])


/-- Signed (two’s-complement) value stored in a `Reg`. -/
def regToInt (r : Reg) : Int :=
  match r with
  | ⟨_, bv⟩ => BitVec.toInt bv

/-- Convenient names for Fin 3 indices. -/
def f0 : Fin 3 := ⟨0, by decide⟩
def f1 : Fin 3 := ⟨1, by decide⟩
def f2 : Fin 3 := ⟨2, by decide⟩

/-- Extract the initial x0,x1,x2 from the *initial* state. -/
def x0 (σ0 : St 3) : Int := regToInt (σ0 f0)
def x1 (σ0 : St 3) : Int := regToInt (σ0 f1)
def x2 (σ0 : St 3) : Int := regToInt (σ0 f2)

-- /-- Your interpolation target function. -/
-- def interpTarget (σ0 : St 3) : Operations.Point → Option Int
--   | Operations.Point.inf => some (x2 σ0)
--   | Operations.Point.int z =>
--       if z = 0 then
--         some (x0 σ0)
--       else if z = 1 then
--         some (x0 σ0 + x1 σ0 + x2 σ0)
--       else if z = (-1) then
--         some (x0 σ0 - x1 σ0 + x2 σ0)
--       else
--         none

-- /--
-- Matcher: `M σ i pt` is true iff register `i` currently equals the interpolation target for `pt`,
-- computed from the *initial* state `σ0`.
-- -/
-- def matchesAt_interp (σ0 : St 3) : St 3 → Fin 3 → Operations.Point → Bool :=
--   fun σ i pt =>
--     match interpTarget σ0 pt with
--     | none => false
--     | some t => decide (regToInt (σ i) = t)
open Operations



/-- Read register `n` from the *initial* state, if `n < k`. -/
def coeff {k : ℕ} (σ0 : St k) (n : Nat) : Option Int :=
  if h : n < k then
    some (regToInt (σ0 ⟨n, h⟩))
  else
    none

/-- Evaluate Σ_{j=0}^{k-1} (w^j * x_j) where x_j are the *initial* register values from σ0. -/
def polyEvalFromInit {k : Nat} (σ0 : St k) (w : Int) : Int :=
  ∑ j : Fin k, (w ^ (j : Nat)) * regToInt (σ0 j)

/-- Last index (k-1) when k>0. -/
def lastFin : (k : Nat) → Option (Fin k)
  | 0     => none
  | k+1   => some ⟨k, by simp⟩

/-- Interpolation target computed from the *initial* state σ0, for any k. -/
def interpTarget {k : Nat} (σ0 : St k) : Operations.Point → Option Int
  | Operations.Point.int z => some (polyEvalFromInit (k := k) σ0 z)
  | Operations.Point.inf   =>
      match lastFin k with
      | none      => none
      | some last => some (regToInt (σ0 last))

/--
Matcher for phase coverage:
`true` iff the *current* register `i` equals the interpolation target for `pt`,
where the target is computed from the *initial* coefficients in `σ0`.
-/
def matchesAt_interp {k : Nat} (σ0 : St k) : St k → Fin k → Operations.Point → Bool :=
  fun σ i pt =>
    match interpTarget (k := k) σ0 pt with
    | none   => false
    | some t => decide (regToInt (σ i) = t)

def eg_pts_0:=[Point.int 0, Point.inf, Point.int 1, Point.int (-1), Point.int 2, Point.int (-2)]
#eval phaseProductCoverage? (k := 3) (matchesAt_interp demo) DemoValidOps.pop1 demo eg_pts_0

def regOfInt (w : Nat) (n : Int) : Reg :=
  ⟨w, BitVec.ofInt w n⟩

def demoσ0 : St 5 :=
  let w := 6
  fun i =>
    match i.val with
    | 0 => regOfInt w  1
    | 1 => regOfInt w  3
    | 2 => regOfInt w (5)
    | 3 => regOfInt w  6
    | _ => regOfInt w  2  -- only remaining case is 4

lemma hk (k:ℕ) (h1:k≠0):0<k:=by omega

def eg_pts_1:=[Point.int 0, Point.inf, Point.int 1, Point.int (-1), Point.int 2, Point.int (-2), Point.int (3)]
def vop_1:=(genOpsWithProduct (hk 5 (by simp)) eg_pts_1)
def pop_1:=compile_valid_ops vop_1

#eval phaseProductCoverage? (k := 5) (matchesAt_interp demoσ0) pop_1 demoσ0 eg_pts_1
