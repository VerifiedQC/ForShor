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

/-- Your interpolation target function. -/
def interpTarget (σ0 : St 3) : Operations.Point → Option Int
  | Operations.Point.inf => some (x2 σ0)
  | Operations.Point.int z =>
      if z = 0 then
        some (x0 σ0)
      else if z = 1 then
        some (x0 σ0 + x1 σ0 + x2 σ0)
      else if z = (-1) then
        some (x0 σ0 - x1 σ0 + x2 σ0)
      else
        none

/--
Matcher: `M σ i pt` is true iff register `i` currently equals the interpolation target for `pt`,
computed from the *initial* state `σ0`.
-/
def matchesAt_interp (σ0 : St 3) : St 3 → Fin 3 → Operations.Point → Bool :=
  fun σ i pt =>
    match interpTarget σ0 pt with
    | none => false
    | some t => decide (regToInt (σ i) = t)

#eval phaseProductCoverage? (k := 3) (matchesAt_interp demo) DemoValidOps.pop1 demo [Point.int 0, Point.inf, Point.int 1, Point.int (-1)]
