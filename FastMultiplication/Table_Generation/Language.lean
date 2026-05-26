import FastMultiplication.Table_Generation.Basic
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
-- /******************************************************************************/
-- /*                           PROGRAMS & EXECUTION CORE                        */
-- /******************************************************************************/

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

/-- Reverse the program and invert each operation. -/
def apply_Op_inverse {k : ℕ} (p : Prog k) : Prog k :=
  p.reverse.map Operations.inv

/-- Execute a program left→right. Fails if any right shift is inexact. -/
def run? {k : ℕ} : Prog k → State k → Option (State k)
| [],       σ => some σ
| op :: ps, σ =>
  match applyOp? σ op with
  | none    => none
  | some σ' => run? ps σ'





-- /******************************************************************************/
-- /*                     WELL-FORMEDNESS & SMALL CONSTRUCTORS                   */
-- /******************************************************************************/

namespace Prog

/-- An op is well-formed if it does not do an in-place scaled add. -/
def OpOK {k : ℕ} : valid_ops k → Prop
  | .addScaled dst src _ _ => dst ≠ src
  | _                      => True

/-- A program is well-formed if all its ops are `OpOK`. -/
def WellFormed {k : ℕ} (p : Prog k) : Prop :=
  ∀ op, op ∈ p → OpOK op

lemma apply_Op_inverse_preserves_WF {k} {p : Prog k} :
    Prog.WellFormed p → Prog.WellFormed (apply_Op_inverse p) := by
  intro wf op hop
  -- membership through `reverse.map`
  have : ∃ o, o ∈ p ∧ inv o = op := by
    -- map membership characterization
    -- op ∈ p.reverse.map inv  →  ∃o ∈ p.reverse, inv o = op → ∃o ∈ p
    revert hop
    simp [apply_Op_inverse, List.mem_map, List.mem_reverse]
  rcases this with ⟨o, ho, rfl⟩
  have hok := wf o ho
  -- `OpOK` is invariant under `inv`
  cases o <;> simp [Prog.OpOK, inv] at hok ⊢
  exact hok

/-- Singleton programs for each primitive (handy for notations). --/
def SHL   {k} (i : Fin k) (n : ℕ) : Prog k := [valid_ops.shiftL i n]
def SHR   {k} (i : Fin k) (n : ℕ) : Prog k := [valid_ops.shiftR i n]
def NEG   {k} (i : Fin k)           : Prog k := [valid_ops.negate i]
def ADD   {k} (dst src : Fin k) (shift : ℕ) : Prog k :=
  [valid_ops.addScaled dst src (negSrc := false) shift]
def SUB   {k} (dst src : Fin k) (shift : ℕ) : Prog k :=
  [valid_ops.addScaled dst src (negSrc := true) shift]

end Prog

-- /******************************************************************************/
-- /*      RUN THE PREFIX OF LENGTH t, WITH t < p.length ENFORCED BY THE TYPE    */
-- /******************************************************************************/

namespace Prog

/-- Execute exactly `t` steps of `p`, where `t < p.length` (so `t : Fin p.length`).
    This is just `run?` on the prefix `p.take t`. -/
def runAtStep? {k : ℕ} (p : Prog k) (t : Fin p.length) (σ : State k) : Option (State k) :=
  run? (p.take t.val) σ


end Prog

-- /******************************************************************************/
-- /*        CHECK THAT `phaseProduct` COVERS EXACTLY THE GIVEN POINT LIST       */
-- /******************************************************************************/

/-- User-supplied matcher: does the *current* state encode the desired
    interpolation polynomial at the given Point? Return `true` when it matches. -/
abbrev MatchesAt (k : Nat) := Register k → Point → Bool

/-- A richer matcher that can inspect the whole state and the destination register. -/
abbrev MatchesAtState (k : Nat) := State k → Fin k → Point → Bool


/-- Expected Vandermonde-style row for a point.
    - `.int z`  ↦  j ↦ z^j
    - `.inf`    ↦  unit vector at the last index (leading coeff selector) -/
def expectedRow {k : Nat} : Point → Register k
| .int z => fun j => (z : Int) ^ (j : Nat)
| .inf   =>
  match k with
  | 0     => fun j => nomatch j
  | k+1   =>
    let last : Fin (k+1) := ⟨k, by simp⟩
    fun j => if j = last then (1 : Int) else (0 : Int)

/-- Pointwise equality check between a register and `expectedRow pt`. -/
def regEqExpected {k : Nat} (r : Register k) (pt : Point) : Bool :=
  (List.finRange k).all (fun j => decide (r j = expectedRow (k := k) pt j))

/-- `MatchesAt` that recognizes whether a register encodes the correct
    interpolation *row* for the given `Point`. -/
def matchesAt_pointRow {k : Nat} : MatchesAt k :=
  fun r pt => regEqExpected (k := k) r pt

/-- Adapter from a register-only matcher to a state-aware matcher. -/
def MatchesAtState.ofRegister {k : Nat} (m : MatchesAt k) : MatchesAtState k :=
  fun σ i pt => m (σ i) pt

def matchesAt_pointRow_state {k : Nat} (_:k>0): MatchesAtState k :=
  fun σ i pt => regEqExpected (k := k) (σ i) pt


/-- Finite index `0 : Fin k` when `k > 0`. -/
def finZero {k : Nat} (hk : 0 < k) : Fin k := ⟨0, hk⟩

/-- A synthesis-friendly expected row: keep the basis `1` at `i`,
    and add `z^u` on every *other* coordinate.  For `.inf` we just reuse the
    original `expectedRow` so equivalence is trivial there. -/
def expectedRow2 {k : Nat} (i : Fin k) : Point → Register k
| .int z => fun u => (if u = i then (1 : Int) else 0)
                     + (if u ≠ i then (z : Int) ^ (u : Nat) else 0)
| .inf   => expectedRow (k := k) .inf

/-- Boolean row-check against `expectedRow2`. -/
def matchesAt_pointRow_state2 {k : Nat} : MatchesAtState k :=
  fun σ i pt =>
    (List.finRange k).all (fun u => decide (σ i u = expectedRow2 (k := k) i pt u))

/-- Bridge: the Bool for `matchesAt_pointRow_state2` is just pointwise equality. -/
@[simp] lemma matchesAt_pointRow_state2_true_iff
  {k : Nat} {σ : State k} {i : Fin k} {pt : Point} :
  matchesAt_pointRow_state2 (k := k) σ i pt = true
  ↔ ∀ u : Fin k, σ i u = expectedRow2 (k := k) i pt u := by
  classical
  unfold matchesAt_pointRow_state2
  -- standard `List.all`/`finRange` equivalence
  constructor
  · intro hall u
    have : decide (σ i u = expectedRow2 (k := k) i pt u) = true := by
      simp_all only [List.all_eq_true, List.mem_finRange, decide_eq_true_eq, forall_const, decide_true]
    simpa using (decide_eq_true_iff.mp this)
  · intro hpoint
    refine List.all_eq_true.mpr ?_
    intro u _; exact (decide_eq_true_iff.mpr (hpoint u))

/-- When `i` is the zero register, `expectedRow2` for `.int z` *equals*
    the original Vandermonde row. -/
@[simp] lemma expectedRow2_finZero_eq_expectedRow_int
  {k : Nat} (hk : 0 < k) (z : Int) :
  expectedRow2 (k := k) (finZero (k := k) hk) (.int z)
    = expectedRow (k := k) (.int z) := by
  funext u
  by_cases hu0 : u = finZero (k := k) hk
  · -- u = 0 : 1 + 0 = z^0
    subst hu0
    simp [expectedRow2, expectedRow, finZero, pow_zero]
  · -- u ≠ 0 : 0 + z^u = z^u
    simp [expectedRow2, expectedRow, finZero]
    unfold finZero at hu0
    simp[hu0]

/-- Consequently, at `i = finZero hk` the two matchers agree for `.int z`. -/
@[simp] lemma matchesAt_pointRow_state2_eq_state_at_finZero_int
  {k : Nat} (hk : 0 < k) (σ : State k) (z : Int) :
  matchesAt_pointRow_state2 (k := k) σ (finZero (k := k) hk) (.int z)
  = matchesAt_pointRow_state  (k := k) hk σ (finZero (k := k) hk) (.int z) := by
  classical
  unfold matchesAt_pointRow_state matchesAt_pointRow_state2
  -- pointwise equality of the targets inside `all (decide …)`
  have H : (fun u => decide (σ (finZero hk) u
                  = expectedRow2 (k := k) (finZero hk) (.int z) u))
         = (fun u => decide (σ (finZero hk) u
                  = expectedRow (k := k) (.int z) u)) := by
    funext u
    simp [expectedRow2_finZero_eq_expectedRow_int (k := k) hk z]
  simp_all only [expectedRow2_finZero_eq_expectedRow_int]
  rfl





namespace List
/-- Remove the *first* element satisfying `p`; return `none` if nothing matches. -/
def eraseFirstMatch? {α} (p : α → Bool) : List α → Option (List α)
| []       => none
| x :: xs  =>
  if p x then
    some xs
  else
    (eraseFirstMatch? p xs).map (fun ys => x :: ys)
end List


def phaseCoverageFrom? {k : ℕ}
    (matchesAt : MatchesAt k)
    (p        : Prog k)
    (σ0       : State k)
    (pts0     : List Point) : Bool :=

  let rec loop (ops : Prog k) (σ : State k) (todo : List Point) :
      Option (List Point) :=
    match ops with
    | [] => some todo
    | op :: rest =>
      match op with
      | valid_ops.phaseProduct i =>
          -- Must match *some* remaining point and remove it.
          let x:=List.eraseFirstMatch? (fun pt => matchesAt (σ i) pt) todo
          match x with
          | none       => none
          | some todo' => loop rest σ todo'
      | _ =>
          -- Normal step: advance state (may fail on inexact SHR).
          match applyOp? σ op with
          | none     => none
          | some σ'  => loop rest σ' todo

  match loop p σ0 pts0 with
  | some [] => true
  | _       => false

def phaseProduct_coverage_check {k : ℕ}
    (p        : Prog k)
    (σ0       : State k)
    (pts0     : List Point) : Bool :=
    phaseCoverageFrom? (matchesAt_pointRow (k := k)) p σ0 pts0




-- /******************************************************************************/
-- /*                                NOTATIONS                                   */
-- /******************************************************************************/

--(shift left)
syntax:70 term:71 " <<s= " term:70 : term
macro_rules
  | `($i <<s= $n) => `(Prog.SHL $i $n)

-- (shift right)
syntax:70 term:71 " >>s= " term:70 : term
macro_rules
  | `($i >>s= $n) => `(Prog.SHR $i $n)

-- neg i
syntax:70 "neg " term:70 : term
macro_rules
  | `(neg $i) => `(Prog.NEG $i)

-- dst +:= src << n
syntax:70 term:71 " +:= " term:71 " << " term:70 : term
macro_rules
  | `($dst +:= $src << $n) => `(Prog.ADD $dst $src $n)

-- dst -:= src << n
syntax:70 term:71 " -:= " term:71 " << " term:70 : term
macro_rules
  | `($dst -:= $src << $n) => `(Prog.SUB $dst $src $n)

infixl:55 " ;; " => List.append





-- /******************************************************************************/
-- /*                                  EXAMPLES                                  */
-- /******************************************************************************/

section Examples
set_option linter.unusedVariables false

variable {k : ℕ} (σ0 : State 4)
def r0 : Fin 4 := ⟨0, by decide⟩
def r1 : Fin 4 := ⟨1, by decide⟩

/-- A small program: r0 +:= r1 << 2 ;; r0 >>s= 1 ;; neg r1 -/
def demoProg : Prog 4 := (r0 +:= r1 << 2) ;; (r0 >>s= 1) ;; (neg r1)

end Examples







-- /******************************************************************************/
-- /*                  INVERSE OF APPEND (TOP-LEVEL VERSION)                     */
-- /******************************************************************************/

@[simp] theorem apply_Op_inverse_append {k : ℕ} (p q : Prog k) :
    apply_Op_inverse ((p;;q)) = apply_Op_inverse q ;; apply_Op_inverse p := by
  unfold apply_Op_inverse
  -- reverse (p ++ q) = reverse q ++ reverse p; then `map` distributes over `++`
  simp [List.reverse_append, List.map_append]


-- /******************************************************************************/
-- /*                     LIGHTWEIGHT PROGRAM EQUIVALENCE                        */
-- /******************************************************************************/

-- Two programs are equivalent if they produce the same (optional) state on all inputs.
def ProgEq {k : ℕ} (p q : Prog k) : Prop :=
  ∀ σ, run? p σ = run? q σ

notation:50 p:51 " ≃ₚ " q:50 => ProgEq p q



-- /******************************************************************************/
-- /*        CHECK THAT `phaseProduct` COVERS EXACTLY THE GIVEN POINT LIST       */
-- /******************************************************************************/


inductive PhaseProductCoverageM {k : ℕ} (M : MatchesAtState k) :
    Prog k → State k → List Operations.Point → Prop
| nil {σ : State k} :
    PhaseProductCoverageM M [] σ []
| step_op {op : Operations.valid_ops k} {ps : Prog k} {σ τ : State k} {pts : List Operations.Point}
    (hops  : ∀i, ¬ op = valid_ops.phaseProduct i)
    (hstep : applyOp? (k := k) σ op = some τ)
    (hrest : PhaseProductCoverageM M ps τ pts) :
    PhaseProductCoverageM M (op :: ps) σ pts
| step_phase {i : Fin k} {ps : Prog k} {σ : State k} {pts pts' : List Operations.Point}
    (hconsume : List.eraseFirstMatch? (fun pt => M σ i pt) pts = some pts')
    (hrest : PhaseProductCoverageM M ps σ pts') :
    PhaseProductCoverageM M (valid_ops.phaseProduct i :: ps) σ pts

def PhaseProductCoverage {k : ℕ} (hk:k>0):
    Prog k → State k → List Operations.Point → Prop:=
    PhaseProductCoverageM (k := k) (matchesAt_pointRow_state (k := k) hk)


-- inductive PhaseProductCoverageM2 {k : ℕ} (M : MatchesAtState k) :
--     Prog k → State k → List Operations.Point → Prop
-- | nil {σ : State k} :
--     PhaseProductCoverageM2 M [] σ []
-- | step_op {op : Operations.valid_ops k} {ps : Prog k} {σ τ : State k} {pts : List Operations.Point}
--     (hops  : ∀i, ¬ op = valid_ops.phaseProduct i)
--     (hstep : applyOp? (k := k) σ op = some τ)
--     (hrest : PhaseProductCoverageM2 M ps τ pts) :
--     PhaseProductCoverageM2 M (op :: ps) σ pts
-- | step_phase {i : Fin k} {ps : Prog k} {σ : State k} {pts pts' : List Operations.Point}
--     (hconsume : List.eraseFirstMatch? (fun pt => M σ i pt) pts = some pts')
--     (hrest : PhaseProductCoverageM2 M ps σ pts') :
--     PhaseProductCoverageM2 M (valid_ops.phaseProduct i :: ps) σ pts


-- def PhaseProductCoverage2 {k : ℕ} (hk:k>0):
--     Prog k → State k → List Operations.Point → Prop:=
--     PhaseProductCoverageM2 (k := k) (matchesAt_pointRow_state (k := k) hk)

namespace PhaseProductCoverage
