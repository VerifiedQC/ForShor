import FastMultiplication.Basic
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
-- /*                      BASIC FACTS ABOUT INVERSE PROGRAMS                    */
-- /******************************************************************************/

@[simp] theorem apply_Op_inverse_involutive {k : ℕ} (p : Prog k) :
    apply_Op_inverse (apply_Op_inverse p) = p := by
  unfold apply_Op_inverse
  -- (rev.map inv).rev.map inv  →  p.rev.rev.map (inv ∘ inv)
  simp
  have : (inv∘inv) =( fun (x:valid_ops k)=>x):= by {
    unfold inv
    funext x
    cases x
    all_goals simp
  }
  rw[this]
  simp


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

def matchesAt_pointRow_state {k : Nat} : MatchesAtState k :=
  fun σ i pt => regEqExpected (k := k) (σ i) pt



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
-- /*                          BASIC `run?` SIMP LEMMAS                          */
-- /******************************************************************************/

@[simp] lemma run?_nil {k} (σ : State k) :
  run? ([] : Prog k) σ = some σ := rfl

@[simp] lemma run?_cons {k} (op : valid_ops k) (ps : Prog k) (σ : State k) :
  run? (op :: ps) σ =
    match applyOp? σ op with
    | none    => none
    | some σ' => run? ps σ' := rfl

lemma run?_append {k} (p q : Prog k) (σ : State k) :
  run? (p ++ q) σ =
    match run? p σ with
    | none    => none
    | some σ' => run? q σ' := by
  induction p generalizing σ with
  | nil => simp [run?]
  | cons op ps IH =>
      simp [run?, IH]
      cases (applyOp? σ op)
      simp
      simp

/- Single-step characterizations (good for rewriting) -/
@[simp] lemma run?_one_shiftL {k} (σ : State k) (i : Fin k) (n : ℕ) :
  run? ([valid_ops.shiftL i n] : Prog k) σ = some (State.shiftLReg σ i n) := rfl

@[simp] lemma run?_one_shiftR {k} (σ : State k) (i : Fin k) (n : ℕ) :
  run? ([valid_ops.shiftR i n] : Prog k) σ = State.shiftRReg? σ i n := by {
    simp
    unfold applyOp?
    simp
    cases σ.shiftRReg? i n
    simp
    simp
  }

@[simp] lemma run?_one_neg {k} (σ : State k) (i : Fin k) :
  run? ([valid_ops.negate i] : Prog k) σ = some (State.negateReg σ i) := rfl

@[simp] lemma run?_one_addScaled {k} (σ : State k)
    (dst src : Fin k) (negSrc : Bool) (n : ℕ) :
  run? ([valid_ops.addScaled dst src negSrc n] : Prog k) σ
    = some (State.addScaledReg σ dst src negSrc n) := rfl

/- Notation-specific simp helpers (these use the macros) -/
@[simp] lemma run?_shl_notation {k} (σ : State k) (i : Fin k) (n : ℕ) :
  run? (i <<s= n) σ = some (State.shiftLReg σ i n) := rfl

@[simp] lemma run?_shr_notation {k} (σ : State k) (i : Fin k) (n : ℕ) :
  run? (i >>s= n) σ = State.shiftRReg? σ i n := by {
    unfold run? Prog.SHR applyOp?
    simp
    cases σ.shiftRReg? i n
    all_goals simp
  }

@[simp] lemma run?_neg_notation {k} (σ : State k) (i : Fin k) :
  run? (neg i) σ = some (State.negateReg σ i) := rfl

@[simp] lemma run?_add_notation {k} (σ : State k)
  (dst src : Fin k) (n : ℕ) :
  run? (dst +:= src << n) σ
    = some (State.addScaledReg σ dst src (negSrc := false) n) := rfl

@[simp] lemma run?_sub_notation {k} (σ : State k)
  (dst src : Fin k) (n : ℕ) :
  run? (dst -:= src << n) σ
    = some (State.addScaledReg σ dst src (negSrc := true) n) := rfl


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

/-- Convenience single-instruction constructor for `phaseProduct`. -/


-- /******************************************************************************/
-- /*                 A SAMPLE PROGRAM & ITS COVERAGE PROOF                      */
-- /******************************************************************************/

def example_prog_1:Prog 3:=
  [valid_ops.phaseProduct 0] ;;
  [valid_ops.phaseProduct 2] ;;
  (1 +:= 0 << 0) ;;
  1+:= 2 << 0 ;;
  [valid_ops.phaseProduct 1]


theorem example_prog_1_phase_converage:
  phaseProduct_coverage_check example_prog_1 State.start_state [Point.int 0,Point.inf,Point.int 1]:=by {
    unfold phaseProduct_coverage_check phaseCoverageFrom? phaseCoverageFrom?.loop example_prog_1 List.eraseFirstMatch? matchesAt_pointRow regEqExpected State.start_state expectedRow List.eraseFirstMatch?
    simp
    have :(∀ (x : Fin 3), x ∈ List.finRange 3 → ((if x = 0 then (1:ℤ) else 0) = 0 ^ x.val))=true:=by {
      simp
      intro x
      split_ifs with h
      simp[h]
      fin_cases x<;>simp_all
    }
    split_ifs with h
    simp [Fin.isValue]
    rfl
    · simp at h
      simp at this
      exfalso
      rcases h with ⟨x, hxne⟩
      simp_all
    · simp_all
  }


/-- Program for the k=3 (regs 0,1,2). -/
def example_prog_2 : Prog 3 :=
  (1 +:= 2 << 0) ;;
  (1 +:= 0 << 0) ;;
  -- Product on all registers
  [valid_ops.phaseProduct 0] ;;
  [valid_ops.phaseProduct 1] ;;
  [valid_ops.phaseProduct 2] ;;

  (neg 1) ;;
  (1 +:= 0 << 0) ;;
  (1 +:= 2 << 1) ;;
  (0 +:= 1 << 0) ;;
  (1 +:= 0 << 0) ;;
  (1 +:= 2 << 1) ;;
  -- Product on regs. 1 and 0
  [valid_ops.phaseProduct 1] ;;
  [valid_ops.phaseProduct 0] ;;

  (neg 1) ;;
  (1 +:= 2 << 1) ;;
  (0 <<s= 1) ;; (0 +:= 1 << 0) ;;
  (1 +:= 0 << 0) ;;
  (1 +:= 2 << 1) ;;
  (1 >>s= 1)

def example_prog_3 : Prog 4 :=
  (1 +:= 3 << 0) ;;
  (1 +:= 2 << 0) ;;
  (1 +:= 0 << 0) ;;
  -- Product on all registers
  [valid_ops.phaseProduct 0] ;;
  [valid_ops.phaseProduct 1] ;;
  [valid_ops.phaseProduct 3] ;;

  (1 -:= 0 << 0) ;;
  (1 -:= 2 << 0) ;;
  (1 -:= 3 << 0) ;;
  (0 -:= 1 << 0) ;;
  (0 +:= 2 << 0) ;;
  (0 -:= 3 << 0) ;;
  [valid_ops.phaseProduct 0] ;;
  (0 +:= 3 << 0) ;;
  (0 -:= 2 << 0) ;;
  (0 +:= 1 << 0)



lemma x_fin_checker(k:ℕ)(hk:k>0): (∀ (x : Fin k), x ∈ List.finRange k → ((if x = (Fin.mk 0 (by simp[hk])) then (1:ℤ) else 0) = 0 ^ x.val))=true:=by {
  simp
  intro x
  split_ifs with h
  simp[h]
  have hx0 : (x : ℕ) ≠ 0 := by
    intro hx
    apply h
    apply Fin.ext
    simpa using hx
  obtain ⟨n, h⟩ := Nat.exists_eq_succ_of_ne_zero hx0
  simp[h]
}

theorem example_prog_2_phase_converage:
  phaseProduct_coverage_check example_prog_2 State.start_state [Point.int 0,Point.inf,Point.int 1,Point.int (-1),Point.int (-2)]:=by {
    simp[phaseProduct_coverage_check,phaseCoverageFrom?,phaseCoverageFrom?.loop,example_prog_2,List.eraseFirstMatch?,matchesAt_pointRow,regEqExpected,State.start_state,expectedRow,List.eraseFirstMatch?,Prog.ADD,applyOp?,phaseCoverageFrom?.loop,State.addScaledReg,State.setReg, Register.addScaled]
    have := x_fin_checker 3 (by simp)
    split_ifs with h
    rfl
    all_goals simp_all
  }


-- /******************************************************************************/
-- /*                 TACTIC FOR VERIFYING PHASEPRODUCT COVERGE                  */
-- /******************************************************************************/

open Lean Meta Elab Tactic

-- Custom tactic
elab "prove_coverage" n:num : tactic => do
  let nVal := n.getNat

  -- We will build the sequence of tactics as syntax
  let tacstx ← `(tactic|
    {
      simp [phaseProduct_coverage_check, phaseCoverageFrom?, phaseCoverageFrom?.loop, List.eraseFirstMatch?, matchesAt_pointRow, regEqExpected,
            State.start_state, expectedRow, List.eraseFirstMatch?, Prog.ADD,
            applyOp?, phaseCoverageFrom?.loop, State.addScaledReg, State.setReg,
            Register.addScaled]

      -- Use the parsed integer `n` here
      have := x_fin_checker $(quote nVal) (by simp)

      split_ifs with h
      rfl
      all_goals simp_all
    }
  )

  -- Run the tactic sequence using evalTactic
  -- This evaluates the tactic block in the current context
  evalTactic tacstx

theorem example_prog_2_phase_converage_2:
  phaseProduct_coverage_check example_prog_2 State.start_state [Point.int 0,Point.inf,Point.int 1,Point.int (-1),Point.int (-2)]:=by {
    unfold example_prog_2
    prove_coverage 3
  }



theorem example_prog_4_phase_coverage :
  phaseProduct_coverage_check example_prog_3 State.start_state [Point.int 0,Point.inf,Point.int 1,Point.int (-1)] := by
    unfold example_prog_3
    prove_coverage 4


-- /******************************************************************************/
-- /*                 RETURN TO ORIGINAL STATE PROOF.                            */
-- /******************************************************************************/



/-- Start state entry (usable by `simp`). -/
@[simp] lemma start_state_entry {k} (i j : Fin k) :
  State.start_state i j = (if j = i then 1 else 0) := by
  simp [State.start_state]


theorem example_prog_2_returns:
  run? example_prog_2 State.start_state = some State.start_state:=by {
    unfold example_prog_2 State.start_state
    simp [ run?_append,
         applyOp?,
         State.addScaledReg, State.negateReg, State.shiftLReg, State.shiftRReg?,
         State.setReg,
         Register.addScaled, Register.negate, Register.shiftL, Register.shiftR?]
    split_ifs with h
    simp
    funext j k
    have h2:=h j
    fin_cases j<;>fin_cases k<;>simp
    simp
    apply h
    intro j
    fin_cases j<;>simp
  }

-- /******************************************************************************/
-- /*               TACTIC TO PROVE RETURN TO ORIGINAL STATE.                    */
-- /******************************************************************************/

elab "returns_to_original?": tactic => do


  -- We will build the sequence of tactics as syntax
  let tacstx ← `(tactic|
    {
      simp [ run?_append,
         State.start_state,
         applyOp?,
         State.addScaledReg, State.negateReg, State.shiftLReg, State.shiftRReg?,
         State.setReg,
         Register.addScaled, Register.negate, Register.shiftL, Register.shiftR?]
      try (unfold State.setReg)
      try (funext j k)
      split_ifs with h
      simp
      try (funext j k)
      have h2:=h j
      fin_cases j<;>fin_cases k<;>simp
      simp
      apply h
      intro j
      fin_cases j<;>simp
    }
  )

  -- Run the tactic sequence using evalTactic
  -- This evaluates the tactic block in the current context
  evalTactic tacstx
theorem example_prog_2_returns_2:
  run? example_prog_2 State.start_state = some State.start_state:=by {
    unfold example_prog_2
    returns_to_original?
  }

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

namespace ProgEq

variable {k : ℕ}

@[refl] lemma refl  (p : Prog k) : p ≃ₚ p := by intro σ; rfl
@[symm] lemma symm  {p q : Prog k} : p ≃ₚ q → q ≃ₚ p := by
  intro h σ; unfold ProgEq at h; rw [h σ]
@[trans] lemma trans {p q r : Prog k} :
  p ≃ₚ q → q ≃ₚ r → p ≃ₚ r := by
  intro hpq hqr σ; simpa [hpq σ] using (hqr σ)

/-- Left congruence for sequencing. -/
lemma cong_left  {p q r : Prog k} :
  p ≃ₚ q → (p ;; r) ≃ₚ (q ;; r) := by
  intro hpq σ
  simp [run?_append, hpq σ]

/-- Right congruence for sequencing. -/
lemma cong_right {p q r : Prog k} :
  q ≃ₚ r → (p ;; q) ≃ₚ (p ;; r) := by
  intro hqr σ
  simp [run?_append]
  unfold ProgEq at hqr
  simp[hqr]

/-- Left identity (`[] ;; p ≃ p`). -/
lemma nil_left  (p : Prog k) : (([] : Prog k) ;; p) ≃ₚ p := by
  intro σ; simp

/-- Right identity (`p ;; [] ≃ p`). -/
lemma nil_right (p : Prog k) : (p ;; ([] : Prog k)) ≃ₚ p := by
  simp;apply refl

end ProgEq



-- /******************************************************************************/
-- /*                   STATE-LEVEL COMMUTING/ALGEBRA HELPERS                    */
-- /******************************************************************************/

namespace State
open State

/-- `setReg` on different indices commutes. -/
lemma setReg_comm {k} (σ : State k)
  (i j : Fin k) (ri rj : Register k) (hij : i ≠ j) :
  State.setReg (State.setReg σ i ri) j rj = State.setReg (State.setReg σ j rj) i ri := by
  funext t
  by_cases ht_i : t = i
  · subst ht_i; simp [State.setReg, hij]
  · by_cases ht_j : t = j
    · subst ht_j; simp [State.setReg, ht_i]
    · simp [State.setReg, ht_i, ht_j]

/-- Shifting two different destination registers (any amounts) commutes. -/
lemma shiftLReg_comm {k} (σ : State k)
  (i j : Fin k) (a b : ℕ) (hij : i ≠ j) :
  State.shiftLReg (State.shiftLReg σ i a) j b =
  State.shiftLReg (State.shiftLReg σ j b) i a := by
  -- both sides are just two setReg updates on different indices
  simp [State.shiftLReg, setReg_comm σ i j _ _ hij,State.setReg]
  simp[hij]
  have h:j ≠ i := by intro h;apply hij;rw[h]
  simp[h]

/-- Negating and shifting the *same* register commute. -/
lemma negate_shiftL_same {k} (σ : State k) (i : Fin k) (n : ℕ) :
  State.negateReg (State.shiftLReg σ i n) i = State.shiftLReg (State.negateReg σ i) i n := by
  -- Reduce to register-level pointwise equality.
  funext t
  by_cases ht : t = i
  · subst ht
    -- same index: - (x * 2^n) = (-x) * 2^n
    simp [State.negateReg, State.shiftLReg, State.setReg]
    unfold Register.negate Register.shiftL
    funext j
    simp
  · -- other indices are unchanged by the update
    simp [State.negateReg, State.shiftLReg, State.setReg, ht]

/-- Double negation on a register restores the state. -/
lemma negateReg_involutive {k} (σ : State k) (i : Fin k) :
  State.negateReg (State.negateReg σ i) i = σ := by
  funext t
  by_cases ht : t = i
  · subst ht; simp [State.negateReg, State.setReg]
    unfold Register.negate
    funext j
    simp
  · simp [State.negateReg, State.setReg, ht]

/-- Two successive left shifts add their exponents. -/
lemma shiftL_add (σ : State k) (i: Fin k) (a b : ℕ)
:(σ.shiftLReg i a).shiftLReg i b = σ.shiftLReg i (a + b):=by
  unfold State.shiftLReg Register.shiftL State.setReg
  funext j
  split_ifs with h1 h2
  · simp;funext m
    have : (2:ℤ) ^ a * (2:ℤ) ^ b= (2:ℤ) ^(a+b) := by rw[← Int.pow_add]
    rw[Int.mul_assoc]
    rw[this]
  · simp at h2
  · rfl
end State


-- /******************************************************************************/
-- /*                 PROGRAM EQUIVALENCES USING STATE HELPERS                   */
-- /******************************************************************************/

open ProgEq

/-- `(i <<s= a) ;; (i <<s= b)  ≃ₚ  (i <<s= (a + b))`. -/
lemma shl_shl_same_reg {k} (i : Fin k) (a b : ℕ) :
  i <<s= a ;; i <<s= b ≃ₚ (i <<s= (a + b)) := by
  intro σ
  simp[run?_append,State.shiftL_add]

/-- Shifts on *different* destination registers commute. -/
lemma shl_shl_comm {k} (i j : Fin k) (a b : ℕ) (hij : i ≠ j) :
  (i <<s= a) ;; (j <<s= b) ≃ₚ (j <<s= b) ;; (i <<s= a) := by
  intro σ
  simp [run?_append, State.shiftLReg_comm σ i j a b hij]

/-- `neg i` then `neg i` is a no-op. -/
lemma neg_neg_cancel {k} (i : Fin k) :
  (neg i) ;; (neg i) ≃ₚ ([] : Prog k) := by
  intro σ
  simp [run?_append, State.negateReg_involutive]

/-- On the *same* register, `neg` commutes with `<<s=`. -/
lemma neg_shl_same_comm {k} (i : Fin k) (n : ℕ) :
  (neg i) ;; (i <<s= n) ≃ₚ (i <<s= n) ;; (neg i) := by
  intro σ
  simp [run?_append, State.negate_shiftL_same]

/-- On *different* destination registers, `neg` and `<<s=` commute. -/
lemma neg_shl_diff_comm {k} (i j : Fin k) (n : ℕ) (hij : i ≠ j) :
  (neg i) ;; (j <<s= n) ≃ₚ (j <<s= n) ;; (neg i) := by
  intro σ
  simp [run?_append, State.setReg_comm σ i j _ _ hij, State.negateReg, State.shiftLReg]
  unfold Register.shiftL State.setReg
  funext t
  split_ifs with ht_i ht_j hij
  all_goals try rfl
  rw[hij] at ht_j; simp[ht_j] at ht_i


-- /******************************************************************************/
-- /*                INVERSE-CANCEL LEMMAS & STRONG UNDO THEOREM                 */
-- /******************************************************************************/

namespace State

/-- Right-shift exactly cancels a preceding left-shift on the same register. -/
lemma shiftR_after_shiftL_exact {k} (σ : State k) (i : Fin k) (n : ℕ) :
  State.shiftRReg? (State.shiftLReg σ i n) i n = some σ := by
   unfold shiftLReg setReg shiftRReg? Register.shiftL Register.shiftR?
   simp
   unfold setReg
   simp
   funext j r
   split_ifs with h
   simp[h]
   rfl

/-- If a right-shift succeeded, the corresponding left-shift restores the state. -/
lemma shiftL_after_shiftR_exact {k} {σ σ' : State k} (i : Fin k) (n : ℕ) :
  State.shiftRReg? σ i n = some σ' → State.shiftLReg σ' i n = σ := by
    unfold shiftLReg setReg shiftRReg? Register.shiftL Register.shiftR?
    simp
    unfold setReg
    split_ifs with h1
    · simp
      intro h2
      rw[← h2]
      funext j r
      simp
      split_ifs with h3
      simp
      rw[Int.ediv_mul_cancel]
      simp[h3]
      have h4:=h1 j
      have hm : σ i r % (2 : ℤ) ^ n = 0 := by simpa using h1 r
      exact Int.dvd_of_emod_eq_zero hm
      simp
    · simp

/-- Adding a scaled (or negated) source and then the opposite undoes the change. -/
lemma addScaled_cancel {k} (σ : State k) (dst src : Fin k) (negSrc : Bool) (n : ℕ) (hds:dst≠src):
  State.addScaledReg (State.addScaledReg σ dst src negSrc n) dst src (!negSrc) n = σ := by
  -- TODO: unfold `addScaledReg` and check the `dst` component; other regs unchanged
    unfold addScaledReg setReg Register.addScaled
    funext j q
    simp
    split_ifs with h1 h2 h3 h4 h5 h6 h7 h8
    all_goals try simp_all

/-- Inverse of a single step, for any well-formed op. -/
lemma run?_inv_singleton_OK {k} (op : valid_ops k) (ok : Prog.OpOK op) :
    ∀ {σ σ' : State k},
      applyOp? σ op = some σ' →
      run? [inv op] σ' = some σ := by
  intro σ σ' hstep
  cases op with
  | shiftL i n =>
      have h:=(State.shiftR_after_shiftL_exact (σ := σ) i n)
      simp[run?,applyOp?,inv,Prog.OpOK] at *
      rw[hstep] at h
      rw[h]
  | shiftR i n =>
      -- inverse: shiftL after a successful shiftR
      have := State.shiftL_after_shiftR_exact (σ := σ) (σ' := σ') i n hstep
      simp[run?,applyOp?,inv,Prog.OpOK] at *
      rw[this]
  | negate i =>
      -- negate twice cancels
      have h:=(State.negateReg_involutive (σ := σ) (i := i))
      simp[run?,applyOp?,inv,Prog.OpOK] at *
      rw[hstep] at h
      rw[h]
  | addScaled dst src b n =>
      -- need dst ≠ src to cancel
      have hne : dst ≠ src := by
        simpa [Prog.OpOK] using ok
      have h:=(State.addScaled_cancel (σ := σ) (dst := dst) (src := src) (negSrc := b) (n := n) hne)
      simp[run?,applyOp?,inv,Prog.OpOK] at *
      rw[hstep] at h
      rw[h]
  | phaseProduct l =>
      simp[run?,applyOp?,inv,Prog.OpOK] at *
      rw[hstep]

@[simp] lemma apply_Op_inverse_cons {k} (op : valid_ops k) (ps : Prog k) :
  apply_Op_inverse (op :: ps) = apply_Op_inverse ps ;; [inv op] := by
  -- (op :: ps).reverse = ps.reverse ++ [op], and `map` distributes over `++`
  unfold apply_Op_inverse
  simp [List.reverse_cons, List.map_append]

@[simp] lemma apply_Op_inverse_append {k} (p q : Prog k) :
  apply_Op_inverse (p ;; q) = apply_Op_inverse q ;; apply_Op_inverse p := by
  unfold apply_Op_inverse
  simp [List.reverse_append, List.map_append]

/-- Running the inverse program undoes any well-formed successful run. -/
theorem run?_inverse_undoes_WF {k}
    (p : Prog k) (WF : Prog.WellFormed p) (σ τ : State k) :
    run? p σ = some τ → run? (apply_Op_inverse p) τ = some σ := by
  revert σ τ
  induction p with
  | nil =>
      intro σ τ h
      simp[run?] at h
      simp[apply_Op_inverse,h]
  | cons op ps ih =>
      intro σ τ h
      have WFop : Prog.OpOK op := by
        exact WF op (by simp)       -- op ∈ op :: ps
      have WFps : Prog.WellFormed ps := by
        intro o ho; exact WF o (by simp [ho])  -- o ∈ ps → o ∈ op::ps
      -- expose first step
      simp [run?, apply_Op_inverse_cons, run?_append] at ⊢
      cases hstep : applyOp? σ op with
      | none    => simp [hstep] at h
      | some σ₁ =>
          have hps : run? ps σ₁ = some τ := by simpa [hstep] using h
          have ih' : run? (apply_Op_inverse ps) τ = some σ₁ :=
            ih WFps _ _ hps
          have hstep_inv :
              run? [inv op] σ₁ = some σ :=
            run?_inv_singleton_OK op WFop (σ := σ) (σ' := σ₁) hstep
          simp [ih']
          simp at hstep_inv
          simp[hstep_inv]
end State




def shiftsOfAux : Nat → Nat → List Nat
| 0,      _  => []
| n+1,    sh =>
  let rest := shiftsOfAux ((n+1) / 2) (sh+1)
  if Nat.bodd (n+1) then sh :: rest else rest
-- termination_by n _ => n
-- decreasing_by
--   -- simplify the well-founded goal then show (n+1)/2 < (n+1)
--   exact Nat.div_lt_self (Nat.succ_pos _) (by decide)


def shiftsOf (n : Nat) : List Nat := shiftsOfAux n 0
-- #eval shiftsOf 24  -- expects [3, 4]

/-- Signed power-of-two decomposition.
    Returns a list of `(neg, shift)` so that
    `c = ∑ (if neg then -1 else +1) * 2^shift`. -/
def signedPow2Decomp (c : Int) : List (Bool × Nat) :=
  if c = 0 then
    []
  else
    let neg'  : Bool := c < 0
    let mag  : Nat  := Int.natAbs c
    (shiftsOf mag).map (fun sh => (neg', sh))

/-- Finite index `0 : Fin k` when `k > 0`. -/
def finZero {k : Nat} (hk : 0 < k) : Fin k := ⟨0, hk⟩

/-- All source registers `j = 1..k-1` (i.e. finRange minus `0`). -/
def nonzeroFins {k : Nat} (hk : 0 < k) : List (Fin k) :=
  (List.finRange k).filter (fun j => decide (j ≠ finZero hk))

/-- Turn a `(neg, shift)` pair into one `addScaled` op: `dst += ± (src << shift)`. -/
def pairToOp {k : Nat} (dst src : Fin k) : (Bool × Nat) → valid_ops k
| (neg', sh) => valid_ops.addScaled dst src (negSrc := neg') sh


/-- Tiny helper: if `p head` is true, the eraser drops the head. -/
@[simp] lemma eraseFirstMatch?_head_true {α} (p : α → Bool) (x : α) (xs : List α)
  (hx : p x = true) :
  List.eraseFirstMatch? p (x :: xs) = some xs := by
  simp [List.eraseFirstMatch?, hx]


lemma phaseProduct_coverage_check_append_cons_of_returns {k : ℕ}
    (p q : Prog k) (σ : State k)
    (head : Point) (tail : List Point)
    (hret : run? p σ = some σ)
    (hp   : phaseProduct_coverage_check p σ [head] = true)
    (hq   : phaseProduct_coverage_check q σ tail   = true) :
  phaseProduct_coverage_check (p ++ q) σ (head :: tail) = true := by {
    sorry
  }
/-- Accumulate all contributions for `.int z` into `dst = 0`, **no uncompute yet**. -/
def computeLocal {k : Nat} (hk : 0 < k) (z : Int) : Prog k :=
  let dst := finZero hk
  (nonzeroFins hk).foldl
    (fun acc (j:Fin k) =>
      let c : Int := z ^ (j : Nat)
      if c = 0 then acc
      else acc ++ (signedPow2Decomp c).map (pairToOp dst j))
    ([] : Prog k)

/-- One block per point: build row in reg 0, mark it, then uncompute. -/
def opsForPointWithProduct {k : Nat} (hk : 0 < k) : Point → Prog k
| .inf   =>
    let last : Fin k := ⟨k-1, by have : 0 < k := hk; exact Nat.sub_lt (Nat.succ_le_of_lt this) (by decide)⟩
    [valid_ops.phaseProduct last]
| .int z =>
  let dst   := finZero hk
  let l := computeLocal hk z
  l ++ [valid_ops.phaseProduct dst] ++ apply_Op_inverse l

/-- Generator that **does** include the `phaseProduct` checkpoints. -/
def genOpsWithProduct {k : Nat} (hk : 0 < k) (points : List Point) : Prog k :=
  points.foldl (fun acc pt => acc ++ opsForPointWithProduct hk pt) ([] : Prog k)

theorem genOpsWithProduct_append (hk : 0 < k)(h:Point)(t:List Point):
  genOpsWithProduct hk (h::t)=genOpsWithProduct hk [h]++genOpsWithProduct hk t:= by
    sorry


theorem genOpsWithProduct_phase_coverage
  {k : Nat} (hk : 0 < k) (pts : List Point) :
  phaseProduct_coverage_check (genOpsWithProduct hk pts) State.start_state pts := by {
    induction pts with
    | nil=>{
      unfold genOpsWithProduct phaseProduct_coverage_check phaseCoverageFrom? matchesAt_pointRow phaseCoverageFrom?.loop
      simp
    }
    | cons head tail ih=>{
      rw[genOpsWithProduct_append,phaseProduct_coverage_check_append_cons_of_returns]
      {
        sorry
      }
      {
        unfold genOpsWithProduct phaseProduct_coverage_check phaseCoverageFrom? matchesAt_pointRow phaseCoverageFrom?.loop opsForPointWithProduct
        simp
        cases head with
        | int x => {
          simp
          sorry
        }
        | inf=> {
          --unfold List.eraseFirstMatch? regEqExpected expectedRow
          simp
          sorry
        }
      }
      {
        rw[ih]
      }
    }
  }
-- /******************************************************************************/
-- /*                   INTEGER → SIGNED POW2 DECOMPOSITION                      */
-- /******************************************************************************/

-- def signedPow2Decomp (c : Int) : List (Int × Nat) :=
--   if c = 0 then
--     []
--   else
--     Id.run do
--       let sgn : Int := if 0 ≤ c then (1 : Int) else (-1 : Int)
--       let mut n  : Nat := c.natAbs
--       let mut sh : Nat := 0
--       let mut out : List (Int × Nat) := []
--       while n ≠ 0 do
--         -- check LSB with modulus, no Nat.bodd needed
--         if n % 2 == (1 : Nat) then
--           out := (sgn, sh) :: out
--         n  := n / 2        -- shift right
--         sh := sh + 1
--       return out.reverse   -- ascending shifts

-- lemma decomp_2 :
--   signedPow2Decomp 2= [(1,1)]:=by {
--     unfold signedPow2Decomp
--     simp
--     sorry
--   }

-- /-- Reconstruct an integer from a decomposition list. -/
-- def sumDecomp (L : List (Int × Nat)) : Int :=
--   L.foldl (fun acc (s, sh) => acc + s * (2 : Int) ^ sh) 0

-- macro "sumDecomp_simp" : tactic =>
--   `(tactic| (unfold sumDecomp; simp))

-- lemma sumDecomp_2:(sumDecomp [(1,1)])=2:=by {
--   sumDecomp_simp
-- }

-- lemma sumDecomp_24:(sumDecomp [(1, 3), (1, 4)])=24:=by {
--   sumDecomp_simp
-- }

-- /--
-- Basic correctness: for all integers `c`, reconstructing from
-- `signedPow2Decomp c` gives back `c`.
-- -/
-- theorem signedPow2Decomp_correct (c : Int) :
--     sumDecomp (signedPow2Decomp c) = c := by
--   by_cases hc : c = 0
--   · simp [signedPow2Decomp, hc, sumDecomp]
--   ·
--     let sgn : Int := if 0 ≤ c then 1 else -1
--     let n := c.natAbs
--     -- since our construction collects exactly those (sgn, sh) where the bit is 1,
--     -- we reconstruct sgn * n
--     have : sumDecomp (signedPow2Decomp c) = sgn * n := by
--       -- this mirrors what the loop does; conceptually true
--       admit
--     -- finally show sgn * n = c
--     simp [Int.natAbs_of_nonneg, Int.natAbs_neg, hc] at *
--     by_cases h : 0 ≤ c
--     · simp [this,sgn,h];simp[n];sorry
--     · unfold sumDecomp
--       simp
--       sorry

-- -- (TODO: full formalization would replace `admit` with an induction on n.)


-- -- /******************************************************************************/
-- -- /*                 LIST-OF-POWERS SUMS & BINARY BIT SHIFTS                    */
-- -- /******************************************************************************/

--  /-- Sum `∑ (2^s)` over a list of shifts. We use lists (not finsets) because the
--     decomposition naturally produces a list. -/
-- def sumPow2 (L : List Nat) : ℤ :=
--   L.foldr (fun s acc => (2 : ℤ) ^ s + acc) 0

-- @[simp] lemma sumPow2_nil : sumPow2 [] = 0 := rfl
-- @[simp] lemma sumPow2_cons (s : Nat) (L : List Nat) :
--   sumPow2 (s :: L) = (2 : ℤ) ^ s + sumPow2 L := rfl

-- lemma sumPow2_append (A B : List Nat) :
--   sumPow2 (A ++ B) = sumPow2 A + sumPow2 B := by
--   induction A with
--   | nil => simp
--   | cons s A IH => simp [IH, Int.add_assoc]

-- /-- Map `succ` over shifts multiplies the sum by 2:  `∑ 2^(s+1) = 2 * ∑ 2^s`. -/
-- lemma sumPow2_mapSucc (L : List Nat) :
--   sumPow2 (L.map Nat.succ) = 2 * sumPow2 L := by
--   induction L with
--   | nil => simp
--   | cons s L IH =>
--       simp [IH, Int.pow_succ, Int.two_mul, Int.add_comm, Int.add_left_comm, Int.add_assoc]
--       omega

-- /-- Bits‐to‐shifts via `Nat.binaryRec`:
--     For `n = bit b m = 2*m + (if b then 1 else 0)`,
--     shifts are those of `m`, incremented by 1, plus `0` if `b = true`. -/
-- def bitShifts (n : Nat) : List Nat :=
--   Nat.binaryRec (motive := fun _ => List Nat)
--     []                                                           -- base: 0 ↦ []
--     (fun b _ acc => acc.map Nat.succ ++ (if b then [0] else [])) -- step: bit b m
--     n

-- /-- The sum of powers at positions `bitShifts n` equals `n` (as an integer). -/
-- lemma bitShifts_sum (n : Nat) : sumPow2 (bitShifts n) = (n : ℤ) := by
--   -- binary induction on `n`
--   refine Nat.binaryRec
--     (motive := fun n => sumPow2 (bitShifts n) = (n : ℤ))
--     ?base ?step n
--   · -- base: n = 0
--     simp [bitShifts]
--   · -- step: n = bit b m = 2*m + (if b then 1 else 0)
--     intro m b IH
--     -- unfold one step of `bitShifts`
--     unfold Nat.bit
--     sorry

-- /-- Boolean sign to ±1 in ℤ. -/
-- @[inline] def sgnInt (b : Bool) : ℤ := if b then -1 else 1
-- @[simp] lemma sgnInt_true  : sgnInt true  = (-1 : ℤ) := rfl
-- @[simp] lemma sgnInt_false : sgnInt false = ( 1 : ℤ) := rfl
