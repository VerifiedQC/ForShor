import FastMultiplication.Qubit_Wiring.Basic

/-
  This file sets up the bridge between:

  (A) the table level operations (`State k`, `Register k`, `applyOp?`, `run?`)
  and
  (B) the concrete qubit operations (`St k`, `prim_ops k`, `eval_prim_ops`).

  The main theorem `compileProg_simulates` needs a way to:
  - interpret a symbolic `State` as a concrete qubit state (`stateToSt`)
  - track widths consistently while compilation emits alloc/free (`curLen`)
  - enforce “no overflow” so MSB sign-extension is semantics-preserving (`FitsSigned`)
  - state and use a one-step preservation property (`ValidForStep`)
  - thread safety conditions for primitive ops (`PrimOKTrace`) to justify using bridge lemmas.
-/


----------------------------------------------------------------------------------------------------
------------------------------- stateToSt + FITS-SIGNED PREDICATES ---------------------------------
----------------------------------------------------------------------------------------------------

/-- Evaluate a symbolic register to an integer using a valuation for the variables. -/
def evalRegister {k : ℕ} (r : Register k) (ρ : Fin k → ℤ) : ℤ :=
  ∑ j : Fin k, (r j) * (ρ j)


/-!
Bundle the extra parameters needed to interpret a symbolic `State k` as a concrete `St k`.
This avoids `(ρ, baseW, curLen)` everywhere.
-/
structure StCtx (k : ℕ) where
  ρ      : Fin k → ℤ
  baseW  : Fin k → Nat
  curLen : List Nat


/-- Proof-friendly: store the evaluated integer directly as a `w`-bit two's-complement bitvector. -/
def stateToSt {k : ℕ} (σ : State k) (ctx : StCtx k) : St k :=
  fun i =>
    let w : Nat := ctx.baseW i + ctx.curLen.getD i.1 0
    let z : ℤ := evalRegister (σ i) ctx.ρ
    let m : ℤ := (2 : ℤ) ^ w
    let r : Nat := Int.toNat (Int.emod z m)
    ⟨w, BitVec.ofNat w r⟩


/-- `z` fits in signed two’s-complement with width `w` (i.e. no overflow). -/
def FitsSigned (w : Nat) (z : ℤ) : Prop :=
  w > 0 ∧ -( (2 : ℤ) ^ (w - 1) ) ≤ z ∧ z < (2 : ℤ) ^ (w - 1)


/-- Width used by `stateToSt` for register `i`. -/
def stWidth {k : ℕ} (ctx : StCtx k) (i : Fin k) : Nat :=
  ctx.baseW i + ctx.curLen.getD i.1 0


/-- The evaluated integer for register `i` fits in the signed range of its current width. -/
def FitsSignedAt {k : ℕ} (σ : State k) (ctx : StCtx k) (i : Fin k) : Prop :=
  FitsSigned (stWidth ctx i) (evalRegister (σ i) ctx.ρ)


/-- Every register’s evaluated value fits in its current signed width. -/
def FitsSignedAll {k : ℕ} (σ : State k) (ctx : StCtx k) : Prop :=
  ∀ i : Fin k, FitsSignedAt (σ := σ) (ctx := ctx) i

structure ValidFor {k : ℕ} (σ : State k) (ctx : StCtx k) : Prop where
  curLen_len : ctx.curLen.length = k
  baseW_eq : ∀ (i j:Fin k), ctx.baseW i = ctx.baseW j
  fits_all   : FitsSignedAll (σ := σ) (ctx := ctx)

open Operations
/--
One-step preservation for `ValidFor` along compilation/execution of a single op.
-/

def ValidForStep
  {k : ℕ} (ctx0 : StCtx k) : Prop :=
  ∀ (σ σ1 : State k) (op : valid_ops k) (curLenNow : List Nat),
    let ctxNow : StCtx k := { ctx0 with curLen := curLenNow }
    applyOp? σ op = some σ1 →
    Prog.OpOK op →
    ValidFor (k := k) σ ctxNow →
    let curLen1 := (compile1 (k := k) op curLenNow).2
    ValidFor (k := k) σ1 { ctx0 with curLen := curLen1 }


/-
  Primitive-op safety tracking:

  `compileProg_simulates` assumes `PrimOKTrace` for the compiled primitive program.
  This is used to:
  - extract preconditions for bridge lemmas (especially Free requires `n ≤ curLen[i]`)
  - split safety across concatenation when compiling `op :: ops`:
      PrimOKTrace (ops1 ++ ops2) ctx  ⇒  PrimOKTrace ops1 ctx  ∧  PrimOKTrace ops2 (ctx after ops1)
-/

/-- Side-condition ensuring a primitive op is safe w.r.t. the current context.

    This captures exactly the safety facts that bridge lemmas require:
    - Free needs enough bits available
    - Add needs equal widths at the moment it executes
    Other ops are always safe from the bookkeeping point of view. -/
def PrimOKForCtx {k : ℕ} : prim_ops k → StCtx k → Prop
| prim_ops.Free  i false n, ctx => n ≤ ctx.curLen.getD i.1 0
| prim_ops.Free  i true n,  ctx => n ≤ ctx.curLen.getD i.1 0
| prim_ops.Add dst src,     ctx => stWidth ctx dst = stWidth ctx src
| _,                          _ => True   -- fill in any remaining constructors as needed


/-- Update `ctx.curLen` as the prim evaluator would (only the bookkeeping part). -/
def stepCtxPrim {k : ℕ} (ctx : StCtx k) : prim_ops k → StCtx k
  | prim_ops.Alloc i true n => { ctx with curLen := incLen ctx.curLen i n }
  | prim_ops.Free  i true n => { ctx with curLen := decLen ctx.curLen i n }
  | prim_ops.Alloc i false n => { ctx with curLen := incLen ctx.curLen i n }
  | prim_ops.Free  i false n => { ctx with curLen := decLen ctx.curLen i n }
  | _                      => ctx


/-- Run the bookkeeping updates for a whole prim-op list. -/
def runCtxPrim {k : ℕ} (ctx : StCtx k) : List (prim_ops k) → StCtx k
  | []      => ctx
  | op::ops => runCtxPrim (stepCtxPrim ctx op) ops

/-- `ops` is safe if each prim op is OK *at the moment it executes* (i.e. w.r.t. the
    current threaded context). -/
def PrimOKTrace {k : ℕ} : List (prim_ops k) → StCtx k → Prop
  | []      , _   => True
  | op::ops , ctx => PrimOKForCtx (k := k) op ctx ∧ PrimOKTrace ops (stepCtxPrim ctx op)

def PrimOKForCtxListRun {k} : List (prim_ops k) → StCtx k → Prop
| [],      _   => True
| p :: ps, ctx => PrimOKForCtx p ctx ∧ PrimOKForCtxListRun ps (stepCtxPrim ctx p)


lemma PrimOKTrace_nil {k} (ctx : StCtx k) : PrimOKTrace (k := k) [] ctx := by
  simp [PrimOKTrace]

lemma PrimOKTrace_cons {k} (op : prim_ops k) (ops : List (prim_ops k)) (ctx : StCtx k) :
  PrimOKTrace (k := k) (op :: ops) ctx ↔
    PrimOKForCtx (k := k) op ctx ∧ PrimOKTrace (k := k) ops (stepCtxPrim ctx op) := by
  rfl


/-- Splitting lemma for safety over concatenation.

    Used in `compileProg_simulates` right after expanding
      compileProg (op :: ops) = ops1 ++ ops2
    to obtain safety of ops1 at ctx and safety of ops2 at the threaded ctx. -/
lemma PrimOKTrace_append {k : ℕ}
  (ops1 ops2 : List (prim_ops k)) (ctx : StCtx k) :
  PrimOKTrace (k := k) (ops1 ++ ops2) ctx
    ↔ PrimOKTrace (k := k) ops1 ctx ∧ PrimOKTrace (k := k) ops2 (runCtxPrim ctx ops1) := by
  induction ops1 generalizing ctx with
  | nil =>
      simp [PrimOKTrace, runCtxPrim]
  | cons op ops1 ih =>
      simp [PrimOKTrace, runCtxPrim, stepCtxPrim, ih, and_assoc]

/-
  runCtxPrim_append:

  `compileProg` produces primitive code by concatenation: `ops1 ++ ops2`.
  Safety splitting (`PrimOKTrace_append`) and the main IH both reference the context
  “after ops1”. That context is defined as `runCtxPrim ctx ops1`.

  This lemma provides associativity of the bookkeeping interpreter:
    runCtxPrim ctx (xs ++ ys) = runCtxPrim (runCtxPrim ctx xs) ys
  so the “context after xs” behaves well with program append.
-/
lemma runCtxPrim_append {k} (ctx : StCtx k) (xs ys : List (prim_ops k)) :
  runCtxPrim ctx (xs ++ ys) = runCtxPrim (runCtxPrim ctx xs) ys := by
  induction xs generalizing ctx with
  | nil =>
      simp [runCtxPrim]
  | cons x xs ih =>
      simp [runCtxPrim, ih, List.cons_append, stepCtxPrim]

/-
  runCtxPrim_if_nil_singleton:

  The compiler often emits “if n=0 then [] else [op]” to avoid no-op allocations/frees.
  During simulation proofs, contexts need to be rewritten through these conditionals.

  This lemma normalizes runCtxPrim over that pattern:
    runCtxPrim ctx (if p then [] else [op]) = if p then ctx else stepCtxPrim ctx op
  It is used heavily when unfolding compile1 for ops with optional alloc/free.
-/
lemma runCtxPrim_if_nil_singleton {k}
  (ctx : StCtx k) (p : Prop) [Decidable p] (op : prim_ops k) :
  runCtxPrim ctx (if p then [] else [op])
    = if p then ctx else stepCtxPrim ctx op := by
  by_cases hp : p <;> simp [hp, runCtxPrim, stepCtxPrim]

----------------------------------------------------------------------------------------------------
------------------------------- Basic list bookkeeping lemma (setAt/getD) ----------------------------
----------------------------------------------------------------------------------------------------

/-
  setAt_getD_id:

  A repeating step in proofs is:
  “write back the value already stored at idx, and the list is unchanged”.

  This lemma is used to prove `incLen_zero` / `decLen_zero` style facts,
  and more generally to simplify nested setAt updates when an update is a no-op.
-/
lemma setAt_getD_id (l : List Nat) (idx : Nat) :
    setAt l idx (l.getD idx 0) = l := by
  induction l generalizing idx with
  | nil =>
      cases idx <;> simp [setAt]
  | cons x xs ih =>
      cases idx with
      | zero =>
          simp [setAt, List.getD]
      | succ idx =>
          simpa [setAt, List.getD] using congrArg (fun t => x :: t) (ih idx)

----------------------------------------------------------------------------------------------------
------------------------------- ValidForStep transport lemma ----------------------------------------
----------------------------------------------------------------------------------------------------

/-
  ValidForStep.withCurLen:

  `compileProg_simulates` performs induction on a program list.
  After simulating the head op, the IH is applied to the tail with context
    { ctx with curLen := curLen1 }.

  The hypothesis `hStepValid : ValidForStep ctx` is stated for the original ctx record.
  This lemma transports that hypothesis to any ctx record that differs only in `curLen`,
  so the IH can be invoked without re-proving the step property.
-/
lemma ValidForStep.withCurLen
  {k : ℕ} (ctx : StCtx k) (L : List Nat) :
  ValidForStep (k := k) ctx → ValidForStep (k := k) { ctx with curLen := L } := by
  intro h
  -- eliminate `ctx` so record updates become definitional (rfl) after unfolding
  cases ctx with
  | mk ρ baseW curLen =>
    unfold ValidForStep at h ⊢
    intro σ σ1 op curLenNow
    simpa using (h (σ := σ) (σ1 := σ1) (op := op) (curLenNow := curLenNow))

----------------------------------------------------------------------------------------------------
------------------------------- Demo: stateToSt on small examples ----------------------------------
----------------------------------------------------------------------------------------------------

namespace StateToStDemo

open scoped BigOperators

-- handy Fin indices for k=3
def r0 : Fin 3 := ⟨0, by decide⟩
def r1 : Fin 3 := ⟨1, by decide⟩
def r2 : Fin 3 := ⟨2, by decide⟩

/-- Valuation for the symbolic variables x0, x1, x2. -/
def ρ3 : Fin 3 → ℤ
| ⟨0, _⟩ => 15
| ⟨1, _⟩ => 6
| ⟨2, _⟩ => -3

/-- Delta widths all zero. -/
def cur0 : List Nat := List.replicate 3 0


--------------------------------------------------------------------------------
-- Demo A: start_state
--------------------------------------------------------------------------------

/-- All regs have base width 5. -/
def baseW5 : Fin 3 → Nat := fun _ => 5

def ctx5 : StCtx 3 :=
{ ρ      := ρ3
  baseW  := baseW5
  curLen := cur0 }

def σ_start : State 3 := State.start_state
def st_start : St 3 := stateToSt σ_start ctx5

#eval printState st_start


--------------------------------------------------------------------------------
-- Demo B: change symbolic state: r0 := r0 + r1
--------------------------------------------------------------------------------

/-- Make register 0 equal to x0 + x1 in the symbolic world. -/
def σ_plus : State 3 :=
  State.addScaledReg σ_start r0 r1 false 0

/-- Use width 6 so +21 stays positive in two's-complement. -/
def baseW6 : Fin 3 → Nat := fun _ => 6

def ctx6 : StCtx 3 :=
{ ρ      := ρ3
  baseW  := baseW6
  curLen := cur0 }

def st_plus : St 3 := stateToSt σ_plus ctx6

#eval printState st_plus

end StateToStDemo


----------------------------------------------------------------------------------------------------
------------------------------- Small arithmetic lemmas ---------------------------------------------
----------------------------------------------------------------------------------------------------

open Operations

/-
  allocMSB_preserves_value:

  MSB allocation uses signExtend on the stored bitvector.
  The simulation proofs for `bridge_allocMSB` need the fact that signExtend preserves
  the interpreted integer (BitVec.toInt), assuming the value fits the original width.
  This lemma isolates the “concrete signExtend preserves toInt” step.
-/
lemma allocMSB_preserves_value
  {k : ℕ} (st : St k) (i : Fin k) (n : Nat) :
  BitVec.toInt ((AllocMSB st i n i).2) = BitVec.toInt ((st i).2) := by
  unfold AllocMSB
  rw [if_pos rfl]
  simp [BitVec.toInt_signExtend]

/-
  lowBitsZero:

  Predicate used to express that the lowest `n` bits of a bitvector are all 0.
  This is useful when reasoning about “shift then unshift” patterns and about
  divisibility by 2^n in the Nat/toNat representation.
-/
def lowBitsZero {w : Nat} (bv : BitVec w) (n : Nat) : Prop :=
  ∀ t : Nat, t < n → Nat.testBit bv.toNat t = false

/-
  freeLSB_undo_shift_toNat:

  FreeLSB removes `n` LSB bits. In Nat terms this is division by 2^n.
  Many bridge proofs (especially for shift/unshift subroutines inside addScaled)
  need to rewrite FreeLSB.toNat into a simple arithmetic form.
-/
lemma freeLSB_undo_shift_toNat
  {k : ℕ} (st : St k) (i : Fin k) (n : ℕ)
  (hn : n ≤ (st i).fst) :
  (FreeLSB st i n i).snd.toNat = (st i).snd.toNat / 2 ^ n := by
  simp [FreeLSB]
  rw[if_pos rfl]
  simp
  let w := (st i).fst
  let v := (st i).snd.toNat
  have h_v_lt : v < 2 ^ w := (st i).snd.isLt
  have h_pow_split : 2 ^ w = 2 ^ (w - n) * 2 ^ n := by
    rw [← Nat.pow_add, Nat.sub_add_cancel hn]
  have h_div_lt : v / 2 ^ n < 2 ^ (w - n) := by
    apply Nat.div_lt_of_lt_mul
    rw [mul_comm,← h_pow_split]
    exact h_v_lt
  apply Nat.mod_eq_of_lt h_div_lt




/-
  eval_prim_ops_append:

  `compileProg` emits primitive code as concatenations (ops1 ++ ops2).
  In `compileProg_simulates`, after simulating ops1 the proof must rewrite the goal
  into evaluation of ops2 starting from the resulting concrete state.
  This lemma is exactly that rewrite.
-/
lemma eval_prim_ops_append {k : ℕ}
  (xs ys : List (prim_ops k)) (st : St k) :
  eval_prim_ops (k := k) (xs ++ ys) st
    = eval_prim_ops (k := k) ys (eval_prim_ops (k := k) xs st) := by
  induction xs generalizing st with
  | nil =>
      simp [eval_prim_ops]
  | cons x xs ih =>
      simp [eval_prim_ops, ih, List.cons_append]

/-
  eval_prim_ops_singleton:

  Convenience lemma for compile1 cases that emit exactly one primitive op.
  Used inside `compile1_simulates` for shiftL/shiftR/negate cases.
-/
lemma eval_prim_ops_singleton {k : ℕ} (p : prim_ops k) (st : St k) :
  eval_prim_ops (k := k) [p] st = eval_prim_op_single (k := k) p st := by
  simp [eval_prim_ops]


----------------------------------------------------------------------------------------------------
------------------------------- List/len bookkeeping lemmas -----------------------------------------
----------------------------------------------------------------------------------------------------

/-
  incLen_to_sum_of_lt / decLen_to_sum_of_lt and their Fin-indexed simp versions:

  `stateToSt` and the bridge lemmas frequently require rewriting occurrences of:
    (incLen curLen i n)[i]? or getD at i
  into the arithmetic expression “old value + n”.
  These lemmas provide that rewrite both at Nat indices (with bounds) and at Fin indices
  (using the length = k invariant).

  These are used throughout `bridge_allocLSB`, `bridge_allocMSB`, and the addScaled
  simulation proofs, since those proofs depend on tracking widths exactly.
-/
lemma incLen_to_sum_of_lt
  (curLen : List ℕ)
  (n : ℕ)
  (idx : Nat)
  (hidx : idx < curLen.length) :
  curLen[idx]?.getD 0 + n =
    (setAt curLen idx (getLen curLen idx + n))[idx]?.getD 0 := by
  classical
  revert idx
  induction curLen with
  | nil =>
      intro idx hidx
      cases hidx
  | cons a xs ih =>
      intro idx hidx
      cases idx with
      | zero =>
          simp [setAt, getLen] at *
      | succ idx =>
          have hidx' : idx < xs.length := Nat.lt_of_succ_lt_succ hidx
          simpa [setAt, getLen] using ih idx hidx'

lemma decLen_to_sum_of_lt
  (curLen : List ℕ)
  (n : ℕ)
  (idx : Nat)
  (hidx : idx < curLen.length) :
  curLen[idx]?.getD 0 - n =
    (setAt curLen idx (getLen curLen idx - n))[idx]?.getD 0 := by
  classical
  revert idx
  induction curLen with
  | nil =>
      intro idx hidx
      cases hidx
  | cons a xs ih =>
      intro idx hidx
      cases idx with
      | zero =>
          simp [setAt, getLen] at *
      | succ idx =>
          have hidx' : idx < xs.length := Nat.lt_of_succ_lt_succ hidx
          simpa [setAt, getLen] using ih idx hidx'

@[simp] lemma incLen_to_sum
  (k : ℕ)
  (curLen : List ℕ)
  (n : ℕ)
  (j : Fin k)
  (hj : curLen.length = k) :
  curLen[j.val]?.getD 0 + n = (incLen curLen j n)[j.val]?.getD 0 := by
  have hjlt : j.val < curLen.length := by
    simp[hj]
  simpa [incLen, setLen] using
    (incLen_to_sum_of_lt (curLen := curLen) (n := n) (idx := j.val) hjlt)

@[simp] lemma decLen_to_diff
  (k : ℕ)
  (curLen : List ℕ)
  (n : ℕ)
  (j : Fin k)
  (hj : curLen.length = k) :
  curLen[j.val]?.getD 0 - n = (decLen curLen j n)[j.val]?.getD 0 := by
  have hjlt : j.val < curLen.length := by
    simp[hj]
  simpa [incLen, setLen] using
    (decLen_to_sum_of_lt (curLen := curLen) (n := n) (idx := j.val) hjlt)



/-
  Cancellation lemmas:

  These establish that `incLen` and `decLen` invert each other at the same index
  (under the relevant Nat-side conditions). They are used to simplify “do then undo”
  patterns in addScaled compilation proofs (shift/unshift and temporary widen/free).
-/
@[simp] lemma decLen_incLen_cancel (i:Fin k) (curLen:List ℕ):
decLen (incLen (curLen) i n) i n=curLen:= by
  cases k with
  | zero =>
      exact (Fin.elim0 i)
  | succ k =>
      -- now i : Fin (k+1)
      induction curLen generalizing i with
      | nil =>
          -- incLen/decLen on [] are []
          simp [incLen, decLen,setLen,setAt]
      | cons x xs ih =>
          -- split i = 0 or i = succ j
          refine Fin.cases ?h0 ?hs i
          ·
            simp [incLen, decLen, setLen, setAt, getLen] at *
          · intro j
            simp [incLen, decLen, setLen, setAt, getLen] at *
            have := ih (Fin.castSucc j)
            simpa using this

@[simp] lemma incLen_decLen_cancel (i:Fin k) (curLen:List ℕ) (hN: ∀ x ∈ curLen, n≤x):
incLen (decLen (curLen) i n) i n=curLen:= by
  cases k with
  | zero =>
      exact (Fin.elim0 i)
  | succ k =>
      -- now i : Fin (k+1)
      induction curLen generalizing i with
      | nil =>
          -- incLen/decLen on [] are []
          simp [incLen, decLen,setLen,setAt]
      | cons x xs ih =>
          -- split i = 0 or i = succ j
          refine Fin.cases ?h0 ?hs i
          ·
            simp [incLen, decLen, setLen, setAt, getLen] at *
            rw[Nat.sub_add_cancel];simp[hN]
          · intro j
            simp [incLen, decLen, setLen, setAt, getLen] at *
            simp_all
            have := ih (Fin.castSucc j)
            simpa using this

@[simp] lemma incLen_incLen_add (i:Fin k) (curLen:List ℕ) :
incLen (incLen (curLen) i n) i m = (incLen (curLen) i (n+m)):= by
cases k with
  | zero =>
      exact (Fin.elim0 i)
  | succ k =>
      induction curLen generalizing i with
      | nil =>
          simp [incLen, setLen, setAt, getLen]
      | cons x xs ih =>
          refine Fin.cases ?h0 ?hs i
          ·
            simp [incLen, setLen, setAt, getLen,Nat.add_left_comm, Nat.add_comm]
          · intro j
            have h := ih (i := Fin.castSucc j)
            simpa [incLen, setLen, setAt, getLen,
                   Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h


/-
  setAt/getD interaction lemmas:

  These are the core facts for “update one index, read another”.
  They are used to show that width updates to one register do not affect widths
  of other registers, which is needed in bridge lemmas and in addScaled width algebra.
-/
/-- `setAt` doesn't affect `getD` at a different index. -/
lemma getD_setAt_ne {α : Type} (xs : List α) (i j : Nat) (a d : α) (h : j ≠ i) :
    (setAt xs i a).getD j d = xs.getD j d := by
  induction xs generalizing i j with
  | nil =>
      simp [setAt]
  | cons x xs ih =>
      cases i <;> cases j <;> simp [setAt] at * ; aesop

/-- `setAt` at two different indices commutes. -/
lemma setAt_setAt_comm {α : Type} (xs : List α) (i j : Nat) (a b : α) (hij : i ≠ j) :
    setAt (setAt xs i a) j b = setAt (setAt xs j b) i a := by
  induction xs generalizing i j with
  | nil =>
      simp [setAt]
  | cons x xs ih =>
      cases i <;> cases j <;> simp [setAt] at *
      · aesop

/-- Reading back the updated index after `setAt` gives the written value (when in bounds). -/
lemma getD_setAt_same {α : Type}
    (xs : List α) (idx : Nat) (a d : α) (h : idx < xs.length) :
    (setAt xs idx a).getD idx d = a := by
  induction xs generalizing idx with
  | nil =>
      cases h
  | cons x xs ih =>
      cases idx with
      | zero =>
          simp [setAt]
      | succ idx =>
          have h' : idx < xs.length := Nat.lt_of_succ_lt_succ h
          have:= ih (idx := idx) h'
          aesop

/-
  getLen_setLen_same / getLen_setLen_other:

  These are the `Nat`-indexed counterparts specialized to `getLen`/`setLen`.
  They are used everywhere widths are compared or rewritten in bridge proofs.
-/
lemma getLen_setLen_same
  (curLen : List ℕ) (i : Fin k) (v : ℕ) (hcurLen : curLen.length = k):
  getLen (setLen curLen i v) (↑i) = v := by
  have hi : i.1 < curLen.length := by
    simp [hcurLen]
  simpa [getLen, setLen] using
    (getD_setAt_same (xs := curLen) (idx := i.1) (a := v) (d := 0) hi)

lemma getLen_setLen_other
  (curLen : List ℕ) (i j : Fin k) (v : ℕ) (hij : (↑i : Nat) ≠ (↑j : Nat))  :
  getLen (setLen curLen i v) (↑j) = getLen curLen (↑j) := by
  simp [getLen, setLen]
  apply getD_setAt_ne (xs := curLen) (i := (↑i)) (j := (↑j)) (a := v) (d := 0)
  aesop




/-
  setLen_setLen_comm:

  Writes to two different registers commute at the bookkeeping level.
  This is useful for rearranging width-update sequences when proving that a target width
  is the same for dst and src after widening.
-/
/-- `setLen` at two different `Fin` indices commutes. -/
lemma setLen_setLen_comm
    {k : ℕ} (curLen : List ℕ) (i j : Fin k) (vi vj : ℕ)
    (hijNat : (↑i : Nat) ≠ (↑j : Nat)) :
    setLen (setLen curLen i vi) j vj = setLen (setLen curLen j vj) i vi := by
  -- unfold to `setAt` and apply `setAt_setAt_comm`
  simpa [setLen] using (setAt_setAt_comm (xs := curLen) (i := (↑i)) (j := (↑j)) (a := vi) (b := vj) hijNat)


/-! ### Disjoint commutation lemmas for inc/dec -/

/-
  Disjoint commutation lemmas:

  These are used to reorder bookkeeping updates when proving width equalities like:
    stWidth ctx dst = stWidth ctx src
  after both registers have been widened to a common target width.

  They keep the main simulation scripts readable by allowing rewrites like
    incLen (incLen l i ...) j ... = incLen (incLen l j ...) i ...
  when i ≠ j.
-/

/-- `incLen` then `incLen` at disjoint indices commutes. -/
lemma incLen_incLen_disjoint_comm
    {k n m : ℕ} {i j : Fin k} (curLen : List ℕ)
    (hij : i ≠ j) :
    incLen (incLen curLen i n) j m = incLen (incLen curLen j m) i n := by
  classical
  have hijNat : (↑i : Nat) ≠ (↑j : Nat) := by
    intro h; apply hij; exact Fin.ext h
  simp [incLen]
  have hGet_ij :
      getLen (setLen curLen i (getLen curLen (↑i) + n)) (↑j) = getLen curLen (↑j) :=
    getLen_setLen_other (curLen := curLen) (i := i) (j := j)
      (v := getLen curLen (↑i) + n) hijNat

  have hGet_ji :
      getLen (setLen curLen j (getLen curLen (↑j) + m)) (↑i) = getLen curLen (↑i) := by
    have : (↑j : Nat) ≠ (↑i : Nat) := by intro h; exact hijNat (Eq.symm h)
    exact getLen_setLen_other (curLen := curLen) (i := j) (j := i)
      (v := getLen curLen (↑j) + m) this
  simpa [hGet_ij, hGet_ji] using
    (setLen_setLen_comm (curLen := curLen) (i := i) (j := j)
      (vi := getLen curLen (↑i) + n) (vj := getLen curLen (↑j) + m) hijNat)


/-- `incLen` then `decLen` at disjoint indices commutes. -/
lemma incLen_decLen_disjoint_comm
    {k n m : ℕ} {i j : Fin k} (curLen : List ℕ)
    (hij : i ≠ j) :
    incLen (decLen curLen j m) i n = decLen (incLen curLen i n) j m := by
  classical
  have hijNat : (↑i : Nat) ≠ (↑j : Nat) := by
    intro h; apply hij; exact Fin.ext h
  simp [incLen, decLen]
  have hGet_ij :
      getLen (setLen curLen i (getLen curLen (↑i) + n)) (↑j) = getLen curLen (↑j) :=
    getLen_setLen_other (curLen := curLen) (i := i) (j := j)
      (v := getLen curLen (↑i) + n) hijNat

  have hGet_ji :
      getLen (setLen curLen j (getLen curLen (↑j) - m)) (↑i) = getLen curLen (↑i) := by
    have : (↑j : Nat) ≠ (↑i : Nat) := by intro h; exact hijNat (Eq.symm h)
    exact getLen_setLen_other (curLen := curLen) (i := j) (j := i)
      (v := getLen curLen (↑j) - m) this
  have := setLen_setLen_comm (curLen := curLen) (i := i) (j := j)
      (vi := getLen curLen (↑i) + n) (vj := getLen curLen (↑j) - m) hijNat
  simpa [hGet_ij, hGet_ji] using this.symm


/-- `decLen` then `incLen` at disjoint indices commutes. -/
lemma decLen_incLen_disjoint_comm
    {k n m : ℕ} {i j : Fin k} (curLen : List ℕ)
    (hij : i ≠ j) (hcurLen : curLen.length = k) :
    decLen (incLen curLen j m) i n = incLen (decLen curLen i n) j m := by
  classical
  have hijNat : (↑i : Nat) ≠ (↑j : Nat) := by
    intro h; apply hij; exact Fin.ext h

  simp [incLen, decLen]

  have hGet_ij :
      getLen (setLen curLen i (getLen curLen (↑i) - n)) (↑j) = getLen curLen (↑j) := by
    exact getLen_setLen_other (curLen := curLen) (i := i) (j := j)
      (v := getLen curLen (↑i) - n) hijNat

  have hGet_ji :
      getLen (setLen curLen j (getLen curLen (↑j) + m)) (↑i) = getLen curLen (↑i) := by
    have : (↑j : Nat) ≠ (↑i : Nat) := by intro h; exact hijNat (Eq.symm h)
    exact getLen_setLen_other (curLen := curLen) (i := j) (j := i)
      (v := getLen curLen (↑j) + m) this

  have := setLen_setLen_comm (curLen := curLen) (i := i) (j := j)
      (vi := getLen curLen (↑i) - n) (vj := getLen curLen (↑j) + m) hijNat
  aesop


/-- `decLen` then `decLen` at disjoint indices commutes. -/
lemma decLen_decLen_disjoint_comm
    {k n m : ℕ} {i j : Fin k} (curLen : List ℕ)
    (hij : i ≠ j)  :
    decLen (decLen curLen i n) j m = decLen (decLen curLen j m) i n := by
  classical
  have hijNat : (↑i : Nat) ≠ (↑j : Nat) := by
    intro h; apply hij; exact Fin.ext h

  simp [decLen]

  have hGet_ij :
      getLen (setLen curLen i (getLen curLen (↑i) - n)) (↑j) = getLen curLen (↑j) :=
    getLen_setLen_other (curLen := curLen) (i := i) (j := j)
      (v := getLen curLen (↑i) - n) hijNat

  have hGet_ji :
      getLen (setLen curLen j (getLen curLen (↑j) - m)) (↑i) = getLen curLen (↑i) := by
    have : (↑j : Nat) ≠ (↑i : Nat) := by intro h; exact hijNat (Eq.symm h)
    exact getLen_setLen_other (curLen := curLen) (i := j) (j := i)
      (v := getLen curLen (↑j) - m) this

  simpa [hGet_ij, hGet_ji] using
    (setLen_setLen_comm (curLen := curLen) (i := i) (j := j)
      (vi := getLen curLen (↑i) - n) (vj := getLen curLen (↑j) - m) hijNat)


/-
  getElem?_setAt_ne:

  Pointwise “list.get?” version of the “setAt at idx doesn’t affect reads at m≠idx”.
  This is commonly used when the proof wants to avoid switching between getD and get?.
-/
@[simp] theorem getElem?_setAt_ne {α} (xs : List α) (idx m : ℕ) (v : α) (hne : m ≠ idx) :
    (setAt xs idx v)[m]? = xs[m]? := by
  induction xs generalizing idx m with
  | nil => simp [setAt]
  | cons head tail ih =>
    match idx, m with
    | 0, 0 => contradiction
    | 0, m' + 1 => simp [setAt]
    | idx' + 1, 0 => simp [setAt]
    | idx' + 1, m' + 1 =>
      simp [setAt]
      apply ih _ _ (by omega)


/-
  List.getD_eq_of_lt:

  When idx is in range, the default argument to getD is irrelevant.
  This is used to rewrite getD idx 1 into getD idx 0 in `incLen_getD_self`.
-/
lemma List.getD_eq_of_lt {α : Type} (xs : List α) (idx : Nat) (d₁ d₂ : α)
    (h : idx < xs.length) :
    xs.getD idx d₁ = xs.getD idx d₂ := by
  revert idx
  induction xs with
  | nil =>
      intro idx h
      cases h
  | cons x xs ih =>
      intro idx h
      cases idx with
      | zero =>
          simp [List.getD]
      | succ idx =>
          have h' : idx < xs.length := Nat.lt_of_succ_lt_succ h
          aesop

/-
  setAt_getD_same:

  “read-after-write at the same index” for getD (when idx < length).
  Used to prove the self-update lemma for incLen/decLen with getD.
-/
lemma setAt_getD_same {α : Type} (xs : List α) (idx : Nat) (a d : α)
    (h : idx < xs.length) :
    (setAt xs idx a).getD idx d = a := by
  revert idx
  induction xs with
  | nil =>
      intro idx h
      cases h
  | cons x xs ih =>
      intro idx h
      cases idx with
      | zero =>
          simp [setAt, List.getD]
      | succ idx =>
          have h' : idx < xs.length := Nat.lt_of_succ_lt_succ h
          aesop

/-
  incLen_getD_self:

  Concrete “self index update” lemma:
    (incLen curLen j n).getD j 0 = curLen.getD j 0 + n
  Used throughout bridge proofs and width-equality proofs (especially for Add safety).
-/
lemma incLen_getD_self
  (k : ℕ)
  (curLen : List ℕ)
  (n : ℕ)
  (j : Fin k)
  (hcurLen : curLen.length = k) :
  (incLen curLen j n).getD j.val 0 = curLen.getD j.val 0 + n := by
  have hjlt : j.val < curLen.length := by
    aesop
  unfold incLen setLen getLen
  have hdef : curLen.getD j.val 1 = curLen.getD j.val 0 :=
    List.getD_eq_of_lt (xs := curLen) (idx := j.val) (d₁ := 1) (d₂ := 0) hjlt
  have := (setAt_getD_same (xs := curLen) (idx := j.val)
      (a := curLen.getD j.val 1 + n) (d := 0) hjlt)
  aesop

/-
  setAt_getD:

  Another “write-back current value” lemma, generalized over any default.
  Used to prove `incLen_zero` and `decLen_zero`.
-/
lemma setAt_getD {α : Type} (xs : List α) (idx : Nat) (d : α) :
    setAt xs idx (xs.getD idx d) = xs := by
  induction xs generalizing idx with
  | nil =>
      simp [setAt]
  | cons x xs ih =>
      cases idx with
      | zero =>
          simp [setAt]
      | succ idx =>
          have:= ih idx
          simp [setAt]
          change setAt xs idx (xs.getD idx d) = xs
          rw[this]

/-
  incLen_zero / decLen_zero:

  The compiler guards alloc/free with `if n=0 then [] else ...`.
  These simp lemmas ensure bookkeeping updates collapse when n=0, so
  context-threading proofs (runCtxPrim_if_alloc/runCtxPrim_if_free style)
  can simplify cleanly.
-/
@[simp] theorem incLen_zero (curLen : List ℕ) (i : Fin k) :
  incLen curLen i 0 = curLen := by
  simpa [incLen, setLen, getLen, Nat.add_zero] using
    (setAt_getD (xs := curLen) (idx := i.val) (d := (0 : Nat)))

@[simp] theorem decLen_zero {k : ℕ} (curLen : List Nat) (i : Fin k) :
  decLen curLen i 0 = curLen := by
  simpa [decLen, setLen, getLen, Nat.sub_zero] using
    (setAt_getD (xs := curLen) (idx := i.val) (d := (0 : Nat)))

/-
  stateToSt_fst:

  Convenience simp lemma: the width stored by stateToSt at register j is exactly
    baseW j + curLen[j]
  Used constantly in bridge lemmas when comparing widths on both sides.
-/
@[simp] lemma stateToSt_fst {k : ℕ}
  (σ : State k) (ctx : StCtx k) (j : Fin k) :
  (stateToSt σ ctx j).fst = ctx.baseW j + ctx.curLen.getD j.val 0 := by
  simp [stateToSt]

/-
  FitsSigned_mono:

  Widening a register (increasing its width) should never break the “fits in signed range”
  property. This monotonicity lemma is used whenever the compiler performs MSB widening
  (AllocMSB / signExtend) and the proof needs to re-establish `ValidFor` for the widened
  context, especially inside the addScaled simulation pipeline.
-/
lemma FitsSigned_mono {w w' : Nat} {z : ℤ} (hw : w ≤ w') :
    FitsSigned w z → FitsSigned w' z := by
  intro hz
  rcases hz with ⟨hwpos, hlo, hhi⟩
  have hwpos' : w' > 0 := lt_of_lt_of_le hwpos hw

  have hExp : w - 1 ≤ w' - 1 := Nat.sub_le_sub_right hw 1
  have hPowNat : (2 : Nat) ^ (w - 1) ≤ (2 : Nat) ^ (w' - 1) :=
    Nat.pow_le_pow_right (by simp) hExp
  have hPow : (2 : ℤ) ^ (w - 1) ≤ (2 : ℤ) ^ (w' - 1) := by
    exact_mod_cast hPowNat

  refine ⟨hwpos', ?_, ?_⟩
  · -- lower bound becomes weaker when width increases
    have : -( (2 : ℤ) ^ (w' - 1) ) ≤ -( (2 : ℤ) ^ (w - 1) ) := by
      exact neg_le_neg hPow
    exact le_trans this hlo
  · -- upper bound becomes larger when width increases
    exact lt_of_lt_of_le hhi hPow

/-
  incLen_getD_ne':

  Bookkeeping lemma: increasing `curLen` at index `i` does not change the `getD` value
  at a different index `j`. This is used constantly when proving width equalities and
  showing that invariants for untouched registers remain unchanged during compilation steps.
-/
lemma incLen_getD_ne'
  {k : ℕ} (curLen : List Nat) (i j : Fin k) (n : Nat)
  (hcurLen : curLen.length = k) (hij : j ≠ i) :
  (incLen curLen i n).getD j.1 0 = curLen.getD j.1 0 := by
  -- unfold incLen / setLen (matches the earlier bookkeeping proofs)
  unfold incLen setLen
  simp
  rw [getElem?_setAt_ne curLen i.val j.val (getLen curLen i.val + n)]
  subst hcurLen
  simp
  intro ha; omega

/-
  FitsSignedAt_incLen:

  If all registers fit their signed widths in the original context, then after
  increasing the width delta list at some index `i` (via incLen), every register
  still fits in the new context.

  This is the key invariant-propagation step used to prove `ValidFor` is stable
  under MSB widening (AllocMSB) and under the bookkeeping updates performed by
  the compiler between bridge steps.
-/
lemma FitsSignedAt_incLen
  {k : ℕ}
  (σ : State k)
  (ctx : StCtx k)
  (hcurLen : ctx.curLen.length = k)
  (fitsAll : ∀ i : Fin k, FitsSignedAt (σ := σ) (ctx := ctx) i)
  (i : Fin k) (n : ℕ) (j : Fin k) :
  FitsSignedAt (σ := σ)
    (ctx := { ρ := ctx.ρ, baseW := ctx.baseW, curLen := incLen ctx.curLen i n }) j := by
  -- Start from the old FitsSignedAt at j
  have hj : FitsSignedAt (σ := σ) (ctx := ctx) j := fitsAll j

  -- Show width only increases
  have hw :
      stWidth (ctx := ctx) j ≤
        stWidth (ctx := { ρ := ctx.ρ, baseW := ctx.baseW, curLen := incLen ctx.curLen i n }) j := by
    unfold stWidth
    apply Nat.add_le_add_left
    by_cases hji : j = i
    · subst hji
      simp_all
      rw [← incLen_to_sum]
      aesop
      apply hcurLen
    ·
      have hget :
          (incLen ctx.curLen i n).getD j.val 0 = ctx.curLen.getD j.val 0 := by
        simpa using
          incLen_getD_ne' (k := k) (curLen := ctx.curLen) (i := i) (j := j) (n := n) hcurLen hji
      aesop

  have hjFits : FitsSigned (stWidth (ctx := ctx) j) (evalRegister (σ j) ctx.ρ) := by
    simpa [FitsSignedAt] using hj

  have hjFits' :
      FitsSigned
        (stWidth (ctx := { ρ := ctx.ρ, baseW := ctx.baseW, curLen := incLen ctx.curLen i n }) j)
        (evalRegister (σ j) ctx.ρ) :=
    FitsSigned_mono
      (w := stWidth (ctx := ctx) j)
      (w' := stWidth (ctx := { ρ := ctx.ρ, baseW := ctx.baseW, curLen := incLen ctx.curLen i n }) j)
      (z := evalRegister (σ j) ctx.ρ)
      hw hjFits

  simpa [FitsSignedAt] using hjFits'

/-
  ValidFor_incLen:

  `ValidFor` is stable under bookkeeping width updates (incLen). This is used whenever
  the compiler widens widths (AllocMSB) or shifts (AllocLSB) and the proof needs
  `ValidFor` for the new context before applying the next bridge lemma.
-/
lemma ValidFor_incLen (i : Fin k) (σ : State k) (ctx : StCtx k) (hV : ValidFor σ ctx) :
  ValidFor (σ) { ρ := ctx.ρ, baseW := ctx.baseW, curLen := (incLen (ctx.curLen) i n) } := by
  induction hV
  rename_i hcurLen baseW_eq fitsAll
  constructor
  · simp [incLen_pres_len, hcurLen]
  · intro j
    unfold FitsSignedAll at *
    intro j_1
    simp; apply baseW_eq
  ·
    -- FitsSigned invariant after widening
    intro j
    simpa [FitsSignedAll] using FitsSignedAt_incLen (σ := σ) (ctx := ctx) hcurLen fitsAll i n j



/-
  PrimOKTrace.append_inv:

  In the cons case of `compileProg_simulates`, the compiled program is `ops1 ++ ops2`.
  The proof needs safety for ops1 at the current ctx, and safety for ops2 at the
  context after running ops1 (runCtxPrim ctx ops1). This lemma extracts exactly that.
-/
/-- Split a `PrimOKTrace` over `++` (tail starts at the threaded ctx after ops1). -/
lemma PrimOKTrace.append_inv {k : ℕ}
  (ops1 ops2 : List (prim_ops k)) (ctx : StCtx k) :
  PrimOKTrace (k := k) (ops1 ++ ops2) ctx →
    (PrimOKTrace (k := k) ops1 ctx ∧
     PrimOKTrace (k := k) ops2 (runCtxPrim (k := k) ctx ops1)) := by
  induction ops1 generalizing ctx with
  | nil =>
      intro h
      simp [PrimOKTrace, runCtxPrim] at h ⊢
      apply h
  | cons op ops ih =>
      intro h
      have h' : PrimOKForCtx (k := k) op ctx ∧
        PrimOKTrace (k := k) (ops ++ ops2) (stepCtxPrim (k := k) ctx op) := by
        simpa [PrimOKTrace] using h
      have tail := ih (ctx := stepCtxPrim (k := k) ctx op) h'.2
      refine ⟨?_, ?_⟩
      ·
        refine ⟨h'.1, tail.1⟩
      ·
        simpa [runCtxPrim] using tail.2


/-
  runCtxPrim_singleton:

  Convenience lemma: running bookkeeping on a singleton list is just one step.
  Used when simplifying contexts for one-op compiler outputs.
-/
@[simp] lemma runCtxPrim_singleton {k : ℕ} (ctx : StCtx k) (op : prim_ops k) :
  runCtxPrim (k := k) ctx [op] = stepCtxPrim (k := k) ctx op := by
  simp [runCtxPrim]

/-
  stepCtxPrim_negate/add/phase:

  Negate/Add/phaseProduct do not change widths, so the bookkeeping context is unchanged.
  Used frequently when normalizing runCtxPrim over compiler-emitted sequences.
-/
-- stepCtxPrim does nothing on these
@[simp] lemma stepCtxPrim_negate {k : ℕ} (ctx : StCtx k) (i : Fin k) :
  stepCtxPrim (k := k) ctx (prim_ops.negate i) = ctx := by
  rfl

@[simp] lemma stepCtxPrim_add {k : ℕ} (ctx : StCtx k) (dst src : Fin k) :
  stepCtxPrim (k := k) ctx (prim_ops.Add dst src) = ctx := by
  rfl

@[simp] lemma stepCtxPrim_phase {k : ℕ} (ctx : StCtx k) (i : Fin k) :
  stepCtxPrim (k := k) ctx (prim_ops.phaseProduct i) = ctx := by
  rfl

/-
  runCtxPrim_if_alloc / runCtxPrim_if_free:

  The compiler emits alloc/free guarded by `if n = 0 then [] else [op]`.
  These lemmas rewrite the resulting `runCtxPrim` exactly into `incLen/decLen`,
  which is needed to:
  - align the tail context in `compileProg_simulates`
  - align the updated `curLen` field in `compile1_simulates`.
-/
lemma runCtxPrim_if_alloc
  {k : ℕ} (ctx : StCtx k) (i : Fin k) (lsb : Bool) (n : Nat) :
  runCtxPrim (k := k) ctx (if n = 0 then [] else [prim_ops.Alloc i lsb n])
    = { ctx with curLen := incLen ctx.curLen i n } := by
  by_cases hn : n = 0
  · subst hn
    simp [runCtxPrim]        -- uses incLen_zero
  · by_cases h:lsb<;>simp [hn, stepCtxPrim, h]

lemma runCtxPrim_if_free
  {k : ℕ} (ctx : StCtx k) (i : Fin k) (lsb : Bool) (n : Nat) :
  runCtxPrim (k := k) ctx (if n = 0 then [] else [prim_ops.Free i lsb n])
    = { ctx with curLen := decLen ctx.curLen i n } := by
  by_cases hn : n = 0
  · subst hn
    simp [runCtxPrim]        -- uses decLen_zero
  · by_cases h:lsb<;>simp [hn, h, stepCtxPrim]

/-
  runCtxPrim_negops / runCtxPrim_adder:

  Bookkeeping simplifications for the small fragments emitted by compile_op_to_prim_single.
  These are used when proving `runCtxPrim_compile1` in the addScaled case by splitting
  the emitted sequence into chunks (negops, shift, widen, add, frees, etc.).
-/
lemma runCtxPrim_negops
  {k : ℕ} (ctx : StCtx k) (src : Fin k) (negSrc : Bool) :
  runCtxPrim (k := k) ctx (if negSrc then [prim_ops.negate src] else [])
    = ctx := by
  cases negSrc <;> simp [runCtxPrim, stepCtxPrim]

lemma runCtxPrim_adder
  {k : ℕ} (ctx : StCtx k) (dst src : Fin k) :
  runCtxPrim (k := k) ctx [prim_ops.Add dst src] = ctx := by
  simp [runCtxPrim, stepCtxPrim]

/-
  runCtxPrim_compile1:

  Key bookkeeping lemma for `compileProg_simulates`.

  In the cons case, after compiling the head op we define:
    ops1 := (compile1 op ctx.curLen).1
    curLen1 := (compile1 op ctx.curLen).2

  The tail IH is stated for context `{ctx with curLen := curLen1}`.
  This lemma identifies the threaded bookkeeping context after running ops1 as exactly that:
    runCtxPrim ctx ops1 = {ctx with curLen := curLen1}
-/
lemma runCtxPrim_compile1
  {k : ℕ} (op : valid_ops k) (ctx : StCtx k) :
  runCtxPrim (k := k) ctx (compile1 (k := k) op ctx.curLen).1
    = { ctx with curLen := (compile1 (k := k) op ctx.curLen).2 } := by
  cases op with
  | shiftL i n =>
      simp [compile1, compile_op_to_prim_single, stepCtxPrim]
  | shiftR i n =>
      simp [compile1, compile_op_to_prim_single, stepCtxPrim]
  | negate i =>
      simp [compile1, compile_op_to_prim_single, stepCtxPrim]
  | phaseProduct i =>
      simp [compile1, compile_op_to_prim_single, stepCtxPrim]
  | addScaled dst src negSrc sh =>
      by_cases hds : dst = src
      · -- compiler emits [] and curLen unchanged
        simp [compile1, compile_op_to_prim_single, hds, runCtxPrim]
      ·
        simp (config := { zeta := true }) [compile1, compile_op_to_prim_single, hds]
        simp (config := { zeta := true })
          [runCtxPrim_append,
          runCtxPrim_negops,
          runCtxPrim_if_alloc,
          runCtxPrim_if_free,
          runCtxPrim, stepCtxPrim]

/-
  PrimOKTrace_if_alloc / PrimOKTrace_if_free / PrimOKTrace_negops / PrimOKTrace_adder:

  These establish safety (`PrimOKTrace`) for the small conditional fragments emitted by compile1.
  In `compile1_simulates` and `compileProg_simulates`, `PrimOKTrace` is used to justify calling
  bridge lemmas (notably, Free requires `n ≤ curLen[i]` at the moment it executes).
-/
lemma PrimOKTrace_if_alloc {k : ℕ}
  (ctx : StCtx k) (i : Fin k) (lsb : Bool) (n : Nat) :
  PrimOKTrace (k := k)
    (if n = 0 then [] else [prim_ops.Alloc i lsb n]) ctx := by
  by_cases hn : n = 0
  · subst hn; simp [PrimOKTrace]
  · simp [hn, PrimOKTrace, PrimOKForCtx]   -- Alloc is always True

lemma PrimOKTrace_if_free
  {k : ℕ} (ctx : StCtx k) (i : Fin k) (lsb : Bool) (n : Nat)
  (h : n ≤ ctx.curLen.getD i.1 0) :
  PrimOKTrace (k := k)
    (if n = 0 then [] else [prim_ops.Free i lsb n]) ctx := by
  by_cases hn : n = 0
  · subst hn; simp [PrimOKTrace]
  · cases lsb<;>simp [hn, PrimOKTrace, PrimOKForCtx]<;> apply h

lemma PrimOKTrace_negops {k : ℕ}
  (ctx : StCtx k) (src : Fin k) (negSrc : Bool) :
  PrimOKTrace (k := k)
    (if negSrc then [prim_ops.negate src] else []) ctx := by
  cases negSrc <;> simp [PrimOKTrace, PrimOKForCtx]

lemma PrimOKTrace_adder
  {k : ℕ} (ctx : StCtx k) (dst src : Fin k)
  (hW : stWidth (k := k) ctx dst = stWidth (k := k) ctx src) :
  PrimOKTrace (k := k) [prim_ops.Add dst src] ctx := by
  simp [PrimOKTrace, PrimOKForCtx, hW]

/-
  le_getD_incLen_self:

  Simple Nat inequality: after incLen at i by n, the stored value at i is ≥ n.
  Used when proving safety for an immediate Free that undoes a prior Alloc,
  and when constructing the `hn : n ≤ curLen[i]` side condition for bridge_freeLSB.
-/
lemma le_getD_incLen_self {k : ℕ} (curLen : List Nat) (i : Fin k) (n : Nat) (hc:curLen.length=k) :
  n ≤ (incLen curLen i n).getD i.1 0 := by
  rw[incLen_getD_self]
  simp
  assumption

lemma le_getD_incLen_self' {k : ℕ} (ctx : StCtx k) (i : Fin k) (n : Nat) (hc:ctx.curLen.length=k):
  n ≤ (incLen ctx.curLen i n).getD i.1 0 := by
  apply le_getD_incLen_self (k := k) ctx.curLen i n hc

/-
  PrimOKTrace_append_fwd:

  Forward direction constructor for PrimOKTrace over append.
  Used when building safety for a concatenated program from safety of its parts.
-/
lemma PrimOKTrace_append_fwd {k : ℕ}
  (ops1 ops2 : List (prim_ops k)) (ctx : StCtx k) :
  PrimOKTrace (k := k) ops1 ctx →
  PrimOKTrace (k := k) ops2 (runCtxPrim (k := k) ctx ops1) →
  PrimOKTrace (k := k) (ops1 ++ ops2) ctx := by
  induction ops1 generalizing ctx with
  | nil =>
      intro h1 h2
      simpa [PrimOKTrace, runCtxPrim] using h2
  | cons op ops ih =>
      intro h1 h2
      have hop : PrimOKForCtx (k := k) op ctx := h1.1
      have hrest : PrimOKTrace (k := k) ops (stepCtxPrim (k := k) ctx op) := h1.2
      have := ih (ctx := stepCtxPrim (k := k) ctx op) hrest h2
      exact ⟨hop, by simpa [PrimOKTrace, runCtxPrim] using this⟩

/-
  PrimOKTrace_compile1_addScaled:

  Special-case safety lemma for compile1(addScaled ...).
  The addScaled compilation emits a longer sequence containing:
  - optional negops
  - optional shift alloc/free
  - MSB widen alloc/free
  - Add

  This lemma proves PrimOKTrace for that full sequence under a uniform baseW and a
  well-formed curLen list. `compile1_simulates` uses this safety to justify applying
  the bridge lemmas in the addScaled proof.
-/
lemma PrimOKTrace_compile1_addScaled
  {k : ℕ}
  (ctx : StCtx k)
  (dst src : Fin k)
  (negSrc : Bool)
  (sh : ℕ)
  (hbase : ∀ i j : Fin k, ctx.baseW i = ctx.baseW j)
  (hcurLen:ctx.curLen.length = k)
  :
  PrimOKTrace (k := k)
    (compile1 (k := k) (.addScaled dst src negSrc sh) ctx.curLen).1 ctx := by
  by_cases hds : dst = src
  {
    simp [compile1, compile_op_to_prim_single, hds, PrimOKTrace]
  }
  {
    simp (config := { zeta := true }) [compile1, compile_op_to_prim_single, hds]
    simp[PrimOKTrace_append,PrimOKTrace_cons,PrimOKTrace_negops,PrimOKTrace_if_alloc,
          runCtxPrim_negops,
          runCtxPrim_if_alloc,
          runCtxPrim_if_free,
           stepCtxPrim]
    split_ifs with h1 h2 h3
    {
      subst h2
      simp[PrimOKTrace_nil]
      unfold PrimOKForCtx
      simp[stWidth];simp[hbase dst src]
      set a:=1 + (getLen ctx.curLen ↑dst).max (getLen ctx.curLen ↑src)
      simp[← List.getD_eq_getElem?_getD]
      rw[incLen_getD_ne',incLen_getD_self,incLen_getD_self,incLen_getD_ne'];unfold getLen; simp
      rw[← Nat.add_sub_assoc,← Nat.add_sub_assoc];
      all_goals try simp
      all_goals try rw[incLen_pres_len]
      all_goals try assumption
      all_goals try intro h;simp_all
      all_goals try unfold a;apply Nat.le_add_left_of_le;unfold getLen;simp
    }
    {
      simp[PrimOKTrace_nil]
      unfold PrimOKForCtx
      simp[stWidth];simp[hbase dst src,PrimOKTrace,PrimOKForCtx]
      set a:=1 + (getLen (incLen ctx.curLen src sh) ↑dst).max (getLen (incLen ctx.curLen src sh) ↑src)
      constructor
      {
        simp[← List.getD_eq_getElem?_getD]
        rw[incLen_getD_ne',incLen_getD_self,incLen_getD_self,incLen_getD_ne'];unfold getLen; rw[incLen_getD_ne',incLen_getD_ne',incLen_getD_self]; simp
        rw[← Nat.add_sub_assoc,← Nat.add_sub_assoc];
        all_goals try simp
        all_goals try repeat rw[incLen_pres_len];
        all_goals try assumption
        all_goals try intro h;simp_all
        all_goals try unfold a;apply Nat.le_add_left_of_le;unfold getLen;simp
        right
        rw[incLen_to_sum]
        assumption
        left
        simp[← List.getD_eq_getElem?_getD];rw[incLen_getD_ne']
        assumption;simp_all
      }
      {
        simp[← List.getD_eq_getElem?_getD]
        rw[incLen_getD_ne',incLen_getD_self]; simp
        assumption
        rw[incLen_pres_len];assumption
        intro h;simp_all
      }
    }
    {
      subst h3
      simp[PrimOKTrace_nil]
      simp[PrimOKForCtx,PrimOKTrace]
      simp[stWidth];simp[hbase dst src]
      set a:=1 + (getLen ctx.curLen ↑dst).max (getLen ctx.curLen ↑src)
      simp[← List.getD_eq_getElem?_getD]
      rw[incLen_getD_ne',incLen_getD_self,incLen_getD_self,incLen_getD_ne'];unfold getLen; simp
      rw[← Nat.add_sub_assoc,← Nat.add_sub_assoc];
      all_goals try simp
      all_goals try rw[incLen_pres_len]
      all_goals try assumption
      all_goals try intro h;simp_all
      all_goals try unfold a;apply Nat.le_add_left_of_le;unfold getLen;simp
    }
    {
      unfold PrimOKForCtx
      simp
      constructor
      {
        simp[stWidth, hbase dst src]
        set a:=1 + (getLen (incLen ctx.curLen src sh) ↑dst).max (getLen (incLen ctx.curLen src sh) ↑src); simp[← List.getD_eq_getElem?_getD,getLen]
        rw[incLen_getD_ne',incLen_getD_self,incLen_getD_ne']
        rw[incLen_getD_self,incLen_getD_ne',incLen_getD_self]
        rw[← Nat.add_sub_assoc,← Nat.add_sub_assoc]
        all_goals try simp
        all_goals try rw[incLen_pres_len]
        all_goals try assumption
        all_goals try intro h;simp_all
        all_goals try apply Nat.le_add_left_of_le;unfold getLen;simp
        all_goals try simp[← List.getD_eq_getElem?_getD]
        rw[incLen_getD_ne',incLen_getD_self];simp;all_goals try assumption
        rw[incLen_getD_ne',incLen_getD_self];simp;all_goals try assumption
        all_goals try rw[incLen_pres_len];assumption
      }
      {
        constructor
        {
          simp[PrimOKTrace,PrimOKForCtx]
          set a:=1 + (getLen (incLen ctx.curLen src sh) ↑dst).max (getLen (incLen ctx.curLen src sh) ↑src)
          simp[← List.getD_eq_getElem?_getD,getLen]
          rw[incLen_getD_self,incLen_getD_ne']
          rw[incLen_getD_self]
          set b:=ctx.curLen.getD (↑src) 0 + sh
          rw[Nat.add_assoc,Nat.sub_add_cancel]
          simp
          unfold b a
          rw[getLen_incLen_ne,getLen_incLen_eq]
          simp[getLen]
          apply Nat.le_add_left_of_le;simp
          set c:=ctx.curLen[src.val]?.getD 0 + sh
          all_goals try simp
          all_goals try rw[incLen_pres_len]
          all_goals try assumption
          all_goals try intro h;simp_all
          rw[incLen_pres_len];assumption
        }
        {
          simp[PrimOKTrace,PrimOKForCtx]
          set a:=1 + (getLen (incLen ctx.curLen src sh) ↑dst).max (getLen (incLen ctx.curLen src sh) ↑src)
          simp[← List.getD_eq_getElem?_getD,getLen]
          rw[incLen_getD_ne',incLen_getD_self];simp
          all_goals try simp
          all_goals try rw[incLen_pres_len]
          all_goals try assumption
          all_goals try intro h;simp_all
        }
      }
    }
  }


----------------------------------------------------------------------------------------------------
------------------------------- Register arithmetic helpers -----------------------------------------
----------------------------------------------------------------------------------------------------

/-
  evalRegister_shiftL:

  Symbolic shiftL corresponds to multiplying the evaluated integer by 2^n.
  This lemma is used in `bridge_allocLSB` (and in addScaled proofs) to align
  the symbolic interpretation with the concrete AllocLSB effect on BitVec storage.
-/
lemma evalRegister_shiftL {k : ℕ} (r : Register k) (ρ : Fin k → ℤ) (n : ℕ) :
  evalRegister (r.shiftL n) ρ = (evalRegister r ρ) * (2 : ℤ) ^ n := by
  unfold evalRegister Register.shiftL
  simp_rw [mul_assoc, mul_comm, ← mul_assoc]
  rw [← Finset.sum_mul,mul_comm]

#check Int.mul_emod_mul_of_pos
#check Nat.mul_mod

/-
  emod_mul_right_helper / Int.emod_mul_right:

  These lemmas support the common pattern “multiply under emod” when translating between:
  - stateToSt’s storage definition using `emod (2^w)`
  - LSB shift semantics which multiply by `2^n`
  They are used in `bridge_allocLSB` to rewrite the new stored Nat after appending zeros.
-/
/-- Scaling both the value and modulus by the same *positive* factor scales `emod`. -/
lemma emod_mul_right_helper (a b c : ℕ ) :
(a % b) * c = (a * c) % (b * c):=by {
  have h0 : c * a % (c * b) = c * (a % b) := by
    rw[Nat.mul_mod_mul_left]
  have h : (a * c) % (b * c) = (a % b) * c := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using h0
  exact h.symm
}

lemma Int.emod_mul_right (a b c : ℤ) (hc : 0 < c) :
  (a.emod b) * c = (a * c).emod (b * c) := by {
    change (a % b) * c = (a * c) % (b * c)
    have h0 : c * a % (c * b) = c * (a % b) := by
      simpa using (Int.mul_emod_mul_of_pos (a := c) a b hc)
    have h : (a * c) % (b * c) = (a % b) * c := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using h0
    exact h.symm
  }

/-
  BitVec.ofNat_append_zeros_eqv:

  Core “AllocLSB = append zeros” arithmetic fact:
  appending n zeros to a w-bit vector matches storing (oldValue * 2^n) at width w+n.
  This lemma is the key bitvector step inside `bridge_allocLSB`.
-/
lemma BitVec.ofNat_append_zeros_eqv (w n z: ℕ) :
  (BitVec.ofNat w z ++ (0#n)) ≍ BitVec.ofNat (w + n) (z * 2 ^ n) := by
  rw[BitVec.append_def]
  simp
  apply BitVec.eq_of_toNat_eq
  induction n with
  |zero=>{
    simp
  }
  |succ k ih =>{
    simp_all
    rw[Nat.shiftLeft_succ,ih]
    rw[mul_comm]
    have := emod_mul_right_helper (z*(2^k)) (2 ^ (w + k)) 2
    rw[this,pow_add,pow_add, pow_add, pow_add, pow_one]
    simp[mul_assoc]
  }

/-
  shiftRReg?_eq_some_implies_divisible / shiftRReg?_eq_some_implies_division:

  These connect the semantic condition “shiftRReg? succeeded” with the arithmetic
  facts needed to reason about division by 2^n:
  - divisibility (remainder 0)
  - the pointwise coefficient update equals division

  These are used in `bridge_freeLSB` (and in any proof that expands shiftRReg?).
-/
lemma shiftRReg?_eq_some_implies_divisible
  {k : ℕ} (σ : State k) (j : Fin k) (n : ℕ) (σ' : State k)
  (h : σ.shiftRReg? j n = some σ') :
  ∀ t, (σ j t) % ((2 : ℤ) ^ n) = 0 := by
  classical
  unfold State.shiftRReg? at h
  cases hR : Register.shiftR? (σ j) n with
  | none =>
      simp [hR] at h
  | some r' =>
      unfold Register.shiftR? at hR
      set m : ℤ := (2 : ℤ) ^ n with hm
      -- shiftR? is an if on divisibility
      by_cases hd : ∀ t, (σ j t) % m = 0
      ·
        simpa [hm] using hd
      · -- if divisibility fails, shiftR? would be none, contradiction with hR = some _
        aesop

lemma shiftRReg?_eq_some_implies_division
  {k : ℕ} (σ : State k) (j : Fin k) (n : ℕ) (σ' : State k)
  (h : σ.shiftRReg? j n = some σ') :
  ∀ t, σ' j t = (σ j t) / ((2 : ℤ) ^ n) := by
  classical
  -- unfold the do-notation
  unfold State.shiftRReg? at h

  -- split on the Option produced by Register.shiftR?
  cases hR : Register.shiftR? (σ j) n with
  | none =>
      simp [hR] at h
  | some r' =>
      have hset : State.setReg σ j r' = σ' := by
        exact Option.some.inj (by simpa [hR] using h)
      unfold Register.shiftR? at hR
      set m : ℤ := (2 : ℤ) ^ n with hm
      by_cases hd : ∀ t, (σ j t) % m = 0
      ·
        have hr' : r' = (fun t => (σ j t) / m) := by
          have : (some (fun t => (σ j t) / m) : Option (Register k)) = some r' := by
            simpa [hd] using hR
          -- extract the function equality
          exact (Option.some.inj this).symm

        intro t
        aesop
      ·
        have : (none : Option (Register k)) = some r' := by
          aesop
        cases this

/-
  shiftRReg?_some_iff:

  Packaging lemma: extracts the internal witness register r' from `shiftRReg? = some σ'`,
  along with the divisibility and division facts. Helpful for proofs that want to avoid
  re-unfolding the Option/do structure each time.
-/
lemma shiftRReg?_some_iff
  {k} {σ σ' : State k} {j : Fin k} {n : Nat}
  (h : State.shiftRReg? σ j n = some σ') :
  ∃ r',
    Register.shiftR? (σ j) n = some r' ∧
    σ' = State.setReg σ j r' ∧
    (∀ t, (σ j t) % ((2:ℤ)^n) = 0) ∧
    (∀ t, r' t = (σ j t) / ((2:ℤ)^n)) := by
    use (σ' j)
    constructor
    unfold State.shiftRReg? at *
    simp at h
    cases h_shift : (σ j).shiftR? n
    aesop
    aesop
    constructor
    unfold State.shiftRReg? at *
    simp at h
    cases h_shift : (σ j).shiftR? n
    aesop
    aesop
    constructor
    intro t
    rw[shiftRReg?_eq_some_implies_divisible σ j n σ']
    assumption
    intro t
    rw[shiftRReg?_eq_some_implies_division σ j n σ' h]

/-
  evalRegister_setReg_div_pow2:

  Main arithmetic step for `bridge_freeLSB`:
  after a successful symbolic shiftRReg?, the evaluated integer for the updated register
  is exactly the old evaluated integer divided by 2^n.

  This is the bridge between symbolic coefficient division and concrete `stateToSt` storage.
-/
lemma evalRegister_setReg_div_pow2
  {k} (σ σ' : State k) (ρ : Fin k → ℤ) (j : Fin k) (n : Nat)
  (h : State.shiftRReg? σ j n = some σ')
  : evalRegister (σ' j) ρ = evalRegister (σ j) ρ / ((2:ℤ)^n) := by
  unfold evalRegister
  have h1:=shiftRReg?_eq_some_implies_divisible σ j n σ' h
  have h2:=shiftRReg?_eq_some_implies_division σ j n σ' h
  simp[h2]
  let f:= fun x => (σ j x / 2 ^ n) * ρ x
  conv_rhs =>
    arg 1 -- Enter the numerator (the sum)
    enter [2, x]
    rw [← Int.mul_ediv_add_emod (σ j x) (2^n), h1 x]
    simp only [add_zero]
    rw[mul_assoc]
    change 2^n * (f x)
  conv_lhs =>
    arg 2
    change f
  rw [← Finset.mul_sum]
  simp





----------------------------------------------------------------------------------------------------
------------------------------- BitVec ↔ Int glue ---------------------------------------------------
----------------------------------------------------------------------------------------------------

/-
  BitVec.ofNat_emod_eq_ofInt:

  `stateToSt` stores values using `BitVec.ofNat` applied to `Int.emod ...`.
  Many BitVec lemmas about toInt are stated for `BitVec.ofInt`.
  This lemma allows switching between the two representations in bridge proofs.
-/
lemma BitVec.ofNat_emod_eq_ofInt (n : ℕ) (i : ℤ) :
    BitVec.ofNat n (i.emod (2 ^ n)).toNat = BitVec.ofInt n i := by
  apply BitVec.eq_of_toInt_eq
  simp [BitVec.toInt_ofNat']
  have h_pos : (0 : ℤ) < 2 ^ n := by
    simp
  have h_emod_nonneg : 0 ≤ i.emod (2 ^ n) :=
    Int.emod_nonneg i (ne_of_gt h_pos)
  rw [max_eq_left h_emod_nonneg]
  have := Int.emod_bmod i (2^n)
  change (i % ((2 ^ n):ℤ)).bmod (2 ^ n) = i.bmod (2 ^ n)
  aesop

#check Int.bmod_eq_bmod_iff_bmod_sub_eq_zero
