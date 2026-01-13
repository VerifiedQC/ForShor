import FastMultiplication.Allocate_dealloc.Basic


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
    let r : Nat := Int.toNat (Int.emod z m)   -- in [0, 2^w)
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





/-- Side-condition ensuring a primitive op is safe w.r.t. the current context. -/
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

lemma PrimOKTrace_append {k : ℕ}
  (ops1 ops2 : List (prim_ops k)) (ctx : StCtx k) :
  PrimOKTrace (k := k) (ops1 ++ ops2) ctx
    ↔ PrimOKTrace (k := k) ops1 ctx ∧ PrimOKTrace (k := k) ops2 (runCtxPrim ctx ops1) := by
  induction ops1 generalizing ctx with
  | nil =>
      simp [PrimOKTrace, runCtxPrim]
  | cons op ops1 ih =>
      simp [PrimOKTrace, runCtxPrim, stepCtxPrim, ih, and_assoc]

lemma runCtxPrim_append {k} (ctx : StCtx k) (xs ys : List (prim_ops k)) :
  runCtxPrim ctx (xs ++ ys) = runCtxPrim (runCtxPrim ctx xs) ys := by
  induction xs generalizing ctx with
  | nil =>
      simp [runCtxPrim]
  | cons x xs ih =>
      simp [runCtxPrim, ih, List.cons_append, stepCtxPrim]

lemma runCtxPrim_if_nil_singleton {k}
  (ctx : StCtx k) (p : Prop) [Decidable p] (op : prim_ops k) :
  runCtxPrim ctx (if p then [] else [op])
    = if p then ctx else stepCtxPrim ctx op := by
  by_cases hp : p <;> simp [hp, runCtxPrim, stepCtxPrim]


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

lemma allocMSB_preserves_value
  {k : ℕ} (st : St k) (i : Fin k) (n : Nat) :
  BitVec.toInt ((AllocMSB st i n i).2) = BitVec.toInt ((st i).2) := by
  unfold AllocMSB
  rw [if_pos rfl]
  simp [BitVec.toInt_signExtend]

def lowBitsZero {w : Nat} (bv : BitVec w) (n : Nat) : Prop :=
  ∀ t : Nat, t < n → Nat.testBit bv.toNat t = false

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


-- lemma freeLSB_undo_shift
--   {k : ℕ} (st : St k) (i : Fin k) (n : Nat)
--   (hn : n ≤ (st i).fst)
--   (h0 : lowBitsZero (st i).2 n) :
--   BitVec.toInt ((FreeLSB st i n i).2)
--     = BitVec.toInt ((st i).2) / (2 : ℤ) ^ n := by
--   unfold FreeLSB
--   simp[lowBitsZero] at *
--   rw[if_pos rfl]
--   aesop
--   sorry





-- def msbFreedAreSignExt {w : Nat} (bv : BitVec w) (n : Nat) : Prop :=
--   -- “the top n bits equal the sign bit of the kept part”
--   True  -- fill in

-- #check BitVec.sshiftRight

-- lemma freeMSB_preserves_value
--   {k : ℕ} (st : St k) (i : Fin k) (n : Nat)
--   (hs : msbFreedAreSignExt (st i).2 n) :
--   BitVec.toInt ((FreeMSB st i n i).2)
--     = BitVec.toInt ((st i).2) := by
--   unfold FreeMSB
--   rw[if_pos rfl]
--   sorry

-- lemma adder_correct_equiv
--   {k : ℕ} (st : St k) (dst src : Fin k) :
--   ((Adder st dst src dst).2) ≍ BitVec.add (st dst).2 (BitVec.truncate (st dst).1 (st src).2) := by
--   -- Usually rfl after unfolding Adder;
--   unfold Adder
--   sorry


lemma eval_prim_ops_append {k : ℕ}
  (xs ys : List (prim_ops k)) (st : St k) :
  eval_prim_ops (k := k) (xs ++ ys) st
    = eval_prim_ops (k := k) ys (eval_prim_ops (k := k) xs st) := by
  induction xs generalizing st with
  | nil =>
      simp [eval_prim_ops]
  | cons x xs ih =>
      simp [eval_prim_ops, ih, List.cons_append]

lemma eval_prim_ops_singleton {k : ℕ} (p : prim_ops k) (st : St k) :
  eval_prim_ops (k := k) [p] st = eval_prim_op_single (k := k) p st := by
  simp [eval_prim_ops]


----------------------------------------------------------------------------------------------------
------------------------------- List/len bookkeeping lemmas -----------------------------------------
----------------------------------------------------------------------------------------------------

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

@[simp]lemma incLen_to_sum
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

@[simp]lemma decLen_to_diff
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



@[simp]lemma decLen_incLen_cancel (i:Fin k) (curLen:List ℕ):
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

@[simp]lemma incLen_decLen_cancel (i:Fin k) (curLen:List ℕ) (hN: ∀ x ∈ curLen, n≤x):
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

@[simp]lemma incLen_incLen_add (i:Fin k) (curLen:List ℕ) :
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




/-- `setLen` at two different `Fin` indices commutes. -/
lemma setLen_setLen_comm
    {k : ℕ} (curLen : List ℕ) (i j : Fin k) (vi vj : ℕ)
    (hijNat : (↑i : Nat) ≠ (↑j : Nat)) :
    setLen (setLen curLen i vi) j vj = setLen (setLen curLen j vj) i vi := by
  -- unfold to `setAt` and apply `setAt_setAt_comm`
  simpa [setLen] using
    (setAt_setAt_comm (xs := curLen) (i := (↑i)) (j := (↑j)) (a := vi) (b := vj) hijNat)


/-! ### Disjoint commutation lemmas for inc/dec -/

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


@[simp]theorem getElem?_setAt_ne {α} (xs : List α) (idx m : ℕ) (v : α) (hne : m ≠ idx) :
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

@[simp] theorem incLen_zero (curLen : List ℕ) (i : Fin k) :
  incLen curLen i 0 = curLen := by
  simpa [incLen, setLen, getLen, Nat.add_zero] using
    (setAt_getD (xs := curLen) (idx := i.val) (d := (0 : Nat)))

@[simp] theorem decLen_zero {k : ℕ} (curLen : List Nat) (i : Fin k) :
  decLen curLen i 0 = curLen := by
  simpa [decLen, setLen, getLen, Nat.sub_zero] using
    (setAt_getD (xs := curLen) (idx := i.val) (d := (0 : Nat)))

@[simp] lemma stateToSt_fst {k : ℕ}
  (σ : State k) (ctx : StCtx k) (j : Fin k) :
  (stateToSt σ ctx j).fst = ctx.baseW j + ctx.curLen.getD j.val 0 := by
  simp [stateToSt]


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

lemma incLen_getD_ne'
  {k : ℕ} (curLen : List Nat) (i j : Fin k) (n : Nat)
  (hcurLen : curLen.length = k) (hij : j ≠ i) :
  (incLen curLen i n).getD j.1 0 = curLen.getD j.1 0 := by
  -- unfold incLen / setLen (matches your earlier proofs)
  unfold incLen setLen
  simp
  rw [getElem?_setAt_ne curLen i.val j.val (getLen curLen i.val + n)]
  subst hcurLen
  simp
  intro ha;omega
-- Your goal: FitsSignedAt preserved when increasing curLen at some i.
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
      stWidth (ctx := ctx) j ≤ stWidth (ctx := { ρ := ctx.ρ, baseW := ctx.baseW, curLen := incLen ctx.curLen i n }) j := by
    unfold stWidth
    -- reduce to a fact about curLen.getD
    apply Nat.add_le_add_left
    by_cases hji : j = i
    · subst hji
      simp_all
      rw[← incLen_to_sum]
      aesop
      apply hcurLen
    ·
      have hget : (incLen ctx.curLen i n).getD j.val 0 = ctx.curLen.getD j.val 0 := by
        -- use your existing lemma name here
        simpa using incLen_getD_ne' (k := k) (curLen := ctx.curLen) (i := i) (j := j) (n := n) hcurLen hji
      aesop

  have hjFits : FitsSigned (stWidth (ctx := ctx) j) (evalRegister (σ j) ctx.ρ) := by
    simpa [FitsSignedAt] using hj

  have hjFits' :
      FitsSigned (stWidth (ctx := { ρ := ctx.ρ, baseW := ctx.baseW, curLen := incLen ctx.curLen i n }) j)
        (evalRegister (σ j) ctx.ρ) :=
    FitsSigned_mono (w := stWidth (ctx := ctx) j)
                   (w' := stWidth (ctx := { ρ := ctx.ρ, baseW := ctx.baseW, curLen := incLen ctx.curLen i n }) j)
                   (z := evalRegister (σ j) ctx.ρ) hw hjFits

  simpa [FitsSignedAt] using hjFits'

lemma ValidFor_incLen(i:Fin k) (σ : State k) (ctx : StCtx k) (hV : ValidFor σ ctx):
  ValidFor (σ) {ρ:=ctx.ρ, baseW:= ctx.baseW, curLen:= (incLen (ctx.curLen) i n)}:=by {
    induction hV
    rename_i hcurLen baseW_eq fitsAll
    constructor
    simp[incLen_pres_len,hcurLen]
    intro j
    unfold FitsSignedAll at *
    intro j_1
    simp;apply baseW_eq
    apply FitsSignedAt_incLen σ ctx hcurLen fitsAll
  }

----------------------------------------------------------------------------------------------------
------------------------------- Register arithmetic helpers -----------------------------------------
----------------------------------------------------------------------------------------------------

lemma evalRegister_shiftL {k : ℕ} (r : Register k) (ρ : Fin k → ℤ) (n : ℕ) :
  evalRegister (r.shiftL n) ρ = (evalRegister r ρ) * (2 : ℤ) ^ n := by
  unfold evalRegister Register.shiftL
  simp_rw [mul_assoc, mul_comm, ← mul_assoc]
  rw [← Finset.sum_mul,mul_comm]

#check Int.mul_emod_mul_of_pos
#check Nat.mul_mod

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

-- exact shape you want to prove/use once:
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

-- This is the key lemma you can prove *just from h*:
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
