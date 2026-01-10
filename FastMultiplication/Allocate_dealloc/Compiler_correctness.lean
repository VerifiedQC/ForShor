import FastMultiplication.Allocate_dealloc.Basic


----------------------------------------------------------------------------------------------------
------------------------------- stateToSt + FITS-SIGNED PREDICATES ---------------------------------
----------------------------------------------------------------------------------------------------

/-- Evaluate a symbolic register to an integer using a valuation for the variables. -/
def evalRegister {k : ℕ} (r : Register k) (ρ : Fin k → ℤ) : ℤ :=
  ∑ j : Fin k, (r j) * (ρ j)


/-!
Bundle the extra parameters needed to interpret a symbolic `State k` as a concrete `St k`.
This avoids threading `(ρ, baseW, curLen)` everywhere.
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
  fits_all   : FitsSignedAll (σ := σ) (ctx := ctx)

open Operations
/--
One-step preservation for `ValidFor` along compilation/execution of a single op.

This is the only extra thing needed to use `ValidFor` inside the `compileProg` induction.
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
