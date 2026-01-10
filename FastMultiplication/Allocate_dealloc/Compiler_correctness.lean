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


----------------------------------------------------------------------------------------------------
------------------------------- Bridge lemmas: prim-op ⇔ symbolic -----------------------------------
----------------------------------------------------------------------------------------------------

-- LSB alloc simulates symbolic shiftL, and updates delta-len
lemma bridge_allocLSB
  {k : ℕ} (σ : State k) (ctx : StCtx k)
  (vF : ValidFor σ ctx)
  (i : Fin k) (n : Nat) :
  eval_prim_op_single (k := k) (prim_ops.Alloc i true n) (stateToSt (k := k) σ ctx)
    =
  stateToSt (k := k) (State.shiftLReg σ i n) { ctx with curLen := incLen ctx.curLen i n } := by
  have hcurLen:=vF.curLen_len
  cases ctx with
  | mk ρ baseW curLen =>
    -- now hcurLen : curLen.length = k, goal is the old one modulo packaging
    unfold eval_prim_op_single
    simp
    unfold AllocLSB
    funext j
    split_ifs with h1
    ·
      subst h1
      unfold stateToSt
      simp
      constructor
      ·
        rw [add_assoc, incLen_to_sum]
        rw [hcurLen]
      ·
        have hW :
          baseW j + (incLen curLen j n).getD j.val 0 = (baseW j + curLen.getD j.val 0) + n := by
          have hinc := incLen_getD_self (k := k) (curLen := curLen) (n := n) (j := j) hcurLen
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            congrArg (fun t => baseW j + t) hinc

        have hE :
            evalRegister ((σ j).shiftL n) ρ = (evalRegister (σ j) ρ) * (2 : ℤ) ^ n := by
          simpa using evalRegister_shiftL (r := (σ j)) (ρ := ρ) (n := n)

        have :=
          BitVec.ofNat_append_zeros_eqv
            (baseW j + curLen.getD (j.val) 0) n
            (((evalRegister (σ j) ρ).emod (2 ^ (baseW j + curLen[j.val]?.getD 0))).toNat)

        apply HEq.trans this
        rw [hW, hE]
        simp [pow_add]

        have h_mod_rhs :
          2 ^ baseW j * 2 ^ (incLen curLen j n)[j.val]?.getD 0
            =
          2 ^ (baseW j + curLen.getD (j.val) 0) * 2 ^ n := by
          rw [← Nat.pow_add, ← Nat.pow_add]
          aesop

        congr
        set a := (evalRegister (σ j) ρ)
        rw [← incLen_to_sum, pow_add, ← mul_assoc]
        set b := ((2 : ℤ) ^ baseW j * 2 ^ curLen[j.val]?.getD 0)
        norm_cast
        rw [← Int.emod_mul_right, Int.toNat_mul]
        simp
        left
        norm_cast
        apply Int.emod_nonneg
        aesop
        aesop
        aesop
        assumption
    ·
      unfold stateToSt
      simp_all
      constructor
      ·
        unfold incLen setLen
        have := getElem?_setAt_ne curLen (i.val) (j.val) (v := (getLen curLen ↑i + n))
        rw [this]
        subst hcurLen
        simp_all
        simp_all only [ne_eq]
        apply Aesop.BuiltinRules.not_intro
        intro a
        have : j = i := by omega
        contradiction
      ·
        have : (incLen curLen i n).getD (j.val) 0 = curLen.getD (j.val) 0 := by
          unfold incLen setLen
          simp_all
          rw [getElem?_setAt_ne curLen i.val j.val (getLen curLen i.val + n)]
          subst hcurLen
          simp_all
          simp_all only [ne_eq]
          apply Aesop.BuiltinRules.not_intro
          intro a
          have : j = i := by omega
          contradiction
        rw [this]
        aesop

-- MSB alloc is sign-extend: symbolic value unchanged, only length delta updates
lemma bridge_allocMSB
  {k : ℕ} (σ : State k) (ctx : StCtx k)
  (hV : ValidFor (k := k) σ ctx)
  (i : Fin k) (n : Nat) :
  eval_prim_op_single (k := k) (prim_ops.Alloc i false n) (stateToSt (k := k) σ ctx)
    =
  stateToSt (k := k) σ { ctx with curLen := incLen ctx.curLen i n } := by
  cases ctx with
  | mk ρ baseW curLen =>
    have hcurLen : curLen.length = k := by
      simpa using hV.curLen_len
    have hfit_i : FitsSigned (baseW i + curLen.getD i.val 0) (evalRegister (σ i) ρ) := by
      simpa [FitsSignedAt, stWidth] using (hV.fits_all i)

    have ha : 0 < baseW i + curLen.getD i.val 0 := hfit_i.1
    have hb_lo : -(2:ℤ) ^ ((baseW i + curLen.getD i.val 0)-1) ≤ evalRegister (σ i) ρ := hfit_i.2.1
    have hb_hi : evalRegister (σ i) ρ <  (2:ℤ) ^ ((baseW i + curLen.getD i.val 0)-1) := hfit_i.2.2

    unfold eval_prim_op_single
    simp
    unfold AllocMSB
    funext j
    split_ifs with h1
    ·
      subst h1
      unfold stateToSt
      simp
      constructor
      ·
        rw[add_comm, add_assoc,incLen_to_sum]
        exact hcurLen
      ·
        set l := (n + (baseW j + curLen.getD (j.val) 0))
        rw[← incLen_to_sum]
        set a := (baseW j + curLen.getD (j.val) 0)
        conv =>
          lhs
          change BitVec.signExtend l (BitVec.ofNat a ((evalRegister (σ j) ρ).emod (2 ^ a)).toNat)
        set b := (evalRegister (σ j) ρ)
        have hl : baseW j + (incLen curLen j n).getD (↑j) 0 = a + n := by
          have := incLen_to_sum k curLen n j hcurLen
          -- keep the exact same steps you had
          simp_all [a]
          rw[← this, add_assoc]
        have := BitVec.toInt_signExtend_eq_toNat_bmod (v := l) (w := a)
          ((BitVec.ofNat a (b.emod (2 ^ a)).toNat))
        simp[BitVec.ofNat_emod_eq_ofInt]
        rw[hl]
        simp [l, Nat.add_comm, Nat.add_left_comm]
        have :(incLen ?curLen ?j ?n)[↑j]?.getD 0 = (incLen curLen j n).getD (↑j) 0 := by simp
        rw[← this] at hl
        have hl2 : n + (baseW j + curLen.getD (j.val) 0) = a + n := by
          rw[add_comm, add_assoc]
        rw[hl2]
        simp_all
        have := BitVec.toInt_inj
          (x := BitVec.signExtend (a + n) (BitVec.ofInt a b))
          (y := BitVec.ofNat (a + n) (b.emod (2 ^ (a + n))).toNat).mp
        apply this
        rw[BitVec.toInt_signExtend]
        simp
        have := BitVec.toInt_ofNat' (n := a + n) (b.emod (2 ^ (a + n))).toNat
        simp[this]
        have := Int.emod_nonneg b (b := (2 ^ (a + n))) (by simp)
        have : max (b.emod (2 ^ (a + n))) 0 = (b.emod (2 ^ (a + n))) := by
          simp
          exact this
        rw[this]
        have := Int.emod_bmod b ((2) ^ (a + n))
        have h2 :
          (b.emod (2 ^ (a + n))).bmod (2 ^ (a + n))
            =
          (b % (((2 ^ (a + n)):ℕ):ℕ)).bmod (2 ^ (a + n)) := by
          simp_all [a, l, b]
          exact this
        rw[h2, this]
        simp_all only
        have hbmod_a : b.bmod (2^a) = b := by
          have h1 : (BitVec.ofInt a b).toInt = b :=
            BitVec.toInt_ofInt_eq_self (w := a) ha hb_lo hb_hi
          have h2 : (BitVec.ofInt a b).toInt = b.bmod (2^a) := by aesop
          exact by aesop
        have hbmod_an : b.bmod (2^(a+n)) = b := by
          have ha' : 0 < a + n := by
            exact lt_of_lt_of_le ha (Nat.le_add_right a n)
          have h_exp : a - 1 ≤ a + n - 1 := by
            omega
          have hpow : (2 : ℤ) ^ (a - 1) ≤ (2 : ℤ) ^ (a + n - 1) := by
            have := Nat.pow_le_pow_right (n := (2)) (by simp) (i := a-1) (j := a+n-1) h_exp
            norm_cast
          clear hl hl2 h2 this
          repeat clear this
          have hb_hi' : b < (2 : ℤ) ^ (a + n - 1) := by
            exact lt_of_lt_of_le hb_hi hpow
          have hb_lo' : -(2 : ℤ) ^ (a + n - 1) ≤ b := by
            have hneg : -(2 : ℤ) ^ (a + n - 1) ≤ -(2 : ℤ) ^ (a - 1) := by
              exact neg_le_neg hpow
            exact le_trans hneg hb_lo
          have h_toInt : (BitVec.ofInt (a + n) b).toInt = b :=
            BitVec.toInt_ofInt_eq_self (w := a + n) ha' hb_lo' hb_hi'
          have h_bmod : (BitVec.ofInt (a + n) b).toInt = b.bmod (2 ^ (a + n)) := by
            aesop
          aesop
        simp[hbmod_a, hbmod_an]
        exact hcurLen
    ·
      unfold stateToSt
      simp_all
      constructor
      ·
        unfold incLen setLen
        rw[getElem?_setAt_ne]
        subst hcurLen
        simp_all
        simp_all only [ne_eq]
        apply Aesop.BuiltinRules.not_intro
        intro a
        have: j=i := by omega
        contradiction
      ·
        have:(incLen curLen i n).getD (j.val) 0 = curLen.getD (j.val) 0 := by
          unfold incLen setLen
          simp_all
          rw[getElem?_setAt_ne curLen i.val j.val (getLen curLen i.val + n)]
          subst hcurLen
          simp_all
          simp_all only [ne_eq]
          apply Aesop.BuiltinRules.not_intro
          intro a
          have: j=i := by omega
          contradiction
        rw[this]
        aesop

-- Negate
lemma bridge_negate
  {k : ℕ} (σ : State k) (ctx : StCtx k)
  (i : Fin k) :
  eval_prim_op_single (k := k) (prim_ops.negate i) (stateToSt (k := k) σ ctx)
    =
  stateToSt (k := k) (State.negateReg σ i) ctx := by
  cases ctx with
  | mk ρ baseW curLen =>
    unfold eval_prim_op_single
    simp
    unfold Negation
    funext j
    split_ifs with h1
    ·
      unfold stateToSt
      subst h1
      simp_all
      set a := (baseW j + curLen.getD (j.val) 0)
      unfold Register.negate evalRegister
      have h_sum :
          (∑ j_1, (fun j_2 => -σ j j_2) j_1 * ρ j_1) = -(∑ j_1, σ j j_1 * ρ j_1) := by
        simp only [neg_mul, Finset.sum_neg_distrib]
      rw[h_sum]
      set S := ∑ j_1, σ j j_1 * ρ j_1
      have h_ofInt_lhs : BitVec.ofNat a (S.emod (2 ^ a)).toNat = BitVec.ofInt a S := by
        simp [BitVec.ofInt]
        conv =>
          lhs
          change BitVec.ofNat a (S % (2 ^ a)).toNat
        rw[BitVec.ofNatLT_eq_ofNat]
      have h_ofInt_rhs : BitVec.ofNat a ((-S).emod (2 ^ a)).toNat = BitVec.ofInt a (-S) := by
        simp [BitVec.ofInt]
        conv =>
          lhs
          change BitVec.ofNat a ((-S) % (2 ^ a)).toNat
        rw[BitVec.ofNatLT_eq_ofNat]
      change -BitVec.ofNat a (S.emod (2 ^ (a))).toNat = BitVec.ofNat a ((-S).emod (2 ^ (a))).toNat
      rw [h_ofInt_lhs, h_ofInt_rhs]
      rw[BitVec.ofInt_neg]
    ·
      unfold stateToSt
      simp_all


-- Add / Free bridges (stubs kept as-is)

lemma bridge_add
  {k : ℕ} (σ : State k) (ctx : StCtx k)
  (dst src : Fin k) :
  eval_prim_op_single (k := k) (prim_ops.Add dst src) (stateToSt (k := k) σ ctx)
    =
  stateToSt (k := k) (State.addScaledReg σ dst src false 0) ctx := by

  sorry

lemma bridge_freeLSB
  {k : ℕ} (σ σ' : State k) (ctx : StCtx k)
  (i : Fin k) (n : Nat)
  (hn : n ≤ ctx.curLen.getD i.1 0)
  (h : State.shiftRReg? σ i n = some σ')
  (hV : ValidFor (k := k) σ ctx)

  :
  eval_prim_op_single (k := k) (prim_ops.Free i true n) (stateToSt (k := k) σ ctx)
    =
  stateToSt (k := k) σ' { ctx with curLen := decLen ctx.curLen i n } := by
  have hcurLen: ctx.curLen.length=k:=by simpa using hV.curLen_len
  cases ctx with
  | mk ρ baseW curLen =>
    unfold eval_prim_op_single
    simp
    unfold FreeLSB
    funext j
    split_ifs with h1
    ·
      subst h1
      unfold stateToSt
      simp
      constructor
      {
        rw[add_comm, add_comm, Nat.add_sub_assoc,decLen_to_diff]
        simpa using hV.curLen_len
        aesop
      }
      {
        rw[← decLen_to_diff,← Nat.add_sub_assoc]
        set a:=(baseW j + curLen[j.val]?.getD 0)
        have:(decLen curLen j n).getD (j.val) 0= curLen.getD (j.val) 0 - n:= by
          simp
          rw[decLen_to_diff]
          simp[hcurLen]
        rw[this]
        rw[← Nat.add_sub_assoc]
        set b:=baseW j + curLen.getD (j.val) 0 - n
        {
          have h1:=evalRegister_setReg_div_pow2 σ σ' ρ j n h
          rw[h1]
          set c:=(evalRegister (σ j) ρ)
          congr
          have h_emod_range : (c.emod (2 ^ a)).toNat < 2 ^ a := by
            simp
            have:=Int.emod_lt ((c)) (b:=2^a) (by simp)
            aesop
          rw [Nat.mod_eq_of_lt h_emod_range]
          have h_exp : (2:ℤ) ^ a = 2 ^ n * 2 ^ (a - n) := by
            rw [← pow_add, Nat.add_sub_cancel']
            unfold a
            simp at hn;linarith
          rw[h_exp]
          change (c % (2 ^ n * 2 ^ (a - n))).toNat / (2) ^ n = ((c / 2 ^ n) % (2 ^ (a - n))).toNat
          --rw[Int.toNat_emod, Int.toNat_emod, Int.toNat_mul]
          have h1:2^n=((2:ℤ) ^ n).toNat:= by norm_cast
          rw[h1]
          set N : ℤ := (2 : ℤ) ^ n
          set K : ℤ := (2 : ℤ) ^ (a - n)
          set M : ℤ := N * K

          have hNpos : 0 < N := by
            unfold N; simp
          have hKpos : 0 < K := by
            unfold K; simp
          have hMpos : 0 < M := by
            simpa [M] using mul_pos hNpos hKpos

          have hN0 : N ≠ 0 := ne_of_gt hNpos
          have hK0 : K ≠ 0 := ne_of_gt hKpos

          set r : ℤ := c % M
          set q : ℤ := c / M

          have h_decomp : r + M * q = c := by
            simpa [r, q] using (Int.emod_add_mul_ediv c M)

          have hr_nonneg : 0 ≤ r := by
            simpa [r] using Int.emod_nonneg c (ne_of_gt hMpos)
          have hr_lt : r < M := by
            simpa [r] using Int.emod_lt_of_pos c hMpos

          -- N divides M*q (since M = N*K)
          have hNdvd : N ∣ M * q := by
            refine ⟨K * q, ?_⟩
            simp [M, mul_assoc]

          -- Divide the decomposition by N; since N ∣ M*q, division distributes
          have h_div_by_N : c / N = r / N + K * q := by
            calc
              c / N = (r + M * q) / N := by simp[h_decomp]
              _ = r / N + (M * q) / N := by
                    simpa using (Int.add_ediv_of_dvd_right (a := r) (b := M*q) (c := N) hNdvd)
              _ = r / N + K * q := by
                    -- (M*q)/N = (N*(K*q))/N = K*q
                    have : (M * q) / N = K * q := by
                      calc
                        (M * q) / N = (N * (K * q)) / N := by
                          simp [M, mul_assoc]
                        _ = K * q := by
                          simpa using (Int.mul_ediv_cancel_left (a := N) (b := K*q) hN0)
                    simp[this]

          have h_rem : (c / N) % K = r / N := by
            have hrN_nonneg : 0 ≤ r / N := by
              -- ediv_nonneg_iff_of_pos : 0 ≤ r / N ↔ 0 ≤ r when N>0
              have := (Int.ediv_nonneg_iff_of_pos (a := r) (b := N) hNpos)
              exact this.mpr hr_nonneg

            have hrN_lt_absK : r / N < |K| := by
              -- From r < N*K = M, we get r/N < K (since N>0). Then |K| = K.
              have hrN_ltK : r / N < K := by
                -- rewrite hr_lt : r < N*K but in the order needed for ediv_lt_of_lt_mul
                have hr_lt' : r < K * N := by
                  simpa [M, mul_assoc, mul_left_comm, mul_comm] using hr_lt
                -- standard lemma: if 0 < N and r < K*N then r/N < K
                exact Int.ediv_lt_of_lt_mul hNpos hr_lt'
              simpa [abs_of_pos hKpos] using hrN_ltK

            have hx :
                (c / N) / K = q ∧ (c / N) % K = r / N := by
              constructor
              rw [h_div_by_N]
              rw [Int.add_mul_ediv_left _ _ hK0]
              have : r / N / K = 0 := by
                apply Int.ediv_eq_zero_of_lt hrN_nonneg
                rwa [abs_of_pos hKpos] at hrN_lt_absK
              rw [this, Int.zero_add]
              rw [h_div_by_N]
              rw [Int.add_mul_emod_self_left]
              apply Int.emod_eq_of_lt hrN_nonneg
              rwa [abs_of_pos hKpos] at hrN_lt_absK
            exact hx.2

          have h_toNat_div : r.toNat / N.toNat = (r / N).toNat := by
            have hrN_nonneg : 0 ≤ r / N := by
              have := (Int.ediv_nonneg_iff_of_pos (a := r) (b := N) hNpos)
              exact this.mpr hr_nonneg
            have hcoe : ((r.toNat / N.toNat : Nat) : ℤ) = r / N := by
              have hr_cast : (r.toNat : ℤ) = r := by
                simp [Int.toNat_of_nonneg hr_nonneg]
              have hN_cast : (N.toNat : ℤ) = N := by
                simp[Int.toNat_of_nonneg (le_of_lt hNpos)]
              simp[hr_cast, hN_cast]
            have := congrArg Int.toNat hcoe
            have h1:=Int.toNat_of_nonneg hrN_nonneg

            have h2:(0:ℤ)≤ r.toNat / N.toNat:=by simp_all
            have h3:=Int.toNat_of_nonneg h2
            rw[← this]
            norm_cast at h3
          calc
            (c % (2 ^ n * 2 ^ (a - n))).toNat / ((2:ℤ) ^ n).toNat
                = r.toNat / N.toNat := by
                    simp [r, N, K, M]
            _   = (r / N).toNat := by simp [h_toNat_div]
            _   = ((c / N) % K).toNat := by simp[h_rem]
            _   = (c / 2 ^ n % 2 ^ (a - n)).toNat := by
                    simp [N, K]

        }
        assumption
        assumption
        assumption
      }

    ·
      unfold stateToSt
      simp_all
      constructor
      ·
        unfold decLen setLen
        rw[getElem?_setAt_ne]
        subst hcurLen
        simp_all
        simp_all only [ne_eq]
        apply Aesop.BuiltinRules.not_intro
        intro a
        have: j=i := by omega
        contradiction
      ·
        have:(decLen curLen i n).getD (j.val) 0 = curLen.getD (j.val) 0 := by
          unfold decLen setLen
          simp_all
          rw[getElem?_setAt_ne curLen i.val j.val (getLen curLen i.val - n)]
          simp_all
          simp_all only [ne_eq]
          apply Aesop.BuiltinRules.not_intro
          intro a
          have: j=i := by omega
          contradiction
        rw[this]
        unfold State.shiftRReg? at h
        cases hR : Register.shiftR? (σ i) n with
        | none =>
            simp [hR] at h
        | some r' =>
            have hσ' : σ' = State.setReg σ i r' := by
              exact (Option.some.inj (by simpa [hR] using h)).symm
            have hreg : σ' j = σ j := by
              subst hσ'
              unfold State.setReg
              have : (j = i) = False := by
                exact propext ⟨(fun hj => False.elim (h1 hj)), (fun hf => False.elim hf)⟩
              simp [h1]
            have hlenj :
              (decLen curLen i n)[↑j]?.getD 0 = curLen.getD (↑j) 0 := by
                unfold decLen setLen
                simp_all
                rw[getElem?_setAt_ne curLen i.val j.val (getLen curLen i.val - n)]
                simp[hcurLen]
                simp_all
                intro a
                have: j=i := by omega
                contradiction
            simp [hreg]
            congr
            unfold decLen setLen
            simp_all
            rw[getElem?_setAt_ne]
            aesop
            intro a
            have: j=i := by omega
            contradiction



lemma bridge_freeMSB
  {k : ℕ} (σ : State k) (ctx : StCtx k)
  (i : Fin k) (n : Nat)
  (hV : ValidFor (k := k) σ ctx)
  :
  eval_prim_op_single (k := k) (prim_ops.Free i false n) (stateToSt (k := k) σ ctx)
    =
  stateToSt (k := k) σ { ctx with curLen := decLen ctx.curLen i n } := by
  sorry

----------------------------------------------------------------------------------------------------
------------------------------- Compiler simulation theorems ----------------------------------------
----------------------------------------------------------------------------------------------------

lemma negate_add_negate_eq_addScaled_true0
  {k : ℕ} (σ : State k) (dst src : Fin k) (hds:dst≠src):
  State.negateReg (State.addScaledReg (State.negateReg σ src) dst src false 0) src
    =
  State.addScaledReg σ dst src true 0 := by
  ext i j
  by_cases hid : i = dst
  · rw[hid]
    aesop
  · by_cases his : i = src
    · subst his
      simp [State.negateReg, State.addScaledReg, State.setReg, hid]
    ·
      simp [State.negateReg, State.addScaledReg, State.setReg, hid, his]

theorem compile1_simulates
  {k : ℕ}
  (op : valid_ops k)
  (σ : State k)
  (ctx : StCtx k)
  (hV : ValidFor (k := k) σ ctx)
  (σ2 : State k)
  (hstep : applyOp? σ op = some σ2)
  (hOK : Prog.OpOK op) :
  let (opsP, curLen') := compile1 (k := k) op ctx.curLen
  eval_prim_ops (k := k) opsP (stateToSt (k := k) σ ctx)
    =
  stateToSt (k := k) σ2 { ctx with curLen := curLen' } := by
  cases ctx with
  | mk ρ baseW curLen =>
    have hcurLen : curLen.length = k := by
      simpa using hV.curLen_len

    cases op with
    | shiftL i n =>
        simp [compile1, compile_op_to_prim_single, applyOp?] at hstep ⊢
        cases hstep
        simpa [eval_prim_ops_singleton] using
          (bridge_allocLSB (k := k) (σ := σ) (ctx := ⟨ρ, baseW, curLen⟩)
            (vF := hV) (i := i) (n := n))

    | shiftR i n =>
        simp [compile1, compile_op_to_prim_single, applyOp?] at hstep ⊢
        have:=(bridge_freeLSB (k := k) (σ := σ) (σ' := σ2) (ctx := ⟨ρ, baseW, curLen⟩)
            (i := i) (n := n) (h := hstep) (hV:=hV))
        sorry

    | negate i =>
        simp [compile1, compile_op_to_prim_single, applyOp?] at hstep ⊢
        cases hstep
        simpa [eval_prim_ops_singleton] using
          (bridge_negate (k := k) (σ := σ) (ctx := ⟨ρ, baseW, curLen⟩) (i := i))

    | phaseProduct i =>
        simp [compile1, compile_op_to_prim_single, applyOp?, eval_prim_ops, eval_prim_op_single] at *
        simp [hstep]

    | addScaled dst src negSrc sh =>
        by_cases hds : dst = src
        ·
          simp [compile1, compile_op_to_prim_single, hds, applyOp?] at hstep ⊢
          cases hstep
          simp [eval_prim_ops]
          simp [Prog.OpOK] at hOK
          contradiction
        ·
          -- from here down, keep your original proof block almost verbatim;
          -- only replace `(stateToSt σ ρ baseW curLen)` with `stateToSt σ ⟨ρ,baseW,curLen⟩`.
          simp [compile1, compile_op_to_prim_single, hds, applyOp?] at hstep ⊢
          split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 <;> simp
          ·
            subst h1 hstep h2
            simp_all
            ext j
            by_cases hjd : j = dst
            ·
              subst hjd
              simp [State.addScaledReg, Register.addScaled]
              have hL :
                  (eval_prim_ops (k := k)
                      [prim_ops.negate src, prim_ops.Add j src, prim_ops.negate src]
                      (stateToSt (k := k) σ ⟨ρ, baseW, curLen⟩) j).fst
                    =
                  (stateToSt (k := k) σ ⟨ρ, baseW, curLen⟩ j).fst := by
                simp [eval_prim_ops, eval_prim_op_single, Negation, Adder, hds]

              have hR :
                  (stateToSt (k := k) (σ.setReg j (fun t => σ j t + -σ src t)) ⟨ρ, baseW,
                      (decLen (decLen (incLen (incLen (incLen curLen src 0) j 0) src 0) src 0) src 0)⟩ j).fst
                    =
                  (stateToSt (k := k) σ ⟨ρ, baseW, curLen⟩ j).fst := by
                simp [stateToSt]
              aesop
            ·
              have hds2 : ¬ src = dst := by sorry
              by_cases hjs : j = src
              ·
                subst hjs
                simp [eval_prim_ops, eval_prim_op_single, Negation, Adder, hjd, Fin.ext_iff]
              ·
                simp [eval_prim_ops, eval_prim_op_single, Negation, Adder, hjd, hjs]

            have hSt :
              eval_prim_ops (k := k)
                  [prim_ops.negate src, prim_ops.Add dst src, prim_ops.negate src]
                  (stateToSt (k := k) σ ⟨ρ, baseW, curLen⟩)
                =
              stateToSt (k := k) (State.addScaledReg σ dst src true 0) ⟨ρ, baseW, curLen⟩ := by
              simp [eval_prim_ops]
              simp [bridge_negate]
              rw [bridge_add (k := k)
                    (σ := State.negateReg σ src) (ctx := ⟨ρ, baseW, curLen⟩)
                    (dst := dst) (src := src)]
              rw [bridge_negate (k := k)
                    (σ := State.addScaledReg (State.negateReg σ src) dst src false 0)
                    (ctx := ⟨ρ, baseW, curLen⟩) (i := src)]
              simp [negate_add_negate_eq_addScaled_true0 σ dst src hds]
            rw [hSt]
          ·
            subst h1 hstep h2
            simp_all only [incLen_zero, decLen_zero]
            sorry
          all_goals sorry


lemma compile1_pres_len {k} (op : valid_ops k) (curLen : List Nat)
  (h : curLen.length = k) :
  (compile1 (k:=k) op curLen).2.length = k :=by
  cases op with
  |shiftL i sh=>{
    unfold compile1 compile_op_to_prim_single
    simp[incLen_pres_len,h]
  }
  |shiftR i sh=>{
    unfold compile1 compile_op_to_prim_single
    simp[decLen_pres_len,h]
  }
  |addScaled dst src negsrc sh=>{
    unfold compile1 compile_op_to_prim_single
    simp
    split_ifs with h1 h2<;>simp[h,incLen_pres_len,decLen_pres_len]
  }
  |negate=>{
    unfold compile1 compile_op_to_prim_single
    simp[h]
  }
  |phaseProduct=>{
    unfold compile1 compile_op_to_prim_single
    simp[h]
  }

theorem compileProg_simulates_go
  {k : ℕ}
  (ops : Prog k)
  (σ : State k)
  (ctx0 : StCtx k)
  (curLenNow : List Nat)
  (σ2 : State k)
  (hstep : run? (k := k) ops σ = some σ2)
  (hOK : Prog.WellFormed ops)
  (hV : ValidFor (k := k) σ { ctx0 with curLen := curLenNow })
  (hStepValid : ValidForStep (k := k) ctx0) :
  let ctxNow : StCtx k := { ctx0 with curLen := curLenNow }
  let (opsP, curLen') := compileProg (k := k) ops curLenNow
  eval_prim_ops (k := k) opsP (stateToSt (k := k) σ ctxNow)
    =
  stateToSt (k := k) σ2 { ctx0 with curLen := curLen' } := by
  induction ops generalizing σ curLenNow σ2 with
  | nil =>
      simp [run?] at hstep
      cases hstep
      simp [compileProg, eval_prim_ops]
  | cons op ops ih =>
      have hOK_head : Prog.OpOK op := by
        aesop
      have hOK_tail : Prog.WellFormed ops := by
        -- same as your existing proof
        simp [Prog.WellFormed] at hOK
        unfold Prog.WellFormed
        rcases hOK with ⟨hl, hr⟩
        intro op hop
        exact hr op hop

      simp [run?] at hstep
      cases hσ1 : applyOp? σ op with
      | none =>
          simp [hσ1] at hstep
      | some σ1 =>
          have hstep_tail : run? (k := k) ops σ1 = some σ2 := by
            simpa [hσ1] using hstep

          -- compile head
          cases hC1 : compile1 (k := k) op curLenNow with
          | mk opsP1 curLen1 =>
              -- simulate the head using compile1_simulates (which should now take ValidFor)
              have hsim_head :
                eval_prim_ops (k := k) opsP1 (stateToSt (k := k) σ { ctx0 with curLen := curLenNow })
                  =
                stateToSt (k := k) σ1 { ctx0 with curLen := curLen1 } := by
                simpa [hC1] using
                  (compile1_simulates (k := k)
                    (op := op) (σ := σ)
                    (ctx := { ctx0 with curLen := curLenNow })
                    (hV := hV)
                    (σ2 := σ1) (hstep := hσ1) (hOK := hOK_head))

              -- get ValidFor for the tail state/context via the step-preservation hypothesis
              have hV1 :
                ValidFor (k := k) σ1 { ctx0 with curLen := curLen1 } := by
                -- unfold the step rule at exactly this situation
                have := hStepValid σ σ1 op curLenNow hσ1 hOK_head hV
                -- rewrite `curLen1` to match compile1's result
                simpa [hC1] using this

              -- apply IH to the tail
              have hsim_tail :
                let (opsP, curLen') := compileProg (k := k) ops curLen1
                eval_prim_ops (k := k) opsP (stateToSt (k := k) σ1 { ctx0 with curLen := curLen1 })
                  =
                stateToSt (k := k) σ2 { ctx0 with curLen := curLen' } := by
                simpa using
                  (ih (σ := σ1) (curLenNow := curLen1) (σ2 := σ2)
                    (hstep := hstep_tail) (hOK := hOK_tail) (hV := hV1))

              -- stitch head ++ tail
              simp [compileProg, hC1]
              simpa [eval_prim_ops_append, hsim_head] using hsim_tail

theorem compileProg_simulates
  {k : ℕ}
  (ops : Prog k)
  (σ : State k)
  (ctx : StCtx k)
  (σ2 : State k)
  (hstep : run? (k := k) ops σ = some σ2)
  (hOK : Prog.WellFormed ops)
  (hV : ValidFor (k := k) σ ctx)
  (hStepValid : ValidForStep (k := k) ctx) :
  let (opsP, curLen') := compileProg (k := k) ops ctx.curLen
  eval_prim_ops (k := k) opsP (stateToSt (k := k) σ ctx)
    =
  stateToSt (k := k) σ2 { ctx with curLen := curLen' } := by
  simpa using
    (compileProg_simulates_go (k := k)
      (ops := ops) (σ := σ) (ctx0 := ctx) (curLenNow := ctx.curLen)
      (σ2 := σ2) (hstep := hstep) (hOK := hOK) (hV := hV) (hStepValid := hStepValid))
