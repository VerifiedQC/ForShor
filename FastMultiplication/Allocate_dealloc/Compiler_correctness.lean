import FastMultiplication.Allocate_dealloc.Basic

/-- If out of range, default delta width = 0 (this matches the “delta-from-initial” model). -/
def getDelta (curLen : List Nat) (idx : Nat) : Nat :=
  curLen.getD idx 0

/-- Evaluate a symbolic register to an integer using a valuation for the variables. -/
def evalRegister {k : ℕ} (r : Register k) (ρ : Fin k → ℤ) : ℤ :=
  ∑ j : Fin k, (r j) * (ρ j)

/-- Convert an integer to a Nat in `[0, 2^w)` (two's-complement storage uses mod 2^w). -/
def intToNatMod (w : Nat) (z : ℤ) : Nat :=
  let mNat : Nat := (2 : Nat) ^ w
  let m    : ℤ   := (Int.ofNat mNat)
  Int.toNat (Int.emod z m)


def stateToSt {k : ℕ}
    (σ : State k)
    (ρ : Fin k → ℤ)
    (baseW : Fin k → Nat)
    (curLen : List Nat) : St k :=
  fun i =>
    let w : Nat := baseW i + getDelta curLen i.val
    let z : ℤ := evalRegister (σ i) ρ
    ⟨w, BitVec.ofNat w (intToNatMod w z)⟩



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
| ⟨2, _⟩ => -8

/-- Delta widths all zero (your “differences only” model). -/
def cur0 : List Nat := List.replicate 3 0

--------------------------------------------------------------------------------
-- Demo A: start_state -> concrete bitvectors match your earlier demo
--------------------------------------------------------------------------------

/-- All regs have base width 5. -/
def baseW5 : Fin 3 → Nat := fun _ => 5

def σ_start : State 3 := State.start_state
def st_start : St 3 := stateToSt σ_start ρ3 baseW5 cur0

-- Expect:
-- 0: 01111  (signed=15)
-- 1: 00110  (signed=6)
-- 2: 11000  (signed=-8)   because (-8) mod 32 = 24 = 11000
#eval printState st_start


--------------------------------------------------------------------------------
-- Demo B: change symbolic state: r0 := r0 + r1  (so value becomes 15+6=21)
--------------------------------------------------------------------------------

/-- Make register 0 equal to x0 + x1 in the symbolic world. -/
def σ_plus : State 3 :=
  State.addScaledReg σ_start r0 r1 false 0   -- dst=r0, src=r1, negSrc=false, shift=0

/-- Use width 6 so +21 stays positive in two's-complement. -/
def baseW6 : Fin 3 → Nat := fun _ => 6

def st_plus : St 3 := stateToSt σ_plus ρ3 baseW6 cur0

-- Expect:
-- reg0 = 21 => 010101 (signed=21) in 6 bits
-- reg1 = 6  => 000110
-- reg2 = -8 => 111000 (because (-8) mod 64 = 56)
#eval printState st_plus




--------------------------------------------------------------------------------
-- THE CRUCUIAL THEOREM- COMPILATION WORKS!!
--------------------------------------------------------------------------------

open Operations



lemma allocMSB_preserves_value
  {k : ℕ} (st : St k) (i : Fin k) (n : Nat) :
  BitVec.toInt ((AllocMSB st i n i).2) = BitVec.toInt ((st i).2) := by
  unfold AllocMSB
  rw [if_pos rfl]
  simp [BitVec.toInt_signExtend]



def lowBitsZero {w : Nat} (bv : BitVec w) (n : Nat) : Prop :=
  ∀ t : Nat, t < n → Nat.testBit bv.toNat t = false




lemma freeLSB_undo_shift
  {k : ℕ} (st : St k) (i : Fin k) (n : Nat)
  (hn : n ≤ (st i).fst)
  (h0 : lowBitsZero (st i).2 n) :
  BitVec.toInt ((FreeLSB st i n i).2)
    = BitVec.toInt ((st i).2) / (2 : ℤ) ^ n := by
  unfold FreeLSB
  simp[lowBitsZero] at *
  rw[if_pos rfl]
  set w  : Nat := (st i).fst
  set bv : BitVec w := (st i).snd
  set w' : Nat := w - n

  change (BitVec.setWidth w' (BitVec.sshiftRight bv n)).toInt
        = bv.toInt / (2 ^ n : Int)
  have hshift :
    (BitVec.sshiftRight bv n).toInt = bv.toInt / (2 ^ n : Int) := by
    -- replace the lemma name below with whatever #find shows you
    have h:= BitVec.toInt_sshiftRight (x := bv) (n:=n)
    simp[h]
    have :=Int.shiftRight_eq_div_pow bv.toInt n
    simp[this]
  have hwidth :
    (BitVec.setWidth w' (BitVec.sshiftRight bv n)).toInt
      = (BitVec.sshiftRight bv n).toInt := by
      by_cases hn0 : n = 0
      · subst hn0
        simp [w', bv] -- n=0 makes w' = w, simplifies the if-branch to rfl
      ·
        have h_lt : w' < w := by
          simp [w']
          have:= Nat.sub_lt_of_pos_le (Nat.pos_of_ne_zero hn0) hn
          aesop
        have h_if : ¬ (w ≤ w') := by omega
        unfold BitVec.setWidth
        let v_shifted := bv.sshiftRight n
        sorry



  calc
    (BitVec.setWidth w' (BitVec.sshiftRight bv n)).toInt
        = (BitVec.sshiftRight bv n).toInt := hwidth
    _   = bv.toInt / (2 ^ n : Int) := hshift



def msbFreedAreSignExt {w : Nat} (bv : BitVec w) (n : Nat) : Prop :=
  -- “the top n bits equal the sign bit of the kept part”
  True  -- fill in

#check BitVec.sshiftRight

lemma freeMSB_preserves_value
  {k : ℕ} (st : St k) (i : Fin k) (n : Nat)
  (hs : msbFreedAreSignExt (st i).2 n) :
  BitVec.toInt ((FreeMSB st i n i).2)
    = BitVec.toInt ((st i).2) := by
  unfold FreeMSB
  rw[if_pos rfl]

  sorry

lemma adder_correct_equiv
  {k : ℕ} (st : St k) (dst src : Fin k) :
  ((Adder st dst src dst).2) ≍ BitVec.add (st dst).2 (BitVec.truncate (st dst).1 (st src).2) := by
  -- Usually rfl after unfolding Adder; your Adder is literally that BitVec.add.
  unfold Adder
  sorry



lemma eval_prim_ops_append {k : ℕ}
  (xs ys : List (prim_ops k)) (st : St k) :
  eval_prim_ops (k := k) (xs ++ ys) st
    = eval_prim_ops (k := k) ys (eval_prim_ops (k := k) xs st) := by
  induction xs generalizing st with
  | nil =>
      simp [eval_prim_ops]
  | cons x xs ih =>
      -- eval (x :: xs ++ ys) st = eval (xs ++ ys) (step x st)
      simp [eval_prim_ops, ih, List.cons_append]

lemma eval_prim_ops_singleton {k : ℕ} (p : prim_ops k) (st : St k) :
  eval_prim_ops (k := k) [p] st = eval_prim_op_single (k := k) p st := by
  simp [eval_prim_ops]


-- LSB alloc simulates symbolic shiftL, and updates delta-len
lemma bridge_allocLSB
  {k : ℕ} (σ : State k) (ρ : Fin k → ℤ) (baseW : Fin k → Nat) (curLen : List Nat)
  (i : Fin k) (n : Nat) :
  eval_prim_op_single (k := k) (prim_ops.Alloc i true n) (stateToSt σ ρ baseW curLen)
    =
  stateToSt (State.shiftLReg σ i n) ρ baseW (incLen curLen i n) := by
  sorry

-- MSB alloc is sign-extend: symbolic value unchanged, only length delta updates
lemma bridge_allocMSB
  {k : ℕ} (σ : State k) (ρ : Fin k → ℤ) (baseW : Fin k → Nat) (curLen : List Nat)
  (i : Fin k) (n : Nat) :
  eval_prim_op_single (k := k) (prim_ops.Alloc i false n) (stateToSt σ ρ baseW curLen)
    =
  stateToSt σ ρ baseW (incLen curLen i n) := by
  sorry

-- Negate
lemma bridge_negate
  {k : ℕ} (σ : State k) (ρ : Fin k → ℤ) (baseW : Fin k → Nat) (curLen : List Nat)
  (i : Fin k) :
  eval_prim_op_single (k := k) (prim_ops.negate i) (stateToSt σ ρ baseW curLen)
    =
  stateToSt (State.negateReg σ i) ρ baseW curLen := by
  sorry

-- Add (dst := dst + src)
lemma bridge_add
  {k : ℕ} (σ : State k) (ρ : Fin k → ℤ) (baseW : Fin k → Nat) (curLen : List Nat)
  (dst src : Fin k) :
  eval_prim_op_single (k := k) (prim_ops.Add dst src) (stateToSt σ ρ baseW curLen)
    =
  stateToSt (State.addScaledReg σ dst src false 0) ρ baseW curLen := by
  sorry

-- LSB free simulates shiftR? (requires your “safe free” invariant; include it in hypotheses as needed)
lemma bridge_freeLSB
  {k : ℕ} (σ σ' : State k) (ρ : Fin k → ℤ) (baseW : Fin k → Nat)
  (curLen : List Nat) (i : Fin k) (n : Nat)
  (h : State.shiftRReg? σ i n = some σ') :
  eval_prim_op_single (k := k) (prim_ops.Free i true n) (stateToSt σ ρ baseW curLen)
    =
  stateToSt σ' ρ baseW (decLen curLen i n) := by
  sorry

-- MSB free: symbolic value unchanged, only length delta updates
lemma bridge_freeMSB
  {k : ℕ} (σ : State k) (ρ : Fin k → ℤ) (baseW : Fin k → Nat) (curLen : List Nat)
  (i : Fin k) (n : Nat) :
  eval_prim_op_single (k := k) (prim_ops.Free i false n) (stateToSt σ ρ baseW curLen)
    =
  stateToSt σ ρ baseW (decLen curLen i n) := by
  sorry

@[simp] lemma incLen_zero {k : ℕ} (curLen : List Nat) (i : Fin k) :
  incLen curLen i 0 = curLen := by
  simp [incLen, setLen, getLen, Nat.add_zero]
  sorry

@[simp] lemma decLen_zero {k : ℕ} (curLen : List Nat) (i : Fin k) :
  decLen curLen i 0 = curLen := by
  simp [decLen, setLen, getLen, Nat.sub_zero]
  sorry
@[simp] lemma stateToSt_fst {k : ℕ}
  (σ : State k) (ρ : Fin k → ℤ) (baseW : Fin k → Nat) (curLen : List Nat) (j : Fin k) :
  (stateToSt σ ρ baseW curLen j).fst = baseW j + getDelta curLen j.val := by
  simp [stateToSt, getDelta]

lemma negate_add_negate_eq_addScaled_true0
  {k : ℕ} (σ : State k) (dst src : Fin k) (hds:dst≠src):
  State.negateReg (State.addScaledReg (State.negateReg σ src) dst src false 0) src
    =
  State.addScaledReg σ dst src true 0 := by
  -- equality of states = pointwise equality of registers
  ext i j
  by_cases hid : i = dst
  · rw[hid]
    simp [State.negateReg, State.addScaledReg, State.setReg,
          Register.addScaled, Register.negate]
    simp_all only [↓reduceIte]
  · by_cases his : i = src
    · subst his
      simp [State.negateReg, State.addScaledReg, State.setReg, hid]
    ·
      simp [State.negateReg, State.addScaledReg, State.setReg, hid, his]


theorem compile1_simulates
  {k : ℕ}
  (op : valid_ops k)
  (σ : State k)
  (ρ : Fin k → ℤ)
  (baseW : Fin k → Nat)
  (curLen : List Nat)
  (σ2 : State k)
  (hstep : applyOp? σ op = some σ2)
  (hOK : Prog.OpOK op) :
  let (opsP, curLen') := compile1 (k := k) op curLen
  eval_prim_ops (k := k) opsP (stateToSt σ ρ baseW curLen)
    =
  stateToSt σ2 ρ baseW curLen' := by
  cases op with
  | shiftL i n =>
      simp [compile1, compile_op_to_prim_single, applyOp?] at hstep ⊢
      cases hstep
      simpa [eval_prim_ops_singleton] using
        (bridge_allocLSB (k := k) σ ρ baseW curLen i n)

  | shiftR i n =>
      simp [compile1, compile_op_to_prim_single, applyOp?] at hstep ⊢
      simpa [eval_prim_ops_singleton] using
        (bridge_freeLSB (k := k) (σ := σ) (σ' := σ2) ρ baseW curLen i n hstep)

  | negate i =>
      simp [compile1, compile_op_to_prim_single, applyOp?] at hstep ⊢
      cases hstep
      simpa [eval_prim_ops_singleton] using
        (bridge_negate (k := k) σ ρ baseW curLen i)

  | phaseProduct i =>
      simp [compile1, compile_op_to_prim_single, applyOp?, eval_prim_ops, eval_prim_op_single] at *
      simp[hstep]

  | addScaled dst src negSrc sh =>
      by_cases hds : dst = src
      · -- compiler emits [] and applyOp? should match (usually identity or ruled out by OpOK)
        simp [compile1, compile_op_to_prim_single, hds, applyOp?] at hstep ⊢
        cases hstep
        simp [eval_prim_ops]   -- eval [] = identity
        simp[Prog.OpOK] at hOK
        contradiction
      ·
        simp [compile1, compile_op_to_prim_single, hds, applyOp?] at hstep ⊢
        split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15<;>simp
        {
          subst h1 hstep h2
          simp_all
          ext j
          by_cases hjd : j = dst
          · subst hjd
            simp [State.addScaledReg,Register.addScaled]
            have hL :
                (eval_prim_ops (k := k)
                    [prim_ops.negate src, prim_ops.Add j src, prim_ops.negate src]
                    (stateToSt σ ρ baseW curLen) j).fst
                  =
                (stateToSt σ ρ baseW curLen j).fst := by
              simp [eval_prim_ops, eval_prim_op_single, Negation, Adder, hds]

            have hR :
                (stateToSt (σ.setReg j (fun t => σ j t + -σ src t)) ρ baseW
                    (decLen (decLen (incLen (incLen (incLen curLen src 0) j 0) src 0) src 0) src 0) j).fst
                  =
                (stateToSt σ ρ baseW curLen j).fst := by
              simp [stateToSt, getDelta]
            aesop

          ·
            have hds2:¬ src =dst :=by sorry
            by_cases hjs : j = src
            · subst hjs
              -- src is negated twice; addScaledReg doesn't touch src
              simp [eval_prim_ops, eval_prim_op_single, Negation, Adder, hjd, Fin.ext_iff]

            · -- all other registers untouched throughout
              simp [eval_prim_ops, eval_prim_op_single, Negation, Adder, hjd, hjs]
            -- Step A: Prove equality of the whole states (stronger than needed).
          have hSt :
            eval_prim_ops (k := k)
                [prim_ops.negate src, prim_ops.Add dst src, prim_ops.negate src]
                (stateToSt σ ρ baseW curLen)
              =
            stateToSt (State.addScaledReg σ dst src true 0) ρ baseW curLen := by
            -- unfold the 3-step evaluator
            simp [eval_prim_ops]
            -- first negate
            simp [bridge_negate]
            -- unfold remaining 2 steps
            -- add
            rw [bridge_add (k := k)
                  (σ := State.negateReg σ src) (ρ := ρ) (baseW := baseW) (curLen := curLen)
                  (dst := dst) (src := src)]
            rw [bridge_negate (k := k)
                  (σ := State.addScaledReg (State.negateReg σ src) dst src false 0)
                  (ρ := ρ) (baseW := baseW) (curLen := curLen) (i := src)]
            simp [negate_add_negate_eq_addScaled_true0 σ dst src hds]

          rw[hSt]
        }
        {
          subst h1 hstep h2
          simp_all only [incLen_zero, decLen_zero]
          sorry
        }
        all_goals sorry
