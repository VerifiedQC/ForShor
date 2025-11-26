import FastMultiplication.QuantumCircuit.circ_model_list

namespace Qubit_level

--------------------------------------------------------------------------------
-- State and state-level operations
--------------------------------------------------------------------------------

abbrev State (k : ℕ) := Fin k → Register

/-- Nicely render a single register as "bits (value)". -/
def prettyRegister (r : Register) : String :=
  let bits := regToString r
  let n    := regToNat r
  s!"{bits} ({n})"

/-- Lines of a pretty-printed state: ["R0 = ...", "R1 = ...", ...]. -/
def prettyStateLines {k : ℕ} (σ : State k) : List String :=
  (List.finRange k).map fun i =>
    s!"R{i.val} = {regToString (σ i)} ({regToNat (σ i)})"

/-- IO printer that actually prints each register on its own line. -/
def printState {k : ℕ} (σ : State k) : IO Unit := do
  for line in prettyStateLines σ do
    IO.println line

-- Example state:
def exampleState : State 2 :=
  fun
  | ⟨0, _⟩ => [false, true, false]  -- 010₂ = 2
  | ⟨1, _⟩ => [true,  true, false]  -- 011₂ = 3

-- State-level operations
def State.add_with_carry {k : ℕ} (s : State k) (dst src : Fin k) (_hdst:dst≠src): State k :=
  let rdst    := s dst
  let rsrc    := s src
  let new_dst := add_reg rdst rsrc
  fun j => if j = dst then new_dst else s j

def State.add_no_carry {k : ℕ} (s : State k) (dst src : Fin k) (_hdst:dst≠src): State k :=
  let rdst    := s dst
  let rsrc    := s src
  let new_dst := add_reg_no_carry rdst rsrc
  fun j => if j = dst then new_dst else s j

def State.shiftL {k : ℕ} (s : State k) (dst : Fin k) : State k :=
  let rdst    := s dst
  let new_dst := left_shift rdst
  fun j => if j = dst then new_dst else s j

def State.shiftR {k : ℕ} (s : State k) (dst : Fin k) : State k :=
  let rdst    := s dst
  let new_dst := right_shift rdst
  fun j => if j = dst then new_dst else s j

def State.negate {k : ℕ} (s : State k) (w : ℕ) (dst : Fin k) : State k :=
  let rdst    := s dst
  let new_dst := negateFixed w rdst
  fun j => if j = dst then new_dst else s j

def truncateTo (w : ℕ) (r : Register) : Register :=  -- LSB-first
  (r.take w)   -- keep only the low w bits

def sub_reg_fixed (w : ℕ) (rDst rSrc : Register) : Register :=
  let rDst_w  := truncateTo w rDst
  let negSrc  := negateFixed w rSrc        -- guaranteed length w
  let diff    := add_reg_no_carry rDst_w negSrc
  truncateTo w diff

def State.add_inverse {k : ℕ} (s : State k) (dst src : Fin k) (w : ℕ) : State k :=
  let rdst    := s dst
  let rsrc    := s src
  let new_dst := sub_reg_fixed w rdst rsrc
  fun j => if j = dst then new_dst else s j

/-- `add_reg` computes the full sum `x + y` as an integer. -/
lemma add_reg_spec (r1 r2 : Register) :
  regToNat (add_reg r1 r2) = regToNat r1 + regToNat r2 := by
  -- nontrivial bit-level proof
  sorry

/-- `add_reg_no_carry` is addition modulo 2^w when both are ≤ w bits. -/
lemma add_reg_no_carry_mod (w : ℕ)
    (r1 r2 : Register)
    (h1 : r1.length ≤ w)
    (h2 : r2.length ≤ w) :
  regToNat (truncateTo w (add_reg_no_carry r1 r2))
    = (regToNat (truncateTo w r1)
       + regToNat (truncateTo w r2)) % (Nat.pow 2 w) := by
  -- another bit-level lemma
  sorry

/-- `negateFixed w` is two’s complement: -x mod 2^w. -/
lemma negateFixed_spec (w : ℕ) (r : Register) :
  regToNat (negateFixed w r)
    = (Nat.pow 2 w - regToNat (truncateTo w r)) % (Nat.pow 2 w) := by
  sorry

/--
If two w-bit registers represent the same integer < 2^w, then the lists are equal.
(This is true for your LSB-first `regToNat` / `Nat.digits` encoding.)
-/
lemma reg_eq_of_nat_eq_mod_pow
    {w : ℕ} {r₁ r₂ : Register}
    (h₁ : r₁.length = w)
    (h₂ : r₂.length = w)
    (hval : regToNat r₁ = regToNat r₂) :
  r₁ = r₂ := by
  -- here you use the fact that binary representation of numbers < 2^w is unique
  sorry

-- I’m assuming `truncateTo` and `sub_reg_fixed` are defined as above.

/-- Arithmetic spec of `sub_reg_fixed`: (dst - src) mod 2^w. -/
lemma sub_reg_fixed_spec (w : ℕ) (rDst rSrc : Register)
  (hDst : (truncateTo w rDst).length ≤ w)
  (hSrc : (truncateTo w rSrc).length ≤ w) :
  regToNat (truncateTo w (sub_reg_fixed w rDst rSrc))
    = (regToNat (truncateTo w rDst)
       + (Nat.pow 2 w - regToNat (truncateTo w rSrc))) % (Nat.pow 2 w) := by
  -- unfold and use the two spec lemmas
  unfold sub_reg_fixed
  simp only [truncateTo]  -- if you have a more complex def, adapt
  set rDst'  := truncateTo w rDst with hDst'
  set negSrc := negateFixed w rSrc with hNeg
  have hNegVal := negateFixed_spec w rSrc
  -- apply add_reg_no_carry_mod to (rDst', negSrc)
  have h1 : rDst'.length ≤ w := by
    -- from `hDst` and `hDst'`, or from properties of `truncateTo`
    sorry
  have h2 : negSrc.length ≤ w := by
    -- from the def of `negateFixed`
    sorry
  have hadd :=
    add_reg_no_carry_mod w rDst' negSrc h1 h2
  -- combine `hadd` with `hNegVal` to get the overall expression
  -- and simplify `(x + (2^w - y)) % 2^w` to `(x - y) % 2^w` if you like.
  sorry


lemma sub_reg_of_add
  (k : ℕ)
  (s   : State k)
  (dst src : Fin k)
  (hds : dst ≠ src) :
  sub_reg_fixed (List.length (s dst))
    (add_reg (s dst) (s src)) (s src)
  = s dst := by
  -- Let w be the width of dst
  let w : ℕ := (s dst).length
  have hw : (s dst).length = w := rfl
  have h_sub_val :
      regToNat (truncateTo w
        (sub_reg_fixed w (add_reg (s dst) (s src)) (s src)))
      = regToNat (truncateTo w (s dst)) := by
    have h_add_val :
        regToNat (add_reg (s dst) (s src))
        = regToNat (s dst) + regToNat (s src) := add_reg_spec _ _
    -- step 2: apply sub_reg_fixed_spec with rDst := add_reg (s dst) (s src)
    have hDst_len : (truncateTo w (add_reg (s dst) (s src))).length ≤ w := by
      simp[truncateTo]

    have hSrc_len : (truncateTo w (s src)).length ≤ w := by
      simp[truncateTo]

    have h_spec :=
      sub_reg_fixed_spec w (add_reg (s dst) (s src)) (s src)
        hDst_len hSrc_len
    -- have h_dst_bound : regToNat (truncateTo w (s dst)) < Nat.pow 2 w := by
    --   sorry
    rw[h_spec]
    simp_all only [ne_eq, Nat.pow_eq, w]
    sorry

  have h_len_left :
      (truncateTo w
        (sub_reg_fixed w (add_reg (s dst) (s src)) (s src))).length
      = w := by
    sorry

  have h_len_right :
      (truncateTo w (s dst)).length = w := by
    simp[truncateTo, hw]

  -- Now we can use the "canonical encoding" lemma.
  have h_eq_trunc :
      truncateTo w
        (sub_reg_fixed w (add_reg (s dst) (s src)) (s src))
      = truncateTo w (s dst) := by
    apply reg_eq_of_nat_eq_mod_pow h_len_left h_len_right
    exact h_sub_val

  have h_trunc_dst :
      truncateTo w (s dst) = s dst := by
    sorry

  have h_trunc_sub :
      truncateTo w
        (sub_reg_fixed w (add_reg (s dst) (s src)) (s src))
      = sub_reg_fixed w (add_reg (s dst) (s src)) (s src) := by
    sorry

  -- Rewrite both sides using these identities:
  calc
    sub_reg_fixed w (add_reg (s dst) (s src)) (s src)
        = truncateTo w (sub_reg_fixed w (add_reg (s dst) (s src)) (s src)) := by
            symm; exact h_trunc_sub
    _   = truncateTo w (s dst) := by simpa [w] using h_eq_trunc
    _   = s dst := h_trunc_dst



--------------------------------------------------------------------------------
-- Inductive description of valid operations + sequencing
--------------------------------------------------------------------------------

/--
`valid_operations k` is the syntax of allowed state-level operations
on a `State k`:

* `addWithCarry dst src`     : `dst ← dst + src` with carry bit
* `addNoCarry dst src`       : `dst ← dst + src` dropping final carry
* `shiftL dst`               : logical left shift of `dst`
* `shiftR dst`               : logical right shift of `dst`
* `negate w dst`             : two's-complement negate `dst` at width `w`
* `phaseProduct`             : no-op on the state
-/
inductive valid_operations (k : ℕ) : Type where
  | add (dst src : Fin k) (hdst:dst≠src) (c:Bool): valid_operations k
  | shiftL      (dst : Fin k)      : valid_operations k
  | shiftR      (dst : Fin k)      : valid_operations k
  | negate      (w : ℕ) (dst : Fin k) : valid_operations k
  | phaseProduct : valid_operations k
deriving Repr

namespace valid_operations

/-- Semantics of a single `valid_operations` on a state. -/
def apply {k : ℕ} (op : valid_operations k) (σ : State k) : State k :=
  match op with
  | valid_operations.add dst src hdst c=>
      if c then (State.add_with_carry σ dst src hdst) else (State.add_no_carry σ dst src hdst)
  | valid_operations.shiftL dst           =>
      State.shiftL σ dst
  | valid_operations.shiftR dst           =>
      State.shiftR σ dst
  | valid_operations.negate w dst         =>
      State.negate σ w dst
  | valid_operations.phaseProduct         =>
      σ


/--
Semantics of a **sequence** of operations.

`applySeq σ ops` applies each operation in `ops` from left to right.
-/
def applySeq {k : ℕ} (σ : State k) (ops : List (valid_operations k)) : State k :=
  ops.foldl (fun σ op => apply op σ) σ

end valid_operations


--------------------------------------------------------------------------------
-- Small example: sequence of operations
--------------------------------------------------------------------------------

open valid_operations

/--
Example program on `exampleState`:

1. addWithCarry R0 R1
2. shiftL R0
3. phaseProduct (no-op)
4. negate width 4 on R0
-/
def exampleProg : List (valid_operations 2) :=
  [ valid_operations.add 0 1 (by decide) True,
    valid_operations.shiftL 0,
    valid_operations.phaseProduct,
    valid_operations.negate 4 0 ]

def exampleAfterProg : State 2 :=
  valid_operations.applySeq exampleState exampleProg

#eval printState exampleState
#eval printState exampleAfterProg




inductive Program (k : ℕ) : Type where
  | skip : Program k
  | op   : valid_operations k → Program k
  | seq  : Program k → Program k → Program k
deriving Repr

namespace Program

open valid_operations

/-- Big-step semantics for programs. -/
def eval {k : ℕ} (p : Program k) (σ : State k) : State k :=
  match p with
  | Program.skip      => σ
  | Program.op o      => valid_operations.apply o σ
  | Program.seq p q   => eval q (eval p σ)

/-- Notation for sequencing: `p ;; q`. -/
infixr:60 " ;; " => Program.seq

/-- Build a Program from a list of operations (run left-to-right). -/
def fromOps {k : ℕ} (ops : List (valid_operations k)) : Program k :=
  ops.foldr (fun o acc => Program.seq (Program.op o) acc) Program.skip

end Program

open valid_operations Program

/--
Example "program":

1. R0 ← R0 + R1  (with carry)
2. shiftL R0
3. phaseProduct (no-op)
4. negate width 4 on R0
-/


def progExample : Program 2 :=
  Program.op (add 0 1 (by simp) True) ;;
  Program.op (shiftL 0) ;;
  Program.op phaseProduct;;
  Program.op (negate 5 1);;
  Program.op (add 0 1 (by simp) False) ;;
  Program.op (negate 5 1)

/-- Run `progExample` on `exampleState`. -/
def exampleAfterProg2 : State 2 :=
  Program.eval progExample exampleState

#eval printState exampleState
#eval printState exampleAfterProg2






theorem add_with_carry_add_inverse_id
  {k : ℕ} (s : State k) (dst src : Fin k) (hds:dst≠src):
  State.add_inverse (State.add_with_carry s dst src hds) dst src ((s dst).length) = s := by
  unfold State.add_with_carry State.add_inverse;simp
  funext j
  split_ifs with hj hds2
  · subst hj hds2
    contradiction
  · rw[sub_reg_of_add k s dst src]
    rw[hj]
    intro h
    subst h;contradiction
  · rfl
end Qubit_level
