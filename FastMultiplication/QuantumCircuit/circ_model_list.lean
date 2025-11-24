import FastMultiplication.one_reg_synth_proof_2

namespace Qubit_level

abbrev Register := List Bool

/-- Example registers (LSB-first):
    r1 = [false, true, false]  = 010₂ = 2
    r2 = [true,  true,  false] = 011₂ = 3
-/
def r1 : Register := [false, true, false]
def r2 : Register := [true,  true, false]

/-- Full adder on single bits.
    Convention: (a + b + cin) ↦ (cout, sum). -/
def fullAdder (a b cin : Bool) : Bool × Bool :=
  match a, b, cin with
  | false, false, false => (false, false)
  | false, false, true  => (false,  true)
  | false, true,  false => (false,  true)
  | false, true,  true  => (true,  false)
  | true,  false, false => (false,  true)
  | true,  false, true  => (true,  false)
  | true,  true,  false => (true,  false)
  | true,  true,  true  => (true,  true)

/-- Pad a register with `false` (0 bits) on the high side to length `n`. -/
def padTo (n : Nat) (r : Register) : Register :=
  r ++ List.replicate (n - r.length) false

/-- Recursive helper: add two registers with an incoming carry.
    Assumes both lists are LSB-first. Returns (sumBits, finalCarry). -/
def addCore : Register → Register → Bool → Register × Bool
  | [], [], cin =>
      ([], cin)
  | a :: as, [], cin =>
      let (cout, s)      := fullAdder a false cin
      let (rest, carry') := addCore as [] cout
      (s :: rest, carry')
  | [], b :: bs, cin =>
      let (cout, s)      := fullAdder false b cin
      let (rest, carry') := addCore [] bs cout
      (s :: rest, carry')
  | a :: as, b :: bs, cin =>
      let (cout, s)      := fullAdder a b cin
      let (rest, carry') := addCore as bs cout
      (s :: rest, carry')

/-- Add two registers (LSB-first lists of bits) with *overflow wire*.
    Output length is `max (length r1) (length r2) + 1`. -/
def add_reg (r1 r2 : Register) : Register :=
  let l1  := r1.length
  let l2  := r2.length
  let l   := Nat.max l1 l2
  let r1' := padTo l r1
  let r2' := padTo l r2
  let (sumBits, carry) := addCore r1' r2' false
  sumBits ++ [carry]

/-- Add two registers but **do not allocate a new qubit for the final carry**.
    Carries still propagate between bits; the final overflow carry is dropped.
    Output length is exactly `max (length r1) (length r2)`.
-/
def add_reg_no_carry (r1 r2 : Register) : Register :=
  let l1  := r1.length
  let l2  := r2.length
  let l   := Nat.max l1 l2
  let r1' := padTo l r1
  let r2' := padTo l r2
  let (sumBits, _carry) := addCore r1' r2' false
  sumBits

/-- Convert a single bit to the corresponding character. -/
def bitToChar (b : Bool) : Char :=
  if b then '1' else '0'

/-- Convert a register to a string with the **most significant bit on the left**. -/
def regToString (r : Register) : String :=
  String.mk (r.reverse.map bitToChar)

/-- Decode an LSB-first register to a natural number. -/
def regToNat : Register → Nat
  | []      => 0
  | b :: bs =>
      let tailVal := regToNat bs
      (if b then 1 else 0) + 2 * tailVal

/-- Encode a natural number as an LSB-first register. -/
def natToReg (n : Nat) : Register :=
  (Nat.digits 2 n).map (fun d => d = 1)

/-
Examples:
r1 = 010₂ = 2
r2 = 011₂ = 3

add_reg r1 r2          -> 5 with overflow wire (length 4)
add_reg_no_carry r1 r2 -> 5 mod 2^3 = 5 (length 3)
-/

#eval regToString (add_reg r1 r2)         -- "0101"
#eval regToString (add_reg_no_carry r1 r2) -- "101"



/-- Bitwise NOT of a register (LSB-first). -/
def bitNot (r : Register) : Register :=
  r.map (fun b => not b)

/-- A w-bit register equal to 1 (LSB-first). -/
def oneReg (w : Nat) : Register :=
  padTo w (natToReg 1)

/-- Two's complement negation at fixed width `w`. -/
def negateFixed (w : Nat) (r : Register) : Register :=
  let r'    := padTo w r
  let notR  := bitNot r'
  add_reg_no_carry notR (oneReg w)

#eval regToNat (r1)         -- "010"
#eval regToNat (r2)

#eval regToString (negateFixed 3 r1)         -- "010"

#eval regToString (add_reg_no_carry r2 (negateFixed 3 r1))


-- Logical right shift by 1 on an LSB-first register.

def right_shift (r : Register) : Register :=
  match r with
  | []      => []
  | _ :: bs => bs ++ [false]

/-- Logical left shift by 1 on an LSB-first register.

Given `r = [b₀, b₁, ..., b_{n-1}]` (b₀ is LSB), we produce

  [false, b₀, b₁, ..., b_{n-2}]

This corresponds to multiplication by 2 modulo 2^n (dropping the MSB,
inserting 0 at LSB).
-/
def left_shift (r : Register) : Register :=
  false :: r

#eval regToString (left_shift r1)

end Qubit_level
