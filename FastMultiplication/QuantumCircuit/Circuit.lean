import FastMultiplication.one_reg_synth_proof_2
open Std

/-!
##############################
# Classical Bitstate + Convention
##############################
-/

/-- Classical bit state of `N` qubits (basis state). -/
abbrev BitState (N : ℕ) := Fin N → Bool

/-
GLOBAL CONVENTION:

For a bit-vector `v : Fin n → Bool`:

  * `v ⟨0, _⟩` is the **most significant bit** (MSB),
  * `v ⟨n-1, _⟩` is the **least significant bit** (LSB).

So for `n = 3`, the bits

  v 0 = true, v 1 = true, v 2 = false

encode the integer 6 (binary 110₂), and the string "110" means 6.
-/

/-!
##############################
# Bit ↔ String Utilities
##############################
-/

/-- Convert a single `Bool` to a `Char` `'0'` or `'1'`. -/
def bitChar (b : Bool) : Char :=
  if b then '1' else '0'

/--
Convert a bit-vector `Fin n → Bool` to a `String` like `"110"`.

We print bits in **index order**:

  index 0, then 1, ..., then n-1,

so the printed string is **MSB-first** under our global convention.
-/
def bitsString {n : ℕ} (v : Fin n → Bool) : String :=
  let rec go : ∀ m, (Fin m → Bool) → String
  | 0,      _    => ""
  | m+1, bits =>
      -- bit at index 0 (MSB for this subvector)
      let b0 : Bool := bits ⟨0, Nat.succ_pos _⟩
      -- higher indices 1..m as Fin m
      let bits' : Fin m → Bool := fun i => bits i.succ
      let tail := go m bits'
      (bitChar b0).toString ++ tail
  go n v

/--
Show a whole `BitState` as a bitstring `"0101"`,

printing the global indices `0, 1, ..., N-1` in order.

Under our convention, this is **MSB-first** w.r.t the whole state.
-/
def showState {N : ℕ} (σ : BitState N) : String :=
  bitsString σ

/-!
##############################
# Core Bit-level Arithmetic
##############################
-/

/-- One-bit full adder: given `a`, `b`, and carry-in `cin`,
    returns `(sum, carry-out)`. -/
def fullAdder (a b cin : Bool) : Bool × Bool :=
  let sum  := Bool.xor (Bool.xor a b) cin
  -- carry = (a ∧ b) ∨ (cin ∧ (a ∨ b))
  let cout := (a && b) || (cin && (a || b))
  (sum, cout)

/--
Ripple-carry adder on `n` bits represented as `Fin n → Bool`.

**Bit indexing convention inside `Fin n`:**

* `i = 0` is the **most significant bit** (MSB),
* `i = n-1` (the last index) is the **least significant bit** (LSB).

`adderAux n x y cin` adds `x + y + cin` (with `cin` as the carry into
the LSB) and returns `(sum bits, final carry-out)`.

Implementation:

* We recurse on the prefix bits `0..n-1` (more significant),
* we treat the **last index** `⟨n, _⟩` of `Fin (n+1)` as the LSB.
-/
def adderAux : (n : ℕ) →
    (Fin n → Bool) → (Fin n → Bool) → Bool →
    (Fin n → Bool) × Bool
| 0,      _, _, cin =>
    (fun i => Fin.elim0 i, cin)
| (n+1),  x, y, cin =>
    -- least significant bit is the *last* index
    let last : Fin (n+1) := ⟨n, Nat.lt_succ_self n⟩
    let a_last : Bool := x last
    let b_last : Bool := y last
    let (s_last, c_last) := fullAdder a_last b_last cin

    -- prefix bits 0..n-1 are more significant
    let x' : Fin n → Bool :=
      fun i => x ⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self n)⟩
    let y' : Fin n → Bool :=
      fun i => y ⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self n)⟩
    let (s_prefix, c_prefix) := adderAux n x' y' c_last

    -- reassemble: indices < n from `s_prefix`, index n is `s_last`
    let s : Fin (n+1) → Bool :=
      fun i =>
        if h : i.1 < n then
          s_prefix ⟨i.1, h⟩
        else
          s_last
    (s, c_prefix)

/-!
##############################
# Bit-level Shifts (on `Fin n → Bool`)
##############################
-/

/--
Logical **right shift** of a bit-vector (MSB-first):

Given bits `[b₀, b₁, ..., b_{n-1}]` with

* `b₀` the MSB,
* `b_{n-1}` the LSB,

we map

  [b₀, b₁, ..., b_{n-1}] ↦ [0, b₀, b₁, ..., b_{n-2}].

This is a logical right shift by 1 (dropping the LSB, inserting 0 at MSB).
-/
def rightShiftBits {n : ℕ} (x : Fin n → Bool) : Fin n → Bool
| ⟨0,  _⟩ => false
| ⟨Nat.succ k, hk⟩ =>
    -- new bit at index (k+1) is old bit at index k
    have hk' : k < n := Nat.lt_of_succ_lt hk
    x ⟨k, hk'⟩

/--
Logical **left shift** of a bit-vector (MSB-first):

Given bits `[b₀, b₁, ..., b_{n-1}]` with `b₀` MSB, `b_{n-1}` LSB, we map

  [b₀, b₁, ..., b_{n-1}] ↦ [b₁, b₂, ..., b_{n-1}, 0].

This is a logical left shift by 1 (dropping the MSB, inserting 0 at LSB).
-/
def leftShiftBits {n : ℕ} (x : Fin n → Bool) : Fin n → Bool
| ⟨i, _⟩ =>
    -- if there *is* a bit at index i+1, use it; otherwise 0
    if h : i + 1 < n then
      x ⟨i + 1, h⟩
    else
      false

/-!
##############################
# Wire-level Read/Write (no Layout, no Registers)
##############################
-/

/--
Read bits from a state along a list of *global* qubit indices.

We interpret the list `wires` as **MSB-first**:

  * `wires.get ⟨0, _⟩` is the wire for the MSB,
  * `wires.get ⟨w-1, _⟩` is the wire for the LSB.

We return a vector `Fin wires.length → Bool` with the same MSB→LSB order.
-/
def readWiresBits {N : ℕ} (σ : BitState N) (wires : List (Fin N)) :
    Fin wires.length → Bool :=
  fun i => σ (wires.get i)


/-- Overwrite a *single* wire `w` with value `b` in the state `σ`. -/
def setWire {N : ℕ} (σ : BitState N) (w : Fin N) (b : Bool) : BitState N :=
  fun q => if q = w then b else σ q

/--
Core recursive helper for `setWiresBits`:

Given a state `σ`, a list of wires, and a list of bits, overwrite the state
wire-by-wire.

Semantics matches `zip wires bits` truncated to the shorter list:
- if either list runs out, we stop;
- otherwise we set the head wire to the head bit and recurse on the tails.
-/
def setWiresBitsCore {N : ℕ} : BitState N → List (Fin N) → List Bool → BitState N
| σ, [],      _        => σ
| σ, _ :: _,  []       => σ
| σ, w :: ws, b :: bs  =>
    let σ' := setWire σ w b
    setWiresBitsCore σ' ws bs

/--
Overwrite a state along a list of *global* qubit indices with given bits.

The list `wires` is interpreted **MSB-first**, and `bits` is a function
`Fin wires.length → Bool` with the same MSB→LSB order.

Implementation:

* Convert `bits` to a `List Bool` via `List.ofFn`,
* then call `setWiresBitsCore` to walk both lists in lockstep.
-/
def setWiresBits {N : ℕ} (σ : BitState N)
    (wires : List (Fin N)) (bits : Fin wires.length → Bool) :
    BitState N :=
  let bs : List Bool := List.ofFn bits
  setWiresBitsCore σ wires bs


/-- `wiresDisjoint dst src` means no global qubit index appears in both lists. -/
def wiresDisjoint {N : ℕ} (dst src : List (Fin N)) : Prop :=
  ∀ q, q ∈ dst → q ∈ src → False

/-!
##############################
# Wire-level Arithmetic (Adder, Shifts, Negation)
##############################
-/

/--
Wire-level adder:

`adder σ dst src carry h_len_dst h_len_src h_disj`:

- `dst` : list of global qubits, **MSB-first** (destination word).
- `src` : list of global qubits, **MSB-first** (source word).
- `carry` : single global qubit, used as carry-in (into the LSB)
           and as final carry-out.

Preconditions:
* `dst.length ≤ N`
* `src.length ≤ N`
* `wiresDisjoint dst src` (no wire is in both words).

Semantics:

If `wdst = dst.length` and we interpret the bits on `dst` and `src`
as integers in `0 .. 2^wdst - 1` (with index 0 MSB, wdst-1 LSB),
then this performs

  (dst, carry) ← dst + src + carry_in   (mod 2^wdst)
-/
def adder {N : ℕ} (σ : BitState N)
    (dst src : List (Fin N)) (carry : Fin N)
    (_h_len_dst : dst.length ≤ N)
    (_h_len_src : src.length ≤ N)
    (_h_disj    : wiresDisjoint dst src) :
    BitState N :=
  let wdst := dst.length
  let wsrc := src.length

  let dstBits : Fin wdst → Bool :=
    readWiresBits σ dst

  let srcBitsRaw : Fin wsrc → Bool :=
    readWiresBits σ src
  let srcBits : Fin wdst → Bool :=
    fun b =>
      if h : (b.1 < wsrc) then
        srcBitsRaw ⟨b.1, h⟩
      else
        false

  let cin : Bool := σ carry

  let (sumBits, cout) := adderAux wdst dstBits srcBits cin

  let σ₁ : BitState N := setWiresBits σ dst sumBits

  let σ₂ : BitState N :=
    fun q =>
      if q = carry then
        cout
      else
        σ₁ q

  σ₂

/--
Right-shift a word stored on a list of wires:

`rightShiftWires σ wires h_len h_nodup`

interprets `wires` as an MSB-first word:

  [b₀, b₁, ..., b_{k-1}]   (b₀ MSB, b_{k-1} LSB)

and updates those wires to

  [0, b₀, b₁, ..., b_{k-2}]

(i.e. logical right shift by 1).

Other qubits are unchanged.
-/
def rightShiftWires {N : ℕ} (σ : BitState N)
    (wires : List (Fin N))
    (_h_len   : wires.length ≤ N)
    (_h_nodup : wires.Nodup) :
    BitState N :=
  let w    := wires.length
  let bits : Fin w → Bool := readWiresBits σ wires
  let bits' : Fin w → Bool := rightShiftBits bits
  setWiresBits σ wires bits'

/--
Left-shift a word stored on a list of wires:

`leftShiftWires σ wires h_len h_nodup`

interprets `wires` as an MSB-first word:

  [b₀, b₁, ..., b_{k-1}]   (b₀ MSB, b_{k-1} LSB)

and updates those wires to

  [b₁, b₂, ..., b_{k-1}, 0]

(i.e. logical left shift by 1).

Other qubits are unchanged.
-/
def leftShiftWires {N : ℕ} (σ : BitState N)
    (wires : List (Fin N))
    (_h_len   : wires.length ≤ N)
    (_h_nodup : wires.Nodup) :
    BitState N :=
  let w    := wires.length
  let bits : Fin w → Bool := readWiresBits σ wires
  let bits' : Fin w → Bool := leftShiftBits bits
  setWiresBits σ wires bits'


/--
Carry-less wire-level adder, with **LSB alignment** and MSB-first convention.

- `dst`, `src` : lists of global qubits, MSB-first.

Semantics:

> dst ← dst + src  (mod 2^(dst.length))

where the **LSBs are aligned**:

* If `dst` has width `wdst` and `src` has width `wsrc`,
  then the bit at distance `d` from the right (LSB) of `dst`
  is added with the bit at distance `d` from the right of `src`,
  if it exists; otherwise that src bit is treated as 0.
-/
def adderNoCarry {N : ℕ} (σ : BitState N)
    (dst src : List (Fin N))
    (_h_len_dst : dst.length ≤ N)
    (_h_len_src : src.length ≤ N)
    (_h_disj    : wiresDisjoint dst src) :
    BitState N :=
  let wdst := dst.length
  let wsrc := src.length

  -- MSB-first bits of dst and src
  let dstBits : Fin wdst → Bool :=
    readWiresBits σ dst
  let srcBitsRaw : Fin wsrc → Bool :=
    readWiresBits σ src

  -- Right-align src with dst (LSB alignment), still MSB-first indexing.
  let srcBits : Fin wdst → Bool :=
    fun b =>
      let i : Nat := b.1
      -- distance from the right (LSB) in dst
      let d : Nat := (wdst - 1) - i
      if h : d < wsrc then
        -- src index: wsrc - 1 - d   (same distance from right)
        let jNat : Nat := (wsrc - 1) - d
        have hj : jNat < wsrc := by
          have : jNat ≤ wsrc - 1 := Nat.sub_le _ _
          omega
        srcBitsRaw ⟨jNat, hj⟩
      else
        false

  -- ripple-carry add, no incoming carry
  let (sumBits, _cout) := adderAux wdst dstBits srcBits false

  -- write back into dst wires
  setWiresBits σ dst sumBits


/--
Inverse of `adderNoCarry` (wire-level):

Given the same parameters as `adderNoCarry`, but applied to a state where
`dst` currently holds

  dst' = (dst + src) mod 2^(dst.length)

this computes

  dst ← (dst' - src) mod 2^(dst.length),

i.e. it reverses the effect of `adderNoCarry` on the destination word.

Conventions:
* `dst`, `src` : MSB-first lists of wires.
* LSBs are aligned exactly as in `adderNoCarry`.
-/
def adderNoCarryInv {N : ℕ} (σ : BitState N)
    (dst src : List (Fin N))
    (_h_len_dst : dst.length ≤ N)
    (_h_len_src : src.length ≤ N)
    (_h_disj    : wiresDisjoint dst src) :
    BitState N :=
  let wdst := dst.length
  let wsrc := src.length

  -- MSB-first bits of dst and src
  let dstBits : Fin wdst → Bool :=
    readWiresBits σ dst
  let srcBitsRaw : Fin wsrc → Bool :=
    readWiresBits σ src

  -- LSB-align src inside width `wdst`, same as in `adderNoCarry`.
  let srcAligned : Fin wdst → Bool :=
    fun b =>
      let i : Nat := b.1
      -- distance from the right (LSB) in dst
      let d : Nat := (wdst - 1) - i
      if h : d < wsrc then
        -- src index j = wsrc - 1 - d
        let jNat : Nat := (wsrc - 1) - d
        have hj : jNat < wsrc := by
          omega
        srcBitsRaw ⟨jNat, hj⟩
      else
        false

  -- Two's-complement of srcAligned: (-srcAligned) mod 2^wdst
  let notSrc : Fin wdst → Bool := fun i => ! srcAligned i
  let (negSrc, _carryNeg) := adderAux wdst notSrc (fun _ => false) true

  -- dst - src = dst + (-src) mod 2^wdst
  let (diffBits, _carryDiff) := adderAux wdst dstBits negSrc false

  -- Write back into dst wires
  setWiresBits σ dst diffBits

/--
Two's-complement negation of a word stored on a list of wires:

`negateWires σ wires h_len h_nodup`

interprets `wires` as an MSB-first word

  [b₀, b₁, ..., b_{k-1}]   (b₀ MSB, b_{k-1} LSB)

and replaces those bits with

  (-x) mod 2^k = (~x + 1) mod 2^k,

where `~` is bitwise NOT and `+` is ordinary binary addition
using `adderAux`.

Only the qubits in `wires` are updated; all others are unchanged.
-/
def negateWires {N : ℕ} (σ : BitState N)
    (wires : List (Fin N))
    (_h_len   : wires.length ≤ N)
    (_h_nodup : wires.Nodup) :
    BitState N :=
  let w    := wires.length
  -- current bits of the word
  let bits : Fin w → Bool := readWiresBits σ wires
  -- bitwise NOT
  let inv  : Fin w → Bool := fun i => ! bits i
  -- add 1: (~x) + 1 = -x  (mod 2^w),
  -- implemented as carry-in = true at the LSB, y = 0.
  let (negBits, _cout) := adderAux w inv (fun _ => false) true
  setWiresBits σ wires negBits


/-!
##############################
# Generic Examples: Adder, Shifts, Negation, Subtraction
##############################
-/

-- Example 1: plain adder with explicit carry wire.
def exampleState₁ : BitState 5
| ⟨0, _⟩ => true   -- dst MSB = 1
| ⟨1, _⟩ => false  -- dst LSB = 0  → dst = 2
| ⟨2, _⟩ => true   -- src MSB = 1
| ⟨3, _⟩ => true   -- src LSB = 1  → src = 3
| ⟨4, _⟩ => false  -- carry = 0

def exampleDst₁ : List (Fin 5) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩]

def exampleSrc₁ : List (Fin 5) :=
  [⟨2, by decide⟩, ⟨3, by decide⟩]

def exampleCarry₁ : Fin 5 := ⟨4, by decide⟩

lemma exampleDst₁_len_le : exampleDst₁.length ≤ 5 := by decide
lemma exampleSrc₁_len_le : exampleSrc₁.length ≤ 5 := by decide

lemma exampleDisj₁ : wiresDisjoint exampleDst₁ exampleSrc₁ := by
  intro q hdst hsrc
  simp [exampleDst₁] at hdst
  simp [exampleSrc₁] at hsrc
  cases hdst <;> cases hsrc <;> simp_all

def exampleAfter₁ : BitState 5 :=
  adder exampleState₁ exampleDst₁ exampleSrc₁ exampleCarry₁
    exampleDst₁_len_le exampleSrc₁_len_le exampleDisj₁

#eval showState exampleState₁    -- "10110"
#eval showState exampleAfter₁    -- dst & carry updated (MSB-first)


-- Example 2: shifts on a 2-bit word (wires [0,1]) inside a 4-bit state.
def exampleState_shift : BitState 4
| ⟨0, _⟩ => true   -- bit 0 (MSB)
| ⟨1, _⟩ => false  -- bit 1
| ⟨2, _⟩ => true   -- extra bit
| ⟨3, _⟩ => true   -- extra bit

def exampleWires_shift : List (Fin 4) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩]

lemma exampleWires_shift_len_le : exampleWires_shift.length ≤ 4 := by decide
lemma exampleWires_shift_nodup : exampleWires_shift.Nodup := by decide

def exampleState_rightShift : BitState 4 :=
  rightShiftWires exampleState_shift exampleWires_shift
    exampleWires_shift_len_le exampleWires_shift_nodup

def exampleState_leftShift : BitState 4 :=
  leftShiftWires exampleState_shift exampleWires_shift
    exampleWires_shift_len_le exampleWires_shift_nodup

#eval showState exampleState_shift       -- initial bits
#eval showState exampleState_rightShift  -- right-shift on [0,1]
#eval showState exampleState_leftShift   -- left-shift on [0,1]


-- Example 3: carry-less adder on the same dst/src as example 1.
def exampleAfterNoCarry₁ : BitState 5 :=
  adderNoCarry exampleState₁ exampleDst₁ exampleSrc₁
    exampleDst₁_len_le exampleSrc₁_len_le exampleDisj₁

#eval showState exampleState₁
#eval showState exampleAfterNoCarry₁


-- Example 4: two's-complement negation on a 3-bit word [0,1,2].
def exampleState_neg : BitState 4
| ⟨0, _⟩ => true   -- b₀ (MSB)
| ⟨1, _⟩ => false  -- b₁
| ⟨2, _⟩ => true   -- b₂ (LSB)   → value 5
| ⟨3, _⟩ => false  -- extra bit

def exampleWires_neg : List (Fin 4) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩]

lemma exampleWires_neg_len_le : exampleWires_neg.length ≤ 4 := by decide
lemma exampleWires_neg_nodup : exampleWires_neg.Nodup := by decide

def exampleState_afterNeg : BitState 4 :=
  negateWires exampleState_neg exampleWires_neg
    exampleWires_neg_len_le exampleWires_neg_nodup

#eval showState exampleState_neg       -- "1010"
#eval showState exampleState_afterNeg  -- should have "...011" on wires [0,1,2]


-- Example 5: subtraction via negate + add:  dst ← dst - src (mod 2^w).
/-
N = 5, with:

  dst wires = [0,1] (2 bits, MSB-first)
  src wires = [2,3] (2 bits, MSB-first)
  wire 4 unused

Initial:

  dst = 1  → bits "01" on wires [0,1]
  src = 3  → bits "11" on wires [2,3]
-/

/-- Initial state: global bits [b₀..b₄] = "01110". -/
def exampleState_sub : BitState 5
| ⟨0, _⟩ => false  -- dst MSB = 0
| ⟨1, _⟩ => true   -- dst LSB = 1  → dst = 1
| ⟨2, _⟩ => true   -- src MSB = 1
| ⟨3, _⟩ => true   -- src LSB = 1  → src = 3
| ⟨4, _⟩ => false  -- unused

def exampleDst_sub : List (Fin 5) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩]

def exampleSrc_sub : List (Fin 5) :=
  [⟨2, by decide⟩, ⟨3, by decide⟩]

lemma exampleDst_sub_len_le : exampleDst_sub.length ≤ 5 := by decide
lemma exampleSrc_sub_len_le : exampleSrc_sub.length ≤ 5 := by decide

lemma exampleDst_sub_nodup : exampleDst_sub.Nodup := by decide
lemma exampleSrc_sub_nodup : exampleSrc_sub.Nodup := by decide

lemma exampleDisj_sub : wiresDisjoint exampleDst_sub exampleSrc_sub := by
  intro q hdst hsrc
  simp [exampleDst_sub] at hdst
  simp [exampleSrc_sub] at hsrc
  cases hdst <;> cases hsrc <;> aesop

/-- Step 1: negate `src` in-place: src ← -src (mod 4). -/
def exampleAfterNeg_sub : BitState 5 :=
  negateWires exampleState_sub exampleSrc_sub
    exampleSrc_sub_len_le exampleSrc_sub_nodup

/-- Step 2: dst ← dst + src (which now holds -src_original). -/
def exampleAfterSub : BitState 5 :=
  adderNoCarry exampleAfterNeg_sub exampleDst_sub exampleSrc_sub
    exampleDst_sub_len_le exampleSrc_sub_len_le exampleDisj_sub

#eval showState exampleState_sub
#eval showState exampleAfterNeg_sub
#eval showState exampleAfterSub


/-!
##############################
# Toy PhaseProduct(phi3) Block for k = 2, n = 2
##############################
-/

/-- Our tiny example uses 6 wires total. -/
def Ntoy : ℕ := 6

/-- Names for the 6 wires, following the diagram (x-half, z-half, carries). -/
def x0 : Fin Ntoy := ⟨0, by decide⟩   -- top x half
def x1 : Fin Ntoy := ⟨1, by decide⟩   -- bottom x half
def cX : Fin Ntoy := ⟨2, by decide⟩   -- overflow bit for x ADD

def z0 : Fin Ntoy := ⟨3, by decide⟩   -- top z half
def z1 : Fin Ntoy := ⟨4, by decide⟩   -- bottom z half
def cZ : Fin Ntoy := ⟨5, by decide⟩   -- overflow bit for z ADD

/-- A word of 1 bit is just a singleton list; MSB = LSB here. -/
def x0_word : List (Fin Ntoy) := [x0]
def x1_word : List (Fin Ntoy) := [x1]
def z0_word : List (Fin Ntoy) := [z0]
def z1_word : List (Fin Ntoy) := [z1]

/-- Length lemmas for the words (needed by `adder`). -/
lemma x0_word_len_le : x0_word.length ≤ Ntoy := by decide
lemma x1_word_len_le : x1_word.length ≤ Ntoy := by decide
lemma z0_word_len_le : z0_word.length ≤ Ntoy := by decide
lemma z1_word_len_le : z1_word.length ≤ Ntoy := by decide

/-- Disjointness lemmas for each ADD (their dst/src wires don't overlap). -/
lemma disj_x : wiresDisjoint x0_word x1_word := by
  intro q hdst hsrc
  simp [x0_word] at hdst
  simp [x1_word] at hsrc
  cases hdst ; cases hsrc

lemma disj_z : wiresDisjoint z0_word z1_word := by
  intro q hdst hsrc
  simp [z0_word] at hdst
  simp [z1_word] at hsrc
  cases hdst ; cases hsrc

/--
Toy "PhaseProduct(phi3)" block for `k = 2`, `n = 2`, **ignoring PhaseProduct**:

It just performs two independent ADDs:

* top:   (x0, x1, cX)  ↦  (x0 + x1, cX = overflow)
* bottom:(z0, z1, cZ)  ↦  (z0 + z1, cZ = overflow)

All words here are width 1, so the "n/2 + 1 bits" for each sum are
exactly `(carry, that 1-bit word)`.
-/
def phaseProduct_phi3_toy (σ : BitState Ntoy) : BitState Ntoy :=
  -- first ADD on the x wires: (x0, x1, cX)
  let σ₁ : BitState Ntoy :=
    adder σ x0_word x1_word cX
      x0_word_len_le x1_word_len_le disj_x
  -- second ADD on the z wires: (z0, z1, cZ)
  let σ₂ : BitState Ntoy :=
    adder σ₁ z0_word z1_word cZ
      z0_word_len_le z1_word_len_le disj_z
  σ₂
