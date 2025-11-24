import FastMultiplication.QuantumCircuit.Circuit

/-!
##############################
# Register Layout + State
##############################
-/

/--
A *register layout* over `N` global wires with `k` logical registers.

* `regWires i` is the **MSB-first** list of global qubits belonging to
  register `i : Fin k`.
-/
structure RegLayout (k N : ℕ) where
  regWires : Fin k → List (Fin N)

/--
Well-formedness of a register layout.

`RegLayout.Valid L` means:

* each register list has length at most `N`,
* no register list has duplicates,
* different registers do not share wires.
-/
inductive RegLayout.Valid {k N : ℕ} (L : RegLayout k N) : Prop where
  | mk
      (len_le  : ∀ i, (L.regWires i).length ≤ N)
      (nodup   : ∀ i, (L.regWires i).Nodup)
      (disjoint: ∀ i j, i ≠ j → wiresDisjoint (L.regWires i) (L.regWires j))

/--
A *register state* consists of:

* a register layout over `N` wires and `k` registers, and
* a global classical bitstring `σ : BitState N`.
-/
structure RegState (k N : ℕ) where
  layout : RegLayout k N
  σ      : BitState N

namespace RegState

/-- Number of bits (width) of register `i`. -/
def width {k N : ℕ} (S : RegState k N) (i : Fin k) : ℕ :=
  (S.layout.regWires i).length

/--
Read the bits of register `i` as a small bit-vector
`Fin (S.width i) → Bool`, MSB-first.
-/
def readRegBits {k N : ℕ} (S : RegState k N) (i : Fin k) :
    Fin (S.width i) → Bool :=
  readWiresBits S.σ (S.layout.regWires i)

/--
Overwrite register `i` with a new bit-vector, leaving all other wires
unchanged.
-/
def setRegBits {k N : ℕ} (S : RegState k N) (i : Fin k)
    (bits : Fin (S.width i) → Bool) : RegState k N :=
  { S with σ := setWiresBits S.σ (S.layout.regWires i) bits }

/-- Show a single register `i` as an MSB-first bitstring `"0101"`. -/
def showReg {k N : ℕ} (S : RegState k N) (i : Fin k) : String :=
  bitsString (S.readRegBits i)

/--
Show the whole `RegState` as:

`"R0: 010 | R1: 11 | R2: 0 | ..."`
-/
def showByRegs {k N : ℕ} (S : RegState k N) : String :=
  let regStrings : List String :=
    (List.finRange k).map (fun i =>
      "R" ++ toString i.1 ++ ": " ++ S.showReg i)
  String.intercalate " | " regStrings


/--
Register-level **add with carry register**:

`addWithCarryReg S dst src cReg h_layout h_dst_ne_src h_dst_ne_c h_src_ne_c h_single`

Assumptions:

* `dst`, `src`, `cReg` are distinct registers:
    - `dst ≠ src`, `dst ≠ cReg`, `src ≠ cReg`.
* `h_layout` : the layout is valid (lengths, nodup, disjoint registers).
* `h_single` : `cReg` is a **single-bit register**:
      `∃ c, S.layout.regWires cReg = [c]`.

Semantics:

1. Let `c` be that unique wire of `cReg`.
2. Run wire-level ADD:

     (dstW, c) ← dstW + srcW + c_in   (mod 2^(|dstW|))

3. Update layout:
   * `dst` now has wires `c :: dstW` (carry becomes new MSB),
   * `cReg` is emptied (becomes `[]`),
   * other registers unchanged.
-/
def addWithCarryReg
  {k N : ℕ}
  (S : RegState k N)
  (dst src carry : Fin k)
  (h_len_comb      :(S.layout.regWires carry ++ S.layout.regWires dst).length ≤ N)
  (h_len_src       :(S.layout.regWires src).length ≤ N)
  (h_disj_comb_src :
     wiresDisjoint
       (S.layout.regWires carry ++ S.layout.regWires dst)
       (S.layout.regWires src))
  : RegState k N :=
  let carryW := List.replicate n (Fin.mk 0 (by  ))
  let dstW   := S.layout.regWires dst
  let srcW   := S.layout.regWires src
  let combDst := carryW ++ dstW --concatenating the carry register to the source.
  let σ' : BitState N := --Bitwise adder function
    adderNoCarry S.σ combDst srcW
      h_len_comb h_len_src h_disj_comb_src
  let L' : RegLayout k N := --New layout with updated destination size and carry register size
    { regWires := fun i =>
        if _h0 : i = dst then
          combDst
        else if _h1 : i = carry then
          []
        else
          S.layout.regWires i }

  { layout := L', σ := σ' }




/--
Register-level **add without explicit carry wire**:

`addNoCarry S dst src h_layout h_dst_ne_src` does:

  dst ← dst + src  (mod 2^(width dst))

using the wire-level `adderNoCarry` on the wires of registers `dst`
and `src`. The layout is unchanged.

Requirements:

* `h_layout`      : guarantees that register wire lists are in-bounds,
                    nodup, and pairwise disjoint.
* `h_dst_ne_src`  : ensures `dst` and `src` are different registers.
-/
def addNoCarry
  {k N : ℕ}
  (S : RegState k N)
  (dst src : Fin k)
  (h_layout     : RegLayout.Valid S.layout)
  (h_dst_ne_src : dst ≠ src)
  : RegState k N :=
by
  -- unpack layout validity
  cases h_layout with
  | mk len_le nodup disjoint =>
    let dstW := S.layout.regWires dst
    let srcW := S.layout.regWires src

    -- structural facts for the wire-level adder
    have h_len_dst : dstW.length ≤ N := len_le dst
    have h_len_src : srcW.length ≤ N := len_le src
    have h_disj    : wiresDisjoint dstW srcW :=
      disjoint dst src h_dst_ne_src

    -- run the wire-level carry-less adder
    let σ' : BitState N :=
      adderNoCarry S.σ dstW srcW h_len_dst h_len_src h_disj

    -- layout unchanged
    exact { S with σ := σ' }
/--
Register-level **right shift**:

`rightShiftReg S i h_layout` applies `rightShiftWires` to the wires of
register `i` (MSB-first), i.e.

  [b₀, b₁, ..., b_{w-1}]  ↦  [0, b₀, b₁, ..., b_{w-2}]

Only the bits of register `i` are changed; the layout is unchanged.
-/
def rightShiftReg
  {k N : ℕ}
  (S : RegState k N)
  (i : Fin k)
  (h_layout : RegLayout.Valid S.layout)
  : RegState k N :=
by
  cases h_layout with
  | mk len_le nodup disjoint =>
    let wires := S.layout.regWires i
    have h_len   : wires.length ≤ N := len_le i
    have h_nodup : wires.Nodup      := nodup i
    let σ' : BitState N :=
      rightShiftWires S.σ wires h_len h_nodup
    exact { S with σ := σ' }


/--
Register-level **left shift**:

`leftShiftReg S i h_layout` applies `leftShiftWires` to the wires of
register `i` (MSB-first), i.e.

  [b₀, b₁, ..., b_{w-1}]  ↦  [b₁, b₂, ..., b_{w-1}, 0]

Only the bits of register `i` are changed; the layout is unchanged.
-/
def leftShiftReg
  {k N : ℕ}
  (S : RegState k N)
  (i : Fin k)
  (h_layout : RegLayout.Valid S.layout)
  : RegState k N :=
by
  cases h_layout with
  | mk len_le nodup disjoint =>
    let wires := S.layout.regWires i
    have h_len   : wires.length ≤ N := len_le i
    have h_nodup : wires.Nodup      := nodup i
    let σ' : BitState N :=
      leftShiftWires S.σ wires h_len h_nodup
    exact { S with σ := σ' }


/--
Register-level **two's-complement negation**:

`negateReg S i h_layout` interprets register `i` (MSB-first) as a
word of width `w = width i` and replaces it with

  (-x) mod 2^w = (~x + 1) mod 2^w

using the wire-level `negateWires`.

Only the bits of register `i` are changed; the layout is unchanged.
-/
def negateReg
  {k N : ℕ}
  (S : RegState k N)
  (i : Fin k)
  (h_layout : RegLayout.Valid S.layout)
  : RegState k N :=
by
  cases h_layout with
  | mk len_le nodup disjoint =>
    let wires := S.layout.regWires i
    have h_len   : wires.length ≤ N := len_le i
    have h_nodup : wires.Nodup      := nodup i
    let σ' : BitState N :=
      negateWires S.σ wires h_len h_nodup
    exact { S with σ := σ' }

end RegState


namespace RegState

/--
Interpret a bit-vector `v : Fin n → Bool` (MSB-first) as a natural number.

Bit at index 0 is the MSB; bit at index n-1 is the LSB.
-/
def bitsToNat {n : ℕ} (v : Fin n → Bool) : Nat :=
  (List.finRange n).foldl
    (fun acc i =>
      let b      := v i
      let weight := Nat.pow 2 (n - 1 - i.1)  -- MSB has exponent n-1
      acc + (if b then weight else 0))
    0

/-- Integer value of register `i` in state `S`, interpreting bits MSB-first. -/
def regValue {k N : ℕ} (S : RegState k N) (i : Fin k) : Nat :=
  bitsToNat (S.readRegBits i)

/--
Pretty-print a single register as:

  `R0 = 11 (1011)`

where `11` is the integer value and `1011` is the bitstring (MSB-first).
-/
def showRegPretty {k N : ℕ} (S : RegState k N) (i : Fin k) : String :=
  let v    := S.regValue i
  let bits := S.readRegBits i
  "R" ++ toString i.1 ++ " = " ++ toString v ++ " (" ++ bitsString bits ++ ")"

/--
Pretty-print the whole `RegState` as:

  `R0 = 11 (1011) | R1 = 6 (0110) | ...`
-/
def showPretty {k N : ℕ} (S : RegState k N) : String :=
  let regStrings : List String :=
    (List.finRange k).map (fun i => S.showRegPretty i)
  String.intercalate " | " regStrings

/-- Use `showPretty` for `ToString`. -/
instance instToString {k N : ℕ} : ToString (RegState k N) :=
  ⟨showPretty⟩

/-- Use `showPretty` for `Repr` as well (so `#eval` looks nice). -/
instance instRepr {k N : ℕ} : Repr (RegState k N) :=
  ⟨fun S _ => showPretty S⟩

end RegState


/-
Big example: k = 2 registers, N = 8 global wires.

Register 0: wires [0,1,2,3]  (MSB → LSB)
Register 1: wires [4,5,6,7]  (MSB → LSB)
-/

def kBig : ℕ := 2
def NBig : ℕ := 8

/-- Wire assignment for each register (MSB-first). -/
def bigRegWires : Fin kBig → List (Fin NBig)
| ⟨0, _⟩ => [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩]
| ⟨1, _⟩ => [⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩]

/-- Concrete layout for the big example. -/
def bigLayout : RegLayout kBig NBig :=
  { regWires := bigRegWires }

/--
Validity of the big layout:

* each register has length ≤ NBig,
* no duplicates inside a register,
* registers are disjoint.
-/
lemma bigLayout_valid : RegLayout.Valid bigLayout := by
  refine RegLayout.Valid.mk ?len ?nodup ?disjoint
  · -- lengths
    intro i
    fin_cases i <;> simp [bigLayout, bigRegWires,NBig]
  · -- no duplicates
    intro i
    fin_cases i <;> simp [bigLayout, bigRegWires]
  · -- pairwise disjoint
    intro i j hij q hdi hsj
    fin_cases i <;> fin_cases j
    · -- i = 0, j = 1
      simp [bigLayout, bigRegWires] at hdi hsj
      -- wires of reg 0 are 0,1,2,3; wires of reg 1 are 4,5,6,7.
      -- No element can be in both.
      rcases hdi with hdi | hdi | hdi | hdi <;>
      rcases hsj with hsj | hsj | hsj | hsj <;>
      subst hdi <;> aesop
    · -- i = 1, j = 0 (symmetric)
      simp [bigLayout, bigRegWires] at hdi hsj
      rcases hdi with hdi | hdi | hdi | hdi <;>
      rcases hsj with hsj | hsj | hsj | hsj <;>
      subst hdi <;> aesop
    · -- i = 1, j = 0 (symmetric)
      simp [bigLayout, bigRegWires] at hdi hsj
      rcases hdi with hdi | hdi | hdi | hdi <;>
      rcases hsj with hsj | hsj | hsj | hsj <;>
      subst hdi <;> aesop
    · -- i = 1, j = 0 (symmetric)
      simp [bigLayout, bigRegWires] at hdi hsj
      rcases hdi with hdi | hdi | hdi | hdi <;>
      rcases hsj with hsj | hsj | hsj | hsj <;>
      subst hdi <;> aesop

/-- Named registers. -/
def R0 : Fin kBig := ⟨0, by decide⟩
def R1 : Fin kBig := ⟨1, by decide⟩

/--
Initial global state:

Indices 0..7 (MSB-first):

  [1,0,1,1, 0,1,1,0]

So:

  * R0 wires [0,1,2,3] = "1011" = 11
  * R1 wires [4,5,6,7] = "0110" = 6
-/
def bigInitState : BitState NBig
| ⟨0, _⟩ => true   -- R0 MSB
| ⟨1, _⟩ => false
| ⟨2, _⟩ => true
| ⟨3, _⟩ => true   -- R0 LSB  → 1011 = 11
| ⟨4, _⟩ => false  -- R1 MSB
| ⟨5, _⟩ => true
| ⟨6, _⟩ => true
| ⟨7, _⟩ => false  -- R1 LSB  → 0110 = 6

/-- Bundle layout + global bitstring into a `RegState`. -/
def bigRegState : RegState kBig NBig :=
  { layout := bigLayout, σ := bigInitState }

#eval RegState.showPretty bigRegState
-- or simply:
#eval bigRegState
-- e.g. `R0 = 11 (1011) | R1 = 6 (0110)`


/--
Example: logical right shift of R0:

  [b0,b1,b2,b3] ↦ [0, b0, b1, b2]
-/
def big_after_rightShift_R0 : RegState kBig NBig :=
  RegState.rightShiftReg bigRegState R0 bigLayout_valid

/--
Example: logical left shift of R1:

  [b0,b1,b2,b3] ↦ [b1, b2, b3, 0]
-/
def big_after_leftShift_R1 : RegState kBig NBig :=
  RegState.leftShiftReg bigRegState R1 bigLayout_valid

#eval bigRegState
#eval big_after_rightShift_R0
#eval big_after_leftShift_R1





/-- Big-ish example with an extra free wire for carry. -/
def kCarry : ℕ := 2
def NCarry : ℕ := 9

/-- Wire assignment for each register (MSB-first). -/
def carryRegWires : Fin kCarry → List (Fin NCarry)
| ⟨0, _⟩ => [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩]
| ⟨1, _⟩ => [⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩]

def carryLayout : RegLayout kCarry NCarry :=
  { regWires := carryRegWires }

/--
Validity of the carry layout:

* each register has length ≤ NCarry,
* no duplicates inside a register,
* registers are disjoint.
-/
lemma carryLayout_valid : RegLayout.Valid carryLayout := by
  refine RegLayout.Valid.mk ?len ?nodup ?disjoint
  · -- lengths
    intro i
    fin_cases i <;> simp [carryLayout, carryRegWires,NCarry]
  · -- no duplicates
    intro i
    fin_cases i <;> simp [carryLayout, carryRegWires]
  · -- pairwise disjoint
    intro i j hij q hdi hsj
    fin_cases i <;> fin_cases j
    · -- i = 0, j = 1
      simp [carryLayout, carryRegWires] at hdi hsj
      rcases hdi with hdi | hdi | hdi | hdi <;>
      rcases hsj with hsj | hsj | hsj | hsj <;>
      aesop
    · -- i = 1, j = 0 (symmetric)
      simp [carryLayout, carryRegWires] at hdi hsj
      rcases hdi with hdi | hdi | hdi | hdi <;>
      rcases hsj with hsj | hsj | hsj | hsj <;>
      aesop
    · -- i = 0, j = 1
      simp [carryLayout, carryRegWires] at hdi hsj
      rcases hdi with hdi | hdi | hdi | hdi <;>
      rcases hsj with hsj | hsj | hsj | hsj <;>
      aesop
    · -- i = 0, j = 1
      simp [carryLayout, carryRegWires] at hdi hsj
      rcases hdi with hdi | hdi | hdi | hdi <;>
      rcases hsj with hsj | hsj | hsj | hsj <;>
      aesop

/-- Named registers. -/
def R0c : Fin kCarry := ⟨0, by decide⟩
def R1c : Fin kCarry := ⟨1, by decide⟩

/-- Fresh carry wire, not in any register initially. -/
def carryWire : Fin NCarry := ⟨8, by decide⟩

lemma carryWire_fresh : ∀ i, carryWire ∉ carryLayout.regWires i := by
  intro i
  fin_cases i <;> simp [carryLayout, carryRegWires, carryWire]


/--
Initial global state on 9 wires (indices 0..8):

  wires 0..7 = [1,0,1,1,  0,1,1,0]   (as in the earlier big example)
  wire 8     = 0 (carry-in)

So:

  * R0 wires [0,1,2,3] = "1011" = 11
  * R1 wires [4,5,6,7] = "0110" = 6
  * carryWire (8)      = 0
-/
def carryInitState : BitState NCarry
| ⟨0, _⟩ => true   -- R0 MSB
| ⟨1, _⟩ => false
| ⟨2, _⟩ => true
| ⟨3, _⟩ => true   -- R0 LSB   → 1011 = 11
| ⟨4, _⟩ => false  -- R1 MSB
| ⟨5, _⟩ => true
| ⟨6, _⟩ => true
| ⟨7, _⟩ => false  -- R1 LSB   → 0110 = 6
| ⟨8, _⟩ => false  -- carry bit = 0

/-- Bundle layout + state into a `RegState`. -/
def carryRegState : RegState kCarry NCarry :=
  { layout := carryLayout, σ := carryInitState }

/-!
Example illustrating `addWithCarryReg`:

- R0 (dst)   = 01      on wires [0,1]
- R1 (src)   = 11010   on wires [2,3,4,5,6]
- R2 (carry) = 0000    on wires [7,8,9,10]

We form the combined word C ++ D = 0000 01 = 000001 (1),
and then compute

  000001 + 11010 = 011011

so the new destination register holds 011011 across C ++ D,
and the carry register becomes empty.
-/

------------------------------------------------------------
-- Layout and initial state for the example
------------------------------------------------------------


/-- Wires for each register (MSB-first). -/
def exRegWires : Fin 3 → List (Fin 11)
| 0 => [0, 1]              -- R0: dst, 2 bits
| 1 => [2, 3, 4, 5, 6]     -- R1: src, 5 bits
| 2 => [7, 8, 9, 10]       -- R2: carry, 4 bits

def exLayout : RegLayout 3 11 :=
  { regWires := exRegWires }

/--
Initial global state (indices 0..10):

  R0 on [0,1]  = 0 1     → "01"
  R1 on [2..6] = 1 1 0 1 0 → "11010"
  R2 on [7..10]= 0 0 0 0 → "0000"
-/
def exInitState : BitState 11
| 0  => false   -- R0 MSB = 0
| 1  => true    -- R0 LSB = 1   → 01
| 2  => true    -- R1 bits = 11010
| 3  => true
| 4  => false
| 5  => true
| 6  => false
| 7  => false   -- R2 = 0000
| 8  => false
| 9  => false
| 10 => false

/-- Bundle layout + state into a register state. -/
def exRegState : RegState 3 11 :=
  { layout := exLayout, σ := exInitState }

/-- Register names: dst = 0, src = 1, carry = 2. -/
def exDst   : Fin 3 := 0
def exSrc   : Fin 3 := 1
def exCarry : Fin 3 := 2

------------------------------------------------------------
-- Structural facts for this particular layout
------------------------------------------------------------

/-- Length of combined destination word `carry ++ dst` is ≤ NEx. -/
lemma ex_len_comb :
  (exRegState.layout.regWires exCarry ++ exRegState.layout.regWires exDst).length ≤ 11 := by
  simp [exRegState, exLayout, exRegWires, exCarry, exDst]

/-- Length of src word is ≤ NEx. -/
lemma ex_len_src :
  (exRegState.layout.regWires exSrc).length ≤ 11 := by
  -- regWires exSrc = [2,3,4,5,6]
  simp [exRegState, exLayout, exRegWires, exSrc]

/--
Combined destination wires (carry ++ dst) are disjoint from src wires.

Concretely:

  carry ++ dst = [7,8,9,10,0,1]
  src          = [2,3,4,5,6]
-/
lemma ex_disj_comb_src :
  wiresDisjoint
    (exRegState.layout.regWires exCarry ++ exRegState.layout.regWires exDst)
    (exRegState.layout.regWires exSrc) := by
  intro q hcomb hsrc
  -- expand memberships and let `simp`/`decide` notice they can't overlap
  simp [exRegState, exLayout, exRegWires, exCarry, exSrc, exDst] at hcomb hsrc
  -- hcomb says q ∈ {7,8,9,10,0,1}, hsrc says q ∈ {2,3,4,5,6} → impossible
  aesop

------------------------------------------------------------
-- Run addWithCarryReg and inspect the result
------------------------------------------------------------

/--
Run the high-level operation:

  dst ← (carry ++ dst) + src  (mod 2^(|carry|+|dst|))

and merge the carry register into dst.
-/
def exAfterAddWithCarry : RegState 3 11 :=
  RegState.addWithCarryReg
    exRegState
    exDst exSrc exCarry
    ex_len_comb ex_len_src ex_disj_comb_src

-- Global bitstrings before and after (MSB-first).
#eval showState exRegState.σ          -- "01101000000"
#eval showState exAfterAddWithCarry.σ -- should encode "...011011" on carry++dst
#eval exRegState.showPretty
#eval exAfterAddWithCarry.showPretty
/-
If you have a pretty-printer for registers (e.g. `showPretty`):

  #eval exRegState.showPretty
  #eval exAfterAddWithCarry.showPretty

You should see that:
  * Initially:  R0 = 01, R1 = 11010, R2 = 0000
  * After:      R0 holds 011011 across wires [7,8,9,10,0,1],
                R2 has become empty.
-/
/-
############################################################
# Example A: dst width 2, src width 5, carry width 3 (all 0)
############################################################
-/

/-- Wires for each register (MSB-first). -/
def exARegWires : Fin 3 → List (Fin 11)
| 0 => [⟨0, by decide⟩, ⟨1, by decide⟩]                       -- R0: dst,  "10"  = 2
| 1 => [⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩,
        ⟨5, by decide⟩, ⟨6, by decide⟩]                       -- R1: src,  "10101" = 21
| 2 => [⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩]      -- R2: carry, "000"  = 0
-- wire 10 unused

def exALayout : RegLayout 3 11 :=
  { regWires := exARegWires }

/--
Initial global state (indices 0..10):

  R0 (dst)   on [0,1]       = "10"    = 2
  R1 (src)   on [2..6]      = "10101" = 21
  R2 (carry) on [7,8,9]     = "000"   = 0
  wire 10                = 0
-/
def exAInitState : BitState 11
| 0  => true    -- R0: "10"
| 1  => false
| 2  => true    -- R1: "10101"
| 3  => false
| 4  => true
| 5  => false
| 6  => true
| 7  => false   -- R2: "000"
| 8  => false
| 9  => false
| 10 => false   -- unused

/-- Bundle into a `RegState`. -/
def exARegState : RegState 3 11 :=
  { layout := exALayout, σ := exAInitState }

/-- Names: dst = 0, src = 1, carry = 2. -/
def exADst   : Fin 3 := ⟨0, by decide⟩
def exASrc   : Fin 3 := ⟨1, by decide⟩
def exACarry : Fin 3 := ⟨2, by decide⟩

/-- Length of combined destination word `carry ++ dst` ≤ NExA. -/
lemma exA_len_comb :
  (exARegState.layout.regWires exACarry ++ exARegState.layout.regWires exADst).length ≤ 11 := by
  simp [exARegState, exALayout, exARegWires, exACarry, exADst]

/-- Length of src word ≤ NExA. -/
lemma exA_len_src :
  (exARegState.layout.regWires exASrc).length ≤ 11 := by
  simp [exARegState, exALayout, exARegWires, exASrc]

/--
Combined destination `carry ++ dst` is disjoint from src.

 carry ++ dst = [7,8,9,0,1]
 src          = [2,3,4,5,6]
-/
lemma exA_disj_comb_src :
  wiresDisjoint
    (exARegState.layout.regWires exACarry ++ exARegState.layout.regWires exADst)
    (exARegState.layout.regWires exASrc) := by
  intro q hcomb hsrc
  simp [exARegState, exALayout, exARegWires, exACarry, exADst, exASrc] at hcomb hsrc
  aesop


def exAAfterAddWithCarry : RegState 3 11 :=
  RegState.addWithCarryReg
    exARegState
    exADst exASrc exACarry
    exA_len_comb exA_len_src exA_disj_comb_src

#eval exARegState.showPretty
#eval exAAfterAddWithCarry.showPretty


/-
############################################################
# Example B: dst width 3, src width 6 (truncation), carry width 2
############################################################
-/

def kExB : ℕ := 3
def NExB : ℕ := 11

/-- Wires for each register (MSB-first). -/
def exBRegWires : Fin 3 → List (Fin 11)
| 0 => [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩]            -- R0: dst, 3 bits
| 1 => [⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩,
        ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩]            -- R1: src, 6 bits
| 2 => [⟨9, by decide⟩, ⟨10, by decide⟩]                           -- R2: carry, 2 bits

def exBLayout : RegLayout 3 11 :=
  { regWires := exBRegWires }

/--
Initial state:

  R0 on [0,1,2]   = "101"    = 5
  R1 on [3..8]    = "111011" = 59
  R2 on [9,10]    = "00"     = 0
-/
def exBInitState : BitState 11
| 0  => true    -- R0: "101"
| 1  => false
| 2  => true
| 3  => true    -- R1: "111011"
| 4  => true
| 5  => true
| 6  => false
| 7  => true
| 8  => true
| 9  => false   -- R2: "00"
| 10 => false

def exBRegState : RegState 3 11 :=
  { layout := exBLayout, σ := exBInitState }

/-- Names. -/
def exBDst   : Fin kExB := ⟨0, by decide⟩
def exBSrc   : Fin kExB := ⟨1, by decide⟩
def exBCarry : Fin kExB := ⟨2, by decide⟩

/-- Length of combined dest `carry ++ dst` ≤ NExB. -/
lemma exB_len_comb :
  (exBRegState.layout.regWires exBCarry ++ exBRegState.layout.regWires exBDst).length ≤ NExB := by
  simp [exBRegState, exBLayout, exBRegWires, exBCarry, exBDst, NExB]

/-- Length of src word ≤ NExB. -/
lemma exB_len_src :
  (exBRegState.layout.regWires exBSrc).length ≤ NExB := by
  simp [exBRegState, exBLayout, exBRegWires, exBSrc, NExB]

/--
Disjointness: (carry ++ dst) vs src.

  carry ++ dst = [9,10,0,1,2]
  src          = [3,4,5,6,7,8]
-/
lemma exB_disj_comb_src :
  wiresDisjoint
    (exBRegState.layout.regWires exBCarry ++ exBRegState.layout.regWires exBDst)
    (exBRegState.layout.regWires exBSrc) := by
  intro q hcomb hsrc
  simp [exBRegState, exBLayout, exBRegWires, exBCarry, exBDst, exBSrc] at hcomb hsrc
  aesop

/--
Run:

  combined := carry ++ dst   (2 + 3 = 5 bits)
  combined ← combined + src  (LSB-aligned, src has 6 bits)

Here:

  carry ++ dst = "00" ++ "101" = "00101" = 5
  src          = "111011" → truncated to last 5 bits "11011" = 27

So we get 5 + 27 = 32 ≡ 0 (mod 2^5), i.e. "00000" on the 5 wires.

`dst` now owns those 5 wires, `carry` becomes empty.
-/
def exBAfterAddWithCarry : RegState kExB NExB :=
  RegState.addWithCarryReg
    exBRegState
    exBDst exBSrc exBCarry
    exB_len_comb exB_len_src exB_disj_comb_src

#eval exBRegState.showPretty
#eval exBAfterAddWithCarry.showPretty
