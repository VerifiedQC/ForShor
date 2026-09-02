import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.Data.Nat.Bitwise

/-!
# Shor verification core — physical registers

This file is the minimal register-definition layer used by the Shor
verification:

* ordered physical registers and logical split/append operations;
* the basis-level encoding interface;
* extendable registers with inactive reserve bits;
* two's-complement and signed-width definitions.

Derived register laws and proof helpers live in
`Implementation/RegisterLemmas.lean`; Framework does not import them.
-/

universe u

namespace Shor

/-! =========================================================
    Section 1: Ordered physical registers

    A `Reg` is an ordered, duplicate-free list of physical qubits. The order is
    the logical bit order used by `toNat`, `writeNat`, and all later arithmetic
    semantics.
========================================================= -/

/--
An ordered collection of distinct physical qubits.

The order is logical: the qubit at position `i` represents bit `i`.
Physical contiguity is not required.
-/
structure Reg where
  qubits : List ℕ
  nodup  : qubits.Nodup
deriving DecidableEq

namespace Reg

/-! ### Basic constructors and slices -/

/-- The empty register. -/
def empty : Reg := ⟨[], by simp⟩

/-- Logical width, i.e. the number of physical qubits in the ordered list. -/
def width (r : Reg) : ℕ := r.qubits.length

/-- Membership of a physical qubit in a register. -/
def contains (r : Reg) (q : ℕ) : Prop := q ∈ r.qubits

/-- The physical qubit used for logical bit `i`. -/
def get (r : Reg) (i : Fin r.width) : ℕ := r.qubits.get ⟨i.1, by simp [width]⟩

/-- A single-qubit register. -/
def singleton (q : ℕ) : Reg := ⟨[q], by simp⟩

/-- Construct the old contiguous interval `[lo, lo + size)`. -/
def interval (lo size : ℕ) : Reg :=
  {
    qubits := (List.range size).map (fun i => lo + i)
    nodup := by
      induction size with
      |zero =>  simp
      | succ n ih =>
        simp[List.range_succ, List.map_append, List.nodup_append, ih]
        intro a ha
        omega
  }

/-- The first `n` logical qubits. -/
def take (r : Reg) (n : ℕ) : Reg :=
  {
    qubits := r.qubits.take n
    nodup := r.nodup.sublist (List.take_sublist n r.qubits)
  }

/-- The logical qubits following the first `n`. -/
def drop (r : Reg) (n : ℕ) : Reg :=
  {
    qubits := r.qubits.drop n
    nodup := r.nodup.sublist (List.drop_sublist n r.qubits)
  }

end Reg

/-! ### Compatibility aliases and register combinators -/

/-- Alias used by older Shor files for the logical width of a register. -/
def regSize (r : Reg) : ℕ := r.width

/-- Cardinality of the computational basis supported by a register. -/
def ASize (r : Reg) : ℕ := 2 ^ regSize r

/-- Ordered physical qubits of a register. -/
def regQubits (r : Reg) : List ℕ := r.qubits

/-- A one-qubit register at physical qubit `q`. -/
def qubitReg (q : ℕ) : Reg := Reg.singleton q

/-- Physical disjointness of two ordered registers. -/
def Disjoint (a b : Reg) : Prop := a.qubits.Disjoint b.qubits

namespace Reg

/-- Append two physically disjoint registers, preserving logical order. -/
def append
    (left right : Reg)
    (h : Disjoint left right) :
    Reg :=
  {
    qubits := left.qubits ++ right.qubits
    nodup := by
      exact List.Nodup.append left.nodup right.nodup h
  }

end Reg

/-- A legal split point for a register. -/
abbrev SplitPoint (r : Reg) := { n : ℕ // n ≤ regSize r }

/-- Prefix side of a logical split. -/
def splitLeft (r : Reg) (m : SplitPoint r) : Reg := r.take m.1

/-- Suffix side of a logical split. -/
def splitRight (r : Reg) (m : SplitPoint r) : Reg := r.drop m.1

/-- The least-significant physical qubit of a nonempty ordered register. -/
def Reg.lowQubit (r : Reg) (h : 0 < regSize r) : ℕ :=
  r.qubits.get ⟨0, by simpa [regSize, Reg.width] using h⟩

/-! =========================================================
    Section 2: Basis encodings for registers

    `RegEncoding` is intentionally small. It provides primitive read/write
    behavior and bit observations; the larger derived algebra lives on the
    Implementation side.
========================================================= -/

/--
`RegEncoding` is the basis-level interface for ordinary finite registers.
It specifies reads, writes, bit observations, register extensionality, and
split/register-locality laws used throughout later semantic proofs.
-/
class RegEncoding (Basis : Type u) where
  toNat    : Reg → Basis → ℕ
  writeNat : Reg → ℕ → Basis → Basis
  bit      : ℕ → Basis → Bool

  /-- The canonical ground basis state: every qubit is |0⟩.  This is the fixed,
  clean initial state the Shor specification is judged against — the qubit
  analogue of an empty EVM memory.  Any concrete register model supplies it as
  its physical all-zeros state, so it costs no global axiom. -/
  zero     : Basis
  /-- Every qubit of the ground state reads `0`. -/
  bit_zero : ∀ q, bit q zero = false

  toNat_writeNat_of_lt :
    ∀ r v b,
      v < ASize r →
      toNat r (writeNat r v b) = v

  toNat_lt_ASize :
    ∀ r b,
      toNat r b < ASize r

  basis_ext :
    ∀ b1 b2 : Basis,
      (∀ q, bit q b1 = bit q b2) → b1 = b2

  bit_writeNat_in :
    ∀ r v b₁ b₂ q,
      q ∈ r.qubits →
      bit q (writeNat r v b₁) =
        bit q (writeNat r v b₂)

  bit_writeNat_out :
    ∀ r v b q,
      q ∉ r.qubits →
      bit q (writeNat r v b) = bit q b

  bit_eq_testBit_toNat :
    ∀ (r : Reg) (b : Basis) (i : Fin (regSize r)),
      bit (r.get i) b =
        Nat.testBit (toNat r b) i.1

/-! =========================================================
    Section 3: Extendable physical registers

    `ExtReg` packages an active register with an ordered reserve. Growth moves
    a prefix of the reserve into the active part while preserving physical
    disjointness.
========================================================= -/

/--
An active register together with exclusively owned inactive workspace.

`reserve` is ordered from the next high bit onward.
-/
structure ExtReg where
  active  : Reg
  reserve : Reg
  active_reserve_disjoint :
    Disjoint active reserve
deriving DecidableEq

namespace ExtReg

/-! ### Constructors and reserve accounting -/

/-- Treat an ordinary register as an extendable register with no reserve. -/
def ofReg (r : Reg) : ExtReg := { active := r, reserve := Reg.empty, active_reserve_disjoint := by simp [Disjoint, Reg.empty] }

/-- Build an extendable register from an active part and owned reserve qubits. -/
def withReserve (active reserve : Reg) (h : Disjoint active reserve) : ExtReg := ⟨active, reserve, h⟩

/-- Width of the currently active part. -/
def width (e : ExtReg) : ℕ := regSize e.active

/-- Number of reserve bits still available for future growth. -/
def capacity (e : ExtReg) : ℕ := regSize e.reserve

/-- The reserve has at least `n` bits available. -/
def CanGrow (e : ExtReg) (n : ℕ) : Prop := n ≤ e.capacity

/-- The next `n` reserve bits that will become active after growth. -/
def newBits (e : ExtReg) (n : ℕ) : Reg := e.reserve.take n

/-- Reserve bits left after growing by `n`. -/
def remainingReserve (e : ExtReg) (n : ℕ) : Reg := e.reserve.drop n

end ExtReg
namespace ExtReg

/-- Activate the next `n` reserve qubits, leaving the remaining reserve inactive. -/
def grow (e : ExtReg) (n : ℕ) : ExtReg :=
  {
    active :=
      Reg.append e.active (e.newBits n) (by
        have hdisj := e.active_reserve_disjoint
        rw [Disjoint, List.disjoint_left] at hdisj ⊢
        intro q hqActive hqNew
        exact hdisj hqActive
          (List.mem_of_mem_take hqNew))

    reserve :=
      e.remainingReserve n

    active_reserve_disjoint := by
      rw [Disjoint, List.disjoint_left]
      intro q hqActiveGrow hqReserve
      rw [ExtReg.remainingReserve, Reg.drop] at hqReserve
      rw [Reg.append, List.mem_append] at hqActiveGrow
      rcases hqActiveGrow with hqActive | hqNew
      · have hdisj := e.active_reserve_disjoint
        rw [Disjoint, List.disjoint_left] at hdisj
        exact hdisj hqActive
          (List.mem_of_mem_drop hqReserve)
      · have htake_drop :
            (List.take n e.reserve.qubits).Disjoint
              (List.drop n e.reserve.qubits) :=
          List.disjoint_take_drop e.reserve.nodup (le_refl n)
        rw [List.disjoint_left] at htake_drop
        exact htake_drop hqNew hqReserve
  }

/-- All physical qubits owned by an extendable register, active first and reserve second. -/
def ownedQubits (e : ExtReg) : List ℕ := e.active.qubits ++ e.reserve.qubits

/-- Disjointness of the currently active portions only. -/
def ActiveDisjoint (x z : ExtReg) : Prop := Disjoint x.active z.active

/-- Disjointness of all owned qubits, including reserve/workspace bits. -/
def OwnedDisjoint (x z : ExtReg) : Prop := x.ownedQubits.Disjoint z.ownedQubits

/-- A control qubit is outside both active data and reserved workspace. -/
def CtrlDisjoint (ctrl : ℕ) (x z : ExtReg) : Prop := ctrl ∉ x.ownedQubits ∧ ctrl ∉ z.ownedQubits

end ExtReg

/-! =========================================================
    Section 4: Register values and freshness predicates

    These definitions interpret active register bits as unsigned or
    two's-complement integers and name the clean-reserve predicates used by
    allocation/growth semantics.
========================================================= -/

/-- Width-based two's-complement decoding. -/
def tcDecodeWidth : ℕ → ℕ → ℤ
  | 0, _ => 0
  | w + 1, n =>
      if _h : n < 2^w then
        (n : ℤ)
      else
        (n : ℤ) - ((2^(w + 1) : ℕ) : ℤ)

def ExtReg.toNat
    {Basis : Type u}
    [RegEncoding Basis]
    (e : ExtReg) (b : Basis) : ℕ :=
  RegEncoding.toNat e.active b

def extToInt
    {Basis : Type u}
    [RegEncoding Basis]
    (e : ExtReg) (b : Basis) : ℤ :=
  tcDecodeWidth e.width (e.toNat b)

def FreshZero
    {Basis : Type u}
    [RegEncoding Basis]
    (r : Reg) (b : Basis) : Prop :=
  RegEncoding.toNat r b = 0

namespace ExtReg

def FreshFor
    {Basis : Type u}
    [RegEncoding Basis]
    (e : ExtReg)
    (n : ℕ)
    (b : Basis) : Prop :=
  FreshZero (e.newBits n) b

end ExtReg

/-! =========================================================
    Section 5: Signed two's-complement arithmetic
========================================================= -/

/-!
These pure arithmetic helpers define how finite bit patterns are interpreted as
signed integers. They sit before the gate language because phase-product and
arithmetic gate semantics refer to `extToInt`, wrapping, and signed-fit facts.
-/

/-- Reduction of an integer modulo the unsigned `w`-bit modulus. -/
def tcModWidth (w : ℕ) (z : ℤ) : ℕ := Int.toNat (z % ((2^w : ℕ) : ℤ))

/-- Wrap an integer to `w` bits and decode the result as two's-complement. -/
def tcWrapInt (w : ℕ) (z : ℤ) : ℤ := tcDecodeWidth w (tcModWidth w z)

/-- Inclusive lower endpoint of the signed `w`-bit range. -/
def signedLo (w : ℕ) : ℤ := -(((2^(w-1) : ℕ) : ℤ))

/-- Exclusive upper endpoint of the signed `w`-bit range. -/
def signedHi (w : ℕ) : ℤ := (((2^(w-1) : ℕ) : ℤ))

/-- Modulo reduction using the active width of an extendable register. -/
def tcModExt (e : ExtReg) (z : ℤ) : ℕ := tcModWidth (ExtReg.width e) z

/-- Inclusive lower endpoint of the signed `w`-bit range; canonical name used by proofs. -/
def signedMin (w : ℕ) : ℤ := -(((2^(w-1) : ℕ) : ℤ))

/-- Exclusive upper endpoint of the signed `w`-bit two's-complement range. -/
def signedMax (w : ℕ) : ℤ := (((2^(w-1) : ℕ) : ℤ))

/-- Predicate saying `z` fits in signed `w`-bit range. -/
def FitsSignedWidth (w : ℕ) (z : ℤ) : Prop :=
  0 < w ∧ signedMin w ≤ z ∧ z < signedMax w


end Shor
