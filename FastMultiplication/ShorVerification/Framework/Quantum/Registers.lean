import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.Data.Nat.Bitwise

/-!
# Shor verification core — physical registers

This file defines the register layer used by the rest of the Shor
verification:

* ordered physical registers and logical split/append operations;
* the minimal basis-level encoding interface;
* derived register-write/read laws proved from bit-level semantics;
* extendable registers with inactive reserve bits;
* two's-complement decoding and signed-width arithmetic helpers.
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

/-! ### Register combinators -/

/-- Cardinality of the computational basis supported by a register. -/
def ASize (r : Reg) : ℕ := 2 ^ Reg.width r

/-- Ordered physical qubits of a register. -/
def regQubits (r : Reg) : List ℕ := r.qubits

/-- A one-qubit register at physical qubit `q`. -/
def qubitReg (q : ℕ) : Reg := Reg.singleton q

/-- Physical disjointness of two ordered registers. -/
def Disjoint (a b : Reg) : Prop := a.qubits.Disjoint b.qubits

theorem Disjoint.symm {a b : Reg} :
    Disjoint a b → Disjoint b a := by
  intro h
  exact List.Disjoint.symm h

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
abbrev SplitPoint (r : Reg) := { n : ℕ // n ≤ Reg.width r }

/-- Prefix side of a logical split. -/
def splitLeft (r : Reg) (m : SplitPoint r) : Reg := r.take m.1

/-- Suffix side of a logical split. -/
def splitRight (r : Reg) (m : SplitPoint r) : Reg := r.drop m.1

@[simp] theorem width_empty :
    Reg.width Reg.empty = 0 := by
  rfl

@[simp] theorem width_singleton (q : ℕ) :
    Reg.width (qubitReg q) = 1 := by
  rfl

@[simp] theorem splitLeft_size
    (r : Reg) (m : SplitPoint r) :
    Reg.width (splitLeft r m) = m.1 := by
  have hm:=m.2
  simp [splitLeft, Reg.take, Reg.width] at *
  simp[hm]

@[simp] theorem splitRight_size
    (r : Reg) (m : SplitPoint r) :
    Reg.width (splitRight r m) = Reg.width r - m.1 := by
  simp [splitRight, Reg.drop, Reg.width]

theorem splitLeft_splitRight_disjoint
    (r : Reg) (m : SplitPoint r) :
    Disjoint (splitLeft r m) (splitRight r m) := by
  simpa [Disjoint, splitLeft, splitRight, Reg.take, Reg.drop] using
    List.disjoint_take_drop r.nodup (le_refl m.1)

/-- The least-significant physical qubit of a nonempty ordered register. -/
def Reg.lowQubit (r : Reg) (h : 0 < Reg.width r) : ℕ :=
  r.qubits.get ⟨0, by simpa [Reg.width] using h⟩

/-! =========================================================
    Section 2: Basis encodings for registers

    `RegEncoding` is intentionally small. It provides primitive read/write
    behavior, bit observations, and enough bit-level agreement to derive the
    larger register algebra below.
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
    ∀ (r : Reg) (b : Basis) (i : Fin (Reg.width r)),
      bit (r.get i) b =
        Nat.testBit (toNat r b) i.1

/-! =========================================================
    Section 3: Derived register encoding laws

    The following facts used to be tempting class fields. They are derived once
    here from the smaller bit-level interface: split writes, disjoint-write
    commutation, write-read roundtrips, and append/split read formulas.
========================================================= -/

/-- Appending the two halves of a split reconstructs the original register. -/
theorem append_split_eq
    (r : Reg) (m : SplitPoint r) :
    Reg.append
        (splitLeft r m)
        (splitRight r m)
        (splitLeft_splitRight_disjoint r m) = r := by
  cases r with
  | mk qubits nodup =>
      cases m with
      | mk n hn =>
          simp [
            Reg.append,
            splitLeft,
            splitRight,
            Reg.take,
            Reg.drop
          ]

namespace RegEncoding

/-! ### Bit-level helpers for split writes -/

theorem bit_writeNat_of_lt
    {Basis : Type u} [RegEncoding Basis]
    (r : Reg) (v : ℕ) (b : Basis)
    (hv : v < ASize r)
    (i : Fin (Reg.width r)) :
    RegEncoding.bit (r.get i)
        (RegEncoding.writeNat r v b) =
      Nat.testBit v i.1 := by
  rw [RegEncoding.bit_eq_testBit_toNat]
  rw [RegEncoding.toNat_writeNat_of_lt r v b hv]

theorem splitLeft_get
    (r : Reg) (m : SplitPoint r)
    (i : Fin (Reg.width (splitLeft r m))) :
    (splitLeft r m).get i =
      r.get ⟨i.1, by
        have hi := i.2
        simp [splitLeft_size] at hi
        exact lt_of_lt_of_le hi m.2⟩ := by
  simp [
    splitLeft,
    Reg.take,
    Reg.get,
    Reg.width
  ]

theorem splitRight_get
    (r : Reg) (m : SplitPoint r)
    (i : Fin (Reg.width (splitRight r m))) :
    (splitRight r m).get i =
      r.get ⟨m.1 + i.1, by
        have hi := i.2
        have hi' : i.1 < Reg.width r - m.1 := by
          simpa [splitRight_size] using hi
        have hbound : m.1 + i.1 < Reg.width r := by
          omega
        simpa [Reg.width] using hbound⟩ := by
  simp [
    splitRight,
    Reg.drop,
    Reg.get,
    Reg.width
  ]

theorem testBit_join
    {m low high j : ℕ}
    (hlow : low < 2 ^ m) :
    Nat.testBit (low + 2 ^ m * high) j =
      if j < m then
        Nat.testBit low j
      else
        Nat.testBit high (j - m) := by
  simpa [Nat.add_comm] using
    Nat.testBit_two_pow_mul_add high hlow j

/--
Writing a combined value to a parent register is the same as writing the low
part to the left split and the high part to the right split.
-/
theorem writeNat_split
    {Basis : Type u} [RegEncoding Basis]
    (r : Reg) (m : SplitPoint r)
    (high low : ℕ) (b : Basis)
    (hlow : low < ASize (splitLeft r m))
    (hhigh : high < ASize (splitRight r m)) :
    RegEncoding.writeNat r
        (low + ASize (splitLeft r m) * high) b =
      RegEncoding.writeNat (splitRight r m) high
        (RegEncoding.writeNat (splitLeft r m) low b) := by

  let left := splitLeft r m
  let right := splitRight r m

  have hdisj : Disjoint left right := by
    exact splitLeft_splitRight_disjoint r m

  have hmwidth :
      Reg.width left = m.1 := by
    simp [left]

  have hjoined :
      low + ASize left * high < ASize r := by
    have hsizes :
        Reg.width left + Reg.width right = Reg.width r := by
      simp [left, right]
      omega

    have hASize :
        ASize r = ASize left * ASize right := by
      unfold ASize
      rw [← hsizes, pow_add]

    rw [hASize]

    calc
      low + ASize left * high
          < ASize left + ASize left * high := by
              exact Nat.add_lt_add_right hlow _
      _ = ASize left * (high + 1) := by
              ring
      _ ≤ ASize left * ASize right := by
              exact Nat.mul_le_mul_left _
                (Nat.succ_le_of_lt hhigh)

  apply RegEncoding.basis_ext
  intro q
  by_cases hqL : q ∈ left.qubits
  · obtain ⟨i, hi⟩ := List.get_of_mem hqL
    have hqR : q ∉ right.qubits := by
      intro h
      exact hdisj hqL h

    obtain ⟨i, hi⟩ := List.get_of_mem hqL

    let iL : Fin (Reg.width left) :=
      ⟨i.1, by
        simp [left, Reg.width]⟩

    have hgetL : left.get iL = q := by
      simpa [iL, Reg.get, Reg.width] using hi

    let iWhole : Fin (Reg.width r) :=
      ⟨iL.1, by
        have hi' : iL.1 < m.1 := by
          simpa [left] using iL.2
        exact lt_of_lt_of_le hi' m.2⟩

    have hgetWhole : r.get iWhole = q := by
      rw [← hgetL]
      exact (splitLeft_get r m iL).symm

    calc
      RegEncoding.bit q
          (RegEncoding.writeNat r
            (low + ASize left * high) b)
          =
        Nat.testBit
          (low + ASize left * high)
          iWhole.1 := by
            rw [← hgetWhole]
            exact RegEncoding.bit_writeNat_of_lt
              r _ b hjoined iWhole

      _ = Nat.testBit low iL.1 := by
            have hi : iL.1 < Reg.width left := iL.2
            rw [ASize]
            have h :=
              Nat.testBit_two_pow_mul_add
                high
                (by simpa [ASize] using hlow)
                iL.1
            simp [Nat.add_comm] at h
            rename_i hi_1 hi_2
            subst hi_1
            simp_all only [splitLeft_size, Fin.eta, ↓reduceIte, List.get_eq_getElem, List.getElem_mem, left, right, iL, iWhole]

      _ =
        RegEncoding.bit q
          (RegEncoding.writeNat left low b) := by
            rw [← hgetL]
            symm
            exact RegEncoding.bit_writeNat_of_lt
              left low b hlow iL

      _ =
        RegEncoding.bit q
          (RegEncoding.writeNat right high
            (RegEncoding.writeNat left low b)) := by
            symm
            exact RegEncoding.bit_writeNat_out
              right high
              (RegEncoding.writeNat left low b)
              q hqR
  · by_cases hqR : q ∈ right.qubits
    · obtain ⟨j, hj⟩ := List.get_of_mem hqR

      let jR : Fin (Reg.width right) :=
        ⟨j.1, by
          simp[right, Reg.width]⟩

      have hgetR : right.get jR = q := by
        simpa [jR, Reg.get, Reg.width] using hj

      let jWhole : Fin (Reg.width r) :=
        ⟨m.1 + jR.1, by
          have hj' := jR.2
          simp [right] at hj'
          omega⟩

      have hgetWhole : r.get jWhole = q := by
        rw [← hgetR]
        exact (splitRight_get r m jR).symm
      calc
        RegEncoding.bit q
            (RegEncoding.writeNat r
              (low + ASize left * high) b)
            =
          Nat.testBit
            (low + ASize left * high)
            jWhole.1 := by
              rw [← hgetWhole]
              exact RegEncoding.bit_writeNat_of_lt
                r _ b hjoined jWhole

        _ = Nat.testBit high jR.1 := by
              have h :=
                Nat.testBit_two_pow_mul_add
                  high
                  (by
                    simpa [ASize, left] using hlow)
                  (m.1 + jR.1)

              simp [left, ASize, jWhole, Nat.not_lt.mpr (Nat.le_add_right _ _)] at *
              rw[← h, add_comm]

        _ =
          RegEncoding.bit q
            (RegEncoding.writeNat right high
              (RegEncoding.writeNat left low b)) := by
              rw [← hgetR]
              symm
              exact RegEncoding.bit_writeNat_of_lt
                right high
                (RegEncoding.writeNat left low b)
                hhigh jR
    · have hqr : q ∉ r.qubits := by
        intro h
        have : q ∈ left.qubits ∨ q ∈ right.qubits := by
          have hsplit :
              q ∈ r.qubits.take m.1 ++ r.qubits.drop m.1 := by
            simpa [List.take_append_drop m.1 r.qubits] using h
          rcases List.mem_append.mp hsplit with hleft | hright
          · left
            simpa [left, splitLeft, Reg.take] using hleft
          · right
            simpa [right, splitRight, Reg.drop] using hright
        exact this.elim hqL hqR

      calc
        RegEncoding.bit q
            (RegEncoding.writeNat r
              (low + ASize left * high) b)
            = RegEncoding.bit q b := by
                exact RegEncoding.bit_writeNat_out
                  r _ b q hqr

        _ =
          RegEncoding.bit q
            (RegEncoding.writeNat left low b) := by
                symm
                exact RegEncoding.bit_writeNat_out
                  left low b q hqL

        _ =
          RegEncoding.bit q
            (RegEncoding.writeNat right high
              (RegEncoding.writeNat left low b)) := by
                symm
                exact RegEncoding.bit_writeNat_out
                  right high
                  (RegEncoding.writeNat left low b)
                  q hqR


/-! ### Disjoint writes and write/read roundtrips -/

theorem writeNat_comm_of_disjoint
    {Basis : Type u} [RegEncoding Basis]
    (left right : Reg)
    (hdisj : Disjoint left right)
    (yL yR : ℕ)
    (b : Basis) :
    RegEncoding.writeNat left yL
        (RegEncoding.writeNat right yR b) =
      RegEncoding.writeNat right yR
        (RegEncoding.writeNat left yL b) := by
  apply RegEncoding.basis_ext
  intro q

  have hd := hdisj
  rw [Disjoint, List.disjoint_left] at hd

  by_cases hqL : q ∈ left.qubits
  · have hqR : q ∉ right.qubits := by
      intro h
      exact hd hqL h

    calc
      RegEncoding.bit q
          (RegEncoding.writeNat left yL
            (RegEncoding.writeNat right yR b))
          =
        RegEncoding.bit q
          (RegEncoding.writeNat left yL b) := by
            exact RegEncoding.bit_writeNat_in
              left yL
              (RegEncoding.writeNat right yR b)
              b q hqL

      _ =
        RegEncoding.bit q
          (RegEncoding.writeNat right yR
            (RegEncoding.writeNat left yL b)) := by
            symm
            exact RegEncoding.bit_writeNat_out
              right yR
              (RegEncoding.writeNat left yL b)
              q hqR

  · by_cases hqR : q ∈ right.qubits
    · calc
        RegEncoding.bit q
            (RegEncoding.writeNat left yL
              (RegEncoding.writeNat right yR b))
            =
          RegEncoding.bit q
            (RegEncoding.writeNat right yR b) := by
              exact RegEncoding.bit_writeNat_out
                left yL
                (RegEncoding.writeNat right yR b)
                q hqL

        _ =
          RegEncoding.bit q
            (RegEncoding.writeNat right yR
              (RegEncoding.writeNat left yL b)) := by
              exact RegEncoding.bit_writeNat_in
                right yR
                b
                (RegEncoding.writeNat left yL b)
                q hqR

    · calc
        RegEncoding.bit q
            (RegEncoding.writeNat left yL
              (RegEncoding.writeNat right yR b))
            =
          RegEncoding.bit q
            (RegEncoding.writeNat right yR b) := by
              exact RegEncoding.bit_writeNat_out
                left yL
                (RegEncoding.writeNat right yR b)
                q hqL

        _ = RegEncoding.bit q b := by
              exact RegEncoding.bit_writeNat_out
                right yR b q hqR

        _ =
          RegEncoding.bit q
            (RegEncoding.writeNat left yL b) := by
              symm
              exact RegEncoding.bit_writeNat_out
                left yL b q hqL

        _ =
          RegEncoding.bit q
            (RegEncoding.writeNat right yR
              (RegEncoding.writeNat left yL b)) := by
              symm
              exact RegEncoding.bit_writeNat_out
                right yR
                (RegEncoding.writeNat left yL b)
                q hqR

theorem writeNat_toNat
    {Basis : Type u} [RegEncoding Basis]
    (r : Reg) (b : Basis) :
    RegEncoding.writeNat r (RegEncoding.toNat r b) b = b := by
  apply RegEncoding.basis_ext
  intro q

  by_cases hq : q ∈ r.qubits
  · -- Since q is in r, it occurs at some logical position i.
    have hex :
        ∃ i : Fin r.qubits.length,
          r.qubits.get i = q := by
      exact List.get_of_mem hq

    obtain ⟨i, hi⟩ := hex

    let j : Fin (Reg.width r) :=
      ⟨i.1, by
        simp [Reg.width]⟩

    have hj : r.get j = q := by
      simpa [Reg.get, j, Reg.width] using hi

    have hread :
        RegEncoding.toNat r
            (RegEncoding.writeNat r (RegEncoding.toNat r b) b) =
          RegEncoding.toNat r b := by
      apply RegEncoding.toNat_writeNat_of_lt
      exact RegEncoding.toNat_lt_ASize r b

    calc
      RegEncoding.bit q
          (RegEncoding.writeNat r (RegEncoding.toNat r b) b)
          =
        RegEncoding.bit (r.get j)
          (RegEncoding.writeNat r (RegEncoding.toNat r b) b) := by
            rw [hj]

      _ =
        Nat.testBit
          (RegEncoding.toNat r
            (RegEncoding.writeNat r (RegEncoding.toNat r b) b))
          j.1 :=
            RegEncoding.bit_eq_testBit_toNat
              r
              (RegEncoding.writeNat r (RegEncoding.toNat r b) b)
              j

      _ =
        Nat.testBit (RegEncoding.toNat r b) j.1 := by
            rw [hread]

      _ =
        RegEncoding.bit (r.get j) b := by
            symm
            exact RegEncoding.bit_eq_testBit_toNat r b j

      _ = RegEncoding.bit q b := by
            rw [hj]

  · exact
      RegEncoding.bit_writeNat_out
        r (RegEncoding.toNat r b) b q hq


theorem toNat_left_write_right
    {Basis : Type u} [RegEncoding Basis]
    (left right : Reg)
    (hdisj : Disjoint left right)
    (b : Basis)
    (yR : ℕ) :
    RegEncoding.toNat left
        (RegEncoding.writeNat right yR b) =
      RegEncoding.toNat left b := by

  have hlt :
      RegEncoding.toNat left b < ASize left :=
    RegEncoding.toNat_lt_ASize left b

  have hcomm :=
    RegEncoding.writeNat_comm_of_disjoint
      left right hdisj
      (RegEncoding.toNat left b) yR b

  rw [RegEncoding.writeNat_toNat left b] at hcomm

  have hread :=
    congrArg (RegEncoding.toNat left) hcomm

  have hwritten :
      RegEncoding.toNat left
          (RegEncoding.writeNat left
            (RegEncoding.toNat left b)
            (RegEncoding.writeNat right yR b))
        =
      RegEncoding.toNat left b :=
    RegEncoding.toNat_writeNat_of_lt
      left
      (RegEncoding.toNat left b)
      (RegEncoding.writeNat right yR b)
      hlt

  exact hread.symm.trans hwritten

theorem toNat_right_write_left
    {Basis : Type u} [RegEncoding Basis]
    (left right : Reg)
    (hdisj : Disjoint left right)
    (b : Basis)
    (yL : ℕ) :
    RegEncoding.toNat right
        (RegEncoding.writeNat left yL b) =
      RegEncoding.toNat right b := by
  exact
    RegEncoding.toNat_left_write_right
      right left (Disjoint.symm hdisj) b yL

/-! ### Append and split read formulas -/

@[simp] theorem splitLeft_append
    (left right : Reg)
    (hdisj : Disjoint left right) :
  splitLeft
      (Reg.append left right hdisj)
      ⟨Reg.width left, by
        simp [Reg.width, Reg.append]⟩ =
    left := by
  cases left with
  | mk leftQubits leftNodup =>
      cases right with
      | mk rightQubits rightNodup =>
          simp [
            splitLeft,
            Reg.take,
            Reg.append,
            Reg.width
          ]

@[simp] theorem splitRight_append
    (left right : Reg)
    (hdisj : Disjoint left right) :
  splitRight
      (Reg.append left right hdisj)
      ⟨Reg.width left, by
        simp [Reg.width, Reg.append]⟩ =
    right := by
  cases left with
  | mk leftQubits leftNodup =>
      cases right with
      | mk rightQubits rightNodup =>
          simp [
            splitRight,
            Reg.drop,
            Reg.append,
            Reg.width
          ]

theorem toNat_append
    {Basis : Type u} [RegEncoding Basis]
    (left right : Reg)
    (hdisj : Disjoint left right)
    (b : Basis) :
    RegEncoding.toNat (Reg.append left right hdisj) b =
      RegEncoding.toNat left b +
        ASize left * RegEncoding.toNat right b := by

  let r := Reg.append left right hdisj

  let m : SplitPoint r :=
    ⟨Reg.width left, by
      simp [r, Reg.width, Reg.append]⟩

  have hleft :
      splitLeft r m = left := by
    dsimp [r, m]
    simp

  have hright :
      splitRight r m = right := by
    dsimp [r, m]
    simp

  have hlow :
      RegEncoding.toNat left b < ASize left :=
    RegEncoding.toNat_lt_ASize left b

  have hhigh :
      RegEncoding.toNat right b < ASize right :=
    RegEncoding.toNat_lt_ASize right b

  have hsize :
      ASize r = ASize left * ASize right := by
    simp [r, ASize, Reg.width, Reg.append, pow_add]

  have hcombined :
      RegEncoding.toNat left b +
          ASize left * RegEncoding.toNat right b <
        ASize r := by
    rw [hsize]
    calc
      RegEncoding.toNat left b +
          ASize left * RegEncoding.toNat right b
          <
        ASize left +
          ASize left * RegEncoding.toNat right b := by
            exact Nat.add_lt_add_right hlow _

      _ =
        ASize left *
          (RegEncoding.toNat right b + 1) := by
            ring

      _ ≤ ASize left * ASize right := by
            exact Nat.mul_le_mul_left _
              (Nat.succ_le_of_lt hhigh)

  have hlow' :
      RegEncoding.toNat left b <
        ASize (splitLeft r m) := by
    simpa [hleft] using hlow

  have hhigh' :
      RegEncoding.toNat right b <
        ASize (splitRight r m) := by
    simpa [hright] using hhigh

  have hsplit :=
    RegEncoding.writeNat_split
      r m
      (RegEncoding.toNat right b)
      (RegEncoding.toNat left b)
      b
      hlow'
      hhigh'

  rw [hleft, hright] at hsplit

  have hwrite :
      RegEncoding.writeNat r
          (RegEncoding.toNat left b +
            ASize left * RegEncoding.toNat right b) b =
        b := by
    rw [RegEncoding.writeNat_toNat left b] at hsplit
    rw [RegEncoding.writeNat_toNat right b] at hsplit
    exact hsplit

  have hread :=
    RegEncoding.toNat_writeNat_of_lt
      r
      (RegEncoding.toNat left b +
        ASize left * RegEncoding.toNat right b)
      b
      hcombined

  rw [hwrite] at hread

  simpa [r] using hread


theorem toNat_split
    {Basis : Type u} [RegEncoding Basis]
    (r : Reg) (m : SplitPoint r) (b : Basis) :
    let left  : Reg := splitLeft r m
    let right : Reg := splitRight r m
    RegEncoding.toNat r b =
      RegEncoding.toNat left b +
        ASize left * RegEncoding.toNat right b := by
  dsimp

  let hdisj :=
    splitLeft_splitRight_disjoint r m

  have happ :
      Reg.append (splitLeft r m) (splitRight r m) hdisj = r := by
    exact append_split_eq r m

  have h :=
    RegEncoding.toNat_append
      (splitLeft r m)
      (splitRight r m)
      hdisj b

  simpa [happ] using h

theorem writeNat_overwrite
    {Basis : Type u}
    [RegEncoding Basis]
    (r : Reg)
    (v w : ℕ)
    (b : Basis) :
    RegEncoding.writeNat r v
        (RegEncoding.writeNat r w b) =
      RegEncoding.writeNat r v b := by
  apply RegEncoding.basis_ext
  intro q

  by_cases hq : q ∈ r.qubits

  · exact
      RegEncoding.bit_writeNat_in
        r v
        (RegEncoding.writeNat r w b)
        b q hq

  · calc
      RegEncoding.bit q
          (RegEncoding.writeNat r v
            (RegEncoding.writeNat r w b))
          =
        RegEncoding.bit q
          (RegEncoding.writeNat r w b) := by
            exact RegEncoding.bit_writeNat_out
              r v _ q hq

      _ = RegEncoding.bit q b := by
            exact RegEncoding.bit_writeNat_out
              r w b q hq

      _ =
        RegEncoding.bit q
          (RegEncoding.writeNat r v b) := by
            symm
            exact RegEncoding.bit_writeNat_out
              r v b q hq

end RegEncoding

/-! =========================================================
    Section 4: Extendable physical registers

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
def width (e : ExtReg) : ℕ := Reg.width e.active

/-- Number of reserve bits still available for future growth. -/
def capacity (e : ExtReg) : ℕ := Reg.width e.reserve

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

@[simp] theorem width_grow
    (e : ExtReg) (n : ℕ)
    (hcap : e.CanGrow n) :
    width (e.grow n) = width e + n := by
  simp [width, grow, Reg.append, newBits, Reg.take, Reg.width,
    CanGrow, capacity] at hcap ⊢
  omega

@[simp] theorem capacity_grow
    (e : ExtReg) (n : ℕ)
    (_hcap : e.CanGrow n) :
    capacity (e.grow n) = capacity e - n := by
  simp [capacity, grow, remainingReserve, Reg.drop, Reg.width]

/-- All physical qubits owned by an extendable register, active first and reserve second. -/
def ownedQubits (e : ExtReg) : List ℕ := e.active.qubits ++ e.reserve.qubits

/-- Disjointness of the currently active portions only. -/
def ActiveDisjoint (x z : ExtReg) : Prop := Disjoint x.active z.active

/-- Disjointness of all owned qubits, including reserve/workspace bits. -/
def OwnedDisjoint (x z : ExtReg) : Prop := x.ownedQubits.Disjoint z.ownedQubits

/-- A control qubit is outside both active data and reserved workspace. -/
def CtrlDisjoint (ctrl : ℕ) (x z : ExtReg) : Prop := ctrl ∉ x.ownedQubits ∧ ctrl ∉ z.ownedQubits

end ExtReg

/-- Namespace-free compatibility wrapper for commuting writes to disjoint registers. -/
lemma writeNat_comm_of_disjoint
  {Basis : Type u} [RegEncoding Basis]
  (left right : Reg) (hdisj : Disjoint left right)
  (yL yR : ℕ) (b : Basis) :
  RegEncoding.writeNat left yL (RegEncoding.writeNat right yR b)
    =
  RegEncoding.writeNat right yR (RegEncoding.writeNat left yL b) := by
  exact RegEncoding.writeNat_comm_of_disjoint left right hdisj yL yR b

/-! =========================================================
    Section 5: Register values and freshness predicates

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

@[simp] theorem ExtReg.toNat_ofReg
    {Basis : Type u}
    [RegEncoding Basis]
    (r : Reg) (b : Basis) :
    ExtReg.toNat (ExtReg.ofReg r) b =
      RegEncoding.toNat r b := by
  rfl

theorem ExtReg.toNat_lt
    {Basis : Type u}
    [RegEncoding Basis]
    (e : ExtReg) (b : Basis) :
    e.toNat b < 2 ^ e.width := by
  simpa [ExtReg.toNat, ExtReg.width, ASize] using
    RegEncoding.toNat_lt_ASize (r := e.active) (b := b)


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

variable {Basis : Type u} [RegEncoding Basis]

/-- Two's-complement decoding is injective on canonical `w`-bit representatives. -/
lemma tcDecodeWidth_inj_of_lt
  {w n1 n2 : ℕ}
  (h1 : n1 < 2 ^ w)
  (h2 : n2 < 2 ^ w)
  (h : tcDecodeWidth w n1 = tcDecodeWidth w n2) :
  n1 = n2 := by
  cases w with
  | zero =>
      have hn1 : n1 = 0 := by omega
      have hn2 : n2 = 0 := by omega
      simp[hn1, hn2]
  | succ w =>
      by_cases hs1 : n1 < 2 ^ w
      · by_cases hs2 : n2 < 2 ^ w
        · have h' : (n1 : ℤ) = (n2 : ℤ) := by
            simpa [tcDecodeWidth, hs1, hs2] using h
          exact_mod_cast h'
        · have hneg2 : tcDecodeWidth (w + 1) n2 < 0 := by
            have h2' : n2 < 2 ^ (w + 1) := h2
            simp [tcDecodeWidth, hs2]
            have : (n2 : ℤ) < (((2 ^ (w + 1)) : ℕ) : ℤ) := by
              exact_mod_cast h2'
            linarith
          have hnonneg1 : 0 ≤ tcDecodeWidth (w + 1) n1 := by
            simp [tcDecodeWidth, hs1]
          have : 0 ≤ tcDecodeWidth (w + 1) n2 := by
            simpa [h] using hnonneg1
          linarith
      · by_cases hs2 : n2 < 2 ^ w
        · have hneg1 : tcDecodeWidth (w + 1) n1 < 0 := by
            have h1' : n1 < 2 ^ (w + 1) := h1
            simp [tcDecodeWidth, hs1]
            have : (n1 : ℤ) < (((2 ^ (w + 1)) : ℕ) : ℤ) := by
              exact_mod_cast h1'
            linarith
          have hnonneg2 : 0 ≤ tcDecodeWidth (w + 1) n2 := by
            simp [tcDecodeWidth, hs2]
          have : 0 ≤ tcDecodeWidth (w + 1) n1 := by
            simpa [h] using hnonneg2
          linarith
        · have h' : (n1 : ℤ) = (n2 : ℤ) := by
            simpa [tcDecodeWidth, hs1, hs2] using h
          exact_mod_cast h'


/-! =========================================================
    Section 6: Signed two's-complement arithmetic
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

lemma FitsSignedWidth_mono
  {w w' : ℕ} {z : ℤ} (hw : w ≤ w') :
  FitsSignedWidth w z → FitsSignedWidth w' z := by
  intro hz
  rcases hz with ⟨hwpos, hlo, hhi⟩
  unfold FitsSignedWidth signedMin signedMax at *
  have hwpos' : 0 < w' := lt_of_lt_of_le hwpos hw
  have hExp : w - 1 ≤ w' - 1 := Nat.sub_le_sub_right hw 1
  have hPowNat : (2 : ℕ) ^ (w - 1) ≤ (2 : ℕ) ^ (w' - 1) :=
    Nat.pow_le_pow_right (by norm_num) hExp
  have hPow : (2 : ℤ) ^ (w - 1) ≤ (2 : ℤ) ^ (w' - 1) := by
    exact_mod_cast hPowNat
  refine ⟨hwpos', ?_, ?_⟩
  ·
    have hneg :
        -((2 : ℤ) ^ (w' - 1)) ≤ -((2 : ℤ) ^ (w - 1)) := by
      exact neg_le_neg hPow
    exact le_trans hneg hlo
  ·
    exact lt_of_lt_of_le hhi hPow

/--
Wrap is the identity on values that already fit the target signed width.
This bridges raw symbolic integer arithmetic to wrapped machine-level gate
semantics.
-/
lemma tcWrapInt_eq_of_fits
  {w : ℕ} {z : ℤ}
  (hw : 0 < w)
  (hfit : FitsSignedWidth w z) :
  tcWrapInt w z = z := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hw) with ⟨w', rfl⟩
  rcases hfit with ⟨_, hlo, hhi⟩
  unfold signedMin signedMax at *
  -- Now w = w' + 1, so w - 1 = w', and we have:
  --   -(2^w' : ℤ) ≤ z < (2^w' : ℤ)
  have hlo' : -((2 : ℤ) ^ w') ≤ z := by
    have := hlo
    push_cast at this
    simpa using this
  have hhi' : z < (2 : ℤ) ^ w' := by
    have := hhi
    push_cast at this
    simpa using this
  have hpow_pos : (0 : ℤ) < (2 : ℤ) ^ (w' + 1) := by positivity
  have hpow_w'_pos : (0 : ℤ) < (2 : ℤ) ^ w' := by positivity
  have h2pow_split : (2 : ℤ) ^ (w' + 1) = 2 * (2 : ℤ) ^ w' := by
    rw [pow_succ]; ring
  -- Split on sign of z
  unfold tcWrapInt tcModWidth
  by_cases hz : 0 ≤ z
  · -- z ≥ 0 case: z % 2^(w'+1) = z, since 0 ≤ z < 2^w' < 2^(w'+1)
    have hz_lt_pow : z < (2 : ℤ) ^ (w' + 1) := by
      rw [h2pow_split]
      linarith
    have hmod : z % ((2 ^ (w' + 1) : ℕ) : ℤ) = z := by
      push_cast
      exact Int.emod_eq_of_lt hz hz_lt_pow
    rw [hmod]
    have htoNat : (Int.toNat z : ℤ) = z := Int.toNat_of_nonneg hz
    have htoNat_lt : Int.toNat z < 2 ^ w' := by
      have : (Int.toNat z : ℤ) < (2 : ℤ) ^ w' := by rw [htoNat]; exact hhi'
      exact_mod_cast this
    unfold tcDecodeWidth
    simp [htoNat_lt, htoNat]
  · -- z < 0 case: z % 2^(w'+1) = z + 2^(w'+1), which is in [2^w', 2^(w'+1))
    push_neg at hz
    have hz_neg : z < 0 := hz
    set M : ℤ := (2 : ℤ) ^ (w' + 1) with hM_def
    have hM_pos : 0 < M := hpow_pos
    have hzM_nonneg : 0 ≤ z + M := by
      rw [h2pow_split] at *
      linarith
    have hzM_lt : z + M < M := by linarith
    have hmod : z % ((2 ^ (w' + 1) : ℕ) : ℤ) = z + M := by
      have hcast : ((2 ^ (w' + 1) : ℕ) : ℤ) = M := by push_cast; rfl
      rw [hcast]
      rw [show z = (z + M) + (-1) * M from by ring]
      simp
      have:= Int.emod_eq_of_lt hzM_nonneg hzM_lt
      simp at this
      apply this

    rw [hmod]
    have htoNat_val : (Int.toNat (z + M) : ℤ) = z + M :=
      Int.toNat_of_nonneg hzM_nonneg
    have htoNat_ge : ¬ Int.toNat (z + M) < 2 ^ w' := by
      intro hcontra
      have hcontra' : (Int.toNat (z + M) : ℤ) < (2 : ℤ) ^ w' := by exact_mod_cast hcontra
      rw [htoNat_val] at hcontra'
      rw [h2pow_split] at hcontra'
      linarith
    unfold tcDecodeWidth
    simp [htoNat_ge, htoNat_val]
    have hcast : ((2 ^ (w' + 1) : ℕ) : ℤ) = M := by push_cast; rfl
    ring



end Shor
