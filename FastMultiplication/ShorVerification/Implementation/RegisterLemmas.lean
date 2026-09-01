import FastMultiplication.ShorVerification.Framework.AbstractMachine.Gates

/-!
# Implementation-side register laws

The Framework register module owns only data structures, operations, and the
minimal `RegEncoding` interface. This module contains every derived register
law used by concrete implementations and their correctness proofs. Keeping
these declarations here preserves the public theorem names without introducing
a Framework-to-Implementation import.
-/

universe u

namespace Shor

theorem Disjoint.symm {a b : Reg} :
    Disjoint a b → Disjoint b a := by
  intro h
  exact List.Disjoint.symm h


@[simp] theorem regSize_empty :
    regSize Reg.empty = 0 := by
  rfl

@[simp] theorem regSize_singleton (q : ℕ) :
    regSize (qubitReg q) = 1 := by
  rfl

@[simp] theorem splitLeft_size
    (r : Reg) (m : SplitPoint r) :
    regSize (splitLeft r m) = m.1 := by
  have hm:=m.2
  simp [splitLeft, Reg.take, regSize, Reg.width, regSize] at *
  simp[hm]

@[simp] theorem splitRight_size
    (r : Reg) (m : SplitPoint r) :
    regSize (splitRight r m) = regSize r - m.1 := by
  simp [splitRight, Reg.drop, regSize, Reg.width]

theorem splitLeft_splitRight_disjoint
    (r : Reg) (m : SplitPoint r) :
    Disjoint (splitLeft r m) (splitRight r m) := by
  simpa [Disjoint, splitLeft, splitRight, Reg.take, Reg.drop] using
    List.disjoint_take_drop r.nodup (le_refl m.1)


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
    (i : Fin (regSize r)) :
    RegEncoding.bit (r.get i)
        (RegEncoding.writeNat r v b) =
      Nat.testBit v i.1 := by
  rw [RegEncoding.bit_eq_testBit_toNat]
  rw [RegEncoding.toNat_writeNat_of_lt r v b hv]

theorem splitLeft_get
    (r : Reg) (m : SplitPoint r)
    (i : Fin (regSize (splitLeft r m))) :
    (splitLeft r m).get i =
      r.get ⟨i.1, by
        have hi := i.2
        simp [splitLeft_size] at hi
        exact lt_of_lt_of_le hi m.2⟩ := by
  simp [
    splitLeft,
    Reg.take,
    Reg.get,
    regSize,
    Reg.width
  ]

theorem splitRight_get
    (r : Reg) (m : SplitPoint r)
    (i : Fin (regSize (splitRight r m))) :
    (splitRight r m).get i =
      r.get ⟨m.1 + i.1, by
        have hi := i.2
        have hi' : i.1 < regSize r - m.1 := by
          simpa [splitRight_size] using hi
        have hbound : m.1 + i.1 < regSize r := by
          omega
        simpa [regSize, Reg.width] using hbound⟩ := by
  simp [
    splitRight,
    Reg.drop,
    Reg.get,
    regSize,
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
      regSize left = m.1 := by
    simp [left]

  have hjoined :
      low + ASize left * high < ASize r := by
    have hsizes :
        regSize left + regSize right = regSize r := by
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

    let iL : Fin (regSize left) :=
      ⟨i.1, by
        simp [left, regSize, Reg.width]⟩

    have hgetL : left.get iL = q := by
      simpa [iL, Reg.get, regSize, Reg.width] using hi

    let iWhole : Fin (regSize r) :=
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
            have hi : iL.1 < regSize left := iL.2
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

      let jR : Fin (regSize right) :=
        ⟨j.1, by
          simp[right, regSize, Reg.width]⟩

      have hgetR : right.get jR = q := by
        simpa [jR, Reg.get, regSize, Reg.width] using hj

      let jWhole : Fin (regSize r) :=
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

    let j : Fin (regSize r) :=
      ⟨i.1, by
        simp [regSize, Reg.width]⟩

    have hj : r.get j = q := by
      simpa [Reg.get, j, regSize, Reg.width] using hi

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
      ⟨regSize left, by
        simp [regSize, Reg.width, Reg.append]⟩ =
    left := by
  cases left with
  | mk leftQubits leftNodup =>
      cases right with
      | mk rightQubits rightNodup =>
          simp [
            splitLeft,
            Reg.take,
            Reg.append,
            regSize,
            Reg.width
          ]

@[simp] theorem splitRight_append
    (left right : Reg)
    (hdisj : Disjoint left right) :
  splitRight
      (Reg.append left right hdisj)
      ⟨regSize left, by
        simp [regSize, Reg.width, Reg.append]⟩ =
    right := by
  cases left with
  | mk leftQubits leftNodup =>
      cases right with
      | mk rightQubits rightNodup =>
          simp [
            splitRight,
            Reg.drop,
            Reg.append,
            regSize,
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
    ⟨regSize left, by
      simp [r, regSize, Reg.width, Reg.append]⟩

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
    simp [r, ASize, regSize, Reg.width, Reg.append, pow_add]

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
namespace ExtReg

@[simp] theorem width_grow
    (e : ExtReg) (n : ℕ)
    (hcap : e.CanGrow n) :
    width (e.grow n) = width e + n := by
  simp [width, grow, Reg.append, newBits, Reg.take, regSize, Reg.width,
    CanGrow, capacity] at hcap ⊢
  omega

@[simp] theorem capacity_grow
    (e : ExtReg) (n : ℕ)
    (_hcap : e.CanGrow n) :
    capacity (e.grow n) = capacity e - n := by
  simp [capacity, grow, remainingReserve, Reg.drop, regSize, Reg.width]

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




namespace Gate

theorem Reg.take_append_drop
    (r : Reg) (n : ℕ) :
    (r.take n).qubits ++ (r.drop n).qubits =
      r.qubits := by
  simp [Reg.take, Reg.drop]

theorem ExtReg.newBits_size
    (e : ExtReg)
    (n : ℕ)
    (hcap : e.CanGrow n) :
    regSize (e.newBits n) = n := by
  simp [ExtReg.newBits, ExtReg.CanGrow,
    ExtReg.capacity, regSize, Reg.width] at *
  simp[Reg.take]
  omega

theorem ExtReg.ownedQubits_grow
    (e : ExtReg)
    (n : ℕ) :
    (e.grow n).ownedQubits = e.ownedQubits := by
  simp [ExtReg.ownedQubits, ExtReg.grow, Reg.append, ExtReg.newBits,
    ExtReg.remainingReserve, Reg.take, Reg.drop, List.append_assoc]

theorem RegEncoding.toNat_append_eq
    {Basis : Type u}
    [RegEncoding Basis]
    (left right : Reg)
    (hdisj : Disjoint left right)
    (b : Basis) :
    RegEncoding.toNat (Reg.append left right hdisj) b
      =
    RegEncoding.toNat left b +
      ASize left * RegEncoding.toNat right b := by
  exact RegEncoding.toNat_append left right hdisj b

theorem ExtReg.active_grow_qubits
    (e : ExtReg)
    (n : ℕ) :
    (e.grow n).active.qubits =
      e.active.qubits ++ (e.newBits n).qubits := by
  rfl

theorem ExtReg.toNat_grow
    {Basis : Type u}
    [RegEncoding Basis]
    (e : ExtReg)
    (n : ℕ)
    (b : Basis) :
    ExtReg.toNat (e.grow n) b
      =
    ExtReg.toNat e b +
      2 ^ e.width *
        RegEncoding.toNat (e.newBits n) b := by
  simpa [ExtReg.toNat, ExtReg.grow, ExtReg.width, ASize] using
    RegEncoding.toNat_append e.active (e.newBits n) _ b

theorem ExtReg.toNat_grow_of_fresh
    {Basis : Type u}
    [RegEncoding Basis]
    (e : ExtReg)
    (n : ℕ)
    (b : Basis)
    (hzero : ExtReg.FreshFor e n b) :
    ExtReg.toNat (e.grow n) b =
      ExtReg.toNat e b := by
  rw [ExtReg.toNat_grow]
  simp [ExtReg.FreshFor, FreshZero] at hzero
  simp [hzero]

lemma tcDecodeWidth_add_eq_of_lt
    {w n value : ℕ}
    (hn : 0 < n)
    (hvalue : value < 2 ^ w) :
    tcDecodeWidth (w + n) value = (value : ℤ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hn)

  have hle :
      2 ^ w ≤ 2 ^ (w + m) :=
    Nat.pow_le_pow_right (by omega)
      (Nat.le_add_right w m)

  have hlt :
      value < 2 ^ (w + m) :=
    lt_of_lt_of_le hvalue hle

  simp [tcDecodeWidth, hlt]

theorem ExtReg.extToInt_grow_of_fresh
    {Basis : Type u}
    [RegEncoding Basis]
    (e : ExtReg)
    (n : ℕ)
    (b : Basis)
    (hcap : e.CanGrow n)
    (hzero : e.FreshFor n b)
    (hn : 0 < n) :
    extToInt (e.grow n) b =
      (ExtReg.toNat e b : ℤ) := by
  unfold extToInt
  rw [ExtReg.toNat_grow_of_fresh e n b hzero]
  rw [ExtReg.width_grow e n hcap]
  apply tcDecodeWidth_add_eq_of_lt hn
  exact ExtReg.toNat_lt e b


end Gate

end Shor
