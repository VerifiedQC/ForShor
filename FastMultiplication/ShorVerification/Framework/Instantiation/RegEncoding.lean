import FastMultiplication.ShorVerification.Framework.Instantiation.QSemantics
import Batteries.Data.Nat.Lemmas

namespace Shor

namespace ConcreteQSemantics

def readReg (r : Reg) (b : Basis) : ℕ :=
  Nat.ofBits fun i : Fin (regSize r) =>
    b.testBit (r.get i)

def writeBit (q : ℕ) (x : Bool) (b : Basis) : Basis :=
  if x then
    b ||| 2 ^ q
  else
    Nat.ldiff b (2 ^ q)

def writeBits : List ℕ → ℕ → Basis → Basis
  | [], _, b => b
  | q :: qs, v, b =>
      writeBits qs (v >>> 1)
        (writeBit q (v.testBit 0) b)

def writeReg (r : Reg) (v : ℕ) (b : Basis) : Basis :=
  writeBits r.qubits v b

@[simp]
lemma testBit_writeBit_same
    (q : ℕ)
    (x : Bool)
    (b : Basis) :
    (writeBit q x b).testBit q = x := by
  cases x <;>
    simp [writeBit,Nat.testBit_ldiff]

lemma testBit_writeBit_ne
    (p q : ℕ)
    (x : Bool)
    (b : Basis)
    (h : p ≠ q) :
    (writeBit q x b).testBit p = b.testBit p := by
  have h' : q ≠ p := Ne.symm h
  cases x <;>
    simp [writeBit,Nat.testBit_ldiff, h']

lemma testBit_writeBits_out
    (qs : List ℕ)
    (p v : ℕ)
    (b : Basis)
    (hp : p ∉ qs) :
    (writeBits qs v b).testBit p = b.testBit p := by
  induction qs generalizing v b with
  | nil =>
      rfl
  | cons q qs ih =>
      have hpq : p ≠ q := by
        intro h
        apply hp
        simp [h]
      have hpqs : p ∉ qs := by
        intro h
        apply hp
        simp [h]
      rw [writeBits]
      rw [ih (v := v >>> 1)
        (b := writeBit q (v.testBit 0) b) hpqs]
      exact testBit_writeBit_ne p q (v.testBit 0) b hpq

lemma testBit_writeBits_mem_independent
    (qs : List ℕ)
    (hnodup : qs.Nodup)
    (q : ℕ)
    (hq : q ∈ qs)
    (v : ℕ)
    (b₁ b₂ : Basis) :
    (writeBits qs v b₁).testBit q =
      (writeBits qs v b₂).testBit q := by
  induction qs generalizing v b₁ b₂ with
  | nil =>
      simp at hq
  | cons a qs ih =>
      have ha : a ∉ qs :=
        (List.nodup_cons.mp hnodup).1
      have hqs : qs.Nodup :=
        (List.nodup_cons.mp hnodup).2
      rcases List.mem_cons.mp hq with hqa | hq
      · subst q
        rw [writeBits, writeBits]
        rw [testBit_writeBits_out qs a (v >>> 1)
          (writeBit a (v.testBit 0) b₁) ha]
        rw [testBit_writeBits_out qs a (v >>> 1)
          (writeBit a (v.testBit 0) b₂) ha]
        simp
      · rw [writeBits, writeBits]
        exact ih hqs hq
          (v >>> 1)
          (writeBit a (v.testBit 0) b₁)
          (writeBit a (v.testBit 0) b₂)

lemma testBit_writeBits_get
    (qs : List ℕ)
    (hnodup : qs.Nodup)
    (v : ℕ)
    (b : Basis)
    (i : Fin qs.length) :
    (writeBits qs v b).testBit (qs.get i) =
      v.testBit i.1 := by
  induction qs generalizing v b with
  | nil =>
      exact Fin.elim0 i
  | cons q qs ih =>
      have hq : q ∉ qs :=
        (List.nodup_cons.mp hnodup).1
      have hqs : qs.Nodup :=
        (List.nodup_cons.mp hnodup).2
      refine Fin.cases ?_ (fun j => ?_) i
      · change
          (writeBits qs (v >>> 1)
            (writeBit q (v.testBit 0) b)).testBit q =
              v.testBit 0
        rw [testBit_writeBits_out qs q (v >>> 1)
          (writeBit q (v.testBit 0) b) hq]
        exact testBit_writeBit_same q (v.testBit 0) b
      · change
          (writeBits qs (v >>> 1)
            (writeBit q (v.testBit 0) b)).testBit (qs.get j) =
              v.testBit (j.1 + 1)
        rw [ih hqs
          (v := v >>> 1)
          (b := writeBit q (v.testBit 0) b)
          (i := j)]
        simp [Nat.testBit_shiftRight, Nat.add_comm]

lemma testBit_writeReg_get
    (r : Reg)
    (v : ℕ)
    (b : Basis)
    (i : Fin (regSize r)) :
    (writeReg r v b).testBit (r.get i) =
      v.testBit i.1 := by
  have h :=
    testBit_writeBits_get
      r.qubits
      r.nodup
      v
      b
      ⟨i.1, by simp [regSize, Reg.width]⟩
  simpa [writeReg, Reg.get, regSize, Reg.width] using h

lemma readReg_writeReg
    (r : Reg)
    (v : ℕ)
    (b : Basis)
    (hv : v < ASize r) :
    readReg r (writeReg r v b) = v := by
  unfold readReg

  have hfun :
      (fun i : Fin (regSize r) =>
        (writeReg r v b).testBit (r.get i)) =
      (fun i : Fin (regSize r) =>
        v.testBit i.1) := by
    funext i
    exact testBit_writeReg_get r v b i

  rw [hfun]
  rw [Nat.ofBits_testBit]

  have hv' : v < 2 ^ regSize r := by
    simpa [ASize] using hv

  exact Nat.mod_eq_of_lt hv'

lemma readReg_lt
    (r : Reg)
    (b : Basis) :
    readReg r b < ASize r := by
  unfold readReg ASize
  exact Nat.ofBits_lt_two_pow
    (fun i : Fin (regSize r) =>
      b.testBit (r.get i))

lemma readReg_testBit
    (r : Reg)
    (b : Basis)
    (i : Fin (regSize r)) :
    b.testBit (r.get i) =
      Nat.testBit (readReg r b) i.1 := by
  unfold readReg
  symm
  exact Nat.testBit_ofBits_lt
    (fun j : Fin (regSize r) =>
      b.testBit (r.get j))
    i.1
    i.2

instance instRegEncoding : RegEncoding Basis where
  toNat := readReg
  writeNat := writeReg
  bit := fun q b => b.testBit q
  zero := 0

  bit_zero := by
    intro q
    simp

  toNat_writeNat_of_lt := by
    intro r v b hv
    exact readReg_writeReg r v b hv

  toNat_lt_ASize := by
    intro r b
    exact readReg_lt r b

  basis_ext := by
    intro b₁ b₂ h
    apply Nat.eq_of_testBit_eq
    intro q
    exact h q

  bit_writeNat_in := by
    intro r v b₁ b₂ q hq
    exact testBit_writeBits_mem_independent
      r.qubits
      r.nodup
      q
      hq
      v
      b₁
      b₂

  bit_writeNat_out := by
    intro r v b q hq
    exact testBit_writeBits_out
      r.qubits
      q
      v
      b
      hq

  bit_eq_testBit_toNat := by
    intro r b i
    exact readReg_testBit r b i

noncomputable instance instConcreteQSemanticsRegEncoding :
    RegEncoding concreteQSemantics.Basis := by
  change RegEncoding Basis
  exact instRegEncoding

end ConcreteQSemantics

end Shor
