import FastMultiplication.ShorVerification.Framework.Quantum.Registers

/-!
# A concrete basis: functions `ℕ → Bool`

The `RegEncoding` instance that every other file in `Model/Standard/` runs on.

`RegEncoding.toNat_writeNat_of_lt` must hold for *every* `Reg`, and a `Reg` is
any duplicate-free list of naturals, so no finite basis type can carry the
class: take a register whose qubits exceed any proposed dimension and write a
value with those bits set. The basis is therefore the full `ℕ → Bool`.

Nothing here is quantum. `Basis.lean` imports only `Framework/Quantum/Registers`.
-/

universe u

namespace Shor
namespace Model

/-- The model's computational basis: an assignment of a bit to every qubit. -/
abbrev ModelBasis : Type := ℕ → Bool

/-! ## Reading a register

`toNatList l b` reads the bits of `b` at the qubits of `l`, least significant
first. Defining it by recursion on the list — rather than as a `Finset.sum` —
is what makes `bit_eq_testBit_toNat` a two-line induction.
-/

/-- Little-endian read of the bits at the qubits of `l`. -/
def toNatList : List ℕ → ModelBasis → ℕ
  | [], _ => 0
  | q :: qs, b => Nat.bit (b q) (toNatList qs b)

@[simp] theorem toNatList_nil (b : ModelBasis) : toNatList [] b = 0 := rfl

@[simp] theorem toNatList_cons (q : ℕ) (qs : List ℕ) (b : ModelBasis) :
    toNatList (q :: qs) b = Nat.bit (b q) (toNatList qs b) := rfl

theorem toNatList_lt (l : List ℕ) (b : ModelBasis) :
    toNatList l b < 2 ^ l.length := by
  induction l with
  | nil => simp
  | cons q qs ih =>
      simp only [toNatList_cons, List.length_cons, pow_succ]
      cases hq : b q <;> simp [Nat.bit] <;> omega

theorem testBit_toNatList (l : List ℕ) (b : ModelBasis) :
    ∀ (i : ℕ) (h : i < l.length), Nat.testBit (toNatList l b) i = b (l[i]'h) := by
  induction l with
  | nil => intro i h; simp at h
  | cons q qs ih =>
      intro i h
      cases i with
      | zero => simp
      | succ j =>
          rw [toNatList_cons, Nat.testBit_bit_succ]
          simpa using ih j (by simpa using Nat.lt_of_succ_lt_succ h)

/-! ## The encoding -/

/-- Read register `r` out of basis state `b`. -/
def mToNat (r : Reg) (b : ModelBasis) : ℕ := toNatList r.qubits b

/-- Overwrite the bits of `r` with the little-endian bits of `v`, leaving every
qubit outside `r` alone. -/
def mWriteNat (r : Reg) (v : ℕ) (b : ModelBasis) : ModelBasis :=
  fun q => if q ∈ r.qubits then Nat.testBit v (r.qubits.idxOf q) else b q

/-- Observe one qubit. -/
def mBit (q : ℕ) (b : ModelBasis) : Bool := b q

theorem mBit_mWriteNat_mem {r : Reg} {v : ℕ} {b : ModelBasis} {q : ℕ}
    (hq : q ∈ r.qubits) :
    mBit q (mWriteNat r v b) = Nat.testBit v (r.qubits.idxOf q) := by
  simp [mBit, mWriteNat, hq]

theorem mBit_mWriteNat_not_mem {r : Reg} {v : ℕ} {b : ModelBasis} {q : ℕ}
    (hq : q ∉ r.qubits) :
    mBit q (mWriteNat r v b) = b q := by
  simp [mBit, mWriteNat, hq]

theorem get_mem (r : Reg) (i : Fin (regSize r)) : r.get i ∈ r.qubits := by
  simp [Reg.get]

theorem idxOf_get (r : Reg) (i : Fin (regSize r)) : r.qubits.idxOf (r.get i) = i.1 := by
  have hlen : i.1 < r.qubits.length := i.2
  have := List.Nodup.idxOf_getElem r.nodup i.1 hlen
  have hget : r.qubits[i.1]'hlen = r.get i := by simp [Reg.get]
  rw [hget] at this
  exact this

/-- The model's `RegEncoding`. This is the only place `mWriteNat` is unfolded:
everything downstream goes through `bit_writeNat_in`/`bit_writeNat_out`. -/
instance instRegEncoding : RegEncoding ModelBasis where
  toNat := mToNat
  writeNat := mWriteNat
  bit := mBit
  zero := fun _ => false
  bit_zero := fun _ => rfl
  toNat_writeNat_of_lt := by
    intro r v b hv
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < regSize r
    · have hmem : r.get ⟨i, hi⟩ ∈ r.qubits := get_mem r ⟨i, hi⟩
      have hbit : mBit (r.get ⟨i, hi⟩) (mWriteNat r v b) = Nat.testBit v i := by
        rw [mBit_mWriteNat_mem hmem]
        exact congrArg (Nat.testBit v) (idxOf_get r ⟨i, hi⟩)
      have hlen : i < r.qubits.length := by simpa [regSize, Reg.width] using hi
      have htb := testBit_toNatList r.qubits (mWriteNat r v b) i hlen
      have hget : r.qubits[i]'hlen = r.get ⟨i, hi⟩ := by simp [Reg.get]
      rw [hget] at htb
      simpa [mToNat, mBit, htb] using hbit
    · push Not at hi
      have h1 : Nat.testBit (mToNat r (mWriteNat r v b)) i = false := by
        refine Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ?_ (Nat.pow_le_pow_right (by norm_num) hi))
        simpa [mToNat, regSize, Reg.width] using toNatList_lt r.qubits (mWriteNat r v b)
      have h2 : Nat.testBit v i = false := by
        refine Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ?_ (Nat.pow_le_pow_right (by norm_num) hi))
        simpa [ASize] using hv
      rw [h1, h2]
  toNat_lt_ASize := by
    intro r b
    simpa [mToNat, ASize, regSize, Reg.width] using toNatList_lt r.qubits b
  basis_ext := by
    intro b1 b2 h
    funext q
    exact h q
  bit_writeNat_in := by
    intro r v b₁ b₂ q hq
    rw [mBit_mWriteNat_mem hq, mBit_mWriteNat_mem hq]
  bit_writeNat_out := by
    intro r v b q hq
    rw [mBit_mWriteNat_not_mem hq]
    rfl
  bit_eq_testBit_toNat := by
    intro r b i
    have hlen : i.1 < r.qubits.length := i.2
    have htb := testBit_toNatList r.qubits b i.1 hlen
    have hget : r.qubits[i.1]'hlen = r.get i := by simp [Reg.get]
    rw [hget] at htb
    simp [mToNat, mBit, htb]

@[simp] theorem toNat_eq (r : Reg) (b : ModelBasis) :
    RegEncoding.toNat r b = mToNat r b := rfl

@[simp] theorem writeNat_eq (r : Reg) (v : ℕ) (b : ModelBasis) :
    RegEncoding.writeNat r v b = mWriteNat r v b := rfl

@[simp] theorem bit_eq (q : ℕ) (b : ModelBasis) :
    RegEncoding.bit q b = b q := rfl

@[simp] theorem zero_eq : (RegEncoding.zero : ModelBasis) = fun _ => false := rfl

/-! ## Register-locality lemmas

These are the only facts about `mWriteNat` used downstream. Everything in
`Lift.lean` and `BasisMaps.lean` goes through them rather than unfolding
`mWriteNat` and meeting `List.idxOf` terms.
-/

theorem testBit_mToNat (r : Reg) (b : ModelBasis) (i : Fin (regSize r)) :
    Nat.testBit (mToNat r b) i.1 = b (r.get i) := by
  have hlen : i.1 < r.qubits.length := i.2
  have htb := testBit_toNatList r.qubits b i.1 hlen
  have hget : r.qubits[i.1]'hlen = r.get i := by simp [Reg.get]
  rw [hget] at htb
  exact htb

theorem exists_get_of_mem {r : Reg} {q : ℕ} (hq : q ∈ r.qubits) :
    ∃ i : Fin (regSize r), r.get i = q := by
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hq
  exact ⟨⟨i, hi⟩, by simpa [Reg.get] using hget⟩

theorem mToNat_lt (r : Reg) (b : ModelBasis) : mToNat r b < ASize r := by
  simpa [mToNat, ASize, regSize, Reg.width] using toNatList_lt r.qubits b

theorem mToNat_mWriteNat {r : Reg} {v : ℕ} (b : ModelBasis) (hv : v < ASize r) :
    mToNat r (mWriteNat r v b) = v :=
  RegEncoding.toNat_writeNat_of_lt (Basis := ModelBasis) r v b hv

/-- Two basis states that agree off `r` and read the same value on `r` are equal. -/
theorem eq_of_agree_off {r : Reg} {b b' : ModelBasis}
    (hoff : ∀ q, q ∉ r.qubits → b q = b' q)
    (hon : mToNat r b = mToNat r b') : b = b' := by
  funext q
  by_cases hq : q ∈ r.qubits
  · obtain ⟨i, rfl⟩ := exists_get_of_mem hq
    rw [← testBit_mToNat r b i, ← testBit_mToNat r b' i, hon]
  · exact hoff q hq

/-- Writing `r` back with the value it already holds is the identity. -/
@[simp] theorem mWriteNat_mToNat (r : Reg) (b : ModelBasis) :
    mWriteNat r (mToNat r b) b = b := by
  refine eq_of_agree_off (r := r) (fun q hq => mBit_mWriteNat_not_mem hq) ?_
  exact mToNat_mWriteNat b (mToNat_lt r b)

/-- A write to `r` overwrites any earlier write to `r`. -/
@[simp] theorem mWriteNat_mWriteNat (r : Reg) (v v' : ℕ) (b : ModelBasis) :
    mWriteNat r v (mWriteNat r v' b) = mWriteNat r v b := by
  funext q
  by_cases hq : q ∈ r.qubits
  · exact mBit_mWriteNat_mem (b := mWriteNat r v' b) hq |>.trans
      (mBit_mWriteNat_mem (b := b) hq).symm
  · rw [show mWriteNat r v (mWriteNat r v' b) q = (mWriteNat r v' b) q from
      mBit_mWriteNat_not_mem hq,
      show mWriteNat r v' b q = b q from mBit_mWriteNat_not_mem hq,
      show mWriteNat r v b q = b q from mBit_mWriteNat_not_mem hq]

/-- When both values are in range, two writes to the same register agree exactly
when the values agree and the two basis states agree off the register. -/
theorem mWriteNat_eq_iff {r : Reg} {y y' : ℕ} {b b' : ModelBasis}
    (hy : y < ASize r) (hy' : y' < ASize r) :
    mWriteNat r y b = mWriteNat r y' b' ↔
      y = y' ∧ ∀ q, q ∉ r.qubits → b q = b' q := by
  constructor
  · intro h
    refine ⟨?_, fun q hq => ?_⟩
    · rw [← mToNat_mWriteNat (r := r) b hy, ← mToNat_mWriteNat (r := r) b' hy', h]
    · rw [← mBit_mWriteNat_not_mem (r := r) (v := y) (b := b) hq, h,
        mBit_mWriteNat_not_mem hq]
  · rintro ⟨rfl, hoff⟩
    funext q
    by_cases hq : q ∈ r.qubits
    · exact mBit_mWriteNat_mem hq |>.trans (mBit_mWriteNat_mem hq).symm
    · rw [show mWriteNat r y b q = b q from mBit_mWriteNat_not_mem hq,
        show mWriteNat r y b' q = b' q from mBit_mWriteNat_not_mem hq]
      exact hoff q hq

/-- Writes to `r` agree off `r` with what they were written onto. -/
theorem mWriteNat_agree_off (r : Reg) (v : ℕ) (b : ModelBasis) (q : ℕ)
    (hq : q ∉ r.qubits) : mWriteNat r v b q = b q :=
  mBit_mWriteNat_not_mem hq

/-! ## Reading depends only on the register's own qubits -/

theorem toNatList_congr : ∀ {l : List ℕ} {b b' : ModelBasis},
    (∀ q ∈ l, b q = b' q) → toNatList l b = toNatList l b'
  | [], _, _, _ => rfl
  | q :: qs, b, b', h => by
      rw [toNatList_cons, toNatList_cons, h q (List.mem_cons_self ..),
        toNatList_congr (fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))]

theorem mToNat_congr {r : Reg} {b b' : ModelBasis} (h : ∀ q ∈ r.qubits, b q = b' q) :
    mToNat r b = mToNat r b' := toNatList_congr h

/-- Writing a register leaves the value of any disjoint register alone. -/
theorem mToNat_mWriteNat_of_disjoint {r s : Reg} (h : ∀ q ∈ s.qubits, q ∉ r.qubits)
    (v : ℕ) (b : ModelBasis) :
    mToNat s (mWriteNat r v b) = mToNat s b :=
  mToNat_congr fun q hq => mWriteNat_agree_off r v b q (h q hq)

/-! ## Splitting a register -/

theorem toNatList_append (l₁ l₂ : List ℕ) (b : ModelBasis) :
    toNatList (l₁ ++ l₂) b = toNatList l₁ b + 2 ^ l₁.length * toNatList l₂ b := by
  induction l₁ with
  | nil => simp
  | cons q qs ih =>
      rw [List.cons_append, toNatList_cons, ih, toNatList_cons, List.length_cons]
      cases hq : b q <;> simp [Nat.bit, pow_succ] <;> ring

theorem mToNat_split (r : Reg) (m : ℕ) (hm : m ≤ regSize r) (b : ModelBasis) :
    mToNat r b
      = mToNat (splitLeft r ⟨m, hm⟩) b + 2 ^ m * mToNat (splitRight r ⟨m, hm⟩) b := by
  have hrs : regSize r = r.qubits.length := rfl
  have hlen : (r.qubits.take m).length = m := by
    rw [List.length_take]; omega
  have : r.qubits = r.qubits.take m ++ r.qubits.drop m := (List.take_append_drop m r.qubits).symm
  rw [mToNat, this, toNatList_append, hlen]
  rfl

@[simp] theorem regSize_splitLeft (r : Reg) (m : ℕ) (hm : m ≤ regSize r) :
    regSize (splitLeft r ⟨m, hm⟩) = m := by
  have hrs : regSize r = r.qubits.length := rfl
  simp only [splitLeft, regSize, Reg.width, Reg.take, List.length_take]
  omega

@[simp] theorem regSize_splitRight (r : Reg) (m : ℕ) (hm : m ≤ regSize r) :
    regSize (splitRight r ⟨m, hm⟩) = regSize r - m := by
  simp [splitRight, regSize, Reg.width, Reg.drop]

/-! ## Single-qubit registers -/

@[simp] theorem qubitReg_qubits (q : ℕ) : (qubitReg q).qubits = [q] := rfl

@[simp] theorem regSize_qubitReg (q : ℕ) : regSize (qubitReg q) = 1 := rfl

@[simp] theorem ASize_qubitReg (q : ℕ) : ASize (qubitReg q) = 2 := rfl

@[simp] theorem mToNat_qubitReg (q : ℕ) (b : ModelBasis) :
    mToNat (qubitReg q) b = if b q then 1 else 0 := by
  cases h : b q <;> simp [mToNat, qubitReg, Reg.singleton, toNatList, Nat.bit, h]

theorem mWriteNat_qubitReg (q v : ℕ) (b : ModelBasis) :
    mWriteNat (qubitReg q) v b = Function.update b q (Nat.testBit v 0) := by
  funext q'
  by_cases h : q' = q
  · subst h; simp [mWriteNat, qubitReg, Reg.singleton]
  · simp [mWriteNat, qubitReg, Reg.singleton, h]

/-- The only two values ever written to a single-qubit register. -/
@[simp] theorem mWriteNat_qubitReg_bool (q : ℕ) (c : Bool) (b : ModelBasis) :
    mWriteNat (qubitReg q) (if c then 1 else 0) b = Function.update b q c := by
  cases c <;> simp [mWriteNat_qubitReg]

/-! ## Sanity checks -/

section Sanity

example : regSize (Reg.interval 0 5) = 5 := rfl
example : ASize (Reg.interval 0 5) = 32 := rfl
example (b : ModelBasis) : mToNat Reg.empty b = 0 := rfl

/-- Little-endian: qubit `i` of `Reg.interval 0 3` carries bit `i`. -/
example : mToNat (Reg.interval 0 3) (fun q => decide (q = 1)) = 2 := by decide

example (b : ModelBasis) : mToNat (Reg.interval 0 3) (mWriteNat (Reg.interval 0 3) 5 b) = 5 :=
  mToNat_mWriteNat b (by decide)

end Sanity

end Model
end Shor
