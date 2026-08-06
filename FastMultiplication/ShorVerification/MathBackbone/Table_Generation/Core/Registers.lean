import Mathlib.Data.Int.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.EuclideanDomain.Basic
-- import Mathlib.Tactic

/-!
# Table-generation linear state model

This file defines the symbolic register/state model used by the table
generation proofs, together with the primitive operations and basic algebraic
facts about shifts, negation, scaled addition, and right-shift success.
-/

/-! =========================================================
    Section 1: Registers and coefficient operations
========================================================= -/

/-- A register is a linear combo of `x₀,…,x_{k-1}` with **integer** coefficients. -/
abbrev Register (k : ℕ) := Fin k → ℤ

/-- A state is `k` registers. -/
abbrev State (k : ℕ) := Fin k → Register k

namespace Register

/-- Zero register. -/
def zero (k : ℕ) : Register k := fun _ => 0

/-- Negate all coefficients in a register. -/
def negate {k : ℕ} (r : Register k) : Register k :=
  fun j => - (r j)

/-- Left shift every coefficient by `n` (multiply by `2^n`). -/
def shiftL {k : ℕ} (r : Register k) (n : ℕ) : Register k :=
  fun j => (r j) * (2 : ℤ) ^ n

/-- Right shift every coefficient by `n`, **iff each coeff is divisible by `2^n`**.
    Returns `none` if any coefficient would be fractional. -/
def shiftR? {k : ℕ} (r : Register k) (n : ℕ) : Option (Register k) :=
  let m : ℤ := (2 : ℤ) ^ n
  if ∀ j, (r j) % m = 0 then
    some (fun j => (r j) / m)
  else
    none

/-- `dst ← dst + (±1) * (src << shift)` (no implicit right shifts). -/
def addScaled {k : ℕ} (dst src : Register k) (negSrc : Bool) (shift : ℕ) : Register k :=
  let sgn : ℤ := if negSrc then -1 else 1
  fun j => (dst j) + sgn * (src j) * (2 : ℤ) ^ shift

end Register

/-! =========================================================
    Section 2: State updates and cancellation helpers
========================================================= -/

namespace State
open Register

/-- Basis state: register `i` = `x_i`. -/
def start_state {k : ℕ} : State k :=
  fun i => fun j => if j = i then (1 : ℤ) else 0

/-- Overwrite register `i`. -/
def setReg {k : ℕ} (σ : State k) (i : Fin k) (r : Register k) : State k :=
  fun j => if j = i then r else σ j

/-- Negate register `i`. -/
def negateReg {k : ℕ} (σ : State k) (i : Fin k) : State k :=
  setReg σ i (Register.negate (σ i))

/-- Left shift register `i` by `n`. -/
def shiftLReg {k : ℕ} (σ : State k) (i : Fin k) (n : ℕ) : State k :=
  setReg σ i (Register.shiftL (σ i) n)

/-- Right shift register `i` by `n` *iff* all coeffs are divisible by `2^n`. -/
def shiftRReg? {k : ℕ} (σ : State k) (i : Fin k) (n : ℕ) : Option (State k) := do
  let r' ← Register.shiftR? (σ i) n
  pure (setReg σ i r')

/-- `dst ← dst + (±1) * (src << shift)`. -/
def addScaledReg {k : ℕ} (σ : State k)
    (dst src : Fin k) (negSrc : Bool) (shift : ℕ) : State k :=
  setReg σ dst (Register.addScaled (σ dst) (σ src) negSrc shift)

theorem negate_addScaledReg_negate
    {k : ℕ} (σ : State k) (dst src : Fin k) (hds : dst ≠ src) :
    ((σ.negateReg src).addScaledReg dst src false 0).negateReg src
      =
    σ.addScaledReg dst src true 0 := by
  classical
  ext r j
  by_cases hr_src : r = src
  · subst hr_src
    have:r≠ dst:=by omega
    simp [State.negateReg, State.addScaledReg, State.setReg,
          Register.negate, this]
  · by_cases hr_dst : r = dst
    · subst hr_dst
      simp [State.negateReg, State.addScaledReg, State.setReg,
            Register.negate, Register.addScaled, hds]
    ·
      simp [State.negateReg, State.addScaledReg, State.setReg, hr_src, hr_dst]


/-- Cancels: shifting left by `n` makes every coeff divisible by `2^n`, so shifting right succeeds. -/
lemma shiftR?_shiftL {k : ℕ} (r : Register k) (n : ℕ) :
    shiftR? (shiftL r n) n = some r := by
  classical
  unfold shiftR? shiftL
  set m : ℤ := (2 : ℤ) ^ n
  have hm0 : m ≠ 0 := by
    subst m
    apply Int.pow_ne_zero (n:=2)
    simp

  have hcond : ∀ j, ((r j) * m) % m = 0 := by
    intro j
    -- m divides (r j)*m
    have hdvd : m ∣ (r j) * m := by
      rw[Int.mul_comm]
      exact Int.dvd_mul_right m (r j)
    -- `%` on Int is `emod`, and emod is 0 when divisible
    simp
  have hall : (∀ j, ((fun j => (r j) * m) j) % m = 0) := by
    intro j; simp
  simp [m, hall, hm0]

lemma addScaledReg_src_unchanged {k : ℕ} (σ : State k) (dst src : Fin k)
    (negSrc : Bool) (sh : ℕ) (hds : dst ≠ src) :
    (σ.addScaledReg dst src negSrc sh) src = σ src := by
  unfold addScaledReg setReg
  simp;intro h;simp_all

/-- Main lemma: after `negate; shiftL; addScaled (touching dst only)`, the right shift on `src` succeeds. -/
lemma exists_shiftRReg_after_neg_shiftL_addScaled
  {k : ℕ} (σ : State k) (dst src : Fin k) (sh : ℕ) (hds : dst ≠ src) :
  ∃ σA',
    (((σ.negateReg src).shiftLReg src sh).addScaledReg dst src false 0).shiftRReg? src sh = some σA' := by
  classical
  set σA : State k :=
    ((σ.negateReg src).shiftLReg src sh).addScaledReg dst src false 0
  have hσA_src : σA src = ((σ.negateReg src).shiftLReg src sh) src := by
    simpa [σA] using (addScaledReg_src_unchanged (σ := (σ.negateReg src).shiftLReg src sh)
      (dst := dst) (src := src) (negSrc := false) (sh := 0) hds)
  have hsrc_shift :
      ((σ.negateReg src).shiftLReg src sh) src = Register.shiftL ((σ.negateReg src) src) sh := by
    unfold shiftLReg setReg
    simp
  have hreg : Register.shiftR? (σA src) sh = some ((σ.negateReg src) src) := by
    simpa [hσA_src, hsrc_shift] using (shiftR?_shiftL (r := (σ.negateReg src) src) (n := sh))
  refine ⟨State.setReg σA src ((σ.negateReg src) src), ?_⟩
  unfold shiftRReg?
  simp [hreg, σA]

/-- Main lemma: after `negate; shiftL; addScaled (touching dst only)`, the right shift on `src` succeeds. -/
lemma exists_shiftRReg_after_shiftL_addScaled
  {k : ℕ} (σ : State k) (dst src : Fin k) (sh : ℕ) (hds : dst ≠ src) :
  ∃ σA',
    (((σ).shiftLReg src sh).addScaledReg dst src false 0).shiftRReg? src sh = some σA' := by
  classical
  set σA : State k :=
    ((σ).shiftLReg src sh).addScaledReg dst src false 0
  have hσA_src : σA src = ((σ).shiftLReg src sh) src := by
    simpa [σA] using (addScaledReg_src_unchanged (σ := (σ).shiftLReg src sh)
      (dst := dst) (src := src) (negSrc := false) (sh := 0) hds)
  have hsrc_shift :
      ((σ).shiftLReg src sh) src = Register.shiftL ((σ) src) sh := by
    unfold shiftLReg setReg
    simp
  have hreg : Register.shiftR? (σA src) sh = some ((σ) src) := by
    simpa [hσA_src, hsrc_shift] using (shiftR?_shiftL (r := (σ) src) (n := sh))
  refine ⟨State.setReg σA src ((σ) src), ?_⟩
  unfold shiftRReg?
  simp [hreg, σA]

lemma shiftRReg?_after_neg_shiftL_addScaled_eq
  {k : ℕ} (σ : State k) (dst src : Fin k) (sh : ℕ) (hds : dst ≠ src) :
  let σA : State k :=
    ((σ.negateReg src).shiftLReg src sh).addScaledReg dst src false 0
  let σA' : State k :=
    State.setReg σA src ((σ.negateReg src) src)
  σA.shiftRReg? src sh = some σA' := by
  classical
  intro σA σA'
  have hσA_src :
      σA src = ((σ.negateReg src).shiftLReg src sh) src := by
    simpa [σA] using
      (addScaledReg_src_unchanged
        (σ := (σ.negateReg src).shiftLReg src sh)
        (dst := dst) (src := src) (negSrc := false) (sh := 0) hds)
  have hsrc_shift :
      ((σ.negateReg src).shiftLReg src sh) src
        =
      Register.shiftL ((σ.negateReg src) src) sh := by
    unfold State.shiftLReg State.setReg
    simp
  have hreg :
      Register.shiftR? (σA src) sh = some ((σ.negateReg src) src) := by
    simpa [hσA_src, hsrc_shift] using (shiftR?_shiftL (r := (σ.negateReg src) src) (n := sh))
  unfold State.shiftRReg?
  simp [hreg, σA']


lemma shiftRReg?_after_shiftL_addScaled_eq
  {k : ℕ} (σ : State k) (dst src : Fin k) (sh : ℕ) (hds : dst ≠ src) :
  let σA : State k :=
    (σ.shiftLReg src sh).addScaledReg dst src false 0
  let σA' : State k :=
    State.setReg σA src (σ src)
  σA.shiftRReg? src sh = some σA' := by
  classical
  intro σA σA'
  have hσA_src :
      σA src = (σ.shiftLReg src sh) src := by
    simpa [σA] using
      (addScaledReg_src_unchanged
        (σ := σ.shiftLReg src sh)
        (dst := dst) (src := src) (negSrc := false) (sh := 0) hds)
  have hsrc_shift :
      (σ.shiftLReg src sh) src
        =
      Register.shiftL (σ src) sh := by
    unfold State.shiftLReg State.setReg
    simp
  have hreg :
      Register.shiftR? (σA src) sh = some (σ src) := by
    simpa [hσA_src, hsrc_shift] using (shiftR?_shiftL (r := σ src) (n := sh))
  unfold State.shiftRReg?
  simp [hreg, σA']
end State

/-! =========================================================
    Section 3: Primitive operations and inverses
========================================================= -/

namespace Operations

inductive Point where
  | int  (z : Int)
  | frac (m : Int)
deriving Repr, DecidableEq

/-- Valid operations on registers. -/
inductive valid_ops (k : ℕ) where
  | shiftL    (i : Fin k) (n : ℕ)
  | shiftR    (i : Fin k) (n : ℕ)
  | negate    (i : Fin k)
  | addScaled (dst src : Fin k) (negSrc : Bool) (shift : ℕ)
  | phaseProduct (i : Fin k)

--deriving Repr, DecidableEq


def inv {k : ℕ} : valid_ops k → valid_ops k
  | .shiftL i n               => .shiftR i n
  | .shiftR i n               => .shiftL i n
  | .negate i                 => .negate i
  | .addScaled dst src b sh   => .addScaled dst src (!b) sh
  | .phaseProduct i       => .phaseProduct i


@[simp] theorem ops_inv_involutive {k} (op : valid_ops k) :
    inv (inv op) = op := by
  cases op <;> simp [inv]
end Operations

/-! =========================================================
    Section 4: Register simp lemmas and right-shift facts
========================================================= -/

namespace Register

@[simp] lemma zero_apply {k : ℕ} (j : Fin k) :
  zero k j = 0 := rfl

@[simp] lemma negate_apply {k : ℕ} (r : Register k) (j : Fin k) :
  negate r j = - r j := rfl

@[simp] lemma shiftL_apply {k : ℕ} (r : Register k) (n : ℕ) (j : Fin k) :
  shiftL r n j = r j * (2 : ℤ) ^ n := rfl

@[simp] lemma addScaled_apply {k : ℕ}
    (dst src : Register k) (negSrc : Bool) (n : ℕ) (j : Fin k) :
  addScaled dst src negSrc n j
    = dst j + (if negSrc then -1 else 1) * src j * (2 : ℤ) ^ n := rfl

/-- Extensionality: registers are equal if they agree pointwise. -/
@[ext] lemma ext {k : ℕ} {r s : Register k}
  (h : ∀ j, r j = s j) : r = s := funext h

/-- *Exact* description of `shiftR?` when it succeeds. -/
lemma shiftR?_eq_some_iff {k : ℕ} {r r' : Register k} {n : ℕ} :
  shiftR? r n = some r' ↔
    (∀ j, (r j) % ((2 : ℤ) ^ n) = 0 ∧ r' j = (r j) / ((2 : ℤ) ^ n)) := by
  unfold shiftR?
  set m : ℤ := (2 : ℤ) ^ n with hm
  constructor
  · intro h j
    simp_all only [Option.ite_none_right_eq_some, Option.some.injEq, true_and, m]
    obtain ⟨left, right⟩ := h
    subst right
    simp_all only
  · intro H
    simp_all only [implies_true, ↓reduceIte, Option.some.injEq, m]
    ext j : 1
    simp_all only

-- A more convenient pair of one-way lemmas extracted from the iff:

/-- If `shiftR? r n = some r'`, then every coeff was divisible by `2^n`. -/
lemma shiftR?_some_divisible {k : ℕ} {r r' : Register k} {n : ℕ}
  (h : shiftR? r n = some r') :
  ∀ j, (r j) % ((2 : ℤ) ^ n) = 0 := by
  rcases (shiftR?_eq_some_iff).1 h with h'; intro j; exact (h' j).1

/-- If `shiftR? r n = some r'`, then `r'` is pointwise `r / 2^n`. -/
lemma shiftR?_some_value {k : ℕ} {r r' : Register k} {n : ℕ}
  (h : shiftR? r n = some r') :
  ∀ j, r' j = (r j) / ((2 : ℤ) ^ n) := by
  rcases (shiftR?_eq_some_iff).1 h with h'; intro j; exact (h' j).2

/-- Shifting the zero register to the right always succeeds and stays zero. -/
@[simp] lemma shiftR?_zero {k : ℕ} (n : ℕ) :
  shiftR? (zero k) n = some (zero k) := by
  unfold shiftR? zero
  simp

end Register

/-! =========================================================
    Section 5: State simp lemmas
========================================================= -/

namespace State
open Register

/-- Basis state: diagonal entry is `1`. -/
@[simp] lemma start_state_self {k : ℕ} (i : Fin k) :
  (start_state (k := k) i) i = 1 := by
  simp [start_state]

/-- Basis state: off-diagonal entries are `0`. -/
@[simp] lemma start_state_other {k : ℕ} (i j : Fin k) (h : j ≠ i) :
  (start_state (k := k) i) j = 0 := by
  simp [start_state, h]

@[simp] lemma setReg_self {k : ℕ} (σ : State k) (i : Fin k) (r : Register k) :
  setReg σ i r i = r := by
  simp [setReg]

@[simp] lemma setReg_other {k : ℕ} (σ : State k) (i j : Fin k) (r : Register k) (h : j ≠ i) :
  setReg σ i r j = σ j := by
  simp [setReg, h]

@[simp] lemma negateReg_self {k : ℕ} (σ : State k) (i : Fin k) :
  negateReg σ i i = Register.negate (σ i) := by
  simp [negateReg, setReg]

@[simp] lemma negateReg_other {k : ℕ} (σ : State k) (i j : Fin k) (h : j ≠ i) :
  negateReg σ i j = σ j := by
  simp [negateReg, setReg, h]

@[simp] lemma shiftLReg_self {k : ℕ} (σ : State k) (i : Fin k) (n : ℕ) :
  shiftLReg σ i n i = Register.shiftL (σ i) n := by
  simp [shiftLReg, setReg]

@[simp] lemma shiftLReg_other {k : ℕ} (σ : State k) (i j : Fin k) (n : ℕ) (h : j ≠ i) :
  shiftLReg σ i n j = σ j := by
  simp [shiftLReg, setReg, h]

/-- If `shiftRReg?` succeeds, it changes only the chosen register. -/
lemma shiftRReg?_ok_other {k : ℕ} {σ : State k} {i j : Fin k} {n : ℕ}
  {σ' : State k} (h : shiftRReg? σ i n = some σ') (hj : j ≠ i) :
  σ' j = σ j := by
  simp [shiftRReg?,shiftR?] at h
  split_ifs at h with hdiv
  · cases h;simp[setReg,hj]
  · simp at h

/-- And the updated register equals pointwise division by `2^n`. -/
lemma shiftRReg?_ok_self {k : ℕ} {σ : State k} {i : Fin k} {n : ℕ}
  {σ' : State k} (h : shiftRReg? σ i n = some σ') :
  σ' i = (fun j => (σ i j) / ((2 : ℤ) ^ n)) := by
  -- Extract the returned register from the definition
  simp [shiftRReg?,shiftR?] at h
  split_ifs at h with hdiv
  · cases h;simp[setReg]
  · simp at h

/-- Destination after `addScaledReg`. -/
@[simp] lemma addScaledReg_self {k : ℕ} (σ : State k)
  (dst src : Fin k) (negSrc : Bool) (n : ℕ) :
  addScaledReg σ dst src negSrc n dst
    = Register.addScaled (σ dst) (σ src) negSrc n := by
  simp [addScaledReg, setReg]

/-- Unaffected register in `addScaledReg`. -/
@[simp] lemma addScaledReg_other {k : ℕ} (σ : State k)
  (dst src j : Fin k) (negSrc : Bool) (n : ℕ) (hj : j ≠ dst) :
  addScaledReg σ dst src negSrc n j = σ j := by
  simp [addScaledReg, setReg, hj]

end State
