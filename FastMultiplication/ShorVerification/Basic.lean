import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

universe u
namespace Shor

/-!
# Shor verification core

This file contains the foundational register model, abstract gate language,
and semantic interfaces used by the Shor verification development.

The order is mostly dependency-driven:

1. Ordinary register structure and basis encodings.
2. Extended-register interpretation and two's-complement helpers.
3. Gate language and derived gate macros.
4. Abstract quantum semantics.
5. Gate-specific semantic fact classes.
6. General evaluation, norm, and overlap lemmas.
-/

/-! =========================================================
    Section 1: Ordinary registers, intervals, and splitting
========================================================= -/

structure Reg where
  lo   : ℕ
  size : ℕ
deriving DecidableEq, Repr

namespace Reg

/-- Exclusive upper endpoint of the register interval. -/
def hi (r : Reg) : ℕ :=
  r.lo + r.size

@[simp] theorem hi_eq (r : Reg) :
    r.hi = r.lo + r.size := rfl

@[simp] theorem lo_le_hi (r : Reg) :
    r.lo ≤ r.hi := by
  unfold hi
  omega

end Reg

/-- Two registers are disjoint if their intervals do not overlap. -/
def Disjoint (a b : Reg) : Prop :=
  a.hi ≤ b.lo ∨ b.hi ≤ a.lo

/-- Register length, i.e. number of qubits. -/
def regSize (r : Reg) : ℕ :=
  r.size

/-- Register cardinality `2^(regSize r)`. -/
def ASize (r : Reg) : ℕ :=
  2 ^ regSize r


@[simp] theorem regSize_mk (lo size : ℕ) :
    regSize ({ lo := lo, size := size } : Reg) = size := rfl

@[simp] theorem ASize_mk (lo size : ℕ) :
    ASize ({ lo := lo, size := size } : Reg) = 2 ^ size := rfl

/-- Construct a register from endpoints `[lo, hi)`, truncating malformed
    endpoint choices to size `0` when `hi < lo`.

    Prefer using `{ lo := ..., size := ... }` directly in new code.
-/
def Reg.ofBounds (lo hi : ℕ) : Reg :=
  { lo := lo, size := hi - lo }

@[simp] theorem Reg.ofBounds_lo (lo hi : ℕ) :
    (Reg.ofBounds lo hi).lo = lo := rfl

@[simp] theorem Reg.ofBounds_size (lo hi : ℕ) :
    (Reg.ofBounds lo hi).size = hi - lo := rfl

@[simp] theorem Reg.ofBounds_hi_of_le {lo hi : ℕ} (h : lo ≤ hi) :
    (Reg.ofBounds lo hi).hi = hi := by
  unfold Reg.ofBounds Reg.hi
  simp
  omega

/-- A one-qubit register at index `q`. -/
def qubitReg (q : ℕ) : Reg :=
  { lo := q, size := 1 }


/-- Extend a register by one high qubit. -/
def extendHi (r : Reg) : Reg :=
  { lo := r.lo, size := r.size + 1 }

/-- List of qubit indices in a register. -/
def regQubits (r : Reg) : List ℕ :=
  (List.range r.size).map (fun k => r.lo + k)

/-- A valid split point of a register. -/
abbrev SplitPoint (r : Reg) : Type :=
  { m : ℕ // m ≤ regSize r }

/-- Left part of a valid split. -/
def splitLeft (r : Reg) (m : SplitPoint r) : Reg :=
  { lo := r.lo, size := m.1 }

/-- Right part of a valid split. -/
def splitRight (r : Reg) (m : SplitPoint r) : Reg :=
  { lo := r.lo + m.1, size := r.size - m.1 }

@[simp] theorem splitLeft_size (r : Reg) (m : SplitPoint r) :
    regSize (splitLeft r m) = m.1 := rfl

@[simp] theorem splitRight_size (r : Reg) (m : SplitPoint r) :
    regSize (splitRight r m) = r.size - m.1 := rfl

@[simp] theorem splitLeft_lo (r : Reg) (m : SplitPoint r) :
    (splitLeft r m).lo = r.lo := rfl

@[simp] theorem splitRight_lo (r : Reg) (m : SplitPoint r) :
    (splitRight r m).lo = r.lo + m.1 := rfl

theorem splitLeft_splitRight_disjoint (r : Reg) (m : SplitPoint r) :
    Disjoint (splitLeft r m) (splitRight r m) := by
  unfold Disjoint splitLeft splitRight Reg.hi
  simp

/--
`RegEncoding` is the basis-level interface for ordinary finite registers.
It specifies reads, writes, bit observations, register extensionality, and
split/register-locality laws used throughout later semantic proofs.
-/
class RegEncoding (Basis : Type u) where
  toNat    : Reg → Basis → ℕ
  writeNat : Reg → ℕ → Basis → Basis
  bit      : ℕ → Basis → Bool

  toNat_writeNat_of_lt :
    ∀ r v b,
      v < ASize r →
      toNat r (writeNat r v b) = v

  writeNat_toNat :
    ∀ r b,
      writeNat r (toNat r b) b = b

  toNat_lt_ASize :
    ∀ r b,
      toNat r b < ASize r

  basis_ext :
    ∀ b1 b2 : Basis,
      (∀ q, bit q b1 = bit q b2) → b1 = b2

  bit_writeNat_in :
    ∀ r v b1 b2 q,
      r.lo ≤ q →
      q < r.hi →
      bit q (writeNat r v b1) = bit q (writeNat r v b2)

  bit_writeNat_out :
    ∀ r v b q,
      q < r.lo ∨ r.hi ≤ q →
      bit q (writeNat r v b) = bit q b

  toNat_left_write_right :
    ∀ (left right : Reg),
      Disjoint left right →
      ∀ b yR,
        toNat left (writeNat right yR b) = toNat left b

  toNat_right_write_left :
    ∀ (left right : Reg),
      Disjoint left right →
      ∀ b yL,
        toNat right (writeNat left yL b) = toNat right b

  writeNat_split :
    ∀ (r : Reg) (m : SplitPoint r) (k0 k1 : ℕ) (b : Basis),
      let left  : Reg := splitLeft r m
      let right : Reg := splitRight r m
      k1 < ASize left →
      k0 < ASize right →
      writeNat r (k1 + (ASize left) * k0) b
        =
      writeNat right k0 (writeNat left k1 b)

  toNat_split :
    ∀ (r : Reg) (m : SplitPoint r) (b : Basis),
      let left  : Reg := splitLeft r m
      let right : Reg := splitRight r m
      toNat r b =
        toNat left b + (ASize left) * toNat right b

  bit_eq_testBit_toNat :
    ∀ r b q,
      r.lo ≤ q →
      q < r.hi →
      bit q b = Nat.testBit (toNat r b) (q - r.lo)
/-! =========================================================
    Section 2: Register-encoding lemmas and extended registers
========================================================= -/

/-- A register together with a semantic high-bit extension budget. -/
structure ExtReg where
  base  : Reg
  extra : ℕ
deriving DecidableEq, Repr

namespace ExtReg

def ofReg (r : Reg) : ExtReg :=
  { base := r, extra := 0 }

def width (e : ExtReg) : ℕ :=
  regSize e.base + e.extra

def addExtra (e : ExtReg) (n : ℕ) : ExtReg :=
  { base := e.base, extra := e.extra + n }

def CtrlDisjoint (ctrl : ℕ) (x z : ExtReg) : Prop :=
  Disjoint (qubitReg ctrl) x.base ∧
  Disjoint (qubitReg ctrl) z.base

@[simp] theorem addExtra_base (e : ExtReg) (n : ℕ) :
    (addExtra e n).base = e.base := rfl

@[simp] theorem addExtra_extra (e : ExtReg) (n : ℕ) :
    (addExtra e n).extra = e.extra + n := rfl

@[simp] theorem width_addExtra (e : ExtReg) (n : ℕ) :
    width (addExtra e n) = width e + n := by
  unfold width addExtra regSize
  simp
  omega

end ExtReg

/-- Writes to disjoint registers commute. -/
lemma writeNat_comm_of_disjoint
  {Basis : Type u} [RegEncoding Basis]
  (left right : Reg) (hdisj : Disjoint left right)
  (yL yR : ℕ) (b : Basis) :
  RegEncoding.writeNat left yL (RegEncoding.writeNat right yR b)
    =
  RegEncoding.writeNat right yR (RegEncoding.writeNat left yL b) := by
  classical
  apply RegEncoding.basis_ext
  intro q
  by_cases hqL : left.lo ≤ q ∧ q < left.hi
  ·
    have : q < right.lo ∨ right.hi ≤ q := by
      cases hdisj with
      | inl h =>
          left
          have : q < right.lo := lt_of_lt_of_le hqL.2 h
          exact this
      | inr h =>
          right
          have : right.hi ≤ q := le_trans h hqL.1
          exact this
    have h_outR₁ :
        RegEncoding.bit q (RegEncoding.writeNat right yR b) = RegEncoding.bit q b :=
      RegEncoding.bit_writeNat_out (r := right) (v := yR) (b := b) (q := q) this
    have h_outR₂ :
        RegEncoding.bit q (RegEncoding.writeNat right yR (RegEncoding.writeNat left yL b))
          = RegEncoding.bit q (RegEncoding.writeNat left yL b) :=
      RegEncoding.bit_writeNat_out (r := right) (v := yR) (b := RegEncoding.writeNat left yL b) (q := q) this

    have h_inL :
      RegEncoding.bit q (RegEncoding.writeNat left yL (RegEncoding.writeNat right yR b))
        =
      RegEncoding.bit q (RegEncoding.writeNat left yL b) :=
      RegEncoding.bit_writeNat_in (r := left) (v := yL)
        (b1 := RegEncoding.writeNat right yR b) (b2 := b)
        (q := q) hqL.1 hqL.2

    calc
      RegEncoding.bit q (RegEncoding.writeNat left yL (RegEncoding.writeNat right yR b))
          = RegEncoding.bit q (RegEncoding.writeNat left yL b) := h_inL
      _   = RegEncoding.bit q (RegEncoding.writeNat right yR (RegEncoding.writeNat left yL b)) := by
              symm
              exact h_outR₂
  ·
    have h_outL : q < left.lo ∨ left.hi ≤ q := by
      have : ¬(left.lo ≤ q ∧ q < left.hi) := hqL
      exact (not_and_or.mp this) |> (fun h => by
        cases h with
        | inl h1 => exact Or.inl (lt_of_not_ge h1)
        | inr h2 => exact Or.inr (le_of_not_gt h2))

    have outL₁ :
        RegEncoding.bit q (RegEncoding.writeNat left yL (RegEncoding.writeNat right yR b))
          =
        RegEncoding.bit q (RegEncoding.writeNat right yR b) :=
      RegEncoding.bit_writeNat_out (r := left) (v := yL)
        (b := RegEncoding.writeNat right yR b) (q := q) h_outL

    have outL₂ :
        RegEncoding.bit q (RegEncoding.writeNat left yL b) = RegEncoding.bit q b :=
      RegEncoding.bit_writeNat_out (r := left) (v := yL) (b := b) (q := q) h_outL

    by_cases hqR : right.lo ≤ q ∧ q < right.hi
    ·
      have inR :
        RegEncoding.bit q (RegEncoding.writeNat right yR b)
          =
        RegEncoding.bit q (RegEncoding.writeNat right yR (RegEncoding.writeNat left yL b)) :=
        RegEncoding.bit_writeNat_in (r := right) (v := yR)
          (b1 := b) (b2 := RegEncoding.writeNat left yL b)
          (q := q) hqR.1 hqR.2
      calc
        RegEncoding.bit q (RegEncoding.writeNat left yL (RegEncoding.writeNat right yR b))
            = RegEncoding.bit q (RegEncoding.writeNat right yR b) := outL₁
        _   = RegEncoding.bit q (RegEncoding.writeNat right yR (RegEncoding.writeNat left yL b)) := inR
    ·
      have h_outR : q < right.lo ∨ right.hi ≤ q := by
        have : ¬(right.lo ≤ q ∧ q < right.hi) := hqR
        exact (not_and_or.mp this) |> (fun h => by
          cases h with
          | inl h1 => exact Or.inl (lt_of_not_ge h1)
          | inr h2 => exact Or.inr (le_of_not_gt h2))
      have outR₁ :
        RegEncoding.bit q (RegEncoding.writeNat right yR b) = RegEncoding.bit q b :=
        RegEncoding.bit_writeNat_out (r := right) (v := yR) (b := b) (q := q) h_outR
      have outR₂ :
        RegEncoding.bit q (RegEncoding.writeNat right yR (RegEncoding.writeNat left yL b))
          = RegEncoding.bit q (RegEncoding.writeNat left yL b) := by
        simpa using
          (RegEncoding.bit_writeNat_out (r := right) (v := yR)
            (b := RegEncoding.writeNat left yL b) (q := q) h_outR)
      calc
        RegEncoding.bit q (RegEncoding.writeNat left yL (RegEncoding.writeNat right yR b))
            = RegEncoding.bit q (RegEncoding.writeNat right yR b) := outL₁
        _   = RegEncoding.bit q b := outR₁
        _   = RegEncoding.bit q (RegEncoding.writeNat left yL b) := by simp [outL₂]
        _   = RegEncoding.bit q (RegEncoding.writeNat right yR (RegEncoding.writeNat left yL b)) := by
              simp [outR₂]

/-- Width-based two's-complement decoding. -/
def tcDecodeWidth : ℕ → ℕ → ℤ
  | 0, _ => 0
  | w + 1, n =>
      if _h : n < 2^w then
        (n : ℤ)
      else
        (n : ℤ) - ((2^(w + 1) : ℕ) : ℤ)

/--
`ExtRegEncoding` interprets an `ExtReg` as a wider two's-complement view of
its base register. The extra width is semantic; layout correctness is handled
by compiler-level invariants using this interface.
-/
class ExtRegEncoding (Basis : Type u) [RegEncoding Basis] where
  extToNat : ExtReg → Basis → ℕ

  extToNat_base :
    ∀ r b,
      extToNat (ExtReg.ofReg r) b = RegEncoding.toNat r b

  extToNat_write_disjoint :
    ∀ (e : ExtReg) (r : Reg),
      Disjoint e.base r →
      ∀ v b,
        extToNat e (RegEncoding.writeNat r v b) = extToNat e b

  extToNat_lt :
    ∀ e b,
      extToNat e b < 2 ^ (ExtReg.width e)

  extToNat_lowBits :
    ∀ e b,
      RegEncoding.toNat e.base b
        = extToNat e b % 2 ^ (regSize e.base)

namespace ExtReg

/-- Read an extended register as a natural number. -/
def toNat {Basis : Type u} [RegEncoding Basis] [ExtRegEncoding Basis] (e : ExtReg) (b : Basis) : ℕ :=
  ExtRegEncoding.extToNat e b

@[simp] theorem toNat_ofReg {Basis : Type u} [RegEncoding Basis] [ExtRegEncoding Basis] (r : Reg) (b : Basis) :
    ExtReg.toNat (ExtReg.ofReg r) b = RegEncoding.toNat r b := by
  simpa [ExtReg.toNat] using
    (ExtRegEncoding.extToNat_base (Basis := Basis) r b)

end ExtReg

namespace ExtRegEncoding

variable {Basis : Type u} [RegEncoding Basis] [ExtRegEncoding Basis]

/-- Signed interpretation of an extended register via two's-complement decoding. -/
def extToInt (e : ExtReg) (b : Basis) : ℤ :=
  tcDecodeWidth (ExtReg.width e) (ExtReg.toNat e b)

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

lemma bit_eq_of_toNat_eq_on_reg
  {Basis : Type u} [RegEncoding Basis]
  {r : Reg} {b1 b2 : Basis} {q : ℕ}
  (hNat : RegEncoding.toNat r b1 = RegEncoding.toNat r b2)
  (hqlo : r.lo ≤ q) (hqhi : q < r.hi) :
  RegEncoding.bit q b1 = RegEncoding.bit q b2 := by
  calc
    RegEncoding.bit q b1
        = RegEncoding.bit q (RegEncoding.writeNat r (RegEncoding.toNat r b1) b1) := by
            rw [RegEncoding.writeNat_toNat]
    _   = RegEncoding.bit q (RegEncoding.writeNat r (RegEncoding.toNat r b1) b2) := by
            exact RegEncoding.bit_writeNat_in
              (r := r) (v := RegEncoding.toNat r b1)
              (b1 := b1) (b2 := b2) (q := q) hqlo hqhi
    _   = RegEncoding.bit q (RegEncoding.writeNat r (RegEncoding.toNat r b2) b2) := by
            rw [hNat]
    _   = RegEncoding.bit q b2 := by
            rw [RegEncoding.writeNat_toNat]

lemma hbit_of_ext
  {Basis : Type u} [RegEncoding Basis] [ExtRegEncoding Basis]
  (e : ExtReg) (b1 b2 : Basis) (q : ℕ)
  (hInt : ExtRegEncoding.extToInt e b1 = ExtRegEncoding.extToInt e b2)
  (hqlo : e.base.lo ≤ q) (hqhi : q < e.base.hi) :
  RegEncoding.bit q b1 = RegEncoding.bit q b2 := by
  have hExtNat :
      ExtRegEncoding.extToNat e b1 = ExtRegEncoding.extToNat e b2 := by
    apply tcDecodeWidth_inj_of_lt
    · simpa [ExtRegEncoding.extToInt, ExtReg.toNat] using
        (ExtRegEncoding.extToNat_lt e b1)
    · simpa [ExtRegEncoding.extToInt, ExtReg.toNat] using
        (ExtRegEncoding.extToNat_lt e b2)
    · simpa [ExtRegEncoding.extToInt, ExtReg.toNat] using hInt

  have hBaseNat :
      RegEncoding.toNat e.base b1 = RegEncoding.toNat e.base b2 := by
    calc
      RegEncoding.toNat e.base b1
          = ExtRegEncoding.extToNat e b1 % 2 ^ (regSize e.base) := by
              simpa [ExtReg.toNat] using
                (ExtRegEncoding.extToNat_lowBits e b1)
      _   = ExtRegEncoding.extToNat e b2 % 2 ^ (regSize e.base) := by
              rw [hExtNat]
      _   = RegEncoding.toNat e.base b2 := by
              symm
              simpa [ExtReg.toNat] using
                (ExtRegEncoding.extToNat_lowBits e b2)

  exact bit_eq_of_toNat_eq_on_reg hBaseNat hqlo hqhi

end ExtRegEncoding

/-! =========================================================
    Section 3: Gate language and derived gate macros
========================================================= -/

/--
Abstract gate language used by the verification layer. Low-level gates such
as `Prim` coexist with structured arithmetic, QFT, phase-product, extension,
and deallocation gates.
-/
inductive Gate : Type
  | id : Gate
  | seq : Gate → Gate → Gate
  | adj : Gate → Gate
  | H : ℕ → Gate
  | X : ℕ → Gate
  | QFT : Reg → Gate
  | RadixReverse : (r : Reg) → (m : ℕ) → Gate
  | SignedPhaseProd  : (phi : Real) → (x z : ExtReg) → Gate
  | CSignedPhaseProd : (ctrl : ℕ) → (phi : Real) → (x z : ExtReg) → Gate
  | Prim : String → List ℕ → Gate
  | ShiftL    : (r : ExtReg) → (n : ℕ) → Gate
  | ShiftR    : (r : ExtReg) → (n : ℕ) → Gate
  | Negate    : (r : ExtReg) → Gate
  | AddScaled : (dst src : ExtReg) → (negSrc : Bool) → (shift : ℕ) → Gate
  | zeroExtend : (r : ExtReg) → (n : ℕ) → Gate
  | signExtend : (r : ExtReg) → (n : ℕ) → Gate
  | zeroDealloc : (r : ExtReg) → (n : ℕ) → Gate
  | signDealloc : (r : ExtReg) → (n : ℕ) → Gate

def radixReverseIndex (r : Reg) (m : ℕ) (hm : m ≤ regSize r) (kL kH : ℕ) : ℕ :=
  let sp : SplitPoint r := ⟨m, hm⟩
  let right := splitRight r sp
  (ASize right) * kL + kH

namespace Gate

infixr:80 " ;; " => Gate.seq
prefix:90 "†" => Gate.adj

def unsignedView (r : Reg) : ExtReg :=
  ExtReg.addExtra (ExtReg.ofReg r) 1

def PhaseProd
    (phi : Real) (x z : Reg) : Gate :=
  Gate.zeroExtend (ExtReg.ofReg x) 1 ;;
  Gate.zeroExtend (ExtReg.ofReg z) 1 ;;
  Gate.SignedPhaseProd phi (unsignedView x) (unsignedView z) ;;
  Gate.zeroDealloc (ExtReg.ofReg z) 1 ;;
  Gate.zeroDealloc (ExtReg.ofReg x) 1

def CPhaseProd
    (ctrl : ℕ) (phi : Real) (x z : Reg) : Gate :=
  Gate.zeroExtend (ExtReg.ofReg x) 1 ;;
  Gate.zeroExtend (ExtReg.ofReg z) 1 ;;
  Gate.CSignedPhaseProd ctrl phi (unsignedView x) (unsignedView z) ;;
  Gate.zeroDealloc (ExtReg.ofReg z) 1 ;;
  Gate.zeroDealloc (ExtReg.ofReg x) 1

end Gate

/-! =========================================================
    Section 4: QFT phase helpers
========================================================= -/

/-- Standard QFT phase schedule. -/
noncomputable def qftPhi (m : ℕ) : ℝ := (2 * Real.pi) / (2^m)

/-- Primitive `N`-th root of unity `exp(2πi/N)`. -/
noncomputable def ω (N : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))

/-- Power of the primitive root `ω N`. -/
noncomputable def ωPow (N k : ℕ) : ℂ :=
  (ω N) ^ k

/-- QFT phase factor `ω_N^(x*y)`. -/
noncomputable def qftPhase (N x y : ℕ) : ℂ :=
  ωPow N (x * y)

/-! =========================================================
    Section 5: Abstract quantum semantics
========================================================= -/

/--
Abstract Hilbert-space semantics for gates. The semantic facts below add
constructor-specific behavior on top of this linear/isometric interface.
-/
class QSemantics where
  Basis : Type u
  State : Type u

  [instNormed : NormedAddCommGroup State]
  [instIP     : InnerProductSpace ℂ State]

  ket   : Basis → State
  eval  : Gate → State → State

  eval_id  : ∀ ψ, eval Gate.id ψ = ψ
  eval_seq : ∀ U V ψ, eval (U ;; V) ψ = eval V (eval U ψ)

  inner_preserved : ∀ U ψ φ, inner ℂ (eval U ψ) (eval U φ) = inner ℂ ψ φ

  eval_zero : ∀ U, eval U 0 = 0
  eval_add  : ∀ U ψ φ, eval U (ψ + φ) = eval U ψ + eval U φ
  eval_smul : ∀ U (a : ℂ) ψ, eval U (a • ψ) = a • eval U ψ

  hsub : ∀ U ψ φ, eval U (ψ - φ) = eval U ψ - eval U φ

  state_induction :
    ∀ (P : State → Prop),
      P 0 →
      (∀ ψ φ, P ψ → P φ → P (ψ + φ)) →
      (∀ (a : ℂ) ψ, P ψ → P (a • ψ)) →
      (∀ b : Basis, P (ket b)) →
      ∀ ψ, P ψ

  tensor : State → State → State

  tensor_add_left  : ∀ ψ₁ ψ₂ φ, tensor (ψ₁ + ψ₂) φ = tensor ψ₁ φ + tensor ψ₂ φ
  tensor_add_right : ∀ ψ φ₁ φ₂, tensor ψ (φ₁ + φ₂) = tensor ψ φ₁ + tensor ψ φ₂
  tensor_smul_left : ∀ (a : ℂ) ψ φ, tensor (a • ψ) φ = a • tensor ψ φ
  tensor_smul_right: ∀ (a : ℂ) ψ φ, tensor ψ (a • φ) = a • tensor ψ φ

  inner_tensor :
    ∀ ψ₁ ψ₂ φ₁ φ₂,
      inner ℂ (tensor ψ₁ φ₁) (tensor ψ₂ φ₂)
        = (inner ℂ ψ₁ ψ₂) * (inner ℂ φ₁ φ₂)

  ket_ne_zero (b : Basis) :
    ket b ≠ 0

  ket_inj : Function.Injective ket

  ket_inner_eq_of_eq :
    ∀ {b₁ b₂ : Basis},
      b₁ = b₂ →
      inner ℂ (ket b₁) (ket b₂) = (1 : ℂ)

  ket_inner_eq_zero_of_ne :
    ∀ {b₁ b₂ : Basis},
      b₁ ≠ b₂ →
      inner ℂ (ket b₁) (ket b₂) = 0

  eval_adj_apply :
    ∀ (U : Gate) (ψ : State),
      eval (Gate.adj U) (eval U ψ) = ψ

  eval_apply_adj :
    ∀ (U : Gate) (ψ : State),
      eval U (eval (Gate.adj U) ψ) = ψ



open QSemantics


attribute [instance] QSemantics.instNormed
attribute [instance] QSemantics.instIP

lemma ket_inner_self
    (qs : QSemantics)
    (b : qs.Basis) :
    inner ℂ (qs.ket b) (qs.ket b) = (1 : ℂ) := by
  exact qs.ket_inner_eq_of_eq rfl

lemma ket_inner_ne
    (qs : QSemantics)
    {b₁ b₂ : qs.Basis}
    (h : b₁ ≠ b₂) :
    inner ℂ (qs.ket b₁) (qs.ket b₂) = 0 := by
  exact qs.ket_inner_eq_zero_of_ne h

lemma ket_norm_one
    (qs : QSemantics)
    (b : qs.Basis) :
    ‖qs.ket b‖ = 1 := by
  have hinner :
      inner ℂ (qs.ket b) (qs.ket b) = (1 : ℂ) :=
    ket_inner_self qs b

  have hsq :
      ‖qs.ket b‖ ^ 2 = (1 : ℝ) := by
    calc
      ‖qs.ket b‖ ^ 2
          = Complex.re (inner ℂ (qs.ket b) (qs.ket b)) := by
              simpa using
                (norm_sq_eq_re_inner (𝕜 := ℂ) (qs.ket b))
      _ = 1 := by
              simp at hinner; cases hinner<;> rename_i h<;> simp[h]

  have hnonneg : 0 ≤ ‖qs.ket b‖ := norm_nonneg _

  have hfactor :
      (‖qs.ket b‖ - 1) * (‖qs.ket b‖ + 1) = 0 := by
    nlinarith

  have hplus_ne :
      ‖qs.ket b‖ + 1 ≠ 0 := by
    nlinarith

  have hminus :
      ‖qs.ket b‖ - 1 = 0 := by
    rcases mul_eq_zero.mp hfactor with h | h
    · exact h
    · exfalso
      exact hplus_ne h

  nlinarith
/-! =========================================================
    Section 6: Two's-complement modular arithmetic helpers
========================================================= -/

def tcModWidth (w : ℕ) (z : ℤ) : ℕ :=
  Int.toNat (z % ((2^w : ℕ) : ℤ))

def tcWrapInt (w : ℕ) (z : ℤ) : ℤ :=
  tcDecodeWidth w (tcModWidth w z)

def signedLo (w : ℕ) : ℤ :=
  -(((2^(w-1) : ℕ) : ℤ))

def signedHi (w : ℕ) : ℤ :=
  (((2^(w-1) : ℕ) : ℤ))

def tcModExt (e : ExtReg) (z : ℤ) : ℕ :=
  tcModWidth (ExtReg.width e) z

def signedMin (w : ℕ) : ℤ :=
  -(((2^(w-1) : ℕ) : ℤ))

/-- Exclusive upper bound of the signed `w`-bit two's-complement range. -/
def signedMax (w : ℕ) : ℤ :=
  (((2^(w-1) : ℕ) : ℤ))

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

/-! =========================================================
    Section 7: Gate-specific semantic fact classes
========================================================= -/

/-- QFT-specific semantic facts. -/
class QFTSemantics
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [ExtRegEncoding qs.Basis] : Type where

  eval_QFT_size0 :
    ∀ (r : Reg) (ψ : qs.State),
      regSize r = 0 →
      qs.eval (Gate.QFT r) ψ = qs.eval Gate.id ψ

  eval_QFT_size1 :
    ∀ (r : Reg) (ψ : qs.State),
      regSize r = 1 →
      qs.eval (Gate.QFT r) ψ = qs.eval (Gate.H r.lo) ψ

  eval_QFT_ket :
    ∀ (r : Reg) (b : qs.Basis),
      qs.eval (Gate.QFT r) (qs.ket b)
        =
      ((1 / Real.sqrt ((2^(regSize r) : ℕ) : ℝ) : ℂ)) •
        ∑ y : Fin (2^(regSize r)),
          (qftPhase (2^(regSize r)) (RegEncoding.toNat r b) y.1) •
            qs.ket (RegEncoding.writeNat r y.1 b)

  eval_adj_QFT_ket :
    ∀ (r : Reg) (b : qs.Basis),
      qs.eval (Gate.adj (Gate.QFT r)) (qs.ket b)
        =
      ((1 / Real.sqrt ((ASize r : ℕ) : ℝ) : ℂ)) •
        ∑ y : Fin (ASize r),
          star (qftPhase (ASize r) (RegEncoding.toNat r b) y.1) •
            qs.ket (RegEncoding.writeNat r y.1 b)

class HadamardSemantics
    (qs : QSemantics)
    [RegEncoding qs.Basis] : Type where

  eval_H_ket :
    ∀ (q : ℕ) (b : qs.Basis),
      qs.eval (Gate.H q) (qs.ket b)
        =
      ((1 / Real.sqrt (2 : ℝ) : ℂ)) •
        (
          qs.ket (RegEncoding.writeNat (qubitReg q) 0 b)
          +
          (if RegEncoding.bit q b then (-1 : ℂ) else 1) •
            qs.ket (RegEncoding.writeNat (qubitReg q) 1 b)
        )

class PauliXSemantics
    (qs : QSemantics)
    [RegEncoding qs.Basis] : Type where

  eval_X_ket :
    ∀ (q : ℕ) (b : qs.Basis),
      qs.eval (Gate.X q) (qs.ket b)
        =
      qs.ket
        (RegEncoding.writeNat
          (qubitReg q)
          (if RegEncoding.bit q b then 0 else 1)
          b)

  eval_X_low_zero_reg_ket :
    ∀ (r : Reg) (b : qs.Basis),
      0 < regSize r →
      RegEncoding.toNat r b = 0 →
      qs.eval (Gate.X r.lo) (qs.ket b)
        =
      qs.ket (RegEncoding.writeNat r 1 b)

class RegisterHadamardSemantics
    (qs : QSemantics)
    [RegEncoding qs.Basis] : Type where

  eval_Hreg_ket :
    ∀ (r : Reg) (b : qs.Basis),
      ∃ α : Fin (ASize r) → ℂ,
        qs.eval
            ((regQubits r).foldl
              (fun acc q => Gate.seq (Gate.H q) acc)
              Gate.id)
            (qs.ket b)
          =
        ∑ t : Fin (ASize r),
          α t • qs.ket (RegEncoding.writeNat r t.1 b)

class RadixReverseSemantics
  (qs : QSemantics)
  [RegEncoding qs.Basis] : Type where

  eval_RadixReverse_ket :
    ∀ (r : Reg) (m : ℕ) (hm : m ≤ regSize r)
      (b : qs.Basis) (kL kH : ℕ),
      let sp : SplitPoint r := ⟨m, hm⟩
      let left  : Reg := splitLeft r sp
      let right : Reg := splitRight r sp
      kL < ASize left →
      kH < ASize right →
      qs.eval (Gate.RadixReverse r m)
        (qs.ket
          (RegEncoding.writeNat left kL
            (RegEncoding.writeNat right kH b)))
      =
      qs.ket
        (RegEncoding.writeNat r
          (radixReverseIndex r m hm kL kH)
          b)

/-- Signed phase-product semantic facts. -/
class PhaseSemantics
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [ExtRegEncoding qs.Basis] : Type where

  eval_SignedPhaseProd_ket :
    ∀ (phi : ℝ) (x z : ExtReg) (b : qs.Basis),
      qs.eval (Gate.SignedPhaseProd phi x z) (qs.ket b)
        =
      (Complex.exp
        (phi * Complex.I *
          (((ExtRegEncoding.extToInt x b : ℤ) : ℂ) *
           (((ExtRegEncoding.extToInt z b : ℤ) : ℂ))))) •
        qs.ket b

  eval_CSignedPhaseProd_ket :
    ∀ (ctrl : ℕ) (phi : ℝ) (x z : ExtReg) (b : qs.Basis),
      qs.eval (Gate.CSignedPhaseProd ctrl phi x z) (qs.ket b)
        =
      if RegEncoding.bit ctrl b then
        (Complex.exp
          (phi * Complex.I *
            (((ExtRegEncoding.extToInt x b : ℤ) : ℂ) *
             (((ExtRegEncoding.extToInt z b : ℤ) : ℂ))))) •
          qs.ket b
      else
        qs.ket b

/-- Zero/sign extension and deallocation semantic facts. -/
class ExtensionSemantics
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [ExtRegEncoding qs.Basis] : Type where

  eval_zeroExtend_ket :
    ∀ (r : ExtReg) (n : ℕ) (b : qs.Basis),
      ∃ b' : qs.Basis,
        qs.eval (Gate.zeroExtend r n) (qs.ket b) = qs.ket b' ∧
        ExtReg.toNat r b' = ExtReg.toNat r b ∧
        ExtReg.toNat (ExtReg.addExtra r n) b'
          = ExtReg.toNat r b ∧
        (∀ e : ExtReg,
          Disjoint e.base r.base →
          ExtReg.toNat e b' = ExtReg.toNat e b)

  eval_signExtend_ket :
    ∀ (r : ExtReg) (n : ℕ) (b : qs.Basis),
      ∃ b' : qs.Basis,
        qs.eval (Gate.signExtend r n) (qs.ket b) = qs.ket b' ∧
        ExtReg.toNat r b' = ExtReg.toNat r b ∧
        ExtRegEncoding.extToInt (ExtReg.addExtra r n) b'
          = ExtRegEncoding.extToInt r b ∧
        (∀ e : ExtReg,
          Disjoint e.base r.base →
          ExtReg.toNat e b' = ExtReg.toNat e b)

  eval_zeroExtend_zeroDealloc :
    ∀ r n ψ,
      qs.eval (Gate.zeroExtend r n ;; Gate.zeroDealloc r n) ψ = ψ

  eval_signExtend_signDealloc :
    ∀ r n ψ,
      qs.eval (Gate.signExtend r n ;; Gate.signDealloc r n) ψ = ψ

lemma tcDecodeWidth_succ_eq_of_lt {w n : ℕ} (h : n < 2 ^ w) :
  tcDecodeWidth (w + 1) n = (n : ℤ) := by
  simp [tcDecodeWidth, h]

lemma zeroExtend_extToInt
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [ExtRegEncoding qs.Basis]
  [ExtensionSemantics qs]
  (r : ExtReg) (n : ℕ) (b b' : qs.Basis)
  (hn : 0 < n)
  (hEval : qs.eval (Gate.zeroExtend r n) (qs.ket b) = qs.ket b') :
  ExtRegEncoding.extToInt (ExtReg.addExtra r n) b'
    = (ExtReg.toNat r b : ℤ) := by
  rcases ExtensionSemantics.eval_zeroExtend_ket
      (qs := qs) (r := r) (n := n) (b := b) with
    ⟨bout, hBoutEval, _hself, hwide, _hloc⟩

  have hket : Function.Injective qs.ket := qs.ket_inj
  have hbout : bout = b' := by
    apply hket
    simpa [hBoutEval] using hEval
  subst hbout

  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn) with ⟨m, rfl⟩

  have hlt0 : ExtReg.toNat r b < 2 ^ (ExtReg.width r) := by
    simpa [ExtReg.toNat] using
      ExtRegEncoding.extToNat_lt (Basis := qs.Basis) (e := r) (b := b)

  have hle :
      2 ^ (ExtReg.width r) ≤ 2 ^ (ExtReg.width r + m) := by
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) (Nat.le_add_right _ _)

  have hlt :
      ExtReg.toNat r b < 2 ^ (ExtReg.width r + m) := by
    exact lt_of_lt_of_le hlt0 hle

  have hdecode :
      tcDecodeWidth (ExtReg.width r + (m + 1)) (ExtReg.toNat r b)
        = (ExtReg.toNat r b : ℤ) := by
    have :=
      tcDecodeWidth_succ_eq_of_lt
        (w := ExtReg.width r + m)
        (n := ExtReg.toNat r b)
        hlt
    simpa [Nat.add_assoc] using this

  unfold ExtRegEncoding.extToInt
  change tcDecodeWidth (ExtReg.width (ExtReg.addExtra r (m + 1)))
      (ExtRegEncoding.extToNat (ExtReg.addExtra r (m + 1)) bout)
    = (ExtRegEncoding.extToNat r b : ℤ)
  simp [ExtReg.width_addExtra]
  calc
  tcDecodeWidth (r.width + (m + 1))
      (ExtRegEncoding.extToNat (r.addExtra (m + 1)) bout)
    = tcDecodeWidth (r.width + (m + 1)) (ExtRegEncoding.extToNat r b) := by
        simpa [ExtReg.toNat] using congrArg
          (tcDecodeWidth (r.width + (m + 1))) hwide
  _ = ↑(ExtRegEncoding.extToNat r b) := hdecode

lemma zeroExtend_ofReg_extToInt
  (qs : QSemantics) [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [ExtensionSemantics qs]
  (r : Reg) (b b' : qs.Basis) (n : ℕ) (hn : n > 0)
  (heval : qs.eval (Gate.zeroExtend (ExtReg.ofReg r) n) (qs.ket b) = qs.ket b') :
  ExtRegEncoding.extToInt (ExtReg.addExtra (ExtReg.ofReg r) n) b'
    = (RegEncoding.toNat r b : ℤ) := by
  rcases ExtensionSemantics.eval_zeroExtend_ket
      (qs := qs) (r := ExtReg.ofReg r) (n := n) (b := b) with
    ⟨bout, heval', _, hwide, _⟩
  have hbout : bout = b' := qs.ket_inj (by rw [← heval', ← heval])
  subst hbout
  unfold ExtRegEncoding.extToInt ExtReg.toNat at *
  rw [hwide]
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn) with ⟨m, rfl⟩
  unfold ExtRegEncoding.extToNat
  simp [ExtReg.width, ExtReg.ofReg, regSize]
  have hlt :=
    ExtRegEncoding.extToNat_lt (Basis := qs.Basis) (e := ExtReg.ofReg r) (b := b)
  simp [ExtReg.width, ExtReg.ofReg, regSize] at hlt
  have hpow :
      RegEncoding.toNat r b < 2 ^ (regSize r + m) := by
    calc
      RegEncoding.toNat r b < 2 ^ regSize r := by
        simp[regSize]
        have:=ExtRegEncoding.extToNat_base (Basis:=qs.Basis) r b
        simp[ExtReg.ofReg] at this
        aesop
      _ ≤ 2 ^ (regSize r + m) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right _ _)
  have:=ExtRegEncoding.extToNat_base (Basis:=qs.Basis) r b
  simp[ExtReg.ofReg] at this
  have htc:=tcDecodeWidth_succ_eq_of_lt hpow
  simp[regSize] at *
  simp[add_assoc] at *
  rw[← htc]
  unfold RegEncoding.toNat
  congr

lemma zeroExtend_preserves_disjoint_extToInt
  (qs : QSemantics) [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [ExtensionSemantics qs]
  (r e : ExtReg) (n : ℕ) (b b' : qs.Basis)
  (hdisj : Disjoint r.base e.base)
  (heval : qs.eval (Gate.zeroExtend r n) (qs.ket b) = qs.ket b') :
  ExtRegEncoding.extToInt e b' = ExtRegEncoding.extToInt e b := by
  rcases ExtensionSemantics.eval_zeroExtend_ket
      (qs := qs) (r := r) (n := n) (b := b) with
    ⟨bout, heval', _, _, hloc⟩
  have hbout : bout = b' := qs.ket_inj (by rw [← heval', ← heval])
  subst hbout
  unfold ExtRegEncoding.extToInt ExtReg.toNat
  have hdisj' : Disjoint e.base r.base := by
    cases hdisj with
    | inl h => exact Or.inr h
    | inr h => exact Or.inl h
  congr 1
  exact hloc e hdisj'

lemma signExtend_preserves_disjoint_extToInt
  (qs : QSemantics) [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [ExtensionSemantics qs]
  (r e : ExtReg) (n : ℕ) (b b' : qs.Basis)
  (hdisj : Disjoint r.base e.base)
  (heval : qs.eval (Gate.signExtend r n) (qs.ket b) = qs.ket b') :
  ExtRegEncoding.extToInt e b' = ExtRegEncoding.extToInt e b := by
  rcases ExtensionSemantics.eval_signExtend_ket
      (qs := qs) (r := r) (n := n) (b := b) with
    ⟨bout, heval', _, _, hloc⟩
  have hbout : bout = b' := qs.ket_inj (by rw [← heval', ← heval])
  subst hbout
  unfold ExtRegEncoding.extToInt ExtReg.toNat
  have hdisj' : Disjoint e.base r.base := by
    cases hdisj with
    | inl h => exact Or.inr h
    | inr h => exact Or.inl h
  congr 1
  exact hloc e hdisj'

/-- Arithmetic-gate semantic facts. -/
class ArithmeticSemantics
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [ExtRegEncoding qs.Basis] : Type where

  /-- Left shift is only specified when the exact result still fits in the
      same signed width. -/
  eval_ShiftL_ket_exact :
    ∀ (r : ExtReg) (n : ℕ) (b : qs.Basis),
      FitsSignedWidth (ExtReg.width r)
        (((2 : ℤ)^n) * ExtRegEncoding.extToInt r b) →
      ∃ b' : qs.Basis,
        qs.eval (Gate.ShiftL r n) (qs.ket b) = qs.ket b' ∧
        ExtRegEncoding.extToInt r b'
          = ((2 : ℤ)^n) * ExtRegEncoding.extToInt r b ∧
        (∀ e : ExtReg,
          Disjoint e.base r.base →
          ExtRegEncoding.extToInt e b' = ExtRegEncoding.extToInt e b)

  /-- Right shift is only specified when the current signed value is exactly
      divisible by `2^n`. -/
  eval_ShiftR_ket_exact :
    ∀ (r : ExtReg) (n : ℕ) (b : qs.Basis) (q : ℤ),
      ExtRegEncoding.extToInt r b = ((2 : ℤ)^n) * q →
      FitsSignedWidth (ExtReg.width r) q →
      ∃ b' : qs.Basis,
        qs.eval (Gate.ShiftR r n) (qs.ket b) = qs.ket b' ∧
        ExtRegEncoding.extToInt r b' = q ∧
        (∀ e : ExtReg,
          Disjoint e.base r.base →
          ExtRegEncoding.extToInt e b' = ExtRegEncoding.extToInt e b)

  /-- Negation is width-`w` modular additive inverse. -/
  eval_Negate_ket_mod :
    ∀ (r : ExtReg) (b : qs.Basis),
      ∃ b' : qs.Basis,
        qs.eval (Gate.Negate r) (qs.ket b) = qs.ket b' ∧
        ExtRegEncoding.extToInt r b'
          = tcWrapInt (ExtReg.width r) (- ExtRegEncoding.extToInt r b) ∧
        (∀ e : ExtReg,
          Disjoint e.base r.base →
          ExtRegEncoding.extToInt e b' = ExtRegEncoding.extToInt e b)

  /-- Scaled add updates `dst` modulo the destination width, preserves `src`,
      and preserves every other disjoint register.

      This is sound as a total modular operation because, for fixed `src`,
      addition into `dst` is bijective.
  -/
  eval_AddScaled_ket_mod :
    ∀ (dst src : ExtReg) (negSrc : Bool) (sh : ℕ) (b : qs.Basis),
      Disjoint dst.base src.base →
      ∃ b' : qs.Basis,
        qs.eval (Gate.AddScaled dst src negSrc sh) (qs.ket b) = qs.ket b' ∧
        ExtRegEncoding.extToInt dst b'
          =
          tcWrapInt (ExtReg.width dst)
            (ExtRegEncoding.extToInt dst b
              + (if negSrc then (-1 : ℤ) else 1)
                  * ((2 : ℤ)^sh)
                  * ExtRegEncoding.extToInt src b) ∧
        ExtRegEncoding.extToInt src b'
          = ExtRegEncoding.extToInt src b ∧
        (∀ e : ExtReg,
          Disjoint e.base dst.base →
          Disjoint e.base src.base →
          ExtRegEncoding.extToInt e b' = ExtRegEncoding.extToInt e b)

/-- Bundled semantic interface for all gate families used in this file. -/
class GateSemanticsFacts
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [ExtRegEncoding qs.Basis] :
  Type extends
    QFTSemantics qs,
    PhaseSemantics qs,
    ExtensionSemantics qs,
    ArithmeticSemantics qs,
    RadixReverseSemantics qs,
    HadamardSemantics qs,
    PauliXSemantics qs,
    RegisterHadamardSemantics qs where

  eval_Hreg_zero_eq_QFT :
    ∀ (r : Reg) (b : qs.Basis),
      RegEncoding.toNat r b = 0 →
      qs.eval
          ((regQubits r).foldl
            (fun acc q => Gate.seq (Gate.H q) acc)
            Gate.id)
          (qs.ket b)
        =
      qs.eval (Gate.QFT r) (qs.ket b)

namespace GateSemanticsFacts

variable {qs : QSemantics}
variable [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
variable [GateSemanticsFacts qs]

theorem eval_RadixReverse_split_ket
  (r : Reg) (m : ℕ) (hm : m ≤ regSize r) (b : qs.Basis)
  (kL kH : ℕ)
  (hkL : kL < ASize (splitLeft r ⟨m, hm⟩))
  (hkH : kH < ASize (splitRight r ⟨m, hm⟩)) :
  qs.eval (Gate.RadixReverse r m)
    (qs.ket
      (RegEncoding.writeNat (splitLeft r ⟨m, hm⟩) kL
        (RegEncoding.writeNat (splitRight r ⟨m, hm⟩) kH b)))
  =
  qs.ket
    (RegEncoding.writeNat r
      (radixReverseIndex r m hm kL kH)
      b) := by
  simpa [radixReverseIndex] using
    (RadixReverseSemantics.eval_RadixReverse_ket
      (qs := qs)
      (r := r) (m := m) (hm := hm) (b := b)
      (kL := kL) (kH := kH)
      hkL
      hkH)

theorem eval_PhaseProd_ket
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  (phi : ℝ) (x z : Reg) (b : qs.Basis)
  (hdisj : Disjoint x z) :
  qs.eval (Gate.PhaseProd phi x z) (qs.ket b) =
    Complex.exp
      (phi * Complex.I *
        ((RegEncoding.toNat x b) * (RegEncoding.toNat z b))) •
      qs.ket b := by
  have hdisj' : Disjoint z x := by
    cases hdisj with
    | inl h => exact Or.inr h
    | inr h => exact Or.inl h

  rw [Gate.PhaseProd]
  simp [qs.eval_seq]

  rcases ExtensionSemantics.eval_zeroExtend_ket
      (qs := qs) (r := ExtReg.ofReg x) (n := 1) (b := b) with
    ⟨b₁, hx_eval, hx_nat_self, hx_nat_wide, hx_loc⟩

  rcases ExtensionSemantics.eval_zeroExtend_ket
      (qs := qs) (r := ExtReg.ofReg z) (n := 1) (b := b₁) with
    ⟨b₂, hz_eval, hz_nat_self, hz_nat_wide, hz_loc⟩

  rw [hx_eval, hz_eval]
  rw [PhaseSemantics.eval_SignedPhaseProd_ket]
  rw [qs.eval_smul, qs.eval_smul]

  have hundo_z :
      qs.eval (Gate.zeroDealloc (ExtReg.ofReg z) 1) (qs.ket b₂) = qs.ket b₁ := by
    have h :=
      ExtensionSemantics.eval_zeroExtend_zeroDealloc
        (qs := qs) (r := ExtReg.ofReg z) (n := 1) (ψ := qs.ket b₁)
    rw [qs.eval_seq] at h
    rw [hz_eval] at h
    simpa using h

  have hundo_x :
      qs.eval (Gate.zeroDealloc (ExtReg.ofReg x) 1) (qs.ket b₁) = qs.ket b := by
    have h :=
      ExtensionSemantics.eval_zeroExtend_zeroDealloc
        (qs := qs) (r := ExtReg.ofReg x) (n := 1) (ψ := qs.ket b)
    rw [qs.eval_seq] at h
    rw [hx_eval] at h
    simpa using h

  rw [hundo_z, hundo_x]
  congr 3

  have hx_ext₁ :
      ExtRegEncoding.extToInt (Gate.unsignedView x) b₁ =
        (RegEncoding.toNat x b : ℤ) := by
    apply zeroExtend_ofReg_extToInt
    · simp
    · exact hx_eval

  have hz_ext₂ :
      ExtRegEncoding.extToInt (Gate.unsignedView z) b₂ =
        (RegEncoding.toNat z b₁ : ℤ) := by
    apply zeroExtend_ofReg_extToInt
    · simp
    · exact hz_eval

  have hz_same :
      RegEncoding.toNat z b₁ = RegEncoding.toNat z b := by
    have h :=
      hx_loc (ExtReg.ofReg z) hdisj'
    simpa using h

  have hx_ext₂ :
      ExtRegEncoding.extToInt (Gate.unsignedView x) b₂ =
        ExtRegEncoding.extToInt (Gate.unsignedView x) b₁ := by
    exact
      zeroExtend_preserves_disjoint_extToInt
        (qs := qs)
        (r := ExtReg.ofReg z)
        (e := Gate.unsignedView x)
        (n := 1)
        (b := b₁)
        (b' := b₂)
        (by
          simpa [Gate.unsignedView, ExtReg.addExtra, ExtReg.ofReg] using hdisj')
        hz_eval

  simp [hx_ext₁, hx_ext₂, hz_ext₂, hz_same]

private lemma zeroExtend_preserves_bit
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [ExtensionSemantics qs]
    (r : ExtReg)
    (n : ℕ)
    (b b' : qs.Basis)
    (q : ℕ)
    (hEval :
      qs.eval (Gate.zeroExtend r n) (qs.ket b) = qs.ket b') :
    RegEncoding.bit q b' = RegEncoding.bit q b := by
  classical
  rcases ExtensionSemantics.eval_zeroExtend_ket
      (qs := qs) (r := r) (n := n) (b := b) with
    ⟨bout, hBoutEval, hself, _hwide, hloc⟩

  have hbout : bout = b' := by
    apply qs.ket_inj
    calc
      qs.ket bout
          = qs.eval (Gate.zeroExtend r n) (qs.ket b) := hBoutEval.symm
      _ = qs.ket b' := hEval
  subst bout

  by_cases hqin : r.base.lo ≤ q ∧ q < r.base.hi
  ·
    have hbase :
        RegEncoding.toNat r.base b' = RegEncoding.toNat r.base b := by
      calc
        RegEncoding.toNat r.base b'
            = ExtReg.toNat r b' % 2 ^ regSize r.base := by
                simpa [ExtReg.toNat] using
                  (ExtRegEncoding.extToNat_lowBits
                    (Basis := qs.Basis) r b')
        _ = ExtReg.toNat r b % 2 ^ regSize r.base := by
              rw [hself]
        _ = RegEncoding.toNat r.base b := by
              symm
              simpa [ExtReg.toNat] using
                (ExtRegEncoding.extToNat_lowBits
                  (Basis := qs.Basis) r b)

    exact
      ExtRegEncoding.bit_eq_of_toNat_eq_on_reg
        hbase hqin.1 hqin.2

  ·
    have hqout : q < r.base.lo ∨ r.base.hi ≤ q := by
      rcases not_and_or.mp hqin with hqlo | hqhi
      · exact Or.inl (lt_of_not_ge hqlo)
      · exact Or.inr (le_of_not_gt hqhi)

    have hqdisj : Disjoint (qubitReg q) r.base := by
      unfold Shor.Disjoint qubitReg Reg.hi
      simp
      simp_all only [Reg.hi_eq, not_and, not_lt]

    have hqNat :
        RegEncoding.toNat (qubitReg q) b'
          =
        RegEncoding.toNat (qubitReg q) b := by
      simpa using
        (hloc (ExtReg.ofReg (qubitReg q)) hqdisj)

    exact
      ExtRegEncoding.bit_eq_of_toNat_eq_on_reg
        hqNat
        (by simp [qubitReg])
        (by simp [qubitReg, Reg.hi])

lemma eval_CSignedPhaseProd_ket_as_if_SignedPhaseProd
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [PhaseSemantics qs]
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : ExtReg)
    (b : qs.Basis) :
    qs.eval (Gate.CSignedPhaseProd ctrl phi x z) (qs.ket b)
      =
    if RegEncoding.bit ctrl b then
      qs.eval (Gate.SignedPhaseProd phi x z) (qs.ket b)
    else
      qs.ket b := by
  by_cases hctrl : RegEncoding.bit ctrl b
  ·
    rw [PhaseSemantics.eval_CSignedPhaseProd_ket]
    rw [if_pos hctrl, if_pos hctrl]
    exact
      (PhaseSemantics.eval_SignedPhaseProd_ket
        (qs := qs) phi x z b).symm
  ·
    rw [PhaseSemantics.eval_CSignedPhaseProd_ket]
    rw [if_neg hctrl, if_neg hctrl]

private lemma eval_CPhaseProd_ket_eq_PhaseProd_of_ctrl
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : Reg)
    (b : qs.Basis)
    (hctrl : RegEncoding.bit ctrl b) :
    qs.eval (Gate.CPhaseProd ctrl phi x z) (qs.ket b)
      =
    qs.eval (Gate.PhaseProd phi x z) (qs.ket b) := by
  simp only [Gate.CPhaseProd, Gate.PhaseProd, qs.eval_seq]

  rcases ExtensionSemantics.eval_zeroExtend_ket
      (qs := qs) (r := ExtReg.ofReg x) (n := 1) (b := b) with
    ⟨b₁, hx_eval, _hx_self, _hx_wide, _hx_loc⟩

  rcases ExtensionSemantics.eval_zeroExtend_ket
      (qs := qs) (r := ExtReg.ofReg z) (n := 1) (b := b₁) with
    ⟨b₂, hz_eval, _hz_self, _hz_wide, _hz_loc⟩

  simp only [hx_eval, hz_eval]

  have hctrl₁ :
      RegEncoding.bit ctrl b₁ = RegEncoding.bit ctrl b :=
    zeroExtend_preserves_bit
      qs (ExtReg.ofReg x) 1 b b₁ ctrl hx_eval

  have hctrl₂eq :
      RegEncoding.bit ctrl b₂ = RegEncoding.bit ctrl b := by
    calc
      RegEncoding.bit ctrl b₂
          = RegEncoding.bit ctrl b₁ :=
        zeroExtend_preserves_bit
          qs (ExtReg.ofReg z) 1 b₁ b₂ ctrl hz_eval
      _ = RegEncoding.bit ctrl b := hctrl₁

  have hctrl₂ : RegEncoding.bit ctrl b₂ := by
    rw [hctrl₂eq]
    exact hctrl

  rw [eval_CSignedPhaseProd_ket_as_if_SignedPhaseProd]
  rw [if_pos hctrl₂]

private lemma eval_CPhaseProd_ket_eq_ket_of_not_ctrl
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : Reg)
    (b : qs.Basis)
    (hctrl : ¬ RegEncoding.bit ctrl b) :
    qs.eval (Gate.CPhaseProd ctrl phi x z) (qs.ket b)
      =
    qs.ket b := by
  simp only [Gate.CPhaseProd, qs.eval_seq]

  rcases ExtensionSemantics.eval_zeroExtend_ket
      (qs := qs) (r := ExtReg.ofReg x) (n := 1) (b := b) with
    ⟨b₁, hx_eval, _hx_self, _hx_wide, _hx_loc⟩

  rcases ExtensionSemantics.eval_zeroExtend_ket
      (qs := qs) (r := ExtReg.ofReg z) (n := 1) (b := b₁) with
    ⟨b₂, hz_eval, _hz_self, _hz_wide, _hz_loc⟩

  simp only [hx_eval, hz_eval]

  have hctrl₁ :
      RegEncoding.bit ctrl b₁ = RegEncoding.bit ctrl b :=
    zeroExtend_preserves_bit
      qs (ExtReg.ofReg x) 1 b b₁ ctrl hx_eval

  have hctrl₂eq :
      RegEncoding.bit ctrl b₂ = RegEncoding.bit ctrl b := by
    calc
      RegEncoding.bit ctrl b₂
          = RegEncoding.bit ctrl b₁ :=
        zeroExtend_preserves_bit
          qs (ExtReg.ofReg z) 1 b₁ b₂ ctrl hz_eval
      _ = RegEncoding.bit ctrl b := hctrl₁

  have hctrl₂ : ¬ RegEncoding.bit ctrl b₂ := by
    intro h
    apply hctrl
    rw [← hctrl₂eq]
    exact h

  rw [eval_CSignedPhaseProd_ket_as_if_SignedPhaseProd]
  rw [if_neg hctrl₂]

  have hundo_z :
      qs.eval (Gate.zeroDealloc (ExtReg.ofReg z) 1) (qs.ket b₂)
        =
      qs.ket b₁ := by
    have h :=
      ExtensionSemantics.eval_zeroExtend_zeroDealloc
        (qs := qs)
        (r := ExtReg.ofReg z)
        (n := 1)
        (ψ := qs.ket b₁)
    rw [qs.eval_seq, hz_eval] at h
    simpa using h

  have hundo_x :
      qs.eval (Gate.zeroDealloc (ExtReg.ofReg x) 1) (qs.ket b₁)
        =
      qs.ket b := by
    have h :=
      ExtensionSemantics.eval_zeroExtend_zeroDealloc
        (qs := qs)
        (r := ExtReg.ofReg x)
        (n := 1)
        (ψ := qs.ket b)
    rw [qs.eval_seq, hx_eval] at h
    simpa using h

  rw [hundo_z, hundo_x]

lemma eval_CPhaseProd_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (ctrl : ℕ)
    (phi : ℝ)
    (data work : Reg)
    (b : qs.Basis)
    (hdisj : Disjoint data work) :
    qs.eval (Gate.CPhaseProd ctrl phi data work) (qs.ket b)
      =
    (if RegEncoding.bit ctrl b then
        Complex.exp
          (phi * Complex.I *
            ((RegEncoding.toNat data b : ℂ) *
             (RegEncoding.toNat work b : ℂ)))
      else
        1) •
      qs.ket b := by
  by_cases hctrl : RegEncoding.bit ctrl b
  ·
    calc
      qs.eval (Gate.CPhaseProd ctrl phi data work) (qs.ket b)
          =
          qs.eval (Gate.PhaseProd phi data work) (qs.ket b) :=
        eval_CPhaseProd_ket_eq_PhaseProd_of_ctrl
          qs ctrl phi data work b hctrl
      _ =
          Complex.exp
            (phi * Complex.I *
              ((RegEncoding.toNat data b : ℂ) *
               (RegEncoding.toNat work b : ℂ))) •
            qs.ket b := by
          simpa [Nat.cast_mul] using
            (GateSemanticsFacts.eval_PhaseProd_ket
              qs phi data work b hdisj)
      _ =
          (if RegEncoding.bit ctrl b then
              Complex.exp
                (phi * Complex.I *
                  ((RegEncoding.toNat data b : ℂ) *
                   (RegEncoding.toNat work b : ℂ)))
            else
              1) •
            qs.ket b := by
          simp [hctrl]

  ·
    calc
      qs.eval (Gate.CPhaseProd ctrl phi data work) (qs.ket b)
          =
          qs.ket b :=
        eval_CPhaseProd_ket_eq_ket_of_not_ctrl
          qs ctrl phi data work b hctrl
      _ =
          (if RegEncoding.bit ctrl b then
              Complex.exp
                (phi * Complex.I *
                  ((RegEncoding.toNat data b : ℂ) *
                   (RegEncoding.toNat work b : ℂ)))
            else
              1) •
            qs.ket b := by
          simp [hctrl]

end GateSemanticsFacts

/-! =========================================================
    Section 8: General algebraic lemmas for `eval`
========================================================= -/

lemma eval_sum {α : Type} [QSemantics] (U : Gate) (s : Finset α) (f : α → QSemantics.State) :
    QSemantics.eval U (∑ a ∈ s, f a) = ∑ a ∈ s, QSemantics.eval U (f a) := by
  classical
  refine Finset.induction_on s ?h0 ?hs
  · simp [QSemantics.eval_zero]
  · intro a s ha hs
    simp [Finset.sum_insert ha, QSemantics.eval_add, hs]

lemma eval_sum_univ {α : Type} [QSemantics] [Fintype α] (U : Gate) (f : α → State) :
    eval U (∑ a : α, f a) = ∑ a : α, eval U (f a) := by
  have := (eval_sum U (Finset.univ) f)
  aesop

/-! =========================================================
    Section 9: Encoding transport lemmas
========================================================= -/

lemma toNat_left_write_right [QSemantics] [RegEncoding (QSemantics.Basis)]
  (left right : Reg) (h : Disjoint left right) (b : QSemantics.Basis) (yR : ℕ) :
  RegEncoding.toNat left (RegEncoding.writeNat right yR b)
    = RegEncoding.toNat left b := by
  simpa using
    (RegEncoding.toNat_left_write_right
      (left := left) (right := right) (Basis:=QSemantics.Basis) (b := b) (yR := yR) h)

/-! =========================================================
    Section 10: Norm, isometry, and overlap inequalities
========================================================= -/

/-- `eval U` is an isometry if it preserves inner products. -/
lemma eval_isometry
  (qs : QSemantics)
  (U : Gate)
  (hU : ∀ ψ φ : qs.State, inner ℂ (qs.eval U ψ) (qs.eval U φ) = inner ℂ ψ φ) :
  ∀ ψ φ : qs.State, ‖qs.eval U ψ - qs.eval U φ‖ = ‖ψ - φ‖ := by
  intro ψ φ
  have hnorm : ‖qs.eval U (ψ - φ)‖ = ‖ψ - φ‖ := by
    have : ‖qs.eval U (ψ - φ)‖ ^ 2 = ‖ψ - φ‖ ^ 2 := by
      simpa [sq] using congrArg Complex.re (hU (ψ - φ) (ψ - φ))
    aesop
  simpa [qs.hsub U ψ φ] using hnorm

@[simp] lemma eval_seq_simp
  (qs : QSemantics) (U V : Gate) (ψ : qs.State) :
  qs.eval (U ;; V) ψ = qs.eval V (qs.eval U ψ) := by
  simpa using (qs.eval_seq U V ψ)

lemma eval_norm_preserved (qs : QSemantics) (U : Gate) (ψ : qs.State) :
  ‖qs.eval U ψ‖ = ‖ψ‖ := by
  have h := eval_isometry qs U (by intro ψ φ; simpa using qs.inner_preserved U ψ φ) ψ 0
  simpa [qs.eval_zero U] using h


end Shor
