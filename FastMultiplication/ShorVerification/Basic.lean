import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

universe u
namespace Shor

/-! =========================================================
    Section 1: Registers and basic encodings
========================================================= -/

/-- A contiguous register occupying qubit indices `[lo, hi)`. -/
structure Reg where
  lo : ℕ
  hi : ℕ


/-- Two registers are disjoint if their intervals do not overlap. -/
def Disjoint (a b : Reg) : Prop := a.hi ≤ b.lo ∨ b.hi ≤ a.lo

/-- Register length (#qubits) as a natural number. -/
def regSize (r : Reg) : ℕ := r.hi - r.lo

/-- Register cardinality `2^(regSize r)`. -/
def ASize (r : Reg) : ℕ := 2^(regSize r)

/-- Basis-level encoding interface for ordinary registers. -/
class RegEncoding (Basis : Type u) where
  toNat    : Reg → Basis → ℕ
  writeNat : Reg → ℕ → Basis → Basis
  bit      : ℕ → Basis → Bool

  toNat_writeNat : ∀ r v b, toNat r (writeNat r v b) = v
  writeNat_toNat : ∀ r b, writeNat r (toNat r b) b = b

  -- extensionality / locality
  basis_ext : ∀ b1 b2 : Basis, (∀ q, bit q b1 = bit q b2) → b1 = b2

  bit_writeNat_in  :
    ∀ r v b1 b2 q, r.lo ≤ q → q < r.hi →
      bit q (writeNat r v b1) = bit q (writeNat r v b2)

  bit_writeNat_out :
    ∀ r v b q, q < r.lo ∨ r.hi ≤ q →
      bit q (writeNat r v b) = bit q b

  toNat_left_write_right :
    ∀ (left right : Reg) (_h : Disjoint left right) (b : Basis) (yR : ℕ),
      toNat left (writeNat right yR b) = toNat left b

  toNat_right_write_left :
    ∀ (left right : Reg) (_h : Disjoint left right) (b : Basis) (yL : ℕ),
      toNat right (writeNat left yL b) = toNat right b

  writeNat_split :
    let left : Reg := ⟨r.lo, r.lo + m⟩
    let right : Reg := ⟨r.lo + m, r.hi⟩
    writeNat r (k1 + (ASize left) * k0) b
      =
    writeNat right k0 (writeNat left k1 b)

  toNat_split :
    let left : Reg := ⟨r.lo, r.lo + m⟩
    let right : Reg := ⟨r.lo + m, r.hi⟩
    toNat r b
      =
    toNat left b * (2^(regSize right)) + toNat right b

  /-- add this to RegEncoding -/
  toNat_lt_ASize : ∀ r b, toNat r b < ASize r
/-! =========================================================
    Section 2: Encoding lemmas and register helpers
========================================================= -/

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

namespace Reg


/-- Namespace alias for reading a register as a natural number. -/
def toNat {Basis : Type u} [RegEncoding Basis] (r : Reg) (b : Basis) : ℕ := RegEncoding.toNat r b

/-- Namespace alias for writing a natural number into a register. -/
def writeNat {Basis : Type u} [RegEncoding Basis]  (r : Reg) (v : ℕ) (b : Basis) : Basis := RegEncoding.writeNat r v b

end Reg

/-! =========================================================
    Section 3: Extended-register views
========================================================= -/

/-- A register together with a semantic high-bit extension budget. -/
structure ExtReg where
  base  : Reg
  extra : ℕ

namespace ExtReg

/-- A plain register with no extra logical high bits. -/
def ofReg (r : Reg) : ExtReg := ⟨r, 0⟩

/-- Logical width seen by signed phase semantics. -/
def width (e : ExtReg) : ℕ := regSize e.base + e.extra

/-- Increase the logical width descriptor by `n` high bits. -/
def addExtra (e : ExtReg) (n : ℕ) : ExtReg := ⟨e.base, e.extra + n⟩

@[simp] theorem addExtra_base (e : ExtReg) (n : ℕ) :
    (addExtra e n).base = e.base := rfl

@[simp] theorem addExtra_extra (e : ExtReg) (n : ℕ) :
    (addExtra e n).extra = e.extra + n := rfl

@[simp] theorem width_addExtra (e : ExtReg) (n : ℕ) :
    width (addExtra e n) = width e + n := by
  simp [width, addExtra, regSize, Nat.add_assoc]

end ExtReg

/-- Width-based two's-complement decoding. -/
def tcDecodeWidth : ℕ → ℕ → ℤ
  | 0, _ => 0
  | w + 1, n =>
      if _h : n < 2^w then
        (n : ℤ)
      else
        (n : ℤ) - ((2^(w + 1) : ℕ) : ℤ)

/-- How an extended register is read from a basis state.
    Extension itself is operationalized later as a gate. -/
class ExtRegEncoding (Basis : Type u) [RegEncoding Basis] where
  extToNat : ExtReg → Basis → ℕ

  extToNat_base :
    ∀ r b, extToNat (ExtReg.ofReg r) b = RegEncoding.toNat r b

  extToNat_write_disjoint :
    ∀ (e : ExtReg) (r : Reg) (_h : Disjoint e.base r) (v : ℕ) (b : Basis),
      extToNat e (RegEncoding.writeNat r v b) = extToNat e b

  extToNat_lt :
    ∀ e b, extToNat e b < 2 ^ (ExtReg.width e)

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
    Section 4: Gate language
========================================================= -/

inductive Gate : Type
  | id : Gate
  | seq : Gate → Gate → Gate
  | adj : Gate → Gate
  | H : ℕ → Gate
  | X : ℕ → Gate
  | QFT : Reg → Gate
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

-- @[simp] theorem PhaseProd_def
--     {Basis : Type u} [RegEncoding Basis] [ExtRegEncoding Basis]
--     (phi : Real) (x z : Reg) :
--     Gate.PhaseProd (Basis := Basis) phi x z
--       =
--     Gate.zeroExtend (ExtReg.ofReg x) 1 ;;
--     Gate.zeroExtend (ExtReg.ofReg z) 1 ;;
--     Gate.SignedPhaseProd phi (unsignedView x) (unsignedView z) := rfl

-- @[simp] theorem CPhaseProd_def
--     {Basis : Type u} [RegEncoding Basis] [ExtRegEncoding Basis]
--     (ctrl : ℕ) (phi : Real) (x z : Reg) :
--     Gate.CPhaseProd (Basis := Basis) ctrl phi x z
--       =
--     Gate.zeroExtend (ExtReg.ofReg x) 1 ;;
--     Gate.zeroExtend (ExtReg.ofReg z) 1 ;;
--     Gate.CSignedPhaseProd ctrl phi (unsignedView x) (unsignedView z) := rfl

end Gate

/-! =========================================================
    Section 5: Core QFT phase helpers
========================================================= -/

/-- A 1-qubit register at index `q`. -/
def qubitReg (q : ℕ) : Reg := ⟨q, q + 1⟩

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
    Section 6: Abstract quantum semantics
========================================================= -/

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


open QSemantics
attribute [instance] QSemantics.instNormed
attribute [instance] QSemantics.instIP

/-! =========================================================
    Section 7: Gate semantic facts
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
/-! =========================================================
    Section 7: Gate semantic facts (split by topic)
========================================================= -/


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

/-- Wrap is the identity on values that already fit the target signed width.
    This is the bridge from the raw symbolic arithmetic semantics to the
    wrapped machine-level gate semantics. -/
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
      (∀ e : ExtReg, Disjoint e.base r.base →
        ExtReg.toNat e b' = ExtReg.toNat e b)

  eval_signExtend_ket :
    ∀ (r : ExtReg) (n : ℕ) (b : qs.Basis),
      ∃ b' : qs.Basis,
        qs.eval (Gate.signExtend r n) (qs.ket b) = qs.ket b' ∧
        ExtReg.toNat r b' = ExtReg.toNat r b ∧
        ExtRegEncoding.extToInt (ExtReg.addExtra r n) b'
          = ExtRegEncoding.extToInt r b ∧
        (∀ e : ExtReg, Disjoint e.base r.base →
          ExtReg.toNat e b' = ExtReg.toNat e b)

  eval_zeroExtend_zeroDealloc :
    ∀ r n ψ,
      qs.eval (Gate.zeroExtend r n ;; Gate.zeroDealloc r n) ψ = ψ

  eval_signExtend_signDealloc :
    ∀ r n ψ,
      qs.eval (Gate.signExtend r n ;; Gate.signDealloc r n) ψ = ψ

  extToNat_lt_width :
  ∀ (e : ExtReg) (b : qs.Basis),
    ExtRegEncoding.extToNat e b < 2 ^ (ExtReg.width e)


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
      ExtensionSemantics.extToNat_lt_width (qs := qs) (e := r) (b := b)

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
    ExtensionSemantics.extToNat_lt_width
      (qs := qs) (e := ExtReg.ofReg r) (b := b)
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

  /-- Left shift is width-`w` modular multiplication by `2^n`. -/
  eval_ShiftL_ket_mod :
    ∀ (r : ExtReg) (n : ℕ) (b : qs.Basis),
      ∃ b' : qs.Basis,
        qs.eval (Gate.ShiftL r n) (qs.ket b) = qs.ket b' ∧
        ExtRegEncoding.extToInt r b'
          = tcWrapInt (ExtReg.width r)
              (((2 : ℤ)^n) * ExtRegEncoding.extToInt r b) ∧
        (∀ e : ExtReg,
          Disjoint e.base r.base →
          ExtRegEncoding.extToInt e b' = ExtRegEncoding.extToInt e b)

  /-- Right shift is only allowed when the current signed value is exactly divisible
      by `2^n`; then it produces the exact quotient. -/
  eval_ShiftR_ket_exact :
    ∀ (r : ExtReg) (n : ℕ) (b : qs.Basis) (q : ℤ),
      ExtRegEncoding.extToInt r b = ((2 : ℤ)^n) * q →
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
      and preserves every other disjoint register. -/
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

/-- Optional aggregate class.
    Keep this if you still want one bundled assumption in some later theorems. -/
class GateSemanticsFacts
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [ExtRegEncoding qs.Basis]:
  Type extends QFTSemantics qs, PhaseSemantics qs, ExtensionSemantics qs, ArithmeticSemantics qs


namespace GateSemanticsFacts

variable {qs : QSemantics}

variable [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
variable [GateSemanticsFacts qs]



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
end GateSemanticsFacts

/-! =========================================================
    Section 8: General linearity lemmas for `eval`
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
      (left := left) (right := right) (_h := h) (b := b) (yR := yR))

lemma toNat_right_write_right [QSemantics] [RegEncoding (QSemantics.Basis)]
  (right : Reg) (b : QSemantics.Basis) (yR : ℕ) :
  RegEncoding.toNat right (RegEncoding.writeNat right yR b) = yR := by
  simpa using (RegEncoding.toNat_writeNat right yR b)

/-! =========================================================
    Section 10: Norm and overlap inequalities
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

/-- Overlap error invariance under a common post-gate. -/
lemma overlap_err_invariant
  (qs : QSemantics) (W : Gate) (ψ φ : qs.State) :
    ‖ (1 : ℂ) - inner ℂ (qs.eval W ψ) (qs.eval W φ)‖
      =
    ‖ (1 : ℂ) - inner ℂ ψ φ‖ := by
  simp [qs.inner_preserved W ψ φ]

/-- `‖1 - inner ψ φ‖ ≤ ‖ψ - φ‖` when `‖ψ‖ = 1`. -/
lemma overlap_le_dist
  (qs : QSemantics) (ψ φ : qs.State) :
  ‖ψ‖ = 1 →
  ‖ (1 : ℂ) - inner ℂ ψ φ‖ ≤ ‖ψ - φ‖ := by
  intro hψ
  have hψψ : inner ℂ ψ ψ = (1 : ℂ) := by
    simp [hψ]
  have h1 : (1 : ℂ) = inner ℂ ψ ψ := by
    simpa using hψψ.symm

  calc
    ‖ (1 : ℂ) - inner ℂ ψ φ‖
        = ‖ inner ℂ ψ ψ - inner ℂ ψ φ‖ := by simp [h1]
    _   = ‖ inner ℂ ψ (ψ - φ)‖ := by
            simp [inner_sub_right]
    _   ≤ ‖ψ‖ * ‖ψ - φ‖ := by
            simpa using (norm_inner_le_norm ψ (ψ - φ))
    _   = ‖ψ - φ‖ := by simp [hψ]

/-- Distance is bounded by the square root of twice the overlap error for unit vectors. -/
lemma dist_le_sqrt_two_mul_overlap
  (qs : QSemantics) (ψ φ : qs.State) :
  ‖ψ‖ = 1 → ‖φ‖ = 1 →
  ‖ψ - φ‖ ≤ Real.sqrt (2 * ‖(1 : ℂ) - inner ℂ ψ φ‖) := by
  intro hψ hφ
  have hmain : ‖ψ - φ‖ ^ 2 ≤ 2 * ‖(1 : ℂ) - inner ℂ ψ φ‖ := by
    have hnormsub :
        ‖ψ - φ‖ ^ 2
          = ‖ψ‖ ^ 2 + ‖φ‖ ^ 2 - 2 * Complex.re (inner ℂ ψ φ) := by
      have := (norm_sub_sq (𝕜 := ℂ) ψ φ)
      simp_all only [one_pow, RCLike.re_to_complex]
      ring
    have hnorms : ‖ψ‖ ^ 2 + ‖φ‖ ^ 2 = (2 : ℝ) := by
      simp [hψ, hφ]
      ring
    have hnormsub' :
        ‖ψ - φ‖ ^ 2 = (2 : ℝ) - 2 * Complex.re (inner ℂ ψ φ) := by
      simpa [hnorms] using hnormsub

    have hre :
        (1 - Complex.re (inner ℂ ψ φ)) ≤ ‖(1 : ℂ) - inner ℂ ψ φ‖ := by
      have h : Complex.re ((1 : ℂ) - inner ℂ ψ φ) ≤ ‖(1 : ℂ) - inner ℂ ψ φ‖ := by
        simpa using (Complex.re_le_norm ((1 : ℂ) - inner ℂ ψ φ))
      simpa [Complex.sub_re, Complex.one_re] using h

    calc
      ‖ψ - φ‖ ^ 2
          = 2 * (1 - Complex.re (inner ℂ ψ φ)) := by
              have : (2 : ℝ) - 2 * Complex.re (inner ℂ ψ φ)
                      = 2 * (1 - Complex.re (inner ℂ ψ φ)) := by ring
              simp [hnormsub', this]
      _   ≤ 2 * ‖(1 : ℂ) - inner ℂ ψ φ‖ := by
              have h2 : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
              exact mul_le_mul_of_nonneg_left hre h2

  apply Real.le_sqrt_of_sq_le
  exact hmain

/-! =========================================================
    Section 11: Specification interface
========================================================= -/

class Spec where
  idealModMul     : (c N : ℕ) → (x : Reg) → Gate
  idealCtrlModMul : (c N : ℕ) → (x : Reg) → (ctrl : ℕ) → Gate

open QSemantics
open Gate

/-! =========================================================
    Section 12: Modular multiplication and exponentiation circuits
========================================================= -/

/-- Inverse QFT. -/
def IQFT (r : Reg) : Gate := †(Gate.QFT r)

/-- Extend a register by one physical high qubit. -/
def extendHi (r : Reg) : Reg := ⟨r.lo, r.hi + 1⟩

/-- List of qubit indices in a register. -/
def regQubits (r : Reg) : List ℕ :=
  (List.range (regSize r)).map (fun k => r.lo + k)

/-- Apply Hadamards across all qubits of a register. -/
def H_reg (r : Reg) : Gate :=
  (regQubits r).foldl (fun acc q => (Gate.H q) ;; acc) Gate.id

/-- Primitive gate wrapper. -/
def PrimN (tag : String) (args : List ℕ) : Gate := Gate.Prim tag args

noncomputable def step1 {Basis : Type u} [RegEncoding Basis] [ExtRegEncoding Basis]
    (c N : ℕ) (ctrl : ℕ) (x_reg w_reg : Reg) : Gate :=
  let phi : ℝ := (2 * Real.pi * ((c + N - 1) % N)) / (N : ℝ)
  (IQFT w_reg) ;;
  (Gate.CPhaseProd ctrl phi x_reg w_reg) ;;
  (H_reg w_reg)

noncomputable def step2 {Basis : Type u} [RegEncoding Basis] [ExtRegEncoding Basis]
    (N : ℕ) (x_reg w_reg : Reg) : (Reg × Gate) :=
  let x_ext : Reg := extendHi x_reg
  let n1 : ℕ := regSize x_ext
  let m  : ℕ := regSize w_reg
  let phi : ℝ := (2 * Real.pi * (N : ℝ)) / ((2 : ℝ) ^ (m + n1))
  (x_ext,
    (IQFT x_ext) ;;
    (Gate.PhaseProd phi w_reg x_ext) ;;
    (Gate.QFT x_ext))

noncomputable def frac_load
    (k N : ℕ) (ctrl : ℕ) (x_reg w_reg : Reg) : Gate :=
  let phi : ℝ := (2 * Real.pi * ((k % N) : ℝ)) / (N : ℝ)
  (IQFT w_reg) ;;
  (Gate.CPhaseProd ctrl phi x_reg w_reg) ;;
  (QFT w_reg)

def step3 (N : ℕ) (x_ext : Reg) (flag : ℕ) : Gate :=
  (PrimN "CMP_GE_CONST" [x_ext.lo, x_ext.hi, N, flag]) ;;
  (PrimN "CSUB_CONST"   [flag, x_ext.lo, x_ext.hi, N])

def step4 (N : ℕ) (x_ext w_reg : Reg) (flag : ℕ) : Gate :=
  PrimN "CMP_LT_NW" [x_ext.lo, x_ext.hi, w_reg.lo, w_reg.hi, N, flag]

noncomputable def step5 {Basis : Type u} [RegEncoding Basis] [ExtRegEncoding Basis]
    (k5 N : ℕ) (ctrl : ℕ) (x_ext w_reg : Reg) : Gate :=
  †(frac_load k5 N ctrl x_ext w_reg)

noncomputable def CmodMulInPlaceCore {Basis : Type u} [RegEncoding Basis] [ExtRegEncoding Basis]
    (c N k5 : ℕ) (ctrl : ℕ) (x_reg w_reg : Reg) (flag : ℕ) : Gate :=
  let U1 : Gate := step1 (Basis := Basis) c N ctrl x_reg w_reg
  let (x_ext, U2) := step2 (Basis := Basis) N x_reg w_reg
  let U3 : Gate := step3 N x_ext flag
  let U4 : Gate := step4 N x_ext w_reg flag
  let U5 : Gate := step5 (Basis := Basis) k5 N ctrl x_ext w_reg
  U5 ;; U4 ;; U3 ;; U2 ;; U1

noncomputable def CmodMulInPlace {Basis : Type u} [RegEncoding Basis] [ExtRegEncoding Basis]
    (base n m c N k5 ctrl : ℕ) : Gate :=
  let x_reg : Reg := ⟨base, base + n⟩
  let w_reg : Reg := ⟨base + n + 1, base + n + m + 1⟩
  let flag  : ℕ := base + n + m + 1
  CmodMulInPlaceCore (Basis := Basis) c N k5 ctrl x_reg w_reg flag

class ModMul (qs : QSemantics) [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [Spec] where
  η : ℝ
  η_nonneg : 0 ≤ η
  k5 : ℕ → ℕ → ℕ
  theorem1_ctrl_gen :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (c N : ℕ) (x_reg w_reg : Reg) (flag ctrl : ℕ) (ψ : qs.State),
        ‖ (1 : ℂ) - inner ℂ
            (qs.eval (CmodMulInPlaceCore (Basis := qs.Basis) c N (k5 c N) ctrl x_reg w_reg flag) ψ)
            (qs.eval (Spec.idealCtrlModMul c N x_reg ctrl) ψ)‖
        ≤ K * η

noncomputable def modExpApproxSteps
    (qs : QSemantics) [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [Spec] [ModMul qs]
    (a N : ℕ) (x y w_reg : Reg) (flag : ℕ) : ℕ → ℕ → Gate
  | _q, 0   => Gate.id
  | q, n+1 =>
      let k : ℕ := q - x.lo
      let c : ℕ := ((a ^ (2 ^ k)) % N)
      (CmodMulInPlaceCore (Basis := qs.Basis) c N (ModMul.k5 (qs := qs) c N) q y w_reg flag) ;;
      modExpApproxSteps qs a N x y w_reg flag (q+1) n

def tbits (x : Reg) : ℕ := x.hi - x.lo

noncomputable def modExpApprox'
    (qs : QSemantics) [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [Spec] [ModMul qs]
    (a N : ℕ) (x y w_reg : Reg) (flag : ℕ) : Gate :=
  modExpApproxSteps qs a N x y w_reg flag x.lo (tbits x)

def modExpIdealSteps (qs : QSemantics) [RegEncoding qs.Basis] [Spec]
    (a N : ℕ) (x y : Reg) : ℕ → ℕ → Gate
  | _q, 0   => Gate.id
  | q, n+1  =>
      let k : ℕ := q - x.lo
      (Spec.idealCtrlModMul ((a ^ (2 ^ k)) % N) N y q) ;;
      modExpIdealSteps qs a N x y (q+1) n

def modExpIdeal' (qs : QSemantics) [RegEncoding qs.Basis] [Spec]
    (a N : ℕ) (x y : Reg) : Gate :=
  modExpIdealSteps qs a N x y x.lo (tbits x)

noncomputable def stepErr (K η : ℝ) : ℝ := Real.sqrt (2 * (K * η))

/-! =========================================================
    Section 13: Modular exponentiation error propagation
========================================================= -/

lemma ctrlMul_step_dist_bound
  (qs : QSemantics) [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [Spec] [ModMul qs] :
  ∃ K : ℝ, 0 ≤ K ∧
    ∀ (c N : ℕ) (x_reg w_reg : Reg) (flag ctrl : ℕ) (ψ : qs.State),
      ‖ψ‖ = 1 →
      ‖ qs.eval (CmodMulInPlaceCore (Basis := qs.Basis) c N (ModMul.k5 (qs := qs) c N) ctrl x_reg w_reg flag) ψ
        - qs.eval (Spec.idealCtrlModMul c N x_reg ctrl) ψ‖
      ≤ stepErr K (ModMul.η (qs := qs)) :=
by
  rcases ModMul.theorem1_ctrl_gen (qs := qs) with ⟨K, K_nonneg, hK⟩
  refine ⟨K, K_nonneg, ?_⟩
  intro c N x_reg w_reg flag ctrl ψ hψ

  set ψA : qs.State :=
    qs.eval (CmodMulInPlaceCore (Basis := qs.Basis) c N (ModMul.k5 (qs := qs) c N) ctrl x_reg w_reg flag) ψ
  set ψI : qs.State :=
    qs.eval (Spec.idealCtrlModMul c N x_reg ctrl) ψ

  have hψA : ‖ψA‖ = 1 := by
    simpa [ψA, hψ] using
      (eval_norm_preserved (qs := qs)
        (CmodMulInPlaceCore (Basis := qs.Basis) c N (ModMul.k5 (qs := qs) c N) ctrl x_reg w_reg flag) ψ)

  have hψI : ‖ψI‖ = 1 := by
    simpa [ψI, hψ] using
      (eval_norm_preserved (qs := qs)
        (Spec.idealCtrlModMul c N x_reg ctrl) ψ)

  have hdist :
      ‖ψA - ψI‖ ≤ Real.sqrt (2 * ‖(1 : ℂ) - inner ℂ ψA ψI‖) :=
    dist_le_sqrt_two_mul_overlap (qs := qs) ψA ψI hψA hψI

  have hov :
      ‖(1 : ℂ) - inner ℂ ψA ψI‖ ≤ K * ModMul.η (qs := qs) := by
    simpa [ψA, ψI] using (hK c N x_reg w_reg flag ctrl ψ)

  have hsqrt :
      Real.sqrt (2 * ‖(1 : ℂ) - inner ℂ ψA ψI‖)
      ≤ Real.sqrt (2 * (K * ModMul.η (qs := qs))) := by
    have hmul :
        2 * ‖(1 : ℂ) - inner ℂ ψA ψI‖ ≤ 2 * (K * ModMul.η (qs := qs)) := by
      have : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
      exact mul_le_mul_of_nonneg_left hov this
    exact Real.sqrt_le_sqrt hmul

  have : ‖ψA - ψI‖ ≤ Real.sqrt (2 * (K * ModMul.η (qs := qs))) :=
    le_trans hdist hsqrt

  simpa [ψA, ψI, stepErr] using this

theorem modExpSteps_dist_bound
  (qs : QSemantics) [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [Spec] [ModMul qs] :
  ∃ K : ℝ, 0 ≤ K ∧
    ∀ (a N : ℕ) (x y w_reg : Reg) (flag : ℕ) (q n : ℕ) (ψ : qs.State),
      ‖ψ‖ = 1 →
      ‖ qs.eval (modExpApproxSteps (qs := qs) a N x y w_reg flag q n) ψ
        - qs.eval (modExpIdealSteps  (qs := qs) a N x y q n) ψ‖
      ≤ (n : ℝ) * stepErr K (ModMul.η (qs := qs)) :=
by
  rcases ctrlMul_step_dist_bound (qs := qs) with ⟨K, K_nonneg, hstep⟩
  refine ⟨K, K_nonneg, ?_⟩
  intro a N x y w_reg flag q n ψ hψ
  revert q ψ
  induction n with
  | zero =>
      intro q ψ hψ
      simp [modExpApproxSteps, modExpIdealSteps, qs.eval_id]
  | succ n ih =>
      intro q ψ hψ
      set k : ℕ := q - x.lo with hk
      set c : ℕ := ((a ^ (2 ^ k)) % N) with hc

      set A : Gate := CmodMulInPlaceCore (Basis := qs.Basis) c N (ModMul.k5 (qs := qs) c N) q y w_reg flag with hA
      set I : Gate := Spec.idealCtrlModMul c N y q with hI
      set RA : Gate := modExpApproxSteps (qs := qs) a N x y w_reg flag (q+1) n with hRA
      set RI : Gate := modExpIdealSteps  (qs := qs) a N x y (q+1) n with hRI

      have hApprox :
        modExpApproxSteps (qs := qs) a N x y w_reg flag q (n+1) = A ;; RA := by
        simp [modExpApproxSteps, hk, hc, hA, hRA]

      have hIdeal :
        modExpIdealSteps (qs := qs) a N x y q (n+1) = I ;; RI := by
        simp [modExpIdealSteps, hk, hc, hI, hRI]

      set ψA0 : qs.State := qs.eval A ψ
      set ψI0 : qs.State := qs.eval I ψ

      have hψA0_unit : ‖ψA0‖ = 1 := by
        simpa [ψA0, hψ] using (eval_norm_preserved (qs := qs) A ψ)

      have hψI0_unit : ‖ψI0‖ = 1 := by
        simpa [ψI0, hψ] using (eval_norm_preserved (qs := qs) I ψ)

      have h_head :
        ‖ψA0 - ψI0‖ ≤ stepErr K (ModMul.η (qs := qs)) := by
        have := hstep c N y w_reg flag q ψ hψ
        simpa [ψA0, ψI0, hA, hI] using this

      have h_tail :
        ‖ qs.eval RA ψI0 - qs.eval RI ψI0‖
          ≤ (n : ℝ) * stepErr K (ModMul.η (qs := qs)) := by
        have := ih (q := q+1) (ψ := ψI0) hψI0_unit
        simpa [hRA, hRI] using this

      have h_iso_RA :
        ‖ qs.eval RA ψA0 - qs.eval RA ψI0‖ = ‖ ψA0 - ψI0‖ := by
        simpa using
          (eval_isometry qs RA
            (by intro ψ φ; simpa using qs.inner_preserved RA ψ φ) ψA0 ψI0)

      have tri :
        ‖qs.eval RA ψA0 - qs.eval RI ψI0‖
          ≤ ‖qs.eval RA ψA0 - qs.eval RA ψI0‖ + ‖qs.eval RA ψI0 - qs.eval RI ψI0‖ := by
        have hdecomp :
          qs.eval RA ψA0 - qs.eval RI ψI0
            = (qs.eval RA ψA0 - qs.eval RA ψI0) + (qs.eval RA ψI0 - qs.eval RI ψI0) := by
          aesop
        calc
          ‖qs.eval RA ψA0 - qs.eval RI ψI0‖
              = ‖(qs.eval RA ψA0 - qs.eval RA ψI0) + (qs.eval RA ψI0 - qs.eval RI ψI0)‖ := by
                  rw [hdecomp]
          _ ≤ ‖qs.eval RA ψA0 - qs.eval RA ψI0‖ + ‖qs.eval RA ψI0 - qs.eval RI ψI0‖ := by
                  simpa using
                    (norm_add_le
                      (qs.eval RA ψA0 - qs.eval RA ψI0)
                      (qs.eval RA ψI0 - qs.eval RI ψI0))

      have hmain :
        ‖ qs.eval (modExpApproxSteps (qs := qs) a N x y w_reg flag q (n+1)) ψ
          - qs.eval (modExpIdealSteps  (qs := qs) a N x y q (n+1)) ψ‖
          ≤ (n+1 : ℝ) * stepErr K (ModMul.η (qs := qs)) := by
        have : ‖ qs.eval RA ψA0 - qs.eval RI ψI0‖
            ≤ (n+1 : ℝ) * stepErr K (ModMul.η (qs := qs)) := by
          calc
            ‖ qs.eval RA ψA0 - qs.eval RI ψI0‖
                ≤ ‖ qs.eval RA ψA0 - qs.eval RA ψI0‖
                  + ‖ qs.eval RA ψI0 - qs.eval RI ψI0‖ := tri
            _ = ‖ ψA0 - ψI0‖ + ‖ qs.eval RA ψI0 - qs.eval RI ψI0‖ := by
                  simp [h_iso_RA]
            _ ≤ stepErr K (ModMul.η (qs := qs)) + (n : ℝ) * stepErr K (ModMul.η (qs := qs)) := by
                  gcongr
            _ = (n+1 : ℝ) * stepErr K (ModMul.η (qs := qs)) := by ring
        simpa [hApprox, hIdeal, ψA0, ψI0, eval_seq_simp] using this
      aesop

theorem modExp_dist_bound
  (qs : QSemantics) [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [Spec] [ModMul qs] :
  ∃ K : ℝ, 0 ≤ K ∧
    ∀ (a N : ℕ) (x y w_reg : Reg) (flag : ℕ) (ψ : qs.State),
      ‖ψ‖ = 1 →
      ‖ qs.eval (modExpApprox' (qs := qs) a N x y w_reg flag) ψ
        - qs.eval (modExpIdeal'  (qs := qs) a N x y) ψ‖
      ≤ (tbits x : ℝ) * stepErr K (ModMul.η (qs := qs)) :=
by
  rcases modExpSteps_dist_bound (qs := qs) with ⟨K, K_nonneg, h⟩
  refine ⟨K, K_nonneg, ?_⟩
  intro a N x y w_reg flag ψ hψ
  simpa [modExpApprox', modExpIdeal', tbits] using
    (h a N x y w_reg flag x.lo (tbits x) ψ hψ)

theorem modExp_overlap_bound_sqrt
  (qs : QSemantics) [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [Spec] [ModMul qs] :
  ∃ K : ℝ, 0 ≤ K ∧
    ∀ (a N : ℕ) (x y w_reg : Reg) (flag : ℕ) (ψ : qs.State),
      ‖ψ‖ = 1 →
      ‖ (1 : ℂ) - inner ℂ
          (qs.eval (modExpApprox' (qs := qs) a N x y w_reg flag) ψ)
          (qs.eval (modExpIdeal'  (qs := qs) a N x y) ψ)‖
      ≤ ((tbits x : ℕ) : ℝ) * Real.sqrt (2 * (K * ModMul.η (qs := qs))) :=
by
  rcases modExp_dist_bound (qs := qs) with ⟨K, K_nonneg, hdist⟩
  refine ⟨K, K_nonneg, ?_⟩
  intro a N x y w_reg flag ψ hψ

  have hA_unit :
      ‖qs.eval (modExpApprox' (qs := qs) a N x y w_reg flag) ψ‖ = 1 := by
    simpa [hψ] using
      (eval_norm_preserved (qs := qs) (modExpApprox' (qs := qs) a N x y w_reg flag) ψ)

  have hov_le_dist :
      ‖ (1 : ℂ) - inner ℂ
          (qs.eval (modExpApprox' (qs := qs) a N x y w_reg flag) ψ)
          (qs.eval (modExpIdeal'  (qs := qs) a N x y) ψ)‖
      ≤ ‖ qs.eval (modExpApprox' (qs := qs) a N x y w_reg flag) ψ
          - qs.eval (modExpIdeal'  (qs := qs) a N x y) ψ‖ := by
    have h :=
      overlap_le_dist (qs := qs)
        (ψ := qs.eval (modExpApprox' (qs := qs) a N x y w_reg flag) ψ)
        (φ := qs.eval (modExpIdeal'  (qs := qs) a N x y) ψ)
    exact h hA_unit

  have hdist' :
      ‖ qs.eval (modExpApprox' (qs := qs) a N x y w_reg flag) ψ
          - qs.eval (modExpIdeal'  (qs := qs) a N x y) ψ‖
      ≤ ((tbits x : ℕ) : ℝ) * stepErr K (ModMul.η (qs := qs)) :=
    hdist a N x y w_reg flag ψ hψ

  have : ‖ (1 : ℂ) - inner ℂ
          (qs.eval (modExpApprox' (qs := qs) a N x y w_reg flag) ψ)
          (qs.eval (modExpIdeal'  (qs := qs) a N x y) ψ)‖
      ≤ ((tbits x : ℕ) : ℝ) * stepErr K (ModMul.η (qs := qs)) :=
    le_trans hov_le_dist hdist'

  simpa [stepErr] using this



end Shor
