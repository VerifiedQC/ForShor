import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.Data.Nat.Bitwise

universe u
namespace Shor

/-!
# Shor verification core

This file is the shared vocabulary for the Shor verification development. It is
organized by mathematical role, while still respecting Lean dependencies:

1. Concrete physical registers and basis encodings.
2. Extendable registers, freshness, and two's-complement arithmetic.
3. Gate syntax, phase-product workspace records, and derived gate macros.
4. Abstract quantum semantics and gate-family semantic fact classes.
5. Reusable semantic lemmas for sums, encodings, isometries, and freshness.
-/

/-! =========================================================
    Section 1: Ordered physical registers
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

theorem Disjoint.symm {a b : Reg} :
    Disjoint a b → Disjoint b a := by
  intro h
  exact List.Disjoint.symm h

namespace Reg

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

/-- The least-significant physical qubit of a nonempty ordered register. -/
def Reg.lowQubit (r : Reg) (h : 0 < regSize r) : ℕ :=
  r.qubits.get ⟨0, by simpa [regSize, Reg.width] using h⟩

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
    ∀ r v b₁ b₂ q,
      q ∈ r.qubits →
      bit q (writeNat r v b₁) =
        bit q (writeNat r v b₂)

  bit_writeNat_out :
    ∀ r v b q,
      q ∉ r.qubits →
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

  writeNat_comm_of_disjoint :
    ∀ (left right : Reg),
      Disjoint left right →
      ∀ yL yR b,
        writeNat left yL (writeNat right yR b) =
          writeNat right yR (writeNat left yL b)

  writeNat_split :
    ∀ (r : Reg) (m : SplitPoint r) (high low : ℕ) (b : Basis),
      let left  := splitLeft r m
      let right := splitRight r m
      low < ASize left →
      high < ASize right →
      writeNat r (low + ASize left * high) b =
        writeNat right high (writeNat left low b)

  toNat_split :
    ∀ (r : Reg) (m : SplitPoint r) (b : Basis),
      let left  : Reg := splitLeft r m
      let right : Reg := splitRight r m
      toNat r b =
        toNat left b + (ASize left) * toNat right b

  toNat_append :
    ∀ (left right : Reg)
      (hdisj : Disjoint left right)
      (b : Basis),
      toNat (Reg.append left right hdisj) b =
        toNat left b + ASize left * toNat right b

  bit_eq_testBit_toNat :
    ∀ (r : Reg) (b : Basis) (i : Fin (regSize r)),
      bit (r.get i) b =
        Nat.testBit (toNat r b) i.1
/-! =========================================================
    Section 2: Extendable physical registers
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
  simp [width, grow, Reg.append, newBits, Reg.take, regSize, Reg.width,
    CanGrow, capacity] at hcap ⊢
  omega

@[simp] theorem capacity_grow
    (e : ExtReg) (n : ℕ)
    (_hcap : e.CanGrow n) :
    capacity (e.grow n) = capacity e - n := by
  simp [capacity, grow, remainingReserve, Reg.drop, regSize, Reg.width]

/-- All physical qubits owned by an extendable register, active first and reserve second. -/
def ownedQubits (e : ExtReg) : List ℕ := e.active.qubits ++ e.reserve.qubits

/-- Disjointness of the currently active portions only. -/
def ActiveDisjoint (x z : ExtReg) : Prop := Disjoint x.active z.active

/-- Disjointness of all owned qubits, including reserve/workspace bits. -/
def OwnedDisjoint (x z : ExtReg) : Prop := x.ownedQubits.Disjoint z.ownedQubits

/-- A control qubit is outside both active data and reserved workspace. -/
def CtrlDisjoint (ctrl : ℕ) (x z : ExtReg) : Prop := ctrl ∉ x.ownedQubits ∧ ctrl ∉ z.ownedQubits

end ExtReg

/-- Writes to disjoint registers commute. -/
lemma writeNat_comm_of_disjoint
  {Basis : Type u} [RegEncoding Basis]
  (left right : Reg) (hdisj : Disjoint left right)
  (yL yR : ℕ) (b : Basis) :
  RegEncoding.writeNat left yL (RegEncoding.writeNat right yR b)
    =
  RegEncoding.writeNat right yR (RegEncoding.writeNat left yL b) := by
  exact RegEncoding.writeNat_comm_of_disjoint left right hdisj yL yR b

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
    Section 3: Signed two's-complement arithmetic
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


/-! =========================================================
    Section 4: Gate language and derived gate macros
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
  | QFT : ExtReg → Gate
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

/--
Workspace needed to implement an unsigned phase product via the signed phase-product gate.
The one-bit reserves hold the sign-extension bit for each operand, and the disjointness
fields make the generated macro local to `x`, `z`, and those reserves.
-/
structure PhaseProdWorkspace (x z : Reg) where
  xReserve : Reg
  zReserve : Reg

  x_can_grow : 1 ≤ regSize xReserve
  z_can_grow : 1 ≤ regSize zReserve

  xz_disjoint : Disjoint x z
  x_reserve_disjoint : Disjoint x xReserve
  z_reserve_disjoint : Disjoint z zReserve

  xReserve_not_z : Disjoint xReserve z
  zReserve_not_x : Disjoint zReserve x
  reserve_disjoint : Disjoint xReserve zReserve

namespace PhaseProdWorkspace

def xExt {x z : Reg} (ws : PhaseProdWorkspace x z) : ExtReg :=
  ExtReg.withReserve x ws.xReserve ws.x_reserve_disjoint

def zExt {x z : Reg} (ws : PhaseProdWorkspace x z) : ExtReg :=
  ExtReg.withReserve z ws.zReserve ws.z_reserve_disjoint

/-- The reserve bits used by the unsigned-to-signed bridge are initially zero. -/
def Clean
    {Basis : Type u}
    [RegEncoding Basis]
    {x z : Reg}
    (ws : PhaseProdWorkspace x z)
    (b : Basis) : Prop :=
  ws.xExt.FreshFor 1 b ∧
  ws.zExt.FreshFor 1 b

@[simp] theorem xExt_canGrow
    {x z : Reg}
    (ws : PhaseProdWorkspace x z) :
    ws.xExt.CanGrow 1 := by
  simpa [
    PhaseProdWorkspace.xExt,
    ExtReg.CanGrow,
    ExtReg.capacity
  ] using ws.x_can_grow

@[simp] theorem zExt_canGrow
    {x z : Reg}
    (ws : PhaseProdWorkspace x z) :
    ws.zExt.CanGrow 1 := by
  simpa [
    PhaseProdWorkspace.zExt,
    ExtReg.CanGrow,
    ExtReg.capacity
  ] using ws.z_can_grow

@[simp] theorem toNat_xExt
    {Basis : Type u}
    [RegEncoding Basis]
    {x z : Reg}
    (ws : PhaseProdWorkspace x z)
    (b : Basis) :
    ExtReg.toNat ws.xExt b =
      RegEncoding.toNat x b := by
  rfl

@[simp] theorem toNat_zExt
    {Basis : Type u}
    [RegEncoding Basis]
    {x z : Reg}
    (ws : PhaseProdWorkspace x z)
    (b : Basis) :
    ExtReg.toNat ws.zExt b =
      RegEncoding.toNat z b := by
  rfl



/-- The controlled bridge may read `ctrl`; this predicate keeps it outside all touched qubits. -/
def ControlDisjoint
    {x z : Reg}
    (ws : PhaseProdWorkspace x z)
    (ctrl : ℕ) : Prop :=
  ctrl ∉ x.qubits ∧
  ctrl ∉ z.qubits ∧
  ctrl ∉ ws.xReserve.qubits ∧
  ctrl ∉ ws.zReserve.qubits
end PhaseProdWorkspace

/--
Unsigned phase product macro: allocate one clean high bit on each operand, run the signed
phase product on the grown registers, and then deallocate the temporary bits.
-/
def PhaseProdUsing
    (phi : ℝ)
    (x z : Reg)
    (ws : PhaseProdWorkspace x z) : Gate :=
  let xext := ws.xExt
  let zext := ws.zExt

  Gate.zeroExtend xext 1 ;;
  Gate.zeroExtend zext 1 ;;
  Gate.SignedPhaseProd phi
    (xext.grow 1)
    (zext.grow 1) ;;
  Gate.zeroDealloc zext 1 ;;
  Gate.zeroDealloc xext 1

/-- Controlled unsigned phase-product macro with the same workspace discipline as `PhaseProdUsing`. -/
def CPhaseProdUsing
    (ctrl : ℕ) (phi : ℝ)
    (x z : Reg)
    (ws : PhaseProdWorkspace x z) :
    Gate :=
  let xext := ws.xExt
  let zext := ws.zExt

  Gate.zeroExtend xext 1 ;;
  Gate.zeroExtend zext 1 ;;
  Gate.CSignedPhaseProd
    ctrl
    phi
    (xext.grow 1)
    (zext.grow 1) ;;
  Gate.zeroDealloc zext 1 ;;
  Gate.zeroDealloc xext 1

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


/-! =========================================================
    Section 5: QFT phase helpers
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
    Section 6: Abstract quantum semantics
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
    Section 7: Gate-specific semantic fact classes
========================================================= -/

/-- QFT-specific semantic facts. -/
class QFTSemantics
  (qs : QSemantics)
  [RegEncoding qs.Basis] : Type where

  eval_QFT_size0 :
    ∀ (r : ExtReg) (ψ : qs.State),
      r.width = 0 →
      qs.eval (Gate.QFT r) ψ = qs.eval Gate.id ψ

  eval_QFT_size1 :
    ∀ (r : ExtReg) (ψ : qs.State)
      (hsize : r.width = 1),
      qs.eval (Gate.QFT r) ψ =
        qs.eval (Gate.H (r.active.lowQubit (by
          simp [ExtReg.width] at hsize
          omega))) ψ

  eval_QFT_ket :
    ∀ (r : ExtReg) (b : qs.Basis),
      qs.eval (Gate.QFT r) (qs.ket b)
        =
      ((1 / Real.sqrt ((2^r.width : ℕ) : ℝ) : ℂ)) •
        ∑ y : Fin (2^r.width),
          (qftPhase (2^r.width) (ExtReg.toNat r b) y.1) •
            qs.ket (RegEncoding.writeNat r.active y.1 b)

  eval_adj_QFT_ket :
    ∀ (r : ExtReg) (b : qs.Basis),
      qs.eval (Gate.adj (Gate.QFT r)) (qs.ket b)
        =
      ((1 / Real.sqrt ((ASize r.active : ℕ) : ℝ) : ℂ)) •
        ∑ y : Fin (ASize r.active),
          star
              (qftPhase
                (ASize r.active)
                (ExtReg.toNat r b)
                y.1) •
            qs.ket (RegEncoding.writeNat r.active y.1 b)

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
      (hpos : 0 < regSize r) →
      RegEncoding.toNat r b = 0 →
      qs.eval (Gate.X (r.lowQubit hpos)) (qs.ket b)
        =
      qs.ket
        (RegEncoding.writeNat r 1 b)

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
  [RegEncoding qs.Basis] : Type where

  eval_SignedPhaseProd_ket :
    ∀ (phi : ℝ) (x z : ExtReg) (b : qs.Basis),
      qs.eval (Gate.SignedPhaseProd phi x z) (qs.ket b)
        =
      (Complex.exp
        (phi * Complex.I *
          (((extToInt x b : ℤ) : ℂ) *
           (((extToInt z b : ℤ) : ℂ))))) •
        qs.ket b

  eval_CSignedPhaseProd_ket :
    ∀ (ctrl : ℕ) (phi : ℝ) (x z : ExtReg) (b : qs.Basis),
      qs.eval (Gate.CSignedPhaseProd ctrl phi x z) (qs.ket b)
        =
      if RegEncoding.bit ctrl b then
        (Complex.exp
          (phi * Complex.I *
            (((extToInt x b : ℤ) : ℂ) *
             (((extToInt z b : ℤ) : ℂ))))) •
          qs.ket b
      else
        qs.ket b

/-- Zero/sign extension and deallocation semantic facts. -/
class ExtensionSemantics
  (qs : QSemantics)
  [RegEncoding qs.Basis] : Type where

  eval_zeroExtend :
    ∀ (r : ExtReg) (n : ℕ) (ψ : qs.State),
      qs.eval (Gate.zeroExtend r n) ψ = ψ

  eval_zeroDealloc :
    ∀ (r : ExtReg) (n : ℕ) (ψ : qs.State),
      qs.eval (Gate.zeroDealloc r n) ψ = ψ

  eval_signExtend_ket :
    ∀ (r : ExtReg) (n : ℕ) (b : qs.Basis),
    r.CanGrow n → ExtReg.FreshFor r n b →
      ∃ b' : qs.Basis,
        qs.eval (Gate.signExtend r n) (qs.ket b) = qs.ket b'
        ∧
        ExtReg.toNat r b' = ExtReg.toNat r b
        ∧
        extToInt (r.grow n) b' = extToInt r b
        ∧
        (∀ e : ExtReg, ExtReg.ActiveDisjoint e (r.grow n) →
          ExtReg.toNat e b' = ExtReg.toNat e b)

  eval_signDealloc_eq_adj :
    ∀ r n ψ,
      qs.eval (Gate.signDealloc r n) ψ = qs.eval (Gate.adj (Gate.signExtend r n)) ψ

theorem ExtReg.toNat_grow_of_fresh
    (r : ExtReg)
    (n : ℕ)
    (b : Basis)
    (_hcap : r.CanGrow n)
    (hzero : r.FreshFor n b) :
    ExtReg.toNat (r.grow n) b =
      ExtReg.toNat r b := by
  exact Gate.ExtReg.toNat_grow_of_fresh r n b hzero

theorem eval_zeroExtend_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtensionSemantics qs]
    (r : ExtReg)
    (n : ℕ)
    (b : qs.Basis)
    (hcap : r.CanGrow n)
    (hzero : ExtReg.FreshFor r n b) :
    qs.eval
        (Gate.zeroExtend r n)
        (qs.ket b)
      =
    qs.ket b
    ∧
    ExtReg.toNat (r.grow n) b =
      ExtReg.toNat r b := by
  constructor
  · exact ExtensionSemantics.eval_zeroExtend r n (qs.ket b)
  · exact ExtReg.toNat_grow_of_fresh r n b hcap hzero

lemma zeroExtend_preserves_bit
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtensionSemantics qs]
    (r : ExtReg)
    (n : ℕ)
    (b b' : qs.Basis)
    (q : ℕ)
    (hEval :
      qs.eval (Gate.zeroExtend r n) (qs.ket b) =
        qs.ket b') :
    RegEncoding.bit q b' =
      RegEncoding.bit q b := by
  have hket :
      qs.ket b = qs.ket b' := by
    calc
      qs.ket b
          = qs.eval (Gate.zeroExtend r n) (qs.ket b) := by
              symm
              exact ExtensionSemantics.eval_zeroExtend
                r n (qs.ket b)
      _ = qs.ket b' := hEval

  have hb : b = b' := qs.ket_inj hket
  subst b'
  rfl

lemma signExtend_preserves_disjoint_extToInt
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtensionSemantics qs]
    (r e : ExtReg)
    (n : ℕ)
    (b b' : qs.Basis)
    (hcap : r.CanGrow n)
    (hfresh : r.FreshFor n b)
    (hdisj :
      ExtReg.ActiveDisjoint e (r.grow n))
    (heval :
      qs.eval (Gate.signExtend r n) (qs.ket b) =
        qs.ket b') :
    extToInt e b' = extToInt e b := by
  rcases ExtensionSemantics.eval_signExtend_ket
      r n b hcap hfresh with
    ⟨bout, heval', _hr, _hwide, hloc⟩

  have hbout : bout = b' := by
    apply qs.ket_inj
    rw [← heval, ← heval']

  subst bout

  unfold extToInt
  rw [hloc e hdisj]

lemma tcDecodeWidth_succ_eq_of_lt {w n : ℕ} (h : n < 2 ^ w) :
  tcDecodeWidth (w + 1) n = (n : ℤ) := by
  simp [tcDecodeWidth, h]

class ArithmeticSemantics
    (qs : QSemantics)
    [RegEncoding qs.Basis] : Type where

  eval_ShiftL_ket_exact :
    ∀ (r : ExtReg) (n : ℕ) (b : qs.Basis),
    FitsSignedWidth r.width ((2 : ℤ) ^ n * extToInt r b) →
      ∃ b' : qs.Basis,
        qs.eval (Gate.ShiftL r n) (qs.ket b) = qs.ket b'
        ∧
        extToInt r b' = (2 : ℤ) ^ n * extToInt r b
        ∧
        (∀ e : ExtReg, ExtReg.ActiveDisjoint e r →
           extToInt e b' = extToInt e b)

  eval_ShiftR_ket_exact :
    ∀ (r : ExtReg) (n : ℕ) (b : qs.Basis) (q : ℤ),
    extToInt r b = (2 : ℤ) ^ n * q →
    FitsSignedWidth r.width q →
    ∃ b' : qs.Basis,
      qs.eval (Gate.ShiftR r n) (qs.ket b) = qs.ket b'
        ∧
      extToInt r b' = q
        ∧
      (∀ e : ExtReg,  ExtReg.ActiveDisjoint e r →
           extToInt e b' = extToInt e b)

  eval_Negate_ket_mod :
    ∀ (r : ExtReg) (b : qs.Basis),
    ∃ b' : qs.Basis,
      qs.eval (Gate.Negate r) (qs.ket b) = qs.ket b'
        ∧
      extToInt r b' = tcWrapInt r.width (- extToInt r b)
        ∧
      (∀ e : ExtReg,  ExtReg.ActiveDisjoint e r →
         extToInt e b' = extToInt e b)

  eval_AddScaled_ket_mod :
    ∀ (dst src : ExtReg) (negSrc : Bool) (sh : ℕ) (b : qs.Basis),
    ExtReg.ActiveDisjoint dst src →
    ∃ b' : qs.Basis,
      qs.eval (Gate.AddScaled dst src negSrc sh) (qs.ket b) = qs.ket b'
        ∧
      extToInt dst b' = tcWrapInt dst.width (extToInt dst b + (if negSrc then (-1 : ℤ) else 1) * (2 : ℤ) ^ sh * extToInt src b)
        ∧
      extToInt src b' = extToInt src b
        ∧
      (∀ e : ExtReg,
          ExtReg.ActiveDisjoint e dst →
          ExtReg.ActiveDisjoint e src →
           extToInt e b' = extToInt e b)


/-- Bundled semantic interface for all gate families used in this file. -/
class GateSemanticsFacts
  (qs : QSemantics)
  [RegEncoding qs.Basis] :
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
    ∀ (r : ExtReg) (b : qs.Basis),
      ExtReg.toNat r b = 0 →
      qs.eval
          ((regQubits r.active).foldl
            (fun acc q => Gate.seq (Gate.H q) acc)
            Gate.id)
          (qs.ket b)
        =
      qs.eval (Gate.QFT r) (qs.ket b)

namespace GateSemanticsFacts

variable {qs : QSemantics}
variable [RegEncoding qs.Basis]
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


private lemma zeroExtend_preserves_bit
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtensionSemantics qs]
    (r : ExtReg)
    (n : ℕ)
    (b b' : qs.Basis)
    (q : ℕ)
    (hEval :
      qs.eval (Gate.zeroExtend r n) (qs.ket b) = qs.ket b') :
    RegEncoding.bit q b' = RegEncoding.bit q b := by
  classical
  exact Shor.zeroExtend_preserves_bit qs r n b b' q hEval

lemma eval_CSignedPhaseProd_ket_as_if_SignedPhaseProd
    (qs : QSemantics)
    [RegEncoding qs.Basis]
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

open Gate
/--
Semantic bridge for the unsigned macro: on clean workspace, `PhaseProdUsing` contributes
exactly the expected phase `exp(i * phi * x * z)` and restores the basis state.
-/
theorem eval_PhaseProdUsing_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (phi : ℝ)
    (x z : Reg)
    (ws : Gate.PhaseProdWorkspace x z)
    (b : qs.Basis)
    (hclean : ws.Clean b) :
    qs.eval
        (Gate.PhaseProdUsing phi x z ws)
        (qs.ket b)
      =
    Complex.exp
        (phi * Complex.I *
          ((RegEncoding.toNat x b : ℂ) *
           (RegEncoding.toNat z b : ℂ))) •
      qs.ket b := by
  have hxFresh :
      ws.xExt.FreshFor 1 b :=
    hclean.1

  have hzFresh :
      ws.zExt.FreshFor 1 b :=
    hclean.2

  have hxInt :
      extToInt
          (ws.xExt.grow 1) b
        =
      (RegEncoding.toNat x b : ℤ) := by
    simpa using
      (ExtReg.extToInt_grow_of_fresh
        (e := ws.xExt)
        (n := 1)
        (b := b)
        ws.xExt_canGrow
        hxFresh
        (by omega))

  have hzInt :
      extToInt
          (ws.zExt.grow 1) b
        =
      (RegEncoding.toNat z b : ℤ) := by
    simpa using
      (ExtReg.extToInt_grow_of_fresh
        (e := ws.zExt)
        (n := 1)
        (b := b)
        ws.zExt_canGrow
        hzFresh
        (by omega))

  simp only [
    Gate.PhaseProdUsing,
    qs.eval_seq,
    ExtensionSemantics.eval_zeroExtend,
    ExtensionSemantics.eval_zeroDealloc
  ]

  rw [PhaseSemantics.eval_SignedPhaseProd_ket]
  rw [hxInt, hzInt]

  simp

/-- Controlled version of `eval_PhaseProdUsing_ket`; the phase appears only when `ctrl` is one. -/
theorem eval_CPhaseProdUsing_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : Reg)
    (ws : Gate.PhaseProdWorkspace x z)
    (b : qs.Basis)
    (hclean : ws.Clean b):
    qs.eval
        (Gate.CPhaseProdUsing ctrl phi x z ws)
        (qs.ket b)
      =
    (if RegEncoding.bit ctrl b then
        Complex.exp
          (phi * Complex.I *
            ((RegEncoding.toNat x b : ℂ) *
             (RegEncoding.toNat z b : ℂ)))
      else
        1) •
      qs.ket b := by
  have hxFresh :
      ws.xExt.FreshFor 1 b :=
    hclean.1

  have hzFresh :
      ws.zExt.FreshFor 1 b :=
    hclean.2

  have hxInt :
      extToInt
          (ws.xExt.grow 1) b
        =
      (RegEncoding.toNat x b : ℤ) := by
    simpa using
      (ExtReg.extToInt_grow_of_fresh
        (e := ws.xExt)
        (n := 1)
        (b := b)
        ws.xExt_canGrow
        hxFresh
        (by omega))

  have hzInt :
      extToInt
          (ws.zExt.grow 1) b
        =
      (RegEncoding.toNat z b : ℤ) := by
    simpa using
      (ExtReg.extToInt_grow_of_fresh
        (e := ws.zExt)
        (n := 1)
        (b := b)
        ws.zExt_canGrow
        hzFresh
        (by omega))

  simp only [Gate.CPhaseProdUsing, qs.eval_seq, ExtensionSemantics.eval_zeroExtend,ExtensionSemantics.eval_zeroDealloc]

  rw [PhaseSemantics.eval_CSignedPhaseProd_ket]
  rw [hxInt, hzInt]

  by_cases hc : RegEncoding.bit ctrl b
  · simp [hc]
  · simp [hc]

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

lemma FreshZero.of_eq_on_bits
    {Basis : Type u}
    [RegEncoding Basis]
    (r : Reg)
    (b₁ b₂ : Basis)
    (hbits :
      ∀ q : ℕ,
        q ∈ r.qubits →
        RegEncoding.bit q b₂ =
          RegEncoding.bit q b₁)
    (hzero : FreshZero r b₁) :
    FreshZero r b₂ := by
  unfold FreshZero at hzero ⊢

  apply Nat.zero_of_testBit_eq_false
  intro j

  by_cases hj : j < regSize r

  · let i : Fin (regSize r) :=
      ⟨j, hj⟩

    let q : ℕ :=
      r.get i

    have hq :
        q ∈ r.qubits := by
      dsimp [q, i, Reg.get]
      exact List.get_mem r.qubits _

    calc
      Nat.testBit
          (RegEncoding.toNat r b₂)
          j
          =
        RegEncoding.bit q b₂ := by
          symm
          simpa [q, i] using
            RegEncoding.bit_eq_testBit_toNat
              r b₂ i

      _ =
        RegEncoding.bit q b₁ :=
          hbits q hq

      _ =
        Nat.testBit
          (RegEncoding.toNat r b₁)
          j := by
            simpa [q, i] using
              RegEncoding.bit_eq_testBit_toNat
                r b₁ i

      _ = false := by
        rw [hzero]
        simp

  · have hwidth :
        regSize r ≤ j :=
      Nat.le_of_not_gt hj

    have hToNat :
        RegEncoding.toNat r b₂
          <
        2 ^ regSize r := by
      simpa [ASize] using
        RegEncoding.toNat_lt_ASize
          (r := r)
          (b := b₂)

    have hpow :
        2 ^ regSize r ≤ 2 ^ j := by
      exact
        Nat.pow_le_pow_right
          (by omega)
          hwidth

    exact
      Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le hToNat hpow)
end Shor
