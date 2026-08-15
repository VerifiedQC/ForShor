import FastMultiplication.ShorVerification.Framework.Quantum.Registers
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.Data.Nat.Bitwise

/-!
# Shor verification core — the high-level `Gate` language

`Gate` is the structured proof language used by the reference implementation.
Its operations are given semantics directly and are later lowered to the
framework's `LowGate` target. Framework users interested only in the submission
boundary can treat this file as implementation-side proof infrastructure.
-/

universe u

namespace Shor

variable {Basis : Type u} [RegEncoding Basis]

/-! =========================================================
    Gate language and derived gate macros
========================================================= -/

/--
Abstract gate language used by the verification layer. Low-level gates such
as `Prim` coexist with structured arithmetic, QFT, phase-product, extension,
and deallocation gates.
-/
inductive Gate : Type
  -- Structural circuit operations.
  | id : Gate
  | seq : Gate → Gate → Gate
  | adj : Gate → Gate
  -- Elementary and structured quantum operations.
  | H : ℕ → Gate
  | X : ℕ → Gate
  | QFT : ExtReg → Gate
  | RadixReverse : (r : Reg) → (m : ℕ) → Gate
  | SignedPhaseProd  : (phi : Real) → (x z : ExtReg) → Gate
  | CSignedPhaseProd : (ctrl : ℕ) → (phi : Real) → (x z : ExtReg) → Gate
  -- Opaque reversible primitive identified by a tag and numeric payload.
  | Prim : String → List ℕ → Gate
  -- Signed arithmetic and register-view operations.
  | ShiftL    : (r : ExtReg) → (n : ℕ) → Gate
  | ShiftR    : (r : ExtReg) → (n : ℕ) → Gate
  | Negate    : (r : ExtReg) → Gate
  | AddScaled : (dst src : ExtReg) → (negSrc : Bool) → (shift : ℕ) → Gate
  | zeroExtend : (r : ExtReg) → (n : ℕ) → Gate
  | signExtend : (r : ExtReg) → (n : ℕ) → Gate
  | zeroDealloc : (r : ExtReg) → (n : ℕ) → Gate
  | signDealloc : (r : ExtReg) → (n : ℕ) → Gate

def radixReverseIndex (r : Reg) (m : ℕ) (hm : m ≤ Reg.width r) (kL kH : ℕ) : ℕ :=
  let sp : SplitPoint r := ⟨m, hm⟩
  let right := splitRight r sp
  (ASize right) * kL + kH

namespace Gate

/-- Sequential composition: `U ;; V` runs `U` first, then `V`. -/
infixr:80 " ;; " => Gate.seq
/-- Adjoint circuit notation. -/
prefix:90 "†" => Gate.adj

/-- Taking and dropping at the same logical index partitions a register's qubits. -/
theorem Reg.take_append_drop
    (r : Reg) (n : ℕ) :
    (r.take n).qubits ++ (r.drop n).qubits =
      r.qubits := by
  simp [Reg.take, Reg.drop]

/-- Growing within capacity activates exactly `n` reserve bits. -/
theorem ExtReg.newBits_size
    (e : ExtReg)
    (n : ℕ)
    (hcap : e.CanGrow n) :
    Reg.width (e.newBits n) = n := by
  simp [ExtReg.newBits, ExtReg.CanGrow,
    ExtReg.capacity, Reg.width] at *
  simp[Reg.take]
  omega

/-- Growth changes the active/reserve split but preserves the set and order of owned qubits. -/
theorem ExtReg.ownedQubits_grow
    (e : ExtReg)
    (n : ℕ) :
    (e.grow n).ownedQubits = e.ownedQubits := by
  simp [ExtReg.ownedQubits, ExtReg.grow, Reg.append, ExtReg.newBits,
    ExtReg.remainingReserve, Reg.take, Reg.drop, List.append_assoc]

/-- The active qubits after growth are the previous active qubits followed by the new bits. -/
theorem ExtReg.active_grow_qubits
    (e : ExtReg)
    (n : ℕ) :
    (e.grow n).active.qubits =
      e.active.qubits ++ (e.newBits n).qubits := by
  rfl

/-- Reading a grown register appends the newly active bits above the previous value. -/
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

/-- Activating clean zero reserve bits preserves the unsigned value. -/
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

/-- Adding one or more leading zero bits preserves the decoded nonnegative value. -/
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

/-- Growing by clean zero bits turns the previous unsigned value into the same signed value. -/
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
    QFT phase helpers
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

theorem qftPhase_comm
    (N x y : ℕ) :
    qftPhase N x y =
      qftPhase N y x := by
  simp [qftPhase, ωPow, Nat.mul_comm]

end Shor
