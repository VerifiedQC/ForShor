import FastMultiplication.ShorVerification.Framework.Quantum.Registers
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.Data.Nat.Bitwise

/-!
# Shor verification core — the high-level Gate language
-/

universe u

namespace Shor

variable {Basis : Type u} [RegEncoding Basis]

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


end Shor
