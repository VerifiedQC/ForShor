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

/-! =========================================================
    Section 4: Gate language and derived gate macros
========================================================= -/

/--
Abstract gate language used by the verification layer. Elementary gates
coexist with typed structured arithmetic, QFT, phase-product, extension, and
deallocation gates.
-/
inductive Gate : Type
  | id : Gate
  | seq : Gate → Gate → Gate
  | adj : Gate → Gate
  | H : ℕ → Gate
  | X : ℕ → Gate
  | CNOT : ℕ → ℕ → Gate
  | Toffoli : ℕ → ℕ → ℕ → Gate
  | QFT : ExtReg → Gate
  | RadixReverse : (r : Reg) → (m : ℕ) → Gate
  | SignedPhaseProd : (phi : Real) → (x z : ExtReg) → Gate
  | CSignedPhaseProd : (ctrl : ℕ) → (phi : Real) → (x z : ExtReg) → Gate
  | CmpGeConst : (N : ℕ) → (data scratch : ExtReg) → (flag : ℕ) → Gate
  | CSubConst : (N : ℕ) → (data scratch : ExtReg) → (flag : ℕ) → Gate
  | ShiftL : (r : ExtReg) → (n : ℕ) → Gate
  | ShiftR : (r : ExtReg) → (n : ℕ) → Gate
  | Negate : (r : ExtReg) → Gate
  | AddScaled : (dst src : ExtReg) → (negSrc : Bool) → (shift : ℕ) → Gate
  | zeroExtend : (r : ExtReg) → (n : ℕ) → Gate
  | signExtend : (r : ExtReg) → (n : ℕ) → Gate
  | zeroDealloc : (r : ExtReg) → (n : ℕ) → Gate
  | signDealloc : (r : ExtReg) → (n : ℕ) → Gate
  | idealCtrlModMul : (c N : ℕ) → (data : Reg) → (ctrl : ℕ) → Gate

def radixReverseIndex (r : Reg) (m : ℕ) (hm : m ≤ regSize r) (kL kH : ℕ) : ℕ :=
  let sp : SplitPoint r := ⟨m, hm⟩
  let right := splitRight r sp
  (ASize right) * kL + kH

namespace Gate

infixr:80 " ;; " => Gate.seq
prefix:90 "†" => Gate.adj


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

theorem qftPhase_comm
    (N x y : ℕ) :
    qftPhase N x y =
      qftPhase N y x := by
  simp [qftPhase, ωPow, Nat.mul_comm]

end Shor
