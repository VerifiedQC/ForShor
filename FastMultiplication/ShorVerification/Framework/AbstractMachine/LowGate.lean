import FastMultiplication.ShorVerification.Framework.Quantum.Registers
import Mathlib.Data.Complex.Basic

namespace Shor

/-!
# Low-Level Gate Language

This file contains the target language accepted by the framework submission and
cost interfaces. The reference implementation lowers its richer `Gate` syntax
to `LowGate`; a different implementation may construct `LowGate` programs
directly.
-/

/-! =========================================================
    Low-level target syntax

    `LowGate` mirrors primitive high-level gates and includes explicit nodes
    for allocation, deallocation, phase-product fallbacks, and radix reversal.
========================================================= -/

/-- Low-level target gate language for lowering. -/
inductive LowGate : Type
  -- Structural circuit operations.
  | id : LowGate
  | seq : LowGate → LowGate → LowGate
  | adj : LowGate → LowGate
  -- Elementary one-qubit gates, addressed by physical qubit number.
  | H : ℕ → LowGate
  | X : ℕ → LowGate
  -- Opaque backend primitive identified by a tag and numeric payload.
  | Prim : String → List ℕ → LowGate
  -- Signed arithmetic on active portions of extendable registers.
  | ShiftL    : (r : ExtReg) → (n : ℕ) → LowGate
  | ShiftR    : (r : ExtReg) → (n : ℕ) → LowGate
  | Negate    : (r : ExtReg) → LowGate
  | AddScaled : (dst src : ExtReg) → (negSrc : Bool) → (shift : ℕ) → LowGate
  -- Direct phase-product operations used as lowering base cases.
  | Naive_SignedPhaseProd : (phi : Real) → (x z : ExtReg) → LowGate
  | Naive_CSignedPhaseProd : (ctrl : ℕ) → (phi : Real) → (x z : ExtReg) → LowGate
  -- Activate or deactivate reserve bits under zero/sign-extension conventions.
  | zeroExtend : (r : ExtReg) → (n : ℕ) → LowGate
  | signExtend : (r : ExtReg) → (n : ℕ) → LowGate
  | zeroDealloc : (r : ExtReg) → (n : ℕ) → LowGate
  | signDealloc : (r : ExtReg) → (n : ℕ) → LowGate
  -- Recombine a logical register split with the high and low blocks exchanged.
  | RadixReverse : (r : Reg) → (m : ℕ) → LowGate
deriving Inhabited

namespace LowGate

/-- Sequential composition: `U ;; V` runs `U` first, then `V`. -/
infixr:80 " ;; " => LowGate.seq

/-- Adjoint notation for low gates. -/
prefix:90 "†" => LowGate.adj

end LowGate


end Shor
