import FastMultiplication.ShorVerification.Framework.Semantics.LowerGate
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.GateLevelCorrectness.GateSemanticsLemmas
import Mathlib.Data.Nat.BitIndices

/-!
# Concrete lowering of Step-3 constant arithmetic

`CmpGeConst` and `CSubConst` remain useful typed gates in the source language,
but they are not primitives of `LowGate`.  This file realizes both operations
with the existing target gates.  One real reserve qubit of `scratch` is used as
the signed one-bit constant `-1`; the active scratch register is computed and
uncomputed around the data operation.
-/

namespace Shor

open LowGate

/-- Static physical conditions needed by the concrete constant-arithmetic
lowerers.  Cleanliness is deliberately kept out of this record. -/
structure ConstArithmeticWorkspace
    (N : ℕ) (data scratch : ExtReg) (flag : ℕ) : Prop where
  data_can_grow : data.CanGrow 1
  scratch_can_grow : scratch.CanGrow 1
  data_scratch_disjoint : data.OwnedDisjoint scratch
  flag_not_data : flag ∉ data.ownedQubits
  flag_not_scratch : flag ∉ scratch.ownedQubits
  scratch_positive : 0 < scratch.width
  constant_fits : N < 2 ^ (scratch.width - 1)
  data_width_fits : data.width ≤ scratch.width - 1

/-- Basis-level cleanliness consumed by both Step-3 lowerers. -/
def ConstArithmeticCleanBasis
    {Basis : Type u} [RegEncoding Basis]
    (data scratch : ExtReg) (b : Basis) : Prop :=
  data.FreshFor 1 b ∧
  extToInt scratch b = 0 ∧
  scratch.FreshFor 1 b

/-- Basis-level cleanliness consumed by controlled subtraction.  The concrete
lowerer performs fixed-width modular subtraction, so it is total on every
control/data value and needs no hidden no-underflow premise. -/
def CSubConstCleanBasis
    {Basis : Type u} [RegEncoding Basis]
    (_N : ℕ) (data scratch : ExtReg) (_flag : ℕ) (b : Basis) : Prop :=
  ConstArithmeticCleanBasis data scratch b

/-- Linear closure of clean comparison inputs. -/
abbrev CmpGeConstCleanState
    (qs : QSemantics) [RegEncoding qs.Basis]
    (data scratch : ExtReg) : qs.State → Prop :=
  CleanClosure (ConstArithmeticCleanBasis data scratch)

/-- Linear closure of clean controlled-subtraction inputs. -/
abbrev CSubConstCleanState
    (qs : QSemantics) [RegEncoding qs.Basis]
    (N : ℕ) (data scratch : ExtReg) (flag : ℕ) : qs.State → Prop :=
  CleanClosure (CSubConstCleanBasis N data scratch flag)

/-- The first genuinely allocated reserve qubit of `scratch`. -/
def constArithmeticUnitQubit
    (scratch : ExtReg) (h : scratch.CanGrow 1) : ℕ :=
  (scratch.newBits 1).get
    ⟨0, by
      have hsize := Gate.ExtReg.newBits_size scratch 1 h
      have hwidth : (scratch.newBits 1).width = 1 := by
        simpa [regSize] using hsize
      omega⟩

/-- Regard the one-bit constant workspace as a signed extendable register. -/
def constArithmeticUnit
    (scratch : ExtReg) (h : scratch.CanGrow 1) : ExtReg :=
  ExtReg.ofReg (qubitReg (constArithmeticUnitQubit scratch h))

/-- Copy a classical bit pattern into `dst`, controlled by one physical qubit.
Out-of-range indices are ignored; the workspace proof later shows that every
bit of the chosen constant is in range. -/
def lowerCopyBitPowers
    (dst : ExtReg) (ctrl : ℕ) : List ℕ → LowGate
  | [] => LowGate.id
  | i :: bits =>
      if hi : i < dst.width then
        LowGate.CNOT ctrl
          (dst.active.get
            ⟨i, by simpa [ExtReg.width] using hi⟩) ;;
        lowerCopyBitPowers dst ctrl bits
      else
        lowerCopyBitPowers dst ctrl bits

/-- Controlled-write the binary expansion of `N` into a clean register. -/
def lowerCopyConstFromUnit
    (N : ℕ) (dst : ExtReg) (ctrl : ℕ) : LowGate :=
  lowerCopyBitPowers dst ctrl N.bitIndices

/-- Prepare `scratch = -N` from clean active scratch and one clean reserve bit.
The constant write is at most one CNOT per active bit; the final negation is
one linear-cost target operation. -/
def lowerPrepareNegConst
    (N : ℕ) (scratch : ExtReg) (h : scratch.CanGrow 1) : LowGate :=
  let q := constArithmeticUnitQubit scratch h
  LowGate.X q ;;
  lowerCopyConstFromUnit N scratch q ;;
  LowGate.Negate scratch

/-- Compare the unsigned active value of `data` against `N` and toggle `flag`
iff `N ≤ data`.  The extra data bit makes the source unsigned; `scratch` is
restored by the adjoint computation. -/
def lowerCmpGeConst
    (N : ℕ) (data scratch : ExtReg) (flag : ℕ)
    (h : ConstArithmeticWorkspace N data scratch flag) : LowGate :=
  let prep := lowerPrepareNegConst N scratch h.scratch_can_grow
  let sign := scratch.active.get
    ⟨scratch.width - 1, by
      have hlt : scratch.width - 1 < scratch.width :=
        Nat.sub_lt h.scratch_positive (by omega)
      simpa [ExtReg.width, regSize] using hlt⟩
  let diff :=
    LowGate.zeroExtend data 1 ;;
    LowGate.AddScaled scratch (data.grow 1) false 0 ;;
    LowGate.zeroDealloc data 1
  prep ;;
  diff ;;
  (LowGate.X flag ;;
   LowGate.CNOT sign flag) ;;
  †diff ;;
  †prep

/-- Conditionally subtract `N` modulo the active width of `data`.  The control
prepares `scratch` as either `0` or `-N`; one fixed-width `AddScaled` performs
the modular subtraction, and the preparation is then uncomputed. -/
def lowerCSubConst
    (N : ℕ) (data scratch : ExtReg) (flag : ℕ)
    (h : ConstArithmeticWorkspace N data scratch flag) : LowGate :=
  let q := constArithmeticUnitQubit scratch h.scratch_can_grow
  let prep :=
    LowGate.CNOT flag q ;;
    lowerCopyConstFromUnit N scratch q ;;
    LowGate.Negate scratch
  prep ;;
  LowGate.AddScaled data scratch false 0 ;;
  †prep

end Shor
