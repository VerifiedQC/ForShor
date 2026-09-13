import FastMultiplication.ShorVerification.Framework.Semantics.GateSemantics
import FastMultiplication.ShorVerification.Implementation.Semantics.GateSemanticsLemmas
import FastMultiplication.ShorVerification.Implementation.Semantics.CleanClosure

/-!
# Modular-Exponentiation Validity

The clean-input predicates for the valid-input subspace the approximation
theorems work on (`GoodModMulBasisInput`, `ValidModMulState`,
`GoodAlgorithm1BasisInput`, `ValidAlgorithm1State`), and the state-level
cleanliness predicates consumed by the two concrete constant-arithmetic
lowerers (`ConstArithmeticCleanBasis`, `CSubConstCleanBasis`,
`CmpGeConstCleanState`, `CSubConstCleanState`).
-/

universe u

namespace Shor

/--
A computational-basis input on which Algorithm 1 is allowed to be called.

The data register contains a canonical residue; the two data reserve bits,
the fractional/work register, and the comparator flag are clean.
All other qubits, including the control and exponent registers, are arbitrary.
-/
def GoodModMulBasisInput
    (qs : QSemantics) [RegEncoding qs.Basis]
    (N : ℕ) (data work : ExtReg) (flag : ℕ) (b : qs.Basis) : Prop :=
  RegEncoding.toNat data.active b < N ∧
  data.FreshFor 2 b ∧
  RegEncoding.toNat work.active b = 0 ∧
  work.FreshFor 1 b ∧
  RegEncoding.toNat (qubitReg flag) b = 0

/--
The full valid-input subspace.

This is the span of *all* computational-basis states satisfying
`GoodModMulBasisInput`; hence it includes arbitrary superpositions over
the control register, exponent register, and valid modular data values.
-/
def ValidModMulState
    (qs : QSemantics) [RegEncoding qs.Basis]
    (N : ℕ) (data work : ExtReg) (flag : ℕ) :
    Submodule ℂ qs.State :=
  Submodule.span ℂ
    ({ ψ : qs.State |
        ∃ b : qs.Basis, GoodModMulBasisInput qs N data work flag b ∧ ψ = qs.ket b } : Set qs.State)

def GoodAlgorithm1BasisInput
    (qs : QSemantics) [RegEncoding qs.Basis]
    (N : ℕ) (data work scratch : ExtReg) (flag : ℕ) (b : qs.Basis) : Prop :=
  GoodModMulBasisInput qs N data work flag b ∧
  RegEncoding.toNat scratch.active b = 0 ∧
  scratch.FreshFor 1 b

def ValidAlgorithm1State
    (qs : QSemantics) [RegEncoding qs.Basis]
    (N : ℕ) (data work scratch : ExtReg) (flag : ℕ) :
    Submodule ℂ qs.State :=
  Submodule.span ℂ
    ({ ψ : qs.State |
        ∃ b : qs.Basis,
          GoodAlgorithm1BasisInput qs N data work scratch flag b ∧ ψ = qs.ket b } : Set qs.State)

/-- Basis-level cleanliness consumed by both Step-3 lowerers. -/
def ConstArithmeticCleanBasis
    {Basis : Type u} [RegEncoding Basis] (data scratch : ExtReg) (b : Basis) : Prop :=
  data.FreshFor 1 b ∧ extToInt scratch b = 0 ∧ scratch.FreshFor 1 b

/-- Basis-level cleanliness consumed by controlled subtraction.  The concrete
lowerer performs fixed-width modular subtraction, so it is total on every
control/data value and needs no hidden no-underflow premise. -/
def CSubConstCleanBasis
    {Basis : Type u} [RegEncoding Basis]
    (_N : ℕ) (data scratch : ExtReg) (_flag : ℕ) (b : Basis) : Prop :=
  ConstArithmeticCleanBasis data scratch b

/-- Linear closure of clean comparison inputs. -/
abbrev CmpGeConstCleanState
    (qs : QSemantics) [RegEncoding qs.Basis] (data scratch : ExtReg) : qs.State → Prop :=
  CleanClosure (ConstArithmeticCleanBasis data scratch)

/-- Linear closure of clean controlled-subtraction inputs. -/
abbrev CSubConstCleanState
    (qs : QSemantics) [RegEncoding qs.Basis]
    (N : ℕ) (data scratch : ExtReg) (flag : ℕ) : qs.State → Prop :=
  CleanClosure (CSubConstCleanBasis N data scratch flag)

end Shor
