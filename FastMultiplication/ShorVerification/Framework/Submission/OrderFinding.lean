import FastMultiplication.ShorVerification.Framework.Math.ShorDefinition
import FastMultiplication.ShorVerification.Framework.Semantics.GateSemantics
import FastMultiplication.ShorVerification.Framework.Quantum.Measurement

namespace Shor

/-!
# Framework/Spec: order-finding interface

Submission-facing order-finding data, measurement semantics, and success
probabilities. This module deliberately imports only framework modules.
-/

variable {qs : QSemantics}
variable [RegEncoding qs.Basis]

/-- Run an arbitrary circuit-like object `C` using `evalC`, then measure `r`. -/
noncomputable def measProbAfter
    [MeasureClass qs]
    {Circuit : Type}
    (evalC : Circuit → qs.State → qs.State)
    (r : Reg)
    (o : ℕ)
    (C : Circuit)
    (ψ : qs.State) : ℝ :=
  MeasureClass.probMeas (qs := qs) r o (evalC C ψ)

/-- Success probability after an arbitrary circuit-like object `C`.

`evalC` specifies how that circuit type acts on states. -/
noncomputable def probability_of_success
    [MeasureClass qs]
    [ContinuedFractionPost]
    {Circuit : Type}
    (evalC : Circuit → qs.State → qs.State)
    (T : ℕ → ℕ)
    (verify : OrderVerifier)
    (x : Reg)
    (r Q : ℕ)
    (C : Circuit)
    (ψ : qs.State) : ℝ :=
  ∑ o : Fin Q,
    (r_found (T := T) verify o.1 Q r) *
      measProbAfter
        (qs := qs) evalC x o.1 C ψ

/-- Arithmetic, width, and continued-fraction assumptions for one
order-finding instance. -/
structure ShorOrderFindingInstance where
  /-- The base whose order is being found. -/
  a : ℕ
  /-- The modulus to factor. -/
  N : ℕ
  /-- The exponent/control register. -/
  x : ExtReg
  /-- The modular-exponentiation data register. -/
  y : ExtReg
  /-- The sampled base is in the valid range. -/
  range : 0 < a ∧ a < N
  /-- The sampled base is coprime to the modulus. -/
  coprime : Nat.gcd a N = 1
  /-- The exponent register has the standard Shor width. -/
  x_width : regSize x.active = Nat.log2 (2 * N^2)
  /-- The data register has enough room for residues modulo `N`. -/
  y_width : regSize y.active = Nat.log2 (2 * N)
  /-- The public exponent and data registers occupy distinct qubits. -/
  xy_disjoint : Disjoint x.active y.active

/-- Clean ideal input expected by order-finding: zero exponent/data registers
and disjoint ownership. -/
def IdealOrderFindingInput
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (x y : ExtReg)
    (b0 : qs.Basis) : Prop :=
  RegEncoding.toNat x.active b0 = 0 ∧
  RegEncoding.toNat y.active b0 = 0 ∧
  ExtReg.OwnedDisjoint x y

end Shor
