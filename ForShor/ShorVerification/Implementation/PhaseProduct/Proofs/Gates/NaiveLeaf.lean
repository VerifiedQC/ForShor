import ForShor.ShorVerification.Implementation.PhaseProduct.Statement
import ForShor.ShorVerification.Framework.Semantics.LowGateSemantics
import ForShor.ShorVerification.Framework.Gatecount.CostModel

/-!
# Naive phase-product leaf: gate definitions

The reference (unoptimized) circuit constructions for the signed/controlled
phase product: `Naive_SignedPhaseProd`, `Naive_CSignedPhaseProd`, and the
`ℂ`-valued term/exponent bookkeeping their correctness proofs need. The
correctness lemmas about them live in `Proofs/NaiveLeaf.lean`.
-/

/-!
# Naive phase-product leaf: gate definitions

The reference (unoptimized) circuit constructions for the signed/controlled
phase product: `Naive_SignedPhaseProd`, `Naive_CSignedPhaseProd`, and the
`ℂ`-valued term/exponent bookkeeping their correctness proofs need. The
correctness lemmas about them live in `Proofs/NaiveLeaf.lean`.
-/

namespace Shor

namespace LowerGateClass

def basisBitInt {Basis : Type*} [RegEncoding Basis] (q : ℕ) (b : Basis) : ℤ :=
  if RegEncoding.bit q b then 1 else 0

def signedTermValue {Basis : Type*} [RegEncoding Basis] (b : Basis) (t : ℕ × ℤ) : ℤ :=
  t.2 * basisBitInt t.1 b

noncomputable def signedPairExponent
    {Basis : Type*} [RegEncoding Basis] (phi : Angle) (b : Basis) (xTerm zTerm : ℕ × ℤ) : ℂ :=
  ((Angle.toReal phi : ℝ) : ℂ) * Complex.I *
    (((signedTermValue b xTerm : ℤ) : ℂ) * ((signedTermValue b zTerm : ℤ) : ℂ))

noncomputable def naiveSignedPhaseExponents
    {Basis : Type*} [RegEncoding Basis] (phi : Angle) (x z : ExtReg) (b : Basis) : List ℂ :=
  (signedTerms x).flatMap fun xTerm =>
    (signedTerms z).map fun zTerm => signedPairExponent phi b xTerm zTerm

end LowerGateClass

namespace LowerGateClass

noncomputable def cSignedPairExponent
    {Basis : Type*} [RegEncoding Basis]
    (ctrl : ℕ) (phi : Angle) (b : Basis) (xTerm zTerm : ℕ × ℤ) : ℂ :=
  if RegEncoding.bit ctrl b then signedPairExponent phi b xTerm zTerm else 0

noncomputable def naiveCSignedPhaseExponents
    {Basis : Type*} [RegEncoding Basis]
    (ctrl : ℕ) (phi : Angle) (x z : ExtReg) (b : Basis) : List ℂ :=
  (signedTerms x).flatMap fun xTerm =>
    (signedTerms z).map fun zTerm => cSignedPairExponent ctrl phi b xTerm zTerm

end LowerGateClass

end Shor
