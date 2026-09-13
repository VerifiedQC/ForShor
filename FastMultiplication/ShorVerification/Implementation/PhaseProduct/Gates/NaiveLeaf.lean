import FastMultiplication.ShorVerification.Framework.Semantics.LowGateSemantics
import FastMultiplication.ShorVerification.Framework.Gatecount.CostModel
import FastMultiplication.ShorVerification.Implementation.RegisterLemmas

/-!
# Naive phase-product leaf: gate definitions

The reference (unoptimized) circuit constructions for the signed/controlled
phase product: `Naive_SignedPhaseProd`, `Naive_CSignedPhaseProd`, and the
`ℂ`-valued term/exponent bookkeeping their correctness proofs need. Split out
of `Proofs/NaivePhaseProduct.lean` / `Proofs/NaiveCPhaseProduct.lean` because
these are definitions, not proofs; the correctness lemmas about them stay in
`Proofs/NaiveLeaf.lean`.
-/

namespace Shor

namespace LowGate

def sequence : List LowGate → LowGate
  | [] => LowGate.id
  | g :: gs => g ;; sequence gs

def CPhase
    (ctrl target : ℕ)
    (theta : Angle) : LowGate :=
  if ctrl = target then
    LowGate.Phase ctrl theta
  else
    LowGate.Phase ctrl (theta / 2) ;;
    LowGate.Phase target (theta / 2) ;;
    LowGate.CNOT ctrl target ;;
    LowGate.Phase target (-theta / 2) ;;
    LowGate.CNOT ctrl target

end LowGate

def signedBitWeight (width i : ℕ) : ℤ :=
  if i + 1 = width then
    -((2 : ℤ) ^ i)
  else
    (2 : ℤ) ^ i

def signedTermsAux :
    ℕ → ℕ → List ℕ → List (ℕ × ℤ)
  | _, _, [] => []
  | width, i, q :: qs =>
      (q, signedBitWeight width i) ::
        signedTermsAux width (i + 1) qs

def signedTerms (r : ExtReg) : List (ℕ × ℤ) :=
  signedTermsAux r.width 0 r.active.qubits

def signedPairAngle
    (phi : Angle)
    (xTerm zTerm : ℕ × ℤ) : Angle :=
  phi * (xTerm.2 : ℚ) * (zTerm.2 : ℚ)

namespace LowGate

def naiveSignedPhaseGates
    (phi : Angle)
    (x z : ExtReg) : List LowGate :=
  (signedTerms x).flatMap fun xTerm =>
    (signedTerms z).map fun zTerm =>
      LowGate.CPhase
        xTerm.1
        zTerm.1
        (signedPairAngle phi xTerm zTerm)

def Naive_SignedPhaseProd
    (phi : Angle)
    (x z : ExtReg) : LowGate :=
  LowGate.sequence (naiveSignedPhaseGates phi x z)

end LowGate

namespace LowerGateClass

def basisBitInt
    {Basis : Type*}
    [RegEncoding Basis]
    (q : ℕ)
    (b : Basis) : ℤ :=
  if RegEncoding.bit q b then 1 else 0

def signedTermValue
    {Basis : Type*}
    [RegEncoding Basis]
    (b : Basis)
    (t : ℕ × ℤ) : ℤ :=
  t.2 * basisBitInt t.1 b

noncomputable def signedPairExponent
    {Basis : Type*}
    [RegEncoding Basis]
    (phi : Angle)
    (b : Basis)
    (xTerm zTerm : ℕ × ℤ) : ℂ :=
  ((Angle.toReal phi : ℝ) : ℂ) * Complex.I *
    (((signedTermValue b xTerm : ℤ) : ℂ) *
     (((signedTermValue b zTerm : ℤ) : ℂ)))

noncomputable def naiveSignedPhaseExponents
    {Basis : Type*}
    [RegEncoding Basis]
    (phi : Angle)
    (x z : ExtReg)
    (b : Basis) : List ℂ :=
  (signedTerms x).flatMap fun xTerm =>
    (signedTerms z).map fun zTerm =>
      signedPairExponent phi b xTerm zTerm

end LowerGateClass

namespace LowGate

def CCPhase
    (a b c : ℕ)
    (theta : Angle) : LowGate :=
  if a = b then
    LowGate.CPhase a c theta
  else if a = c then
    LowGate.CPhase a b theta
  else if b = c then
    LowGate.CPhase a b theta
  else
    LowGate.CPhase a b (theta / 2) ;;
    LowGate.Phase c (theta / 2) ;;
    LowGate.Toffoli a b c ;;
    LowGate.Phase c (-theta / 2) ;;
    LowGate.Toffoli a b c

def naiveCSignedPhaseGates
    (ctrl : ℕ)
    (phi : Angle)
    (x z : ExtReg) : List LowGate :=
  (signedTerms x).flatMap fun xTerm =>
    (signedTerms z).map fun zTerm =>
      LowGate.CCPhase
        ctrl
        xTerm.1
        zTerm.1
        (signedPairAngle phi xTerm zTerm)

def Naive_CSignedPhaseProd
    (ctrl : ℕ)
    (phi : Angle)
    (x z : ExtReg) : LowGate :=
  LowGate.sequence
    (naiveCSignedPhaseGates ctrl phi x z)

end LowGate

namespace LowerGateClass

noncomputable def cSignedPairExponent
    {Basis : Type*}
    [RegEncoding Basis]
    (ctrl : ℕ)
    (phi : Angle)
    (b : Basis)
    (xTerm zTerm : ℕ × ℤ) : ℂ :=
  if RegEncoding.bit ctrl b then
    signedPairExponent phi b xTerm zTerm
  else
    0

noncomputable def naiveCSignedPhaseExponents
    {Basis : Type*}
    [RegEncoding Basis]
    (ctrl : ℕ)
    (phi : Angle)
    (x z : ExtReg)
    (b : Basis) : List ℂ :=
  (signedTerms x).flatMap fun xTerm =>
    (signedTerms z).map fun zTerm =>
      cSignedPairExponent ctrl phi b xTerm zTerm

end LowerGateClass

end Shor
