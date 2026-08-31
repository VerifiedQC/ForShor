import FastMultiplication.ShorVerification.Framework.Semantics.LowerGate
import FastMultiplication.ShorVerification.Framework.Gatecount.CostModel

namespace Shor

namespace LowGate

def sequence : List LowGate → LowGate
  | [] => LowGate.id
  | g :: gs => g ;; sequence gs

noncomputable def CPhase
    (ctrl target : ℕ)
    (theta : ℝ) : LowGate :=
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

noncomputable def signedPairAngle
    (phi : ℝ)
    (xTerm zTerm : ℕ × ℤ) : ℝ :=
  phi * (xTerm.2 : ℝ) * (zTerm.2 : ℝ)

namespace LowGate

noncomputable def naiveSignedPhaseGates
    (phi : ℝ)
    (x z : ExtReg) : List LowGate :=
  (signedTerms x).flatMap fun xTerm =>
    (signedTerms z).map fun zTerm =>
      LowGate.CPhase
        xTerm.1
        zTerm.1
        (signedPairAngle phi xTerm zTerm)

noncomputable def Naive_SignedPhaseProd
    (phi : ℝ)
    (x z : ExtReg) : LowGate :=
  LowGate.sequence (naiveSignedPhaseGates phi x z)

end LowGate

namespace LowerGateClass

theorem evalL_naive_signedPhaseProd_ket
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    (phi : ℝ)
    (x z : ExtReg)
    (b : qs.Basis) :
    LowerGateClass.evalL
        (qs := qs)
        (LowGate.Naive_SignedPhaseProd phi x z)
        (qs.ket b)
      =
    (Complex.exp
      (phi * Complex.I *
        (((extToInt x b : ℤ) : ℂ) *
         (((extToInt z b : ℤ) : ℂ))))) •
      qs.ket b := by
  sorry

theorem gateCount_Naive_SignedPhaseProd
    (M : LowGateCostModel)
    (phi : ℝ)
    (x z : ExtReg)
    (hdisjoint : ExtReg.OwnedDisjoint x z) :
    LowGate.gateCount M
        (LowGate.Naive_SignedPhaseProd phi x z)
      =
    directSignedPhaseProductGateCount x z := by
  sorry
end LowerGateClass

end Shor
