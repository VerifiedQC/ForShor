import FastMultiplication.ShorVerification.Implementation.PhaseProduct.NaivePhaseProduct

namespace Shor

namespace LowGate

noncomputable def CCPhase
    (a b c : ℕ)
    (theta : ℝ) : LowGate :=
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

noncomputable def naiveCSignedPhaseGates
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : ExtReg) : List LowGate :=
  (signedTerms x).flatMap fun xTerm =>
    (signedTerms z).map fun zTerm =>
      LowGate.CCPhase
        ctrl
        xTerm.1
        zTerm.1
        (signedPairAngle phi xTerm zTerm)

noncomputable def Naive_CSignedPhaseProd
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : ExtReg) : LowGate :=
  LowGate.sequence
    (naiveCSignedPhaseGates ctrl phi x z)

end LowGate

namespace LowerGateClass

theorem evalL_naive_csignedPhaseProd_ket
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : ExtReg)
    (b : qs.Basis) :
    LowerGateClass.evalL
        (qs := qs)
        (LowGate.Naive_CSignedPhaseProd ctrl phi x z)
        (qs.ket b)
      =
    if RegEncoding.bit ctrl b then
      (Complex.exp
        (phi * Complex.I *
          (((extToInt x b : ℤ) : ℂ) *
           (((extToInt z b : ℤ) : ℂ))))) •
        qs.ket b
    else
      qs.ket b := by
  sorry

end LowerGateClass

namespace LowGate

theorem gateCount_Naive_CSignedPhaseProd
    (M : LowGateCostModel)
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : ExtReg)
    (hdisjoint : ExtReg.OwnedDisjoint x z)
    (hctrlX : ctrl ∉ x.ownedQubits)
    (hctrlZ : ctrl ∉ z.ownedQubits) :
    LowGate.gateCount M
        (LowGate.Naive_CSignedPhaseProd ctrl phi x z)
      =
    directCSignedPhaseProductGateCount x z := by
  sorry

end LowGate
end Shor
