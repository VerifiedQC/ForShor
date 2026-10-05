import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.ModExp
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Spec.Config
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Spec.Precision

/-!
# Modular-Exponentiation Public Assertion

The final semantic claim of the modular-exponentiation implementation, stated as
a named proposition: the approximate modular-exponentiation gate is uniformly
close to the ideal gate, with a constant that does not depend on the precision.
-/

namespace Shor

/--
Uniform approximation bound for modular exponentiation: there is a single
constant `K ≥ 0` such that, on any valid unit state, the approximate
modular-exponentiation gate differs from the ideal gate by at most
`tbits · stepErr K η`.
-/
def ModExpApproxValidDistUniform
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [IdealCtrlModMulExactSemantics qs]: Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ K ≤ 2048 ∧
    ∀ (η : ℝ) (cfg : ModExpConfig η) (ψ : qs.State),
      ModExpConfig.ValidUnitState qs cfg ψ →
      ‖qs.eval (ModExpConfig.approxGate cfg) ψ -
        qs.eval (ModExpConfig.idealGate qs cfg) ψ‖
        ≤ (tbits cfg.x : ℝ) * stepErr K η

/-- The same uniform bound at the explicit constant `2048`.

`ModExpApproxValidDistUniform` hides its constant behind an existential, which
a caller that must *choose* a precision cannot act on. This is the form with
the number in it, and it is what `Shor`'s precision schedule and `Reference`
are stated against. -/
def ModExpApproxValidDist2048
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [IdealCtrlModMulExactSemantics qs] : Prop :=
  ∀ (η : ℝ) (cfg : ModExpConfig η) (ψ : qs.State),
    ModExpConfig.ValidUnitState qs cfg ψ →
    ‖qs.eval (ModExpConfig.approxGate cfg) ψ -
      qs.eval (ModExpConfig.idealGate qs cfg) ψ‖
      ≤ (tbits cfg.x : ℝ) * stepErr 2048 η

end Shor
