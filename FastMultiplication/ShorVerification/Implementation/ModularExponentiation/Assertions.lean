import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Defs

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
    [Spec]
    [GateSemanticsFacts qs]
    [IdealCtrlModMulExactSemantics qs]: Prop :=
  ∃ K : ℝ, 0 ≤ K ∧
    ∀ (η : ℝ) (cfg : ModExpConfig η) (ψ : qs.State),
      ModExpConfig.ValidUnitState qs cfg ψ →
      ‖qs.eval (ModExpConfig.approxGate (Basis := qs.Basis) cfg) ψ -
        qs.eval (ModExpConfig.idealGate qs cfg) ψ‖
        ≤ (tbits cfg.x : ℝ) * stepErr K η

end Shor
