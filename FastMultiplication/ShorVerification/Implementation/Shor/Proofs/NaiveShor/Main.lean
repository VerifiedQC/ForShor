import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.NaiveShor.GoodOutcomeMassLowerBound

/-!
# Naive Shor Correctness
-/

namespace Shor

variable {qs : QSemantics}
variable [RegEncoding qs.Basis]
variable [MeasureClass qs]
variable [ContinuedFractionPost]
variable [Spec]

/-! =========================================================
    Ideal Order-Finding Correctness
========================================================= -/

/-- Ideal order-finding success probability for Shor's algorithm. -/
theorem Shor_correct
    [GateSemanticsFacts qs]
    [IdealCtrlModMulExactSemantics qs]
    (T : ℕ → ℕ)
    (hT : ContinuedFractionSearchComplete T)
    (inst : ShorOrderFindingInstance)
    (x y : ExtReg)
    (b0 : qs.Basis)
    (hm : regSize x.active = Nat.log2 (2 * inst.N^2))
    (hn : regSize y.active = Nat.log2 (2 * inst.N))
    (hinput : IdealOrderFindingInput qs x y b0) :
    ShorCorrect T hT inst x y b0 hm hn hinput := by

  unfold ShorCorrect

  have hsetting :
      BasicSetting
        inst.a
        (ord inst.a inst.N inst.coprime)
        inst.N
        (regSize x.active)
        (regSize y.active) :=
    basicSetting_of_shor_instance
      inst
      (regSize x.active)
      (regSize y.active)
      hm
      hn

  calc
    κ / (Nat.log2 inst.N : ℝ) ^ 4
        ≤
      ∑ o : Fin (ASize x.active),
        goodOutcomeIndicator
          o.1
          (ASize x.active)
          (ord inst.a inst.N inst.coprime) *
        measProbAfter
          (qs := qs)
          qs.eval
          x.active
          o.1
          (orderFindingIdeal
            (qs := qs) inst.a inst.N x y)
          (qs.ket b0) :=
      ideal_orderFinding_goodOutcome_mass_lower_bound
        inst x y b0 hsetting hinput

    _ ≤
      probability_of_success
        (qs := qs)
        (T := T)
        (verify :=
          fun d =>
            decide ((inst.a ^ d) % inst.N = 1))
        (x := x.active)
        (r := ord inst.a inst.N inst.coprime)
        (Q := ASize x.active)
        (evalC := qs.eval)
        (C :=
          orderFindingIdeal
            (qs := qs)
            inst.a inst.N x y)
        (ψ := qs.ket b0) :=
      goodOutcome_mass_le_probability_of_success
        T hT inst
        qs.eval
        x.active
        (ASize x.active)
        (orderFindingIdeal
          (qs := qs)
          inst.a inst.N x y)
        (qs.ket b0)

end Shor
