import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.Body.NoPhaseRuns

namespace Shor
open Gate
open Operations
open scoped BigOperators

/-! =========================================================
    Phase Gates And Block Induction
    After the no-phase arithmetic prefix of a block has produced the matching
    row, the phase gate contributes exactly the scalar prescribed by the phase
    product. The block inductions compose those scalars across all points.
========================================================= -/

/-- An uncontrolled phase-product gate contributes the scalar for a matched point row. -/
lemma eval_matched_phase_ket_from
  (qs : QSemantics)
  [RegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ}
  (src dst : LayoutState k)
  (σ : State k)
  (b0 b1 : qs.Basis)
  (hk0 : 0 < k)
  (i : Fin k)
  (pt : Point)
  (phi : Angle)
  (hEnc : EncodesStateFrom (qs := qs) src dst σ b0 b1)
  (hmatch : matchesAt_pointRow_state (k := k) hk0 σ i pt = true) :
  qs.eval
      (Gate.SignedPhaseProd phi (dst.xslot i) (dst.zslot i))
      (qs.ket b1)
    =
  (Complex.exp
      (((Angle.toReal phi : ℝ) : ℂ) * Complex.I *
        (((evalRowX (qs := qs) src (expectedRow (k := k) pt) b0 : ℤ) : ℂ) *
         (((evalRowZ (qs := qs) src (expectedRow (k := k) pt) b0 : ℤ) : ℂ))))) •
    qs.ket b1 := by
  simp[PhaseSemantics.eval_SignedPhaseProd_ket]
  have hσi : σ i = expectedRow (k := k) pt := by
    unfold matchesAt_pointRow_state regEqExpected at hmatch
    have hall : ∀ j : Fin k, σ i j = expectedRow (k := k) pt j := by
      intro j
      have hmem : j ∈ List.finRange k := List.mem_finRange j
      have := List.all_eq_true.mp hmatch j hmem
      simpa using of_decide_eq_true this
    funext j
    exact hall j
  rw [hEnc.1 i, hσi]
  rw [hEnc.2 i, hσi]

/-- A controlled phase-product gate contributes the same scalar exactly when the control bit is set. -/
lemma eval_matched_cphase_ket_from
  (qs : QSemantics)
  [RegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ}
  (src dst : LayoutState k)
  (σ : State k)
  (b0 b1 : qs.Basis)
  (hk0 : 0 < k)
  (ctrl : ℕ)
  (i : Fin k)
  (pt : Point)
  (phi : Angle)
  (hEnc : EncodesStateFrom (qs := qs) src dst σ b0 b1)
  (hmatch : matchesAt_pointRow_state (k := k) hk0 σ i pt) :
  qs.eval
      (Gate.CSignedPhaseProd ctrl phi (dst.xslot i) (dst.zslot i))
      (qs.ket b1)
    =
  if RegEncoding.bit ctrl b1 then
    (Complex.exp
        (((Angle.toReal phi : ℝ) : ℂ) * Complex.I *
          (((evalRowX (qs := qs) src (expectedRow (k := k) pt) b0 : ℤ) : ℂ) *
           (((evalRowZ (qs := qs) src (expectedRow (k := k) pt) b0 : ℤ) : ℂ))))) •
      qs.ket b1
  else
    qs.ket b1 := by
  by_cases hctrl : RegEncoding.bit ctrl b1
  · rw [PhaseSemantics.eval_CSignedPhaseProd_ket]
    rw [if_pos hctrl, if_pos hctrl]
    have hσi : σ i = expectedRow (k := k) pt := by
      unfold matchesAt_pointRow_state regEqExpected at hmatch
      have hall : ∀ j : Fin k, σ i j = expectedRow (k := k) pt j := by
        intro j
        have hmem : j ∈ List.finRange k := List.mem_finRange j
        have := List.all_eq_true.mp hmatch j hmem
        simpa using of_decide_eq_true this
      funext j
      exact hall j
    rw [hEnc.1 i, hσi]
    rw [hEnc.2 i, hσi]
  · rw [PhaseSemantics.eval_CSignedPhaseProd_ket]
    rw [if_neg hctrl, if_neg hctrl]

end Shor
