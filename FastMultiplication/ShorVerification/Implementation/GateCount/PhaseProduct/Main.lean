import FastMultiplication.ShorVerification.Implementation.GateCount.PhaseProduct.Lemmas

namespace Shor

/-! =========================================================
    PhaseProduct Gate-Count Main Theorems

This file keeps the important proof structure for the public PhaseProduct bounds.
The technical lemmas are proved in `PhaseProduct.Lemmas`; here we assemble the
program hypotheses, recurrence solution, generated-program facts, and controlled
comparison into the final theorem statements.
========================================================= -/

/-! ---------------------------------------------------------
    Unsigned PhaseProduct main theorem
--------------------------------------------------------- -/

theorem phaseProductGateCountBound_of_programOK
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (hops : PhaseProductProgramOK k hk ops) :
    PhaseProductGateCountBound (Basis := Basis) k hk ops := by

  have hcount :
      phaseProductCount ops = q k := by
    unfold PhaseProductProgramOK at hops
    dsimp at hops
    exact hops.2.2.2

  have hbalancedWidth :
      ∃ c : ℕ, ∀ x z : ExtReg,
        ExtReg.width x = ExtReg.width z →
        nextSignedWidth x z ops ≤ (ExtReg.width x + k - 1) / k + c :=
    prog_balanced_nextSignedWidth k hk ops

  have hoverhead :
      ∃ A B : ℕ, ∀ W : ℕ,
        phaseProgramOverhead W ops ≤ A * W + B :=
    phaseProgramOverhead_linear ops

  obtain ⟨C, hC, hbalanced⟩ :=
    balanced_phaseProduct_recurrence_solution
      (Basis := Basis) k hk ops hcount hbalancedWidth hoverhead

  have hgrowth :
      ∃ c : ℕ, ∀ x z : ExtReg,
        nextSignedWidth x z ops ≤ phaseInputSize x z + c :=
    prog_nextSignedWidth_le_input_add_const k hk ops

  have hnarrow :
      ∃ d : ℕ, ∀ x z : ExtReg,
        ¬ nextSignedWidth x z ops < phaseInputSize x z →
        min (ExtReg.width x) (ExtReg.width z) ≤ d :=
    prog_no_recurse_implies_small_operand k hk ops

  exact phaseProductGateCountBound_of_balanced_signed_bound
    (Basis := Basis) k hk ops hcount hoverhead hgrowth hnarrow C hC hbalanced


/-! ---------------------------------------------------------
    Controlled PhaseProduct main theorem
--------------------------------------------------------- -/

namespace CPhaseProductReduction

theorem cPhaseProductGateCountBound_of_programOK
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (hops : PhaseProductProgramOK k hk ops) :
    CPhaseProductGateCountBound
      (Basis := Basis) k hk ops := by
  obtain ⟨C, hC, n₀, hn₀, hbound⟩ :=
    phaseProductGateCountBound_of_programOK
      (Basis := Basis) k hk ops hops
  refine ⟨5 * C, by positivity, n₀, hn₀, ?_⟩
  intro ctrl φ x z ws hworkspace
  dsimp only
  intro hn
  let hc :
      CSignedRecursiveWorkspaceOK ops ctrl
        (ws.xExt.grow 1)
        (ws.zExt.grow 1) :=
    cPhaseProdUsing_controlledWorkspace
      ops ctrl φ x z ws hworkspace
  let hs :
      SignedRecursiveWorkspaceOK ops
        (ws.xExt.grow 1)
        (ws.zExt.grow 1) :=
    hc.toSignedRecursiveWorkspaceOK
  have hunsignedWorkspace :
      GateWorkspaceOK ops
        (Gate.PhaseProdUsing φ x z ws) := by
    simpa [GateWorkspaceOK, Gate.PhaseProdUsing] using hs
  have hdomNat :
      cSignedPhaseProductGateCount
          (Basis := Basis)
          k hk ops ctrl φ
          (ws.xExt.grow 1)
          (ws.zExt.grow 1)
          hc
        ≤
      5 *
        signedPhaseProductGateCount
          (Basis := Basis)
          k hk ops φ
          (ws.xExt.grow 1)
          (ws.zExt.grow 1)
          hs :=
    cSignedPhaseProductGateCount_le_five_signed
      (Basis := Basis)
      k hk ops ctrl φ
      (ws.xExt.grow 1)
      (ws.zExt.grow 1)
      hc
  have hb :=
    hbound φ x z ws hunsignedWorkspace hn
  rw [
    lowerGate_CPhaseProdUsing_gateCount_eq_cSigned
      (Basis := Basis)
      k hk ops ctrl φ x z ws hworkspace
  ]
  have hdomReal :
      (cSignedPhaseProductGateCount
          (Basis := Basis)
          k hk ops ctrl φ
          (ws.xExt.grow 1)
          (ws.zExt.grow 1)
          hc : ℝ)
        ≤
      5 *
        (signedPhaseProductGateCount
          (Basis := Basis)
          k hk ops φ
          (ws.xExt.grow 1)
          (ws.zExt.grow 1)
          hs : ℝ) := by
    exact_mod_cast hdomNat
  have hsignedEq :
      signedPhaseProductGateCount
          (Basis := Basis)
          k hk ops φ
          (ws.xExt.grow 1)
          (ws.zExt.grow 1)
          hs
        =
      LowGate.gateCount shorGateCostModel
        (lowerGate
          (Basis := Basis)
          k hk ops
          (Gate.PhaseProdUsing φ x z ws)
          hunsignedWorkspace) := by
    symm
    exact
      lowerGate_PhaseProdUsing_gateCount_eq_signed
        (Basis := Basis)
        k hk ops φ x z ws hunsignedWorkspace
  rw [hsignedEq] at hdomReal
  have hb' :
      (LowGate.gateCount shorGateCostModel
          (lowerGate
            (Basis := Basis)
            k hk ops
            (Gate.PhaseProdUsing φ x z ws)
            hunsignedWorkspace) : ℝ)
        ≤
      C *
        Real.rpow
          (max (regSize x : ℝ) (regSize z : ℝ))
          (phaseProductExponent k) := by
    simpa only [Nat.cast_max] using hb
  have hn1 :
      1 ≤ max (regSize x) (regSize z) :=
    le_trans hn₀ hn
  have hsafe :
      phaseProductSafeRate
          k (max (regSize x) (regSize z))
        =
      Real.rpow
        (max (regSize x) (regSize z) : ℝ)
        (phaseProductExponent k) := by
    simp [phaseProductSafeRate, max_eq_right hn1]
  rw [hsafe]
  calc
  _ ≤
      5 *
        (LowGate.gateCount shorGateCostModel
          (lowerGate
            (Basis := Basis)
            k hk ops
            (Gate.PhaseProdUsing φ x z ws)
            hunsignedWorkspace) : ℝ) := by
    simpa only using hdomReal

  _ ≤
      5 *
        (C *
          Real.rpow
            (max (regSize x) (regSize z) : ℝ)
            (phaseProductExponent k)) := by
    exact
      mul_le_mul_of_nonneg_left
        hb'
        (by norm_num)

  _ =
      5 * C *
        Real.rpow
          (max (regSize x) (regSize z) : ℝ)
          (phaseProductExponent k) := by
    ring


end CPhaseProductReduction

end Shor
