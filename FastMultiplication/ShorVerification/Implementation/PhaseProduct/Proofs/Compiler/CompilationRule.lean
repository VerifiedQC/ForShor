import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.Compilation

/-!
# Compiled phase-product correctness under a width rule

The theorems of `Compilation.lean` for either width rule `R`
(`Framework/Policy.lean`, `WidthRule`): the same proofs, with the slots grown
to `neededWidthsBy R`. `Compilation.lean` keeps upstream's statements (the
scan); the policy lowering uses these.
-/

namespace Shor
open Gate
open Operations
open scoped BigOperators

/-- For either width rule `R`: Correctness of the signed compiled circuit on a basis ket, assuming an explicit block decomposition. -/
lemma eval_compileOpsToSignedGate_correct_ket_of_blocks_by
    (R : WidthRule)
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (k : ℕ) (hk : 1 < k)
    (phi : Angle)
    (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z k)
    (pts : List Point)
    (hpts : List.length pts = q k)
    (hInterp : GoodToomCookPoints k pts hpts)
    (b : qs.Basis)
    (ops : Prog k)
    (hB : BlockDecomposition (k := k) (by omega) State.start_state ops pts)
    (hworkspace : CompilerWorkspaceOK (initSignedLayoutState layout) (neededWidthsBy R x z ops) b)
    (run_ops_start_state : run? ops State.start_state = some State.start_state)
    (hSafeAdd :
      ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
        ops = pre ++ valid_ops.addScaled d s negSrc sh :: rest → d ≠ s) :
    let Wphase : ℕ := phaseLimbWidth x z k
    let coeff : Fin (q k) → ℚ := phaseCoeffFromPtsWidth k Wphase pts hpts
    qs.eval (compileOpsToSignedGateBy R k hk phi x z layout coeff ops) (qs.ket b)
      = qs.eval (Gate.SignedPhaseProd phi x z) (qs.ket b) := by
  dsimp
  set need : NeededWidths k := neededWidthsBy R x z ops
  set stInit : LayoutState k := initSignedLayoutState layout
  set stFinal : LayoutState k := targetSignedLayoutState stInit need
  set Wphase : ℕ := phaseLimbWidth x z k
  set coeff : Fin (q k) → ℚ := phaseCoeffFromPtsWidth k Wphase pts hpts
  rcases eval_compileSignedAllocations_ket_fits_by (R := R)
      (qs := qs) (layout := layout) (ops := ops) (b := b) hworkspace with
    ⟨bAlloc, hAllocEval, hEncAlloc⟩
  have hFitsFinal :
    ∀ {τ : State k},
      (∃ pre rest, ops = pre ++ rest ∧ run? pre State.start_state = some τ) →
        (∀ j : Fin k,
          FitsSignedWidth (ExtReg.width (stFinal.xslot j)) (evalRowX (qs := qs) stInit (τ j) b)) ∧
        (∀ j : Fin k,
          FitsSignedWidth (ExtReg.width (stFinal.zslot j)) (evalRowZ (qs := qs) stInit (τ j) b)) := by
    intro τ hτ
    simpa [stInit, stFinal, need] using
      allocated_widths_sound_by (R := R) (qs := qs) layout ops hworkspace.1 b (σ := τ) hτ
  have hLayoutDisjoint : LayoutSlotsDisjoint stFinal := by
    simpa [stFinal, stInit] using targetSignedLayoutState_owned_disjoint layout need
  have hBodyDealloc :
    qs.eval
        (compileAnnotatedOpsToSignedGateAux k hk phi coeff stFinal (annotatePhaseTermsAux k 0 ops) ;;
         compileSignedDeallocations k stInit stFinal)
        (qs.ket bAlloc)
      =
    phaseScalarFrom (qs := qs) k phi coeff stInit b pts 0 (by simpa using hpts) • qs.ket b := by
    exact eval_compileAnnotatedOpsToSignedGateAux_of_blocks_then_dealloc
      (qs := qs) (k := k) (hk := hk) (phi := phi) (pts := pts) (hpts := hpts)
      (coeff := coeff) (src := stInit) (dst := stFinal) (b0 := b) (bMid := bAlloc) (ops := ops)
      hLayoutDisjoint hFitsFinal hSafeAdd hEncAlloc hAllocEval hB run_ops_start_state
  have hScalar :
      phaseScalarFrom (qs := qs) k phi coeff stInit b pts 0 (by simpa using hpts)
        =
      Complex.exp
        (((Angle.toReal phi : ℝ) : ℂ) * Complex.I *
          (((extToInt x b : ℤ) : ℂ) * (((extToInt z b : ℤ) : ℂ)))) := by
    simpa [stInit, Wphase, coeff, phaseCoeffFromPtsForRegs] using
      toom_cook_interpolation
        (qs := qs) (hk := hk) (phi := phi) (x := x) (z := z) (layout := layout)
        (pts := pts) (hpts := hpts) (hInterp := hInterp) (b := b)
  calc
    qs.eval (compileOpsToSignedGateBy R k hk phi x z layout coeff ops) (qs.ket b)
        =
      qs.eval
        (compileAnnotatedOpsToSignedGateAux k hk phi coeff stFinal (annotatePhaseTermsAux k 0 ops) ;;
         compileSignedDeallocations k stInit stFinal)
        (qs.ket bAlloc) := by
          simp [compileOpsToSignedGateBy, stInit, stFinal, need, hAllocEval, qs.eval_seq]
    _ = phaseScalarFrom (qs := qs) k phi coeff stInit b pts 0 (by simpa using hpts) • qs.ket b :=
      hBodyDealloc
    _ =
      Complex.exp
        (((Angle.toReal phi : ℝ) : ℂ) * Complex.I *
          (((extToInt x b : ℤ) : ℂ) * (((extToInt z b : ℤ) : ℂ)))) • qs.ket b := by
          rw [hScalar]
    _ = qs.eval (SignedPhaseProd phi x z) (qs.ket b) := by
          symm
          simpa using
            (PhaseSemantics.eval_SignedPhaseProd_ket (qs := qs) (phi := phi) (x := x) (z := z) (b := b))

/-- For either width rule `R`: Basis-ket correctness of the signed compiled circuit from the public program-consumption hypothesis. -/
lemma eval_compileOpsToSignedGate_correct_ket_by
    (R : WidthRule)
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (k : ℕ) (hk : 1 < k)
    (phi : Angle)
    (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z k)
    (pts : List Point)
    (hpts : List.length pts = q k)
    (hInterp : GoodToomCookPoints k pts hpts)
    (b : qs.Basis)
    (ops : Prog k)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops pts)
    (hworkspace : CompilerWorkspaceOK (initSignedLayoutState layout) (neededWidthsBy R x z ops) b)
    (run_ops_start_state : run? ops State.start_state = some State.start_state) :
  let Wphase : ℕ := phaseLimbWidth x z k
  let coeff : Fin (q k) → ℚ := phaseCoeffFromPtsWidth k Wphase pts hpts
  qs.eval (compileOpsToSignedGateBy R k hk phi x z layout coeff ops) (qs.ket b)
    =
  qs.eval (Gate.SignedPhaseProd phi x z) (qs.ket b) := by
  have hB : BlockDecomposition (k := k) (by omega) State.start_state ops pts :=
    progConsumesPts_has_blockDecomposition (k := k) (by omega) ops State.start_state pts hC.1
  simpa using
    (eval_compileOpsToSignedGate_correct_ket_of_blocks_by (R := R)
      (qs := qs) (k := k) (hk := hk) (phi := phi) (x := x) (z := z) (layout := layout)
      (pts := pts) (hpts := hpts) (hInterp := hInterp) (b := b) (ops := ops)
      (hB := hB)
      (hworkspace := hworkspace)
      (run_ops_start_state := run_ops_start_state)
      (hSafeAdd := hC.2))

/-- For either width rule `R`: Basis-ket correctness of the controlled signed compiled circuit. -/
lemma eval_compileOpsToCSignedGate_correct_ket_by
    (R : WidthRule)
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (k : ℕ)
    (hk : 1 < k)
    (ctrl : ℕ)
    (phi : Angle)
    (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z k)
    (hctrl : layout.ControlDisjoint ctrl)
    (pts : List Point)
    (hpts : pts.length = q k)
    (hInterp : GoodToomCookPoints k pts hpts)
    (ops : Prog k)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops pts)
    (hRun : run? ops State.start_state = some State.start_state)
    (b : qs.Basis)
    (hworkspace : CompilerWorkspaceOK (initSignedLayoutState layout) (neededWidthsBy R x z ops) b) :
    qs.eval
      (compileOpsToCSignedGateBy R k hk ctrl phi x z layout
        (phaseCoeffFromPtsWidth k (phaseLimbWidth x z k) pts hpts) ops)
      (qs.ket b)
      = qs.eval (Gate.CSignedPhaseProd ctrl phi x z) (qs.ket b) := by
  set need : NeededWidths k := neededWidthsBy R x z ops
  set stInit : LayoutState k := initSignedLayoutState layout
  set stFinal : LayoutState k := targetSignedLayoutState stInit need
  set Wphase : ℕ := phaseLimbWidth x z k
  set coeff : Fin (q k) → ℚ := phaseCoeffFromPtsWidth k Wphase pts hpts
  rcases eval_compileSignedAllocations_ket_fits_by (R := R)
      (qs := qs) (layout := layout) (ops := ops) (b := b) hworkspace with
    ⟨bAlloc, hAllocEval, hEncAlloc⟩
  rcases eval_compileSignedAllocations_sameOutside_by (R := R)
      (qs := qs) (layout := layout) (ops := ops) (b := b) hworkspace with
    ⟨bAllocSO, hAllocSOEval, hAllocSO⟩
  have hbAllocSO : bAllocSO = bAlloc := by
    apply qs.ket_inj
    calc
      qs.ket bAllocSO = qs.eval (compileSignedAllocations k stInit stFinal) (qs.ket b) := by
            simpa [stInit, stFinal, need] using hAllocSOEval.symm
      _ = qs.ket bAlloc := by
            simpa [stInit, stFinal, need] using hAllocEval
  have hAllocSO' : SameOutsideLayout qs stFinal b bAlloc := by
    simpa [hbAllocSO, stInit, stFinal, need] using hAllocSO
  have hFitsFinal :
    ∀ {τ : State k},
      (∃ pre rest, ops = pre ++ rest ∧ run? pre State.start_state = some τ) →
        (∀ j : Fin k,
          FitsSignedWidth (ExtReg.width (stFinal.xslot j)) (evalRowX (qs := qs) stInit (τ j) b)) ∧
        (∀ j : Fin k,
          FitsSignedWidth (ExtReg.width (stFinal.zslot j)) (evalRowZ (qs := qs) stInit (τ j) b)) := by
    intro τ hτ
    simpa [stInit, stFinal, need] using
      allocated_widths_sound_by (R := R) (qs := qs) layout ops hworkspace.1 b (σ := τ) hτ
  have hLayoutDisjoint : LayoutSlotsDisjoint stFinal := by
    simpa [stFinal, stInit] using targetSignedLayoutState_owned_disjoint layout need
  have hCtrlOutside : OutsideLayout stFinal (ExtReg.ofReg (qubitReg ctrl)) := by
    have hCtrlOwned :
        (∀ i, ctrl ∉ (stFinal.xslot i).ownedQubits) ∧ (∀ i, ctrl ∉ (stFinal.zslot i).ownedQubits) := by
      simpa [stFinal, stInit] using controlDisjoint_target layout ctrl need hctrl
    constructor
    · intro i
      rw [ExtReg.ActiveDisjoint, Disjoint, List.disjoint_left]
      intro q hqCtrl hqSlot
      have hq : q = ctrl := by simpa [ExtReg.ofReg, qubitReg, Reg.singleton] using hqCtrl
      subst q
      exact hCtrlOwned.1 i (by
        simp only [ExtReg.ownedQubits, List.mem_append]
        exact Or.inl hqSlot)
    · intro i
      rw [ExtReg.ActiveDisjoint, Disjoint, List.disjoint_left]
      intro q hqCtrl hqSlot
      have hq : q = ctrl := by simpa [ExtReg.ofReg, qubitReg, Reg.singleton] using hqCtrl
      subst q
      exact hCtrlOwned.2 i (by
        simp only [ExtReg.ownedQubits, List.mem_append]
        exact Or.inl hqSlot)
  have hCtrlAlloc : RegEncoding.bit ctrl bAlloc = RegEncoding.bit ctrl b :=
    SameOutsideLayout.bit_eq_of_outside (qs := qs) hAllocSO' ctrl hCtrlOutside
  have hBodyDealloc :
    qs.eval
        (controlPhaseLeaves ctrl
          (compileAnnotatedOpsToSignedGateAux k hk phi coeff stFinal (annotatePhaseTermsAux k 0 ops)) ;;
         compileSignedDeallocations k stInit stFinal)
        (qs.ket bAlloc)
      =
    (if RegEncoding.bit ctrl b then
      phaseScalarFrom (qs := qs) k phi coeff stInit b pts 0 (by simpa using hpts)
    else
      1) • qs.ket b := by
    exact eval_controlPhaseLeaves_compileAnnotatedOpsToSignedGateAux_of_blocks_then_dealloc
      (qs := qs) (k := k) (hk := hk) (ctrl := ctrl) (phi := phi) (pts := pts) (hpts := hpts)
      (coeff := coeff) (src := stInit) (dst := stFinal) (b0 := b) (bMid := bAlloc) (ops := ops)
      hLayoutDisjoint hCtrlOutside hCtrlAlloc hFitsFinal hC.2 hEncAlloc hAllocEval
      (progConsumesPts_has_blockDecomposition (k := k) (by omega) ops State.start_state pts hC.1)
      hRun
  have hScalar :
      phaseScalarFrom (qs := qs) k phi coeff stInit b pts 0 (by simpa using hpts)
        =
      Complex.exp
        (((Angle.toReal phi : ℝ) : ℂ) * Complex.I *
          (((extToInt x b : ℤ) : ℂ) * (((extToInt z b : ℤ) : ℂ)))) := by
    simpa [stInit, Wphase, coeff, phaseCoeffFromPtsForRegs] using
      toom_cook_interpolation
        (qs := qs) (hk := hk) (phi := phi) (x := x) (z := z) (layout := layout)
        (pts := pts) (hpts := hpts) (hInterp := hInterp) (b := b)
  calc
    qs.eval (compileOpsToCSignedGateBy R k hk ctrl phi x z layout coeff ops) (qs.ket b)
        =
      qs.eval
        (controlPhaseLeaves ctrl
          (compileAnnotatedOpsToSignedGateAux k hk phi coeff stFinal (annotatePhaseTermsAux k 0 ops)) ;;
         compileSignedDeallocations k stInit stFinal)
        (qs.ket bAlloc) := by
          simp [
            compileOpsToCSignedGateBy,
            compileOpsToSignedGateBy,
            controlPhaseLeaves,
            controlPhaseLeaves_compileSignedAllocations,
            controlPhaseLeaves_compileSignedDeallocations,
            stInit,
            stFinal,
            need,
            hAllocEval,
            qs.eval_seq
          ]
    _ =
      (if RegEncoding.bit ctrl b then
        phaseScalarFrom (qs := qs) k phi coeff stInit b pts 0 (by simpa using hpts)
      else
        1) • qs.ket b := hBodyDealloc
    _ = qs.eval (Gate.CSignedPhaseProd ctrl phi x z) (qs.ket b) := by
          by_cases hc : RegEncoding.bit ctrl b
          · rw [PhaseSemantics.eval_CSignedPhaseProd_ket]; simp [hc, hScalar]
          · rw [PhaseSemantics.eval_CSignedPhaseProd_ket]; simp [hc]

end Shor
