import FastMultiplication.ShorVerification.AlgorithmCorrectness.PhaseProduct.BodyCorrectness
import FastMultiplication.ShorVerification.AlgorithmCorrectness.PhaseProduct.InterpolationCorrectness

namespace Shor
open Gate
open Operations
open scoped BigOperators

/-!
# Compiled Phase-Product Correctness

This file assembles allocation correctness, body/deallocation correctness, and
the Toom-Cook interpolation identity into the compiled phase-product circuit theorem for
`compileOpsToSignedGate`.
-/

/-! =========================================================
    Section 1: Main compiled-body correctness theorem
========================================================= -/

lemma eval_compileOpsToSignedGate_correct_ket_of_blocks
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [ExtRegEncoding qs.Basis]
  [ExtRegSplitSemantics qs.Basis]
  [GateSemanticsFacts qs]
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ)
  (x z : ExtReg)
  (hxz : Disjoint x.base z.base)
  (pts : List Point)
  (hpts : List.length pts = q k)
  (hInterp : GoodToomCookPoints k pts hpts)
  (b : qs.Basis)
  (ops : Prog k)
  (hB : BlockDecomposition (k := k) (by omega) State.start_state ops pts)
  (run_ops_start_state : run? ops State.start_state = some State.start_state)
  (hSafeAdd :
    ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
      ops = pre ++ valid_ops.addScaled d s negSrc sh :: rest → d ≠ s) :
  let Wphase : ℕ := phaseLimbWidth x z k
  let coeff : Fin (q k) → ℚ := phaseCoeffFromPtsWidth k Wphase pts hpts
  qs.eval
      (compileOpsToSignedGate
        (Basis := qs.Basis) k hk phi x z coeff ops)
      (qs.ket b)
    =
  qs.eval
      (Gate.SignedPhaseProd phi x z)
      (qs.ket b) := by
  dsimp

  set need : NeededWidths k := scanNeededWidths x z ops
  set stInit : LayoutState k :=
    initSignedLayoutState (Basis := qs.Basis) x z k
  set stFinal : LayoutState k :=
    targetSignedLayoutState (Basis := qs.Basis) x z k need

  set Wphase : ℕ := phaseLimbWidth x z k
  set coeff : Fin (q k) → ℚ := phaseCoeffFromPtsWidth k Wphase pts hpts

  rcases eval_compileSignedAllocations_ket_fits
      (qs := qs)
      (x := x) (z := z)
      (hxz := hxz)
      (ops := ops) (b := b) with
    ⟨bAlloc, hAllocEval, hEncAlloc⟩

  have hFitsFinal :
    ∀ {τ : State k},
      (∃ pre rest, ops = pre ++ rest ∧ run? pre State.start_state = some τ) →
        (∀ j : Fin k,
          FitsSignedWidth (ExtReg.width (stFinal.xslot j))
            (evalRowX (qs := qs) stInit (τ j) b)) ∧
        (∀ j : Fin k,
          FitsSignedWidth (ExtReg.width (stFinal.zslot j))
            (evalRowZ (qs := qs) stInit (τ j) b)) := by
    intro τ hτ
    simpa [stInit, stFinal, need] using
      (allocated_widths_sound
        (qs := qs) (x := x) (z := z) (ops := ops) (b := b)
        (σ := τ) hτ)

  have hLayoutDisjoint : LayoutSlotsDisjoint stFinal := by
    subst stFinal
    unfold LayoutSlotsDisjoint
    constructor
    · intro i j hij
      have hsrc :
          Disjoint
            ((initSignedLayoutState (Basis := qs.Basis) x z k).xslot i).base
            ((initSignedLayoutState (Basis := qs.Basis) x z k).xslot j).base := by
        simpa [initSignedLayoutState] using
          splitExtReg_disjoint
            (Basis := qs.Basis)
            x k (phaseLimbWidth x z k)
            i j hij
      simpa [targetSignedLayoutState, widenExtRegTo] using hsrc
    · constructor
      · intro i j hij
        have hsrc :
            Disjoint
              ((initSignedLayoutState (Basis := qs.Basis) x z k).zslot i).base
              ((initSignedLayoutState (Basis := qs.Basis) x z k).zslot j).base := by
          simpa [initSignedLayoutState] using
            splitExtReg_disjoint
              (Basis := qs.Basis)
              z k (phaseLimbWidth x z k)
              i j hij
        simpa [targetSignedLayoutState, widenExtRegTo] using hsrc
      · intro i j
        have hsrc :
            Disjoint
              ((initSignedLayoutState (Basis := qs.Basis) x z k).xslot i).base
              ((initSignedLayoutState (Basis := qs.Basis) x z k).zslot j).base := by
          simpa [initSignedLayoutState] using
            splitExtReg_disjoint_of_disjoint
              (Basis := qs.Basis)
              x z k (phaseLimbWidth x z k)
              i j hxz
        simpa [targetSignedLayoutState, widenExtRegTo] using hsrc

  have hBodyDealloc :
    qs.eval
        (compileAnnotatedOpsToSignedGateAux k hk phi coeff stFinal
          (annotatePhaseTermsAux k 0 ops) ;;
         compileSignedDeallocations k stInit stFinal)
        (qs.ket bAlloc)
      =
    phaseScalarFrom (qs := qs) k phi coeff stInit b pts 0 (by simpa using hpts) •
      qs.ket b := by
    exact eval_compileAnnotatedOpsToSignedGateAux_of_blocks_then_dealloc
      (qs := qs)
      (k := k) (hk := hk)
      (phi := phi)
      (pts := pts)
      (hpts := hpts)
      (coeff := coeff)
      (src := stInit)
      (dst := stFinal)
      (b0 := b)
      (bMid := bAlloc)
      (ops := ops)
      hLayoutDisjoint
      hFitsFinal
      hSafeAdd
      hEncAlloc
      hAllocEval
      hB
      run_ops_start_state

  have hScalar :
      phaseScalarFrom (qs := qs) k phi coeff stInit b pts 0 (by simpa using hpts)
        =
      Complex.exp
        (phi * Complex.I *
          (((ExtRegEncoding.extToInt x b : ℤ) : ℂ) *
          (((ExtRegEncoding.extToInt z b : ℤ) : ℂ)))) := by
    simpa [stInit, Wphase, coeff] using
      toom_cook_interpolation
        (qs := qs)
        (hk := hk)
        (phi := phi)
        (x := x)
        (z := z)
        (pts := pts)
        (hpts := hpts)
        (hInterp := hInterp)
        (b := b)

  calc
    qs.eval
        (compileOpsToSignedGate
          (Basis := qs.Basis) k hk phi x z coeff ops)
        (qs.ket b)
        =
      qs.eval
        (compileAnnotatedOpsToSignedGateAux k hk phi coeff stFinal
          (annotatePhaseTermsAux k 0 ops) ;;
         compileSignedDeallocations k stInit stFinal)
        (qs.ket bAlloc) := by
          simp [
            compileOpsToSignedGate,
            stInit,
            stFinal,
            need,
            hAllocEval,
            qs.eval_seq
          ]
    _ =
      phaseScalarFrom (qs := qs) k phi coeff stInit b pts 0 (by simpa using hpts) •
        qs.ket b := hBodyDealloc
    _ =
      Complex.exp
        (phi * Complex.I *
          (((ExtRegEncoding.extToInt x b : ℤ) : ℂ) *
          (((ExtRegEncoding.extToInt z b : ℤ) : ℂ)))) •
        qs.ket b := by
          rw [hScalar]
    _ =
      qs.eval (SignedPhaseProd phi x z) (qs.ket b) := by
        symm
        simpa using
          (PhaseSemantics.eval_SignedPhaseProd_ket
            (qs := qs) (phi := phi) (x := x) (z := z) (b := b))

/-! =========================================================
    Section 2: Public correctness wrappers
========================================================= -/

lemma eval_compileOpsToSignedGate_correct_ket
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [ExtRegEncoding qs.Basis]
  [ExtRegSplitSemantics qs.Basis]
  [GateSemanticsFacts qs]
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ)
  (x z : ExtReg)
  (hxz : Disjoint x.base z.base)
  (pts : List Point)
  (hpts : List.length pts = q k)
  (hInterp : GoodToomCookPoints k pts hpts)
  (b : qs.Basis)
  (ops : Prog k)
  (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops pts)
  (run_ops_start_state : run? ops State.start_state = some State.start_state) :
  let Wphase : ℕ := phaseLimbWidth x z k
  let coeff : Fin (q k) → ℚ := phaseCoeffFromPtsWidth k Wphase pts hpts
  qs.eval
      (compileOpsToSignedGate
        (Basis := qs.Basis) k hk phi x z coeff ops)
      (qs.ket b)
    =
  qs.eval
      (Gate.SignedPhaseProd phi x z)
      (qs.ket b) := by
  have hB :
      BlockDecomposition (k := k) (by omega) State.start_state ops pts :=
    progConsumesPts_has_blockDecomposition
      (k := k) (by omega) ops State.start_state pts hC.1
  simpa using
    (eval_compileOpsToSignedGate_correct_ket_of_blocks
      (qs := qs)
      (k := k) (hk := hk)
      (phi := phi)
      (x := x) (z := z)
      (hxz := hxz)
      (pts := pts) (hpts := hpts)
      (hInterp := hInterp)
      (b := b)
      (ops := ops)
      (hB := hB)
      (run_ops_start_state := run_ops_start_state)
      (hSafeAdd := hC.2))

lemma eval_compileOpsToSignedGate_correct
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [ExtRegEncoding qs.Basis]
  [ExtRegSplitSemantics qs.Basis]
  [GateSemanticsFacts qs]
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ)
  (x z : ExtReg)
  (hxz : Disjoint x.base z.base)
  (pts : List Point)
  (hpts : List.length pts = q k)
  (hInterp : GoodToomCookPoints k pts hpts)
  (ψ : qs.State)
  (ops : Prog k)
  (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops pts)
  (run_ops_start_state : run? ops State.start_state = some State.start_state) :
  let Wphase : ℕ := phaseLimbWidth x z k
  let coeff : Fin (q k) → ℚ := phaseCoeffFromPtsWidth k Wphase pts hpts
  qs.eval
      (compileOpsToSignedGate
        (Basis := qs.Basis) k hk phi x z coeff ops)
      ψ
    =
  qs.eval
      (Gate.SignedPhaseProd phi x z)
      ψ := by
  have hket :
      ∀ b : qs.Basis,
        let Wphase : ℕ := phaseLimbWidth x z k
        let coeff : Fin (q k) → ℚ := phaseCoeffFromPtsWidth k Wphase pts hpts
        qs.eval
            (compileOpsToSignedGate
              (Basis := qs.Basis) k hk phi x z coeff ops)
            (qs.ket b)
          =
        qs.eval
            (Gate.SignedPhaseProd phi x z)
            (qs.ket b) := by
    intro b
    exact
      eval_compileOpsToSignedGate_correct_ket
        (qs := qs)
        (k := k) (hk := hk)
        (phi := phi)
        (x := x) (z := z)
        (hxz := hxz)
        (pts := pts)
        (hpts := hpts)
        (hInterp := hInterp)
        (b := b)
        (ops := ops)
        (hC := hC)
        (run_ops_start_state := run_ops_start_state)

  exact gate_eq_of_ket_eq qs (by intro b; simpa using hket b) ψ

lemma eval_compileOpsToCSignedGate_correct_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [ExtRegSplitSemantics qs.Basis]
    [GateSemanticsFacts qs]
    (k : ℕ) (hk : 1 < k)
    (ctrl : ℕ) (phi : ℝ) (x z : ExtReg)
    (hxz : Disjoint x.base z.base)
    (hctrl : ExtReg.CtrlDisjoint ctrl x z)
    (pts : List Point)
    (hpts : pts.length = q k)
    (hInterp : GoodToomCookPoints k pts hpts)
    (ops : Prog k)
    (hC : ProgConsumesPtsSafe (k := k) (by omega)
      State.start_state ops pts)
    (hRun : run? ops State.start_state = some State.start_state)
    (b : qs.Basis) :
    qs.eval
      (compileOpsToCSignedGate
        (Basis := qs.Basis) k hk ctrl phi x z
        (phaseCoeffFromPtsWidth k (phaseLimbWidth x z k) pts hpts) ops)
      (qs.ket b)
    =
    qs.eval (Gate.CSignedPhaseProd ctrl phi x z) (qs.ket b) := by
  set need : NeededWidths k := scanNeededWidths x z ops
  set stInit : LayoutState k :=
    initSignedLayoutState (Basis := qs.Basis) x z k
  set stFinal : LayoutState k :=
    targetSignedLayoutState (Basis := qs.Basis) x z k need

  set Wphase : ℕ := phaseLimbWidth x z k
  set coeff : Fin (q k) → ℚ := phaseCoeffFromPtsWidth k Wphase pts hpts

  rcases eval_compileSignedAllocations_ket_fits
      (qs := qs)
      (x := x) (z := z)
      (hxz := hxz)
      (ops := ops) (b := b) with
    ⟨bAlloc, hAllocEval, hEncAlloc⟩

  rcases eval_compileSignedAllocations_sameOutside
      (qs := qs)
      (x := x) (z := z)
      (hxz := hxz)
      (ops := ops) (b := b) with
    ⟨bAllocSO, hAllocSOEval, hAllocSO⟩

  have hbAllocSO : bAllocSO = bAlloc := by
    apply qs.ket_inj
    calc
      qs.ket bAllocSO
          = qs.eval (compileSignedAllocations k stInit stFinal) (qs.ket b) := by
              simpa [stInit, stFinal, need] using hAllocSOEval.symm
      _ = qs.ket bAlloc := by
              simpa [stInit, stFinal, need] using hAllocEval

  have hAllocSO' : SameOutsideLayout qs stFinal b bAlloc := by
    simpa [hbAllocSO, stInit, stFinal, need] using hAllocSO

  have hFitsFinal :
    ∀ {τ : State k},
      (∃ pre rest, ops = pre ++ rest ∧ run? pre State.start_state = some τ) →
        (∀ j : Fin k,
          FitsSignedWidth (ExtReg.width (stFinal.xslot j))
            (evalRowX (qs := qs) stInit (τ j) b)) ∧
        (∀ j : Fin k,
          FitsSignedWidth (ExtReg.width (stFinal.zslot j))
            (evalRowZ (qs := qs) stInit (τ j) b)) := by
    intro τ hτ
    simpa [stInit, stFinal, need] using
      (allocated_widths_sound
        (qs := qs) (x := x) (z := z) (ops := ops) (b := b)
        (σ := τ) hτ)

  have hLayoutDisjoint : LayoutSlotsDisjoint stFinal := by
    subst stFinal
    unfold LayoutSlotsDisjoint
    constructor
    · intro i j hij
      have hsrc :
          Disjoint
            ((initSignedLayoutState (Basis := qs.Basis) x z k).xslot i).base
            ((initSignedLayoutState (Basis := qs.Basis) x z k).xslot j).base := by
        simpa [initSignedLayoutState] using
          splitExtReg_disjoint
            (Basis := qs.Basis)
            x k (phaseLimbWidth x z k)
            i j hij
      simpa [targetSignedLayoutState, widenExtRegTo] using hsrc
    · constructor
      · intro i j hij
        have hsrc :
            Disjoint
              ((initSignedLayoutState (Basis := qs.Basis) x z k).zslot i).base
              ((initSignedLayoutState (Basis := qs.Basis) x z k).zslot j).base := by
          simpa [initSignedLayoutState] using
            splitExtReg_disjoint
              (Basis := qs.Basis)
              z k (phaseLimbWidth x z k)
              i j hij
        simpa [targetSignedLayoutState, widenExtRegTo] using hsrc
      · intro i j
        have hsrc :
            Disjoint
              ((initSignedLayoutState (Basis := qs.Basis) x z k).xslot i).base
              ((initSignedLayoutState (Basis := qs.Basis) x z k).zslot j).base := by
          simpa [initSignedLayoutState] using
            splitExtReg_disjoint_of_disjoint
              (Basis := qs.Basis)
              x z k (phaseLimbWidth x z k)
              i j hxz
        simpa [targetSignedLayoutState, widenExtRegTo] using hsrc

  have hCtrlOutside : OutsideLayout stFinal (ExtReg.ofReg (qubitReg ctrl)) := by
    subst stFinal
    constructor
    · intro i
      have hqx : Disjoint x.base (qubitReg ctrl) := by
        cases hctrl.1 with
        | inl h => exact Or.inr h
        | inr h => exact Or.inl h
      have hsplit :
          Disjoint
            ((initSignedLayoutState (Basis := qs.Basis) x z k).xslot i).base
            (qubitReg ctrl) := by
        simpa [initSignedLayoutState] using
          splitExtReg_disjoint_reg_of_disjoint
            (Basis := qs.Basis)
            x (qubitReg ctrl) k (phaseLimbWidth x z k) i hqx
      have hsplit' : Disjoint
          (qubitReg ctrl)
          ((initSignedLayoutState (Basis := qs.Basis) x z k).xslot i).base := by
        cases hsplit with
        | inl h => exact Or.inr h
        | inr h => exact Or.inl h
      simpa [targetSignedLayoutState, widenExtRegTo, ExtReg.ofReg] using hsplit'
    · intro i
      have hqz : Disjoint z.base (qubitReg ctrl) := by
        cases hctrl.2 with
        | inl h => exact Or.inr h
        | inr h => exact Or.inl h
      have hsplit :
          Disjoint
            ((initSignedLayoutState (Basis := qs.Basis) x z k).zslot i).base
            (qubitReg ctrl) := by
        simpa [initSignedLayoutState] using
          splitExtReg_disjoint_reg_of_disjoint
            (Basis := qs.Basis)
            z (qubitReg ctrl) k (phaseLimbWidth x z k) i hqz
      have hsplit' : Disjoint
          (qubitReg ctrl)
          ((initSignedLayoutState (Basis := qs.Basis) x z k).zslot i).base := by
        cases hsplit with
        | inl h => exact Or.inr h
        | inr h => exact Or.inl h
      simpa [targetSignedLayoutState, widenExtRegTo, ExtReg.ofReg] using hsplit'

  have hCtrlAlloc : RegEncoding.bit ctrl bAlloc = RegEncoding.bit ctrl b :=
    SameOutsideLayout.bit_eq_of_outside
      (qs := qs) hAllocSO' ctrl hCtrlOutside

  have hBodyDealloc :
    qs.eval
        (controlPhaseLeaves ctrl
          (compileAnnotatedOpsToSignedGateAux k hk phi coeff stFinal
            (annotatePhaseTermsAux k 0 ops)) ;;
         compileSignedDeallocations k stInit stFinal)
        (qs.ket bAlloc)
      =
    (if RegEncoding.bit ctrl b then
      phaseScalarFrom (qs := qs) k phi coeff stInit b pts 0 (by simpa using hpts)
    else
      1) •
      qs.ket b := by
    exact eval_controlPhaseLeaves_compileAnnotatedOpsToSignedGateAux_of_blocks_then_dealloc
      (qs := qs)
      (k := k) (hk := hk)
      (ctrl := ctrl)
      (phi := phi)
      (pts := pts)
      (hpts := hpts)
      (coeff := coeff)
      (src := stInit)
      (dst := stFinal)
      (b0 := b)
      (bMid := bAlloc)
      (ops := ops)
      hLayoutDisjoint
      hCtrlOutside
      hCtrlAlloc
      hFitsFinal
      hC.2
      hEncAlloc
      hAllocEval
      (progConsumesPts_has_blockDecomposition
        (k := k) (by omega) ops State.start_state pts hC.1)
      hRun

  have hScalar :
      phaseScalarFrom (qs := qs) k phi coeff stInit b pts 0 (by simpa using hpts)
        =
      Complex.exp
        (phi * Complex.I *
          (((ExtRegEncoding.extToInt x b : ℤ) : ℂ) *
          (((ExtRegEncoding.extToInt z b : ℤ) : ℂ)))) := by
    simpa [stInit, Wphase, coeff] using
      toom_cook_interpolation
        (qs := qs)
        (hk := hk)
        (phi := phi)
        (x := x)
        (z := z)
        (pts := pts)
        (hpts := hpts)
        (hInterp := hInterp)
        (b := b)

  calc
    qs.eval
        (compileOpsToCSignedGate
          (Basis := qs.Basis) k hk ctrl phi x z coeff ops)
        (qs.ket b)
        =
      qs.eval
        (controlPhaseLeaves ctrl
          (compileAnnotatedOpsToSignedGateAux k hk phi coeff stFinal
            (annotatePhaseTermsAux k 0 ops)) ;;
         compileSignedDeallocations k stInit stFinal)
        (qs.ket bAlloc) := by
          simp [
            compileOpsToCSignedGate,
            compileOpsToSignedGate,
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
        1) •
        qs.ket b := hBodyDealloc
    _ =
      qs.eval (Gate.CSignedPhaseProd ctrl phi x z) (qs.ket b) := by
        by_cases hc : RegEncoding.bit ctrl b
        · rw [PhaseSemantics.eval_CSignedPhaseProd_ket]
          simp [hc, hScalar]
        · rw [PhaseSemantics.eval_CSignedPhaseProd_ket]
          simp [hc]

lemma eval_compileOpsToCSignedGate_correct
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [ExtRegSplitSemantics qs.Basis]
    [GateSemanticsFacts qs]
    (k : ℕ) (hk : 1 < k)
    (ctrl : ℕ) (phi : ℝ) (x z : ExtReg)
    (hxz : Disjoint x.base z.base)
    (hctrl : ExtReg.CtrlDisjoint ctrl x z)
    (pts : List Point)
    (hpts : pts.length = q k)
    (hInterp : GoodToomCookPoints k pts hpts)
    (ops : Prog k)
    (hC : ProgConsumesPtsSafe (k := k) (by omega)
      State.start_state ops pts)
    (hRun : run? ops State.start_state = some State.start_state)
    (ψ : qs.State) :
    qs.eval
      (compileOpsToCSignedGate
        (Basis := qs.Basis) k hk ctrl phi x z
        (phaseCoeffFromPtsWidth k (phaseLimbWidth x z k) pts hpts) ops)
      ψ
    =
    qs.eval (Gate.CSignedPhaseProd ctrl phi x z) ψ := by
  apply gate_eq_of_ket_eq qs
  intro b
  exact
    eval_compileOpsToCSignedGate_correct_ket
      (qs := qs)
      (k := k) (hk := hk)
      (ctrl := ctrl) (phi := phi)
      (x := x) (z := z)
      (hxz := hxz)
      (hctrl := hctrl)
      (pts := pts)
      (hpts := hpts)
      (hInterp := hInterp)
      (ops := ops)
      (hC := hC)
      (hRun := hRun)
      (b := b)

lemma eval_SignedPhaseProd_zero_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [PhaseSemantics qs]
    (x z : ExtReg)
    (b : qs.Basis) :
    qs.eval (Gate.SignedPhaseProd 0 x z) (qs.ket b) = qs.ket b := by
  rw [PhaseSemantics.eval_SignedPhaseProd_ket]
  simp

lemma eval_controlled_compileOpsToSignedGate_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [ExtRegEncoding qs.Basis]
    [ExtRegSplitSemantics qs.Basis]
    [GateSemanticsFacts qs]
    (k : ℕ) (hk : 1 < k)
    (ctrl : ℕ) (phi : ℝ) (x z : ExtReg)
    (hxz : Disjoint x.base z.base)
    (hctrl : ExtReg.CtrlDisjoint ctrl x z)
    (pts : List Point)
    (hpts : pts.length = q k)
    (hInterp : GoodToomCookPoints k pts hpts)
    (ops : Prog k)
    (hC : ProgConsumesPtsSafe (k := k) (by omega)
      State.start_state ops pts)
    (hRun : run? ops State.start_state = some State.start_state)
    (b : qs.Basis) :
    qs.eval
      (compileOpsToCSignedGate
        (Basis := qs.Basis) k hk ctrl phi x z
        (phaseCoeffFromPtsWidth k (phaseLimbWidth x z k) pts hpts) ops)
      (qs.ket b)
    =
    if RegEncoding.bit ctrl b then
      qs.eval
        (compileOpsToSignedGate
          (Basis := qs.Basis) k hk phi x z
          (phaseCoeffFromPtsWidth k (phaseLimbWidth x z k) pts hpts) ops)
        (qs.ket b)
    else
      qs.eval
        (compileOpsToSignedGate
          (Basis := qs.Basis) k hk 0 x z
          (phaseCoeffFromPtsWidth k (phaseLimbWidth x z k) pts hpts) ops)
        (qs.ket b) := by
  classical
  have hCS :=
    eval_compileOpsToCSignedGate_correct_ket
      (qs := qs)
      (k := k) (hk := hk)
      (ctrl := ctrl) (phi := phi)
      (x := x) (z := z)
      (hxz := hxz)
      (hctrl := hctrl)
      (pts := pts)
      (hpts := hpts)
      (hInterp := hInterp)
      (ops := ops)
      (hC := hC)
      (hRun := hRun)
      (b := b)
  have hSigned_phi :=
    eval_compileOpsToSignedGate_correct_ket
      (qs := qs)
      (k := k) (hk := hk)
      (phi := phi)
      (x := x) (z := z)
      (hxz := hxz)
      (pts := pts)
      (hpts := hpts)
      (hInterp := hInterp)
      (b := b)
      (ops := ops)
      (hC := hC)
      (run_ops_start_state := hRun)
  have hSigned_zero :=
    eval_compileOpsToSignedGate_correct_ket
      (qs := qs)
      (k := k) (hk := hk)
      (phi := 0)
      (x := x) (z := z)
      (hxz := hxz)
      (pts := pts)
      (hpts := hpts)
      (hInterp := hInterp)
      (b := b)
      (ops := ops)
      (hC := hC)
      (run_ops_start_state := hRun)
  by_cases hc : RegEncoding.bit ctrl b
  · simp [hc]
    calc
      qs.eval
          (compileOpsToCSignedGate
            (Basis := qs.Basis) k hk ctrl phi x z
            (phaseCoeffFromPtsWidth k (phaseLimbWidth x z k) pts hpts) ops)
          (qs.ket b)
          =
        qs.eval (Gate.CSignedPhaseProd ctrl phi x z) (qs.ket b) := hCS
      _ =
        qs.eval (Gate.SignedPhaseProd phi x z) (qs.ket b) := by
          rw [PhaseSemantics.eval_CSignedPhaseProd_ket]
          rw [PhaseSemantics.eval_SignedPhaseProd_ket]
          simp [hc]
      _ =
        qs.eval
          (compileOpsToSignedGate
            (Basis := qs.Basis) k hk phi x z
            (phaseCoeffFromPtsWidth k (phaseLimbWidth x z k) pts hpts) ops)
          (qs.ket b) := hSigned_phi.symm
  · simp [hc]
    calc
      qs.eval
          (compileOpsToCSignedGate
            (Basis := qs.Basis) k hk ctrl phi x z
            (phaseCoeffFromPtsWidth k (phaseLimbWidth x z k) pts hpts) ops)
          (qs.ket b)
          =
        qs.eval (Gate.CSignedPhaseProd ctrl phi x z) (qs.ket b) := hCS
      _ =
        qs.eval (Gate.SignedPhaseProd 0 x z) (qs.ket b) := by
          calc
            qs.eval (Gate.CSignedPhaseProd ctrl phi x z) (qs.ket b)
                = qs.ket b := by
                  rw [PhaseSemantics.eval_CSignedPhaseProd_ket]
                  simp [hc]
            _ = qs.eval (Gate.SignedPhaseProd 0 x z) (qs.ket b) :=
                  (eval_SignedPhaseProd_zero_ket (qs := qs) x z b).symm
      _ =
        qs.eval
          (compileOpsToSignedGate
            (Basis := qs.Basis) k hk 0 x z
            (phaseCoeffFromPtsWidth k (phaseLimbWidth x z k) pts hpts) ops)
          (qs.ket b) := hSigned_zero.symm

end Shor
