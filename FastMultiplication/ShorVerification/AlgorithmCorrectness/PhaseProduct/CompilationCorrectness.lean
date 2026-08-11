import FastMultiplication.ShorVerification.AlgorithmCorrectness.PhaseProduct.BodyCorrectness
import FastMultiplication.ShorVerification.AlgorithmCorrectness.PhaseProduct.InterpolationCorrectness

namespace Shor
open Gate
open Operations
open scoped BigOperators

/-!
# Compiled Phase-Product Correctness
This file assembles allocation correctness, body/deallocation correctness, and
the Toom-Cook interpolation identity into the public correctness theorems for
compiled signed and controlled phase-product circuits.
-/

/-! =========================================================
    Section 1: Block-based signed compilation theorem
    The core theorem starts from an explicit block decomposition. It allocates
    widened chunks, runs the compiled body plus deallocation, then uses the
    interpolation theorem to identify the resulting scalar with `SignedPhaseProd`.
========================================================= -/

/-- Correctness of the signed compiled circuit on a basis ket, assuming an explicit block decomposition. -/
lemma eval_compileOpsToSignedGate_correct_ket_of_blocks
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [GateSemanticsFacts qs]
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ)
  (x z : ExtReg)
  (layout : Gate.PhaseProductLayout x z k)
  (pts : List Point)
  (hpts : List.length pts = q k)
  (hInterp : GoodToomCookPoints k pts hpts)
  (b : qs.Basis)
  (ops : Prog k)
  (hB : BlockDecomposition (k := k) (by omega) State.start_state ops pts)
  (hworkspace :
    CompilerWorkspaceOK
      (initSignedLayoutState layout)
      (scanNeededWidths x z ops)
      b)
  (run_ops_start_state :
    run? ops State.start_state = some State.start_state)
  (hSafeAdd :
    ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
      ops = pre ++ valid_ops.addScaled d s negSrc sh :: rest →
      d ≠ s) :
  let Wphase : ℕ := phaseLimbWidth x z k
  let coeff : Fin (q k) → ℚ :=
    phaseCoeffFromPtsWidth k Wphase pts hpts
  qs.eval
      (compileOpsToSignedGate
        k hk phi x z layout coeff ops)
      (qs.ket b)
    =
  qs.eval
      (Gate.SignedPhaseProd phi x z)
      (qs.ket b) := by
  dsimp
  set need : NeededWidths k := scanNeededWidths x z ops
  set stInit : LayoutState k := initSignedLayoutState layout
  set stFinal : LayoutState k := targetSignedLayoutState stInit need
  set Wphase : ℕ := phaseLimbWidth x z k
  set coeff : Fin (q k) → ℚ := phaseCoeffFromPtsWidth k Wphase pts hpts
  rcases eval_compileSignedAllocations_ket_fits
      (qs := qs)
      (layout := layout)
      (ops := ops)
      (b := b)
      hworkspace with
    ⟨bAlloc, hAllocEval, hEncAlloc⟩
  have hFitsFinal :
    ∀ {τ : State k},
      (∃ pre rest,
        ops = pre ++ rest ∧
        run? pre State.start_state = some τ) →
        (∀ j : Fin k,
          FitsSignedWidth
            (ExtReg.width (stFinal.xslot j))
            (evalRowX (qs := qs) stInit (τ j) b)) ∧
        (∀ j : Fin k,
          FitsSignedWidth
            (ExtReg.width (stFinal.zslot j))
            (evalRowZ (qs := qs) stInit (τ j) b)) := by
    intro τ hτ
    simpa [stInit, stFinal, need] using
      allocated_widths_sound
        (qs := qs)
        layout
        ops
        hworkspace.1
        b
        (σ := τ)
        hτ
  have hLayoutDisjoint : LayoutSlotsDisjoint stFinal := by
    simpa [stFinal, stInit] using targetSignedLayoutState_owned_disjoint layout need
  have hBodyDealloc :
    qs.eval
        (compileAnnotatedOpsToSignedGateAux
            k hk phi coeff stFinal
            (annotatePhaseTermsAux k 0 ops) ;;
         compileSignedDeallocations k stInit stFinal)
        (qs.ket bAlloc)
      =
    phaseScalarFrom
        (qs := qs)
        k phi coeff stInit b pts 0
        (by simpa using hpts) •
      qs.ket b := by
    exact
      eval_compileAnnotatedOpsToSignedGateAux_of_blocks_then_dealloc
        (qs := qs) (k := k) (hk := hk) (phi := phi) (pts := pts) (hpts := hpts)
        (coeff := coeff) (src := stInit) (dst := stFinal) (b0 := b) (bMid := bAlloc) (ops := ops)
        hLayoutDisjoint
        hFitsFinal
        hSafeAdd
        hEncAlloc
        hAllocEval
        hB
        run_ops_start_state
  have hScalar :
      phaseScalarFrom
          (qs := qs)
          k phi coeff stInit b pts 0
          (by simpa using hpts)
        =
      Complex.exp
        (phi * Complex.I *
          (((extToInt x b : ℤ) : ℂ) *
           (((extToInt z b : ℤ) : ℂ)))) := by
    simpa [
      stInit,
      Wphase,
      coeff,
      phaseCoeffFromPtsForRegs
    ] using
      toom_cook_interpolation
        (qs := qs) (hk := hk) (phi := phi) (x := x) (z := z) (layout := layout)
        (pts := pts) (hpts := hpts) (hInterp := hInterp) (b := b)
  calc
    qs.eval
        (compileOpsToSignedGate
          k hk phi x z layout coeff ops)
        (qs.ket b)
        =
      qs.eval
        (compileAnnotatedOpsToSignedGateAux
            k hk phi coeff stFinal
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
      phaseScalarFrom
          (qs := qs)
          k phi coeff stInit b pts 0
          (by simpa using hpts) •
        qs.ket b := hBodyDealloc
    _ =
      Complex.exp
        (phi * Complex.I *
          (((extToInt x b : ℤ) : ℂ) *
           (((extToInt z b : ℤ) : ℂ)))) •
        qs.ket b := by
          rw [hScalar]
    _ =
      qs.eval
        (SignedPhaseProd phi x z)
        (qs.ket b) := by
          symm
          simpa using
            (PhaseSemantics.eval_SignedPhaseProd_ket
              (qs := qs)
              (phi := phi)
              (x := x)
              (z := z)
              (b := b))

/-! =========================================================
    Section 2: Public signed correctness wrappers
    These wrappers recover the block decomposition from `ProgConsumesPtsSafe` and
    lift the basis-ket theorem to arbitrary clean workspace states by linearity.
========================================================= -/

/-- Basis-ket correctness of the signed compiled circuit from the public program-consumption hypothesis. -/
lemma eval_compileOpsToSignedGate_correct_ket
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [GateSemanticsFacts qs]
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ)
  (x z : ExtReg)
  (layout : Gate.PhaseProductLayout x z k)
  (pts : List Point)
  (hpts : List.length pts = q k)
  (hInterp : GoodToomCookPoints k pts hpts)
  (b : qs.Basis)
  (ops : Prog k)
  (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops pts)
  (hworkspace : CompilerWorkspaceOK (initSignedLayoutState layout) (scanNeededWidths x z ops) b)
  (run_ops_start_state : run? ops State.start_state = some State.start_state) :
  let Wphase : ℕ := phaseLimbWidth x z k
  let coeff : Fin (q k) → ℚ := phaseCoeffFromPtsWidth k Wphase pts hpts
  qs.eval (compileOpsToSignedGate k hk phi x z layout coeff ops) (qs.ket b)
    =
  qs.eval (Gate.SignedPhaseProd phi x z) (qs.ket b) := by
  have hB : BlockDecomposition (k := k) (by omega) State.start_state ops pts :=
    progConsumesPts_has_blockDecomposition (k := k) (by omega) ops State.start_state pts hC.1
  simpa using
    (eval_compileOpsToSignedGate_correct_ket_of_blocks
      (qs := qs) (k := k) (hk := hk) (phi := phi) (x := x) (z := z) (layout := layout)
      (pts := pts) (hpts := hpts) (hInterp := hInterp) (b := b) (ops := ops)
      (hB := hB)
      (hworkspace := hworkspace)
      (run_ops_start_state := run_ops_start_state)
      (hSafeAdd := hC.2))

/-- State-level correctness of the signed compiled circuit on clean workspace states. -/
lemma eval_compileOpsToSignedGate_correct
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [GateSemanticsFacts qs]
  (k : ℕ) (hk : 1 < k)
  (phi : ℝ)
  (x z : ExtReg)
  (layout : Gate.PhaseProductLayout x z k)
  (pts : List Point)
  (hpts : List.length pts = q k)
  (hInterp : GoodToomCookPoints k pts hpts)
  (ψ : qs.State)
  (ops : Prog k)
  (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops pts)
  (hψ : CleanWorkspaceState qs (initSignedLayoutState layout) (scanNeededWidths x z ops) ψ)
  (run_ops_start_state : run? ops State.start_state = some State.start_state) :
  let Wphase : ℕ := phaseLimbWidth x z k
  let coeff : Fin (q k) → ℚ := phaseCoeffFromPtsWidth k Wphase pts hpts
  qs.eval (compileOpsToSignedGate k hk phi x z layout coeff ops) ψ
    =
  qs.eval (Gate.SignedPhaseProd phi x z) ψ := by
  induction hψ with
  | ket b hworkspace =>
      exact
        eval_compileOpsToSignedGate_correct_ket
          (qs := qs)
          (k := k)
          (hk := hk)
          (phi := phi)
          (x := x)
          (z := z)
          (layout := layout)
          (pts := pts)
          (hpts := hpts)
          (hInterp := hInterp)
          (b := b)
          (ops := ops)
          (hC := hC)
          (hworkspace := hworkspace)
          (run_ops_start_state := run_ops_start_state)
  | zero => simp [qs.eval_zero]
  | add hψ hφ ihψ ihφ => simpa [qs.eval_add] using congrArg₂ (· + ·) ihψ ihφ
  | smul a hψ ihψ => simpa [qs.eval_smul] using congrArg (a • ·) ihψ

/-! =========================================================
    Section 3: Controlled signed correctness wrappers
    The controlled proof additionally shows that allocation preserves the control
    bit because the control qubit is outside the grown layout, then delegates the
    body to the controlled body/deallocation theorem.
========================================================= -/

/-- Basis-ket correctness of the controlled signed compiled circuit. -/
lemma eval_compileOpsToCSignedGate_correct_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (k : ℕ)
    (hk : 1 < k)
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z k)
    (hctrl : layout.ControlDisjoint ctrl)
    (pts : List Point)
    (hpts : pts.length = q k)
    (hInterp : GoodToomCookPoints k pts hpts)
    (ops : Prog k)
    (hC :
      ProgConsumesPtsSafe
        (k := k)
        (by omega)
        State.start_state
        ops
        pts)
    (hRun :
      run? ops State.start_state = some State.start_state)
    (b : qs.Basis)
    (hworkspace :
      CompilerWorkspaceOK
        (initSignedLayoutState layout)
        (scanNeededWidths x z ops)
        b) :
    qs.eval
      (compileOpsToCSignedGate
        k hk ctrl phi x z layout
        (phaseCoeffFromPtsWidth
          k
          (phaseLimbWidth x z k)
          pts
          hpts)
        ops)
      (qs.ket b)
    =
    qs.eval
      (Gate.CSignedPhaseProd ctrl phi x z)
      (qs.ket b) := by
  set need : NeededWidths k := scanNeededWidths x z ops
  set stInit : LayoutState k := initSignedLayoutState layout
  set stFinal : LayoutState k := targetSignedLayoutState stInit need
  set Wphase : ℕ := phaseLimbWidth x z k
  set coeff : Fin (q k) → ℚ := phaseCoeffFromPtsWidth k Wphase pts hpts
  rcases eval_compileSignedAllocations_ket_fits
      (qs := qs)
      (layout := layout)
      (ops := ops)
      (b := b)
      hworkspace with
    ⟨bAlloc, hAllocEval, hEncAlloc⟩
  rcases eval_compileSignedAllocations_sameOutside
      (qs := qs)
      (layout := layout)
      (ops := ops)
      (b := b)
      hworkspace with
    ⟨bAllocSO, hAllocSOEval, hAllocSO⟩
  have hbAllocSO : bAllocSO = bAlloc := by
    apply qs.ket_inj
    calc
      qs.ket bAllocSO
          =
        qs.eval
          (compileSignedAllocations k stInit stFinal)
          (qs.ket b) := by
            simpa [stInit, stFinal, need] using
              hAllocSOEval.symm
      _ = qs.ket bAlloc := by
            simpa [stInit, stFinal, need] using
              hAllocEval
  have hAllocSO' :
      SameOutsideLayout qs stFinal b bAlloc := by
    simpa [hbAllocSO, stInit, stFinal, need] using hAllocSO
  have hFitsFinal :
    ∀ {τ : State k},
      (∃ pre rest,
        ops = pre ++ rest ∧
        run? pre State.start_state = some τ) →
        (∀ j : Fin k,
          FitsSignedWidth
            (ExtReg.width (stFinal.xslot j))
            (evalRowX (qs := qs) stInit (τ j) b)) ∧
        (∀ j : Fin k,
          FitsSignedWidth
            (ExtReg.width (stFinal.zslot j))
            (evalRowZ (qs := qs) stInit (τ j) b)) := by
    intro τ hτ
    simpa [stInit, stFinal, need] using
      allocated_widths_sound
        (qs := qs)
        layout
        ops
        hworkspace.1
        b
        (σ := τ)
        hτ
  have hLayoutDisjoint : LayoutSlotsDisjoint stFinal := by
    simpa [stFinal, stInit] using targetSignedLayoutState_owned_disjoint layout need
  have hCtrlOutside :
      OutsideLayout
        stFinal
        (ExtReg.ofReg (qubitReg ctrl)) := by
    have hCtrlOwned :
        (∀ i,
          ctrl ∉ (stFinal.xslot i).ownedQubits) ∧
        (∀ i,
          ctrl ∉ (stFinal.zslot i).ownedQubits) := by
      simpa [stFinal, stInit] using
        controlDisjoint_target
          layout
          ctrl
          need
          hctrl
    constructor
    · intro i
      rw [ExtReg.ActiveDisjoint, Disjoint, List.disjoint_left]
      intro q hqCtrl hqSlot
      have hq : q = ctrl := by
        simpa [ExtReg.ofReg, qubitReg, Reg.singleton] using hqCtrl
      subst q
      exact hCtrlOwned.1 i (by
        simp only [ExtReg.ownedQubits, List.mem_append]
        exact Or.inl hqSlot)
    · intro i
      rw [ExtReg.ActiveDisjoint, Disjoint, List.disjoint_left]
      intro q hqCtrl hqSlot
      have hq : q = ctrl := by
        simpa [ExtReg.ofReg, qubitReg, Reg.singleton] using hqCtrl
      subst q
      exact hCtrlOwned.2 i (by
        simp only [ExtReg.ownedQubits, List.mem_append]
        exact Or.inl hqSlot)
  have hCtrlAlloc :
      RegEncoding.bit ctrl bAlloc =
        RegEncoding.bit ctrl b :=
    SameOutsideLayout.bit_eq_of_outside
      (qs := qs)
      hAllocSO'
      ctrl
      hCtrlOutside
  have hBodyDealloc :
    qs.eval
        (controlPhaseLeaves ctrl
          (compileAnnotatedOpsToSignedGateAux
            k hk phi coeff stFinal
            (annotatePhaseTermsAux k 0 ops)) ;;
         compileSignedDeallocations k stInit stFinal)
        (qs.ket bAlloc)
      =
    (if RegEncoding.bit ctrl b then
      phaseScalarFrom
        (qs := qs)
        k phi coeff stInit b pts 0
        (by simpa using hpts)
    else
      1) •
      qs.ket b := by
    exact
      eval_controlPhaseLeaves_compileAnnotatedOpsToSignedGateAux_of_blocks_then_dealloc
        (qs := qs) (k := k) (hk := hk) (ctrl := ctrl) (phi := phi) (pts := pts) (hpts := hpts)
        (coeff := coeff) (src := stInit) (dst := stFinal) (b0 := b) (bMid := bAlloc) (ops := ops)
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
      phaseScalarFrom
          (qs := qs)
          k phi coeff stInit b pts 0
          (by simpa using hpts)
        =
      Complex.exp
        (phi * Complex.I *
          (((extToInt x b : ℤ) : ℂ) *
           (((extToInt z b : ℤ) : ℂ)))) := by
    simpa [
      stInit,
      Wphase,
      coeff,
      phaseCoeffFromPtsForRegs
    ] using
      toom_cook_interpolation
        (qs := qs) (hk := hk) (phi := phi) (x := x) (z := z) (layout := layout)
        (pts := pts) (hpts := hpts) (hInterp := hInterp) (b := b)
  calc
    qs.eval
        (compileOpsToCSignedGate
          k hk ctrl phi x z layout coeff ops)
        (qs.ket b)
        =
      qs.eval
        (controlPhaseLeaves ctrl
          (compileAnnotatedOpsToSignedGateAux
            k hk phi coeff stFinal
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
        phaseScalarFrom
          (qs := qs)
          k phi coeff stInit b pts 0
          (by simpa using hpts)
      else
        1) •
        qs.ket b := hBodyDealloc
    _ =
      qs.eval
        (Gate.CSignedPhaseProd ctrl phi x z)
        (qs.ket b) := by
          by_cases hc : RegEncoding.bit ctrl b
          · rw [PhaseSemantics.eval_CSignedPhaseProd_ket]; simp [hc, hScalar]
          · rw [PhaseSemantics.eval_CSignedPhaseProd_ket]; simp [hc]

/-- State-level correctness of the controlled signed compiled circuit on clean workspace states. -/
lemma eval_compileOpsToCSignedGate_correct
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (k : ℕ)
    (hk : 1 < k)
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z k)
    (hctrl : layout.ControlDisjoint ctrl)
    (pts : List Point)
    (hpts : pts.length = q k)
    (hInterp : GoodToomCookPoints k pts hpts)
    (ops : Prog k)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops pts)
    (hRun : run? ops State.start_state = some State.start_state)
    (ψ : qs.State)
    (hψ :  CleanWorkspaceState qs (initSignedLayoutState layout) (scanNeededWidths x z ops) ψ) :
    qs.eval (compileOpsToCSignedGate k hk ctrl phi x z layout
      (phaseCoeffFromPtsWidth k (phaseLimbWidth x z k)  pts hpts) ops)  ψ
    =
    qs.eval (Gate.CSignedPhaseProd ctrl phi x z) ψ := by
  induction hψ with
  | ket b hworkspace =>
      exact
        eval_compileOpsToCSignedGate_correct_ket
          (qs := qs)
          (k := k)
          (hk := hk)
          (ctrl := ctrl)
          (phi := phi)
          (x := x)
          (z := z)
          (layout := layout)
          (hctrl := hctrl)
          (pts := pts)
          (hpts := hpts)
          (hInterp := hInterp)
          (ops := ops)
          (hC := hC)
          (hRun := hRun)
          (b := b)
          (hworkspace := hworkspace)
  | zero => simp [qs.eval_zero]
  | add hψ hφ ihψ ihφ => simpa [qs.eval_add] using congrArg₂ (· + ·) ihψ ihφ
  | smul a hψ ihψ => simpa [qs.eval_smul] using congrArg (a • ·) ihψ

/-! =========================================================
    Section 4: Controlled circuit branch theorem
    The final comparison theorem states that the controlled compiled circuit acts
    like the signed compiled circuit at phase `phi` when the control bit is set,
    and like the signed compiled circuit at phase `0` otherwise.
========================================================= -/

/-- A zero-angle signed phase product is identity on basis kets. -/
lemma eval_SignedPhaseProd_zero_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [PhaseSemantics qs]
    (x z : ExtReg)
    (b : qs.Basis) :
    qs.eval
      (Gate.SignedPhaseProd 0 x z)
      (qs.ket b)
      =
    qs.ket b := by
  rw [PhaseSemantics.eval_SignedPhaseProd_ket]; simp

/-- Controlled compilation equals the signed compilation selected by the input control bit. -/
lemma eval_controlled_compileOpsToSignedGate_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (k : ℕ)
    (hk : 1 < k)
    (ctrl : ℕ)
    (phi : ℝ)
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
    (hworkspace : CompilerWorkspaceOK (initSignedLayoutState layout) (scanNeededWidths x z ops) b) :
    qs.eval
      (compileOpsToCSignedGate  k hk ctrl phi x z layout
        (phaseCoeffFromPtsWidth k (phaseLimbWidth x z k) pts hpts) ops) (qs.ket b)
    =
    if RegEncoding.bit ctrl b then
      qs.eval (compileOpsToSignedGate k hk phi x z layout (phaseCoeffFromPtsWidth k
        (phaseLimbWidth x z k) pts hpts) ops) (qs.ket b)
    else
      qs.eval
        (compileOpsToSignedGate k hk 0 x z layout (phaseCoeffFromPtsWidth
          k (phaseLimbWidth x z k) pts hpts) ops) (qs.ket b) := by
  classical
  have hCS :=
    eval_compileOpsToCSignedGate_correct_ket
      (qs := qs) (k := k) (hk := hk) (phi := phi) (x := x) (z := z) (layout := layout)
      (hctrl := hctrl) (pts := pts) (hpts := hpts) (hInterp := hInterp) (b := b) (ops := ops)
      (hC := hC)
      (hRun := hRun)
      (hworkspace := hworkspace)
  have hSigned_phi :=
    eval_compileOpsToSignedGate_correct_ket
      (qs := qs) (k := k) (hk := hk) (phi := phi) (x := x) (z := z) (layout := layout)
      (pts := pts) (hpts := hpts) (hInterp := hInterp) (b := b) (ops := ops)
      (hC := hC)
      (hworkspace := hworkspace)
      (run_ops_start_state := hRun)
  have hSigned_zero :=
    eval_compileOpsToSignedGate_correct_ket
      (qs := qs) (k := k) (hk := hk) (phi := 0) (x := x) (z := z) (layout := layout)
      (pts := pts) (hpts := hpts) (hInterp := hInterp) (b := b) (ops := ops)
      (hC := hC)
      (hworkspace := hworkspace)
      (run_ops_start_state := hRun)
  by_cases hc : RegEncoding.bit ctrl b
  · simp [hc]
    calc
      qs.eval
          (compileOpsToCSignedGate
            k hk ctrl phi x z layout
            (phaseCoeffFromPtsWidth
              k
              (phaseLimbWidth x z k)
              pts
              hpts)
            ops)
          (qs.ket b)
          =
        qs.eval
          (Gate.CSignedPhaseProd ctrl phi x z)
          (qs.ket b) := hCS
      _ =
        qs.eval
          (Gate.SignedPhaseProd phi x z)
          (qs.ket b) := by
            rw [PhaseSemantics.eval_CSignedPhaseProd_ket]
            rw [PhaseSemantics.eval_SignedPhaseProd_ket]
            simp [hc]
      _ =
        qs.eval
          (compileOpsToSignedGate
            k hk phi x z layout
            (phaseCoeffFromPtsWidth
              k
              (phaseLimbWidth x z k)
              pts
              hpts)
            ops)
          (qs.ket b) := hSigned_phi.symm
  · simp [hc]
    calc
      qs.eval
          (compileOpsToCSignedGate
            k hk ctrl phi x z layout
            (phaseCoeffFromPtsWidth
              k
              (phaseLimbWidth x z k)
              pts
              hpts)
            ops)
          (qs.ket b)
          =
        qs.eval
          (Gate.CSignedPhaseProd ctrl phi x z)
          (qs.ket b) := hCS
      _ =
        qs.eval
          (Gate.SignedPhaseProd 0 x z)
          (qs.ket b) := by
            calc
              qs.eval
                  (Gate.CSignedPhaseProd ctrl phi x z)
                  (qs.ket b)
                  =
                qs.ket b := by
                  rw [PhaseSemantics.eval_CSignedPhaseProd_ket]
                  simp [hc]
              _ =
                qs.eval
                  (Gate.SignedPhaseProd 0 x z)
                  (qs.ket b) :=
                    (eval_SignedPhaseProd_zero_ket
                      (qs := qs)
                      x
                      z
                      b).symm
      _ =
        qs.eval
          (compileOpsToSignedGate
            k hk 0 x z layout
            (phaseCoeffFromPtsWidth
              k
              (phaseLimbWidth x z k)
              pts
              hpts)
            ops)
          (qs.ket b) := hSigned_zero.symm

end Shor
