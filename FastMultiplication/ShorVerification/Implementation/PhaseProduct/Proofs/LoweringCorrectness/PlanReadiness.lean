import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.LoweringCorrectness.Workspace

namespace Shor
open Gate
open Operations

/-!
# Phase-Product Plan Readiness
This file assembles all readiness proofs for canonical recursive signed
phase-product lowering. It first proves readiness for compiled annotated bodies,
then handles allocation and deallocation plans, and finally lifts the canonical
recursive plan from clean basis states to clean quantum states.
-/

/-! =========================================================
    Readiness Of Compiled Bodies
    The body compiler alternates arithmetic prefixes with phase-product leaves.
    No-phase prefixes simply thread readiness forward; block decompositions then
    identify the basis state reached before each recursive phase leaf.
========================================================= -/

/-- A no-phase prefix threads readiness from the suffix back to the whole annotated program. -/
lemma planCompileAnnotatedOps_ready_append_of_noPhase
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    [GateSemanticsFacts qs]
    {k : ℕ}
    (hk : 1 < k)
    (pts : List Point)
    (hpts : pts.length = q k)
    (allOps : Prog k)
    (initSize : ℕ)
    (phi : ℝ)
    (coeff : Fin (q k) → ℚ)
    (dst : LayoutState k)
    (recurse :
      ∀ (i : Fin k) (theta : ℝ),
        PhaseLoweringPlan k hk pts hpts allOps initSize
          (Gate.SignedPhaseProd theta (dst.xslot i) (dst.zslot i)))
    (pre : Prog k)
    (hNo : NoPhase pre)
    (n : ℕ)
    (suffix : List (AnnotatedOp k))
    (ψ : qs.State)
    (hTail :
      PhaseLoweringReady qs
        (planCompileAnnotatedOpsToSignedGateAux (hk := hk) (pts := pts) (hpts := hpts) (ops := allOps)
          initSize phi coeff dst recurse suffix)
        (qs.eval
          (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst (annotatePhaseTermsAux k n pre)) ψ)) :
    PhaseLoweringReady
      qs
      (planCompileAnnotatedOpsToSignedGateAux
        (hk := hk)
        (pts := pts)
        (hpts := hpts)
        (ops := allOps)
        initSize phi coeff dst recurse
        (annotatePhaseTermsAux k n pre ++ suffix))
      ψ := by
  induction pre generalizing n ψ with
  | nil =>
      simpa [
        annotatePhaseTermsAux,
        compileAnnotatedOpsToSignedGateAux,
        planCompileAnnotatedOpsToSignedGateAux,
        qs.eval_id
      ] using hTail
  | cons op rest ih =>
      have hNoRest : NoPhase rest := by
        intro i hi
        exact hNo i (by simp [hi])
      cases op with
      | shiftL i m =>
          have hTail' :
              PhaseLoweringReady
                qs
                (planCompileAnnotatedOpsToSignedGateAux
                  (hk := hk)
                  (pts := pts)
                  (hpts := hpts)
                  (ops := allOps)
                  initSize phi coeff dst recurse suffix)
                (qs.eval
                  (compileAnnotatedOpsToSignedGateAux
                    k hk phi coeff dst
                    (annotatePhaseTermsAux k n rest))
                  (qs.eval
                    (Gate.ShiftL (dst.zslot i) m)
                    (qs.eval
                      (Gate.ShiftL (dst.xslot i) m)
                      ψ))) := by
            simpa [
              annotatePhaseTermsAux,
              compileAnnotatedOpsToSignedGateAux,
              qs.eval_seq
            ] using hTail
          have hrest :=
            ih hNoRest n
              (qs.eval
                (Gate.ShiftL (dst.zslot i) m)
                (qs.eval
                  (Gate.ShiftL (dst.xslot i) m)
                  ψ))
              hTail'
          dsimp [
            annotatePhaseTermsAux,
            planCompileAnnotatedOpsToSignedGateAux
          ]
          refine ⟨trivial, trivial, ?_⟩
          change
            PhaseLoweringReady
              qs
              _
              (LowerGateClass.evalL
                (qs := qs)
                (LowGate.ShiftL (dst.zslot i) m)
                (LowerGateClass.evalL
                  (qs := qs)
                  (LowGate.ShiftL (dst.xslot i) m)
                  ψ))
          rw [
            LowerGateClass.evalL_shiftL,
            LowerGateClass.evalL_shiftL
          ]
          exact hrest
      | shiftR i m =>
          have hTail' :
              PhaseLoweringReady
                qs
                (planCompileAnnotatedOpsToSignedGateAux
                  (hk := hk)
                  (pts := pts)
                  (hpts := hpts)
                  (ops := allOps)
                  initSize phi coeff dst recurse suffix)
                (qs.eval
                  (compileAnnotatedOpsToSignedGateAux
                    k hk phi coeff dst
                    (annotatePhaseTermsAux k n rest))
                  (qs.eval
                    (Gate.ShiftR (dst.zslot i) m)
                    (qs.eval
                      (Gate.ShiftR (dst.xslot i) m)
                      ψ))) := by
            simpa [
              annotatePhaseTermsAux,
              compileAnnotatedOpsToSignedGateAux,
              qs.eval_seq
            ] using hTail
          have hrest :=
            ih hNoRest n
              (qs.eval
                (Gate.ShiftR (dst.zslot i) m)
                (qs.eval
                  (Gate.ShiftR (dst.xslot i) m)
                  ψ))
              hTail'
          dsimp [
            annotatePhaseTermsAux,
            planCompileAnnotatedOpsToSignedGateAux
          ]
          refine ⟨trivial, trivial, ?_⟩
          change
            PhaseLoweringReady
              qs
              _
              (LowerGateClass.evalL
                (qs := qs)
                (LowGate.ShiftR (dst.zslot i) m)
                (LowerGateClass.evalL
                  (qs := qs)
                  (LowGate.ShiftR (dst.xslot i) m)
                  ψ))
          rw [
            LowerGateClass.evalL_shiftR,
            LowerGateClass.evalL_shiftR
          ]
          exact hrest
      | negate i =>
          have hTail' :
              PhaseLoweringReady
                qs
                (planCompileAnnotatedOpsToSignedGateAux
                  (hk := hk)
                  (pts := pts)
                  (hpts := hpts)
                  (ops := allOps)
                  initSize phi coeff dst recurse suffix)
                (qs.eval
                  (compileAnnotatedOpsToSignedGateAux
                    k hk phi coeff dst
                    (annotatePhaseTermsAux k n rest))
                  (qs.eval
                    (Gate.Negate (dst.zslot i))
                    (qs.eval
                      (Gate.Negate (dst.xslot i))
                      ψ))) := by
            simpa [
              annotatePhaseTermsAux,
              compileAnnotatedOpsToSignedGateAux,
              qs.eval_seq
            ] using hTail
          have hrest :=
            ih hNoRest n
              (qs.eval
                (Gate.Negate (dst.zslot i))
                (qs.eval
                  (Gate.Negate (dst.xslot i))
                  ψ))
              hTail'
          dsimp [
            annotatePhaseTermsAux,
            planCompileAnnotatedOpsToSignedGateAux
          ]
          refine ⟨trivial, trivial, ?_⟩
          change
            PhaseLoweringReady
              qs
              _
              (LowerGateClass.evalL
                (qs := qs)
                (LowGate.Negate (dst.zslot i))
                (LowerGateClass.evalL
                  (qs := qs)
                  (LowGate.Negate (dst.xslot i))
                  ψ))
          rw [
            LowerGateClass.evalL_negate,
            LowerGateClass.evalL_negate
          ]
          exact hrest
      | addScaled d s negSrc sh =>
          have hTail' :
              PhaseLoweringReady
                qs
                (planCompileAnnotatedOpsToSignedGateAux
                  (hk := hk)
                  (pts := pts)
                  (hpts := hpts)
                  (ops := allOps)
                  initSize phi coeff dst recurse suffix)
                (qs.eval
                  (compileAnnotatedOpsToSignedGateAux
                    k hk phi coeff dst
                    (annotatePhaseTermsAux k n rest))
                  (qs.eval
                    (Gate.AddScaled
                      (dst.zslot d)
                      (dst.zslot s)
                      negSrc sh)
                    (qs.eval
                      (Gate.AddScaled
                        (dst.xslot d)
                        (dst.xslot s)
                        negSrc sh)
                      ψ))) := by
            simpa [
              annotatePhaseTermsAux,
              compileAnnotatedOpsToSignedGateAux,
              qs.eval_seq
            ] using hTail
          have hrest :=
            ih hNoRest n
              (qs.eval
                (Gate.AddScaled
                  (dst.zslot d)
                  (dst.zslot s)
                  negSrc sh)
                (qs.eval
                  (Gate.AddScaled
                    (dst.xslot d)
                    (dst.xslot s)
                    negSrc sh)
                  ψ))
              hTail'
          dsimp [
            annotatePhaseTermsAux,
            planCompileAnnotatedOpsToSignedGateAux
          ]
          refine ⟨trivial, trivial, ?_⟩
          change
            PhaseLoweringReady
              qs
              _
              (LowerGateClass.evalL
                (qs := qs)
                (LowGate.AddScaled
                  (dst.zslot d)
                  (dst.zslot s)
                  negSrc sh)
                (LowerGateClass.evalL
                  (qs := qs)
                  (LowGate.AddScaled
                    (dst.xslot d)
                    (dst.xslot s)
                    negSrc sh)
                  ψ))
          rw [
            LowerGateClass.evalL_addScaled,
            LowerGateClass.evalL_addScaled
          ]
          exact hrest
      | phaseProduct i =>
          exfalso
          exact hNo i (by simp)

/-- Block-level induction proving readiness for the compiled annotated body on a basis ket. -/
lemma planCompileAnnotatedOps_ready_ket_of_blocks_from
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGatePrimitiveBridge qs]
    {k : ℕ}
    (hk : 1 < k)
    (planPts : List Point)
    (hPlanPts : planPts.length = q k)
    (hInterp : GoodToomCookPoints k planPts hPlanPts)
    (allOps : Prog k)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state allOps planPts)
    (hRun : run? allOps State.start_state = some State.start_state)
    (initSize : ℕ)
    (phi : ℝ)
    (coeff : Fin (q k) → ℚ)
    (src dst : LayoutState k)
    (recurse :
      ∀ (i : Fin k) (theta : ℝ),
        PhaseLoweringPlan k hk planPts hPlanPts allOps initSize
          (Gate.SignedPhaseProd theta (dst.xslot i) (dst.zslot i)))
    (hleaf :
      ∀ (i : Fin k) (theta : ℝ) (b' : qs.Basis),
        RecursiveWorkspaceCleanBasis (dst.xslot i) (dst.zslot i) b' →
        PhaseLoweringReady qs (recurse i theta) (qs.ket b')) :
    ∀ {σ : State k}
      {bodyOps : Prog k}
      {blockPts : List Point},
      BlockDecomposition (k := k) (by omega) σ bodyOps blockPts →
      ∀ (n : ℕ)
        (_hn : n + blockPts.length = q k)
        (b₀ bCur : qs.Basis),
        LayoutSlotsDisjoint dst →
        (∀ {τ : State k},
          (∃ pre rest,
            bodyOps = pre ++ rest ∧
            run? pre σ = some τ) →
          (∀ j : Fin k,
            FitsSignedWidth
              (ExtReg.width (dst.xslot j))
              (evalRowX (qs := qs) src (τ j) b₀))
          ∧
          (∀ j : Fin k,
            FitsSignedWidth
              (ExtReg.width (dst.zslot j))
              (evalRowZ (qs := qs) src (τ j) b₀))) →
        (∀ {pre rest : Prog k}
          {d s : Fin k}
          {negSrc : Bool}
          {sh : ℕ},
          bodyOps =
              pre ++
                valid_ops.addScaled d s negSrc sh ::
                rest →
          d ≠ s) →
        EncodesStateFromFits
          qs src dst σ b₀ bCur →
        (∀ b' : qs.Basis,
          SameOutsideLayout qs dst bCur b' →
          ∀ i : Fin k,
            RecursiveWorkspaceCleanBasis
              (dst.xslot i)
              (dst.zslot i)
              b') →
        PhaseLoweringReady
          qs
          (planCompileAnnotatedOpsToSignedGateAux
            (hk := hk)
            (pts := planPts)
            (hpts := hPlanPts)
            (ops := allOps)
            initSize
            phi
            coeff
            dst
            recurse
            (annotatePhaseTermsAux k n bodyOps))
          (qs.ket bCur) := by
  intro σ bodyOps blockPts hB
  induction hB with
  | nil σ σ' tail hNo hrun =>
      intro n hn b₀ bCur hdisjoint hFits hSafeAdd hEnc hcleanOutside
      have hready :=
        planCompileAnnotatedOps_ready_append_of_noPhase
          qs hk planPts hPlanPts allOps
          initSize phi coeff dst recurse
          tail hNo n []
          (qs.ket bCur)
          (by trivial)
      rw [List.append_nil] at hready
      exact hready
  | cons B hrest ih =>
      intro n hn b₀ bCur hdisjoint hFits hSafeAdd hEnc hcleanOutside
      rename_i σ₂ pt pts₂ oprest
      have hlt : n < q k := by
        simp at hn
        omega
      let l : Fin (q k) := ⟨n, hlt⟩
      let theta : ℝ :=
        phi * (((coeff l : ℚ) : ℝ))
      have hnTail :
          n + 1 + pts₂.length = q k := by
        simp at hn
        omega
      have hFitsArith :
          ∀ {τ : State k},
            (∃ pre rest,
              B.arith = pre ++ rest ∧
              run? pre σ₂ = some τ) →
            (∀ j : Fin k,
              FitsSignedWidth
                (ExtReg.width (dst.xslot j))
                (evalRowX
                  (qs := qs) src (τ j) b₀))
            ∧
            (∀ j : Fin k,
              FitsSignedWidth
                (ExtReg.width (dst.zslot j))
                (evalRowZ
                  (qs := qs) src (τ j) b₀)) := by
        intro τ hτ
        rcases hτ with
          ⟨pre, rest, hsplit, hrunPre⟩
        apply hFits
        refine
          ⟨pre,
           rest ++ [.phaseProduct B.i] ++ oprest,
           ?_,
           hrunPre⟩
        simp [
          PhaseBlock.toProg,
          hsplit,
          List.append_assoc
        ]
      have hSafeAddArith :
          ∀ {pre rest : Prog k}
            {d s : Fin k}
            {negSrc : Bool}
            {sh : ℕ},
            B.arith =
                pre ++
                  .addScaled d s negSrc sh ::
                  rest →
            d ≠ s := by
        intro pre rest d s negSrc sh hadd
        exact
          hSafeAdd
            (pre := pre)
            (rest :=
              rest ++
                [.phaseProduct B.i] ++
                oprest)
            (d := d)
            (s := s)
            (negSrc := negSrc)
            (sh := sh)
            (by
              rw [PhaseBlock.toProg]
              simp [hadd, List.append_assoc])
      rcases
          encodesFrom_after_noPhase_run_ket_gen
            (qs := qs)
            (hk := hk)
            (phi := phi)
            (coeff := coeff)
            (src := src)
            (dst := dst)
            (ops := B.arith)
            (σ := σ₂)
            (σ' := B.σmid)
            (bRef := b₀)
            (bCur := bCur)
            (n := n)
            hdisjoint
            hFitsArith
            hSafeAddArith
            B.noPhase_pre
            B.run_pre
            hEnc
        with ⟨bMid, hArithEval, hArithEnc⟩
      rcases
          sameOutside_after_noPhase_run_ket_gen
            (qs := qs)
            (hk := hk)
            (phi := phi)
            (coeff := coeff)
            (src := src)
            (dst := dst)
            (ops := B.arith)
            (σ := σ₂)
            (σ' := B.σmid)
            (bRef := b₀)
            (bCur := bCur)
            (n := n)
            hdisjoint
            hFitsArith
            hSafeAddArith
            B.noPhase_pre
            B.run_pre
            hEnc
        with ⟨bMid', hArithEval', hArithSO'⟩
      have hbMid : bMid' = bMid := by
        apply qs.ket_inj
        rw [← hArithEval, ← hArithEval']
      subst bMid'
      have hArithSO :
          SameOutsideLayout
            qs dst bCur bMid := hArithSO'
      have hSlotClean :
          RecursiveWorkspaceCleanBasis
            (dst.xslot B.i)
            (dst.zslot B.i)
            bMid := by
        exact
          hcleanOutside
            bMid
            hArithSO
            B.i
      have hLeafReady :
          PhaseLoweringReady
            qs
            (recurse B.i theta)
            (qs.ket bMid) := by
        exact
          hleaf
            B.i
            theta
            bMid
            hSlotClean
      have hRunBlock :
          run? B.toProg σ₂ =
            some B.σmid := by
        simp [
          PhaseBlock.toProg,
          run?_append,
          B.run_pre,
          applyOp?
        ]
      have hFitsTail :
          ∀ {τ : State k},
            (∃ pre rest,
              oprest = pre ++ rest ∧
              run? pre B.σmid = some τ) →
            (∀ j : Fin k,
              FitsSignedWidth
                (ExtReg.width (dst.xslot j))
                (evalRowX
                  (qs := qs) src (τ j) b₀))
            ∧
            (∀ j : Fin k,
              FitsSignedWidth
                (ExtReg.width (dst.zslot j))
                (evalRowZ
                  (qs := qs) src (τ j) b₀)) := by
        intro τ hτ
        rcases hτ with
          ⟨pre, rest, hsplit, hrunPre⟩
        apply hFits
        refine
          ⟨B.toProg ++ pre,
           rest,
           ?_,
           ?_⟩
        · simp [hsplit, List.append_assoc]
        · rw [run?_append, hRunBlock]
          simpa using hrunPre
      have hSafeAddTail :
          ∀ {pre rest : Prog k}
            {d s : Fin k}
            {negSrc : Bool}
            {sh : ℕ},
            oprest =
                pre ++
                  .addScaled d s negSrc sh ::
                  rest →
            d ≠ s := by
        intro pre rest d s negSrc sh hadd
        exact
          hSafeAdd
            (pre := B.toProg ++ pre)
            (rest := rest)
            (d := d)
            (s := s)
            (negSrc := negSrc)
            (sh := sh)
            (by simp [hadd, List.append_assoc])
      have hCleanTail :
          ∀ b' : qs.Basis,
            SameOutsideLayout
                qs dst bMid b' →
            ∀ i : Fin k,
              RecursiveWorkspaceCleanBasis
                (dst.xslot i)
                (dst.zslot i)
                b' := by
        intro b' hSO i
        exact
          hcleanOutside
            b'
            (SameOutsideLayout.trans
              (qs := qs)
              hArithSO
              hSO)
            i
      have hTailReady :
          PhaseLoweringReady
            qs
            (planCompileAnnotatedOpsToSignedGateAux
              (hk := hk)
              (pts := planPts)
              (hpts := hPlanPts)
              (ops := allOps)
              initSize
              phi
              coeff
              dst
              recurse
              (annotatePhaseTermsAux
                k (n + 1) oprest))
            (qs.ket bMid) := by
        exact
          ih
            (n + 1)
            hnTail
            b₀
            bMid
            hdisjoint
            hFitsTail
            hSafeAddTail
            hArithEnc
            hCleanTail
      have hLeafEval :
          LowerGateClass.evalL
              (qs := qs)
              (lowerGateRec
                (recurse B.i theta))
              (qs.ket bMid)
            =
          qs.eval
              (Gate.SignedPhaseProd
                theta
                (dst.xslot B.i)
                (dst.zslot B.i))
              (qs.ket bMid) := by
        exact
          evalL_lowerGateRec_correct
            (qs := qs)
            (hInterp := hInterp)
            (hC := hC)
            (hRun := hRun)
            (recurse B.i theta)
            (qs.ket bMid)
            hLeafReady
      have hTailAfterLeaf :
          PhaseLoweringReady
            qs
            (planCompileAnnotatedOpsToSignedGateAux
              (hk := hk)
              (pts := planPts)
              (hpts := hPlanPts)
              (ops := allOps)
              initSize
              phi
              coeff
              dst
              recurse
              (annotatePhaseTermsAux
                k (n + 1) oprest))
            (LowerGateClass.evalL
              (qs := qs)
              (lowerGateRec
                (recurse B.i theta))
              (qs.ket bMid)) := by
        rw [
          hLeafEval,
          PhaseSemantics.eval_SignedPhaseProd_ket
        ]
        exact
          PhaseLoweringReady.smul
            qs
            _
            _
            hTailReady
      have hPhaseTail :
          PhaseLoweringReady
            qs
            (planCompileAnnotatedOpsToSignedGateAux
              (hk := hk)
              (pts := planPts)
              (hpts := hPlanPts)
              (ops := allOps)
              initSize
              phi
              coeff
              dst
              recurse
              ({
                op := .phaseProduct B.i
                phaseTerm? := some l
              } ::
              annotatePhaseTermsAux
                k (n + 1) oprest))
            (qs.ket bMid) := by
        change
          PhaseLoweringReady
              qs
              (recurse B.i theta)
              (qs.ket bMid)
          ∧
          PhaseLoweringReady
              qs
              (planCompileAnnotatedOpsToSignedGateAux
                (hk := hk)
                (pts := planPts)
                (hpts := hPlanPts)
                (ops := allOps)
                initSize
                phi
                coeff
                dst
                recurse
                (annotatePhaseTermsAux
                  k (n + 1) oprest))
              (LowerGateClass.evalL
                (qs := qs)
                (lowerGateRec
                  (recurse B.i theta))
                (qs.ket bMid))
        exact ⟨hLeafReady, hTailAfterLeaf⟩
      have hAfterArith :
          PhaseLoweringReady
            qs
            (planCompileAnnotatedOpsToSignedGateAux
              (hk := hk)
              (pts := planPts)
              (hpts := hPlanPts)
              (ops := allOps)
              initSize
              phi
              coeff
              dst
              recurse
              ({
                op := .phaseProduct B.i
                phaseTerm? := some l
              } ::
              annotatePhaseTermsAux
                k (n + 1) oprest))
            (qs.eval
              (compileAnnotatedOpsToSignedGateAux
                k hk phi coeff dst
                (annotatePhaseTermsAux
                  k n B.arith))
              (qs.ket bCur)) := by
        rw [hArithEval]
        exact hPhaseTail
      have hReadyCombined :
          PhaseLoweringReady
            qs
            (planCompileAnnotatedOpsToSignedGateAux
              (hk := hk)
              (pts := planPts)
              (hpts := hPlanPts)
              (ops := allOps)
              initSize
              phi
              coeff
              dst
              recurse
              (annotatePhaseTermsAux
                  k n B.arith ++
                ({
                  op := .phaseProduct B.i
                  phaseTerm? := some l
                } ::
                annotatePhaseTermsAux
                  k (n + 1) oprest)))
            (qs.ket bCur) := by
        exact
          planCompileAnnotatedOps_ready_append_of_noPhase
            qs hk planPts hPlanPts allOps
            initSize phi coeff dst recurse
            B.arith
            B.noPhase_pre
            n
            ({
              op := .phaseProduct B.i
              phaseTerm? := some l
            } ::
            annotatePhaseTermsAux
              k (n + 1) oprest)
            (qs.ket bCur)
            hAfterArith
      have hCount :
          phaseProductCount B.toProg = 1 := by
        rw [PhaseBlock.toProg, phaseProductCount_append]
        simp [
          phaseProductCount_eq_zero_of_NoPhase,
          B.noPhase_pre,
          phaseProductCount
        ]
      have hAnnAll :
          annotatePhaseTermsAux
              k n (B.toProg ++ oprest)
            =
          annotatePhaseTermsAux k n B.toProg ++
            annotatePhaseTermsAux
              k (n + 1) oprest := by
        rw [annotatePhaseTermsAux_append]
        simp [hCount]
      have hAnnBlock :
          annotatePhaseTermsAux k n B.toProg
            =
          annotatePhaseTermsAux k n B.arith ++
            [{
              op := .phaseProduct B.i
              phaseTerm? := some l
            }] := by
        rw [
          PhaseBlock.toProg,
          annotatePhaseTermsAux_append
        ]
        simp [
          annotatePhaseTermsAux,
          l,
          hlt,
          phaseProductCount_eq_zero_of_NoPhase,
          B.noPhase_pre
        ]
      rw [hAnnAll, hAnnBlock]
      have hList :
          (annotatePhaseTermsAux k n B.arith ++
              [{
                op := .phaseProduct B.i
                phaseTerm? := some l
              }]) ++
            annotatePhaseTermsAux k (n + 1) oprest
          =
          annotatePhaseTermsAux k n B.arith ++
            ({
              op := .phaseProduct B.i
              phaseTerm? := some l
            } ::
            annotatePhaseTermsAux k (n + 1) oprest) := by
        rw [List.append_assoc]
        rfl
      rw [hList]
      exact hReadyCombined

/-- A no-phase prefix threads controlled readiness from the suffix back to the whole annotated program. -/
lemma planCompileAnnotatedOps_c_ready_append_of_noPhase
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    [GateSemanticsFacts qs]
    {k : ℕ}
    (hk : 1 < k)
    (pts : List Point)
    (hpts : pts.length = q k)
    (allOps : Prog k)
    (initSize : ℕ)
    (ctrl : ℕ)
    (phi : ℝ)
    (coeff : Fin (q k) → ℚ)
    (dst : LayoutState k)
    (recurse :
      ∀ (i : Fin k) (theta : ℝ),
        PhaseLoweringPlan k hk pts hpts allOps initSize
          (Gate.CSignedPhaseProd ctrl theta (dst.xslot i) (dst.zslot i)))
    (pre : Prog k)
    (hNo : NoPhase pre)
    (n : ℕ)
    (suffix : List (AnnotatedOp k))
    (ψ : qs.State)
    (hTail :
      PhaseLoweringReady qs
        (planCompileAnnotatedOpsToCSignedGateAux (hk := hk) (pts := pts) (hpts := hpts) (ops := allOps)
          initSize ctrl phi coeff dst recurse suffix)
        (qs.eval
          (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst (annotatePhaseTermsAux k n pre)) ψ)) :
    PhaseLoweringReady
      qs
      (planCompileAnnotatedOpsToCSignedGateAux
        (hk := hk)
        (pts := pts)
        (hpts := hpts)
        (ops := allOps)
        initSize ctrl phi coeff dst recurse
        (annotatePhaseTermsAux k n pre ++ suffix))
      ψ := by
  induction pre generalizing n ψ with
  | nil =>
      simpa [
        annotatePhaseTermsAux,
        compileAnnotatedOpsToSignedGateAux,
        planCompileAnnotatedOpsToCSignedGateAux,
        qs.eval_id
      ] using hTail
  | cons op rest ih =>
      have hNoRest : NoPhase rest := by
        intro i hi
        exact hNo i (by simp [hi])
      cases op with
      | shiftL i m =>
          have hTail' :
              PhaseLoweringReady
                qs
                (planCompileAnnotatedOpsToCSignedGateAux
                  (hk := hk)
                  (pts := pts)
                  (hpts := hpts)
                  (ops := allOps)
                  initSize ctrl phi coeff dst recurse suffix)
                (qs.eval
                  (compileAnnotatedOpsToSignedGateAux
                    k hk phi coeff dst
                    (annotatePhaseTermsAux k n rest))
                  (qs.eval
                    (Gate.ShiftL (dst.zslot i) m)
                    (qs.eval
                      (Gate.ShiftL (dst.xslot i) m)
                      ψ))) := by
            simpa [
              annotatePhaseTermsAux,
              compileAnnotatedOpsToSignedGateAux,
              qs.eval_seq
            ] using hTail
          have hrest :=
            ih hNoRest n
              (qs.eval
                (Gate.ShiftL (dst.zslot i) m)
                (qs.eval
                  (Gate.ShiftL (dst.xslot i) m)
                  ψ))
              hTail'
          dsimp [
            annotatePhaseTermsAux,
            planCompileAnnotatedOpsToCSignedGateAux
          ]
          refine ⟨trivial, trivial, ?_⟩
          change
            PhaseLoweringReady
              qs
              _
              (LowerGateClass.evalL
                (qs := qs)
                (LowGate.ShiftL (dst.zslot i) m)
                (LowerGateClass.evalL
                  (qs := qs)
                  (LowGate.ShiftL (dst.xslot i) m)
                  ψ))
          rw [
            LowerGateClass.evalL_shiftL,
            LowerGateClass.evalL_shiftL
          ]
          exact hrest
      | shiftR i m =>
          have hTail' :
              PhaseLoweringReady
                qs
                (planCompileAnnotatedOpsToCSignedGateAux
                  (hk := hk)
                  (pts := pts)
                  (hpts := hpts)
                  (ops := allOps)
                  initSize ctrl phi coeff dst recurse suffix)
                (qs.eval
                  (compileAnnotatedOpsToSignedGateAux
                    k hk phi coeff dst
                    (annotatePhaseTermsAux k n rest))
                  (qs.eval
                    (Gate.ShiftR (dst.zslot i) m)
                    (qs.eval
                      (Gate.ShiftR (dst.xslot i) m)
                      ψ))) := by
            simpa [
              annotatePhaseTermsAux,
              compileAnnotatedOpsToSignedGateAux,
              qs.eval_seq
            ] using hTail
          have hrest :=
            ih hNoRest n
              (qs.eval
                (Gate.ShiftR (dst.zslot i) m)
                (qs.eval
                  (Gate.ShiftR (dst.xslot i) m)
                  ψ))
              hTail'
          dsimp [
            annotatePhaseTermsAux,
            planCompileAnnotatedOpsToCSignedGateAux
          ]
          refine ⟨trivial, trivial, ?_⟩
          change
            PhaseLoweringReady
              qs
              _
              (LowerGateClass.evalL
                (qs := qs)
                (LowGate.ShiftR (dst.zslot i) m)
                (LowerGateClass.evalL
                  (qs := qs)
                  (LowGate.ShiftR (dst.xslot i) m)
                  ψ))
          rw [
            LowerGateClass.evalL_shiftR,
            LowerGateClass.evalL_shiftR
          ]
          exact hrest
      | negate i =>
          have hTail' :
              PhaseLoweringReady
                qs
                (planCompileAnnotatedOpsToCSignedGateAux
                  (hk := hk)
                  (pts := pts)
                  (hpts := hpts)
                  (ops := allOps)
                  initSize ctrl phi coeff dst recurse suffix)
                (qs.eval
                  (compileAnnotatedOpsToSignedGateAux
                    k hk phi coeff dst
                    (annotatePhaseTermsAux k n rest))
                  (qs.eval
                    (Gate.Negate (dst.zslot i))
                    (qs.eval
                      (Gate.Negate (dst.xslot i))
                      ψ))) := by
            simpa [
              annotatePhaseTermsAux,
              compileAnnotatedOpsToSignedGateAux,
              qs.eval_seq
            ] using hTail
          have hrest :=
            ih hNoRest n
              (qs.eval
                (Gate.Negate (dst.zslot i))
                (qs.eval
                  (Gate.Negate (dst.xslot i))
                  ψ))
              hTail'
          dsimp [
            annotatePhaseTermsAux,
            planCompileAnnotatedOpsToCSignedGateAux
          ]
          refine ⟨trivial, trivial, ?_⟩
          change
            PhaseLoweringReady
              qs
              _
              (LowerGateClass.evalL
                (qs := qs)
                (LowGate.Negate (dst.zslot i))
                (LowerGateClass.evalL
                  (qs := qs)
                  (LowGate.Negate (dst.xslot i))
                  ψ))
          rw [
            LowerGateClass.evalL_negate,
            LowerGateClass.evalL_negate
          ]
          exact hrest
      | addScaled d s negSrc sh =>
          have hTail' :
              PhaseLoweringReady
                qs
                (planCompileAnnotatedOpsToCSignedGateAux
                  (hk := hk)
                  (pts := pts)
                  (hpts := hpts)
                  (ops := allOps)
                  initSize ctrl phi coeff dst recurse suffix)
                (qs.eval
                  (compileAnnotatedOpsToSignedGateAux
                    k hk phi coeff dst
                    (annotatePhaseTermsAux k n rest))
                  (qs.eval
                    (Gate.AddScaled
                      (dst.zslot d)
                      (dst.zslot s)
                      negSrc sh)
                    (qs.eval
                      (Gate.AddScaled
                        (dst.xslot d)
                        (dst.xslot s)
                        negSrc sh)
                      ψ))) := by
            simpa [
              annotatePhaseTermsAux,
              compileAnnotatedOpsToSignedGateAux,
              qs.eval_seq
            ] using hTail
          have hrest :=
            ih hNoRest n
              (qs.eval
                (Gate.AddScaled
                  (dst.zslot d)
                  (dst.zslot s)
                  negSrc sh)
                (qs.eval
                  (Gate.AddScaled
                    (dst.xslot d)
                    (dst.xslot s)
                    negSrc sh)
                  ψ))
              hTail'
          dsimp [
            annotatePhaseTermsAux,
            planCompileAnnotatedOpsToCSignedGateAux
          ]
          refine ⟨trivial, trivial, ?_⟩
          change
            PhaseLoweringReady
              qs
              _
              (LowerGateClass.evalL
                (qs := qs)
                (LowGate.AddScaled
                  (dst.zslot d)
                  (dst.zslot s)
                  negSrc sh)
                (LowerGateClass.evalL
                  (qs := qs)
                  (LowGate.AddScaled
                    (dst.xslot d)
                    (dst.xslot s)
                    negSrc sh)
                  ψ))
          rw [
            LowerGateClass.evalL_addScaled,
            LowerGateClass.evalL_addScaled
          ]
          exact hrest
      | phaseProduct i =>
          exfalso
          exact hNo i (by simp)

/-- Block-level induction proving controlled readiness for the compiled annotated body on a basis ket. -/
lemma planCompileAnnotatedOps_c_ready_ket_of_blocks_from
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGatePrimitiveBridge qs]
    {k : ℕ}
    (hk : 1 < k)
    (planPts : List Point)
    (hPlanPts : planPts.length = q k)
    (hInterp : GoodToomCookPoints k planPts hPlanPts)
    (allOps : Prog k)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state allOps planPts)
    (hRun : run? allOps State.start_state = some State.start_state)
    (initSize : ℕ)
    (ctrl : ℕ)
    (phi : ℝ)
    (coeff : Fin (q k) → ℚ)
    (src dst : LayoutState k)
    (recurse :
      ∀ (i : Fin k) (theta : ℝ),
        PhaseLoweringPlan k hk planPts hPlanPts allOps initSize
          (Gate.CSignedPhaseProd ctrl theta (dst.xslot i) (dst.zslot i)))
    (hleaf :
      ∀ (i : Fin k) (theta : ℝ) (b' : qs.Basis),
        RecursiveWorkspaceCleanBasis (dst.xslot i) (dst.zslot i) b' →
        PhaseLoweringReady qs (recurse i theta) (qs.ket b')) :
    ∀ {σ : State k}
      {bodyOps : Prog k}
      {blockPts : List Point},
      BlockDecomposition (k := k) (by omega) σ bodyOps blockPts →
      ∀ (n : ℕ)
        (_hn : n + blockPts.length = q k)
        (b₀ bCur : qs.Basis),
        LayoutSlotsDisjoint dst →
        (∀ {τ : State k},
          (∃ pre rest,
            bodyOps = pre ++ rest ∧
            run? pre σ = some τ) →
          (∀ j : Fin k,
            FitsSignedWidth
              (ExtReg.width (dst.xslot j))
              (evalRowX (qs := qs) src (τ j) b₀))
          ∧
          (∀ j : Fin k,
            FitsSignedWidth
              (ExtReg.width (dst.zslot j))
              (evalRowZ (qs := qs) src (τ j) b₀))) →
        (∀ {pre rest : Prog k}
          {d s : Fin k}
          {negSrc : Bool}
          {sh : ℕ},
          bodyOps =
              pre ++
                valid_ops.addScaled d s negSrc sh ::
                rest →
          d ≠ s) →
        EncodesStateFromFits
          qs src dst σ b₀ bCur →
        (∀ b' : qs.Basis,
          SameOutsideLayout qs dst bCur b' →
          ∀ i : Fin k,
            RecursiveWorkspaceCleanBasis
              (dst.xslot i)
              (dst.zslot i)
              b') →
        PhaseLoweringReady
          qs
          (planCompileAnnotatedOpsToCSignedGateAux
            (hk := hk)
            (pts := planPts)
            (hpts := hPlanPts)
            (ops := allOps)
            initSize
            ctrl
            phi
            coeff
            dst
            recurse
            (annotatePhaseTermsAux k n bodyOps))
          (qs.ket bCur) := by
  intro σ bodyOps blockPts hB
  induction hB with
  | nil σ σ' tail hNo hrun =>
      intro n hn b₀ bCur hdisjoint hFits hSafeAdd hEnc hcleanOutside
      have hready :=
        planCompileAnnotatedOps_c_ready_append_of_noPhase
          qs hk planPts hPlanPts allOps
          initSize ctrl phi coeff dst recurse
          tail hNo n []
          (qs.ket bCur)
          (by trivial)
      rw [List.append_nil] at hready
      exact hready
  | cons B hrest ih =>
      intro n hn b₀ bCur hdisjoint hFits hSafeAdd hEnc hcleanOutside
      rename_i σ₂ pt pts₂ oprest
      have hlt : n < q k := by
        simp at hn
        omega
      let l : Fin (q k) := ⟨n, hlt⟩
      let theta : ℝ :=
        phi * (((coeff l : ℚ) : ℝ))
      have hnTail :
          n + 1 + pts₂.length = q k := by
        simp at hn
        omega
      have hFitsArith :
          ∀ {τ : State k},
            (∃ pre rest,
              B.arith = pre ++ rest ∧
              run? pre σ₂ = some τ) →
            (∀ j : Fin k,
              FitsSignedWidth
                (ExtReg.width (dst.xslot j))
                (evalRowX
                  (qs := qs) src (τ j) b₀))
            ∧
            (∀ j : Fin k,
              FitsSignedWidth
                (ExtReg.width (dst.zslot j))
                (evalRowZ
                  (qs := qs) src (τ j) b₀)) := by
        intro τ hτ
        rcases hτ with
          ⟨pre, rest, hsplit, hrunPre⟩
        apply hFits
        refine
          ⟨pre,
           rest ++ [.phaseProduct B.i] ++ oprest,
           ?_,
           hrunPre⟩
        simp [
          PhaseBlock.toProg,
          hsplit,
          List.append_assoc
        ]
      have hSafeAddArith :
          ∀ {pre rest : Prog k}
            {d s : Fin k}
            {negSrc : Bool}
            {sh : ℕ},
            B.arith =
                pre ++
                  .addScaled d s negSrc sh ::
                  rest →
            d ≠ s := by
        intro pre rest d s negSrc sh hadd
        exact
          hSafeAdd
            (pre := pre)
            (rest :=
              rest ++
                [.phaseProduct B.i] ++
                oprest)
            (d := d)
            (s := s)
            (negSrc := negSrc)
            (sh := sh)
            (by
              rw [PhaseBlock.toProg]
              simp [hadd, List.append_assoc])
      rcases
          encodesFrom_after_noPhase_run_ket_gen
            (qs := qs)
            (hk := hk)
            (phi := phi)
            (coeff := coeff)
            (src := src)
            (dst := dst)
            (ops := B.arith)
            (σ := σ₂)
            (σ' := B.σmid)
            (bRef := b₀)
            (bCur := bCur)
            (n := n)
            hdisjoint
            hFitsArith
            hSafeAddArith
            B.noPhase_pre
            B.run_pre
            hEnc
        with ⟨bMid, hArithEval, hArithEnc⟩
      rcases
          sameOutside_after_noPhase_run_ket_gen
            (qs := qs)
            (hk := hk)
            (phi := phi)
            (coeff := coeff)
            (src := src)
            (dst := dst)
            (ops := B.arith)
            (σ := σ₂)
            (σ' := B.σmid)
            (bRef := b₀)
            (bCur := bCur)
            (n := n)
            hdisjoint
            hFitsArith
            hSafeAddArith
            B.noPhase_pre
            B.run_pre
            hEnc
        with ⟨bMid', hArithEval', hArithSO'⟩
      have hbMid : bMid' = bMid := by
        apply qs.ket_inj
        rw [← hArithEval, ← hArithEval']
      subst bMid'
      have hArithSO :
          SameOutsideLayout
            qs dst bCur bMid := hArithSO'
      have hSlotClean :
          RecursiveWorkspaceCleanBasis
            (dst.xslot B.i)
            (dst.zslot B.i)
            bMid := by
        exact
          hcleanOutside
            bMid
            hArithSO
            B.i
      have hLeafReady :
          PhaseLoweringReady
            qs
            (recurse B.i theta)
            (qs.ket bMid) := by
        exact
          hleaf
            B.i
            theta
            bMid
            hSlotClean
      have hRunBlock :
          run? B.toProg σ₂ =
            some B.σmid := by
        simp [
          PhaseBlock.toProg,
          run?_append,
          B.run_pre,
          applyOp?
        ]
      have hFitsTail :
          ∀ {τ : State k},
            (∃ pre rest,
              oprest = pre ++ rest ∧
              run? pre B.σmid = some τ) →
            (∀ j : Fin k,
              FitsSignedWidth
                (ExtReg.width (dst.xslot j))
                (evalRowX
                  (qs := qs) src (τ j) b₀))
            ∧
            (∀ j : Fin k,
              FitsSignedWidth
                (ExtReg.width (dst.zslot j))
                (evalRowZ
                  (qs := qs) src (τ j) b₀)) := by
        intro τ hτ
        rcases hτ with
          ⟨pre, rest, hsplit, hrunPre⟩
        apply hFits
        refine
          ⟨B.toProg ++ pre,
           rest,
           ?_,
           ?_⟩
        · simp [hsplit, List.append_assoc]
        · rw [run?_append, hRunBlock]
          simpa using hrunPre
      have hSafeAddTail :
          ∀ {pre rest : Prog k}
            {d s : Fin k}
            {negSrc : Bool}
            {sh : ℕ},
            oprest =
                pre ++
                  .addScaled d s negSrc sh ::
                  rest →
            d ≠ s := by
        intro pre rest d s negSrc sh hadd
        exact
          hSafeAdd
            (pre := B.toProg ++ pre)
            (rest := rest)
            (d := d)
            (s := s)
            (negSrc := negSrc)
            (sh := sh)
            (by simp [hadd, List.append_assoc])
      have hCleanTail :
          ∀ b' : qs.Basis,
            SameOutsideLayout
                qs dst bMid b' →
            ∀ i : Fin k,
              RecursiveWorkspaceCleanBasis
                (dst.xslot i)
                (dst.zslot i)
                b' := by
        intro b' hSO i
        exact
          hcleanOutside
            b'
            (SameOutsideLayout.trans
              (qs := qs)
              hArithSO
              hSO)
            i
      have hTailReady :
          PhaseLoweringReady
            qs
            (planCompileAnnotatedOpsToCSignedGateAux
              (hk := hk)
              (pts := planPts)
              (hpts := hPlanPts)
              (ops := allOps)
              initSize
              ctrl
              phi
              coeff
              dst
              recurse
              (annotatePhaseTermsAux
                k (n + 1) oprest))
            (qs.ket bMid) := by
        exact
          ih
            (n + 1)
            hnTail
            b₀
            bMid
            hdisjoint
            hFitsTail
            hSafeAddTail
            hArithEnc
            hCleanTail
      have hLeafEval :
          LowerGateClass.evalL
              (qs := qs)
              (lowerGateRec
                (recurse B.i theta))
              (qs.ket bMid)
            =
          qs.eval
              (Gate.CSignedPhaseProd
                ctrl
                theta
                (dst.xslot B.i)
                (dst.zslot B.i))
              (qs.ket bMid) := by
        exact
          evalL_lowerGateRec_correct
            (qs := qs)
            (hInterp := hInterp)
            (hC := hC)
            (hRun := hRun)
            (recurse B.i theta)
            (qs.ket bMid)
            hLeafReady
      have hTailAfterLeaf :
          PhaseLoweringReady
            qs
            (planCompileAnnotatedOpsToCSignedGateAux
              (hk := hk)
              (pts := planPts)
              (hpts := hPlanPts)
              (ops := allOps)
              initSize
              ctrl
              phi
              coeff
              dst
              recurse
              (annotatePhaseTermsAux
                k (n + 1) oprest))
            (LowerGateClass.evalL
              (qs := qs)
              (lowerGateRec
                (recurse B.i theta))
              (qs.ket bMid)) := by
        rw [hLeafEval, PhaseSemantics.eval_CSignedPhaseProd_ket]
        by_cases hc : RegEncoding.bit ctrl bMid
        · simp [hc]
          exact PhaseLoweringReady.smul qs _ _ hTailReady
        · simp [hc]
          exact hTailReady
      have hPhaseTail :
          PhaseLoweringReady
            qs
            (planCompileAnnotatedOpsToCSignedGateAux
              (hk := hk)
              (pts := planPts)
              (hpts := hPlanPts)
              (ops := allOps)
              initSize
              ctrl
              phi
              coeff
              dst
              recurse
              ({
                op := .phaseProduct B.i
                phaseTerm? := some l
              } ::
              annotatePhaseTermsAux
                k (n + 1) oprest))
            (qs.ket bMid) := by
        change
          PhaseLoweringReady
              qs
              (recurse B.i theta)
              (qs.ket bMid)
          ∧
          PhaseLoweringReady
              qs
              (planCompileAnnotatedOpsToCSignedGateAux
                (hk := hk)
                (pts := planPts)
                (hpts := hPlanPts)
                (ops := allOps)
                initSize
                ctrl
                phi
                coeff
                dst
                recurse
                (annotatePhaseTermsAux
                  k (n + 1) oprest))
              (LowerGateClass.evalL
                (qs := qs)
                (lowerGateRec
                  (recurse B.i theta))
                (qs.ket bMid))
        exact ⟨hLeafReady, hTailAfterLeaf⟩
      have hAfterArith :
          PhaseLoweringReady
            qs
            (planCompileAnnotatedOpsToCSignedGateAux
              (hk := hk)
              (pts := planPts)
              (hpts := hPlanPts)
              (ops := allOps)
              initSize
              ctrl
              phi
              coeff
              dst
              recurse
              ({
                op := .phaseProduct B.i
                phaseTerm? := some l
              } ::
              annotatePhaseTermsAux
                k (n + 1) oprest))
            (qs.eval
              (compileAnnotatedOpsToSignedGateAux
                k hk phi coeff dst
                (annotatePhaseTermsAux
                  k n B.arith))
              (qs.ket bCur)) := by
        rw [hArithEval]
        exact hPhaseTail
      have hReadyCombined :
          PhaseLoweringReady
            qs
            (planCompileAnnotatedOpsToCSignedGateAux
              (hk := hk)
              (pts := planPts)
              (hpts := hPlanPts)
              (ops := allOps)
              initSize
              ctrl
              phi
              coeff
              dst
              recurse
              (annotatePhaseTermsAux
                  k n B.arith ++
                ({
                  op := .phaseProduct B.i
                  phaseTerm? := some l
                } ::
                annotatePhaseTermsAux
                  k (n + 1) oprest)))
            (qs.ket bCur) := by
        exact
          planCompileAnnotatedOps_c_ready_append_of_noPhase
            qs hk planPts hPlanPts allOps
            initSize ctrl phi coeff dst recurse
            B.arith
            B.noPhase_pre
            n
            ({
              op := .phaseProduct B.i
              phaseTerm? := some l
            } ::
            annotatePhaseTermsAux
              k (n + 1) oprest)
            (qs.ket bCur)
            hAfterArith
      have hCount :
          phaseProductCount B.toProg = 1 := by
        rw [PhaseBlock.toProg, phaseProductCount_append]
        simp [
          phaseProductCount_eq_zero_of_NoPhase,
          B.noPhase_pre,
          phaseProductCount
        ]
      have hAnnAll :
          annotatePhaseTermsAux
              k n (B.toProg ++ oprest)
            =
          annotatePhaseTermsAux k n B.toProg ++
            annotatePhaseTermsAux
              k (n + 1) oprest := by
        rw [annotatePhaseTermsAux_append]
        simp [hCount]
      have hAnnBlock :
          annotatePhaseTermsAux k n B.toProg
            =
          annotatePhaseTermsAux k n B.arith ++
            [{
              op := .phaseProduct B.i
              phaseTerm? := some l
            }] := by
        rw [
          PhaseBlock.toProg,
          annotatePhaseTermsAux_append
        ]
        simp [
          annotatePhaseTermsAux,
          l,
          hlt,
          phaseProductCount_eq_zero_of_NoPhase,
          B.noPhase_pre
        ]
      rw [hAnnAll, hAnnBlock]
      have hList :
          (annotatePhaseTermsAux k n B.arith ++
              [{
                op := .phaseProduct B.i
                phaseTerm? := some l
              }]) ++
            annotatePhaseTermsAux k (n + 1) oprest
          =
          annotatePhaseTermsAux k n B.arith ++
            ({
              op := .phaseProduct B.i
              phaseTerm? := some l
            } ::
            annotatePhaseTermsAux k (n + 1) oprest) := by
        rw [List.append_assoc]
        rfl
      rw [hList]
      exact hReadyCombined


/-! =========================================================
    Allocation And Deallocation Readiness
    Allocation and deallocation chunks compile to primitive low gates, so their
    readiness proofs mostly transport across definitional equalities exposed by
    the plan constructors.
========================================================= -/

/-- Transport readiness across an equality of high-level gates in a plan type. -/
lemma PhaseLoweringReady.cast_gate_mpr
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    [GateSemanticsFacts qs]
    {k : ℕ}
    {hk : 1 < k}
    {pts : List Point}
    {hpts : pts.length = q k}
    {ops : Prog k}
    {initSize : ℕ}
    {U V : Gate}
    (h : V = U)
    (plan :
      PhaseLoweringPlan
        k hk pts hpts ops initSize U)
    {ψ : qs.State}
    (hready :
      PhaseLoweringReady qs plan ψ) :
    PhaseLoweringReady qs
      (Eq.mpr
        (congrArg
          (PhaseLoweringPlan
            k hk pts hpts ops initSize)
          h)
        plan)
      ψ := by
  subst V
  exact hready

/-- Allocation chunk plans are always ready because they contain only primitive low gates. -/
lemma planAllocChunkGate_ready
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    [GateSemanticsFacts qs]
    {k : ℕ}
    {hk : 1 < k}
    {pts : List Point}
    {hpts : pts.length = q k}
    {ops : Prog k}
    (initSize : ℕ)
    (i : Fin k)
    (src dst : ExtReg)
    (ψ : qs.State) :
    PhaseLoweringReady qs
      (planAllocChunkGate
        (hk := hk)
        (pts := pts)
        (hpts := hpts)
        (ops := ops)
        initSize i src dst)
      ψ := by
  by_cases hzero : extraDelta src dst = 0
  · have hdecZero :
        instDecidableEqNat (extraDelta src dst) 0 =
          Decidable.isTrue hzero :=
      Subsingleton.elim _ _
    unfold planAllocChunkGate
    simp only [hdecZero]
    dsimp only [_root_.id]
    apply PhaseLoweringReady.cast_gate_mpr
    all_goals
      simp [allocChunkGate, hzero, PhaseLoweringReady]
  · by_cases htop : isTopChunk i
    · have hdecZero :
          instDecidableEqNat (extraDelta src dst) 0 =
            Decidable.isFalse hzero :=
        Subsingleton.elim _ _
      have hdecTop :
          instDecidableIsTopChunk i =
            Decidable.isTrue htop :=
        Subsingleton.elim _ _
      unfold planAllocChunkGate
      simp only [hdecZero, hdecTop]
      dsimp only [_root_.id]
      apply PhaseLoweringReady.cast_gate_mpr
      all_goals
        first
        | apply PhaseLoweringReady.cast_gate_mpr
        | simp [
            allocChunkGate,
            hzero,
            htop]
      all_goals
        simp [htop, PhaseLoweringReady]
    · have hdecZero :
          instDecidableEqNat (extraDelta src dst) 0 =
            Decidable.isFalse hzero :=
        Subsingleton.elim _ _
      have hdecTop :
          instDecidableIsTopChunk i =
            Decidable.isFalse htop :=
        Subsingleton.elim _ _
      unfold planAllocChunkGate
      simp only [hdecZero, hdecTop]
      dsimp only [_root_.id]
      apply PhaseLoweringReady.cast_gate_mpr
      all_goals
        first
        | apply PhaseLoweringReady.cast_gate_mpr
        | simp [
            allocChunkGate,
            hzero,
            htop]
      all_goals
        simp [htop, PhaseLoweringReady]

/-- Auxiliary allocation plans are ready for every starting state. -/
lemma planCompileSignedAllocationsAux_ready
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    [GateSemanticsFacts qs]
    {k : ℕ}
    {hk : 1 < k}
    {pts : List Point}
    {hpts : pts.length = q k}
    {ops : Prog k}
    (initSize : ℕ)
    (src dst : LayoutState k) :
    ∀ n hn ψ,
      PhaseLoweringReady qs
        (planCompileSignedAllocationsAux
          (hk := hk)
          (pts := pts)
          (hpts := hpts)
          (ops := ops)
          initSize src dst n hn)
        ψ := by
  intro n
  induction n with
  | zero =>
      intro hn ψ
      trivial
  | succ n ih =>
      intro hn ψ
      dsimp only [planCompileSignedAllocationsAux]
      refine ⟨?_, ?_, ?_⟩
      · exact ih _ _
      · apply planAllocChunkGate_ready
      · apply planAllocChunkGate_ready

/-- Full signed-allocation plans are ready for every starting state. -/
lemma planCompileSignedAllocations_ready
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    [GateSemanticsFacts qs]
    {k : ℕ}
    (hk : 1 < k)
    (pts : List Point)
    (hpts : pts.length = q k)
    (ops : Prog k)
    (initSize : ℕ)
    (src dst : LayoutState k)
    (ψ : qs.State) :
    PhaseLoweringReady qs
      (planCompileSignedAllocations
        (hk := hk)
        (pts := pts)
        (hpts := hpts)
        (ops := ops)
        initSize src dst)
      ψ := by
  unfold planCompileSignedAllocations
  exact
    planCompileSignedAllocationsAux_ready
      qs initSize src dst k le_rfl ψ

/-- Deallocation chunk plans are always ready because they contain only primitive low gates. -/
lemma planDeallocChunkGate_ready
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    [GateSemanticsFacts qs]
    {k : ℕ}
    {hk : 1 < k}
    {pts : List Point}
    {hpts : pts.length = q k}
    {ops : Prog k}
    (initSize : ℕ)
    (i : Fin k)
    (src dst : ExtReg)
    (ψ : qs.State) :
    PhaseLoweringReady qs
      (planDeallocChunkGate
        (hk := hk)
        (pts := pts)
        (hpts := hpts)
        (ops := ops)
        initSize i src dst)
      ψ := by
  by_cases hzero : extraDelta src dst = 0
  · have hdecZero :
        instDecidableEqNat (extraDelta src dst) 0 =
          Decidable.isTrue hzero :=
      Subsingleton.elim _ _
    unfold planDeallocChunkGate
    simp only [hdecZero]
    dsimp only [_root_.id]
    apply PhaseLoweringReady.cast_gate_mpr
    all_goals
      simp [deallocChunkGate, hzero, PhaseLoweringReady]
  · by_cases htop : isTopChunk i
    · have hdecZero :
          instDecidableEqNat (extraDelta src dst) 0 =
            Decidable.isFalse hzero :=
        Subsingleton.elim _ _
      have hdecTop :
          instDecidableIsTopChunk i =
            Decidable.isTrue htop :=
        Subsingleton.elim _ _
      unfold planDeallocChunkGate
      simp only [hdecZero, hdecTop]
      dsimp only [_root_.id]
      apply PhaseLoweringReady.cast_gate_mpr
      all_goals
        first
        | apply PhaseLoweringReady.cast_gate_mpr
        | simp [
            deallocChunkGate,
            hzero,
            htop
          ]
      all_goals
        simp [htop, PhaseLoweringReady]
    · have hdecZero :
          instDecidableEqNat (extraDelta src dst) 0 =
            Decidable.isFalse hzero :=
        Subsingleton.elim _ _
      have hdecTop :
          instDecidableIsTopChunk i =
            Decidable.isFalse htop :=
        Subsingleton.elim _ _
      unfold planDeallocChunkGate
      simp only [hdecZero, hdecTop]
      dsimp only [_root_.id]
      apply PhaseLoweringReady.cast_gate_mpr
      all_goals
        first
        | apply PhaseLoweringReady.cast_gate_mpr
        | simp [
            deallocChunkGate,
            hzero,
            htop
          ]
      all_goals
        simp [htop, PhaseLoweringReady]

/-- Auxiliary deallocation plans are ready for every starting state. -/
lemma planCompileSignedDeallocationsAux_ready
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    [GateSemanticsFacts qs]
    {k : ℕ}
    {hk : 1 < k}
    {pts : List Point}
    {hpts : pts.length = q k}
    {ops : Prog k}
    (initSize : ℕ)
    (src dst : LayoutState k) :
    ∀ n hn ψ,
      PhaseLoweringReady qs
        (planCompileSignedDeallocationsAux
          (hk := hk)
          (pts := pts)
          (hpts := hpts)
          (ops := ops)
          initSize src dst n hn)
        ψ := by
  intro n
  induction n with
  | zero =>
      intro hn ψ
      trivial
  | succ n ih =>
      intro hn ψ
      dsimp only [planCompileSignedDeallocationsAux]
      refine ⟨?_, ?_, ?_⟩
      · apply planDeallocChunkGate_ready
      · apply planDeallocChunkGate_ready
      · exact ih _ _

/-- Full signed-deallocation plans are ready for every starting state. -/
lemma planCompileSignedDeallocations_ready
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    [GateSemanticsFacts qs]
    {k : ℕ}
    (hk : 1 < k)
    (pts : List Point)
    (hpts : pts.length = q k)
    (ops : Prog k)
    (initSize : ℕ)
    (src dst : LayoutState k)
    (ψ : qs.State) :
    PhaseLoweringReady qs
      (planCompileSignedDeallocations
        (hk := hk)
        (pts := pts)
        (hpts := hpts)
        (ops := ops)
        initSize src dst)
      ψ := by
  unfold planCompileSignedDeallocations
  exact
    planCompileSignedDeallocationsAux_ready
      qs initSize src dst k le_rfl ψ

/-! =========================================================
    Recursive Signed Phase-Product Readiness
    These lemmas assemble allocation, body readiness, recursive child readiness,
    and deallocation into readiness for the canonical signed phase-product
    lowering plan. The basis-ket proof is extended to arbitrary clean states by
    linearity.
========================================================= -/

/-- Readiness of the compiled signed phase-product plan on a clean basis ket. -/
lemma planCompiledSignedPhaseGate_ready_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGatePrimitiveBridge qs]
    {k : ℕ}
    (hk : 1 < k)
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
      run? ops State.start_state =
        some State.start_state)
    (phi : ℝ)
    (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z k)
    (hcapacity :
      (initSignedLayoutState layout).CanGrowToNeeds
        (scanNeededWidths x z ops))
    (recurse :
      let src := initSignedLayoutState layout
      let dst :=
        targetSignedLayoutState src
          (scanNeededWidths x z ops)
      ∀ i theta,
        PhaseLoweringPlan
          k hk pts hpts ops
          (nextSignedWidth x z ops)
          (Gate.SignedPhaseProd
            theta
            (dst.xslot i)
            (dst.zslot i)))
    (hleaf :
      let src := initSignedLayoutState layout
      let dst :=
        targetSignedLayoutState src
          (scanNeededWidths x z ops)
      ∀ i theta b',
        RecursiveWorkspaceCleanBasis
            (dst.xslot i) (dst.zslot i) b' →
        PhaseLoweringReady
          qs (recurse i theta) (qs.ket b'))
    (b : qs.Basis)
    (hclean : RecursiveWorkspaceCleanBasis x z b) :
    PhaseLoweringReady
      qs
      (planCompiledSignedPhaseGate
        hk pts hpts ops phi x z layout recurse)
      (qs.ket b) := by
  let need : NeededWidths k :=
    scanNeededWidths x z ops
  let src : LayoutState k :=
    initSignedLayoutState layout
  let dst : LayoutState k :=
    targetSignedLayoutState src need
  let coeff : Fin (q k) → ℚ :=
    loweringPhaseCoeff k x z pts hpts
  let annOps :=
    annotatePhaseTermsAux k 0 ops
  let allocPlan :=
    planCompileSignedAllocations
      (hk := hk) (pts := pts) (hpts := hpts) (ops := ops)
      (nextSignedWidth x z ops) src dst
  let bodyPlan :=
    planCompileAnnotatedOpsToSignedGateAux
      (hk := hk) (pts := pts) (hpts := hpts) (ops := ops)
      (nextSignedWidth x z ops)
      phi coeff dst recurse annOps
  let deallocPlan :=
    planCompileSignedDeallocations
      (hk := hk) (pts := pts) (hpts := hpts) (ops := ops)
      (nextSignedWidth x z ops) src dst
  have hworkspace :
      CompilerWorkspaceOK src need b := by
    simpa [src, need] using
      compilerWorkspaceOK_of_recursiveWorkspaceCleanBasis ops x z layout hcapacity b hclean
  rcases
      eval_compileSignedAllocations_ket_fits_and_child_clean
        qs ops x z layout b hworkspace hclean
    with ⟨bAlloc, hAllocEval, hEncAlloc, hAllocClean⟩
  have hFits :
      ∀ {τ : State k},
        (∃ pre rest,
          ops = pre ++ rest ∧
          run? pre State.start_state = some τ) →
        (∀ j : Fin k,
          FitsSignedWidth
            (ExtReg.width (dst.xslot j))
            (evalRowX
              (qs := qs) src (τ j) b))
        ∧
        (∀ j : Fin k,
          FitsSignedWidth
            (ExtReg.width (dst.zslot j))
            (evalRowZ
              (qs := qs) src (τ j) b)) := by
    intro τ hτ
    simpa [src, dst, need] using
      allocated_widths_sound
        (qs := qs)
        layout
        ops
        hcapacity
        b
        (σ := τ)
        hτ
  have hdisjoint : LayoutSlotsDisjoint dst := by
    simpa [src, dst, need] using
      targetSignedLayoutState_owned_disjoint layout need
  have hblocks :
      BlockDecomposition
        (k := k)
        (by omega)
        State.start_state
        ops
        pts :=
    progConsumesPts_has_blockDecomposition
      (k := k)
      (by omega)
      ops
      State.start_state
      pts
      hC.1
  have hBodyReady :
      PhaseLoweringReady qs bodyPlan (qs.ket bAlloc) := by
    apply
      planCompileAnnotatedOps_ready_ket_of_blocks_from
        qs hk pts hpts hInterp
        ops hC hRun
        (nextSignedWidth x z ops)
        phi coeff src dst recurse hleaf
        hblocks
        0
        (by simpa using hpts)
        b
        bAlloc
        hdisjoint
        hFits
        hC.2
        hEncAlloc
    exact hAllocClean
  have hAllocReady :
      PhaseLoweringReady qs allocPlan (qs.ket b) :=
    planCompileSignedAllocations_ready
      qs hk pts hpts ops
      (nextSignedWidth x z ops)
      src dst
      (qs.ket b)
  have hLowAlloc :
      LowerGateClass.evalL
          (qs := qs)
          (lowerGateRec allocPlan)
          (qs.ket b)
        =
      qs.ket bAlloc := by
    calc
      LowerGateClass.evalL
          (qs := qs)
          (lowerGateRec allocPlan)
          (qs.ket b)
          =
        qs.eval
          (compileSignedAllocations k src dst)
          (qs.ket b) := by
            exact
              evalL_lowerGateRec_correct
                (qs := qs)
                (hInterp := hInterp)
                (hC := hC)
                (hRun := hRun)
                allocPlan
                (qs.ket b)
                hAllocReady
      _ = qs.ket bAlloc := hAllocEval
  have hDeallocReady :
      PhaseLoweringReady
        qs
        deallocPlan
        (LowerGateClass.evalL
          (qs := qs)
          (lowerGateRec bodyPlan)
          (qs.ket bAlloc)) :=
    planCompileSignedDeallocations_ready
      qs hk pts hpts ops
      (nextSignedWidth x z ops)
      src dst
      _
  unfold planCompiledSignedPhaseGate
  dsimp only
  refine ⟨hAllocReady, ?_⟩
  rw [hLowAlloc]
  exact ⟨hBodyReady, hDeallocReady⟩

/-- The canonical standard plan is ready on a basis ket with clean recursive workspace. -/
lemma standardSignedPhaseLoweringPlan_ready_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGatePrimitiveBridge qs]
    (k : ℕ)
    (hk : 1 < k)
    (phi : ℝ)
    (x z : ExtReg)
    (ops : Prog k)
    (b : qs.Basis)
    (hstatic :
      SignedRecursiveWorkspaceOK ops x z)
    (hclean :
      RecursiveWorkspaceCleanBasis x z b)
    (hC :
      ProgConsumesPtsSafe
        (k := k)
        (by omega)
        State.start_state
        ops
        (genInterpolationPoints k))
    (hRun :
      run? ops State.start_state =
        some State.start_state) :
    PhaseLoweringReady
      qs
      (standardSignedPhaseLoweringPlan
        k hk phi x z ops hstatic)
      (qs.ket b) := by
  rw [standardSignedPhaseLoweringPlan]
  split
  next hrec =>
    let step : CanonicalSignedStep ops x z :=
      canonicalSignedStep
        hk ops x z hrec hstatic
    let src : LayoutState k :=
      initSignedLayoutState step.layout
    let dst : LayoutState k :=
      targetSignedLayoutState
        src
        (scanNeededWidths x z ops)
    have hcurrent :
        CleanWorkspaceState
          qs
          (initSignedLayoutState step.layout)
          (scanNeededWidths x z ops)
          (qs.ket b) :=
      cleanWorkspaceState_ket_of_recursiveWorkspaceCleanBasis
        qs
        ops
        x
        z
        step.layout
        step.capacity
        b
        hclean
    dsimp only
    refine And.intro hcurrent ?_
    apply
      planCompiledSignedPhaseGate_ready_ket
        (qs := qs)
        (hk := hk)
        (pts := genInterpolationPoints k)
        (hpts :=
          generatedInterpolationPoints_length k)
        (hInterp := by
          simpa using genInterpolationPoints_good k)
        (ops := ops)
        (hC := hC)
        (hRun := hRun)
        (phi := phi)
        (x := x)
        (z := z)
        (layout := step.layout)
        (hcapacity := step.capacity)
        (b := b)
        (hclean := hclean)
    dsimp only
    intro i theta b' hclean'
    have hchild :
        SignedRecursiveWorkspaceOK
          ops
          (dst.xslot i)
          (dst.zslot i) := by
      simpa [src, dst] using
        step.childWorkspace i
    have hsize :
        phaseInputSize
            (dst.xslot i)
            (dst.zslot i)
          =
        nextSignedWidth x z ops := by
      simpa [src, dst] using
        step.childInputSize i
    have hchildReady :
        PhaseLoweringReady
          qs
          (standardSignedPhaseLoweringPlan
            k
            hk
            theta
            (dst.xslot i)
            (dst.zslot i)
            ops
            hchild)
          (qs.ket b') := by
      exact
        standardSignedPhaseLoweringPlan_ready_ket
          (qs := qs)
          (k := k)
          (hk := hk)
          (phi := theta)
          (x := dst.xslot i)
          (z := dst.zslot i)
          (ops := ops)
          (b := b')
          (hstatic := hchild)
          (hclean := hclean')
          (hC := hC)
          (hRun := hRun)
    dsimp only [id_eq]
    convert hchildReady using 2
    all_goals
      first
        | exact hsize.symm
        | (rw [eq_mp_eq_cast]; exact cast_heq _ _)
  next hstop =>
    exact True.intro
termination_by phaseInputSize x z
decreasing_by
  have hsize :
      phaseInputSize (dst.xslot i) (dst.zslot i) = nextSignedWidth x z ops := by
    simpa [src, dst] using step.childInputSize i
  rw [hsize]
  assumption

/-- The canonical standard plan is ready and preserves recursive cleanliness on any clean state. -/
theorem standardSignedPhaseLoweringPlan_ready_and_clean
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGatePrimitiveBridge qs]
    (k : ℕ)
    (hk : 1 < k)
    (phi : ℝ)
    (x z : ExtReg)
    (ops : Prog k)
    (ψ : qs.State)
    (hstatic :
      SignedRecursiveWorkspaceOK ops x z)
    (hclean :
      RecursiveWorkspaceCleanState qs x z ψ)
    (hC :
      ProgConsumesPtsSafe
        (k := k)
        (by omega)
        State.start_state
        ops
        (genInterpolationPoints k))
    (hRun :
      run? ops State.start_state =
        some State.start_state) :
    let plan :=
      standardSignedPhaseLoweringPlan
        k hk phi x z ops hstatic
    PhaseLoweringReady qs plan ψ
      ∧
    RecursiveWorkspaceCleanState
      qs x z
      (LowerGateClass.evalL
        (qs := qs)
        (lowerGateRec plan)
        ψ) := by
  dsimp only
  let plan :=
    standardSignedPhaseLoweringPlan
      k hk phi x z ops hstatic
  have hready :
      PhaseLoweringReady qs plan ψ := by
    induction hclean with
    | zero =>
        exact
          PhaseLoweringReady.zero
            qs plan
    | ket b hcleanBasis =>
        exact
          standardSignedPhaseLoweringPlan_ready_ket
            qs
            k
            hk
            phi
            x
            z
            ops
            b
            hstatic
            hcleanBasis
            hC
            hRun
    | add hψ hφ ihψ ihφ =>
        exact
          PhaseLoweringReady.add
            qs plan ihψ ihφ
    | smul a hψ ihψ =>
        exact
          PhaseLoweringReady.smul
            qs plan a ihψ
  constructor
  · exact hready
  · exact
      standardSignedPhaseLoweringPlan_preserves_clean_of_ready
        qs
        k
        hk
        phi
        x
        z
        ops
        ψ
        hstatic
        hclean
        hready
        hC
        hRun

/-- Readiness projection from the ready-and-clean theorem. -/
theorem standardSignedPhaseLoweringPlan_ready
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGatePrimitiveBridge qs]
    (k : ℕ)
    (hk : 1 < k)
    (phi : ℝ)
    (x z : ExtReg)
    (ops : Prog k)
    (ψ : qs.State)
    (hstatic : SignedRecursiveWorkspaceOK ops x z)
    (hclean : RecursiveWorkspaceCleanState qs x z ψ)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops (genInterpolationPoints k))
    (hRun : run? ops State.start_state = some State.start_state) :
    PhaseLoweringReady qs (standardSignedPhaseLoweringPlan k hk phi x z ops hstatic) ψ := by
  exact
    (standardSignedPhaseLoweringPlan_ready_and_clean qs k hk phi x z ops ψ
      hstatic
      hclean
      hC
      hRun).1

/-- Public workspace-state invariant implies readiness for the canonical standard plan. -/
lemma standardSignedPhaseLoweringPlan_ready_of_workspace
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGatePrimitiveBridge qs]
    (k : ℕ)
    (hk : 1 < k)
    (phi : ℝ)
    (x z : ExtReg)
    (ops : Prog k)
    (ψ : qs.State)
    (hworkspace : SignedRecursiveWorkspaceStateOK qs ops x z ψ)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops (genInterpolationPoints k))
    (hRun : run? ops State.start_state = some State.start_state):
    PhaseLoweringReady qs (standardSignedPhaseLoweringPlan k hk phi x z ops hworkspace.static) ψ := by
  exact
    standardSignedPhaseLoweringPlan_ready qs k hk phi x z ops ψ
      hworkspace.static hworkspace.clean hC hRun


/-- Readiness of the compiled controlled signed phase-product plan on a clean basis ket. -/
lemma planCompiledCSignedPhaseGate_ready_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGatePrimitiveBridge qs]
    {k : ℕ}
    (hk : 1 < k)
    (pts : List Point)
    (hpts : pts.length = q k)
    (hInterp : GoodToomCookPoints k pts hpts)
    (ops : Prog k)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops pts)
    (hRun : run? ops State.start_state = some State.start_state)
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z k)
    (hcapacity : (initSignedLayoutState layout).CanGrowToNeeds (scanNeededWidths x z ops))
    (recurse :
      let src := initSignedLayoutState layout
      let dst := targetSignedLayoutState src (scanNeededWidths x z ops)
      ∀ i theta,
        PhaseLoweringPlan k hk pts hpts ops (nextSignedWidth x z ops)
          (Gate.CSignedPhaseProd ctrl theta (dst.xslot i) (dst.zslot i)))
    (hleaf :
      let src := initSignedLayoutState layout
      let dst := targetSignedLayoutState src (scanNeededWidths x z ops)
      ∀ i theta b',
        RecursiveWorkspaceCleanBasis (dst.xslot i) (dst.zslot i) b' →
        PhaseLoweringReady qs (recurse i theta) (qs.ket b'))
    (b : qs.Basis)
    (hclean : RecursiveWorkspaceCleanBasis x z b) :
    PhaseLoweringReady qs
      (planCompiledCSignedPhaseGate hk pts hpts ops ctrl phi x z layout recurse)
      (qs.ket b) := by
  let need : NeededWidths k := scanNeededWidths x z ops
  let src : LayoutState k := initSignedLayoutState layout
  let dst : LayoutState k := targetSignedLayoutState src need
  let coeff : Fin (q k) → ℚ := loweringPhaseCoeff k x z pts hpts
  let annOps := annotatePhaseTermsAux k 0 ops
  let allocPlan :=
    planCompileSignedAllocations
      (hk := hk) (pts := pts) (hpts := hpts) (ops := ops)
      (nextSignedWidth x z ops) src dst
  let bodyPlan :=
    planCompileAnnotatedOpsToCSignedGateAux
      (hk := hk) (pts := pts) (hpts := hpts) (ops := ops)
      (nextSignedWidth x z ops) ctrl phi coeff dst recurse annOps
  let deallocPlan :=
    planCompileSignedDeallocations
      (hk := hk) (pts := pts) (hpts := hpts) (ops := ops)
      (nextSignedWidth x z ops) src dst
  have hworkspace : CompilerWorkspaceOK src need b := by
    simpa [src, need] using
      compilerWorkspaceOK_of_recursiveWorkspaceCleanBasis ops x z layout hcapacity b hclean
  rcases eval_compileSignedAllocations_ket_fits_and_child_clean
        qs ops x z layout b hworkspace hclean with
    ⟨bAlloc, hAllocEval, hEncAlloc, hAllocClean⟩
  have hFits :
      ∀ {τ : State k},
        (∃ pre rest, ops = pre ++ rest ∧ run? pre State.start_state = some τ) →
        (∀ j : Fin k, FitsSignedWidth (ExtReg.width (dst.xslot j))
          (evalRowX (qs := qs) src (τ j) b)) ∧
        (∀ j : Fin k, FitsSignedWidth (ExtReg.width (dst.zslot j))
          (evalRowZ (qs := qs) src (τ j) b)) := by
    intro τ hτ
    simpa [src, dst, need] using
      allocated_widths_sound (qs := qs) layout ops hcapacity b (σ := τ) hτ
  have hdisjoint : LayoutSlotsDisjoint dst := by
    simpa [src, dst, need] using targetSignedLayoutState_owned_disjoint layout need
  have hblocks : BlockDecomposition (k := k) (by omega) State.start_state ops pts :=
    progConsumesPts_has_blockDecomposition (k := k) (by omega) ops State.start_state pts hC.1
  have hBodyReady : PhaseLoweringReady qs bodyPlan (qs.ket bAlloc) := by
    apply
      planCompileAnnotatedOps_c_ready_ket_of_blocks_from
        qs hk pts hpts hInterp ops hC hRun
        (nextSignedWidth x z ops) ctrl phi coeff src dst recurse hleaf
        hblocks 0 (by simpa using hpts) b bAlloc hdisjoint hFits hC.2 hEncAlloc
    exact hAllocClean
  have hAllocReady : PhaseLoweringReady qs allocPlan (qs.ket b) :=
    planCompileSignedAllocations_ready qs hk pts hpts ops (nextSignedWidth x z ops) src dst (qs.ket b)
  have hLowAlloc :
      LowerGateClass.evalL (qs := qs) (lowerGateRec allocPlan) (qs.ket b) = qs.ket bAlloc := by
    calc
      LowerGateClass.evalL (qs := qs) (lowerGateRec allocPlan) (qs.ket b)
          = qs.eval (compileSignedAllocations k src dst) (qs.ket b) := by
            exact evalL_lowerGateRec_correct (qs := qs) (hInterp := hInterp)
              (hC := hC) (hRun := hRun) allocPlan (qs.ket b) hAllocReady
      _ = qs.ket bAlloc := hAllocEval
  have hDeallocReady :
      PhaseLoweringReady qs deallocPlan
        (LowerGateClass.evalL (qs := qs) (lowerGateRec bodyPlan) (qs.ket bAlloc)) :=
    planCompileSignedDeallocations_ready qs hk pts hpts ops (nextSignedWidth x z ops) src dst _
  have hCompleteReady :
      PhaseLoweringReady qs (PhaseLoweringPlan.seq allocPlan (PhaseLoweringPlan.seq bodyPlan deallocPlan))
        (qs.ket b) := by
    refine ⟨hAllocReady, ?_⟩
    rw [hLowAlloc]
    exact ⟨hBodyReady, hDeallocReady⟩
  unfold planCompiledCSignedPhaseGate
  dsimp only
  exact
    PhaseLoweringReady.cast_gate_mpr
      qs
      (by
        simp [compiledCSignedPhaseGate, compileOpsToCSignedGate, compileOpsToSignedGate,
          controlPhaseLeaves, controlPhaseLeaves_compileSignedAllocations,
          controlPhaseLeaves_compileSignedDeallocations])
      _
      hCompleteReady

/-- The canonical controlled standard plan is ready on a basis ket with clean recursive workspace. -/
lemma standardCSignedPhaseLoweringPlan_ready_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGatePrimitiveBridge qs]
    (k : ℕ)
    (hk : 1 < k)
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : ExtReg)
    (ops : Prog k)
    (b : qs.Basis)
    (hstatic : CSignedRecursiveWorkspaceOK ops ctrl x z)
    (hclean : RecursiveWorkspaceCleanBasis x z b)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops (genInterpolationPoints k))
    (hRun : run? ops State.start_state = some State.start_state) :
    PhaseLoweringReady qs
      (standardCSignedPhaseLoweringPlan k hk ctrl phi x z ops hstatic)
      (qs.ket b) := by
  rw [standardCSignedPhaseLoweringPlan]
  split
  next hrec =>
    let step : CanonicalSignedStep ops x z :=
      canonicalSignedStep hk ops x z hrec hstatic.toSignedRecursiveWorkspaceOK
    let src : LayoutState k := initSignedLayoutState step.layout
    let dst : LayoutState k := targetSignedLayoutState src (scanNeededWidths x z ops)
    have hcurrent :
        CleanWorkspaceState qs (initSignedLayoutState step.layout)
          (scanNeededWidths x z ops) (qs.ket b) :=
      cleanWorkspaceState_ket_of_recursiveWorkspaceCleanBasis qs ops x z step.layout step.capacity b hclean
    dsimp only
    refine And.intro hcurrent ?_
    apply
      planCompiledCSignedPhaseGate_ready_ket
        (qs := qs)
        (hk := hk)
        (pts := genInterpolationPoints k)
        (hpts := generatedInterpolationPoints_length k)
        (hInterp := by simpa using genInterpolationPoints_good k)
        (ops := ops)
        (hC := hC)
        (hRun := hRun)
        (ctrl := ctrl)
        (phi := phi)
        (x := x)
        (z := z)
        (layout := step.layout)
        (hcapacity := step.capacity)
        (b := b)
        (hclean := hclean)
    dsimp only
    intro i theta b' hclean'
    have hchildSigned : SignedRecursiveWorkspaceOK ops (dst.xslot i) (dst.zslot i) := by
      simpa [src, dst] using step.childWorkspace i
    have hctrlLayout : step.layout.ControlDisjoint ctrl :=
      step.layout.controlDisjoint_of_ctrlDisjoint hstatic.control_disjoint
    have hctrlDst := controlDisjoint_target step.layout ctrl (scanNeededWidths x z ops) hctrlLayout
    have hchild : CSignedRecursiveWorkspaceOK ops ctrl (dst.xslot i) (dst.zslot i) :=
      { toSignedRecursiveWorkspaceOK := hchildSigned
        control_disjoint := by
          constructor
          · exact (by simpa [src, dst] using hctrlDst.1 i)
          · exact (by simpa [src, dst] using hctrlDst.2 i) }
    have hsize : phaseInputSize (dst.xslot i) (dst.zslot i) = nextSignedWidth x z ops := by
      simpa [src, dst] using step.childInputSize i
    have hchildReady :
        PhaseLoweringReady qs
          (standardCSignedPhaseLoweringPlan k hk ctrl theta (dst.xslot i) (dst.zslot i) ops hchild)
          (qs.ket b') := by
      exact standardCSignedPhaseLoweringPlan_ready_ket (qs := qs) (k := k) (hk := hk)
        (ctrl := ctrl) (phi := theta) (x := dst.xslot i) (z := dst.zslot i)
        (ops := ops) (b := b') (hstatic := hchild) (hclean := hclean') (hC := hC) (hRun := hRun)
    dsimp only [id_eq]
    convert hchildReady using 2
    all_goals
      first
        | exact hsize.symm
        | (rw [eq_mp_eq_cast]; exact cast_heq _ _)
  next hstop =>
    exact True.intro
termination_by phaseInputSize x z
decreasing_by
  have hsize : phaseInputSize (dst.xslot i) (dst.zslot i) = nextSignedWidth x z ops := by
    simpa [src, dst] using step.childInputSize i
  rw [hsize]
  assumption

/-- Readiness of the canonical controlled standard plan on any clean state. -/
theorem standardCSignedPhaseLoweringPlan_ready
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGatePrimitiveBridge qs]
    (k : ℕ)
    (hk : 1 < k)
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : ExtReg)
    (ops : Prog k)
    (ψ : qs.State)
    (hstatic : CSignedRecursiveWorkspaceOK ops ctrl x z)
    (hclean : RecursiveWorkspaceCleanState qs x z ψ)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops (genInterpolationPoints k))
    (hRun : run? ops State.start_state = some State.start_state) :
    PhaseLoweringReady qs (standardCSignedPhaseLoweringPlan k hk ctrl phi x z ops hstatic) ψ := by
  induction hclean with
  | zero => exact PhaseLoweringReady.zero qs _
  | ket b hcleanBasis =>
      exact standardCSignedPhaseLoweringPlan_ready_ket qs k hk ctrl phi x z ops b hstatic hcleanBasis hC hRun
  | add hψ hφ ihψ ihφ => exact PhaseLoweringReady.add qs _ ihψ ihφ
  | smul a hψ ihψ => exact PhaseLoweringReady.smul qs _ a ihψ

/-- Public controlled workspace-state invariant implies readiness for the canonical controlled standard plan. -/
lemma standardCSignedPhaseLoweringPlan_ready_of_workspace
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGatePrimitiveBridge qs]
    (k : ℕ)
    (hk : 1 < k)
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : ExtReg)
    (ops : Prog k)
    (ψ : qs.State)
    (hworkspace : CSignedRecursiveWorkspaceStateOK qs ops ctrl x z ψ)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops (genInterpolationPoints k))
    (hRun : run? ops State.start_state = some State.start_state):
    PhaseLoweringReady qs (standardCSignedPhaseLoweringPlan k hk ctrl phi x z ops hworkspace.static) ψ := by
  exact standardCSignedPhaseLoweringPlan_ready qs k hk ctrl phi x z ops ψ
    hworkspace.static hworkspace.clean hC hRun

end Shor
