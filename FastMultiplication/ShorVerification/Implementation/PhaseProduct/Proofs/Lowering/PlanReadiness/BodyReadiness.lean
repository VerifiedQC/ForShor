import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.Lowering.Workspace
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Lowering.PlanBuilders
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Coefficients
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Spec.Readiness
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Spec.Cleanliness
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.Lowering.EvalL
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.Lowering.PlanSemantics
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.Lowering.Linearity
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.Body.NoPhaseRuns

namespace Shor
open Gate
open Operations

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
    (phi : Angle)
    (coeff : Fin (q k) → ℚ)
    (dst : LayoutState k)
    (recurse :
      ∀ (i : Fin k) (theta : Angle),
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
    {k : ℕ}
    (hk : 1 < k)
    (planPts : List Point)
    (hPlanPts : planPts.length = q k)
    (hInterp : GoodToomCookPoints k planPts hPlanPts)
    (allOps : Prog k)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state allOps planPts)
    (hRun : run? allOps State.start_state = some State.start_state)
    (initSize : ℕ)
    (phi : Angle)
    (coeff : Fin (q k) → ℚ)
    (src dst : LayoutState k)
    (recurse :
      ∀ (i : Fin k) (theta : Angle),
        PhaseLoweringPlan k hk planPts hPlanPts allOps initSize
          (Gate.SignedPhaseProd theta (dst.xslot i) (dst.zslot i)))
    (hleaf :
      ∀ (i : Fin k) (theta : Angle) (b' : qs.Basis),
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
      let theta : Angle :=
        phi * coeff l
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
    (phi : Angle)
    (coeff : Fin (q k) → ℚ)
    (dst : LayoutState k)
    (recurse :
      ∀ (i : Fin k) (theta : Angle),
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
    (phi : Angle)
    (coeff : Fin (q k) → ℚ)
    (src dst : LayoutState k)
    (recurse :
      ∀ (i : Fin k) (theta : Angle),
        PhaseLoweringPlan k hk planPts hPlanPts allOps initSize
          (Gate.CSignedPhaseProd ctrl theta (dst.xslot i) (dst.zslot i)))
    (hleaf :
      ∀ (i : Fin k) (theta : Angle) (b' : qs.Basis),
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
      let theta : Angle :=
        phi * coeff l
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



end Shor
