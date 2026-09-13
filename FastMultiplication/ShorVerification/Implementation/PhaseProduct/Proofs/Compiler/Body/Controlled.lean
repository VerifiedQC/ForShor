import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.Body.PhaseBlocks

namespace Shor
open Gate
open Operations
open scoped BigOperators

/-! =========================================================
    Control-Phase Wrappers
    `controlPhaseLeaves` only changes phase-product leaves. These lemmas push it
    through compiled lists and show that purely arithmetic fragments are fixed.
========================================================= -/

/-- `controlPhaseLeaves` respects append decomposition of compiled annotated operations. -/
lemma eval_controlPhaseLeaves_compileAnnotatedOpsToSignedGateAux_append
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [GateSemanticsCore qs]
  {k : ℕ} (hk : 1 < k)
  (ctrl : ℕ)
  (phi : Angle)
  (coeff : Fin (q k) → ℚ)
  (st : LayoutState k)
  (xs ys : List (AnnotatedOp k))
  (ψ : qs.State) :
  qs.eval
      (controlPhaseLeaves ctrl
        (compileAnnotatedOpsToSignedGateAux k hk phi coeff st (xs ++ ys)))
      ψ
    =
  qs.eval
      (controlPhaseLeaves ctrl
        (compileAnnotatedOpsToSignedGateAux k hk phi coeff st ys))
      (qs.eval
        (controlPhaseLeaves ctrl
          (compileAnnotatedOpsToSignedGateAux k hk phi coeff st xs))
        ψ) := by
  induction xs generalizing ψ with
  | nil =>
      simp [compileAnnotatedOpsToSignedGateAux, controlPhaseLeaves, qs.eval_id]
  | cons a xs ih =>
      cases a with
      | mk op term? =>
          cases op <;>
            cases term? <;>
            simp [compileAnnotatedOpsToSignedGateAux, controlPhaseLeaves,
              qs.eval_seq, ih]

/-- Control-phase wrapping is the identity on compiled no-phase fragments. -/
lemma controlPhaseLeaves_compileAnnotatedOpsToSignedGateAux_of_NoPhase
  {k : ℕ} (hk : 1 < k)
  (ctrl : ℕ)
  (phi : Angle)
  (coeff : Fin (q k) → ℚ)
  (st : LayoutState k)
  (ops : Prog k)
  (n : ℕ)
  (hNo : NoPhase ops) :
  controlPhaseLeaves ctrl
      (compileAnnotatedOpsToSignedGateAux k hk phi coeff st
        (annotatePhaseTermsAux k n ops))
    =
  compileAnnotatedOpsToSignedGateAux k hk phi coeff st
    (annotatePhaseTermsAux k n ops) := by
  induction ops generalizing n with
  | nil =>
      simp [annotatePhaseTermsAux, compileAnnotatedOpsToSignedGateAux,
        controlPhaseLeaves]
  | cons op ops ih =>
      have hNoTail : NoPhase ops := by intro i hi; exact hNo i (by simp [hi])
      cases op with
      | shiftL i m =>
          simp [annotatePhaseTermsAux, compileAnnotatedOpsToSignedGateAux,
            controlPhaseLeaves, ih n hNoTail]
      | shiftR i m =>
          simp [annotatePhaseTermsAux, compileAnnotatedOpsToSignedGateAux,
            controlPhaseLeaves, ih n hNoTail]
      | negate i =>
          simp [annotatePhaseTermsAux, compileAnnotatedOpsToSignedGateAux,
            controlPhaseLeaves, ih n hNoTail]
      | addScaled dst src negSrc sh =>
          simp [annotatePhaseTermsAux, compileAnnotatedOpsToSignedGateAux,
            controlPhaseLeaves, ih n hNoTail]
      | phaseProduct i =>
          exfalso
          exact hNo i (by simp)

/-- A no-phase program has zero phase-product instructions. -/
@[simp] lemma phaseProductCount_eq_zero_of_NoPhase
  {k : ℕ} {ops : Prog k} (hNo : NoPhase ops) :
  phaseProductCount ops = 0 := by
  induction ops with
  | nil =>
      simp [phaseProductCount]
  | cons op ops ih =>
      have hNoTail : NoPhase ops := by intro i hi; exact hNo i (by simp [hi])
      cases op with
      | shiftL i n =>
          simpa [phaseProductCount] using ih hNoTail
      | shiftR i n =>
          simpa [phaseProductCount] using ih hNoTail
      | negate i =>
          simpa [phaseProductCount] using ih hNoTail
      | addScaled dst src negSrc sh =>
          simpa [phaseProductCount] using ih hNoTail
      | phaseProduct i =>
          exfalso
          exact hNo i (by simp)

/-- Induction-friendly existential body theorem for the phase-block proof stack. -/
lemma eval_compileAnnotatedOpsToSignedGateAux_of_blocks_from
  (qs : QSemantics)
  [RegEncoding qs.Basis] [GateSemanticsFacts qs]
  (k : ℕ) (hk : 1 < k)
  (phi : Angle)
  (coeff : Fin (q k) → ℚ)
  (src dst : LayoutState k) :
  ∀ {σ : State k} {ops : Prog k} {pts : List Point},
    BlockDecomposition (k := k) (by omega) σ ops pts →
    ∀ (n : ℕ) (hn : n + pts.length = q k) (b0 bCur : qs.Basis),
      (hdisj : LayoutSlotsDisjoint dst) →
      (hFits :
        ∀ {τ : State k},
          (∃ pre rest, ops = pre ++ rest ∧ run? pre σ = some τ) →
            (∀ j : Fin k,
              FitsSignedWidth (ExtReg.width (dst.xslot j))
                (evalRowX (qs := qs) src (τ j) b0)) ∧
            (∀ j : Fin k,
              FitsSignedWidth (ExtReg.width (dst.zslot j))
                (evalRowZ (qs := qs) src (τ j) b0))) →
      (hSafeAdd :
        ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
          ops = pre ++ valid_ops.addScaled d s negSrc sh :: rest → d ≠ s) →
      EncodesStateFromFits (qs := qs) src dst σ b0 bCur →
      ∃ σf bNext,
        run? ops σ = some σf ∧
        qs.eval
            (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst
              (annotatePhaseTermsAux k n ops))
            (qs.ket bCur)
          =
        phaseScalarFrom (qs := qs) k phi coeff src b0 pts n hn •
          qs.ket bNext
        ∧
        EncodesStateFromFits (qs := qs) src dst σf b0 bNext := by
  intro σ ops pts hB
  induction hB with
  | nil σ σ' tail hNP hrun =>
      intro n hn b0 bCur hdisj hFits hSafeAdd hEnc
      rcases encodesFrom_after_noPhase_run_ket_gen
          (qs := qs)
          (hk := hk)
          (phi := phi)
          (coeff := coeff)
          (src := src)
          (dst := dst)
          (ops := tail)
          (σ := σ)
          (σ' := σ')
          (bRef := b0)
          (bCur := bCur)
          (n := n)
          hdisj
          hFits
          hSafeAdd
          hNP
          hrun
          hEnc with
        ⟨bNext, hEval, hEncNext⟩
      refine ⟨σ', bNext, hrun, ?_, hEncNext⟩
      simpa [phaseScalarFrom] using hEval
  | cons B hrest ih =>
      intro n hn b0 bCur hdisj hFits hSafeAdd hEnc
      rename_i σ2 pt pts2 oprest
      have hlt : n < q k := by
        simp at hn;omega
      have hnTail : n + 1 + pts2.length = q k := by
        simp at hn; simp[← hn]; simp[add_assoc]; rw[add_comm]
      have hcount : phaseProductCount B.toProg = 1 := by
        rw [PhaseBlock.toProg, phaseProductCount_append]
        simp [phaseProductCount_eq_zero_of_NoPhase, B.noPhase_pre, phaseProductCount]
      have hAnnAll :
          annotatePhaseTermsAux k n (B.toProg ++ oprest) =
            annotatePhaseTermsAux k n B.toProg ++
            annotatePhaseTermsAux k (n + 1) oprest := by
        rw [annotatePhaseTermsAux_append]
        simp [hcount]
      have hAnnBlock :
          annotatePhaseTermsAux k n B.toProg =
            annotatePhaseTermsAux k n B.arith ++
            [{ op := .phaseProduct B.i, phaseTerm? := some ⟨n, hlt⟩ }] := by
        rw [PhaseBlock.toProg, annotatePhaseTermsAux_append]
        simp [annotatePhaseTermsAux, hlt,
          phaseProductCount_eq_zero_of_NoPhase, B.noPhase_pre]
      have hFitsArith :
          ∀ {τ : State k},
            (∃ pre rest, B.arith = pre ++ rest ∧ run? pre σ2 = some τ) →
              (∀ j : Fin k,
                FitsSignedWidth (ExtReg.width (dst.xslot j))
                  (evalRowX (qs := qs) src (τ j) b0)) ∧
              (∀ j : Fin k,
                FitsSignedWidth (ExtReg.width (dst.zslot j))
                  (evalRowZ (qs := qs) src (τ j) b0)) := by
        intro τ hτ
        rcases hτ with ⟨pre, rest, hsplit, hrunpre⟩
        apply hFits
        refine ⟨pre, rest ++ [.phaseProduct B.i] ++ oprest, ?_, ?_⟩
        · simp [PhaseBlock.toProg, hsplit, List.append_assoc]
        · exact hrunpre
      have hSafeAddArith :
          ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
            B.arith = pre ++ valid_ops.addScaled d s negSrc sh :: rest → d ≠ s := by
        intro pre rest d s negSrc sh hmem
        exact hSafeAdd
          (pre := pre)
          (rest := rest ++ [valid_ops.phaseProduct B.i] ++ oprest)
          (d := d) (s := s) (negSrc := negSrc) (sh := sh)
          (by
            rw [PhaseBlock.toProg]
            simp [hmem, List.append_assoc])
      rcases encodesFrom_after_noPhase_run_ket_gen
          (qs := qs)
          (hk := hk)
          (phi := phi)
          (coeff := coeff)
          (src := src)
          (dst := dst)
          (ops := B.arith)
          (σ := σ2)
          (σ' := B.σmid)
          (bRef := b0)
          (bCur := bCur)
          (n := n)
          hdisj
          hFitsArith
          hSafeAddArith
          B.noPhase_pre
          B.run_pre
          hEnc with
        ⟨bMid, hArithEval, hArithEnc⟩
      have hRunBlock : run? B.toProg σ2 = some B.σmid := by
        simp[PhaseBlock.toProg, run?_append, B.run_pre, applyOp?]
      have hFitsTail :
          ∀ {τ : State k},
            (∃ pre rest, oprest = pre ++ rest ∧ run? pre B.σmid = some τ) →
              (∀ j : Fin k,
                FitsSignedWidth (ExtReg.width (dst.xslot j))
                  (evalRowX (qs := qs) src (τ j) b0)) ∧
              (∀ j : Fin k,
                FitsSignedWidth (ExtReg.width (dst.zslot j))
                  (evalRowZ (qs := qs) src (τ j) b0)) := by
        intro τ hτ
        rcases hτ with ⟨pre, rest, hsplit, hrunpre⟩
        apply hFits
        refine ⟨B.toProg ++ pre, rest, ?_, ?_⟩
        · simp [PhaseBlock.toProg, hsplit, List.append_assoc]
        · rw [run?_append, hRunBlock];simp[hrunpre]
      have hSafeAddTail :
          ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
            oprest = pre ++ valid_ops.addScaled d s negSrc sh :: rest → d ≠ s := by
        intro pre rest d s negSrc sh hmem
        exact hSafeAdd
          (pre := B.toProg ++ pre)
          (rest := rest)
          (d := d) (s := s) (negSrc := negSrc) (sh := sh)
          (by simp [hmem, List.append_assoc])
      rcases ih (n + 1) hnTail b0 bMid hdisj hFitsTail hSafeAddTail hArithEnc with
        ⟨σf, bNext, hRunTail, hEvalTail, hEncTail⟩
      refine ⟨σf, bNext, ?_, ?_, hEncTail⟩
      · simpa [PhaseBlock.toProg, run?_append, B.run_pre, applyOp?] using hRunTail
      · rw [hAnnAll]
        rw [eval_compileAnnotatedOpsToSignedGateAux_append
              (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
              (st := dst)
              (xs := annotatePhaseTermsAux k n B.toProg)
              (ys := annotatePhaseTermsAux k (n + 1) oprest)
              (ψ := qs.ket bCur)]
        rw [hAnnBlock]
        rw [eval_compileAnnotatedOpsToSignedGateAux_append
              (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
              (st := dst)
              (xs := annotatePhaseTermsAux k n B.arith)
              (ys := [{ op := .phaseProduct B.i, phaseTerm? := some ⟨n, hlt⟩ }])
              (ψ := qs.ket bCur)]
        rw [hArithEval]
        have hPhase :
            qs.eval
                (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst
                  [{ op := .phaseProduct B.i, phaseTerm? := some ⟨n, hlt⟩ }])
                (qs.ket bMid)
              =
            (Complex.exp
              (((Angle.toReal (phi * coeff ⟨n, hlt⟩) : ℝ) : ℂ) * Complex.I *
                (((evalRowX (qs := qs) src (expectedRow (k := k) pt) b0 : ℤ) : ℂ) *
                 (((evalRowZ (qs := qs) src (expectedRow (k := k) pt) b0 : ℤ) : ℂ))))) •
              qs.ket bMid := by
          simp [compileAnnotatedOpsToSignedGateAux, qs.eval_seq, qs.eval_id]
          simpa using
            (eval_matched_phase_ket_from
              (qs := qs)
              (src := src)
              (dst := dst)
              (σ := B.σmid)
              (b0 := b0)
              (b1 := bMid)
              (hk0 := by omega)
              (i := B.i)
              (pt := pt)
              (phi := phi * coeff ⟨n, hlt⟩)
              hArithEnc.1
              B.match_pt)
        rw [hPhase]
        rw [qs.eval_smul]
        rw [hEvalTail]
        simp [phaseScalarFrom, mul_assoc, smul_smul]

/-- Block evaluation also preserves registers outside the destination layout. -/
lemma eval_compileAnnotatedOpsToSignedGateAux_of_blocks_from_sameOutside
  (qs : QSemantics)
  [RegEncoding qs.Basis] [GateSemanticsFacts qs]
  (k : ℕ) (hk : 1 < k)
  (phi : Angle)
  (coeff : Fin (q k) → ℚ)
  (src dst : LayoutState k) :
  ∀ {σ : State k} {ops : Prog k} {pts : List Point},
    BlockDecomposition (k := k) (by omega) σ ops pts →
    ∀ (n : ℕ) (hn : n + pts.length = q k) (b0 bCur : qs.Basis),
      (hdisj : LayoutSlotsDisjoint dst) →
      (hFits :
        ∀ {τ : State k},
          (∃ pre rest, ops = pre ++ rest ∧ run? pre σ = some τ) →
            (∀ j : Fin k,
              FitsSignedWidth (ExtReg.width (dst.xslot j))
                (evalRowX (qs := qs) src (τ j) b0)) ∧
            (∀ j : Fin k,
              FitsSignedWidth (ExtReg.width (dst.zslot j))
                (evalRowZ (qs := qs) src (τ j) b0))) →
      (hSafeAdd :
        ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
          ops = pre ++ valid_ops.addScaled d s negSrc sh :: rest → d ≠ s) →
      EncodesStateFromFits (qs := qs) src dst σ b0 bCur →
      ∃ bNext,
        qs.eval
            (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst
              (annotatePhaseTermsAux k n ops))
            (qs.ket bCur)
          =
        phaseScalarFrom (qs := qs) k phi coeff src b0 pts n hn •
          qs.ket bNext
        ∧
        SameOutsideLayout qs dst bCur bNext := by
  intro σ ops pts hB
  induction hB with
  | nil σ σ' tail hNP hrun =>
      intro n hn b0 bCur hdisj hFits hSafeAdd hEnc
      rcases sameOutside_after_noPhase_run_ket_gen
          (qs := qs)
          (hk := hk)
          (phi := phi)
          (coeff := coeff)
          (src := src) (dst := dst)
          (ops := tail)
          (σ := σ) (σ' := σ')
          (bRef := b0) (bCur := bCur)
          (n := n)
          hdisj hFits hSafeAdd hNP hrun hEnc with
        ⟨bNext, hEval, hSO⟩
      refine ⟨bNext, ?_, hSO⟩
      simpa [phaseScalarFrom] using hEval
  | cons B hrest ih =>
      intro n hn b0 bCur hdisj hFits hSafeAdd hEnc
      rename_i σ2 pt pts2 oprest
      have hlt : n < q k := by simp at hn; omega
      have hFitsArith :
          ∀ {τ : State k},
            (∃ pre rest, B.arith = pre ++ rest ∧ run? pre σ2 = some τ) →
              (∀ j : Fin k,
                FitsSignedWidth (ExtReg.width (dst.xslot j))
                  (evalRowX (qs := qs) src (τ j) b0)) ∧
              (∀ j : Fin k,
                FitsSignedWidth (ExtReg.width (dst.zslot j))
                  (evalRowZ (qs := qs) src (τ j) b0)) := by
        intro τ hτ
        rcases hτ with ⟨pre, rest, hsplit, hrunpre⟩
        apply hFits
        refine ⟨pre, rest ++ [.phaseProduct B.i] ++ oprest, ?_, ?_⟩
        · simp [PhaseBlock.toProg, hsplit, List.append_assoc]
        · exact hrunpre
      have hSafeAddArith :
          ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
            B.arith = pre ++ valid_ops.addScaled d s negSrc sh :: rest → d ≠ s := by
        intro pre rest d s negSrc sh hadd
        exact hSafeAdd
          (pre := pre)
          (rest := rest ++ [valid_ops.phaseProduct B.i] ++ oprest)
          (d := d) (s := s) (negSrc := negSrc) (sh := sh)
          (by
            rw [PhaseBlock.toProg]
            simp [hadd, List.append_assoc])
      rcases encodesFrom_after_noPhase_run_ket_gen
          (qs := qs)
          (hk := hk)
          (phi := phi)
          (coeff := coeff)
          (src := src) (dst := dst)
          (ops := B.arith)
          (σ := σ2) (σ' := B.σmid)
          (bRef := b0) (bCur := bCur)
          (n := n)
          hdisj hFitsArith hSafeAddArith
          B.noPhase_pre B.run_pre hEnc with
        ⟨bMid, hArithEval, hArithEnc⟩
      rcases sameOutside_after_noPhase_run_ket_gen
          (qs := qs)
          (hk := hk)
          (phi := phi)
          (coeff := coeff)
          (src := src) (dst := dst)
          (ops := B.arith)
          (σ := σ2) (σ' := B.σmid)
          (bRef := b0) (bCur := bCur)
          (n := n)
          hdisj hFitsArith hSafeAddArith
          B.noPhase_pre B.run_pre hEnc with
        ⟨bMid', hArithEval', hArithSO'⟩
      have hbMid' : bMid' = bMid := by
        apply qs.ket_inj
        simp [hArithEval] at hArithEval';simp[hArithEval']
      have hArithSO : SameOutsideLayout qs dst bCur bMid := by
        simpa [hbMid'] using hArithSO'
      have hRunBlock : run? B.toProg σ2 = some B.σmid := by simp [PhaseBlock.toProg, run?_append, B.run_pre, applyOp?]
      have hFitsTail :
          ∀ {τ : State k},
            (∃ pre rest, oprest = pre ++ rest ∧ run? pre B.σmid = some τ) →
              (∀ j : Fin k,
                FitsSignedWidth (ExtReg.width (dst.xslot j))
                  (evalRowX (qs := qs) src (τ j) b0)) ∧
              (∀ j : Fin k,
                FitsSignedWidth (ExtReg.width (dst.zslot j))
                  (evalRowZ (qs := qs) src (τ j) b0)) := by
        intro τ hτ
        rcases hτ with ⟨pre, rest, hsplit, hrunpre⟩
        apply hFits
        refine ⟨B.toProg ++ pre, rest, ?_, ?_⟩
        · simp [PhaseBlock.toProg, hsplit, List.append_assoc]
        · rw [run?_append, hRunBlock]; simpa using hrunpre
      have hSafeAddTail :
          ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
            oprest = pre ++ valid_ops.addScaled d s negSrc sh :: rest → d ≠ s := by
        intro pre rest d s negSrc sh hadd
        exact hSafeAdd
          (pre := B.toProg ++ pre)
          (rest := rest)
          (d := d) (s := s) (negSrc := negSrc) (sh := sh)
          (by simp [hadd, List.append_assoc])
      have hnTail : n + 1 + pts2.length = q k := by simp at hn; omega
      rcases ih (n + 1) hnTail b0 bMid hdisj hFitsTail hSafeAddTail hArithEnc with
        ⟨bNext, hEvalTail, hTailSO⟩
      refine ⟨bNext, ?_, SameOutsideLayout.trans (qs := qs) hArithSO hTailSO⟩
      have hAnnAll :
          annotatePhaseTermsAux k n (B.toProg ++ oprest) =
            annotatePhaseTermsAux k n B.toProg ++
              annotatePhaseTermsAux k (n + 1) oprest := by
        have hCountBlock : phaseProductCount B.toProg = 1 := by
          simp [PhaseBlock.toProg, phaseProductCount, B.noPhase_pre]
        have hAnnAll :
            annotatePhaseTermsAux k n (B.toProg ++ oprest) =
              annotatePhaseTermsAux k n B.toProg ++
                annotatePhaseTermsAux k (n + 1) oprest := by
          rw [annotatePhaseTermsAux_append]
          simp [hCountBlock]
        rw[hAnnAll]
      have hAnnBlock :
          annotatePhaseTermsAux k n B.toProg =
            annotatePhaseTermsAux k n B.arith ++
              [{ op := .phaseProduct B.i, phaseTerm? := some ⟨n, hlt⟩ }] := by
        simp [PhaseBlock.toProg]
        rw [annotatePhaseTermsAux_append]
        simp [annotatePhaseTermsAux, hlt,
          phaseProductCount_eq_zero_of_NoPhase, B.noPhase_pre]
      rw [hAnnAll]
      rw [eval_compileAnnotatedOpsToSignedGateAux_append
            (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
            (st := dst)
            (xs := annotatePhaseTermsAux k n B.toProg)
            (ys := annotatePhaseTermsAux k (n + 1) oprest)
            (ψ := qs.ket bCur)]
      rw [hAnnBlock]
      rw [eval_compileAnnotatedOpsToSignedGateAux_append
            (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
            (st := dst)
            (xs := annotatePhaseTermsAux k n B.arith)
            (ys := [{ op := .phaseProduct B.i, phaseTerm? := some ⟨n, hlt⟩ }])
            (ψ := qs.ket bCur)]
      rw [hArithEval]
      have hPhase :
          qs.eval
              (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst
                [{ op := .phaseProduct B.i, phaseTerm? := some ⟨n, hlt⟩ }])
              (qs.ket bMid)
            =
          (Complex.exp
            (((Angle.toReal (phi * coeff ⟨n, hlt⟩) : ℝ) : ℂ) * Complex.I *
              (((evalRowX (qs := qs) src (expectedRow (k := k) pt) b0 : ℤ) : ℂ) *
               (((evalRowZ (qs := qs) src (expectedRow (k := k) pt) b0 : ℤ) : ℂ))))) •
            qs.ket bMid := by
        simp [compileAnnotatedOpsToSignedGateAux, qs.eval_seq, qs.eval_id]
        simpa using
          (eval_matched_phase_ket_from
            (qs := qs)
            (src := src)
            (dst := dst)
            (σ := B.σmid)
            (b0 := b0)
            (b1 := bMid)
            (hk0 := by omega)
            (i := B.i)
            (pt := pt)
            (phi := phi * coeff ⟨n, hlt⟩)
            hArithEnc.1
            B.match_pt)
      rw [hPhase]
      rw [qs.eval_smul]
      rw [hEvalTail]
      simp [phaseScalarFrom, mul_assoc, smul_smul]

/-! =========================================================
    Public Body Theorems And Controlled Variants
    These are the body-level statements used by the surrounding compiler proof:
    the full annotated body evaluates to the phase scalar, and the controlled
    version evaluates to either that scalar or identity while preserving layout.
========================================================= -/

/-- Controlled block evaluation returns the conditional phase scalar plus final encoding and locality. -/
lemma eval_controlPhaseLeaves_compileAnnotatedOpsToSignedGateAux_of_blocks_from_sameOutside
  (qs : QSemantics)
  [RegEncoding qs.Basis] [GateSemanticsFacts qs]
  (k : ℕ) (hk : 1 < k)
  (ctrl : ℕ)
  (phi : Angle)
  (coeff : Fin (q k) → ℚ)
  (src dst : LayoutState k) :
  ∀ {σ : State k} {ops : Prog k} {pts : List Point},
    BlockDecomposition (k := k) (by omega) σ ops pts →
    ∀ (n : ℕ) (hn : n + pts.length = q k) (b0 bCur : qs.Basis),
      (hdisj : LayoutSlotsDisjoint dst) →
      (hCtrlOutside : OutsideLayout dst (ExtReg.ofReg (qubitReg ctrl))) →
      RegEncoding.bit ctrl bCur = RegEncoding.bit ctrl b0 →
      (hFits :
        ∀ {τ : State k},
          (∃ pre rest, ops = pre ++ rest ∧ run? pre σ = some τ) →
            (∀ j : Fin k,
              FitsSignedWidth (ExtReg.width (dst.xslot j))
                (evalRowX (qs := qs) src (τ j) b0)) ∧
            (∀ j : Fin k,
              FitsSignedWidth (ExtReg.width (dst.zslot j))
                (evalRowZ (qs := qs) src (τ j) b0))) →
      (hSafeAdd :
        ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
          ops = pre ++ valid_ops.addScaled d s negSrc sh :: rest → d ≠ s) →
      EncodesStateFromFits (qs := qs) src dst σ b0 bCur →
      ∃ σf bNext,
        run? ops σ = some σf ∧
        qs.eval
            (controlPhaseLeaves ctrl
              (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst
                (annotatePhaseTermsAux k n ops)))
            (qs.ket bCur)
          =
        (if RegEncoding.bit ctrl b0 then
          phaseScalarFrom (qs := qs) k phi coeff src b0 pts n hn
        else
          1) •
          qs.ket bNext
        ∧
        EncodesStateFromFits (qs := qs) src dst σf b0 bNext ∧
        SameOutsideLayout qs dst bCur bNext := by
  intro σ ops pts hB
  induction hB with
  | nil σ σ' tail hNP hrun =>
      intro n hn b0 bCur hdisj hCtrlOutside hCtrlCur hFits hSafeAdd hEnc
      rcases encodesFrom_after_noPhase_run_ket_gen
          (qs := qs)
          (hk := hk)
          (phi := phi)
          (coeff := coeff)
          (src := src) (dst := dst)
          (ops := tail)
          (σ := σ) (σ' := σ')
          (bRef := b0) (bCur := bCur)
          (n := n)
          hdisj hFits hSafeAdd hNP hrun hEnc with
        ⟨bEnc, hEvalEnc, hEncNext⟩
      rcases sameOutside_after_noPhase_run_ket_gen
          (qs := qs)
          (hk := hk)
          (phi := phi)
          (coeff := coeff)
          (src := src) (dst := dst)
          (ops := tail)
          (σ := σ) (σ' := σ')
          (bRef := b0) (bCur := bCur)
          (n := n)
          hdisj hFits hSafeAdd hNP hrun hEnc with
        ⟨bSO, hEvalSO, hSO⟩
      have hbSO : bSO = bEnc := by
        apply qs.ket_inj
        calc
          qs.ket bSO
              = qs.eval
                  (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst
                    (annotatePhaseTermsAux k n tail))
                  (qs.ket bCur) := hEvalSO.symm
          _ = qs.ket bEnc := hEvalEnc
      subst bSO
      refine ⟨σ', bEnc, hrun, ?_, hEncNext, hSO⟩
      have hNoCtrl :
          controlPhaseLeaves ctrl
              (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst
                (annotatePhaseTermsAux k n tail))
            =
          compileAnnotatedOpsToSignedGateAux k hk phi coeff dst
            (annotatePhaseTermsAux k n tail) := by
        exact controlPhaseLeaves_compileAnnotatedOpsToSignedGateAux_of_NoPhase
          hk ctrl phi coeff dst tail n hNP
      rw [hNoCtrl]
      by_cases hc : RegEncoding.bit ctrl b0
      · simp [phaseScalarFrom, hc]
        simpa [phaseScalarFrom] using hEvalEnc
      · simp [hc]
        simpa using hEvalEnc
  | cons B hrest ih =>
      intro n hn b0 bCur hdisj hCtrlOutside hCtrlCur hFits hSafeAdd hEnc
      rename_i σ2 pt pts2 oprest
      have hlt : n < q k := by simp at hn; omega
      have hFitsArith :
          ∀ {τ : State k},
            (∃ pre rest, B.arith = pre ++ rest ∧ run? pre σ2 = some τ) →
              (∀ j : Fin k,
                FitsSignedWidth (ExtReg.width (dst.xslot j))
                  (evalRowX (qs := qs) src (τ j) b0)) ∧
              (∀ j : Fin k,
                FitsSignedWidth (ExtReg.width (dst.zslot j))
                  (evalRowZ (qs := qs) src (τ j) b0)) := by
        intro τ hτ
        rcases hτ with ⟨pre, rest, hsplit, hrunpre⟩
        apply hFits
        refine ⟨pre, rest ++ [.phaseProduct B.i] ++ oprest, ?_, ?_⟩
        · simp [PhaseBlock.toProg, hsplit, List.append_assoc]
        · exact hrunpre
      have hSafeAddArith :
          ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
            B.arith = pre ++ valid_ops.addScaled d s negSrc sh :: rest → d ≠ s := by
        intro pre rest d s negSrc sh hadd
        exact hSafeAdd
          (pre := pre)
          (rest := rest ++ [valid_ops.phaseProduct B.i] ++ oprest)
          (d := d) (s := s) (negSrc := negSrc) (sh := sh)
          (by
            rw [PhaseBlock.toProg]
            simp [hadd, List.append_assoc])
      rcases encodesFrom_after_noPhase_run_ket_gen
          (qs := qs)
          (hk := hk)
          (phi := phi)
          (coeff := coeff)
          (src := src) (dst := dst)
          (ops := B.arith)
          (σ := σ2) (σ' := B.σmid)
          (bRef := b0) (bCur := bCur)
          (n := n)
          hdisj hFitsArith hSafeAddArith
          B.noPhase_pre B.run_pre hEnc with
        ⟨bMid, hArithEval, hArithEnc⟩
      rcases sameOutside_after_noPhase_run_ket_gen
          (qs := qs)
          (hk := hk)
          (phi := phi)
          (coeff := coeff)
          (src := src) (dst := dst)
          (ops := B.arith)
          (σ := σ2) (σ' := B.σmid)
          (bRef := b0) (bCur := bCur)
          (n := n)
          hdisj hFitsArith hSafeAddArith
          B.noPhase_pre B.run_pre hEnc with
        ⟨bMid', hArithEval', hArithSO'⟩
      have hbMid' : bMid' = bMid := by
        apply qs.ket_inj
        simp [hArithEval] at hArithEval'
        simp [hArithEval']
      have hArithSO : SameOutsideLayout qs dst bCur bMid := by
        simpa [hbMid'] using hArithSO'
      have hCtrlMid : RegEncoding.bit ctrl bMid = RegEncoding.bit ctrl b0 := by
        calc
          RegEncoding.bit ctrl bMid
              = RegEncoding.bit ctrl bCur :=
                SameOutsideLayout.bit_eq_of_outside
                  (qs := qs) hArithSO ctrl hCtrlOutside
          _ = RegEncoding.bit ctrl b0 := hCtrlCur
      have hRunBlock : run? B.toProg σ2 = some B.σmid := by simp [PhaseBlock.toProg, run?_append, B.run_pre, applyOp?]
      have hFitsTail :
          ∀ {τ : State k},
            (∃ pre rest, oprest = pre ++ rest ∧ run? pre B.σmid = some τ) →
              (∀ j : Fin k,
                FitsSignedWidth (ExtReg.width (dst.xslot j))
                  (evalRowX (qs := qs) src (τ j) b0)) ∧
              (∀ j : Fin k,
                FitsSignedWidth (ExtReg.width (dst.zslot j))
                  (evalRowZ (qs := qs) src (τ j) b0)) := by
        intro τ hτ
        rcases hτ with ⟨pre, rest, hsplit, hrunpre⟩
        apply hFits
        refine ⟨B.toProg ++ pre, rest, ?_, ?_⟩
        · simp [PhaseBlock.toProg, hsplit, List.append_assoc]
        · rw [run?_append, hRunBlock]; simpa using hrunpre
      have hSafeAddTail :
          ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
            oprest = pre ++ valid_ops.addScaled d s negSrc sh :: rest → d ≠ s := by
        intro pre rest d s negSrc sh hadd
        exact hSafeAdd
          (pre := B.toProg ++ pre)
          (rest := rest)
          (d := d) (s := s) (negSrc := negSrc) (sh := sh)
          (by simp [hadd, List.append_assoc])
      have hnTail : n + 1 + pts2.length = q k := by simp at hn; omega
      rcases ih (n + 1) hnTail b0 bMid hdisj hCtrlOutside hCtrlMid
          hFitsTail hSafeAddTail hArithEnc with
        ⟨σf, bNext, hRunTail, hEvalTail, hEncTail, hTailSO⟩
      have hRunAll : run? (B.toProg ++ oprest) σ2 = some σf := by rw [run?_append, hRunBlock]; exact hRunTail
      refine ⟨σf, bNext, hRunAll, ?_, hEncTail,
        SameOutsideLayout.trans (qs := qs) hArithSO hTailSO⟩
      have hAnnAll :
          annotatePhaseTermsAux k n (B.toProg ++ oprest) =
            annotatePhaseTermsAux k n B.toProg ++
              annotatePhaseTermsAux k (n + 1) oprest := by
        have hCountBlock : phaseProductCount B.toProg = 1 := by
          simp [PhaseBlock.toProg, phaseProductCount, B.noPhase_pre]
        rw [annotatePhaseTermsAux_append]
        simp [hCountBlock]
      have hAnnBlock :
          annotatePhaseTermsAux k n B.toProg =
            annotatePhaseTermsAux k n B.arith ++
              [{ op := .phaseProduct B.i, phaseTerm? := some ⟨n, hlt⟩ }] := by
        simp [PhaseBlock.toProg]
        rw [annotatePhaseTermsAux_append]
        simp [annotatePhaseTermsAux, hlt,
          phaseProductCount_eq_zero_of_NoPhase, B.noPhase_pre]
      rw [hAnnAll]
      rw [eval_controlPhaseLeaves_compileAnnotatedOpsToSignedGateAux_append
            (qs := qs) (hk := hk) (ctrl := ctrl) (phi := phi) (coeff := coeff)
            (st := dst)
            (xs := annotatePhaseTermsAux k n B.toProg)
            (ys := annotatePhaseTermsAux k (n + 1) oprest)
            (ψ := qs.ket bCur)]
      rw [hAnnBlock]
      rw [eval_controlPhaseLeaves_compileAnnotatedOpsToSignedGateAux_append
            (qs := qs) (hk := hk) (ctrl := ctrl) (phi := phi) (coeff := coeff)
            (st := dst)
            (xs := annotatePhaseTermsAux k n B.arith)
            (ys := [{ op := .phaseProduct B.i, phaseTerm? := some ⟨n, hlt⟩ }])
            (ψ := qs.ket bCur)]
      have hNoCtrlArith :
          controlPhaseLeaves ctrl
              (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst
                (annotatePhaseTermsAux k n B.arith))
            =
          compileAnnotatedOpsToSignedGateAux k hk phi coeff dst
            (annotatePhaseTermsAux k n B.arith) := by
        exact controlPhaseLeaves_compileAnnotatedOpsToSignedGateAux_of_NoPhase
          hk ctrl phi coeff dst B.arith n B.noPhase_pre
      rw [hNoCtrlArith]
      rw [hArithEval]
      have hPhase :
          qs.eval
              (controlPhaseLeaves ctrl
                (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst
                  [{ op := .phaseProduct B.i, phaseTerm? := some ⟨n, hlt⟩ }]))
              (qs.ket bMid)
            =
          if RegEncoding.bit ctrl bMid then
            (Complex.exp
              (((Angle.toReal (phi * coeff ⟨n, hlt⟩) : ℝ) : ℂ) * Complex.I *
                (((evalRowX (qs := qs) src (expectedRow (k := k) pt) b0 : ℤ) : ℂ) *
                 (((evalRowZ (qs := qs) src (expectedRow (k := k) pt) b0 : ℤ) : ℂ))))) •
              qs.ket bMid
          else
            qs.ket bMid := by
        simp [compileAnnotatedOpsToSignedGateAux, controlPhaseLeaves,
          qs.eval_seq, qs.eval_id]
        simpa using
          (eval_matched_cphase_ket_from
            (qs := qs)
            (src := src)
            (dst := dst)
            (σ := B.σmid)
            (b0 := b0)
            (b1 := bMid)
            (hk0 := by omega)
            (ctrl := ctrl)
            (i := B.i)
            (pt := pt)
            (phi := phi * coeff ⟨n, hlt⟩)
            hArithEnc.1
            B.match_pt)
      rw [hPhase]
      by_cases hc : RegEncoding.bit ctrl b0
      · have hcMid : RegEncoding.bit ctrl bMid = true := by
          simpa [hc] using hCtrlMid
        simp [hc, hcMid]
        rw [qs.eval_smul]
        rw [hEvalTail]
        simp [phaseScalarFrom, hc, mul_assoc, smul_smul]
      · have hcMid : RegEncoding.bit ctrl bMid = false := by
          cases hmid : RegEncoding.bit ctrl bMid <;> simp
          · have : RegEncoding.bit ctrl b0 = true := by
              simpa [hmid] using hCtrlMid.symm
            exact False.elim (hc this)
        simp [hc, hcMid]
        rw [hEvalTail]
        simp [hc]

/-- Full body evaluation from the start state returns the accumulated phase scalar. -/
lemma eval_compileAnnotatedOpsToSignedGateAux_of_blocks
  (qs : QSemantics)
  [RegEncoding qs.Basis] [GateSemanticsFacts qs]
  (k : ℕ) (hk : 1 < k)
  (phi : Angle)
  (pts : List Point)
  (hpts : pts.length = q k)
  (coeff : Fin (q k) → ℚ)
  (src dst : LayoutState k)
  (b0 bMid : qs.Basis)
  (ops : Prog k)
  (hdisj : LayoutSlotsDisjoint dst)
  (hFits :
    ∀ {τ : State k},
      (∃ pre rest, ops = pre ++ rest ∧ run? pre State.start_state = some τ) →
        (∀ j : Fin k,
          FitsSignedWidth (ExtReg.width (dst.xslot j))
            (evalRowX (qs := qs) src (τ j) b0)) ∧
        (∀ j : Fin k,
          FitsSignedWidth (ExtReg.width (dst.zslot j))
            (evalRowZ (qs := qs) src (τ j) b0)))
  (hSafeAdd :
    ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
      ops = pre ++ valid_ops.addScaled d s negSrc sh :: rest → d ≠ s)
  (hEnc : EncodesStateFromFits (qs := qs) src dst State.start_state b0 bMid)
  (hB : BlockDecomposition (k := k) (by omega) State.start_state ops pts)
  (run_ops_start_state : run? ops State.start_state = some State.start_state) :
  qs.eval
      (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst
        (annotatePhaseTermsAux k 0 ops))
      (qs.ket bMid)
    =
  phaseScalarFrom (qs := qs) k phi coeff src b0 pts 0 (by simpa using hpts) •
    qs.ket bMid := by
  rcases eval_compileAnnotatedOpsToSignedGateAux_of_blocks_from
      (qs := qs)
      (k := k) (hk := hk)
      (phi := phi)
      (coeff := coeff)
      (src := src) (dst := dst)
      (σ := State.start_state)
      (ops := ops)
      (pts := pts)
      hB
      0
      (by simp [hpts])
      b0
      bMid
      hdisj
      hFits
      hSafeAdd
      hEnc with
    ⟨σf, bNext, hRun, hBody, hEncNextFits⟩
  rcases hEncNextFits with ⟨hEncNext, hOutX, hOutZ⟩
  rcases eval_compileAnnotatedOpsToSignedGateAux_of_blocks_from_sameOutside
      (qs := qs)
      (k := k) (hk := hk)
      (phi := phi)
      (coeff := coeff)
      (src := src) (dst := dst)
      (σ := State.start_state)
      (ops := ops)
      (pts := pts)
      hB
      0
      (by simp [hpts])
      b0
      bMid
      hdisj
      hFits
      hSafeAdd
      hEnc with
    ⟨bSO, hBodySO, hSO⟩
  have hσf : σf = State.start_state := by
    have hs : some σf = some State.start_state := by
      calc
        some σf = run? ops State.start_state := by simp [hRun]
        _ = some State.start_state := run_ops_start_state
    exact Option.some.inj hs
  subst hσf
  have hscalar_ne :
      phaseScalarFrom (qs := qs) k phi coeff src b0 pts 0 (by simpa using hpts) ≠ 0 := by
    exact phaseScalarFrom_ne_zero
      (qs := qs) (k := k) (phi := phi) (coeff := coeff)
      (src := src) (b0 := b0)
      pts 0 (by simpa using hpts)
  have hbSO : bSO = bNext := by
    apply ket_eq_of_same_nonzero_smul
      (qs := qs)
      (a := phaseScalarFrom (qs := qs) k phi coeff src b0 pts 0 (by simpa using hpts))
      hscalar_ne
    calc
      phaseScalarFrom (qs := qs) k phi coeff src b0 pts 0 (by simpa using hpts) • qs.ket bSO
          = qs.eval
              (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst
                (annotatePhaseTermsAux k 0 ops))
              (qs.ket bMid) := by
                simpa using hBodySO.symm
      _   = phaseScalarFrom (qs := qs) k phi coeff src b0 pts 0 (by simpa using hpts) •
              qs.ket bNext := by
                simpa using hBody
  have hSO' : SameOutsideLayout qs dst bMid bNext := by
    simpa [hbSO] using hSO
  have hXslots :
      ∀ i : Fin k,
        extToInt (dst.xslot i) bNext =
          extToInt (dst.xslot i) bMid := by
    intro i
    calc
      extToInt (dst.xslot i) bNext
          = evalRowX (qs := qs) src (State.start_state i) b0 := by
              simpa [EncodesStateFrom] using hEncNext.1 i
      _   = extToInt (dst.xslot i) bMid := by
              symm
              simpa [EncodesStateFrom] using hEnc.1.1 i
  have hZslots :
      ∀ i : Fin k,
        extToInt (dst.zslot i) bNext =
          extToInt (dst.zslot i) bMid := by
    intro i
    calc
      extToInt (dst.zslot i) bNext
          = evalRowZ (qs := qs) src (State.start_state i) b0 := by
              simpa [EncodesStateFrom] using hEncNext.2 i
      _   = extToInt (dst.zslot i) bMid := by
              symm
              simpa [EncodesStateFrom] using hEnc.1.2 i
  have hbNext_eq : bNext = bMid := by
    exact basis_eq_of_sameOutside_and_slots
      (qs := qs)
      (dst := dst)
      (bMid := bMid)
      (bNext := bNext)
      hSO'
      hXslots
      hZslots
  subst hbNext_eq
  simpa using hBody

/-- Controlled full body evaluation returns the accumulated scalar only when the control bit is set. -/
lemma eval_controlPhaseLeaves_compileAnnotatedOpsToSignedGateAux_of_blocks
  (qs : QSemantics)
  [RegEncoding qs.Basis] [GateSemanticsFacts qs]
  (k : ℕ) (hk : 1 < k)
  (ctrl : ℕ)
  (phi : Angle)
  (pts : List Point)
  (hpts : pts.length = q k)
  (coeff : Fin (q k) → ℚ)
  (src dst : LayoutState k)
  (b0 bMid : qs.Basis)
  (ops : Prog k)
  (hdisj : LayoutSlotsDisjoint dst)
  (hCtrlOutside : OutsideLayout dst (ExtReg.ofReg (qubitReg ctrl)))
  (hCtrlMid : RegEncoding.bit ctrl bMid = RegEncoding.bit ctrl b0)
  (hFits :
    ∀ {τ : State k},
      (∃ pre rest, ops = pre ++ rest ∧ run? pre State.start_state = some τ) →
        (∀ j : Fin k,
          FitsSignedWidth (ExtReg.width (dst.xslot j))
            (evalRowX (qs := qs) src (τ j) b0)) ∧
        (∀ j : Fin k,
          FitsSignedWidth (ExtReg.width (dst.zslot j))
            (evalRowZ (qs := qs) src (τ j) b0)))
  (hSafeAdd :
    ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
      ops = pre ++ valid_ops.addScaled d s negSrc sh :: rest → d ≠ s)
  (hEnc : EncodesStateFromFits (qs := qs) src dst State.start_state b0 bMid)
  (hB : BlockDecomposition (k := k) (by omega) State.start_state ops pts)
  (run_ops_start_state : run? ops State.start_state = some State.start_state) :
  qs.eval
      (controlPhaseLeaves ctrl
        (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst
          (annotatePhaseTermsAux k 0 ops)))
      (qs.ket bMid)
    =
  (if RegEncoding.bit ctrl b0 then
    phaseScalarFrom (qs := qs) k phi coeff src b0 pts 0 (by simpa using hpts)
  else
    1) •
    qs.ket bMid := by
  rcases eval_controlPhaseLeaves_compileAnnotatedOpsToSignedGateAux_of_blocks_from_sameOutside
      (qs := qs)
      (k := k) (hk := hk)
      (ctrl := ctrl)
      (phi := phi)
      (coeff := coeff)
      (src := src) (dst := dst)
      (σ := State.start_state)
      (ops := ops)
      (pts := pts)
      hB
      0
      (by simp [hpts])
      b0
      bMid
      hdisj
      hCtrlOutside
      hCtrlMid
      hFits
      hSafeAdd
      hEnc with
    ⟨σf, bNext, hRun, hBody, hEncNextFits, hSO⟩
  rcases hEncNextFits with ⟨hEncNext, hOutX, hOutZ⟩
  have hσf : σf = State.start_state := by
    have hs : some σf = some State.start_state := by
      calc
        some σf = run? ops State.start_state := by simp [hRun]
        _ = some State.start_state := run_ops_start_state
    exact Option.some.inj hs
  subst hσf
  have hXslots :
      ∀ i : Fin k,
        extToInt (dst.xslot i) bNext =
          extToInt (dst.xslot i) bMid := by
    intro i
    calc
      extToInt (dst.xslot i) bNext
          = evalRowX (qs := qs) src (State.start_state i) b0 := by
              simpa [EncodesStateFrom] using hEncNext.1 i
      _   = extToInt (dst.xslot i) bMid := by
              symm
              simpa [EncodesStateFrom] using hEnc.1.1 i
  have hZslots :
      ∀ i : Fin k,
        extToInt (dst.zslot i) bNext =
          extToInt (dst.zslot i) bMid := by
    intro i
    calc
      extToInt (dst.zslot i) bNext
          = evalRowZ (qs := qs) src (State.start_state i) b0 := by
              simpa [EncodesStateFrom] using hEncNext.2 i
      _   = extToInt (dst.zslot i) bMid := by
              symm
              simpa [EncodesStateFrom] using hEnc.1.2 i
  have hbNext_eq : bNext = bMid := by
    exact basis_eq_of_sameOutside_and_slots
      (qs := qs)
      (dst := dst)
      (bMid := bMid)
      (bNext := bNext)
      hSO
      hXslots
      hZslots
  subst hbNext_eq
  simpa using hBody

end Shor
