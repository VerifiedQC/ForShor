import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.Body.SingleStep

namespace Shor
open Gate
open Operations
open scoped BigOperators

/-! =========================================================
    No-Phase Arithmetic Runs
    A no-phase segment is just a sequence of arithmetic row updates. The two
    inductions below carry, respectively, outside-layout preservation and encoded
    state preservation through such a segment.
========================================================= -/

/-- No-phase arithmetic runs preserve all registers outside the destination layout. -/
lemma sameOutside_after_noPhase_run_ket_gen
  (qs : QSemantics)
  [RegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ} (hk : 1 < k)
  (phi : Angle)
  (coeff : Fin (q k) → ℚ)
  (src dst : LayoutState k)
  (ops : Prog k)
  (σ σ' : State k)
  (bRef bCur : qs.Basis)
  (n : ℕ)
  (hdisj : LayoutSlotsDisjoint dst)
  (hFits :
    ∀ {τ : State k},
      (∃ pre rest, ops = pre ++ rest ∧ run? pre σ = some τ) →
      (∀ j : Fin k,
        FitsSignedWidth (ExtReg.width (dst.xslot j))
          (evalRowX (qs := qs) src (τ j) bRef)) ∧
      (∀ j : Fin k,
        FitsSignedWidth (ExtReg.width (dst.zslot j))
          (evalRowZ (qs := qs) src (τ j) bRef)))
  (hSafeAdd :
    ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
      ops = pre ++ (.addScaled d s negSrc sh :: rest) →
      d ≠ s)
  (hNP : NoPhase ops)
  (hrun : run? ops σ = some σ')
  (hEnc : EncodesStateFromFits (qs := qs) src dst σ bRef bCur) :
  ∃ bNext : qs.Basis,
    qs.eval
        (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst (annotatePhaseTermsAux k n ops))
        (qs.ket bCur)
      = qs.ket bNext ∧
    SameOutsideLayout qs dst bCur bNext := by
  induction ops generalizing σ σ' bCur n with
  | nil =>
      have hσ : σ = σ' := by simpa [run?] using hrun
      subst hσ
      refine ⟨bCur, ?_, SameOutsideLayout.refl qs dst bCur⟩
      simp [annotatePhaseTermsAux, compileAnnotatedOpsToSignedGateAux, qs.eval_id]
  | cons op ops ih =>
      have hNoTail : NoPhase ops := by intro i hi; exact hNP i (by simp [hi])
      cases op with
      | shiftL i m =>
          cases hstep : applyOp? σ (.shiftL i m) with
          | none =>
              simp [run?, hstep] at hrun
          | some σ1 =>
              have hrunTail : run? ops σ1 = some σ' := by simpa [run?, hstep] using hrun
              have hFit1 :
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.xslot j))
                      (evalRowX (qs := qs) src (σ1 j) bRef)) ∧
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.zslot j))
                      (evalRowZ (qs := qs) src (σ1 j) bRef)) := by
                apply hFits; refine ⟨[.shiftL i m], ops, ?_, ?_⟩ <;> simp [run?, hstep]
              rcases encodesFrom_after_shiftL_ket
                  (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
                  (src := src) (dst := dst) (hdisj := hdisj)
                  (i := i) (m := m)
                  (σ := σ) (σ1 := σ1)
                  (bRef := bRef) (bCur := bCur)
                  hstep hEnc hFit1.1 hFit1.2 with
                ⟨b1, hEval1, hEnc1⟩
              have hSO1 :
                  SameOutsideLayout qs dst bCur b1 := by
                have hσ1 : σ1 = State.shiftLReg σ i m := by
                  simp [applyOp?] at hstep
                  simpa using hstep.symm
                have hrow_shift_x :
                    evalRowX (qs := qs) src ((σ i).shiftL m) bRef
                    = ((2 : ℤ)^m) * evalRowX (qs := qs) src (σ i) bRef := by
                  simpa using
                    (evalRowX_shiftL_raw
                      (qs := qs) (src := src) (r := σ i) (m := m) (b := bRef))
                have hFitX :
                    FitsSignedWidth (ExtReg.width (dst.xslot i))
                      (((2 : ℤ)^m) * extToInt (dst.xslot i) bCur) := by
                  have hfit_post :
                      FitsSignedWidth (ExtReg.width (dst.xslot i))
                        (((2 : ℤ)^m) * evalRowX (qs := qs) src (σ i) bRef) := by
                    simpa [hσ1, State.shiftLReg, hrow_shift_x] using hFit1.1 i
                  rw [hEnc.1.1 i]
                  exact hfit_post
                have hrow_shift_z :
                    evalRowZ (qs := qs) src ((σ i).shiftL m) bRef
                    = ((2 : ℤ)^m) * evalRowZ (qs := qs) src (σ i) bRef := by
                  simpa using
                    (evalRowZ_shiftL_raw
                      (qs := qs) (src := src) (r := σ i) (m := m) (b := bRef))
                have hFitZ :
                    FitsSignedWidth (ExtReg.width (dst.zslot i))
                      (((2 : ℤ)^m) * extToInt (dst.zslot i) bCur) := by
                  have hfit_post :
                      FitsSignedWidth (ExtReg.width (dst.zslot i))
                        (((2 : ℤ)^m) * evalRowZ (qs := qs) src (σ i) bRef) := by
                    simpa [hσ1, State.shiftLReg, hrow_shift_z] using hFit1.2 i
                  rw [hEnc.1.2 i]
                  exact hfit_post
                exact sameOutside_after_shiftL_single
                  (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
                  (dst := dst) (hdisj := hdisj)
                  (i := i) (m := m) (bCur := bCur) (b1 := b1)
                  hFitX hFitZ hEval1
              have hFitsTail :
                ∀ {τ : State k},
                  (∃ pre rest, ops = pre ++ rest ∧ run? pre σ1 = some τ) →
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.xslot j))
                      (evalRowX (qs := qs) src (τ j) bRef)) ∧
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.zslot j))
                      (evalRowZ (qs := qs) src (τ j) bRef)) := by
                intro τ hτ
                rcases hτ with ⟨pre, rest, hsplit, hrunpre⟩
                apply hFits
                refine ⟨(.shiftL i m) :: pre, rest, ?_, ?_⟩
                · simp [hsplit]
                · simp [run?, hstep, hrunpre]
              have hSafeAddTail :
                ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
                  ops = pre ++ (.addScaled d s negSrc sh :: rest) →
                  d ≠ s := by
                intro pre rest d s negSrc sh hadd
                exact hSafeAdd
                  (pre := (.shiftL i m) :: pre)
                  (rest := rest)
                  (d := d) (s := s) (negSrc := negSrc) (sh := sh)
                  (by simp [hadd])
              rcases ih (σ := σ1) (σ' := σ') (bCur := b1) (n := n)
                  hFitsTail hSafeAddTail hNoTail hrunTail hEnc1 with
                ⟨bNext, hEvalTail, hSOTail⟩
              refine ⟨bNext, ?_, SameOutsideLayout.trans (qs := qs) hSO1 hSOTail⟩
              rw [show annotatePhaseTermsAux k n (.shiftL i m :: ops)
                    = [{ op := .shiftL i m, phaseTerm? := none }]
                        ++ annotatePhaseTermsAux k n ops by
                    simp [annotatePhaseTermsAux]]
              rw [eval_compileAnnotatedOpsToSignedGateAux_append
                    (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
                    (st := dst)
                    (xs := [{ op := .shiftL i m, phaseTerm? := none }])
                    (ys := annotatePhaseTermsAux k n ops)
                    (ψ := qs.ket bCur)]
              simpa [hEval1] using hEvalTail
      | shiftR i m =>
          cases hstep : applyOp? σ (.shiftR i m) with
          | none =>
              simp [run?, hstep] at hrun
          | some σ1 =>
              have hrunTail : run? ops σ1 = some σ' := by simpa [run?, hstep] using hrun
              have hFit1 :
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.xslot j))
                      (evalRowX (qs := qs) src (σ1 j) bRef)) ∧
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.zslot j))
                      (evalRowZ (qs := qs) src (σ1 j) bRef)) := by
                apply hFits; refine ⟨[.shiftR i m], ops, ?_, ?_⟩ <;> simp [run?, hstep]
              rcases encodesFrom_after_shiftR_ket
                  (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
                  (src := src) (dst := dst) (hdisj := hdisj)
                  (i := i) (m := m)
                  (σ := σ) (σ1 := σ1)
                  (bRef := bRef) (bCur := bCur)
                  hstep hEnc hFit1.1 hFit1.2 with
                ⟨b1, hEval1, hEnc1⟩
              have hSO1 :
                  SameOutsideLayout qs dst bCur b1 := by
                exact sameOutside_after_shiftR_single
                  (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
                  (src := src) (dst := dst) (hdisj := hdisj)
                  (i := i) (m := m)
                  (σ := σ) (σ1 := σ1)
                  (bRef := bRef) (bCur := bCur) (b1 := b1)
                  hstep hEnc hFit1.1 hFit1.2 hEval1
              have hFitsTail :
                ∀ {τ : State k},
                  (∃ pre rest, ops = pre ++ rest ∧ run? pre σ1 = some τ) →
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.xslot j))
                      (evalRowX (qs := qs) src (τ j) bRef)) ∧
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.zslot j))
                      (evalRowZ (qs := qs) src (τ j) bRef)) := by
                intro τ hτ
                rcases hτ with ⟨pre, rest, hsplit, hrunpre⟩
                apply hFits
                refine ⟨(.shiftR i m) :: pre, rest, ?_, ?_⟩
                · simp [hsplit]
                · simp [run?, hstep, hrunpre]
              have hSafeAddTail :
                ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
                  ops = pre ++ (.addScaled d s negSrc sh :: rest) →
                  d ≠ s := by
                intro pre rest d s negSrc sh hadd
                exact hSafeAdd
                  (pre := (.shiftR i m) :: pre)
                  (rest := rest)
                  (d := d) (s := s) (negSrc := negSrc) (sh := sh)
                  (by simp [hadd])
              rcases ih (σ := σ1) (σ' := σ') (bCur := b1) (n := n)
                  hFitsTail hSafeAddTail hNoTail hrunTail hEnc1 with
                ⟨bNext, hEvalTail, hSOTail⟩
              refine ⟨bNext, ?_, SameOutsideLayout.trans (qs := qs) hSO1 hSOTail⟩
              rw [show annotatePhaseTermsAux k n (.shiftR i m :: ops)
                    = [{ op := .shiftR i m, phaseTerm? := none }]
                        ++ annotatePhaseTermsAux k n ops by
                    simp [annotatePhaseTermsAux]]
              rw [eval_compileAnnotatedOpsToSignedGateAux_append
                    (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
                    (st := dst)
                    (xs := [{ op := .shiftR i m, phaseTerm? := none }])
                    (ys := annotatePhaseTermsAux k n ops)
                    (ψ := qs.ket bCur)]
              simpa [hEval1] using hEvalTail
      | negate i =>
          cases hstep : applyOp? σ (.negate i) with
          | none =>
              simp [run?, hstep] at hrun
          | some σ1 =>
              have hrunTail : run? ops σ1 = some σ' := by simpa [run?, hstep] using hrun
              have hFit1 :
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.xslot j))
                      (evalRowX (qs := qs) src (σ1 j) bRef)) ∧
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.zslot j))
                      (evalRowZ (qs := qs) src (σ1 j) bRef)) := by
                apply hFits; refine ⟨[.negate i], ops, ?_, ?_⟩ <;> simp [run?, hstep]
              rcases encodesFrom_after_negate_ket
                  (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
                  (src := src) (dst := dst) (hdisj := hdisj)
                  (i := i)
                  (σ := σ) (σ1 := σ1)
                  (bRef := bRef) (bCur := bCur)
                  hstep hEnc hFit1.1 hFit1.2 with
                ⟨b1, hEval1, hEnc1⟩
              have hSO1 :
                  SameOutsideLayout qs dst bCur b1 := by
                exact sameOutside_after_negate_single
                  (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
                  (dst := dst) (hdisj := hdisj)
                  (i := i) (bCur := bCur) (b1 := b1) hEval1
              have hFitsTail :
                ∀ {τ : State k},
                  (∃ pre rest, ops = pre ++ rest ∧ run? pre σ1 = some τ) →
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.xslot j))
                      (evalRowX (qs := qs) src (τ j) bRef)) ∧
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.zslot j))
                      (evalRowZ (qs := qs) src (τ j) bRef)) := by
                intro τ hτ
                rcases hτ with ⟨pre, rest, hsplit, hrunpre⟩
                apply hFits
                refine ⟨(.negate i) :: pre, rest, ?_, ?_⟩
                · simp [hsplit]
                · simp [run?, hstep, hrunpre]
              have hSafeAddTail :
                ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
                  ops = pre ++ (.addScaled d s negSrc sh :: rest) →
                  d ≠ s := by
                intro pre rest d s negSrc sh hadd
                exact hSafeAdd
                  (pre := (.negate i) :: pre)
                  (rest := rest)
                  (d := d) (s := s) (negSrc := negSrc) (sh := sh)
                  (by simp [hadd])
              rcases ih (σ := σ1) (σ' := σ') (bCur := b1) (n := n)
                  hFitsTail hSafeAddTail hNoTail hrunTail hEnc1 with
                ⟨bNext, hEvalTail, hSOTail⟩
              refine ⟨bNext, ?_, SameOutsideLayout.trans (qs := qs) hSO1 hSOTail⟩
              rw [show annotatePhaseTermsAux k n (.negate i :: ops)
                    = [{ op := .negate i, phaseTerm? := none }]
                        ++ annotatePhaseTermsAux k n ops by
                    simp [annotatePhaseTermsAux]]
              rw [eval_compileAnnotatedOpsToSignedGateAux_append
                    (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
                    (st := dst)
                    (xs := [{ op := .negate i, phaseTerm? := none }])
                    (ys := annotatePhaseTermsAux k n ops)
                    (ψ := qs.ket bCur)]
              simpa [hEval1] using hEvalTail
      | addScaled d s negSrc sh =>
          cases hstep : applyOp? σ (.addScaled d s negSrc sh) with
          | none =>
              simp [run?, hstep] at hrun
          | some σ1 =>
              have hrunTail : run? ops σ1 = some σ' := by simpa [run?, hstep] using hrun
              have hds : d ≠ s := by
                have:=hSafeAdd (pre := []) (rest := ops) (sh:=sh) (negSrc:=negSrc) (s:=s) (d:=d)
                simp at this;simp[this]
              have hFit1 :
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.xslot j))
                      (evalRowX (qs := qs) src (σ1 j) bRef)) ∧
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.zslot j))
                      (evalRowZ (qs := qs) src (σ1 j) bRef)) := by
                apply hFits; refine ⟨[.addScaled d s negSrc sh], ops, ?_, ?_⟩ <;> simp [run?, hstep]
              rcases encodesFrom_after_addScaled_ket
                  (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
                  (src := src) (dst := dst) (hdisj := hdisj)
                  (dsti := d) (srci := s) (negSrc := negSrc) (sh := sh)
                  hds
                  (σ := σ) (σ1 := σ1)
                  (bRef := bRef) (bCur := bCur)
                  hstep hEnc hFit1.1 hFit1.2 with
                ⟨b1, hEval1, hEnc1⟩
              have hSO1 :
                  SameOutsideLayout qs dst bCur b1 := by
                exact sameOutside_after_addScaled_single
                  (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
                  (dst := dst) (hdisj := hdisj)
                  (dsti := d) (srci := s) (negSrc := negSrc) (sh := sh)
                  hds
                  (bCur := bCur) (b1 := b1) hEval1
              have hFitsTail :
                ∀ {τ : State k},
                  (∃ pre rest, ops = pre ++ rest ∧ run? pre σ1 = some τ) →
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.xslot j))
                      (evalRowX (qs := qs) src (τ j) bRef)) ∧
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.zslot j))
                      (evalRowZ (qs := qs) src (τ j) bRef)) := by
                intro τ hτ
                rcases hτ with ⟨pre, rest, hsplit, hrunpre⟩
                apply hFits
                refine ⟨(.addScaled d s negSrc sh) :: pre, rest, ?_, ?_⟩
                · simp [hsplit]
                · simp [run?, hstep, hrunpre]
              have hSafeAddTail :
                ∀ {pre rest : Prog k} {d' s' : Fin k} {negSrc' : Bool} {sh' : ℕ},
                  ops = pre ++ (.addScaled d' s' negSrc' sh' :: rest) →
                  d' ≠ s' := by
                intro pre rest d' s' negSrc' sh' hadd
                exact hSafeAdd
                  (pre := (.addScaled d s negSrc sh) :: pre)
                  (rest := rest)
                  (d := d') (s := s') (negSrc := negSrc') (sh := sh')
                  (by simp [hadd])
              rcases ih (σ := σ1) (σ' := σ') (bCur := b1) (n := n)
                  hFitsTail hSafeAddTail hNoTail hrunTail hEnc1 with
                ⟨bNext, hEvalTail, hSOTail⟩
              refine ⟨bNext, ?_, SameOutsideLayout.trans (qs := qs) hSO1 hSOTail⟩
              rw [show annotatePhaseTermsAux k n (.addScaled d s negSrc sh :: ops)
                    = [{ op := .addScaled d s negSrc sh, phaseTerm? := none }]
                        ++ annotatePhaseTermsAux k n ops by
                    simp [annotatePhaseTermsAux]]
              rw [eval_compileAnnotatedOpsToSignedGateAux_append
                    (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
                    (st := dst)
                    (xs := [{ op := .addScaled d s negSrc sh, phaseTerm? := none }])
                    (ys := annotatePhaseTermsAux k n ops)
                    (ψ := qs.ket bCur)]
              simpa [hEval1] using hEvalTail
      | phaseProduct i =>
          exfalso
          exact hNP i (by simp)

/-- No-phase arithmetic runs preserve the encoded symbolic state. -/
lemma encodesFrom_after_noPhase_run_ket_gen_aux
  (qs : QSemantics)
  [RegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ} (hk : 1 < k)
  (phi : Angle)
  (coeff : Fin (q k) → ℚ)
  (src dst : LayoutState k)
  (ops : Prog k)
  (σ σ' : State k)
  (bRef bCur : qs.Basis)
  (n : ℕ)
  (hdisj : LayoutSlotsDisjoint dst)
  (hFits :
    ∀ {τ : State k},
      (∃ pre rest, ops = pre ++ rest ∧ run? pre σ = some τ) →
      (∀ j : Fin k,
        FitsSignedWidth (ExtReg.width (dst.xslot j))
          (evalRowX (qs := qs) src (τ j) bRef)) ∧
      (∀ j : Fin k,
        FitsSignedWidth (ExtReg.width (dst.zslot j))
          (evalRowZ (qs := qs) src (τ j) bRef)))
  (hSafeAdd :
    ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
      ops = pre ++ (.addScaled d s negSrc sh :: rest) →
      d ≠ s)
  (hNP : NoPhase ops)
  (hrun : run? ops σ = some σ')
  (hEnc : EncodesStateFromFits (qs := qs) src dst σ bRef bCur) :
  ∃ bNext : qs.Basis,
    qs.eval
        (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst (annotatePhaseTermsAux k n ops))
        (qs.ket bCur)
      = qs.ket bNext ∧
    EncodesStateFromFits (qs := qs) src dst σ' bRef bNext := by
  induction ops generalizing σ σ' bCur n with
  | nil =>
      have hσ : σ = σ' := by simpa [run?] using hrun
      subst hσ
      refine ⟨bCur, ?_, hEnc⟩
      simp [annotatePhaseTermsAux, compileAnnotatedOpsToSignedGateAux, qs.eval_id]
  | cons op ops ih =>
      have hNoTail : NoPhase ops := by intro i hi; exact hNP i (by simp [hi])
      cases op with
      | shiftL i m =>
          cases hstep : applyOp? σ (.shiftL i m) with
          | none =>
              simp [run?, hstep] at hrun
          | some σ1 =>
              have hrunTail : run? ops σ1 = some σ' := by simpa [run?, hstep] using hrun
              have hFit1 :
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.xslot j))
                      (evalRowX (qs := qs) src (σ1 j) bRef)) ∧
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.zslot j))
                      (evalRowZ (qs := qs) src (σ1 j) bRef)) := by
                apply hFits; refine ⟨[.shiftL i m], ops, ?_, ?_⟩ <;> simp [run?, hstep]
              rcases encodesFrom_after_shiftL_ket
                  (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
                  (src := src) (dst := dst)
                  (hdisj := hdisj)
                  (i := i) (m := m)
                  (σ := σ) (σ1 := σ1)
                  (bRef := bRef) (bCur := bCur)
                  hstep hEnc hFit1.1 hFit1.2 with
                ⟨b1, hEval1, hEnc1⟩
              have hFitsTail :
                ∀ {τ : State k},
                  (∃ pre rest, ops = pre ++ rest ∧ run? pre σ1 = some τ) →
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.xslot j))
                      (evalRowX (qs := qs) src (τ j) bRef)) ∧
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.zslot j))
                      (evalRowZ (qs := qs) src (τ j) bRef)) := by
                intro τ hτ
                rcases hτ with ⟨pre, rest, hsplit, hrunpre⟩
                apply hFits
                refine ⟨(.shiftL i m) :: pre, rest, ?_, ?_⟩
                · simp [hsplit]
                · simp [run?, hstep, hrunpre]
              have hSafeAddTail :
                  ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
                    ops = pre ++ valid_ops.addScaled d s negSrc sh :: rest → d ≠ s := by
                intro pre rest d s negSrc sh hmem
                exact hSafeAdd
                  (pre := valid_ops.shiftL i m :: pre)
                  (rest := rest)
                  (d := d) (s := s) (negSrc := negSrc) (sh := sh)
                  (by simp [hmem])
              rcases ih σ1 σ' b1 n hFitsTail hSafeAddTail hNoTail hrunTail hEnc1 with
                ⟨bNext, hEvalTail, hEncTail⟩
              refine ⟨bNext, ?_, hEncTail⟩
              have hAnn :
                  annotatePhaseTermsAux k n (valid_ops.shiftL i m :: ops) =
                    [{ op := valid_ops.shiftL i m, phaseTerm? := none }] ++
                      annotatePhaseTermsAux k n ops := by simp [annotatePhaseTermsAux]
              rw [hAnn]
              rw [eval_compileAnnotatedOpsToSignedGateAux_append
                    (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
                    (st := dst)
                    (xs := [{ op := valid_ops.shiftL i m, phaseTerm? := none }])
                    (ys := annotatePhaseTermsAux k n ops)
                    (ψ := qs.ket bCur)]
              rw [hEval1]
              exact hEvalTail
      | shiftR i m =>
          cases hstep : applyOp? σ (.shiftR i m) with
          | none =>
              simp [run?, hstep] at hrun
          | some σ1 =>
              have hrunTail : run? ops σ1 = some σ' := by simpa [run?, hstep] using hrun
              have hFit1 :
                  (∀ (j : Fin k), FitsSignedWidth (dst.xslot j).width (evalRowX qs src (σ1 j) bRef)) ∧
                    ∀ (j : Fin k), FitsSignedWidth (dst.zslot j).width (evalRowZ qs src (σ1 j) bRef) := by
                apply hFits; refine ⟨[.shiftR i m], ops, ?_, ?_⟩ <;> simp [run?, hstep]
              rcases encodesFrom_after_shiftR_ket
                  (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
                  (src := src) (dst := dst)
                  (hdisj := hdisj)
                  (i := i) (m := m)
                  (σ := σ) (σ1 := σ1)
                  (bRef := bRef) (bCur := bCur)
                  hstep hEnc hFit1.1 hFit1.2 with
                ⟨b1, hEval1, hEnc1⟩
              have hFitsTail :
                ∀ {τ : State k},
                  (∃ pre rest, ops = pre ++ rest ∧ run? pre σ1 = some τ) →
                    (∀ (j : Fin k), FitsSignedWidth (dst.xslot j).width (evalRowX qs src (τ j) bRef)) ∧
                      ∀ (j : Fin k), FitsSignedWidth (dst.zslot j).width (evalRowZ qs src (τ j) bRef) := by
                intro τ hτ
                rcases hτ with ⟨pre, rest, hsplit, hrunpre⟩
                apply hFits
                refine ⟨.shiftR i m :: pre, rest, ?_, ?_⟩
                · simp [hsplit]
                · simp [run?, hstep, hrunpre]
              have hSafeAddTail :
                ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
                  ops = pre ++ valid_ops.addScaled d s negSrc sh :: rest → d ≠ s := by
                intro pre rest d s negSrc sh hmem
                exact hSafeAdd
                  (pre := .shiftR i m :: pre)
                  (rest := rest)
                  (d := d) (s := s) (negSrc := negSrc) (sh := sh)
                  (by simp [hmem])
              rcases ih σ1 σ' b1 n hFitsTail hSafeAddTail hNoTail hrunTail hEnc1 with
                ⟨bNext, hEvalTail, hEncTail⟩
              refine ⟨bNext, ?_, hEncTail⟩
              have hAnn :
                  annotatePhaseTermsAux k n (.shiftR i m :: ops) =
                    [{ op := .shiftR i m, phaseTerm? := none }] ++
                      annotatePhaseTermsAux k n ops := by simp [annotatePhaseTermsAux]
              rw [hAnn]
              rw [eval_compileAnnotatedOpsToSignedGateAux_append
                    (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
                    (st := dst)
                    (xs := [{ op := .shiftR i m, phaseTerm? := none }])
                    (ys := annotatePhaseTermsAux k n ops)
                    (ψ := qs.ket bCur)]
              rw [hEval1]
              exact hEvalTail
      | negate i =>
          have hstep : applyOp? σ (.negate i) = some (State.negateReg σ i) := by simp [applyOp?, State.negateReg]
          have hrunTail : run? ops (State.negateReg σ i) = some σ' := by simpa [run?, hstep] using hrun
          have hFit1 :
              (∀ (j : Fin k), FitsSignedWidth (dst.xslot j).width (evalRowX qs src ((State.negateReg σ i) j) bRef)) ∧
                ∀ (j : Fin k), FitsSignedWidth (dst.zslot j).width (evalRowZ qs src ((State.negateReg σ i) j) bRef) := by
            apply hFits; refine ⟨[.negate i], ops, ?_, ?_⟩ <;> simp [run?, hstep]
          rcases encodesFrom_after_negate_ket
              (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
              (src := src) (dst := dst)
              (hdisj := hdisj)
              (i := i)
              (σ := σ) (σ1 := State.negateReg σ i)
              (bRef := bRef) (bCur := bCur)
              hstep hEnc hFit1.1 hFit1.2 with
            ⟨b1, hEval1, hEnc1⟩
          have hFitsTail :
            ∀ {τ : State k},
              (∃ pre rest, ops = pre ++ rest ∧ run? pre (State.negateReg σ i) = some τ) →
                (∀ (j : Fin k), FitsSignedWidth (dst.xslot j).width (evalRowX qs src (τ j) bRef)) ∧
                  ∀ (j : Fin k), FitsSignedWidth (dst.zslot j).width (evalRowZ qs src (τ j) bRef) := by
            intro τ hτ
            rcases hτ with ⟨pre, rest, hsplit, hrunpre⟩
            apply hFits
            refine ⟨.negate i :: pre, rest, ?_, ?_⟩
            · simp [hsplit]
            · simp [run?, hstep, hrunpre]
          have hSafeAddTail :
            ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
              ops = pre ++ valid_ops.addScaled d s negSrc sh :: rest → d ≠ s := by
            intro pre rest d s negSrc sh hmem
            exact hSafeAdd
              (pre := .negate i :: pre)
              (rest := rest)
              (d := d) (s := s) (negSrc := negSrc) (sh := sh)
              (by simp [hmem])
          rcases ih (State.negateReg σ i) σ' b1 n hFitsTail hSafeAddTail hNoTail hrunTail hEnc1 with
            ⟨bNext, hEvalTail, hEncTail⟩
          refine ⟨bNext, ?_, hEncTail⟩
          have hAnn :
              annotatePhaseTermsAux k n (.negate i :: ops) =
                [{ op := .negate i, phaseTerm? := none }] ++
                  annotatePhaseTermsAux k n ops := by simp [annotatePhaseTermsAux]
          rw [hAnn]
          rw [eval_compileAnnotatedOpsToSignedGateAux_append
                (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
                (st := dst)
                (xs := [{ op := .negate i, phaseTerm? := none }])
                (ys := annotatePhaseTermsAux k n ops)
                (ψ := qs.ket bCur)]
          rw [hEval1]
          exact hEvalTail
      | addScaled dsti srci negSrc sh =>
          cases hstep : applyOp? σ (.addScaled dsti srci negSrc sh) with
          | none =>
              simp [run?, hstep] at hrun
          | some σ1 =>
              have hrunTail : run? ops σ1 = some σ' := by simpa [run?, hstep] using hrun
              have hFit1 :
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.xslot j))
                      (evalRowX (qs := qs) src (σ1 j) bRef)) ∧
                  (∀ j : Fin k,
                    FitsSignedWidth (ExtReg.width (dst.zslot j))
                      (evalRowZ (qs := qs) src (σ1 j) bRef)) := by
                apply hFits; refine ⟨[.addScaled dsti srci negSrc sh], ops, ?_, ?_⟩ <;> simp [run?, hstep]
              have hds : dsti ≠ srci := by
                exact hSafeAdd
                  (pre := [])
                  (rest := ops)
                  (d := dsti) (s := srci) (negSrc := negSrc) (sh := sh)
                  (by simp)
              rcases encodesFrom_after_addScaled_ket
                  (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
                  (src := src) (dst := dst)
                  (hdisj := hdisj)
                  (dsti := dsti) (srci := srci) (negSrc := negSrc) (sh := sh)
                  (hds := hds)
                  (σ := σ) (σ1 := σ1)
                  (bRef := bRef) (bCur := bCur)
                  hstep hEnc hFit1.1 hFit1.2 with
                ⟨b1, hEval1, hEnc1⟩
              have hFitsTail :
                ∀ {τ : State k},
                  (∃ pre rest, ops = pre ++ rest ∧ run? pre σ1 = some τ) →
                    (∀ (j : Fin k), FitsSignedWidth (dst.xslot j).width (evalRowX qs src (τ j) bRef)) ∧
                      ∀ (j : Fin k), FitsSignedWidth (dst.zslot j).width (evalRowZ qs src (τ j) bRef) := by
                intro τ hτ
                rcases hτ with ⟨pre, rest, hsplit, hrunpre⟩
                apply hFits
                refine ⟨valid_ops.addScaled dsti srci negSrc sh :: pre, rest, ?_, ?_⟩
                · simp [hsplit]
                · simp [run?, hstep, hrunpre]
              have hSafeAddTail :
                ∀ {pre rest : Prog k} {d s : Fin k} {negSrc_1 : Bool} {sh_1 : ℕ},
                  ops = pre ++ valid_ops.addScaled d s negSrc_1 sh_1 :: rest → d ≠ s := by
                intro pre rest d s negSrc_1 sh_1 hmem
                exact hSafeAdd
                  (pre := valid_ops.addScaled dsti srci negSrc sh :: pre)
                  (rest := rest)
                  (d := d) (s := s) (negSrc := negSrc_1) (sh := sh_1)
                  (by simp [hmem])
              rcases ih σ1 σ' b1 n hFitsTail hSafeAddTail hNoTail hrunTail hEnc1 with
                ⟨bNext, hEvalTail, hEncTail⟩
              refine ⟨bNext, ?_, hEncTail⟩
              have hAnn :
                  annotatePhaseTermsAux k n (valid_ops.addScaled dsti srci negSrc sh :: ops) =
                    [{ op := valid_ops.addScaled dsti srci negSrc sh, phaseTerm? := none }] ++
                      annotatePhaseTermsAux k n ops := by simp [annotatePhaseTermsAux]
              rw [hAnn]
              rw [eval_compileAnnotatedOpsToSignedGateAux_append
                    (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
                    (st := dst)
                    (xs := [{ op := valid_ops.addScaled dsti srci negSrc sh, phaseTerm? := none }])
                    (ys := annotatePhaseTermsAux k n ops)
                    (ψ := qs.ket bCur)]
              rw [hEval1]
              exact hEvalTail
      | phaseProduct i =>
          exfalso
          exact hNP i (by simp)

/-- Public wrapper for encoded-state preservation across a no-phase arithmetic run. -/
lemma encodesFrom_after_noPhase_run_ket_gen
  (qs : QSemantics)
  [RegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ} (hk : 1 < k)
  (phi : Angle)
  (coeff : Fin (q k) → ℚ)
  (src dst : LayoutState k)
  (ops : Prog k)
  (σ σ' : State k)
  (bRef bCur : qs.Basis)
  (n : ℕ)
  (hdisj : LayoutSlotsDisjoint dst)
  (hFits :
    ∀ {τ : State k},
      (∃ pre rest, ops = pre ++ rest ∧ run? pre σ = some τ) →
      (∀ j : Fin k,
        FitsSignedWidth (ExtReg.width (dst.xslot j))
          (evalRowX (qs := qs) src (τ j) bRef)) ∧
      (∀ j : Fin k,
        FitsSignedWidth (ExtReg.width (dst.zslot j))
          (evalRowZ (qs := qs) src (τ j) bRef)))
  (hSafeAdd :
    ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
      ops = pre ++ (.addScaled d s negSrc sh :: rest) →
      d ≠ s)
  (hNP : NoPhase ops)
  (hrun : run? ops σ = some σ')
  (hEnc : EncodesStateFromFits (qs := qs) src dst σ bRef bCur) :
  ∃ bNext : qs.Basis,
    qs.eval
        (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst (annotatePhaseTermsAux k n ops))
        (qs.ket bCur)
      = qs.ket bNext ∧
    EncodesStateFromFits (qs := qs) src dst σ' bRef bNext := by
  exact encodesFrom_after_noPhase_run_ket_gen_aux
    (qs := qs) (hk := hk) (phi := phi) (coeff := coeff)
    (src := src) (dst := dst) (ops := ops)
    (σ := σ) (σ' := σ') (bRef := bRef) (bCur := bCur) (n := n)
    hdisj hFits hSafeAdd hNP hrun hEnc

end Shor
