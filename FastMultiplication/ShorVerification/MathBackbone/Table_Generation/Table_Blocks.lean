import FastMultiplication.ShorVerification.MathBackbone.Table_Generation.One_register_synthesis_combined

open List Operations

def SafeProg {k : ℕ} (ops : Prog k) : Prop :=
  ∀ {pre rest : Prog k} {d s : Fin k} {negSrc : Bool} {sh : ℕ},
    ops = pre ++ valid_ops.addScaled d s negSrc sh :: rest →
      d ≠ s

structure ProgConsumesPtsSafe {k : ℕ} (hk : k > 0) (σ : State k) (ops : Prog k) (pts : List Point) : Prop where
  consumes : ProgConsumesPts hk σ ops pts
  safe_add : SafeProg ops

open Operations

/-- A single phase block: some arithmetic with no `phaseProduct`,
    ending right before one `phaseProduct`. -/
structure PhaseBlock {k : ℕ} (hk : k > 0)
    (σ : State k) (pt : Point) where
  i : Fin k
  arith : Prog k
  σmid : State k
  noPhase_pre : NoPhase arith
  run_pre : run? arith σ = some σmid
  match_pt : matchesAt_pointRow_state (k := k) hk σmid i pt = true

/-- The concrete program of one phase block. -/
def PhaseBlock.toProg
  {k : ℕ} {hk : k > 0} {σ : State k} {pt : Point}
  (B : PhaseBlock hk σ pt) : Prog k :=
  B.arith ++ [valid_ops.phaseProduct B.i]

/-- Decomposition into phase blocks, allowing a final no-phase suffix
    once all points have been consumed. -/
inductive BlockDecomposition
    {k : ℕ} (hk : k > 0) :
    State k → Prog k → List Point → Prop
| nil
    (σ σ': State k)
    (tail : Prog k)
    (hNP : NoPhase tail)
    (hrun : run? tail σ = some σ')
    :
    BlockDecomposition hk σ tail []
| cons
    {σ : State k} {pt : Point} {pts : List Point}
    (B : PhaseBlock hk σ pt)
    {ops_rest : Prog k}
    (hrest : BlockDecomposition hk B.σmid ops_rest pts) :
    BlockDecomposition hk σ (B.toProg ++ ops_rest) (pt :: pts)



lemma NoPhase_nil {k : ℕ} : NoPhase ([] : Prog k) := by
  intro i h
  simp at h

lemma NoPhase_append_singleton_of_nonphase
  {k : ℕ} {pre : Prog k} {op : valid_ops k}
  (hpre : NoPhase pre)
  (hop : ∀ i, op ≠ valid_ops.phaseProduct i) :
  NoPhase (pre ++ [op]) := by
  intro i hmem
  rw [List.mem_append] at hmem
  cases hmem with
  | inl hpre_mem =>
      exact hpre i hpre_mem
  | inr hsing =>
      have hop_eq : op = valid_ops.phaseProduct i := by
        simp at hsing
        rw[hsing]
      exact hop i hop_eq

/-- Strengthened helper: accumulate a no-phase prefix `pre` until the next phase. -/
lemma progConsumesPts_has_blockDecomposition_aux
  {k : ℕ} (hk : k > 0) :
  ∀ (ops : Prog k),
    ∀ {σ1 : State k} {pts : List Point},
      ProgConsumesPts hk σ1 ops pts →
      ∀ (σ0 : State k) (pre : Prog k),
        NoPhase pre →
        run? pre σ0 = some σ1 →
        BlockDecomposition hk σ0 (pre ++ ops) pts
| [], σ1, pts, hC, σ0, pre, hNP, hrun => by
    simp [ProgConsumesPts] at hC
    subst hC
    simp
    apply BlockDecomposition.nil (hk := hk) σ0 σ1 pre hNP hrun

| op :: ops, σ1, pts, hC, σ0, pre, hNP, hrun => by
    cases op with
    | shiftL i n =>
        simp [ProgConsumesPts] at hC
        rcases hC with ⟨σ2, hstep, htail⟩
        have hNP' : NoPhase (pre ++ [valid_ops.shiftL i n]) := by
          apply NoPhase_append_singleton_of_nonphase hNP
          intro j h
          cases h
        have hrun' : run? (pre ++ [valid_ops.shiftL i n]) σ0 = some σ2 := by
          simp[run?_append]
          simp [hrun, hstep]
        simpa [List.append_assoc] using
          progConsumesPts_has_blockDecomposition_aux hk ops htail σ0 (pre ++ [valid_ops.shiftL i n]) hNP' hrun'

    | shiftR i n =>
        simp [ProgConsumesPts] at hC
        rcases hC with ⟨σ2, hstep, htail⟩
        have hNP' : NoPhase (pre ++ [valid_ops.shiftR i n]) := by
          apply NoPhase_append_singleton_of_nonphase hNP
          intro j h
          cases h
        have hrun' : run? (pre ++ [valid_ops.shiftR i n]) σ0 = some σ2 := by
          rw [run?_append]
          simp [hrun, hstep]
        simpa [List.append_assoc] using
          progConsumesPts_has_blockDecomposition_aux hk ops htail σ0 (pre ++ [valid_ops.shiftR i n]) hNP' hrun'

    | negate i =>
        simp [ProgConsumesPts] at hC
        rcases hC with ⟨σ2, hstep, htail⟩
        have hNP' : NoPhase (pre ++ [valid_ops.negate i]) := by
          apply NoPhase_append_singleton_of_nonphase hNP
          intro j h
          cases h
        have hrun' : run? (pre ++ [valid_ops.negate i]) σ0 = some σ2 := by
          rw [run?_append]
          simp [hrun, hstep]
        simpa [List.append_assoc] using
          progConsumesPts_has_blockDecomposition_aux hk ops htail σ0 (pre ++ [valid_ops.negate i]) hNP' hrun'

    | addScaled dst src negSrc sh =>
        simp [ProgConsumesPts] at hC
        have hNP' : NoPhase (pre ++ [valid_ops.addScaled dst src negSrc sh]) := by
          apply NoPhase_append_singleton_of_nonphase hNP
          intro j h
          cases h
        have hrun' :
            run? (pre ++ [valid_ops.addScaled dst src negSrc sh]) σ0
              = some (σ1.addScaledReg dst src negSrc sh) := by
          rw [run?_append]
          simp [hrun, applyOp?]

        simpa [List.append_assoc] using
          progConsumesPts_has_blockDecomposition_aux
            (hk := hk) (ops := ops) (σ1 := σ1.addScaledReg dst src negSrc sh) (pts := pts) hC σ0
            (pre ++ [valid_ops.addScaled dst src negSrc sh]) hNP' hrun'


    | phaseProduct i =>
        simp [ProgConsumesPts] at hC
        rcases hC with ⟨pt, ptsTail, hpts, hmatch, htail⟩
        subst hpts
        let B : PhaseBlock hk σ0 pt :=
        { i := i
          arith := pre
          σmid := σ1
          noPhase_pre := hNP
          run_pre := hrun
          match_pt := hmatch }

        have hrest : BlockDecomposition hk B.σmid ops ptsTail := by
          simpa [B] using
            progConsumesPts_has_blockDecomposition_aux hk ops htail σ1 [] NoPhase_nil (by simp [run?])

        simpa [PhaseBlock.toProg, B, List.append_assoc] using
          BlockDecomposition.cons (hk := hk) (B := B) hrest

/-- Main theorem: ordered point-consumption gives a block decomposition. -/
theorem progConsumesPts_has_blockDecomposition
  {k : ℕ} (hk : k > 0)
  (ops : Prog k) (σ : State k) (pts : List Point)
  (hC : ProgConsumesPts hk σ ops pts) :
  BlockDecomposition hk σ ops pts := by
  simpa using
    progConsumesPts_has_blockDecomposition_aux hk ops hC σ [] NoPhase_nil (by simp [run?])



theorem progConsumesPts_implies_phaseProductCoverage
  {k : ℕ} (hk : k > 0) :
  ∀ (ops : Prog k) (σ : State k) (pts : List Point),
    ProgConsumesPts hk σ ops pts →
    PhaseProductCoverage hk ops σ pts := by
  intro ops
  induction ops with
  | nil =>
      intro σ pts hC
      change
        PhaseProductCoverageM
          (M := matchesAt_pointRow_state (k := k) hk) [] σ pts
      simp [ProgConsumesPts] at hC
      subst hC
      exact PhaseProductCoverageM.nil

  | cons op ops ih =>
      intro σ pts hC
      change
        PhaseProductCoverageM
          (M := matchesAt_pointRow_state (k := k) hk) (op :: ops) σ pts

      cases op with
      | shiftL i n =>
          simp [ProgConsumesPts] at hC
          rcases hC with ⟨σ', hstep, htail⟩
          refine PhaseProductCoverageM.step_op
            (M := matchesAt_pointRow_state (k := k) hk)
            (op := valid_ops.shiftL i n)
            (ps := ops)
            (σ := σ)
            (τ := σ')
            (pts := pts)
            ?_ hstep ?_
          · intro j h
            cases h
          · exact ih σ' pts htail

      | shiftR i n =>
          simp [ProgConsumesPts] at hC
          rcases hC with ⟨σ', hstep, htail⟩
          refine PhaseProductCoverageM.step_op
            (M := matchesAt_pointRow_state (k := k) hk)
            (op := valid_ops.shiftR i n)
            (ps := ops)
            (σ := σ)
            (τ := σ')
            (pts := pts)
            ?_ hstep ?_
          · intro j h
            cases h
          · exact ih σ' pts htail

      | negate i =>
          simp [ProgConsumesPts] at hC
          rcases hC with ⟨σ', hstep, htail⟩
          refine PhaseProductCoverageM.step_op
            (M := matchesAt_pointRow_state (k := k) hk)
            (op := valid_ops.negate i)
            (ps := ops)
            (σ := σ)
            (τ := σ')
            (pts := pts)
            ?_ hstep ?_
          · intro j h
            cases h
          · exact ih σ' pts htail

      | addScaled dst src negSrc sh =>
          simp [ProgConsumesPts] at hC
          refine PhaseProductCoverageM.step_op
            (M := matchesAt_pointRow_state (k := k) hk)
            (op := valid_ops.addScaled dst src negSrc sh)
            (ps := ops)
            (σ := σ)
            (τ := σ.addScaledReg dst src negSrc sh)
            (pts := pts)
            ?_ ?_ ?_
          · intro i h
            cases h
          · simp [applyOp?]
          · exact ih (σ.addScaledReg dst src negSrc sh) pts hC

      | phaseProduct i =>
          simp [ProgConsumesPts] at hC
          rcases hC with ⟨pt, ptsTail, hpts, hmatch, htail⟩
          subst hpts
          refine PhaseProductCoverageM.step_phase
            (M := matchesAt_pointRow_state (k := k) hk)
            (i := i)
            (ps := ops)
            (σ := σ)
            (pts := pt :: ptsTail)
            (pts' := ptsTail)
            ?_ ?_
          · simpa using
              (eraseFirstMatch_head_true
                (p := fun q => matchesAt_pointRow_state (k := k) hk σ i q)
                pt ptsTail hmatch)
          · exact ih σ ptsTail htail


theorem phaseProductCoverage_peel_block
  {k : ℕ} (hk : k > 0)
  (ops : Prog k) (σ : State k) (pt : Point) (pts : List Point)
  (hC : ProgConsumesPts hk σ ops (pt::pts)) :
  ∃ (B : PhaseBlock hk σ pt) (ops_rest : Prog k),
    ops = B.toProg ++ ops_rest ∧
    BlockDecomposition hk B.σmid ops_rest pts := by
  have hBD : BlockDecomposition hk σ ops (pt :: pts) :=
    progConsumesPts_has_blockDecomposition hk ops σ (pt :: pts) hC
  cases hBD with
  | cons B hrest =>
      exact ⟨B, _, rfl, hrest⟩
