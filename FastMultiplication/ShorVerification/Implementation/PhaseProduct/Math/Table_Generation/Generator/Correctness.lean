import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Generator.WellFormed
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Core.Coverage

open Operations

namespace Table_Generation

/- The generated point list is the protected canonical point list. -/
theorem generatedPoints_valid (mode : ProductMode) (k : ℕ) (_ : k ≥ 2) :
    ValidPointList mode k (generatedPoints mode k) := by
  rfl

private def targetState (middle₁ middle₂ : Point) : State 4 :=
  fun i =>
    if i = 0 then expectedRow (.int 0)
    else if i = 1 then expectedRow middle₁
    else if i = 2 then expectedRow middle₂
    else expectedRow (.frac 0)

lemma targetFirst_wellFormed : Prog.WellFormed targetFirst := by
  simp [targetFirst, Prog.ADD, Prog.SUB, Prog.SHL, Prog.WellFormed, Prog.OpOK]

lemma targetFirst_noPhase : NoPhase targetFirst := by
  simp [targetFirst, Prog.ADD, Prog.SUB, Prog.SHL, NoPhase]

lemma targetFirst_run :
    run? targetFirst (State.start_state (k := 4)) =
      some (targetState (.int 1) (.int (-1))) := by
  decide

private def phaseFirst : Prog 4 :=
  [valid_ops.phaseProduct 0, valid_ops.phaseProduct 3,
    valid_ops.phaseProduct 1, valid_ops.phaseProduct 2]

lemma phaseFirst_consumes :
    ProgConsumesPts (k := 4) (by decide) (targetState (.int 1) (.int (-1)))
      phaseFirst [.int 0, .frac 0, .int 1, .int (-1)] := by
  have h0 :
      matchesAt_pointRow_state (k := 4) (by decide)
        (targetState (.int 1) (.int (-1))) 0 (.int 0) = true := by
    decide
  have hinf :
      matchesAt_pointRow_state (k := 4) (by decide)
        (targetState (.int 1) (.int (-1))) 3 (.frac 0) = true := by
    decide
  have h1 :
      matchesAt_pointRow_state (k := 4) (by decide)
        (targetState (.int 1) (.int (-1))) 1 (.int 1) = true := by
    decide
  have hm1 :
      matchesAt_pointRow_state (k := 4) (by decide)
        (targetState (.int 1) (.int (-1))) 2 (.int (-1)) = true := by
    decide
  simp [phaseFirst, ProgConsumesPts, h0, hinf, h1, hm1]

lemma phaseFirst_run :
    run? phaseFirst (targetState (.int 1) (.int (-1))) =
      some (targetState (.int 1) (.int (-1))) := by
  decide

lemma returningLayer_consumes
    {p phases : Prog 4} {pts : List Point} {σmid : State 4}
    (hWF : Prog.WellFormed p) (hNP : NoPhase p)
    (hrun : run? p (State.start_state (k := 4)) = some σmid)
    (hphase : ProgConsumesPts (k := 4) (by decide) σmid phases pts)
    (hphaseRun : run? phases σmid = some σmid) :
    ProgConsumesPts (k := 4) (by decide) (State.start_state (k := 4))
      (p ++ phases ++ apply_Op_inverse p) pts := by
  have hbuild :
      ProgConsumesPts (k := 4) (by decide) (State.start_state (k := 4)) p [] :=
    progConsumesPts_of_noPhase_run (k := 4) (by decide) hNP hrun
  have hprefix :
      ProgConsumesPts (k := 4) (by decide) (State.start_state (k := 4))
        (p ++ phases) pts := by
    simpa using
      progConsumesPts_append (k := 4) (by decide)
        (p := p) (q := phases) (σ := State.start_state) (σret := σmid)
        (a := []) (b := pts) hbuild hrun hphase
  have hprefixRun :
      run? (p ++ phases) (State.start_state (k := 4)) = some σmid := by
    simp [run?_append, hrun, hphaseRun]
  have hinverseRun :
      run? (apply_Op_inverse p) σmid = some (State.start_state (k := 4)) :=
    State.run?_inverse_undoes_WF p hWF State.start_state σmid hrun
  have hinverseNP : NoPhase (apply_Op_inverse p) := by
    exact NoPhase_map_inv_of_NoPhase (NoPhase_reverse hNP)
  have hinverse :
      ProgConsumesPts (k := 4) (by decide) σmid (apply_Op_inverse p) [] :=
    progConsumesPts_of_noPhase_run (k := 4) (by decide) hinverseNP hinverseRun
  simpa using
    progConsumesPts_append (k := 4) (by decide)
      (p := p ++ phases) (q := apply_Op_inverse p)
      (σ := State.start_state) (σret := σmid)
      (a := pts) (b := []) hprefix hprefixRun hinverse

lemma returningLayer_run
    {p phases : Prog 4} {σmid : State 4}
    (hWF : Prog.WellFormed p)
    (hrun : run? p (State.start_state (k := 4)) = some σmid)
    (hphaseRun : run? phases σmid = some σmid) :
    run? (p ++ phases ++ apply_Op_inverse p) (State.start_state (k := 4)) =
      some (State.start_state (k := 4)) := by
  have hinverseRun :
      run? (apply_Op_inverse p) σmid = some (State.start_state (k := 4)) :=
    State.run?_inverse_undoes_WF p hWF State.start_state σmid hrun
  simp [run?_append, hrun, hphaseRun, hinverseRun]

lemma targetAtTwo_wellFormed : Prog.WellFormed targetAtTwo := by
  simp [targetAtTwo, Prog.ADD, Prog.SUB, Prog.SHL, Prog.WellFormed, Prog.OpOK]

lemma targetAtTwo_noPhase : NoPhase targetAtTwo := by
  simp [targetAtTwo, Prog.ADD, Prog.SUB, Prog.SHL, NoPhase]

lemma targetAtTwo_run :
    run? targetAtTwo (State.start_state (k := 4)) =
      some (targetState (.int 2) (.int (-2))) := by
  decide

private def phaseAtTwo : Prog 4 :=
  [valid_ops.phaseProduct 1, valid_ops.phaseProduct 2]

lemma phaseAtTwo_consumes :
    ProgConsumesPts (k := 4) (by decide) (targetState (.int 2) (.int (-2)))
      phaseAtTwo [.int 2, .int (-2)] := by
  have h2 :
      matchesAt_pointRow_state (k := 4) (by decide)
        (targetState (.int 2) (.int (-2))) 1 (.int 2) = true := by
    decide
  have hm2 :
      matchesAt_pointRow_state (k := 4) (by decide)
        (targetState (.int 2) (.int (-2))) 2 (.int (-2)) = true := by
    decide
  simp [phaseAtTwo, ProgConsumesPts, h2, hm2]

lemma phaseAtTwo_run :
    run? phaseAtTwo (targetState (.int 2) (.int (-2))) =
      some (targetState (.int 2) (.int (-2))) := by
  decide

lemma targetAtHalf_wellFormed : Prog.WellFormed targetAtHalf := by
  simp [targetAtHalf, Prog.ADD, Prog.SUB, Prog.SHL, Prog.WellFormed, Prog.OpOK]

lemma targetAtHalf_noPhase : NoPhase targetAtHalf := by
  simp [targetAtHalf, Prog.ADD, Prog.SUB, Prog.SHL, NoPhase]

lemma targetAtHalf_run :
    run? targetAtHalf (State.start_state (k := 4)) =
      some (targetState (.frac (-2)) (.frac 2)) := by
  decide

private def phaseAtHalf : Prog 4 :=
  [valid_ops.phaseProduct 2, valid_ops.phaseProduct 1]

lemma phaseAtHalf_consumes :
    ProgConsumesPts (k := 4) (by decide) (targetState (.frac (-2)) (.frac 2))
      phaseAtHalf [.frac 2, .frac (-2)] := by
  have h2 :
      matchesAt_pointRow_state (k := 4) (by decide)
        (targetState (.frac (-2)) (.frac 2)) 2 (.frac 2) = true := by
    decide
  have hm2 :
      matchesAt_pointRow_state (k := 4) (by decide)
        (targetState (.frac (-2)) (.frac 2)) 1 (.frac (-2)) = true := by
    decide
  simp [phaseAtHalf, ProgConsumesPts, h2, hm2]

lemma phaseAtHalf_run :
    run? phaseAtHalf (targetState (.frac (-2)) (.frac 2)) =
      some (targetState (.frac (-2)) (.frac 2)) := by
  decide

lemma targetAtFour_wellFormed : Prog.WellFormed targetAtFour := by
  simp [targetAtFour, Prog.ADD, Prog.SUB, Prog.SHL, Prog.WellFormed, Prog.OpOK]

lemma targetAtFour_noPhase : NoPhase targetAtFour := by
  simp [targetAtFour, Prog.ADD, Prog.SUB, Prog.SHL, NoPhase]

lemma targetAtFour_run :
    run? targetAtFour (State.start_state (k := 4)) =
      some (targetState (.int 4) (.int (-4))) := by
  decide

private def phaseAtFour : Prog 4 :=
  [valid_ops.phaseProduct 1, valid_ops.phaseProduct 2]

lemma phaseAtFour_consumes :
    ProgConsumesPts (k := 4) (by decide) (targetState (.int 4) (.int (-4)))
      phaseAtFour [.int 4, .int (-4)] := by
  have h4 :
      matchesAt_pointRow_state (k := 4) (by decide)
        (targetState (.int 4) (.int (-4))) 1 (.int 4) = true := by
    decide
  have hm4 :
      matchesAt_pointRow_state (k := 4) (by decide)
        (targetState (.int 4) (.int (-4))) 2 (.int (-4)) = true := by
    decide
  simp [phaseAtFour, ProgConsumesPts, h4, hm4]

lemma targetGenerate_consumes :
    ProgConsumesPts (k := 4) (by decide) (State.start_state (k := 4)) targetGenerate
      (canonicalPoints .PhaseTripleProduct 4) := by
  let ptsFirst : List Point := [.int 0, .frac 0, .int 1, .int (-1)]
  let ptsTwo : List Point := [.int 2, .int (-2)]
  let ptsHalf : List Point := [.frac 2, .frac (-2)]
  let ptsFour : List Point := [.int 4, .int (-4)]
  let layerFirst : Prog 4 := targetFirst ++ phaseFirst ++ apply_Op_inverse targetFirst
  let layerTwo : Prog 4 := targetAtTwo ++ phaseAtTwo ++ apply_Op_inverse targetAtTwo
  let layerHalf : Prog 4 := targetAtHalf ++ phaseAtHalf ++ apply_Op_inverse targetAtHalf
  let layerFour : Prog 4 := targetAtFour ++ phaseAtFour
  have hFirst :
      ProgConsumesPts (k := 4) (by decide) State.start_state layerFirst ptsFirst := by
    exact returningLayer_consumes targetFirst_wellFormed targetFirst_noPhase
      targetFirst_run phaseFirst_consumes phaseFirst_run
  have hFirstRun : run? layerFirst State.start_state = some (State.start_state (k := 4)) := by
    exact returningLayer_run targetFirst_wellFormed targetFirst_run phaseFirst_run
  have hTwo :
      ProgConsumesPts (k := 4) (by decide) State.start_state layerTwo ptsTwo := by
    exact returningLayer_consumes targetAtTwo_wellFormed targetAtTwo_noPhase
      targetAtTwo_run phaseAtTwo_consumes phaseAtTwo_run
  have hTwoRun : run? layerTwo State.start_state = some (State.start_state (k := 4)) := by
    exact returningLayer_run targetAtTwo_wellFormed targetAtTwo_run phaseAtTwo_run
  have hHalf :
      ProgConsumesPts (k := 4) (by decide) State.start_state layerHalf ptsHalf := by
    exact returningLayer_consumes targetAtHalf_wellFormed targetAtHalf_noPhase
      targetAtHalf_run phaseAtHalf_consumes phaseAtHalf_run
  have hHalfRun : run? layerHalf State.start_state = some (State.start_state (k := 4)) := by
    exact returningLayer_run targetAtHalf_wellFormed targetAtHalf_run phaseAtHalf_run
  have hFourBuild :
      ProgConsumesPts (k := 4) (by decide) State.start_state targetAtFour [] :=
    progConsumesPts_of_noPhase_run (k := 4) (by decide)
      targetAtFour_noPhase targetAtFour_run
  have hFour :
      ProgConsumesPts (k := 4) (by decide) State.start_state layerFour ptsFour := by
    simpa [layerFour] using
      progConsumesPts_append (k := 4) (by decide)
        (p := targetAtFour) (q := phaseAtFour)
        (σ := State.start_state) (σret := targetState (.int 4) (.int (-4)))
        (a := []) (b := ptsFour) hFourBuild targetAtFour_run phaseAtFour_consumes
  have hFirstTwo :
      ProgConsumesPts (k := 4) (by decide) State.start_state
        (layerFirst ++ layerTwo) (ptsFirst ++ ptsTwo) :=
    progConsumesPts_append (k := 4) (by decide)
      hFirst hFirstRun hTwo
  have hFirstTwoRun :
      run? (layerFirst ++ layerTwo) State.start_state = some (State.start_state (k := 4)) := by
    simp [run?_append, hFirstRun, hTwoRun]
  have hFirstTwoHalf :
      ProgConsumesPts (k := 4) (by decide) State.start_state
        ((layerFirst ++ layerTwo) ++ layerHalf) ((ptsFirst ++ ptsTwo) ++ ptsHalf) :=
    progConsumesPts_append (k := 4) (by decide)
      hFirstTwo hFirstTwoRun hHalf
  have hFirstTwoHalfRun :
      run? ((layerFirst ++ layerTwo) ++ layerHalf) State.start_state =
        some (State.start_state (k := 4)) := by
    rw [run?_append, run?_append, hFirstRun]
    simp [hTwoRun, hHalfRun]
  have hAll :
      ProgConsumesPts (k := 4) (by decide) State.start_state
        (((layerFirst ++ layerTwo) ++ layerHalf) ++ layerFour)
        (((ptsFirst ++ ptsTwo) ++ ptsHalf) ++ ptsFour) :=
    progConsumesPts_append (k := 4) (by decide)
      hFirstTwoHalf hFirstTwoHalfRun hFour
  simpa [targetGenerate, phaseFirst, phaseAtTwo, phaseAtHalf, phaseAtFour,
    layerFirst, layerTwo, layerHalf, layerFour, ptsFirst, ptsTwo, ptsHalf, ptsFour,
    canonicalPoints, ProductMode.pointCount, canonicalPoint, List.append_assoc] using hAll

lemma targetGenerate_safe : SafeProg (k := 4) targetGenerate := by
  apply SafeProg_of_WellFormed
  simp [targetGenerate, targetFirst, targetAtTwo, targetAtHalf, targetAtFour,
    Prog.ADD, Prog.SUB, Prog.SHL, apply_Op_inverse,
    Operations.inv, Prog.WellFormed, Prog.OpOK]

lemma opsForPointWithProduct_wellFormed
    {k : ℕ} (hk : 0 < k) (pt : Point) :
    Prog.WellFormed (opsForPointWithProduct hk pt) := by
  cases pt with
  | int z =>
      change Prog.WellFormed
        (computeLocal2 hk z ++ [valid_ops.phaseProduct (finZero hk)] ++
          apply_Op_inverse (computeLocal2 hk z))
      exact WellFormed_append
        (WellFormed_append (computeLocal2_Valid hk) (by
          simp [Prog.WellFormed, Prog.OpOK]))
        (Prog.apply_Op_inverse_preserves_WF (computeLocal2_Valid hk))
  | frac c =>
      by_cases hc : c = 0
      · simp [opsForPointWithProduct, hc, Prog.WellFormed, Prog.OpOK]
      · simp only [opsForPointWithProduct, hc, ↓reduceDIte]
        exact WellFormed_append
          (WellFormed_append (computeFracLocal2_Valid hk) (by
            simp [Prog.WellFormed, Prog.OpOK]))
          (Prog.apply_Op_inverse_preserves_WF (computeFracLocal2_Valid hk))

lemma genOpsWithProduct_wellFormed
    {k : ℕ} (hk : 0 < k) (pts : List Point) :
    Prog.WellFormed (genOpsWithProduct hk pts) := by
  induction pts with
  | nil => simp [genOpsWithProduct, Prog.WellFormed]
  | cons pt pts ih =>
      rw [genOpsWithProduct]
      exact WellFormed_append (opsForPointWithProduct_wellFormed hk pt) ih

/- The generated program safely consumes a permutation of the canonical points. -/
theorem generate_ProgConsumesPtsSafe (mode : ProductMode) (k : ℕ) (hk : k ≥ 2) :
    ValidPointOrder mode k (generatePointsInOrder mode k hk) ∧
      ProgConsumesPtsSafe (by omega) State.start_state
        (generate mode k hk) (generatePointsInOrder mode k hk) := by
  have horder : ValidPointOrder mode k (generatePointsInOrder mode k hk) := by
    simp [ValidPointOrder, generatePointsInOrder, generatedPoints]
  refine ⟨horder, ?_⟩
  have hkpos : 0 < k := by omega
  cases mode with
  | PhaseProduct =>
      refine ⟨?_, ?_⟩
      · simpa [generate] using
          genOpsWithProduct_ProgConsumesPts hkpos (generatePointsInOrder .PhaseProduct k hk)
      · apply SafeProg_of_WellFormed
        simpa [generate] using
          genOpsWithProduct_wellFormed hkpos (generatePointsInOrder .PhaseProduct k hk)
  | PhaseTripleProduct =>
      by_cases hk4 : k = 4
      · subst k
        refine ⟨?_, ?_⟩
        · simpa [generate, generatePointsInOrder, generatedPoints] using
            targetGenerate_consumes
        · change SafeProg (k := 4) targetGenerate
          exact targetGenerate_safe
      · refine ⟨?_, ?_⟩
        · simpa [generate, hk4] using
            genOpsWithProduct_ProgConsumesPts hkpos
              (generatePointsInOrder .PhaseTripleProduct k hk)
        · apply SafeProg_of_WellFormed
          simpa [generate, hk4] using
            genOpsWithProduct_wellFormed hkpos
              (generatePointsInOrder .PhaseTripleProduct k hk)

end Table_Generation
