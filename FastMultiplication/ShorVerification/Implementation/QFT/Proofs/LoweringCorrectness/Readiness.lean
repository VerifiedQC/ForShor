import FastMultiplication.ShorVerification.Implementation.QFT.Proofs.Lowering
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Defs
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.GateLevelCorrectness.GateSemanticsLemmas
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.LoweringCorrectness.PlanReadiness

/-!
# QFT Lowering Readiness and Correctness

This file proves that the canonical QFT workspace selected in `Workspace.lean`
is clean enough to execute the recursive QFT lowering plan, and that the
public `lowerQFT` circuit evaluates like the high-level `Gate.QFT`.

The proof has three layers:

1. convert fresh-zero reserve facts into the phase-product clean-state
   hypotheses needed by the middle split gate;
2. show QFT and phase-product subcircuits preserve the chosen workspace pools;
3. assemble readiness for the standard recursive plan and expose
   `evalL_lowerQFT`.
-/

namespace Shor

open Gate

universe u

/-! =========================================================
    Section 1: Fresh reserve facts for QFT workspaces

    These lemmas turn the public clean-state predicate for the two QFT
    workspace pools into the `FreshFor` facts required by the phase-product
    lowerer that appears in the middle of a QFT split.
========================================================= -/

lemma freshFor_of_freshZero_reserve
    {Basis : Type u}
    [RegEncoding Basis]
    (e : ExtReg)
    (n : ℕ)
    (b : Basis)
    (hzero : FreshZero e.reserve b) :
    e.FreshFor n b := by
  unfold ExtReg.FreshFor
  apply FreshZero.of_subset
    (e.newBits n)
    e.reserve
    b
    ?_
    hzero
  intro q hq
  exact List.mem_of_mem_take hq


lemma freshFor_grow_capacity_of_freshZero_reserve
    {Basis : Type u}
    [RegEncoding Basis]
    (e : ExtReg)
    (n : ℕ)
    (b : Basis)
    (hzero : FreshZero e.reserve b) :
    (e.grow n).FreshFor (e.grow n).capacity b := by
  unfold ExtReg.FreshFor
  apply FreshZero.of_subset
    ((e.grow n).newBits (e.grow n).capacity)
    e.reserve
    b
    ?_
    hzero
  intro q hq
  have hqReserve :
      q ∈ (e.grow n).reserve.qubits :=
    List.mem_of_mem_take hq
  apply List.mem_of_mem_drop
  simpa [
    ExtReg.grow,
    ExtReg.remainingReserve,
    Reg.drop
  ] using hqReserve


/-! =========================================================
    Section 2: Converting QFT cleanliness to phase-product cleanliness

    A split QFT invokes an unsigned phase product. These lemmas reinterpret
    the two QFT workspace pools as the clean workspace required by that
    phase-product subplan.
========================================================= -/

lemma QFTWorkspaceCleanState.phaseCleanState
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {x z xWork zWork : Reg}
    (ws : Gate.PhaseProdWorkspace x z)
    (hxReserve : ws.xReserve = xWork)
    (hzReserve : ws.zReserve = zWork)
    {ψ : qs.State}
    (hclean :
      QFTWorkspaceCleanState
        qs xWork zWork ψ) :
    Gate.PhaseProdWorkspace.CleanState
      qs ws ψ := by
  induction hclean with
  | zero =>
      exact CleanClosure.zero
  | ket b hx hz =>
      apply CleanClosure.ket
      constructor
      · apply freshFor_of_freshZero_reserve
        simpa [
          Gate.PhaseProdWorkspace.xExt,
          ExtReg.withReserve,
          hxReserve
        ] using hx
      · apply freshFor_of_freshZero_reserve
        simpa [
          Gate.PhaseProdWorkspace.zExt,
          ExtReg.withReserve,
          hzReserve
        ] using hz
  | add hψ hφ ihψ ihφ =>
      exact
        CleanClosure.add
          ihψ ihφ
  | smul a hψ ihψ =>
      exact
        CleanClosure.smul
          a ihψ


lemma QFTWorkspaceCleanState.signedCleanState
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {x z xWork zWork : Reg}
    (ws : Gate.PhaseProdWorkspace x z)
    (hxReserve : ws.xReserve = xWork)
    (hzReserve : ws.zReserve = zWork)
    {ψ : qs.State}
    (hclean :
      QFTWorkspaceCleanState
        qs xWork zWork ψ) :
    RecursiveWorkspaceCleanState
      qs
      (ws.xExt.grow 1)
      (ws.zExt.grow 1)
      ψ := by
  induction hclean with
  | zero =>
      exact CleanClosure.zero
  | ket b hx hz =>
      apply CleanClosure.ket
      constructor
      · exact
          freshFor_grow_capacity_of_freshZero_reserve
            ws.xExt
            1
            b
            (by
              simpa [
                Gate.PhaseProdWorkspace.xExt,
                ExtReg.withReserve,
                hxReserve
              ] using hx)
      · exact
          freshFor_grow_capacity_of_freshZero_reserve
            ws.zExt
            1
            b
            (by
              simpa [
                Gate.PhaseProdWorkspace.zExt,
                ExtReg.withReserve,
                hzReserve
              ] using hz)
  | add hψ hφ ihψ ihφ =>
      exact
        CleanClosure.add
          ihψ ihφ
  | smul a hψ ihψ =>
      exact
        CleanClosure.smul
          a ihψ


/-! =========================================================
    Section 3: Preservation by the middle phase-product subplan

    The QFT split uses a phase product between the right and left recursive
    QFT calls. These lemmas prove that executing that phase product keeps the
    same QFT workspace pools clean.
========================================================= -/

lemma eval_PhaseProdUsing_preserves_QFTWorkspaceCleanState
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (phi : ℝ)
    {x z xWork zWork : Reg}
    (ws : Gate.PhaseProdWorkspace x z)
    (hxReserve : ws.xReserve = xWork)
    (hzReserve : ws.zReserve = zWork)
    {ψ : qs.State}
    (hclean :
      QFTWorkspaceCleanState
        qs xWork zWork ψ) :
    QFTWorkspaceCleanState
      qs xWork zWork
      (qs.eval
        (Gate.PhaseProdUsing phi x z ws)
        ψ) := by
  induction hclean with
  | zero =>
      rw [qs.eval_zero]
      exact QFTWorkspaceCleanState.zero
  | ket b hx hz =>
      have hwsClean : ws.Clean b := by
        constructor
        · apply freshFor_of_freshZero_reserve
          simpa [
            Gate.PhaseProdWorkspace.xExt,
            ExtReg.withReserve,
            hxReserve
          ] using hx
        · apply freshFor_of_freshZero_reserve
          simpa [
            Gate.PhaseProdWorkspace.zExt,
            ExtReg.withReserve,
            hzReserve
          ] using hz
      rw [
        GateSemanticsFacts.eval_PhaseProdUsing_ket
          qs phi x z ws b hwsClean
      ]
      exact
        QFTWorkspaceCleanState.smul
          _
          (QFTWorkspaceCleanState.ket b hx hz)
  | add hψ hφ ihψ ihφ =>
      rw [qs.eval_add]
      exact QFTWorkspaceCleanState.add ihψ ihφ
  | smul a hψ ihψ =>
      rw [qs.eval_smul]
      exact QFTWorkspaceCleanState.smul a ihψ


/-! =========================================================
    Section 4: Readiness for the unsigned phase-product bridge

    `standardPhaseProdUsingPlan` is the QFT-facing wrapper around signed
    phase-product lowering. This section proves that the wrapper is ready and
    preserves the QFT workspace clean-state invariant.
========================================================= -/

theorem standardPhaseProdUsingPlan_ready_and_clean
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGateGateBridge qs]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (phi : ℝ)
    {x z xWork zWork : Reg}
    (ws : Gate.PhaseProdWorkspace x z)
    (hxReserve : ws.xReserve = xWork)
    (hzReserve : ws.zReserve = zWork)
    (ψ : qs.State)
    (hstatic :
      SignedRecursiveWorkspaceOK
        ops
        (ws.xExt.grow 1)
        (ws.zExt.grow 1))
    (hclean :
      QFTWorkspaceCleanState
        qs xWork zWork ψ)
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
      standardPhaseProdUsingPlan
        k hk ops phi ws hstatic

    PhaseLoweringReady qs plan ψ
      ∧
    QFTWorkspaceCleanState
      qs xWork zWork
      (LowerGateClass.evalL
        (qs := qs)
        (lowerGateRec plan)
        ψ) := by
  dsimp only

  let signedPlan :=
    standardSignedPhaseLoweringPlan
      k
      hk
      phi
      (ws.xExt.grow 1)
      (ws.zExt.grow 1)
      ops
      hstatic

  have hsignedClean :
      RecursiveWorkspaceCleanState
        qs
        (ws.xExt.grow 1)
        (ws.zExt.grow 1)
        ψ :=
    QFTWorkspaceCleanState.signedCleanState
      qs ws hxReserve hzReserve hclean

  have hsigned :
      PhaseLoweringReady qs signedPlan ψ
        ∧
      RecursiveWorkspaceCleanState
        qs
        (ws.xExt.grow 1)
        (ws.zExt.grow 1)
        (LowerGateClass.evalL
          (qs := qs)
          (lowerGateRec signedPlan)
          ψ) := by
    exact
      standardSignedPhaseLoweringPlan_ready_and_clean
        qs
        k
        hk
        phi
        (ws.xExt.grow 1)
        (ws.zExt.grow 1)
        ops
        ψ
        hstatic
        hsignedClean
        hC
        hRun

  have hready :
      PhaseLoweringReady
        qs
        (standardPhaseProdUsingPlan
          k hk ops phi ws hstatic)
        ψ := by
    simpa [
      standardPhaseProdUsingPlan,
      signedPlan,
      PhaseLoweringReady,
      lowerGateRec,
      LowerGateClass.evalL_zeroExtend,
      ExtensionSemantics.eval_zeroExtend
    ] using hsigned.1

  constructor
  · exact hready
  ·
    have hInterp :
        GoodToomCookPoints
          k
          (genInterpolationPoints k)
          (generatedInterpolationPoints_length k) := by
      simpa using genInterpolationPoints_good k

    have heval :
        LowerGateClass.evalL
            (qs := qs)
            (lowerGateRec
              (standardPhaseProdUsingPlan
                k hk ops phi ws hstatic))
            ψ
          =
        qs.eval
          (Gate.PhaseProdUsing phi x z ws)
          ψ := by
      exact
        evalL_lowerGateRec_correct
          (qs := qs)
          (hInterp := hInterp)
          (hC := hC)
          (hRun := hRun)
          (standardPhaseProdUsingPlan
            k hk ops phi ws hstatic)
          ψ
          hready

    rw [heval]
    exact
      eval_PhaseProdUsing_preserves_QFTWorkspaceCleanState
        qs phi ws hxReserve hzReserve hclean


/-! =========================================================
    Section 5: Preservation by recursive QFT calls

    A QFT only writes its active data register. If the selected workspace pools
    are disjoint from that data register, QFT evaluation preserves their
    fresh-zero invariant.
========================================================= -/

lemma eval_QFT_preserves_QFTWorkspaceCleanState
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (data xWork zWork : Reg)
    {ψ : qs.State}
    (hxDisjoint : Disjoint data xWork)
    (hzDisjoint : Disjoint data zWork)
    (hclean :
      QFTWorkspaceCleanState
        qs xWork zWork ψ) :
    QFTWorkspaceCleanState
      qs xWork zWork
      (qs.eval
        (Gate.QFT (ExtReg.ofReg data))
        ψ) := by
  induction hclean with
  | zero =>
      rw [qs.eval_zero]
      exact QFTWorkspaceCleanState.zero
  | ket b hx hz =>
      classical
      rw [QFTSemantics.eval_QFT_ket]
      apply QFTWorkspaceCleanState.smul
      let f :
          Fin (2 ^ (ExtReg.ofReg data).width) →
            qs.State :=
        fun y =>
          qftPhase
              (2 ^ (ExtReg.ofReg data).width)
              (ExtReg.toNat (ExtReg.ofReg data) b)
              y.1
            •
          qs.ket
            (RegEncoding.writeNat data y.1 b)
      have hterm :
          ∀ y : Fin (2 ^ (ExtReg.ofReg data).width),
            QFTWorkspaceCleanState
              qs xWork zWork
              (f y) := by
        intro y
        apply QFTWorkspaceCleanState.smul
        apply QFTWorkspaceCleanState.ket
        · unfold FreshZero at hx ⊢
          rw [
            RegEncoding.toNat_left_write_right
              xWork
              data
              (Disjoint.symm hxDisjoint)
              b
              y.1
          ]
          exact hx
        · unfold FreshZero at hz ⊢
          rw [
            RegEncoding.toNat_left_write_right
              zWork
              data
              (Disjoint.symm hzDisjoint)
              b
              y.1
          ]
          exact hz
      have hsum :
          ∀ s : Finset
              (Fin (2 ^ (ExtReg.ofReg data).width)),
            QFTWorkspaceCleanState
              qs xWork zWork
              (∑ y ∈ s, f y) := by
        intro s
        induction s using Finset.induction_on with
        | empty =>
            simpa using
              (QFTWorkspaceCleanState.zero :
                QFTWorkspaceCleanState
                  qs xWork zWork 0)
        | @insert y s hy ih =>
            rw [Finset.sum_insert hy]
            exact
              QFTWorkspaceCleanState.add
                (hterm y)
                ih
      simpa using hsum Finset.univ
  | add hψ hφ ihψ ihφ =>
      rw [qs.eval_add]
      exact QFTWorkspaceCleanState.add ihψ ihφ
  | smul a hψ ihψ =>
      rw [qs.eval_smul]
      exact QFTWorkspaceCleanState.smul a ihψ


/-! =========================================================
    Section 6: Readiness derived from explicit work registers

    This is the main recursive readiness proof. It assumes the caller has
    already selected concrete `xWork` and `zWork` registers satisfying
    `QFTWorkspaceOK`, then proves the standard plan is ready and remains clean.
========================================================= -/

theorem standardQFTLoweringPlan_ready_and_clean_explicit
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGateGateBridge qs]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (data xWork zWork : Reg)
    (ψ : qs.State)
    (hstatic :
      QFTWorkspaceOK
        ops data xWork zWork)
    (hclean :
      QFTWorkspaceCleanState
        qs xWork zWork ψ)
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
      standardQFTLoweringPlan
        k hk ops data xWork zWork hstatic

    QFTLoweringReady qs plan ψ
      ∧
    QFTWorkspaceCleanState
      qs xWork zWork
      (LowerGateClass.evalL
        (qs := qs)
        (lowerQFTPlan plan)
        ψ) := by
  dsimp only

  by_cases hzero : Reg.width data = 0
  ·
    have hready :
        QFTLoweringReady
          qs
          (standardQFTLoweringPlan
            k hk ops data xWork zWork hstatic)
          ψ := by
      simp [standardQFTLoweringPlan, hzero, QFTLoweringReady]

    constructor
    · exact hready
    ·
      have heval :=
        evalL_lowerQFTPlan
          (qs := qs)
          (hk := hk)
          (ops := ops)
          (hC := hC)
          (hRun := hRun)
          (plan :=
            standardQFTLoweringPlan
              k hk ops data xWork zWork hstatic)
          (ψ := ψ)
          hready
      rw [heval]
      exact
        eval_QFT_preserves_QFTWorkspaceCleanState
          qs data xWork zWork
          hstatic.data_x_disjoint
          hstatic.data_z_disjoint
          hclean

  · by_cases hone : Reg.width data = 1
    ·
      have hready :
          QFTLoweringReady
            qs
            (standardQFTLoweringPlan
              k hk ops data xWork zWork hstatic)
            ψ := by
        simp [
          standardQFTLoweringPlan,
          hone,
          QFTLoweringReady
        ]

      constructor
      · exact hready
      ·
        have heval :=
          evalL_lowerQFTPlan
            (qs := qs)
            (hk := hk)
            (ops := ops)
            (hC := hC)
            (hRun := hRun)
            (plan :=
              standardQFTLoweringPlan
                k hk ops data xWork zWork hstatic)
            (ψ := ψ)
            hready
        rw [heval]
        exact
          eval_QFT_preserves_QFTWorkspaceCleanState
            qs data xWork zWork
            hstatic.data_x_disjoint
            hstatic.data_z_disjoint
            hclean

    ·
      have hlarge : 2 ≤ Reg.width data := by
        omega

      let ws :
          Gate.PhaseProdWorkspace
            (leftReg data)
            (rightReg data) :=
        hstatic.phaseWorkspace hlarge

      have hphaseStatic :
          SignedRecursiveWorkspaceOK
            ops
            (ws.xExt.grow 1)
            (ws.zExt.grow 1) := by
        simpa [ws] using
          hstatic.signedWorkspaceOK hlarge

      have hright :=
        standardQFTLoweringPlan_ready_and_clean_explicit
          qs
          k
          hk
          ops
          (rightReg data)
          xWork
          zWork
          ψ
          (hstatic.right hlarge)
          hclean
          hC
          hRun

      have hphase :=
        standardPhaseProdUsingPlan_ready_and_clean
          qs
          k
          hk
          ops
          (qftPhi (Reg.width data))
          ws
          rfl
          rfl
          (LowerGateClass.evalL
            (qs := qs)
            (lowerQFTPlan
              (standardQFTLoweringPlan
                k hk ops
                (rightReg data)
                xWork
                zWork
                (hstatic.right hlarge)))
            ψ)
          hphaseStatic
          hright.2
          hC
          hRun

      have hleft :=
        standardQFTLoweringPlan_ready_and_clean_explicit
          qs
          k
          hk
          ops
          (leftReg data)
          xWork
          zWork
          (LowerGateClass.evalL
            (qs := qs)
            (lowerGateRec
              (standardPhaseProdUsingPlan
                k
                hk
                ops
                (qftPhi (Reg.width data))
                ws
                hphaseStatic))
            (LowerGateClass.evalL
              (qs := qs)
              (lowerQFTPlan
                (standardQFTLoweringPlan
                  k hk ops
                  (rightReg data)
                  xWork
                  zWork
                  (hstatic.right hlarge)))
              ψ))
          (hstatic.left hlarge)
          hphase.2
          hC
          hRun

      have hphaseClean :
          Gate.PhaseProdWorkspace.CleanState
            qs ws ψ := by
        exact
          QFTWorkspaceCleanState.phaseCleanState
            qs ws rfl rfl hclean

      have hready :
          QFTLoweringReady
            qs
            (standardQFTLoweringPlan
              k hk ops data xWork zWork hstatic)
            ψ := by
        unfold standardQFTLoweringPlan
        simp only [hzero, hone, ↓reduceDIte]
        change
          Gate.PhaseProdWorkspace.CleanState qs ws ψ
            ∧
          QFTLoweringReady
            qs
            (standardQFTLoweringPlan
              k hk ops
              (rightReg data)
              xWork
              zWork
              (hstatic.right hlarge))
            ψ
            ∧
          PhaseLoweringReady
            qs
            (standardPhaseProdUsingPlan
              k hk ops
              (qftPhi (Reg.width data))
              ws
              hphaseStatic)
            (LowerGateClass.evalL
              (qs := qs)
              (lowerQFTPlan
                (standardQFTLoweringPlan
                  k hk ops
                  (rightReg data)
                  xWork
                  zWork
                  (hstatic.right hlarge)))
              ψ)
            ∧
          QFTLoweringReady
            qs
            (standardQFTLoweringPlan
              k hk ops
              (leftReg data)
              xWork
              zWork
              (hstatic.left hlarge))
            (LowerGateClass.evalL
              (qs := qs)
              (lowerGateRec
                (standardPhaseProdUsingPlan
                  k hk ops
                  (qftPhi (Reg.width data))
                  ws
                  hphaseStatic))
              (LowerGateClass.evalL
                (qs := qs)
                (lowerQFTPlan
                  (standardQFTLoweringPlan
                    k hk ops
                    (rightReg data)
                    xWork
                    zWork
                    (hstatic.right hlarge)))
                ψ))
        exact
          And.intro
            hphaseClean
            (And.intro
              hright.1
              (And.intro
                hphase.1
                hleft.1))

      constructor
      · exact hready
      ·
        have heval :=
          evalL_lowerQFTPlan
            (qs := qs)
            (hk := hk)
            (ops := ops)
            (hC := hC)
            (hRun := hRun)
            (plan :=
              standardQFTLoweringPlan
                k hk ops data xWork zWork hstatic)
            (ψ := ψ)
            hready
        rw [heval]
        exact
          eval_QFT_preserves_QFTWorkspaceCleanState
            qs data xWork zWork
            hstatic.data_x_disjoint
            hstatic.data_z_disjoint
            hclean

termination_by Reg.width data
decreasing_by
  ·
    have hhalfPos :
        0 < Reg.width data / 2 := by
      exact Nat.div_pos (by omega) (by decide)
    have hright :
        Reg.width data - Reg.width data / 2 <
          Reg.width data :=
      Nat.sub_lt (by omega) hhalfPos
    simpa [
      rightReg,
      halfSplitPoint,
      splitM
    ] using hright
  ·
    have hleft :
        Reg.width data / 2 <
          Reg.width data :=
      Nat.div_lt_self (by omega) (by decide)
    simpa [
      leftReg,
      halfSplitPoint,
      splitM
    ] using hleft


/-! =========================================================
    Section 7: Public readiness and correctness for `lowerQFT`

    The public API hides the concrete workspace registers. It derives them
    from `r.reserve`, packages readiness helpers, and exposes the final
    semantic correctness theorem used by whole-program lowering.
========================================================= -/

theorem standardQFTLoweringPlan_ready_and_clean
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGateGateBridge qs]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (r : ExtReg)
    (ψ : qs.State)
    (hworkspace :
      QFTWorkspaceStateOK qs ops r ψ)
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
      reserveQFTLoweringPlan
        k hk ops r hworkspace.static

    QFTLoweringReady qs plan ψ
      ∧
    QFTWorkspaceCleanState
      qs
      (qftXWork ops r)
      (qftZWork ops r)
      (LowerGateClass.evalL
        (qs := qs)
        (lowerQFTPlan plan)
        ψ) := by
  exact
    standardQFTLoweringPlan_ready_and_clean_explicit
      qs
      k
      hk
      ops
      r.active
      (qftXWork ops r)
      (qftZWork ops r)
      ψ
      hworkspace.static.explicitWorkspace
      hworkspace.clean
      hC
      hRun


lemma reserveQFTLoweringPlan_ready_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGateGateBridge qs]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (r : ExtReg)
    (b : qs.Basis)
    (hstatic : QFTReserveOK ops r)
    (hx : FreshZero (qftXWork ops r) b)
    (hz : FreshZero (qftZWork ops r) b)
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
    QFTLoweringReady
      qs
      (reserveQFTLoweringPlan
        k hk ops r hstatic)
      (qs.ket b) := by
  let hworkspace :
      QFTWorkspaceStateOK
        qs ops r (qs.ket b) :=
    {
      static := hstatic
      clean :=
        QFTWorkspaceCleanState.ket
          b hx hz
    }

  exact
    (standardQFTLoweringPlan_ready_and_clean
      qs k hk ops r (qs.ket b)
      hworkspace hC hRun).1


lemma reserveQFTLoweringPlan_preserves_clean_of_ready
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGateGateBridge qs]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (r : ExtReg)
    (ψ : qs.State)
    (hstatic : QFTReserveOK ops r)
    (hclean :
      QFTWorkspaceCleanState
        qs
        (qftXWork ops r)
        (qftZWork ops r)
        ψ)
    (_hready :
      QFTLoweringReady qs (reserveQFTLoweringPlan k hk ops r hstatic) ψ)
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
    QFTWorkspaceCleanState
      qs
      (qftXWork ops r)
      (qftZWork ops r)
      (LowerGateClass.evalL
        (qs := qs)
        (lowerQFTPlan
          (reserveQFTLoweringPlan
            k hk ops r hstatic))
        ψ) := by
  let hworkspace :
      QFTWorkspaceStateOK qs ops r ψ :=
    {
      static := hstatic
      clean := hclean
    }

  exact
    (standardQFTLoweringPlan_ready_and_clean
      qs k hk ops r ψ
      hworkspace hC hRun).2


theorem evalL_lowerQFT
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGateGateBridge qs]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (r : ExtReg)
    (ψ : qs.State)
    (hworkspace : QFTWorkspaceStateOK qs ops r ψ)
    (hC : ProgConsumesPtsSafe (k := k) (by omega)
        State.start_state ops (genInterpolationPoints k))
    (hRun : run? ops State.start_state = some State.start_state) :
    LowerGateClass.evalL (qs := qs) (lowerQFT k hk ops r hworkspace.static) ψ
      =
    qs.eval (Gate.QFT r) ψ := by
  unfold lowerQFT

  have hready :
      QFTLoweringReady
        qs
        (reserveQFTLoweringPlan
          k hk ops r hworkspace.static)
        ψ :=
    (standardQFTLoweringPlan_ready_and_clean
      qs k hk ops r ψ
      hworkspace hC hRun).1

  have hcore :
      LowerGateClass.evalL
          (qs := qs)
          (lowerQFTPlan
            (reserveQFTLoweringPlan
              k hk ops r hworkspace.static))
          ψ
        =
      qs.eval
        (Gate.QFT (ExtReg.ofReg r.active))
        ψ := by
    exact
      evalL_lowerQFTPlan
        (qs := qs)
        (hk := hk)
        (ops := ops)
        (hC := hC)
        (hRun := hRun)
        (plan :=
          reserveQFTLoweringPlan
            k hk ops r hworkspace.static)
        (ψ := ψ)
        hready

  calc
    LowerGateClass.evalL
        (qs := qs)
        (lowerQFTPlan
          (reserveQFTLoweringPlan
            k hk ops r hworkspace.static))
        ψ
        =
      qs.eval
        (Gate.QFT (ExtReg.ofReg r.active))
        ψ := hcore

    _ =
      qs.eval (Gate.QFT r) ψ := by
        exact
          eval_QFT_eq_of_active_eq
            (qs := qs)
            (ExtReg.ofReg r.active)
            r
            rfl
            ψ

end Shor
