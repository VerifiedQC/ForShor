import FastMultiplication.ShorVerification.Implementation.QFT.Defs
import FastMultiplication.ShorVerification.Implementation.QFT.Proofs.LoweringCorrectness.PlanSemantics
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

namespace QFTWorkspaceCleanState
variable {qs : QSemantics} [RegEncoding qs.Basis] {xWork zWork : Reg}
/-! =========================================================
    Section 1: Clean-state closure and custom eliminator
========================================================= -/

theorem ket (b : qs.Basis) (hx : FreshZero xWork b) (hz : FreshZero zWork b) :
    QFTWorkspaceCleanState qs xWork zWork (qs.ket b) := CleanClosure.ket b ⟨hx, hz⟩
theorem add {ψ φ : qs.State} (hψ : QFTWorkspaceCleanState qs xWork zWork ψ)
    (hφ : QFTWorkspaceCleanState qs xWork zWork φ) :
    QFTWorkspaceCleanState qs xWork zWork (ψ + φ) := CleanClosure.add hψ hφ
theorem smul (a : ℂ) {ψ : qs.State} (hψ : QFTWorkspaceCleanState qs xWork zWork ψ) :
    QFTWorkspaceCleanState qs xWork zWork (a • ψ) := CleanClosure.smul a hψ
/-- Custom eliminator so `induction`/`cases` keep the original 2-hypothesis
`ket` shape (`| ket b hx hz`) despite the generic single-predicate closure. -/
@[induction_eliminator, cases_eliminator]
def rec' {motive : (ψ : qs.State) → QFTWorkspaceCleanState qs xWork zWork ψ → Prop}
    (zero : motive 0 QFTWorkspaceCleanState.zero)
    (ket : ∀ (b : qs.Basis) (hx : FreshZero xWork b) (hz : FreshZero zWork b),
        motive (qs.ket b) (QFTWorkspaceCleanState.ket b hx hz))
    (add : ∀ {ψ φ : qs.State} (hψ : QFTWorkspaceCleanState qs xWork zWork ψ)
        (hφ : QFTWorkspaceCleanState qs xWork zWork φ),
        motive ψ hψ → motive φ hφ → motive (ψ + φ) (QFTWorkspaceCleanState.add hψ hφ))
    (smul : ∀ (a : ℂ) {ψ : qs.State} (hψ : QFTWorkspaceCleanState qs xWork zWork ψ),
        motive ψ hψ → motive (a • ψ) (QFTWorkspaceCleanState.smul a hψ))
    {ψ : qs.State} (h : QFTWorkspaceCleanState qs xWork zWork ψ) : motive ψ h := by
  induction h with
  | zero => exact zero
  | ket b hconj => exact ket b hconj.1 hconj.2
  | add hψ hφ ihψ ihφ => exact add hψ hφ ihψ ihφ
  | smul a hψ ih => exact smul a hψ ih
end QFTWorkspaceCleanState

/-! =========================================================
    Section 2: Fresh reserve facts for QFT workspaces
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
    Section 3: Converting QFT cleanliness to phase-product cleanliness
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
    Section 4: Preservation by the middle phase-product subplan
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
    Section 5: Readiness for the unsigned phase-product bridge
========================================================= -/

theorem standardPhaseProdUsingPlan_ready_and_clean
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGatePrimitiveBridge qs]
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
    Section 6: Preservation by recursive QFT calls
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
    Section 7: Readiness derived from explicit work registers
========================================================= -/

theorem standardQFTLoweringPlan_ready_and_clean_explicit
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGatePrimitiveBridge qs]
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

  by_cases hzero : regSize data = 0
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

  · by_cases hone : regSize data = 1
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
      have hlarge : 2 ≤ regSize data := by
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
          (qftPhi (regSize data))
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
                (qftPhi (regSize data))
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
              (qftPhi (regSize data))
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
                  (qftPhi (regSize data))
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

termination_by regSize data
decreasing_by
  ·
    have hhalfPos :
        0 < regSize data / 2 := by
      exact Nat.div_pos (by omega) (by decide)
    have hright :
        regSize data - regSize data / 2 <
          regSize data :=
      Nat.sub_lt (by omega) hhalfPos
    simpa [
      rightReg,
      halfSplitPoint,
      splitM
    ] using hright
  ·
    have hleft :
        regSize data / 2 <
          regSize data :=
      Nat.div_lt_self (by omega) (by decide)
    simpa [
      leftReg,
      halfSplitPoint,
      splitM
    ] using hleft

theorem standardQFTLoweringPlan_ready_and_clean
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGatePrimitiveBridge qs]
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

/-! =========================================================
    Section 8: Reserve plan and the public `evalL_lowerQFT`
========================================================= -/

lemma reserveQFTLoweringPlan_ready_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGatePrimitiveBridge qs]
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
    [LowerGatePrimitiveBridge qs]
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
    [LowerGatePrimitiveBridge qs]
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
