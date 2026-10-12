import FastMultiplication.ShorVerification.Implementation.QFT.Split
import FastMultiplication.ShorVerification.Implementation.QFT.Lowering.Workspace
import FastMultiplication.ShorVerification.Implementation.QFT.Lowering.Plan
import FastMultiplication.ShorVerification.Implementation.QFT.Lowering.PlanBuilders
import FastMultiplication.ShorVerification.Implementation.QFT.Proofs.Lowering.PlanSemantics
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Coefficients
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Workspace
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Gates.Macros
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Lowering.Plan
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Lowering.PlanBuilders
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Spec.Cleanliness
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Spec.Readiness
import FastMultiplication.ShorVerification.Implementation.Shared.States
import FastMultiplication.ShorVerification.Implementation.Shared.Registers
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.MacroSemantics
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.Lowering.PlanReadiness.RecursiveReadiness

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
open Operations

universe u

namespace QFTWorkspaceCleanState
variable {qs : QSemantics} [RegEncoding qs.Basis] {xWork zWork : Reg}
/-! =========================================================
    Clean-state closure and custom eliminator
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
    Fresh reserve facts for QFT workspaces
========================================================= -/

lemma freshFor_of_freshZero_reserve
    {Basis : Type u} [RegEncoding Basis] (e : ExtReg) (n : ℕ) (b : Basis)
    (hzero : FreshZero e.reserve b) :
    e.FreshFor n b := by
  unfold ExtReg.FreshFor
  apply FreshZero.of_subset (e.newBits n) e.reserve b ?_ hzero
  intro q hq
  exact List.mem_of_mem_take hq

lemma freshFor_grow_capacity_of_freshZero_reserve
    {Basis : Type u} [RegEncoding Basis] (e : ExtReg) (n : ℕ) (b : Basis)
    (hzero : FreshZero e.reserve b) :
    (e.grow n).FreshFor (e.grow n).capacity b := by
  unfold ExtReg.FreshFor
  apply FreshZero.of_subset ((e.grow n).newBits (e.grow n).capacity) e.reserve b ?_ hzero
  intro q hq
  have hqReserve : q ∈ (e.grow n).reserve.qubits := List.mem_of_mem_take hq
  apply List.mem_of_mem_drop
  simpa [ExtReg.grow, ExtReg.remainingReserve, Reg.drop] using hqReserve

/-! =========================================================
    Converting QFT cleanliness to phase-product cleanliness
========================================================= -/

lemma QFTWorkspaceCleanState.phaseCleanState
    (qs : QSemantics) [RegEncoding qs.Basis] {x z xWork zWork : Reg}
    (ws : Gate.PhaseProdWorkspace x z)
    (hxReserve : ws.xReserve = xWork) (hzReserve : ws.zReserve = zWork)
    {ψ : qs.State} (hclean : QFTWorkspaceCleanState qs xWork zWork ψ) :
    Gate.PhaseProdWorkspace.CleanState qs ws ψ := by
  induction hclean with
  | zero =>
      exact CleanClosure.zero
  | ket b hx hz =>
      apply CleanClosure.ket
      constructor
      · apply freshFor_of_freshZero_reserve
        simpa [Gate.PhaseProdWorkspace.xExt, ExtReg.withReserve, hxReserve] using hx
      · apply freshFor_of_freshZero_reserve
        simpa [Gate.PhaseProdWorkspace.zExt, ExtReg.withReserve, hzReserve] using hz
  | add hψ hφ ihψ ihφ =>
      exact CleanClosure.add ihψ ihφ
  | smul a hψ ihψ =>
      exact CleanClosure.smul a ihψ

lemma QFTWorkspaceCleanState.signedCleanState
    (qs : QSemantics) [RegEncoding qs.Basis] {x z xWork zWork : Reg}
    (ws : Gate.PhaseProdWorkspace x z)
    (hxReserve : ws.xReserve = xWork) (hzReserve : ws.zReserve = zWork)
    {ψ : qs.State} (hclean : QFTWorkspaceCleanState qs xWork zWork ψ) :
    RecursiveWorkspaceCleanState qs (ws.xExt.grow 1) (ws.zExt.grow 1) ψ := by
  induction hclean with
  | zero =>
      exact CleanClosure.zero
  | ket b hx hz =>
      apply CleanClosure.ket
      constructor
      · exact freshFor_grow_capacity_of_freshZero_reserve ws.xExt 1 b
          (by simpa [Gate.PhaseProdWorkspace.xExt, ExtReg.withReserve, hxReserve] using hx)
      · exact freshFor_grow_capacity_of_freshZero_reserve ws.zExt 1 b
          (by simpa [Gate.PhaseProdWorkspace.zExt, ExtReg.withReserve, hzReserve] using hz)
  | add hψ hφ ihψ ihφ =>
      exact CleanClosure.add ihψ ihφ
  | smul a hψ ihψ =>
      exact CleanClosure.smul a ihψ

/-! =========================================================
    Preservation by the middle phase-product subplan
========================================================= -/

lemma eval_PhaseProdUsing_preserves_QFTWorkspaceCleanState
    (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs] (phi : Angle)
    {x z xWork zWork : Reg} (ws : Gate.PhaseProdWorkspace x z)
    (hxReserve : ws.xReserve = xWork) (hzReserve : ws.zReserve = zWork)
    {ψ : qs.State} (hclean : QFTWorkspaceCleanState qs xWork zWork ψ) :
    QFTWorkspaceCleanState qs xWork zWork (qs.eval (Gate.PhaseProdUsing phi x z ws) ψ) := by
  induction hclean with
  | zero =>
      rw [qs.eval_zero]
      exact QFTWorkspaceCleanState.zero
  | ket b hx hz =>
      have hwsClean : ws.Clean b := by
        constructor
        · apply freshFor_of_freshZero_reserve
          simpa [Gate.PhaseProdWorkspace.xExt, ExtReg.withReserve, hxReserve] using hx
        · apply freshFor_of_freshZero_reserve
          simpa [Gate.PhaseProdWorkspace.zExt, ExtReg.withReserve, hzReserve] using hz
      rw [GateSemanticsFacts.eval_PhaseProdUsing_ket qs phi x z ws b hwsClean]
      exact QFTWorkspaceCleanState.smul _ (QFTWorkspaceCleanState.ket b hx hz)
  | add hψ hφ ihψ ihφ =>
      rw [qs.eval_add]
      exact QFTWorkspaceCleanState.add ihψ ihφ
  | smul a hψ ihψ =>
      rw [qs.eval_smul]
      exact QFTWorkspaceCleanState.smul a ihψ

/-! =========================================================
    Readiness for the unsigned phase-product bridge
========================================================= -/

theorem Policy.phaseProdUsingPlan_ready_and_clean
    (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]
    (P : ShorLoweringPolicy) (hP : P.Admissible) (phi : Angle) {x z xWork zWork : Reg}
    (ws : Gate.PhaseProdWorkspace x z)
    (hxReserve : ws.xReserve = xWork) (hzReserve : ws.zReserve = zWork) (ψ : qs.State)
    (hstatic : Policy.WorkspaceOK P (ws.xExt.grow 1) (ws.zExt.grow 1))
    (hclean : QFTWorkspaceCleanState qs xWork zWork ψ) :
    let plan := Policy.phaseProdUsingPlan P phi ws hstatic
    PhaseLoweringReady qs plan ψ
      ∧
    QFTWorkspaceCleanState qs xWork zWork
      (LowerGateClass.evalL (qs := qs) (lowerGateRec plan) ψ) := by
  dsimp only

  let signedPlan :=
    Policy.signedPlan P phi (ws.xExt.grow 1) (ws.zExt.grow 1) hstatic

  have hsignedClean : RecursiveWorkspaceCleanState qs (ws.xExt.grow 1) (ws.zExt.grow 1) ψ :=
    QFTWorkspaceCleanState.signedCleanState qs ws hxReserve hzReserve hclean

  have hsigned :
      PhaseLoweringReady qs signedPlan ψ
        ∧
      RecursiveWorkspaceCleanState qs (ws.xExt.grow 1) (ws.zExt.grow 1)
        (LowerGateClass.evalL (qs := qs) (lowerGateRec signedPlan) ψ) := by
    exact Policy.signedPlan_ready_and_clean qs P hP phi
      (ws.xExt.grow 1) (ws.zExt.grow 1) ψ hstatic hsignedClean

  have hready :
      PhaseLoweringReady qs (Policy.phaseProdUsingPlan P phi ws hstatic) ψ := by
    simpa [Policy.phaseProdUsingPlan, signedPlan,
      PhaseLoweringReady, lowerGateRec,
      LowerGateClass.evalL_zeroExtend, ExtensionSemantics.eval_zeroExtend] using hsigned.1

  constructor
  · exact hready
  ·
    have heval :
        LowerGateClass.evalL (qs := qs)
            (lowerGateRec (Policy.phaseProdUsingPlan P phi ws hstatic)) ψ
          =
        qs.eval (Gate.PhaseProdUsing phi x z ws) ψ := by
      exact evalL_lowerGateRec_correct (qs := qs) hP
        (Policy.phaseProdUsingPlan P phi ws hstatic) ψ hready

    rw [heval]
    exact eval_PhaseProdUsing_preserves_QFTWorkspaceCleanState
      qs phi ws hxReserve hzReserve hclean

/-! =========================================================
    Preservation by recursive QFT calls
========================================================= -/

lemma eval_QFT_preserves_QFTWorkspaceCleanState
    (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs]
    (data xWork zWork : Reg) {ψ : qs.State}
    (hxDisjoint : Disjoint data xWork) (hzDisjoint : Disjoint data zWork)
    (hclean : QFTWorkspaceCleanState qs xWork zWork ψ) :
    QFTWorkspaceCleanState qs xWork zWork (qs.eval (Gate.QFT (ExtReg.ofReg data)) ψ) := by
  induction hclean with
  | zero =>
      rw [qs.eval_zero]
      exact QFTWorkspaceCleanState.zero
  | ket b hx hz =>
      classical
      rw [QFTSemantics.eval_QFT_ket]
      apply QFTWorkspaceCleanState.smul
      let f : Fin (2 ^ (ExtReg.ofReg data).width) → qs.State :=
        fun y =>
          qftPhase (2 ^ (ExtReg.ofReg data).width) (ExtReg.toNat (ExtReg.ofReg data) b) y.1
            •
          qs.ket (RegEncoding.writeNat data y.1 b)
      have hterm :
          ∀ y : Fin (2 ^ (ExtReg.ofReg data).width),
            QFTWorkspaceCleanState qs xWork zWork (f y) := by
        intro y
        apply QFTWorkspaceCleanState.smul
        apply QFTWorkspaceCleanState.ket
        · unfold FreshZero at hx ⊢
          rw [RegEncoding.toNat_left_write_right xWork data (Disjoint.symm hxDisjoint) b y.1]
          exact hx
        · unfold FreshZero at hz ⊢
          rw [RegEncoding.toNat_left_write_right zWork data (Disjoint.symm hzDisjoint) b y.1]
          exact hz
      have hsum :
          ∀ s : Finset (Fin (2 ^ (ExtReg.ofReg data).width)),
            QFTWorkspaceCleanState qs xWork zWork (∑ y ∈ s, f y) := by
        intro s
        induction s using Finset.induction_on with
        | empty =>
            simpa using (QFTWorkspaceCleanState.zero : QFTWorkspaceCleanState qs xWork zWork 0)
        | @insert y s hy ih =>
            rw [Finset.sum_insert hy]
            exact QFTWorkspaceCleanState.add (hterm y) ih
      simpa using hsum Finset.univ
  | add hψ hφ ihψ ihφ =>
      rw [qs.eval_add]
      exact QFTWorkspaceCleanState.add ihψ ihφ
  | smul a hψ ihψ =>
      rw [qs.eval_smul]
      exact QFTWorkspaceCleanState.smul a ihψ

/-! =========================================================
    Readiness derived from explicit work registers
========================================================= -/

theorem Policy.qftPlan_ready_and_clean_explicit
    (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]
    (P : ShorLoweringPolicy) (hP : P.Admissible) (data xWork zWork : Reg) (ψ : qs.State)
    (hstatic : Policy.QFTWorkspaceOK P data xWork zWork)
    (hclean : QFTWorkspaceCleanState qs xWork zWork ψ) :
    let plan := Policy.qftPlan P data xWork zWork hstatic
    QFTLoweringReady qs plan ψ
      ∧
    QFTWorkspaceCleanState qs xWork zWork
      (LowerGateClass.evalL (qs := qs) (lowerQFTPlan plan) ψ) := by
  dsimp only

  by_cases hzero : regSize data = 0
  ·
    have hready :
        QFTLoweringReady qs (Policy.qftPlan P data xWork zWork hstatic) ψ := by
      simp [Policy.qftPlan, hzero, QFTLoweringReady]

    constructor
    · exact hready
    ·
      have heval :=
        evalL_lowerQFTPlan (qs := qs) hP
          (plan := Policy.qftPlan P data xWork zWork hstatic) (ψ := ψ) hready
      rw [heval]
      exact eval_QFT_preserves_QFTWorkspaceCleanState qs data xWork zWork
        hstatic.data_x_disjoint hstatic.data_z_disjoint hclean

  · by_cases hone : regSize data = 1
    ·
      have hready :
          QFTLoweringReady qs (Policy.qftPlan P data xWork zWork hstatic) ψ := by
        simp [Policy.qftPlan, hone, QFTLoweringReady]

      constructor
      · exact hready
      ·
        have heval :=
          evalL_lowerQFTPlan (qs := qs) hP
            (plan := Policy.qftPlan P data xWork zWork hstatic) (ψ := ψ) hready
        rw [heval]
        exact eval_QFT_preserves_QFTWorkspaceCleanState qs data xWork zWork
          hstatic.data_x_disjoint hstatic.data_z_disjoint hclean

    ·
      have hlarge : 2 ≤ regSize data := by omega

      let ws : Gate.PhaseProdWorkspace (leftReg data) (rightReg data) :=
        hstatic.phaseWorkspace hlarge

      have hphaseStatic : Policy.WorkspaceOK P (ws.xExt.grow 1) (ws.zExt.grow 1) := by
        simpa [ws] using hstatic.policySignedWorkspaceOK hlarge

      have hright :=
        Policy.qftPlan_ready_and_clean_explicit qs P hP (rightReg data) xWork zWork ψ
          (hstatic.right hlarge) hclean

      have hphase :=
        Policy.phaseProdUsingPlan_ready_and_clean qs P hP (qftPhi (regSize data)) ws rfl rfl
          (LowerGateClass.evalL (qs := qs)
            (lowerQFTPlan (Policy.qftPlan P (rightReg data) xWork zWork
              (hstatic.right hlarge))) ψ)
          hphaseStatic hright.2

      have hleft :=
        Policy.qftPlan_ready_and_clean_explicit qs P hP (leftReg data) xWork zWork
          (LowerGateClass.evalL (qs := qs)
            (lowerGateRec (Policy.phaseProdUsingPlan P (qftPhi (regSize data)) ws
              hphaseStatic))
            (LowerGateClass.evalL (qs := qs)
              (lowerQFTPlan (Policy.qftPlan P (rightReg data) xWork zWork
                (hstatic.right hlarge))) ψ))
          (hstatic.left hlarge) hphase.2

      have hphaseClean : Gate.PhaseProdWorkspace.CleanState qs ws ψ := by
        exact QFTWorkspaceCleanState.phaseCleanState qs ws rfl rfl hclean

      have hready :
          QFTLoweringReady qs (Policy.qftPlan P data xWork zWork hstatic) ψ := by
        unfold Policy.qftPlan
        simp only [hzero, hone, ↓reduceDIte]
        change
          Gate.PhaseProdWorkspace.CleanState qs ws ψ
            ∧
          QFTLoweringReady qs
            (Policy.qftPlan P (rightReg data) xWork zWork (hstatic.right hlarge))
            ψ
            ∧
          PhaseLoweringReady qs
            (Policy.phaseProdUsingPlan P (qftPhi (regSize data)) ws hphaseStatic)
            (LowerGateClass.evalL (qs := qs)
              (lowerQFTPlan (Policy.qftPlan P (rightReg data) xWork zWork
                (hstatic.right hlarge))) ψ)
            ∧
          QFTLoweringReady qs
            (Policy.qftPlan P (leftReg data) xWork zWork (hstatic.left hlarge))
            (LowerGateClass.evalL (qs := qs)
              (lowerGateRec (Policy.phaseProdUsingPlan P (qftPhi (regSize data)) ws
                hphaseStatic))
              (LowerGateClass.evalL (qs := qs)
                (lowerQFTPlan (Policy.qftPlan P (rightReg data) xWork zWork
                  (hstatic.right hlarge))) ψ))
        exact And.intro hphaseClean (And.intro hright.1 (And.intro hphase.1 hleft.1))

      constructor
      · exact hready
      ·
        have heval :=
          evalL_lowerQFTPlan (qs := qs) hP
            (plan := Policy.qftPlan P data xWork zWork hstatic) (ψ := ψ) hready
        rw [heval]
        exact eval_QFT_preserves_QFTWorkspaceCleanState qs data xWork zWork
          hstatic.data_x_disjoint hstatic.data_z_disjoint hclean

termination_by regSize data
decreasing_by
  ·
    have hhalfPos : 0 < regSize data / 2 := by
      exact Nat.div_pos (by omega) (by decide)
    have hright : regSize data - regSize data / 2 < regSize data :=
      Nat.sub_lt (by omega) hhalfPos
    simpa [rightReg, halfSplitPoint, splitM] using hright
  ·
    have hleft : regSize data / 2 < regSize data :=
      Nat.div_lt_self (by omega) (by decide)
    simpa [leftReg, halfSplitPoint, splitM] using hleft

theorem Policy.qftPlan_ready_and_clean
    (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]
    (P : ShorLoweringPolicy) (hP : P.Admissible) (r : ExtReg) (ψ : qs.State)
    (hworkspace : Policy.QFTWorkspaceStateOK qs P r ψ) :
    let plan := Policy.reserveQftPlan P r hworkspace.static
    QFTLoweringReady qs plan ψ
      ∧
    QFTWorkspaceCleanState qs (Policy.qftXWork P r) (Policy.qftZWork P r)
      (LowerGateClass.evalL (qs := qs) (lowerQFTPlan plan) ψ) := by
  exact Policy.qftPlan_ready_and_clean_explicit qs P hP r.active
    (Policy.qftXWork P r) (Policy.qftZWork P r) ψ
    hworkspace.static.explicitWorkspace hworkspace.clean

/-! =========================================================
    Reserve plan and the public `evalL_lowerQFT`
========================================================= -/

lemma Policy.reserveQftPlan_ready_ket
    (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]
    (P : ShorLoweringPolicy) (hP : P.Admissible) (r : ExtReg) (b : qs.Basis)
    (hstatic : Policy.QFTReserveOK P r)
    (hx : FreshZero (Policy.qftXWork P r) b) (hz : FreshZero (Policy.qftZWork P r) b) :
    QFTLoweringReady qs (Policy.reserveQftPlan P r hstatic) (qs.ket b) := by
  let hworkspace : Policy.QFTWorkspaceStateOK qs P r (qs.ket b) :=
    { static := hstatic
      clean := QFTWorkspaceCleanState.ket b hx hz }

  exact (Policy.qftPlan_ready_and_clean qs P hP r (qs.ket b) hworkspace).1

lemma Policy.reserveQftPlan_preserves_clean_of_ready
    (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]
    (P : ShorLoweringPolicy) (hP : P.Admissible) (r : ExtReg) (ψ : qs.State)
    (hstatic : Policy.QFTReserveOK P r)
    (hclean : QFTWorkspaceCleanState qs (Policy.qftXWork P r) (Policy.qftZWork P r) ψ)
    (_hready : QFTLoweringReady qs (Policy.reserveQftPlan P r hstatic) ψ) :
    QFTWorkspaceCleanState qs (Policy.qftXWork P r) (Policy.qftZWork P r)
      (LowerGateClass.evalL (qs := qs)
        (lowerQFTPlan (Policy.reserveQftPlan P r hstatic)) ψ) := by
  let hworkspace : Policy.QFTWorkspaceStateOK qs P r ψ :=
    { static := hstatic
      clean := hclean }

  exact (Policy.qftPlan_ready_and_clean qs P hP r ψ hworkspace).2

theorem Policy.evalL_lowerQFT
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (P : ShorLoweringPolicy)
    (hP : P.Admissible)
    (r : ExtReg)
    (ψ : qs.State)
    (hworkspace : Policy.QFTWorkspaceStateOK qs P r ψ) :
    LowerGateClass.evalL (qs := qs) (Policy.lowerQFT P r hworkspace.static) ψ
      =
    qs.eval (Gate.QFT r) ψ := by
  unfold Policy.lowerQFT

  have hready : QFTLoweringReady qs (Policy.reserveQftPlan P r hworkspace.static) ψ :=
    (Policy.qftPlan_ready_and_clean qs P hP r ψ hworkspace).1

  have hcore :
      LowerGateClass.evalL (qs := qs)
          (lowerQFTPlan (Policy.reserveQftPlan P r hworkspace.static)) ψ
        =
      qs.eval (Gate.QFT (ExtReg.ofReg r.active)) ψ := by
    exact evalL_lowerQFTPlan (qs := qs) hP
      (plan := Policy.reserveQftPlan P r hworkspace.static) (ψ := ψ) hready

  calc
    LowerGateClass.evalL (qs := qs)
        (lowerQFTPlan (Policy.reserveQftPlan P r hworkspace.static)) ψ
        =
      qs.eval (Gate.QFT (ExtReg.ofReg r.active)) ψ := hcore

    _ =
      qs.eval (Gate.QFT r) ψ := by
        exact eval_QFT_eq_of_active_eq (qs := qs) (ExtReg.ofReg r.active) r rfl ψ

/-- The fixed-table spelling, unchanged in statement: the policy theorem at
the constant policy. -/
theorem evalL_lowerQFT
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (r : ExtReg)
    (ψ : qs.State)
    {pts : List Point} {hpts : pts.length = q k}
    (hworkspace : QFTWorkspaceStateOK qs ops r ψ)
    (hInterp : GoodToomCookPoints k pts hpts)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops pts)
    (hRun : run? ops State.start_state = some State.start_state) :
    LowerGateClass.evalL (qs := qs) (lowerQFT k hk ops pts hpts r hworkspace.static) ψ
      =
    qs.eval (Gate.QFT r) ψ := by
  -- Proved through the policy machinery at `constPolicy`, but keeping the
  -- `ops`-keyed workspace pools, so no transport along the pool bridges is
  -- needed (they sit in a dependent position inside the plan's type).
  have hP : (ShorLoweringPolicy.constPolicy
      (⟨k, hk, pts, hpts, ops⟩ : ToomCookTable)).Admissible :=
    ShorLoweringPolicy.constPolicy_admissible (T := ⟨k, hk, pts, hpts, ops⟩)
      ⟨hInterp, hC, hRun⟩
  unfold lowerQFT
  have hready :
      QFTLoweringReady qs (reserveQFTLoweringPlan k hk ops pts hpts r hworkspace.static) ψ := by
    unfold reserveQFTLoweringPlan
    exact (Policy.qftPlan_ready_and_clean_explicit qs _ hP r.active
      (qftXWork ops r) (qftZWork ops r) ψ
      (Policy.qftWorkspaceOK_const_iff.mpr hworkspace.static.explicitWorkspace)
      hworkspace.clean).1
  have hcore :
      LowerGateClass.evalL (qs := qs)
          (lowerQFTPlan (reserveQFTLoweringPlan k hk ops pts hpts r hworkspace.static)) ψ
        =
      qs.eval (Gate.QFT (ExtReg.ofReg r.active)) ψ :=
    evalL_lowerQFTPlan (qs := qs) hP
      (plan := reserveQFTLoweringPlan k hk ops pts hpts r hworkspace.static) (ψ := ψ) hready
  rw [hcore]
  exact eval_QFT_eq_of_active_eq (qs := qs) (ExtReg.ofReg r.active) r rfl ψ

end Shor
