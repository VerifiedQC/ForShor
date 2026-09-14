import FastMultiplication.ShorVerification.Implementation.Shor.Spec.Setup
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Lowering
import FastMultiplication.ShorVerification.Implementation.QFT.Proofs.Lowering.Readiness
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.Workspace
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.Steps
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.CmpLtNW
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Workspace
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Gates.Macros
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Spec.Cleanliness
import FastMultiplication.ShorVerification.Implementation.Semantics.GateSemanticsLemmas
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.MacroSemantics
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness.Static
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness.Sequencing
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness.Primitives
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness.Init
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness.Step1

/-!
# Step 2 Readiness

Step 2 makes the carry bit active, swaps the phase-product operand order,
and preserves `ShorLoweringCleanState`.
-/

namespace Shor
open Gate
open Classical


/-- The second and third clean registers play symmetric roles. -/
private theorem threeRegsCleanState_swap23
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    {r₁ r₂ r₃ : Reg}
    {ψ : qs.State}
    (hclean :
      ThreeRegsCleanState
        qs r₁ r₂ r₃ ψ) :
    ThreeRegsCleanState
      qs r₁ r₃ r₂ ψ := by
  induction hclean with
  | zero =>
      exact ThreeRegsCleanState.zero

  | ket b h₁ h₂ h₃ =>
      exact
        ThreeRegsCleanState.ket
          b h₁ h₃ h₂

  | add hψ hφ ihψ ihφ =>
      exact
        ThreeRegsCleanState.add
          ihψ
          ihφ

  | smul a hψ ihψ =>
      exact
        ThreeRegsCleanState.smul
          a
          ihψ

/-- Growing a register never adds physical qubits it did not already own. -/
private lemma ownedQubits_grow_subset
    (e : ExtReg)
    (n : ℕ)
    {q : ℕ}
    (hq :
      q ∈ (e.grow n).ownedQubits) :
    q ∈ e.ownedQubits := by
  rw [ExtReg.ownedQubits, List.mem_append] at hq ⊢

  rcases hq with hqActive | hqReserve

  · have hqSplit :
        q ∈
          e.active.qubits ++
            (List.take n e.reserve.qubits) := by
      simpa [
        ExtReg.grow,
        Reg.append,
        ExtReg.newBits,
        Reg.take
      ] using hqActive

    rcases List.mem_append.mp hqSplit with
      hqOld | hqNew
    · exact Or.inl hqOld
    · exact
        Or.inr
          (List.mem_of_mem_take hqNew)

  · have hqDrop :
        q ∈ List.drop n e.reserve.qubits := by
      simpa [
        ExtReg.grow,
        ExtReg.remainingReserve,
        Reg.drop
      ] using hqReserve

    exact
      Or.inr
        (List.mem_of_mem_drop hqDrop)

/-- Owned-disjointness survives growing the register on the right. -/
private lemma ownedDisjoint_grow_right
    {y e : ExtReg}
    (n : ℕ)
    (h :
      ExtReg.OwnedDisjoint y e) :
    ExtReg.OwnedDisjoint y (e.grow n) := by
  rw [ExtReg.OwnedDisjoint, List.disjoint_left] at h ⊢

  intro q hqy hqGrow

  exact
    h hqy
      (ownedQubits_grow_subset e n hqGrow)

private theorem eval_QFT_preserves_threeRegsCleanState
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (r : ExtReg)
    (r₁ r₂ r₃ : Reg)
    {ψ : qs.State}
    (h₁r :
      Disjoint r₁ r.active)
    (h₂r :
      Disjoint r₂ r.active)
    (h₃r :
      Disjoint r₃ r.active)
    (hclean :
      ThreeRegsCleanState
        qs r₁ r₂ r₃ ψ) :
    ThreeRegsCleanState
      qs r₁ r₂ r₃
      (qs.eval (Gate.QFT r) ψ) := by
  classical

  induction hclean with
  | zero =>
      rw [qs.eval_zero]
      exact ThreeRegsCleanState.zero

  | ket b h₁ h₂ h₃ =>
      rw [QFTSemantics.eval_QFT_ket]

      let f :
          Fin (2 ^ r.width) →
            qs.State :=
        fun t =>
          (qftPhase
            (2 ^ r.width)
            (ExtReg.toNat r b)
            t.1) •
            qs.ket
              (RegEncoding.writeNat
                r.active
                t.1
                b)

      have hterm :
          ∀ t : Fin (2 ^ r.width),
            ThreeRegsCleanState
              qs r₁ r₂ r₃
              (f t) := by
        intro t

        apply ThreeRegsCleanState.smul
        apply ThreeRegsCleanState.ket

        · unfold FreshZero at h₁ ⊢
          rw [
            RegEncoding.toNat_left_write_right
              r₁
              r.active
              h₁r
              b
              t.1
          ]
          exact h₁

        · unfold FreshZero at h₂ ⊢
          rw [
            RegEncoding.toNat_left_write_right
              r₂
              r.active
              h₂r
              b
              t.1
          ]
          exact h₂

        · unfold FreshZero at h₃ ⊢
          rw [
            RegEncoding.toNat_left_write_right
              r₃
              r.active
              h₃r
              b
              t.1
          ]
          exact h₃

      have hsum :
          ∀ s : Finset (Fin (2 ^ r.width)),
            ThreeRegsCleanState
              qs r₁ r₂ r₃
              (∑ t ∈ s, f t) := by
        intro s

        induction s using Finset.induction_on with
        | empty =>
            simpa using
              (ThreeRegsCleanState.zero :
                ThreeRegsCleanState
                  qs r₁ r₂ r₃ 0)

        | @insert t s ht ih =>
            rw [Finset.sum_insert ht]

            exact
              ThreeRegsCleanState.add
                (hterm t)
                ih

      exact
        ThreeRegsCleanState.smul
          _
          (by simpa [f] using hsum Finset.univ)

  | add hψ hφ ihψ ihφ =>
      rw [qs.eval_add]
      exact
        ThreeRegsCleanState.add
          ihψ
          ihφ

  | smul a hψ ihψ =>
      rw [qs.eval_smul]
      exact
        ThreeRegsCleanState.smul
          a
          ihψ

private theorem gateWorkspaceCleanState_PhaseProdUsing_of_threeRegsClean
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    {lowering : ShorLoweringSetup}
    {r₁ r₂ r₃ : Reg}
    {x z : Reg}
    (φ : Angle)
    (ws : Gate.PhaseProdWorkspace x z)
    (hxReserve :
      ws.xExt.reserve = r₂)
    (hzReserve :
      ws.zExt.reserve = r₃)
    (hworkspace :
      GateWorkspaceOK
        lowering.ops
        (Gate.PhaseProdUsing
          φ x z ws))
    (ψ : qs.State)
    (hclean :
      ThreeRegsCleanState
        qs r₁ r₂ r₃ ψ) :
    GateWorkspaceCleanState
      qs
      lowering.k
      lowering.hk
      lowering.ops
      (Gate.PhaseProdUsing
        φ x z ws)
      hworkspace
      ψ := by
  have hrecursive :
      RecursiveWorkspaceCleanState
        qs
        (ws.xExt.grow 1)
        (ws.zExt.grow 1)
        ψ :=
    threeRegsCleanState_to_grownRecursiveWorkspaceCleanState
      ws
      hxReserve
      hzReserve
      hclean

  simpa [
    Gate.PhaseProdUsing,
    GateWorkspaceCleanState,
    lowerGate,
    LowerGateClass.evalL_zeroExtend,
    ExtensionSemantics.eval_zeroExtend
  ] using hrecursive

private theorem eval_PhaseProdUsing_preserves_threeRegsCleanState
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {r₁ r₂ r₃ : Reg}
    (φ : Angle)
    {x z : Reg}
    (ws : Gate.PhaseProdWorkspace x z)
    (hxReserve :
      ws.xExt.reserve = r₂)
    (hzReserve :
      ws.zExt.reserve = r₃)
    {ψ : qs.State}
    (hclean :
      ThreeRegsCleanState
        qs r₁ r₂ r₃ ψ) :
    ThreeRegsCleanState
      qs r₁ r₂ r₃
      (qs.eval
        (Gate.PhaseProdUsing
          φ x z ws)
        ψ) := by
  induction hclean with
  | zero =>
      rw [qs.eval_zero]
      exact ThreeRegsCleanState.zero

  | ket b h₁ h₂ h₃ =>
      have hxZero :
          FreshZero ws.xExt.reserve b := by
        simpa only [hxReserve] using h₂

      have hzZero :
          FreshZero ws.zExt.reserve b := by
        simpa only [hzReserve] using h₃

      have hwsClean :
          ws.Clean b := by
        constructor
        · exact
            freshFor_of_freshZero_reserve
              ws.xExt
              1
              b
              hxZero

        · exact
            freshFor_of_freshZero_reserve
              ws.zExt
              1
              b
              hzZero

      rw [
        GateSemanticsFacts.eval_PhaseProdUsing_ket
          qs
          φ
          x
          z
          ws
          b
          hwsClean
      ]

      exact
        ThreeRegsCleanState.smul
          _
          (ThreeRegsCleanState.ket
            b h₁ h₂ h₃)

  | add hψ hφ ihψ ihφ =>
      rw [qs.eval_add]
      exact
        ThreeRegsCleanState.add
          ihψ
          ihφ

  | smul a hψ ihψ =>
      rw [qs.eval_smul]
      exact
        ThreeRegsCleanState.smul
          a
          ihψ

/-- Step 4 temporarily uses `scratch.active`, but its three lowering-workspace
reserves are already zero in the public concrete Shor invariant. -/
private theorem shorConcreteCleanState_to_step4ReserveClean
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    (x data work scratch : ExtReg)
    (hxScratch : x.OwnedDisjoint scratch)
    {ψ : qs.State}
    (hclean :
      ShorConcreteCleanState
        qs x data work scratch hxScratch ψ) :
    ThreeRegsCleanState
      qs
      (data.reserve.drop 1)
      work.reserve
      scratch.reserve
      ψ := by
  induction hclean with
  | zero =>
      exact ThreeRegsCleanState.zero
  | ket b hbasis =>
      rcases hbasis with ⟨hcombined, hdata, hwork⟩
      apply ThreeRegsCleanState.ket b hdata hwork
      apply FreshZero.of_subset
          scratch.reserve
          (exponentScratchCleanReg x scratch hxScratch)
          b
      · intro q hq
        simp only [
          exponentScratchCleanReg,
          Reg.append,
          ExtReg.ownedReg,
          List.mem_append
        ]
        exact Or.inr (Or.inr hq)
      · exact hcombined
  | add hψ hφ ihψ ihφ =>
      exact ThreeRegsCleanState.add ihψ ihφ
  | smul a hψ ihψ =>
      exact ThreeRegsCleanState.smul a ihψ

/-- Dynamic readiness for the QFT--phase-product--inverse-QFT block used to
compute `N * work` into the Step-4 scratch register. -/
private theorem lowered_fastConstMulInto_ready_and_clean
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (lowering : ShorLoweringSetup)
    (r₁ : Reg)
    (N : ℕ)
    (work scratch : ExtReg)
    (ws : Gate.PhaseProdWorkspace work.active scratch.active)
    (hxReserve : ws.xExt.reserve = work.reserve)
    (hzReserve : ws.zExt.reserve = scratch.reserve)
    (h₁Scratch : Disjoint r₁ scratch.active)
    (hworkScratch : Disjoint work.reserve scratch.active)
    (hscratchScratch : Disjoint scratch.reserve scratch.active)
    (hworkspace :
      GateWorkspaceOK
        lowering.ops
        (fastConstMulInto N work scratch ws))
    (ψ : qs.State)
    (hclean :
      ThreeRegsCleanState
        qs r₁ work.reserve scratch.reserve ψ) :
    LoweredCleanResult
      qs
      lowering
      (ThreeRegsCleanState
        qs r₁ work.reserve scratch.reserve)
      (fastConstMulInto N work scratch ws)
      hworkspace
      ψ := by
  let φ : Angle :=
    (2 * (N : ℚ)) /
      (ASize ws.zExt.active : ℚ)
  let U1 : Gate := Gate.QFT ws.zExt
  let U2 : Gate :=
    Gate.PhaseProdUsing φ work.active scratch.active ws
  let U3 : Gate := IQFT ws.zExt

  change
    GateWorkspaceOK lowering.ops U1 ∧
      GateWorkspaceOK lowering.ops U2 ∧
      GateWorkspaceOK lowering.ops U3
    at hworkspace

  have hzActive : ws.zExt.active = scratch.active := by
    rfl
  have h₁Z : Disjoint r₁ ws.zExt.active := by
    simpa only [hzActive] using h₁Scratch
  have hworkZ : Disjoint work.reserve ws.zExt.active := by
    simpa only [hzActive] using hworkScratch
  have hscratchZ : Disjoint scratch.reserve ws.zExt.active := by
    simpa only [hzActive] using hscratchScratch

  have hU1Clean :
      GateWorkspaceCleanState
        qs lowering.k lowering.hk lowering.ops
        U1 hworkspace.1 ψ := by
    exact
      threeRegsCleanState_to_QFTWorkspaceCleanState
        lowering.ops ws.zExt hzReserve hclean

  let ψ1 : qs.State :=
    LowerGateClass.evalL
      (qs := qs)
      (lowerGate
        lowering.k lowering.hk lowering.ops
        U1 hworkspace.1)
      ψ

  have hψ1 :
      ThreeRegsCleanState
        qs r₁ work.reserve scratch.reserve ψ1 := by
    dsimp only [ψ1]
    rw [
      lowerGate_correctness
        qs lowering.k lowering.hk lowering.ops
        lowering.consumes lowering.returns
        U1 hworkspace.1 ψ hU1Clean
    ]
    exact
      eval_QFT_preserves_threeRegsCleanState
        ws.zExt r₁ work.reserve scratch.reserve
        h₁Z hworkZ hscratchZ hclean

  have hU1 :
      LoweredCleanResult
        qs lowering
        (ThreeRegsCleanState
          qs r₁ work.reserve scratch.reserve)
        U1 hworkspace.1 ψ :=
    ⟨hU1Clean, hψ1⟩

  have hU2Clean :
      GateWorkspaceCleanState
        qs lowering.k lowering.hk lowering.ops
        U2 hworkspace.2.1 ψ1 := by
    exact
      gateWorkspaceCleanState_PhaseProdUsing_of_threeRegsClean
        φ ws hxReserve hzReserve hworkspace.2.1 ψ1 hψ1

  let ψ2 : qs.State :=
    LowerGateClass.evalL
      (qs := qs)
      (lowerGate
        lowering.k lowering.hk lowering.ops
        U2 hworkspace.2.1)
      ψ1

  have hψ2 :
      ThreeRegsCleanState
        qs r₁ work.reserve scratch.reserve ψ2 := by
    dsimp only [ψ2]
    rw [
      lowerGate_correctness
        qs lowering.k lowering.hk lowering.ops
        lowering.consumes lowering.returns
        U2 hworkspace.2.1 ψ1 hU2Clean
    ]
    simpa only [U2] using
      eval_PhaseProdUsing_preserves_threeRegsCleanState
        φ ws hxReserve hzReserve hψ1

  have hU2 :
      LoweredCleanResult
        qs lowering
        (ThreeRegsCleanState
          qs r₁ work.reserve scratch.reserve)
        U2 hworkspace.2.1 ψ1 :=
    ⟨hU2Clean, hψ2⟩

  have hHighU3 :
      ThreeRegsCleanState
        qs r₁ work.reserve scratch.reserve
        (qs.eval U3 ψ2) := by
    simpa only [U3] using
      eval_IQFT_preserves_threeRegsCleanState
        ws.zExt r₁ work.reserve scratch.reserve
        h₁Z hworkZ hscratchZ hψ2

  have hQFTLocal :
      QFTWorkspaceCleanState
        qs
        (qftXWork lowering.ops ws.zExt)
        (qftZWork lowering.ops ws.zExt)
        (qs.eval U3 ψ2) :=
    threeRegsCleanState_to_QFTWorkspaceCleanState
      lowering.ops ws.zExt hzReserve hHighU3

  have hU3Clean :
      GateWorkspaceCleanState
        qs lowering.k lowering.hk lowering.ops
        U3 hworkspace.2.2 ψ2 := by
    simpa [U3, IQFT, GateWorkspaceCleanState] using hQFTLocal

  have hU3 :
      LoweredCleanResult
        qs lowering
        (ThreeRegsCleanState
          qs r₁ work.reserve scratch.reserve)
        U3 hworkspace.2.2 ψ2 := by
    constructor
    · exact hU3Clean
    · rw [
        lowerGate_correctness
          qs lowering.k lowering.hk lowering.ops
          lowering.consumes lowering.returns
          U3 hworkspace.2.2 ψ2 hU3Clean
      ]
      exact hHighU3

  have hU23 :
      LoweredCleanResult
        qs lowering
        (ThreeRegsCleanState
          qs r₁ work.reserve scratch.reserve)
        (U2 ;; U3) hworkspace.2 ψ1 :=
    LoweredCleanResult.seq hworkspace.2 ψ1 hU2
      (by simpa only [ψ2] using hU3)

  have hU123 :
      LoweredCleanResult
        qs lowering
        (ThreeRegsCleanState
          qs r₁ work.reserve scratch.reserve)
        (U1 ;; U2 ;; U3) hworkspace ψ :=
    LoweredCleanResult.seq hworkspace ψ hU1
      (U := U1)
      (V := U2 ;; U3)
      (by simpa only [ψ1] using hU23)

  simpa [
    U1,
    U2,
    U3,
    φ,
    fastConstMulInto
  ] using hU123

/-- Step 4 has real recursive workspace inside both multiplication blocks.
The forward block is discharged from the reserve-only invariant; the adjoint
block is discharged at the fully uncomputed high-level output. -/
theorem lowered_step4_ready_and_clean
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (lowering : ShorLoweringSetup)
    (x data work scratch : ExtReg)
    (N flag : ℕ)
    (hxData : x.OwnedDisjoint data)
    (hxWork : x.OwnedDisjoint work)
    (hxScratch : x.OwnedDisjoint scratch)
    (hmod : ModMulCircuitWorkspaceOK data work)
    (hflagX : flag ∉ x.ownedQubits)
    (hstep4 :
      CmpLtNWWorkspace N (data.grow 1) work scratch flag)
    (hworkspace :
      GateWorkspaceOK
        lowering.ops
        (step4 N (data.grow 1) work scratch flag hstep4))
    (ψ : qs.State)
    (hclean :
      ShorConcreteCleanState
        qs x data work scratch hxScratch ψ) :
    LoweredCleanResult
      qs
      lowering
      (ShorConcreteCleanState
        qs x data work scratch hxScratch)
      (step4 N (data.grow 1) work scratch flag hstep4)
      hworkspace
      ψ := by
  let U1 :=
    fastConstMulInto N work scratch hstep4.mulWorkspace
  let U2 :=
    cmpLtNWDifference
      (data.grow 1) work scratch hstep4.data_can_grow
  have hscratchPos : 0 < regSize scratch.active := by
    rw [hstep4.scratch_width]
    unfold cmpLtNWWidth
    omega
  let sign := cmpLtNWSignQubit scratch hscratchPos
  let U3 := Gate.CNOT sign flag
  let U4 := †U2
  let U5 := †U1

  change
    GateWorkspaceOK lowering.ops U1 ∧
      GateWorkspaceOK lowering.ops U2 ∧
      GateWorkspaceOK lowering.ops U3 ∧
      GateWorkspaceOK lowering.ops U4 ∧
      GateWorkspaceOK lowering.ops U5
    at hworkspace

  have hlocal :
      ThreeRegsCleanState
        qs
        (data.reserve.drop 1)
        work.reserve
        scratch.reserve
        ψ :=
    shorConcreteCleanState_to_step4ReserveClean
      x data work scratch hxScratch hclean

  have hdataScratch :
      Disjoint (data.reserve.drop 1) scratch.active :=
    by
      simpa [ExtReg.grow, ExtReg.remainingReserve, Reg.drop] using
        (reserve_active_disjoint_of_ownedDisjoint
          hstep4.data_scratch_disjoint)
  have hworkScratch :
      Disjoint work.reserve scratch.active :=
    reserve_active_disjoint_of_ownedDisjoint
      hstep4.work_scratch_disjoint
  have hscratchScratch :
      Disjoint scratch.reserve scratch.active :=
    Disjoint.symm scratch.active_reserve_disjoint

  have hU1 :
      LoweredCleanResult
        qs lowering
        (ThreeRegsCleanState
          qs
          (data.reserve.drop 1)
          work.reserve
          scratch.reserve)
        U1 hworkspace.1 ψ := by
    simpa only [U1] using
      lowered_fastConstMulInto_ready_and_clean
        lowering
        (data.reserve.drop 1)
        N work scratch hstep4.mulWorkspace
        hstep4.mul_xReserve_eq
        hstep4.mul_zReserve_eq
        hdataScratch
        hworkScratch
        hscratchScratch
        hworkspace.1
        ψ
        hlocal

  let ψ1 :=
    LowerGateClass.evalL
      (qs := qs)
      (lowerGate
        lowering.k lowering.hk lowering.ops
        U1 hworkspace.1)
      ψ

  have hψ1 : ψ1 = qs.eval U1 ψ := by
    dsimp only [ψ1]
    rw [
      lowerGate_correctness
        qs lowering.k lowering.hk lowering.ops
        lowering.consumes lowering.returns
        U1 hworkspace.1 ψ hU1.1
    ]

  have hU2Clean :
      GateWorkspaceCleanState
        qs lowering.k lowering.hk lowering.ops
        U2 hworkspace.2.1 ψ1 := by
    simp [U2, cmpLtNWDifference, GateWorkspaceCleanState]

  let ψ2 :=
    LowerGateClass.evalL
      (qs := qs)
      (lowerGate
        lowering.k lowering.hk lowering.ops
        U2 hworkspace.2.1)
      ψ1

  have hψ2 : ψ2 = qs.eval U2 (qs.eval U1 ψ) := by
    dsimp only [ψ2]
    rw [
      lowerGate_correctness
        qs lowering.k lowering.hk lowering.ops
        lowering.consumes lowering.returns
        U2 hworkspace.2.1 ψ1 hU2Clean,
      hψ1
    ]

  have hU3Clean :
      GateWorkspaceCleanState
        qs lowering.k lowering.hk lowering.ops
        U3 hworkspace.2.2.1 ψ2 := by
    simp [U3, GateWorkspaceCleanState]

  let ψ3 :=
    LowerGateClass.evalL
      (qs := qs)
      (lowerGate
        lowering.k lowering.hk lowering.ops
        U3 hworkspace.2.2.1)
      ψ2

  have hψ3 :
      ψ3 = qs.eval U3 (qs.eval U2 (qs.eval U1 ψ)) := by
    dsimp only [ψ3]
    rw [
      lowerGate_correctness
        qs lowering.k lowering.hk lowering.ops
        lowering.consumes lowering.returns
        U3 hworkspace.2.2.1 ψ2 hU3Clean,
      hψ2
    ]

  have hU4Clean :
      GateWorkspaceCleanState
        qs lowering.k lowering.hk lowering.ops
        U4 hworkspace.2.2.2.1 ψ3 := by
    simp [U4, U2, cmpLtNWDifference, GateWorkspaceCleanState]

  let ψ4 :=
    LowerGateClass.evalL
      (qs := qs)
      (lowerGate
        lowering.k lowering.hk lowering.ops
        U4 hworkspace.2.2.2.1)
      ψ3

  have hψ4 :
      ψ4 =
        qs.eval U4
          (qs.eval U3 (qs.eval U2 (qs.eval U1 ψ))) := by
    dsimp only [ψ4]
    rw [
      lowerGate_correctness
        qs lowering.k lowering.hk lowering.ops
        lowering.consumes lowering.returns
        U4 hworkspace.2.2.2.1 ψ3 hU4Clean,
      hψ3
    ]

  have hHighFull :
      ShorConcreteCleanState
        qs x data work scratch hxScratch
        (qs.eval
          (step4 N (data.grow 1) work scratch flag hstep4)
          ψ) :=
    eval_step4_preserves_lowering_clean
      x data work scratch N flag
      hxData hxWork hxScratch hmod hflagX hstep4 hclean

  have hLocalFull :
      ThreeRegsCleanState
        qs
        (data.reserve.drop 1)
        work.reserve
        scratch.reserve
        (qs.eval
          (step4 N (data.grow 1) work scratch flag hstep4)
          ψ) :=
    shorConcreteCleanState_to_step4ReserveClean
      x data work scratch hxScratch hHighFull

  have hU5Input :
      qs.eval U5 ψ4 =
        qs.eval
          (step4 N (data.grow 1) work scratch flag hstep4)
          ψ := by
    rw [hψ4]
    simp only [
      step4,
      cmpLtNW,
      U1,
      U2,
      U3,
      U4,
      U5,
      sign,
      qs.eval_seq
    ]

  have hU5Clean :
      GateWorkspaceCleanState
        qs lowering.k lowering.hk lowering.ops
        U5 hworkspace.2.2.2.2 ψ4 := by
    change
      GateWorkspaceCleanState
        qs lowering.k lowering.hk lowering.ops
        U1 hworkspace.2.2.2.2 (qs.eval U5 ψ4)
    rw [hU5Input]
    exact
      (lowered_fastConstMulInto_ready_and_clean
        lowering
        (data.reserve.drop 1)
        N work scratch hstep4.mulWorkspace
        hstep4.mul_xReserve_eq
        hstep4.mul_zReserve_eq
        hdataScratch
        hworkScratch
        hscratchScratch
        hworkspace.2.2.2.2
        (qs.eval
          (step4 N (data.grow 1) work scratch flag hstep4)
          ψ)
        hLocalFull).1

  have hgateClean :
      GateWorkspaceCleanState
        qs lowering.k lowering.hk lowering.ops
        (step4 N (data.grow 1) work scratch flag hstep4)
        hworkspace ψ := by
    change
      GateWorkspaceCleanState
          qs lowering.k lowering.hk lowering.ops
          U1 hworkspace.1 ψ ∧
        GateWorkspaceCleanState
          qs lowering.k lowering.hk lowering.ops
          U2 hworkspace.2.1 ψ1 ∧
        GateWorkspaceCleanState
          qs lowering.k lowering.hk lowering.ops
          U3 hworkspace.2.2.1 ψ2 ∧
        GateWorkspaceCleanState
          qs lowering.k lowering.hk lowering.ops
          U4 hworkspace.2.2.2.1 ψ3 ∧
        GateWorkspaceCleanState
          qs lowering.k lowering.hk lowering.ops
          U5 hworkspace.2.2.2.2 ψ4
    exact ⟨hU1.1, hU2Clean, hU3Clean, hU4Clean, hU5Clean⟩

  constructor
  · exact hgateClean
  · rw [
      lowerGate_correctness
        qs lowering.k lowering.hk lowering.ops
        lowering.consumes lowering.returns
        (step4 N (data.grow 1) work scratch flag hstep4)
        hworkspace ψ hgateClean
    ]
    exact hHighFull

theorem lowered_step1_ready_and_full_clean
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (lowering : ShorLoweringSetup)
    (x data work : ExtReg)
    (c N ctrl : ℕ)
    (hxWork :
      ExtReg.OwnedDisjoint x work)
    (hmod :
      ModMulCircuitWorkspaceOK data work)
    (hworkspace :
      GateWorkspaceOK
        lowering.ops
        (step1
          c N ctrl data work hmod))
    (ψ : qs.State)
    (hclean :
      ShorLoweringCleanState
        qs x data work ψ) :
    LoweredCleanResult
      qs
      lowering
      (ShorLoweringCleanState
        qs x data work)
      (step1
        c N ctrl data work hmod)
      hworkspace
      ψ := by
  let φ : Angle :=
    (2 *
      (((c + N - 1) % N : ℕ) : ℚ))
      /
    (N : ℚ)

  let U1 : Gate :=
    H_reg work.active

  let U2 : Gate :=
    Gate.CPhaseProdUsing
      ctrl
      φ
      data.active
      work.active
      hmod.step1Workspace

  let U3 : Gate :=
    IQFT hmod.step1Workspace.zExt

  change
    GateWorkspaceOK lowering.ops U1
      ∧
    GateWorkspaceOK lowering.ops U2
      ∧
    GateWorkspaceOK lowering.ops U3
    at hworkspace

  change
    LoweredCleanResult
      qs
      lowering
      (ShorLoweringCleanState
        qs x data work)
      (U1 ;; U2 ;; U3)
      hworkspace
      ψ

  have hxWorkActive :
      Disjoint x.reserve work.active :=
    reserve_active_disjoint_of_ownedDisjoint
      hxWork

  have hdataWorkActive :
      Disjoint (data.reserve.drop 1) work.active :=
    reserve_drop_active_disjoint_of_ownedDisjoint
      hmod.2.2
      1

  have hworkWorkActive :
      Disjoint work.reserve work.active :=
    Disjoint.symm
      work.active_reserve_disjoint

  /- Hadamard stage. -/

  have hU1Clean :
      GateWorkspaceCleanState
        qs
        lowering.k
        lowering.hk
        lowering.ops
        U1
        hworkspace.1
        ψ := by
    exact
      (workspaceFree_H_reg work.active).clean
        hworkspace.1
        ψ

  let ψ1 : qs.State :=
    LowerGateClass.evalL
      (qs := qs)
      (lowerGate
        lowering.k
        lowering.hk
        lowering.ops
        U1
        hworkspace.1)
      ψ

  have hψ1 :
      ShorLoweringCleanState
        qs x data work ψ1 := by
    dsimp only [ψ1]

    rw [
      lowerGate_correctness
        qs
        lowering.k
        lowering.hk
        lowering.ops
        lowering.consumes
        lowering.returns
        U1
        hworkspace.1
        ψ
        hU1Clean
    ]

    simpa only [U1] using
      eval_H_reg_preserves_threeRegsCleanState
        work.active
        x.reserve
        (data.reserve.drop 1)
        work.reserve
        hxWorkActive
        hdataWorkActive
        hworkWorkActive
        hclean

  have hU1 :
      LoweredCleanResult
        qs
        lowering
        (ShorLoweringCleanState
          qs x data work)
        U1
        hworkspace.1
        ψ :=
    ⟨hU1Clean, hψ1⟩

  /- Controlled phase-product stage. -/

  have hxReserve :
      hmod.step1Workspace.xExt.reserve =
        data.reserve.drop 1 := by
    rfl

  have hzReserve :
      hmod.step1Workspace.zExt.reserve =
        work.reserve := by
    rfl

  have hU2Clean :
      GateWorkspaceCleanState
        qs
        lowering.k
        lowering.hk
        lowering.ops
        U2
        hworkspace.2.1
        ψ1 := by
    exact
      gateWorkspaceCleanState_CPhaseProdUsing_of_threeRegsClean
        ctrl
        φ
        hmod.step1Workspace
        hxReserve
        hzReserve
        hworkspace.2.1
        ψ1
        hψ1

  let ψ2 : qs.State :=
    LowerGateClass.evalL
      (qs := qs)
      (lowerGate
        lowering.k
        lowering.hk
        lowering.ops
        U2
        hworkspace.2.1)
      ψ1

  have hψ2 :
      ShorLoweringCleanState
        qs x data work ψ2 := by
    dsimp only [ψ2]

    rw [
      lowerGate_correctness
        qs
        lowering.k
        lowering.hk
        lowering.ops
        lowering.consumes
        lowering.returns
        U2
        hworkspace.2.1
        ψ1
        hU2Clean
    ]

    simpa only [U2] using
      eval_CPhaseProdUsing_preserves_threeRegsCleanState
        ctrl
        φ
        hmod.step1Workspace
        hxReserve
        hzReserve
        hψ1

  have hU2 :
      LoweredCleanResult
        qs
        lowering
        (ShorLoweringCleanState
          qs x data work)
        U2
        hworkspace.2.1
        ψ1 :=
    ⟨hU2Clean, hψ2⟩

  /- Inverse-QFT stage. -/

  have hzExtActive :
      hmod.step1Workspace.zExt.active =
        work.active := by
    rfl

  have hxZExt :
      Disjoint
        x.reserve
        hmod.step1Workspace.zExt.active := by
    simpa only [hzExtActive] using
      hxWorkActive

  have hdataZExt :
      Disjoint
        (data.reserve.drop 1)
        hmod.step1Workspace.zExt.active := by
    simpa only [hzExtActive] using
      hdataWorkActive

  have hworkZExt :
      Disjoint
        work.reserve
        hmod.step1Workspace.zExt.active := by
    simpa only [hzExtActive] using
      hworkWorkActive

  have hHighU3 :
      ShorLoweringCleanState
        qs x data work
        (qs.eval U3 ψ2) := by
    simpa only [U3] using
      eval_IQFT_preserves_threeRegsCleanState
        hmod.step1Workspace.zExt
        x.reserve
        (data.reserve.drop 1)
        work.reserve
        hxZExt
        hdataZExt
        hworkZExt
        hψ2

  have hQFTLocal :
      QFTWorkspaceCleanState
        qs
        (qftXWork
          lowering.ops
          hmod.step1Workspace.zExt)
        (qftZWork
          lowering.ops
          hmod.step1Workspace.zExt)
        (qs.eval U3 ψ2) := by
    exact
      threeRegsCleanState_to_QFTWorkspaceCleanState
        lowering.ops
        hmod.step1Workspace.zExt
        hzReserve
        hHighU3

  have hU3Clean :
      GateWorkspaceCleanState
        qs
        lowering.k
        lowering.hk
        lowering.ops
        U3
        hworkspace.2.2
        ψ2 := by
    simpa [
      U3,
      IQFT,
      GateWorkspaceCleanState
    ] using hQFTLocal

  have hU3 :
      LoweredCleanResult
        qs
        lowering
        (ShorLoweringCleanState
          qs x data work)
        U3
        hworkspace.2.2
        ψ2 := by
    constructor
    · exact hU3Clean

    · rw [
        lowerGate_correctness
          qs
          lowering.k
          lowering.hk
          lowering.ops
          lowering.consumes
          lowering.returns
          U3
          hworkspace.2.2
          ψ2
          hU3Clean
      ]

      exact hHighU3

  /- Assemble the three sequential stages. -/

  have hU23 :
      LoweredCleanResult
        qs
        lowering
        (ShorLoweringCleanState
          qs x data work)
        (U2 ;; U3)
        hworkspace.2
        ψ1 := by
    apply
      LoweredCleanResult.seq
        hworkspace.2
        ψ1
        hU2

    simpa only [ψ2] using hU3

  exact
    LoweredCleanResult.seq
      (U := U1)
      (V := U2 ;; U3)
      hworkspace
      ψ
      hU1
      (by simpa only [ψ1] using hU23)


theorem lowered_step2_ready_and_carry_clean
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (lowering : ShorLoweringSetup)
    (x data work : ExtReg)
    (N : ℕ)
    (hxData :
      ExtReg.OwnedDisjoint x data)
    (hmod :
      ModMulCircuitWorkspaceOK data work)
    (hworkspace :
      GateWorkspaceOK
        lowering.ops
        (step2
          N data work hmod))
    (ψ : qs.State)
    (hclean :
      ShorLoweringCleanState
        qs x data work ψ) :
    LoweredCleanResult
      qs
      lowering
      (ShorLoweringCleanState
        qs x data work)
      (step2
        N data work hmod)
      hworkspace
      ψ := by
  classical

  /- The three sequential stages of Step 2. -/

  let dc : ExtReg := data.grow 1

  let ws :
      Gate.PhaseProdWorkspace
        work.active dc.active :=
    hmod.step2Workspace

  let φ : Angle :=
    (2 * (N : ℚ)) /
      (2 : ℚ) ^
        (regSize work.active + regSize dc.active)

  let U1 : Gate := Gate.QFT ws.zExt

  let U2 : Gate :=
    Gate.PhaseProdUsing
      φ work.active dc.active ws

  let U3 : Gate := IQFT ws.zExt

  change
    GateWorkspaceOK lowering.ops U1
      ∧
    GateWorkspaceOK lowering.ops U2
      ∧
    GateWorkspaceOK lowering.ops U3
    at hworkspace

  /- Layout facts about the carry-extended data register. -/

  have hxCarry :
      ExtReg.OwnedDisjoint x dc :=
    ownedDisjoint_grow_right 1 hxData

  have hxCarryActive :
      Disjoint x.reserve dc.active :=
    reserve_active_disjoint_of_ownedDisjoint
      hxCarry

  have hworkCarryActive :
      Disjoint work.reserve dc.active :=
    reserve_active_disjoint_of_ownedDisjoint
      hmod.work_dataCarry_disjoint

  have hdataCarryActive :
      Disjoint (data.reserve.drop 1) dc.active :=
    Disjoint.symm
      dc.active_reserve_disjoint

  have hxReserve :
      ws.xExt.reserve = work.reserve := by
    rfl

  have hzReserve :
      ws.zExt.reserve = data.reserve.drop 1 := by
    rfl

  /-
  Step 2 touches the carry bit, so the invariant is carried in the order
  `(x.reserve, work.reserve, data.reserve.drop 1)`: that is the order in
  which the phase-product workspace consumes its two reserves.
  -/

  have hclean0 :
      ThreeRegsCleanState
        qs
        x.reserve
        work.reserve
        (data.reserve.drop 1)
        ψ :=
    threeRegsCleanState_swap23
      (hclean)

  /- Forward-QFT stage. -/

  have hU1Clean :
      GateWorkspaceCleanState
        qs
        lowering.k
        lowering.hk
        lowering.ops
        U1
        hworkspace.1
        ψ := by
    exact
      threeRegsCleanState_to_QFTWorkspaceCleanState
        lowering.ops
        ws.zExt
        hzReserve
        hclean0

  let ψ1 : qs.State :=
    LowerGateClass.evalL
      (qs := qs)
      (lowerGate
        lowering.k
        lowering.hk
        lowering.ops
        U1
        hworkspace.1)
      ψ

  have hψ1 :
      ThreeRegsCleanState
        qs
        x.reserve
        work.reserve
        (data.reserve.drop 1)
        ψ1 := by
    dsimp only [ψ1]

    rw [
      lowerGate_correctness
        qs
        lowering.k
        lowering.hk
        lowering.ops
        lowering.consumes
        lowering.returns
        U1
        hworkspace.1
        ψ
        hU1Clean
    ]

    exact
      eval_QFT_preserves_threeRegsCleanState
        ws.zExt
        x.reserve
        work.reserve
        (data.reserve.drop 1)
        hxCarryActive
        hworkCarryActive
        hdataCarryActive
        hclean0

  have hU1 :
      LoweredCleanResult
        qs
        lowering
        (ThreeRegsCleanState
          qs
          x.reserve
          work.reserve
          (data.reserve.drop 1))
        U1
        hworkspace.1
        ψ :=
    ⟨hU1Clean, hψ1⟩

  /- Unsigned phase-product stage. -/

  have hU2Clean :
      GateWorkspaceCleanState
        qs
        lowering.k
        lowering.hk
        lowering.ops
        U2
        hworkspace.2.1
        ψ1 := by
    exact
      gateWorkspaceCleanState_PhaseProdUsing_of_threeRegsClean
        φ
        ws
        hxReserve
        hzReserve
        hworkspace.2.1
        ψ1
        hψ1

  let ψ2 : qs.State :=
    LowerGateClass.evalL
      (qs := qs)
      (lowerGate
        lowering.k
        lowering.hk
        lowering.ops
        U2
        hworkspace.2.1)
      ψ1

  have hψ2 :
      ThreeRegsCleanState
        qs
        x.reserve
        work.reserve
        (data.reserve.drop 1)
        ψ2 := by
    dsimp only [ψ2]

    rw [
      lowerGate_correctness
        qs
        lowering.k
        lowering.hk
        lowering.ops
        lowering.consumes
        lowering.returns
        U2
        hworkspace.2.1
        ψ1
        hU2Clean
    ]

    simpa only [U2] using
      eval_PhaseProdUsing_preserves_threeRegsCleanState
        φ
        ws
        hxReserve
        hzReserve
        hψ1

  have hU2 :
      LoweredCleanResult
        qs
        lowering
        (ThreeRegsCleanState
          qs
          x.reserve
          work.reserve
          (data.reserve.drop 1))
        U2
        hworkspace.2.1
        ψ1 :=
    ⟨hU2Clean, hψ2⟩

  /- Inverse-QFT stage. -/

  have hHighU3 :
      ThreeRegsCleanState
        qs
        x.reserve
        work.reserve
        (data.reserve.drop 1)
        (qs.eval U3 ψ2) := by
    simpa only [U3] using
      eval_IQFT_preserves_threeRegsCleanState
        ws.zExt
        x.reserve
        work.reserve
        (data.reserve.drop 1)
        hxCarryActive
        hworkCarryActive
        hdataCarryActive
        hψ2

  have hQFTLocal :
      QFTWorkspaceCleanState
        qs
        (qftXWork lowering.ops ws.zExt)
        (qftZWork lowering.ops ws.zExt)
        (qs.eval U3 ψ2) :=
    threeRegsCleanState_to_QFTWorkspaceCleanState
      lowering.ops
      ws.zExt
      hzReserve
      hHighU3

  have hU3Clean :
      GateWorkspaceCleanState
        qs
        lowering.k
        lowering.hk
        lowering.ops
        U3
        hworkspace.2.2
        ψ2 := by
    simpa [
      U3,
      IQFT,
      GateWorkspaceCleanState
    ] using hQFTLocal

  have hU3 :
      LoweredCleanResult
        qs
        lowering
        (ShorLoweringCleanState
          qs x data work)
        U3
        hworkspace.2.2
        ψ2 := by
    constructor
    · exact hU3Clean

    · rw [
        lowerGate_correctness
          qs
          lowering.k
          lowering.hk
          lowering.ops
          lowering.consumes
          lowering.returns
          U3
          hworkspace.2.2
          ψ2
          hU3Clean
      ]

      exact
        threeRegsCleanState_swap23 hHighU3

  /- Assemble the three sequential stages. -/

  have hU23 :
      LoweredCleanResult
        qs
        lowering
        (ShorLoweringCleanState
          qs x data work)
        (U2 ;; U3)
        hworkspace.2
        ψ1 :=
    LoweredCleanResult.seq
      (U := U2)
      (V := U3)
      hworkspace.2
      ψ1
      hU2
      (by simpa only [ψ2] using hU3)

  exact
    LoweredCleanResult.seq
      (U := U1)
      (V := U2 ;; U3)
      hworkspace
      ψ
      hU1
      (by simpa only [ψ1] using hU23)


end Shor
