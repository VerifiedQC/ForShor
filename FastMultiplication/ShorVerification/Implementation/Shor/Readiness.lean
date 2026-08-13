import FastMultiplication.ShorVerification.Implementation.Shor.OrderFinding
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Defs
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.GateSemanticsLemmas
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Shor
open Gate
open Classical

/-!
# Shor workspace readiness and clean-state preservation

This module contains the lowered workspace readiness and dynamic clean-state
preservation results for the approximate Shor order-finding circuit.

Organization:

* Static readiness: `gateWorkspaceOK_orderFindingApprox` and
  `LoweredShorReady.workspace`.
* Dynamic infrastructure: `LoweredCleanResult`, workspace-free gates,
  disjointness/locality helpers, and clean-state preservation for primitive
  steps.
* Stage readiness: lowered readiness for initialization, Step 1, Step 2,
  Step 5, IQFT, one modular-multiplication core, modular exponentiation, and
  the full order-finding circuit.
* Public final result: `LoweredShorReady.workspace_clean`.
-/

/-! =========================================================
    Section 1: Public static readiness theorem
========================================================= -/

/-! ---------------------------------------------------------
    Static reserve arithmetic helpers
--------------------------------------------------------- -/

private lemma reserve_le_capacity_sub_one_of_succ_le
    {need capacity : ℕ}
    (h : 1 + need ≤ capacity) :
    need ≤ capacity - 1 := by
  omega

private lemma reserve_le_capacity_sub_two_of_two_add_le
    {need capacity : ℕ}
    (h : 2 + need ≤ capacity) :
    need ≤ capacity - 2 := by
  omega

private theorem gateWorkspaceOK_H_reg
    {k : ℕ}
    (ops : Prog k)
    (r : Reg) :
    GateWorkspaceOK ops (H_reg r) := by
  unfold H_reg
  have hfold :
      ∀ (l : List ℕ) (U : Gate),
        GateWorkspaceOK ops U →
        GateWorkspaceOK ops
          (l.foldl (fun acc q => Gate.H q ;; acc) U) := by
    intro l
    induction l with
    | nil =>
        intro U hU
        simpa
    | cons q l ih =>
        intro U hU
        simp only [List.foldl_cons]
        exact ih (Gate.H q ;; U) ⟨trivial, hU⟩
  exact hfold (regQubits r) Gate.id trivial


/--
Main static theorem for this module.

It expands the public Shor reserve budget into the per-stage
`GateWorkspaceOK` facts required by lowering the full approximate order-finding
circuit.
-/
theorem gateWorkspaceOK_orderFindingApprox
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    {k : ℕ}
    (ops : Prog k)
    (η : ℝ)
    (a N : ℕ)
    (x data work : ExtReg)
    (flag : ℕ)
    (b0 : qs.Basis)
    (hsetup :
      ShorApproxSetup
        qs η x data work flag b0)
    (hlarge :
      ShorWorkspaceLargeEnough
        ops x data work) :
    GateWorkspaceOK ops
      (orderFindingApprox
        qs a N x data work flag
        hsetup.circuit_workspace) := by
  let hmod : ModMulCircuitWorkspaceOK data work :=
    hsetup.circuit_workspace

  have hDataGrow : data.CanGrow 1 :=
    hmod.data_canGrow_one
  have hDataCarryGrow : (data.grow 1).CanGrow 1 :=
    hmod.dataCarry_canGrow_one
  have hWorkGrow : work.CanGrow 1 :=
    hmod.work_canGrow_one

  have hDataBounds := hlarge.data_large_enough
  have hWorkBounds := hlarge.auxiliary_large_enough
  dsimp [shorWorkspaceNeed] at hDataBounds hWorkBounds
  simp only [max_le_iff] at hDataBounds hWorkBounds
  rcases hDataBounds with
    ⟨hDataStep1, hDataQFT, hDataStep2, hDataStep5⟩
  rcases hWorkBounds with
    ⟨hWorkQFT, hWorkStep1, hWorkStep2, hWorkStep5⟩

  have hQFTX : QFTReserveOK ops x := by
    refine ⟨?_⟩
    change qftReserveNeed ops x.width ≤ x.capacity
    exact hlarge.exponent_large_enough

  have hQFTWork : QFTReserveOK ops work := by
    refine ⟨?_⟩
    simpa [qftReserveNeed] using hWorkQFT

  have hQFTDataCarry : QFTReserveOK ops (data.grow 1) := by
    refine ⟨?_⟩
    rw [
      ExtReg.width_grow data 1 hDataGrow,
      ExtReg.capacity_grow data 1 hDataGrow
    ]
    have h := hDataQFT
    simp only [qftReserveNeed] at h
    omega

  have hStep1ZExt : hmod.step1Workspace.zExt = work := by
    rfl
  have hStep2XExt : hmod.step2Workspace.xExt = work := by
    rfl
  have hStep2ZExt : hmod.step2Workspace.zExt = data.grow 1 := by
    rfl
  have hStep5XExt : hmod.step5Workspace.xExt = data.grow 1 := by
    rfl
  have hStep5ZExt : hmod.step5Workspace.zExt = work := by
    rfl

  have hHWork : GateWorkspaceOK ops (H_reg work.active) :=
    gateWorkspaceOK_H_reg ops work.active

  have hCore :
      ∀ (c ctrl : ℕ),
        ModMulCoreLayout data work flag ctrl →
        GateWorkspaceOK ops
          (CmodMulInPlaceCore
            (Basis := qs.Basis)
            c N ctrl data work flag hmod) := by
    intro c ctrl hlayout

    have hctrlData : ctrl ∉ data.ownedQubits :=
      hlayout.2.2.2.1
    have hctrlWork : ctrl ∉ work.ownedQubits :=
      hlayout.2.2.2.2.1

    have hStep1Static :
        CSignedRecursiveWorkspaceOK
          ops ctrl
          (hmod.step1Workspace.xExt.grow 1)
          (hmod.step1Workspace.zExt.grow 1) :=
      {
        toSignedRecursiveWorkspaceOK :=
          {
            owned_disjoint := by
              rw [
                ExtReg.OwnedDisjoint,
                ExtReg.ownedQubits_grow,
                ExtReg.ownedQubits_grow,
                List.disjoint_left
              ]
              intro q hqx hqz
              rw [ExtReg.ownedQubits, List.mem_append] at hqx hqz
              rcases hqx with hqxActive | hqxReserve
              · rcases hqz with hqzActive | hqzReserve
                · have h := hmod.step1Workspace.xz_disjoint
                  rw [Disjoint, List.disjoint_left] at h
                  exact h hqxActive hqzActive
                · have h := hmod.step1Workspace.zReserve_not_x
                  rw [Disjoint, List.disjoint_left] at h
                  exact h hqzReserve hqxActive
              · rcases hqz with hqzActive | hqzReserve
                · have h := hmod.step1Workspace.xReserve_not_z
                  rw [Disjoint, List.disjoint_left] at h
                  exact h hqxReserve hqzActive
                · have h := hmod.step1Workspace.reserve_disjoint
                  rw [Disjoint, List.disjoint_left] at h
                  exact h hqxReserve hqzReserve

            x_reserve_sufficient := by
              rw [
                ExtReg.width_grow
                  hmod.step1Workspace.xExt
                  1
                  hmod.step1Workspace.xExt_canGrow,
                ExtReg.width_grow
                  hmod.step1Workspace.zExt
                  1
                  hmod.step1Workspace.zExt_canGrow,
                ExtReg.capacity_grow
                  hmod.step1Workspace.xExt
                  1
                  hmod.step1Workspace.xExt_canGrow
              ]
              rw [
                show hmod.step1Workspace.xExt.width = data.width by rfl,
                show hmod.step1Workspace.zExt.width = work.width by rfl,
                show hmod.step1Workspace.xExt.capacity = data.capacity - 1 by
                  change regSize (data.reserve.drop 1) = data.capacity - 1
                  simp [
                    ExtReg.capacity,
                    Reg.drop,
                    regSize,
                    Reg.width
                  ]
              ]
              exact reserve_le_capacity_sub_two_of_two_add_le hDataStep1

            z_reserve_sufficient := by
              rw [
                ExtReg.width_grow
                  hmod.step1Workspace.xExt
                  1
                  hmod.step1Workspace.xExt_canGrow,
                ExtReg.width_grow
                  hmod.step1Workspace.zExt
                  1
                  hmod.step1Workspace.zExt_canGrow,
                ExtReg.capacity_grow
                  hmod.step1Workspace.zExt
                  1
                  hmod.step1Workspace.zExt_canGrow
              ]
              rw [
                show hmod.step1Workspace.xExt.width = data.width by rfl,
                show hmod.step1Workspace.zExt.width = work.width by rfl,
                show hmod.step1Workspace.zExt.capacity = work.capacity by rfl
              ]
              exact reserve_le_capacity_sub_one_of_succ_le hWorkStep1
          }

        control_disjoint := by
          rw [
            ExtReg.CtrlDisjoint,
            ExtReg.ownedQubits_grow,
            ExtReg.ownedQubits_grow
          ]
          constructor
          · rw [ExtReg.ownedQubits, List.mem_append]
            intro hctrl
            apply hctrlData
            rw [ExtReg.ownedQubits, List.mem_append]
            rcases hctrl with hctrlActive | hctrlReserve
            · exact Or.inl hctrlActive
            · exact Or.inr (List.mem_of_mem_drop hctrlReserve)
          · exact hctrlWork
      }

    have hStep2Static :
        SignedRecursiveWorkspaceOK
          ops
          (work.grow 1)
          ((data.grow 1).grow 1) :=
      {
        owned_disjoint := by
          simpa [
            ExtReg.OwnedDisjoint,
            ExtReg.ownedQubits_grow
          ] using hmod.work_dataCarry_disjoint

        x_reserve_sufficient := by
          rw [
            ExtReg.width_grow work 1 hWorkGrow,
            ExtReg.width_grow (data.grow 1) 1 hDataCarryGrow,
            ExtReg.width_grow data 1 hDataGrow,
            ExtReg.capacity_grow work 1 hWorkGrow
          ]
          rw [show data.width + 1 + 1 = data.width + 2 by omega]
          exact reserve_le_capacity_sub_one_of_succ_le hWorkStep2

        z_reserve_sufficient := by
          rw [
            ExtReg.width_grow work 1 hWorkGrow,
            ExtReg.width_grow (data.grow 1) 1 hDataCarryGrow,
            ExtReg.width_grow data 1 hDataGrow,
            ExtReg.capacity_grow (data.grow 1) 1 hDataCarryGrow,
            ExtReg.capacity_grow data 1 hDataGrow
          ]
          rw [show data.width + 1 + 1 = data.width + 2 by omega]
          exact reserve_le_capacity_sub_two_of_two_add_le hDataStep2
      }

    have hStep5Static :
        CSignedRecursiveWorkspaceOK
          ops ctrl
          ((data.grow 1).grow 1)
          (work.grow 1) :=
      {
        toSignedRecursiveWorkspaceOK :=
          {
            owned_disjoint := by
              simpa [
                ExtReg.OwnedDisjoint,
                ExtReg.ownedQubits_grow
              ] using hmod.dataCarry_work_disjoint

            x_reserve_sufficient := by
              rw [
                ExtReg.width_grow (data.grow 1) 1 hDataCarryGrow,
                ExtReg.width_grow data 1 hDataGrow,
                ExtReg.width_grow work 1 hWorkGrow,
                ExtReg.capacity_grow (data.grow 1) 1 hDataCarryGrow,
                ExtReg.capacity_grow data 1 hDataGrow
              ]
              rw [show data.width + 1 + 1 = data.width + 2 by omega]
              exact reserve_le_capacity_sub_two_of_two_add_le hDataStep5

            z_reserve_sufficient := by
              rw [
                ExtReg.width_grow (data.grow 1) 1 hDataCarryGrow,
                ExtReg.width_grow data 1 hDataGrow,
                ExtReg.width_grow work 1 hWorkGrow,
                ExtReg.capacity_grow work 1 hWorkGrow
              ]
              rw [show data.width + 1 + 1 = data.width + 2 by omega]
              exact reserve_le_capacity_sub_one_of_succ_le hWorkStep5
          }

        control_disjoint := by
          simpa [
            ExtReg.CtrlDisjoint,
            ExtReg.ownedQubits_grow
          ] using And.intro hctrlData hctrlWork
      }

    have hStep1Phase :
        CSignedRecursiveWorkspaceOK
          ops ctrl
          (hmod.step1Workspace.xExt.grow 1)
          (hmod.step1Workspace.zExt.grow 1) := by
      exact hStep1Static

    have hStep2Phase :
        SignedRecursiveWorkspaceOK
          ops
          (hmod.step2Workspace.xExt.grow 1)
          (hmod.step2Workspace.zExt.grow 1) := by
      simpa only [hStep2XExt, hStep2ZExt] using hStep2Static

    have hStep5Phase :
        CSignedRecursiveWorkspaceOK
          ops ctrl
          (hmod.step5Workspace.xExt.grow 1)
          (hmod.step5Workspace.zExt.grow 1) := by
      simpa only [hStep5XExt, hStep5ZExt] using hStep5Static

    have hStep1QFT :
        QFTReserveOK ops hmod.step1Workspace.zExt := by
      simpa only [hStep1ZExt] using hQFTWork

    have hStep2QFT :
        QFTReserveOK ops hmod.step2Workspace.zExt := by
      simpa only [hStep2ZExt] using hQFTDataCarry

    have hStep5QFT :
        QFTReserveOK ops hmod.step5Workspace.zExt := by
      simpa only [hStep5ZExt] using hQFTWork

    have hStep1OK :
        GateWorkspaceOK ops
          (step1
            (Basis := qs.Basis)
            c N ctrl data work hmod) := by
      simp [
        step1,
        IQFT,
        Gate.CPhaseProdUsing,
        GateWorkspaceOK,
        hHWork,
        hStep1Phase,
        hStep1QFT
      ]

    have hStep2OK :
        GateWorkspaceOK ops
          (step2
            (Basis := qs.Basis)
            N data work hmod) := by
      simp [
        step2,
        IQFT,
        Gate.PhaseProdUsing,
        GateWorkspaceOK,
        hStep2Phase,
        hStep2QFT
      ]

    have hStep5OK :
        GateWorkspaceOK ops
          (step5
            (Basis := qs.Basis)
            (step5Constant c N)
            N ctrl data work hmod) := by
      simp [
        step5,
        IQFT,
        Gate.CPhaseProdUsing,
        GateWorkspaceOK,
        hHWork,
        hStep5Phase,
        hStep5QFT
      ]

    simp [
      CmodMulInPlaceCore,
      step3,
      step4,
      GateWorkspaceOK,
      hStep1OK,
      hStep2OK,
      hStep5OK
    ]

  have hLayoutOfMem :
      ∀ ctrl ∈ x.active.qubits,
        ModMulCoreLayout data work flag ctrl := by
    intro ctrl hctrl
    rcases List.get_of_mem hctrl with ⟨j, hj⟩
    let i : Fin (regSize x.active) :=
      ⟨j.1, by
        simp[regSize, Reg.width]⟩
    have hget : x.active.get i = ctrl := by
      dsimp [i, Reg.get]
      simpa [Reg.width] using hj
    have hi := hsetup.register_layout i
    simpa only [hget] using hi

  have hSteps :
      ∀ (e : ℕ) (ctrls : List ℕ),
        (∀ ctrl ∈ ctrls,
          ModMulCoreLayout data work flag ctrl) →
        GateWorkspaceOK ops
          (modExpApproxStepsValid
            (Basis := qs.Basis)
            a N data work flag hmod e ctrls) := by
    intro e ctrls
    induction ctrls generalizing e with
    | nil =>
        intro _
        simp [modExpApproxStepsValid, GateWorkspaceOK]

    | cons ctrl ctrls ih =>
        intro hLayout
        have hHeadLayout :
            ModMulCoreLayout data work flag ctrl :=
          hLayout ctrl (by simp)
        have hTailLayout :
            ∀ q ∈ ctrls,
              ModMulCoreLayout data work flag q := by
          intro q hq
          exact hLayout q (by simp [hq])
        have hHead :=
          hCore ((a ^ (2 ^ e)) % N) ctrl hHeadLayout
        have hTail :=
          ih (e := e + 1) hTailLayout
        simpa [modExpApproxStepsValid] using
          And.intro hHead hTail

  have hHExponent :
      GateWorkspaceOK ops (H_reg x.active) :=
    gateWorkspaceOK_H_reg ops x.active

  have hInit :
      GateWorkspaceOK ops (initY1 data.active) := by
    cases hq : data.active.qubits with
    | nil =>
        simp [initY1, hq, GateWorkspaceOK]
    | cons q qs =>
        simp [initY1, hq, GateWorkspaceOK]

  have hModExp :
      GateWorkspaceOK ops
        (modExpApproxValid
          (Basis := qs.Basis)
          a N x.active data work flag hmod) :=
    hSteps 0 x.active.qubits hLayoutOfMem

  have hFinalQFT :
      GateWorkspaceOK ops (IQFT x) := by
    simpa [IQFT, GateWorkspaceOK] using hQFTX

  have hAll :
      GateWorkspaceOK ops (H_reg x.active) ∧
      GateWorkspaceOK ops (initY1 data.active) ∧
      GateWorkspaceOK ops
        (modExpApproxValid
          (Basis := qs.Basis)
          a N x.active data work flag hmod) ∧
      GateWorkspaceOK ops (IQFT x) :=
    ⟨hHExponent, hInit, hModExp, hFinalQFT⟩

  simpa [orderFindingApprox, GateWorkspaceOK, hmod] using hAll

/--
Public readiness package for both static workspace availability and dynamic
initial cleanliness.
-/
structure LoweredShorReady
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGateGateBridge qs]
    (lowering : ShorLoweringSetup)
    (η : ℝ)
    (a N : ℕ)
    (x y work : ExtReg)
    (flag : ℕ)
    (b0 : qs.Basis) :
    Prop where

  approx :
    ShorApproxSetupMinimal qs η x y work flag b0

  workspace_large_enough :
    ShorWorkspaceLargeEnough lowering.ops x y work

  workspace_isolated :
    ShorWorkspaceIsolation x work flag

  workspace_initially_zero :
    ShorWorkspaceCleanInput x y work b0
  -- clean :
  --   let hworkspace :=
  --     gateWorkspaceOK_orderFindingApprox (ops := lowering.ops)  (η := η) (a := a) (N := N)
  --       (x := x) (data := y) (work := work) (flag := flag) (b0 := b0) approx workspace_large_enough

  --   GateWorkspaceCleanState qs lowering.k lowering.hk lowering.ops
  --     (orderFindingApprox qs a N x y work flag  approx.circuit_workspace)
  --     hworkspace (qs.ket b0)
/-! =========================================================
    Section 2: Clean-result sequencing infrastructure
========================================================= -/

/-!
`LoweredCleanResult P G hworkspace ψ` says:

1. every recursively lowered gate in `G` starts with clean local workspace;
2. after executing the lowered `G`, the state satisfies `P`.
-/
private def LoweredCleanResult
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [LowerGateClass qs]
    [LowerGateGateBridge qs]
    (lowering : ShorLoweringSetup)
    (P : qs.State → Prop)
    (G : Gate)
    (hworkspace :
      GateWorkspaceOK lowering.ops G)
    (ψ : qs.State) :
    Prop :=
  GateWorkspaceCleanState
      qs
      lowering.k
      lowering.hk
      lowering.ops
      G
      hworkspace
      ψ
    ∧
  P
    (LowerGateClass.evalL
      (qs := qs)
      (lowerGate
        (Basis := qs.Basis)
        lowering.k
        lowering.hk
        lowering.ops
        G
        hworkspace)
      ψ)

private theorem LoweredCleanResult.seq
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGateGateBridge qs]
    {lowering : ShorLoweringSetup}
    {Pmid Pout : qs.State → Prop}
    {U V : Gate}
    (hworkspace :
      GateWorkspaceOK lowering.ops (U ;; V))
    (ψ : qs.State)
    (hU :
      LoweredCleanResult
        qs lowering Pmid
        U hworkspace.1 ψ)
    (hV :
      LoweredCleanResult
        qs lowering Pout
        V
        hworkspace.2
        (LowerGateClass.evalL
          (qs := qs)
          (lowerGate
            (Basis := qs.Basis)
            lowering.k
            lowering.hk
            lowering.ops
            U
            hworkspace.1)
          ψ)) :
    LoweredCleanResult
      qs lowering Pout
      (U ;; V)
      hworkspace
      ψ := by
  constructor
  · exact ⟨hU.1, hV.1⟩
  · change
      Pout
        (LowerGateClass.evalL
          (qs := qs)
          (LowGate.seq
            (lowerGate
              (Basis := qs.Basis)
              lowering.k
              lowering.hk
              lowering.ops
              U
              hworkspace.1)
            (lowerGate
              (Basis := qs.Basis)
              lowering.k
              lowering.hk
              lowering.ops
              V
              hworkspace.2))
          ψ)

    rw [LowerGateClass.evalL_seq]
    exact hV.2

/-! =========================================================
    Section 3: Workspace-free gates

    These gates have no recursive lowerer workspace obligations. The final
    helper of this section, `WorkspaceFree.clean`, turns that syntactic fact
    into `GateWorkspaceCleanState`.
========================================================= -/

/--
A gate whose syntax contains no QFT or recursive phase-product nodes.

Such gates have no dynamic lowering-workspace cleanliness obligations.
-/
private inductive WorkspaceFree : Gate → Prop
  | id :
      WorkspaceFree Gate.id

  | H (q : ℕ) :
      WorkspaceFree (Gate.H q)

  | X (q : ℕ) :
      WorkspaceFree (Gate.X q)

  | seq
      {U V : Gate}
      (hU : WorkspaceFree U)
      (hV : WorkspaceFree V) :
      WorkspaceFree (U ;; V)


private theorem WorkspaceFree.clean
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [LowerGateClass qs]
    [LowerGateGateBridge qs]
    {lowering : ShorLoweringSetup}
    {G : Gate}
    (hfree : WorkspaceFree G)
    (hworkspace :
      GateWorkspaceOK lowering.ops G)
    (ψ : qs.State) :
    GateWorkspaceCleanState
      qs
      lowering.k
      lowering.hk
      lowering.ops
      G
      hworkspace
      ψ := by
  induction hfree generalizing ψ with
  | id =>
      trivial

  | H q =>
      trivial

  | X q =>
      trivial

  | @seq U V hU hV ihU ihV =>
      change
        GateWorkspaceCleanState
            qs
            lowering.k
            lowering.hk
            lowering.ops
            U
            hworkspace.1
            ψ
          ∧
        GateWorkspaceCleanState
            qs
            lowering.k
            lowering.hk
            lowering.ops
            V
            hworkspace.2
            (LowerGateClass.evalL
              (qs := qs)
              (lowerGate
                (Basis := qs.Basis)
                lowering.k
                lowering.hk
                lowering.ops
                U
                hworkspace.1)
              ψ)

      exact
        ⟨ihU hworkspace.1 ψ,
          ihV hworkspace.2
            (LowerGateClass.evalL
              (qs := qs)
              (lowerGate
                (Basis := qs.Basis)
                lowering.k
                lowering.hk
                lowering.ops
                U
                hworkspace.1)
              ψ)⟩

private lemma workspaceFree_H_reg
    (r : Reg) :
    WorkspaceFree (H_reg r) := by
  unfold H_reg

  have hfold :
      ∀ (qubits : List ℕ) (acc : Gate),
        WorkspaceFree acc →
        WorkspaceFree
          (qubits.foldl
            (fun acc q => (Gate.H q) ;; acc)
            acc) := by
    intro qubits

    induction qubits with
    | nil =>
        intro acc hacc
        simpa

    | cons q qubits ih =>
        intro acc hacc
        simp only [List.foldl]

        exact
          ih
            ((Gate.H q) ;; acc)
            (WorkspaceFree.seq
              (WorkspaceFree.H q)
              hacc)

  exact
    hfold
      r.qubits
      Gate.id
      WorkspaceFree.id

private lemma workspaceFree_initY1
    (r : Reg) :
    WorkspaceFree (initY1 r) := by
  cases hqubits : r.qubits with
  | nil =>
      simpa [initY1, hqubits] using
        WorkspaceFree.id

  | cons q qubits =>
      simpa [initY1, hqubits] using
        WorkspaceFree.X q

/-! =========================================================
    Section 4: Primitive locality and Step 3/4 readiness

    The disjointness helpers feed the primitive semantic locality assumptions
    for Steps 3 and 4. The final theorems in this section are
    `lowered_step3_ready_and_clean` and `lowered_step4_ready_and_clean`.
========================================================= -/

private lemma reserve_active_disjoint_of_ownedDisjoint
    {x y : ExtReg}
    (hxy :
      ExtReg.OwnedDisjoint x y) :
    Disjoint x.reserve y.active := by
  rw [
    ExtReg.OwnedDisjoint,
    List.disjoint_left
  ] at hxy

  rw [Disjoint, List.disjoint_left]

  intro q hqReserve hqActive

  have hqOwnedX : q ∈ x.ownedQubits := by
    rw [ExtReg.ownedQubits, List.mem_append]
    exact Or.inr hqReserve

  have hqOwnedY : q ∈ y.ownedQubits := by
    rw [ExtReg.ownedQubits, List.mem_append]
    exact Or.inl hqActive

  exact hxy hqOwnedX hqOwnedY

private lemma ownedDisjoint_symm
    {x y : ExtReg}
    (hxy :
      ExtReg.OwnedDisjoint x y) :
    ExtReg.OwnedDisjoint y x := by
  exact List.Disjoint.symm hxy

private lemma disjoint_qubitReg_of_mem_right
    {r s : Reg}
    {q : ℕ}
    (hrs : Disjoint r s)
    (hq : q ∈ s.qubits) :
    Disjoint r (qubitReg q) := by
  rw [Disjoint, List.disjoint_left] at hrs ⊢

  intro p hp hpSingle

  have hpq : p = q := by
    simpa [qubitReg, Reg.singleton] using hpSingle

  subst p
  exact hrs hp hq

private lemma disjoint_drop_left
    {r s : Reg}
    (hrs : Disjoint r s)
    (n : ℕ) :
    Disjoint (r.drop n) s := by
  rw [Disjoint, List.disjoint_left] at hrs ⊢
  intro q hqDrop hqS
  exact hrs (List.mem_of_mem_drop hqDrop) hqS

private lemma reserve_drop_active_disjoint_of_ownedDisjoint
    {x y : ExtReg}
    (hxy :
      ExtReg.OwnedDisjoint x y)
    (n : ℕ) :
    Disjoint (x.reserve.drop n) y.active :=
  disjoint_drop_left
    (reserve_active_disjoint_of_ownedDisjoint hxy)
    n

private lemma reserve_drop_active_disjoint_self
    (x : ExtReg)
    (n : ℕ) :
    Disjoint (x.reserve.drop n) x.active :=
  disjoint_drop_left
    (Disjoint.symm x.active_reserve_disjoint)
    n

/-- Every active qubit after growing was already owned by the original
extendable register. -/
private lemma mem_grow_active_owned
    (e : ExtReg)
    (n : ℕ)
    {q : ℕ}
    (hq :
      q ∈ (e.grow n).active.qubits) :
    q ∈ e.ownedQubits := by
  have hq' :
      q ∈
        e.active.qubits ++
          List.take n e.reserve.qubits := by
    simpa [
      ExtReg.grow,
      ExtReg.newBits,
      Reg.append,
      Reg.take
    ] using hq

  rw [ExtReg.ownedQubits, List.mem_append]
  rcases List.mem_append.mp hq' with hqActive | hqNew
  · exact Or.inl hqActive
  · exact Or.inr (List.mem_of_mem_take hqNew)

/-- A reserve remains disjoint from the active portion of a disjoint
register after that register is grown. -/
private lemma reserve_grow_active_disjoint_of_ownedDisjoint
    {x y : ExtReg}
    (hxy :
      ExtReg.OwnedDisjoint x y)
    (n : ℕ) :
    Disjoint x.reserve (y.grow n).active := by
  have hxy' := hxy
  rw [
    ExtReg.OwnedDisjoint,
    List.disjoint_left
  ] at hxy'

  rw [Disjoint, List.disjoint_left]
  intro q hqx hqGrow

  apply hxy'
  · rw [ExtReg.ownedQubits, List.mem_append]
    exact Or.inr hqx
  · exact mem_grow_active_owned y n hqGrow

/-- The reserve remaining after growth is disjoint from the grown active
register. -/
private lemma reserve_drop_grow_active_disjoint_self
    (e : ExtReg)
    (n : ℕ) :
    Disjoint
      (e.reserve.drop n)
      (e.grow n).active := by
  simpa [
    ExtReg.grow,
    ExtReg.remainingReserve
  ] using
    (Disjoint.symm
      (e.grow n).active_reserve_disjoint)

/-- Membership in the left side of a disjoint pair implies nonmembership
in the right side. -/
private lemma not_mem_right_of_mem_left_of_disjoint
    {r s : Reg}
    (hrs : Disjoint r s)
    {q : ℕ}
    (hq : q ∈ r.qubits) :
    q ∉ s.qubits := by
  rw [Disjoint, List.disjoint_left] at hrs
  exact hrs hq

private theorem eval_step3_preserves_lowering_clean
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [ModMulPrimitiveGateSemantics qs]
    (x data work : ExtReg)
    (N flag : ℕ)
    (hxData :
      ExtReg.OwnedDisjoint x data)
    (hmod :
      ModMulCircuitWorkspaceOK data work)
    (hflagX :
      flag ∉ x.ownedQubits)
    (hflagData :
      flag ∉ data.ownedQubits)
    (hflagWork :
      flag ∉ work.ownedQubits)
    {ψ : qs.State}
    (hclean :
      ShorLoweringCleanState
        qs x data work ψ) :
    ShorLoweringCleanState
      qs x data work
      (qs.eval
        (step3
          N
          (data.grow 1).active
          flag)
        ψ) := by
  have hxCarry :
      Disjoint
        x.reserve
        (data.grow 1).active :=
    reserve_grow_active_disjoint_of_ownedDisjoint
      hxData 1

  have hdataCarry :
      Disjoint
        (data.reserve.drop 1)
        (data.grow 1).active :=
    reserve_drop_grow_active_disjoint_self data 1

  have hworkCarry :
      Disjoint
        work.reserve
        (data.grow 1).active :=
    reserve_active_disjoint_of_ownedDisjoint
      hmod.work_dataCarry_disjoint

  induction hclean with
  | zero =>
      rw [qs.eval_zero]
      exact ThreeRegsCleanState.zero

  | ket b hx hdata hwork =>
      rcases
          eval_step3_local_ket_of_primitive
            (qs := qs)
            N
            (data.grow 1).active
            flag
            b
            (by
              intro hq
              apply hflagData
              have howned :
                  flag ∈ (data.grow 1).ownedQubits :=
                List.mem_append_left _ hq
              simpa [Gate.ExtReg.ownedQubits_grow] using howned) with
        ⟨b', heval, hlocal⟩

      rw [heval]
      apply ThreeRegsCleanState.ket

      · exact
          FreshZero.of_eq_on_bits
            x.reserve
            b
            b'
            (by
              intro q hq

              apply hlocal q
              · exact
                  not_mem_right_of_mem_left_of_disjoint
                    hxCarry hq
              · intro hqFlag
                subst q
                apply hflagX
                rw [
                  ExtReg.ownedQubits,
                  List.mem_append
                ]
                exact Or.inr hq)
            hx

      · exact
          FreshZero.of_eq_on_bits
            (data.reserve.drop 1)
            b
            b'
            (by
              intro q hq

              apply hlocal q
              · exact
                  not_mem_right_of_mem_left_of_disjoint
                    hdataCarry hq
              · intro hqFlag
                subst q
                apply hflagData
                rw [
                  ExtReg.ownedQubits,
                  List.mem_append
                ]
                exact
                  Or.inr
                    (List.mem_of_mem_drop hq))
            hdata

      · exact
          FreshZero.of_eq_on_bits
            work.reserve
            b
            b'
            (by
              intro q hq

              apply hlocal q
              · exact
                  not_mem_right_of_mem_left_of_disjoint
                    hworkCarry hq
              · intro hqFlag
                subst q
                apply hflagWork
                rw [
                  ExtReg.ownedQubits,
                  List.mem_append
                ]
                exact Or.inr hq)
            hwork

  | add hψ hφ ihψ ihφ =>
      rw [qs.eval_add]
      exact
        ThreeRegsCleanState.add
          ihψ ihφ

  | smul a hψ ihψ =>
      rw [qs.eval_smul]
      exact
        ThreeRegsCleanState.smul
          a ihψ

private theorem eval_step4_preserves_lowering_clean
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [ModMulPrimitiveGateSemantics qs]
    (x data work : ExtReg)
    (N flag : ℕ)
    (hxData :
      ExtReg.OwnedDisjoint x data)
    (hxWork :
      ExtReg.OwnedDisjoint x work)
    (hmod :
      ModMulCircuitWorkspaceOK data work)
    (hflagX :
      flag ∉ x.ownedQubits)
    (hflagData :
      flag ∉ data.ownedQubits)
    (hflagWork :
      flag ∉ work.ownedQubits)
    {ψ : qs.State}
    (hclean :
      ShorLoweringCleanState
        qs x data work ψ) :
    ShorLoweringCleanState
      qs x data work
      (qs.eval
        (step4
          N
          (data.grow 1).active
          work.active
          flag)
        ψ) := by
  have hxCarry :
      Disjoint
        x.reserve
        (data.grow 1).active :=
    reserve_grow_active_disjoint_of_ownedDisjoint
      hxData 1

  have hxWorkActive :
      Disjoint
        x.reserve
        work.active :=
    reserve_active_disjoint_of_ownedDisjoint
      hxWork

  have hdataCarry :
      Disjoint
        (data.reserve.drop 1)
        (data.grow 1).active :=
    reserve_drop_grow_active_disjoint_self data 1

  have hdataWorkActive :
      Disjoint
        (data.reserve.drop 1)
        work.active :=
    reserve_drop_active_disjoint_of_ownedDisjoint
      hmod.2.2
      1

  have hworkCarry :
      Disjoint
        work.reserve
        (data.grow 1).active :=
    reserve_active_disjoint_of_ownedDisjoint
      hmod.work_dataCarry_disjoint

  have hworkWorkActive :
      Disjoint
        work.reserve
        work.active :=
    Disjoint.symm
      work.active_reserve_disjoint

  induction hclean with
  | zero =>
      rw [qs.eval_zero]
      exact ThreeRegsCleanState.zero

  | ket b hx hdata hwork =>
      rcases
          eval_step4_local_ket_of_primitive
            (qs := qs)
            N
            (data.grow 1).active
            work.active
            flag
            b
            (by
              intro hq
              apply hflagData
              have howned :
                  flag ∈ (data.grow 1).ownedQubits :=
                List.mem_append_left _ hq
              simpa [Gate.ExtReg.ownedQubits_grow] using howned)
            (by
              intro hq
              apply hflagWork
              rw [
                ExtReg.ownedQubits,
                List.mem_append
              ]
              exact Or.inl hq) with
        ⟨b', heval, hlocal⟩

      rw [heval]
      apply ThreeRegsCleanState.ket

      · exact
          FreshZero.of_eq_on_bits
            x.reserve
            b
            b'
            (by
              intro q hq

              apply hlocal q
              · exact
                  not_mem_right_of_mem_left_of_disjoint
                    hxCarry hq
              · exact
                  not_mem_right_of_mem_left_of_disjoint
                    hxWorkActive hq
              · intro hqFlag
                subst q
                apply hflagX
                rw [
                  ExtReg.ownedQubits,
                  List.mem_append
                ]
                exact Or.inr hq)
            hx

      · exact
          FreshZero.of_eq_on_bits
            (data.reserve.drop 1)
            b
            b'
            (by
              intro q hq

              apply hlocal q
              · exact
                  not_mem_right_of_mem_left_of_disjoint
                    hdataCarry hq
              · exact
                  not_mem_right_of_mem_left_of_disjoint
                    hdataWorkActive hq
              · intro hqFlag
                subst q
                apply hflagData
                rw [
                  ExtReg.ownedQubits,
                  List.mem_append
                ]
                exact
                  Or.inr
                    (List.mem_of_mem_drop hq))
            hdata

      · exact
          FreshZero.of_eq_on_bits
            work.reserve
            b
            b'
            (by
              intro q hq

              apply hlocal q
              · exact
                  not_mem_right_of_mem_left_of_disjoint
                    hworkCarry hq
              · exact
                  not_mem_right_of_mem_left_of_disjoint
                    hworkWorkActive hq
              · intro hqFlag
                subst q
                apply hflagWork
                rw [
                  ExtReg.ownedQubits,
                  List.mem_append
                ]
                exact Or.inr hq)
            hwork

  | add hψ hφ ihψ ihφ =>
      rw [qs.eval_add]
      exact
        ThreeRegsCleanState.add
          ihψ ihφ

  | smul a hψ ihψ =>
      rw [qs.eval_smul]
      exact
        ThreeRegsCleanState.smul
          a ihψ

private theorem lowered_step3_ready_and_clean
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGateGateBridge qs]
    [ModMulPrimitiveGateSemantics qs]
    (lowering : ShorLoweringSetup)
    (x data work : ExtReg)
    (N flag : ℕ)
    (hxData :
      ExtReg.OwnedDisjoint x data)
    (_hxWork :
      ExtReg.OwnedDisjoint x work)
    (hmod :
      ModMulCircuitWorkspaceOK data work)
    (hflagX :
      flag ∉ x.ownedQubits)
    (hflagData :
      flag ∉ data.ownedQubits)
    (hflagWork :
      flag ∉ work.ownedQubits)
    (hworkspace :
      GateWorkspaceOK
        lowering.ops
        (step3 N (data.grow 1).active flag))
    (ψ : qs.State)
    (hclean :
      ShorLoweringCleanState
        qs x data work ψ) :
    LoweredCleanResult
      qs
      lowering
      (ShorLoweringCleanState
        qs x data work)
      (step3 N (data.grow 1).active flag)
      hworkspace
      ψ := by
  have hgateClean :
      GateWorkspaceCleanState
        qs
        lowering.k
        lowering.hk
        lowering.ops
        (step3 N (data.grow 1).active flag)
        hworkspace
        ψ := by
    simp [step3, GateWorkspaceCleanState]

  constructor
  · exact hgateClean

  · rw [
      lowerGate_correctness
        qs
        lowering.k
        lowering.hk
        lowering.ops
        lowering.consumes
        lowering.returns
        (step3 N (data.grow 1).active flag)
        hworkspace
        ψ
        hgateClean
    ]

    exact
      eval_step3_preserves_lowering_clean
        x
        data
        work
        N
        flag
        hxData
        hmod
        hflagX
        hflagData
        hflagWork
        hclean

private theorem lowered_step4_ready_and_clean
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGateGateBridge qs]
    [ModMulPrimitiveGateSemantics qs]
    (lowering : ShorLoweringSetup)
    (x data work : ExtReg)
    (N flag : ℕ)
    (hxData :
      ExtReg.OwnedDisjoint x data)
    (hxWork :
      ExtReg.OwnedDisjoint x work)
    (hmod :
      ModMulCircuitWorkspaceOK data work)
    (hflagX :
      flag ∉ x.ownedQubits)
    (hflagData :
      flag ∉ data.ownedQubits)
    (hflagWork :
      flag ∉ work.ownedQubits)
    (hworkspace :
      GateWorkspaceOK
        lowering.ops
        (step4
          N
          (data.grow 1).active
          work.active
          flag))
    (ψ : qs.State)
    (hclean :
      ShorLoweringCleanState
        qs x data work ψ) :
    LoweredCleanResult
      qs
      lowering
      (ShorLoweringCleanState
        qs x data work)
      (step4
        N
        (data.grow 1).active
        work.active
        flag)
      hworkspace
      ψ := by
  have hgateClean :
      GateWorkspaceCleanState
        qs
        lowering.k
        lowering.hk
        lowering.ops
        (step4
          N
          (data.grow 1).active
          work.active
          flag)
        hworkspace
        ψ := by
    simp [step4, GateWorkspaceCleanState]

  constructor
  · exact hgateClean

  · rw [
      lowerGate_correctness
        qs
        lowering.k
        lowering.hk
        lowering.ops
        lowering.consumes
        lowering.returns
        (step4
          N
          (data.grow 1).active
          work.active
          flag)
        hworkspace
        ψ
        hgateClean
    ]

    exact
      eval_step4_preserves_lowering_clean
        x
        data
        work
        N
        flag
        hxData
        hxWork
        hmod
        hflagX
        hflagData
        hflagWork
        hclean

/-! =========================================================
    Section 5: Workspace-free initialization gates

    These helpers cover `H_reg x.active` and `initY1 data.active`, which do not
    allocate recursive lowering workspace but must still preserve the global
    lowered clean invariant.
========================================================= -/

private theorem eval_H_reg_preserves_threeRegsCleanState
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (r r₁ r₂ r₃ : Reg)
    {ψ : qs.State}
    (h₁r : Disjoint r₁ r)
    (h₂r : Disjoint r₂ r)
    (h₃r : Disjoint r₃ r)
    (hclean :
      ThreeRegsCleanState
        qs r₁ r₂ r₃ ψ) :
    ThreeRegsCleanState
      qs r₁ r₂ r₃
      (qs.eval (H_reg r) ψ) := by
  induction hclean with
  | zero =>
      rw [qs.eval_zero]
      exact ThreeRegsCleanState.zero

  | ket b h₁ h₂ h₃ =>
      classical

      rcases
          RegisterHadamardSemantics.eval_Hreg_ket
            r b with
        ⟨α, heval⟩

      have heval' :
          qs.eval (H_reg r) (qs.ket b)
            =
          ∑ t : Fin (ASize r),
            α t •
              qs.ket
                (RegEncoding.writeNat r t.1 b) := by
        simpa [H_reg] using heval

      rw [heval']

      let f : Fin (ASize r) → qs.State :=
        fun t =>
          α t •
            qs.ket
              (RegEncoding.writeNat r t.1 b)

      have hterm :
          ∀ t : Fin (ASize r),
            ThreeRegsCleanState
              qs r₁ r₂ r₃
              (f t) := by
        intro t

        apply ThreeRegsCleanState.smul
        apply ThreeRegsCleanState.ket

        · unfold FreshZero at h₁ ⊢
          rw [
            RegEncoding.toNat_left_write_right
              r₁ r h₁r b t.1
          ]
          exact h₁

        · unfold FreshZero at h₂ ⊢
          rw [
            RegEncoding.toNat_left_write_right
              r₂ r h₂r b t.1
          ]
          exact h₂

        · unfold FreshZero at h₃ ⊢
          rw [
            RegEncoding.toNat_left_write_right
              r₃ r h₃r b t.1
          ]
          exact h₃

      have hsum :
          ∀ s : Finset (Fin (ASize r)),
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

      simpa [f] using hsum Finset.univ

  | add hψ hφ ihψ ihφ =>
      rw [qs.eval_add]
      exact ThreeRegsCleanState.add ihψ ihφ

  | smul a hψ ihψ =>
      rw [qs.eval_smul]
      exact ThreeRegsCleanState.smul a ihψ


private theorem eval_X_preserves_threeRegsCleanState
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (q : ℕ)
    (r₁ r₂ r₃ : Reg)
    {ψ : qs.State}
    (h₁q :
      Disjoint r₁ (qubitReg q))
    (h₂q :
      Disjoint r₂ (qubitReg q))
    (h₃q :
      Disjoint r₃ (qubitReg q))
    (hclean :
      ThreeRegsCleanState
        qs r₁ r₂ r₃ ψ) :
    ThreeRegsCleanState
      qs r₁ r₂ r₃
      (qs.eval (Gate.X q) ψ) := by
  induction hclean with
  | zero =>
      rw [qs.eval_zero]
      exact ThreeRegsCleanState.zero

  | ket b h₁ h₂ h₃ =>
      rw [PauliXSemantics.eval_X_ket]

      apply ThreeRegsCleanState.ket

      · unfold FreshZero at h₁ ⊢
        rw [
          RegEncoding.toNat_left_write_right
            r₁
            (qubitReg q)
            h₁q
            b
            (if RegEncoding.bit q b then 0 else 1)
        ]
        exact h₁

      · unfold FreshZero at h₂ ⊢
        rw [
          RegEncoding.toNat_left_write_right
            r₂
            (qubitReg q)
            h₂q
            b
            (if RegEncoding.bit q b then 0 else 1)
        ]
        exact h₂

      · unfold FreshZero at h₃ ⊢
        rw [
          RegEncoding.toNat_left_write_right
            r₃
            (qubitReg q)
            h₃q
            b
            (if RegEncoding.bit q b then 0 else 1)
        ]
        exact h₃

  | add hψ hφ ihψ ihφ =>
      rw [qs.eval_add]
      exact ThreeRegsCleanState.add ihψ ihφ

  | smul a hψ ihψ =>
      rw [qs.eval_smul]
      exact ThreeRegsCleanState.smul a ihψ

private theorem lowered_H_reg_ready_and_full_clean
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGateGateBridge qs]
    (lowering : ShorLoweringSetup)
    (x data work : ExtReg)
    (hxData :
      ExtReg.OwnedDisjoint x data)
    (hxWork :
      ExtReg.OwnedDisjoint x work)
    (hworkspace :
      GateWorkspaceOK
        lowering.ops
        (H_reg x.active))
    (ψ : qs.State)
    (hclean :
      ShorLoweringCleanState
        qs x data work ψ) :
    LoweredCleanResult
      qs
      lowering
      (ShorLoweringCleanState
        qs x data work)
      (H_reg x.active)
      hworkspace
      ψ := by
  have hgateClean :
      GateWorkspaceCleanState
        qs
        lowering.k
        lowering.hk
        lowering.ops
        (H_reg x.active)
        hworkspace
        ψ :=
    (workspaceFree_H_reg x.active).clean
      hworkspace ψ

  have hxReserve :
      Disjoint x.reserve x.active :=
    Disjoint.symm
      x.active_reserve_disjoint

  have hdataReserve :
      Disjoint (data.reserve.drop 1) x.active :=
    reserve_drop_active_disjoint_of_ownedDisjoint
      (ownedDisjoint_symm hxData)
      1

  have hworkReserve :
      Disjoint work.reserve x.active :=
    reserve_active_disjoint_of_ownedDisjoint
      (ownedDisjoint_symm hxWork)

  constructor

  · exact hgateClean

  · rw [
      lowerGate_correctness
        qs
        lowering.k
        lowering.hk
        lowering.ops
        lowering.consumes
        lowering.returns
        (H_reg x.active)
        hworkspace
        ψ
        hgateClean
    ]

    exact
      eval_H_reg_preserves_threeRegsCleanState
        x.active
        x.reserve
        (data.reserve.drop 1)
        work.reserve
        hxReserve
        hdataReserve
        hworkReserve
        hclean

private theorem eval_initY1_preserves_fullShorWorkspaceCleanState
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (x data work : ExtReg)
    (hxData :
      ExtReg.OwnedDisjoint x data)
    (hmod :
      ModMulCircuitWorkspaceOK data work)
    {ψ : qs.State}
    (hclean :
      ShorLoweringCleanState
        qs x data work ψ) :
    ShorLoweringCleanState
      qs x data work
      (qs.eval (initY1 data.active) ψ) := by
  cases hqubits : data.active.qubits with
  | nil =>
      have hgate :
          initY1 data.active = Gate.id := by
        simp [initY1, hqubits]

      rw [hgate, qs.eval_id]
      exact hclean

  | cons q qubits =>
      have hgate :
          initY1 data.active = Gate.X q := by
        simp [initY1, hqubits]

      have hqActive :
          q ∈ data.active.qubits := by
        simp [hqubits]

      have hxReserveData :
          Disjoint x.reserve data.active :=
        reserve_active_disjoint_of_ownedDisjoint
          hxData

      have hdataReserveData :
          Disjoint (data.reserve.drop 1) data.active :=
        reserve_drop_active_disjoint_self data 1

      have hworkDataOwned :
          ExtReg.OwnedDisjoint work data :=
        ownedDisjoint_symm hmod.2.2

      have hworkReserveData :
          Disjoint work.reserve data.active :=
        reserve_active_disjoint_of_ownedDisjoint
          hworkDataOwned

      have hxQubit :
          Disjoint x.reserve (qubitReg q) :=
        disjoint_qubitReg_of_mem_right
          hxReserveData
          hqActive

      have hdataQubit :
          Disjoint (data.reserve.drop 1) (qubitReg q) :=
        disjoint_qubitReg_of_mem_right
          hdataReserveData
          hqActive

      have hworkQubit :
          Disjoint work.reserve (qubitReg q) :=
        disjoint_qubitReg_of_mem_right
          hworkReserveData
          hqActive

      rw [hgate]

      exact
        eval_X_preserves_threeRegsCleanState
          q
          x.reserve
          (data.reserve.drop 1)
          work.reserve
          hxQubit
          hdataQubit
          hworkQubit
          hclean

private theorem lowered_initY1_ready_and_full_clean
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGateGateBridge qs]
    (lowering : ShorLoweringSetup)
    (x data work : ExtReg)
    (hxData :
      ExtReg.OwnedDisjoint x data)
    (hmod :
      ModMulCircuitWorkspaceOK data work)
    (hworkspace :
      GateWorkspaceOK
        lowering.ops
        (initY1 data.active))
    (ψ : qs.State)
    (hclean :
      ShorLoweringCleanState
        qs x data work ψ) :
    LoweredCleanResult
      qs
      lowering
      (ShorLoweringCleanState
        qs x data work)
      (initY1 data.active)
      hworkspace
      ψ := by
  have hgateClean :
      GateWorkspaceCleanState
        qs
        lowering.k
        lowering.hk
        lowering.ops
        (initY1 data.active)
        hworkspace
        ψ :=
    (workspaceFree_initY1 data.active).clean
      hworkspace ψ

  constructor

  · exact hgateClean

  · rw [
      lowerGate_correctness
        qs
        lowering.k
        lowering.hk
        lowering.ops
        lowering.consumes
        lowering.returns
        (initY1 data.active)
        hworkspace
        ψ
        hgateClean
    ]

    exact
      eval_initY1_preserves_fullShorWorkspaceCleanState
        x
        data
        work
        hxData
        hmod
        hclean

/-! =========================================================
    Section 6: Step 1 readiness

    Step 1 uses the data reserve after dropping the carry bit and the full work
    reserve. The final theorem in this section is
    `lowered_step1_ready_and_full_clean`.
========================================================= -/

private theorem threeRegsCleanState_to_grownRecursiveWorkspaceCleanState
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    {r₁ r₂ r₃ : Reg}
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
    RecursiveWorkspaceCleanState
      qs
      (ws.xExt.grow 1)
      (ws.zExt.grow 1)
      ψ := by
  induction hclean with
  | zero =>
      exact CleanClosure.zero

  | ket b h₁ h₂ h₃ =>
      have hxZero :
          FreshZero ws.xExt.reserve b := by
        simpa only [hxReserve] using h₂

      have hzZero :
          FreshZero ws.zExt.reserve b := by
        simpa only [hzReserve] using h₃

      exact
        CleanClosure.ket
          b
          ⟨
            freshFor_grow_capacity_of_freshZero_reserve
              ws.xExt 1 b hxZero,
            freshFor_grow_capacity_of_freshZero_reserve
              ws.zExt 1 b hzZero
          ⟩

  | add hψ hφ ihψ ihφ =>
      exact
        CleanClosure.add
          ihψ
          ihφ

  | smul a hψ ihψ =>
      exact
        CleanClosure.smul
          a
          ihψ

private theorem gateWorkspaceCleanState_CPhaseProdUsing_of_threeRegsClean
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGateGateBridge qs]
    {lowering : ShorLoweringSetup}
    {r₁ r₂ r₃ : Reg}
    {x z : Reg}
    (ctrl : ℕ)
    (φ : ℝ)
    (ws : Gate.PhaseProdWorkspace x z)
    (hxReserve :
      ws.xExt.reserve = r₂)
    (hzReserve :
      ws.zExt.reserve = r₃)
    (hworkspace :
      GateWorkspaceOK
        lowering.ops
        (Gate.CPhaseProdUsing
          ctrl φ x z ws))
    (ψ : qs.State)
    (hclean :
      ThreeRegsCleanState
        qs r₁ r₂ r₃ ψ) :
    GateWorkspaceCleanState
      qs
      lowering.k
      lowering.hk
      lowering.ops
      (Gate.CPhaseProdUsing
        ctrl φ x z ws)
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
    Gate.CPhaseProdUsing,
    GateWorkspaceCleanState,
    lowerGate,
    LowerGateClass.evalL_zeroExtend,
    ExtensionSemantics.eval_zeroExtend
  ] using hrecursive


private theorem eval_CPhaseProdUsing_preserves_threeRegsCleanState
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {r₁ r₂ r₃ : Reg}
    (ctrl : ℕ)
    (φ : ℝ)
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
        (Gate.CPhaseProdUsing
          ctrl φ x z ws)
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
        GateSemanticsFacts.eval_CPhaseProdUsing_ket
          qs
          ctrl
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

private theorem eval_IQFT_preserves_threeRegsCleanState
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
      (qs.eval (IQFT r) ψ) := by
  classical

  induction hclean with
  | zero =>
      rw [qs.eval_zero]
      exact ThreeRegsCleanState.zero

  | ket b h₁ h₂ h₃ =>
      rcases
          eval_iqft_work_expansion
            qs r b with
        ⟨α, heval⟩

      rw [heval]

      let f :
          Fin (ASize r.active) →
            qs.State :=
        fun t =>
          α t •
            qs.ket
              (RegEncoding.writeNat
                r.active
                t.1
                b)

      have hterm :
          ∀ t : Fin (ASize r.active),
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
          ∀ s : Finset (Fin (ASize r.active)),
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

      simpa [f] using hsum Finset.univ

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


private theorem threeRegsCleanState_to_QFTWorkspaceCleanState
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    {k : ℕ}
    (ops : Prog k)
    (r : ExtReg)
    {r₁ r₂ r₃ : Reg}
    (hreserve :
      r.reserve = r₃)
    {ψ : qs.State}
    (hclean :
      ThreeRegsCleanState
        qs r₁ r₂ r₃ ψ) :
    QFTWorkspaceCleanState
      qs
      (qftXWork ops r)
      (qftZWork ops r)
      ψ := by
  induction hclean with
  | zero =>
      exact QFTWorkspaceCleanState.zero

  | ket b h₁ h₂ h₃ =>
      apply QFTWorkspaceCleanState.ket b

      · apply FreshZero.of_subset
          (qftXWork ops r)
          r₃
          b
        · intro q hq

          simpa only [hreserve] using
            qftXWork_mem_reserve
              ops r hq

        · exact h₃

      · apply FreshZero.of_subset
          (qftZWork ops r)
          r₃
          b
        · intro q hq

          simpa only [hreserve] using
            qftZWork_mem_reserve
              ops r hq

        · exact h₃

  | add hψ hφ ihψ ihφ =>
      exact
        QFTWorkspaceCleanState.add
          ihψ
          ihφ

  | smul a hψ ihψ =>
      exact
        QFTWorkspaceCleanState.smul
          a
          ihψ

/-! =========================================================
    Section 7: Step 2 readiness

    Step 2 makes the carry bit active, swaps the phase-product operand order,
    and preserves `ShorLoweringCleanState`.
========================================================= -/

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
    [LowerGateGateBridge qs]
    {lowering : ShorLoweringSetup}
    {r₁ r₂ r₃ : Reg}
    {x z : Reg}
    (φ : ℝ)
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
    (φ : ℝ)
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

private theorem lowered_step1_ready_and_full_clean
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGateGateBridge qs]
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
          (Basis := qs.Basis)
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
        (Basis := qs.Basis)
        c N ctrl data work hmod)
      hworkspace
      ψ := by
  let φ : ℝ :=
    (2 * Real.pi *
      (((c + N - 1) % N : ℕ) : ℝ))
      /
    (N : ℝ)

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
        (Basis := qs.Basis)
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
        (Basis := qs.Basis)
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


private theorem lowered_step2_ready_and_carry_clean
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGateGateBridge qs]
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
          (Basis := qs.Basis)
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
        (Basis := qs.Basis)
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

  let φ : ℝ :=
    (2 * Real.pi * (N : ℝ)) /
      ((2 : ℝ) ^
        (regSize work.active + regSize dc.active))

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
        (Basis := qs.Basis)
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
        (Basis := qs.Basis)
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

/-! =========================================================
    Section 8: Step 5 readiness via adjoint decomposition

    Step 5 is proved by proving the forward Step-5 body clean, then using the
    generic adjoint lemma `LoweredCleanResult.adj`.
========================================================= -/

private theorem LoweredCleanResult.adj
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGateGateBridge qs]
    {lowering : ShorLoweringSetup}
    {P : qs.State → Prop}
    {U : Gate}
    {hworkspace :
      GateWorkspaceOK lowering.ops U}
    {ψ : qs.State}
    (hpost :
      P (qs.eval (†U) ψ))
    (hforward :
      LoweredCleanResult
        qs
        lowering
        P
        U
        hworkspace
        (qs.eval (†U) ψ)) :
    LoweredCleanResult
      qs
      lowering
      P
      (†U)
      hworkspace
      ψ := by
  have hadjClean :
      GateWorkspaceCleanState
        qs
        lowering.k
        lowering.hk
        lowering.ops
        (†U)
        hworkspace
        ψ := by
    change
      GateWorkspaceCleanState
        qs
        lowering.k
        lowering.hk
        lowering.ops
        U
        hworkspace
        (qs.eval (†U) ψ)

    exact hforward.1

  constructor
  · exact hadjClean

  · rw [
      lowerGate_correctness
        qs
        lowering.k
        lowering.hk
        lowering.ops
        lowering.consumes
        lowering.returns
        (†U)
        hworkspace
        ψ
        hadjClean
    ]

    exact hpost

private noncomputable def step5Forward
    (k5val N ctrl : ℕ)
    (data work : ExtReg)
    (hmod :
      ModMulCircuitWorkspaceOK data work) :
    Gate :=
  let φ : ℝ :=
    (2 * Real.pi *
      ((k5val % N : ℕ) : ℝ)) /
    (N : ℝ)

  H_reg work.active ;;
  Gate.CPhaseProdUsing
    ctrl
    φ
    (data.grow 1).active
    work.active
    hmod.step5Workspace ;;
  IQFT hmod.step5Workspace.zExt

private theorem step5_eq_adj_step5Forward
    {Basis : Type u}
    [RegEncoding Basis]
    (k5val N ctrl : ℕ)
    (data work : ExtReg)
    (hmod :
      ModMulCircuitWorkspaceOK data work) :
    step5
        (Basis := Basis)
        k5val N ctrl data work hmod
      =
    †(step5Forward
        k5val N ctrl data work hmod) := by
  rfl

private theorem ThreeRegsCleanState.weaken
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    {r₁ r₂ r₃ s₁ s₂ s₃ : Reg}
    {ψ : qs.State}
    (h₁ :
      ∀ q,
        q ∈ s₁.qubits →
        q ∈ r₁.qubits)
    (h₂ :
      ∀ q,
        q ∈ s₂.qubits →
        q ∈ r₂.qubits)
    (h₃ :
      ∀ q,
        q ∈ s₃.qubits →
        q ∈ r₃.qubits)
    (hclean :
      ThreeRegsCleanState
        qs r₁ r₂ r₃ ψ) :
    ThreeRegsCleanState
      qs s₁ s₂ s₃ ψ := by
  induction hclean with
  | zero =>
      exact ThreeRegsCleanState.zero

  | ket b hr₁ hr₂ hr₃ =>
      exact
        ThreeRegsCleanState.ket
          b
          (FreshZero.of_subset
            s₁ r₁ b h₁ hr₁)
          (FreshZero.of_subset
            s₂ r₂ b h₂ hr₂)
          (FreshZero.of_subset
            s₃ r₃ b h₃ hr₃)

  | add hψ hφ ihψ ihφ =>
      exact ThreeRegsCleanState.add ihψ ihφ

  | smul a hψ ihψ =>
      exact ThreeRegsCleanState.smul a ihψ


private theorem
    threeRegsCleanState_to_grownRecursiveWorkspaceCleanState_of_subset
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    {r₁ r₂ r₃ : Reg}
    {x z : Reg}
    (ws : Gate.PhaseProdWorkspace x z)
    (hxReserve :
      ∀ q,
        q ∈ ws.xExt.reserve.qubits →
        q ∈ r₂.qubits)
    (hzReserve :
      ∀ q,
        q ∈ ws.zExt.reserve.qubits →
        q ∈ r₃.qubits)
    {ψ : qs.State}
    (hclean :
      ThreeRegsCleanState
        qs r₁ r₂ r₃ ψ) :
    RecursiveWorkspaceCleanState
      qs
      (ws.xExt.grow 1)
      (ws.zExt.grow 1)
      ψ := by
  induction hclean with
  | zero =>
      exact CleanClosure.zero

  | ket b h₁ h₂ h₃ =>
      have hxZero :
          FreshZero ws.xExt.reserve b :=
        FreshZero.of_subset
          ws.xExt.reserve
          r₂
          b
          hxReserve
          h₂

      have hzZero :
          FreshZero ws.zExt.reserve b :=
        FreshZero.of_subset
          ws.zExt.reserve
          r₃
          b
          hzReserve
          h₃

      exact
        CleanClosure.ket
          b
          ⟨
            freshFor_grow_capacity_of_freshZero_reserve
              ws.xExt 1 b hxZero,
            freshFor_grow_capacity_of_freshZero_reserve
              ws.zExt 1 b hzZero
          ⟩

  | add hψ hφ ihψ ihφ =>
      exact CleanClosure.add ihψ ihφ

  | smul a hψ ihψ =>
      exact CleanClosure.smul a ihψ


private theorem
    gateWorkspaceCleanState_CPhaseProdUsing_of_threeRegsClean_of_subset
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGateGateBridge qs]
    {lowering : ShorLoweringSetup}
    {r₁ r₂ r₃ : Reg}
    {x z : Reg}
    (ctrl : ℕ)
    (φ : ℝ)
    (ws : Gate.PhaseProdWorkspace x z)
    (hxReserve :
      ∀ q,
        q ∈ ws.xExt.reserve.qubits →
        q ∈ r₂.qubits)
    (hzReserve :
      ∀ q,
        q ∈ ws.zExt.reserve.qubits →
        q ∈ r₃.qubits)
    (hworkspace :
      GateWorkspaceOK
        lowering.ops
        (Gate.CPhaseProdUsing
          ctrl φ x z ws))
    (ψ : qs.State)
    (hclean :
      ThreeRegsCleanState
        qs r₁ r₂ r₃ ψ) :
    GateWorkspaceCleanState
      qs
      lowering.k
      lowering.hk
      lowering.ops
      (Gate.CPhaseProdUsing
        ctrl φ x z ws)
      hworkspace
      ψ := by
  have hrecursive :
      RecursiveWorkspaceCleanState
        qs
        (ws.xExt.grow 1)
        (ws.zExt.grow 1)
        ψ :=
    threeRegsCleanState_to_grownRecursiveWorkspaceCleanState_of_subset
      ws
      hxReserve
      hzReserve
      hclean

  simpa [
    Gate.CPhaseProdUsing,
    GateWorkspaceCleanState,
    lowerGate,
    LowerGateClass.evalL_zeroExtend,
    ExtensionSemantics.eval_zeroExtend
  ] using hrecursive


private theorem
    eval_CPhaseProdUsing_preserves_threeRegsCleanState_of_subset
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    {r₁ r₂ r₃ : Reg}
    (ctrl : ℕ)
    (φ : ℝ)
    {x z : Reg}
    (ws : Gate.PhaseProdWorkspace x z)
    (hxReserve :
      ∀ q,
        q ∈ ws.xExt.reserve.qubits →
        q ∈ r₂.qubits)
    (hzReserve :
      ∀ q,
        q ∈ ws.zExt.reserve.qubits →
        q ∈ r₃.qubits)
    {ψ : qs.State}
    (hclean :
      ThreeRegsCleanState
        qs r₁ r₂ r₃ ψ) :
    ThreeRegsCleanState
      qs r₁ r₂ r₃
      (qs.eval
        (Gate.CPhaseProdUsing
          ctrl φ x z ws)
        ψ) := by
  induction hclean with
  | zero =>
      rw [qs.eval_zero]
      exact ThreeRegsCleanState.zero

  | ket b h₁ h₂ h₃ =>
      have hxZero :
          FreshZero ws.xExt.reserve b :=
        FreshZero.of_subset
          ws.xExt.reserve
          r₂
          b
          hxReserve
          h₂

      have hzZero :
          FreshZero ws.zExt.reserve b :=
        FreshZero.of_subset
          ws.zExt.reserve
          r₃
          b
          hzReserve
          h₃

      have hwsClean :
          ws.Clean b := by
        constructor
        · exact
            freshFor_of_freshZero_reserve
              ws.xExt 1 b hxZero

        · exact
            freshFor_of_freshZero_reserve
              ws.zExt 1 b hzZero

      rw [
        GateSemanticsFacts.eval_CPhaseProdUsing_ket
          qs ctrl φ x z ws b hwsClean
      ]

      exact
        ThreeRegsCleanState.smul
          _
          (ThreeRegsCleanState.ket
            b h₁ h₂ h₃)

  | add hψ hφ ihψ ihφ =>
      rw [qs.eval_add]
      exact ThreeRegsCleanState.add ihψ ihφ

  | smul a hψ ihψ =>
      rw [qs.eval_smul]
      exact ThreeRegsCleanState.smul a ihψ

private theorem lowered_step5Forward_ready_and_full_clean
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGateGateBridge qs]
    (lowering : ShorLoweringSetup)
    (x data work : ExtReg)
    (k5val N ctrl : ℕ)
    (_hxData :
      ExtReg.OwnedDisjoint x data)
    (hxWork :
      ExtReg.OwnedDisjoint x work)
    (hmod :
      ModMulCircuitWorkspaceOK data work)
    (hworkspace :
      GateWorkspaceOK
        lowering.ops
        (step5Forward
          k5val N ctrl data work hmod))
    (ψ : qs.State)
    (hclean :
      ShorLoweringCleanState
        qs x data work ψ) :
    LoweredCleanResult
      qs
      lowering
      (ShorLoweringCleanState
        qs x data work)
      (step5Forward
        k5val N ctrl data work hmod)
      hworkspace
      ψ := by
  let φ : ℝ :=
    (2 * Real.pi *
      ((k5val % N : ℕ) : ℝ)) /
    (N : ℝ)

  let U1 : Gate :=
    H_reg work.active

  let U2 : Gate :=
    Gate.CPhaseProdUsing
      ctrl
      φ
      (data.grow 1).active
      work.active
      hmod.step5Workspace

  let U3 : Gate :=
    IQFT hmod.step5Workspace.zExt

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

  have hDataGrowReserve :
      ∀ q,
        q ∈ (data.grow 1).reserve.qubits →
        q ∈ data.reserve.qubits := by
    intro q hq
    have hqTail :
        q ∈ data.reserve.qubits.tail := by
      simpa [
        ExtReg.grow,
        ExtReg.remainingReserve,
        Reg.drop
      ] using hq
    exact List.tail_subset data.reserve.qubits hqTail

  have hStep5XReserve :
      ∀ q,
        q ∈ hmod.step5Workspace.xExt.reserve.qubits →
        q ∈ (data.reserve.drop 1).qubits := by
    intro q hq
    simpa [
      ModMulCircuitWorkspaceOK.step5Workspace,
      Gate.PhaseProdWorkspace.ofExtRegs,
      Gate.PhaseProdWorkspace.xExt,
      ExtReg.withReserve
    ] using hq

  have hStep5ZReserve :
      ∀ q,
        q ∈ hmod.step5Workspace.zExt.reserve.qubits →
        q ∈ work.reserve.qubits := by
    intro q hq
    simpa [
      ModMulCircuitWorkspaceOK.step5Workspace,
      Gate.PhaseProdWorkspace.ofExtRegs,
      Gate.PhaseProdWorkspace.zExt,
      ExtReg.withReserve
    ] using hq

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
        (Basis := qs.Basis)
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
      gateWorkspaceCleanState_CPhaseProdUsing_of_threeRegsClean_of_subset
        ctrl
        φ
        hmod.step5Workspace
        hStep5XReserve
        hStep5ZReserve
        hworkspace.2.1
        ψ1
        hψ1

  let ψ2 : qs.State :=
    LowerGateClass.evalL
      (qs := qs)
      (lowerGate
        (Basis := qs.Basis)
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
      eval_CPhaseProdUsing_preserves_threeRegsCleanState_of_subset
        ctrl
        φ
        hmod.step5Workspace
        hStep5XReserve
        hStep5ZReserve
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
      hmod.step5Workspace.zExt.active =
        work.active := by
    rfl

  have hxZExt :
      Disjoint
        x.reserve
        hmod.step5Workspace.zExt.active := by
    simpa only [hzExtActive] using hxWorkActive

  have hdataZExt :
      Disjoint
        (data.reserve.drop 1)
        hmod.step5Workspace.zExt.active := by
    simpa only [hzExtActive] using hdataWorkActive

  have hworkZExt :
      Disjoint
        work.reserve
        hmod.step5Workspace.zExt.active := by
    simpa only [hzExtActive] using hworkWorkActive

  have hHighU3 :
      ShorLoweringCleanState
        qs x data work
        (qs.eval U3 ψ2) := by
    simpa only [U3] using
      eval_IQFT_preserves_threeRegsCleanState
        hmod.step5Workspace.zExt
        x.reserve
        (data.reserve.drop 1)
        work.reserve
        hxZExt
        hdataZExt
        hworkZExt
        hψ2

  have hzReserve :
      hmod.step5Workspace.zExt.reserve =
        work.reserve := by
    rfl

  have hQFTLocal :
      QFTWorkspaceCleanState
        qs
        (qftXWork
          lowering.ops
          hmod.step5Workspace.zExt)
        (qftZWork
          lowering.ops
          hmod.step5Workspace.zExt)
        (qs.eval U3 ψ2) := by
    exact
      threeRegsCleanState_to_QFTWorkspaceCleanState
        lowering.ops
        hmod.step5Workspace.zExt
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

  have hworkspace123 :
      GateWorkspaceOK lowering.ops (U1 ;; U2 ;; U3) := by
    exact hworkspace

  apply
    LoweredCleanResult.seq
      hworkspace123
      ψ
      hU1

  simpa only [ψ1] using hU23


/-! =========================================================
    Semantic decomposition of adjoint circuits
========================================================= -/

private theorem qeval_injective
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (U : Gate) :
    Function.Injective (qs.eval U) := by
  intro ψ φ h

  have h' :=
    congrArg (qs.eval (†U)) h

  simpa only [qs.eval_adj_apply] using h'

private theorem eval_adj_seq_eq
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (U V : Gate)
    (ψ : qs.State) :
    qs.eval (†(U ;; V)) ψ
      =
    qs.eval (†U)
      (qs.eval (†V) ψ) := by
  apply qeval_injective qs (U ;; V)

  calc
    qs.eval
        (U ;; V)
        (qs.eval (†(U ;; V)) ψ)
        =
      ψ := by
        exact qs.eval_apply_adj (U ;; V) ψ

    _ =
      qs.eval
        (U ;; V)
        (qs.eval (†U)
          (qs.eval (†V) ψ)) := by
        rw [
          qs.eval_seq,
          qs.eval_apply_adj,
          qs.eval_apply_adj
        ]

private theorem eval_adj_adj_eq
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (U : Gate)
    (ψ : qs.State) :
    qs.eval (†(†U)) ψ =
      qs.eval U ψ := by
  apply qeval_injective qs (†U)

  calc
    qs.eval
        (†U)
        (qs.eval (†(†U)) ψ)
        =
      ψ := by
        exact qs.eval_apply_adj (†U) ψ

    _ =
      qs.eval
        (†U)
        (qs.eval U ψ) := by
        symm
        exact qs.eval_adj_apply U ψ

/-! =========================================================
    Step-5 QFT locality
========================================================= -/

private theorem eval_step5_QFT_preserves_full_clean
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (x data work : ExtReg)
    (hxWork :
      ExtReg.OwnedDisjoint x work)
    (hmod :
      ModMulCircuitWorkspaceOK data work)
    (ψ : qs.State)
    (hclean :
      ShorLoweringCleanState
        qs x data work ψ) :
    ShorLoweringCleanState
      qs x data work
      (qs.eval
        (Gate.QFT hmod.step5Workspace.zExt)
        ψ) := by
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

  have hzActive :
      hmod.step5Workspace.zExt.active =
        work.active := by
    rfl

  have hxZActive :
      Disjoint
        x.reserve
        hmod.step5Workspace.zExt.active := by
    simpa only [hzActive] using hxWorkActive

  have hdataZActive :
      Disjoint
        (data.reserve.drop 1)
        hmod.step5Workspace.zExt.active := by
    simpa only [hzActive] using hdataWorkActive

  have hworkZActive :
      Disjoint
        work.reserve
        hmod.step5Workspace.zExt.active := by
    simpa only [hzActive] using hworkWorkActive

  induction hclean with
  | zero =>
      rw [qs.eval_zero]
      exact ThreeRegsCleanState.zero

  | ket b hx hdata hwork =>
      classical

      rw [QFTSemantics.eval_QFT_ket]
      apply ThreeRegsCleanState.smul

      let f :
          Fin
              (2 ^
                hmod.step5Workspace.zExt.width) →
            qs.State :=
        fun y =>
          qftPhase
              (2 ^
                hmod.step5Workspace.zExt.width)
              (ExtReg.toNat
                hmod.step5Workspace.zExt
                b)
              y.1
            •
          qs.ket
            (RegEncoding.writeNat
              hmod.step5Workspace.zExt.active
              y.1
              b)

      have hterm :
          ∀ y :
              Fin
                (2 ^
                  hmod.step5Workspace.zExt.width),
            ThreeRegsCleanState
              qs
              x.reserve
              (data.reserve.drop 1)
              work.reserve
              (f y) := by
        intro y

        apply ThreeRegsCleanState.smul
        apply ThreeRegsCleanState.ket

        · unfold FreshZero at hx ⊢
          rw [
            RegEncoding.toNat_left_write_right
              x.reserve
              hmod.step5Workspace.zExt.active
              hxZActive
              b
              y.1
          ]
          exact hx

        · unfold FreshZero at hdata ⊢
          rw [
            RegEncoding.toNat_left_write_right
              (data.reserve.drop 1)
              hmod.step5Workspace.zExt.active
              hdataZActive
              b
              y.1
          ]
          exact hdata

        · unfold FreshZero at hwork ⊢
          rw [
            RegEncoding.toNat_left_write_right
              work.reserve
              hmod.step5Workspace.zExt.active
              hworkZActive
              b
              y.1
          ]
          exact hwork

      have hsum :
          ∀ s :
              Finset
                (Fin
                  (2 ^
                    hmod.step5Workspace.zExt.width)),
            ThreeRegsCleanState
              qs
              x.reserve
              (data.reserve.drop 1)
              work.reserve
              (∑ y ∈ s, f y) := by
        intro s

        induction s using Finset.induction_on with
        | empty =>
            simpa using
              (ThreeRegsCleanState.zero :
                ThreeRegsCleanState
                  qs
                  x.reserve
                  (data.reserve.drop 1)
                  work.reserve
                  0)

        | @insert y s hy ih =>
            rw [Finset.sum_insert hy]
            exact
              ThreeRegsCleanState.add
                (hterm y)
                ih

      simpa [f] using hsum Finset.univ

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


/-! =========================================================
    Step-5 workspace subset facts
========================================================= -/
theorem step5Workspace_xReserve_subset
    {data work : ExtReg}
    (hmod :
      ModMulCircuitWorkspaceOK data work) :
    ∀ q,
      q ∈
          hmod.step5Workspace.xExt.reserve.qubits →
      q ∈ (data.reserve.drop 1).qubits := by
  intro q hq

  change
    q ∈ data.reserve.qubits.drop 1
    at hq

  exact hq

theorem step5Workspace_zReserve_subset
    {data work : ExtReg}
    (hmod :
      ModMulCircuitWorkspaceOK data work) :
    ∀ q,
      q ∈
          hmod.step5Workspace.zExt.reserve.qubits →
      q ∈ work.reserve.qubits := by
  intro q hq

  change q ∈ work.reserve.qubits at hq
  exact hq


/-! =========================================================
    Adjoint controlled phase-product locality
========================================================= -/
theorem
    eval_adj_step5_CPhaseProdUsing_preserves_full_clean
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (x data work : ExtReg)
    (ctrl : ℕ)
    (φ : ℝ)
    (hmod :
      ModMulCircuitWorkspaceOK data work)
    (ψ : qs.State)
    (hclean :
      ShorLoweringCleanState
        qs x data work ψ) :
    ShorLoweringCleanState
      qs x data work
      (qs.eval
        (†(Gate.CPhaseProdUsing
          ctrl
          φ
          (data.grow 1).active
          work.active
          hmod.step5Workspace))
        ψ) := by
  let U : Gate :=
    Gate.CPhaseProdUsing
      ctrl
      φ
      (data.grow 1).active
      work.active
      hmod.step5Workspace

  induction hclean with
  | zero =>
      rw [qs.eval_zero]
      exact ThreeRegsCleanState.zero

  | ket b hx hdata hwork =>
      have hxReserveZero :
          FreshZero
            hmod.step5Workspace.xExt.reserve
            b := by
        exact
          FreshZero.of_subset
            hmod.step5Workspace.xExt.reserve
            (data.reserve.drop 1)
            b
            (step5Workspace_xReserve_subset hmod)
            hdata

      have hzReserveZero :
          FreshZero
            hmod.step5Workspace.zExt.reserve
            b := by
        exact
          FreshZero.of_subset
            hmod.step5Workspace.zExt.reserve
            work.reserve
            b
            (step5Workspace_zReserve_subset hmod)
            hwork

      have hworkspaceClean :
          hmod.step5Workspace.Clean b := by
        constructor
        · exact
            freshFor_of_freshZero_reserve
              hmod.step5Workspace.xExt
              1
              b
              hxReserveZero

        · exact
            freshFor_of_freshZero_reserve
              hmod.step5Workspace.zExt
              1
              b
              hzReserveZero

      let c : ℂ :=
        if RegEncoding.bit ctrl b then
          Complex.exp
            (φ * Complex.I *
              ((RegEncoding.toNat
                  (data.grow 1).active
                  b : ℂ) *
               (RegEncoding.toNat
                  work.active
                  b : ℂ)))
        else
          1

      have hforward :
          qs.eval U (qs.ket b) =
            c • qs.ket b := by
        simpa only [U, c] using
          GateSemanticsFacts.eval_CPhaseProdUsing_ket
            qs
            ctrl
            φ
            (data.grow 1).active
            work.active
            hmod.step5Workspace
            b
            hworkspaceClean

      have hc :
          c ≠ 0 := by
        dsimp only [c]

        split
        · exact Complex.exp_ne_zero _
        · simp

      have hinverse :
          qs.eval (†U)
              (qs.eval U (qs.ket b))
            =
          qs.ket b :=
        qs.eval_adj_apply U (qs.ket b)

      rw [hforward, qs.eval_smul] at hinverse

      have hscaled :=
        congrArg
          (fun ξ : qs.State =>
            c⁻¹ • ξ)
          hinverse

      have hadjoint :
          qs.eval (†U) (qs.ket b)
            =
          c⁻¹ • qs.ket b := by
        simpa [smul_smul, hc] using hscaled

      change
        ThreeRegsCleanState
          qs
          x.reserve
          (data.reserve.drop 1)
          work.reserve
          (qs.eval (†U) (qs.ket b))

      rw [hadjoint]

      exact
        ThreeRegsCleanState.smul
          c⁻¹
          (ThreeRegsCleanState.ket
            b hx hdata hwork)

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

/-! =========================================================
    Elementary Hadamard inverse facts
========================================================= -/
theorem writeNat_writeNat_same
    {Basis : Type u}
    [RegEncoding Basis]
    (r : Reg)
    (v w : ℕ)
    (b : Basis) :
    RegEncoding.writeNat r v
        (RegEncoding.writeNat r w b)
      =
    RegEncoding.writeNat r v b := by
  apply RegEncoding.basis_ext
  intro q

  by_cases hq : q ∈ r.qubits
  · exact
      RegEncoding.bit_writeNat_in
        r
        v
        (RegEncoding.writeNat r w b)
        b
        q
        hq

  · rw [
      RegEncoding.bit_writeNat_out
        r v
        (RegEncoding.writeNat r w b)
        q hq,
      RegEncoding.bit_writeNat_out
        r w b q hq,
      RegEncoding.bit_writeNat_out
        r v b q hq
    ]

private theorem bit_writeNat_qubitReg
    {Basis : Type u}
    [RegEncoding Basis]
    (q v : ℕ)
    (b : Basis)
    (hv : v < 2) :
    RegEncoding.bit q
        (RegEncoding.writeNat
          (qubitReg q)
          v
          b)
      =
    Nat.testBit v 0 := by
  let i : Fin (regSize (qubitReg q)) :=
    ⟨0, by simp⟩

  have hbit :=
    RegEncoding.bit_eq_testBit_toNat
      (qubitReg q)
      (RegEncoding.writeNat
        (qubitReg q)
        v
        b)
      i

  have hget :
      (qubitReg q).get i = q := by
    rfl

  rw [hget] at hbit

  have hv' :
      v < ASize (qubitReg q) := by
    simpa [ASize] using hv

  rw [
    RegEncoding.toNat_writeNat_of_lt
      (qubitReg q)
      v
      b
      hv'
  ] at hbit

  exact hbit

theorem bit_eq_testBit_toNat_qubitReg
    {Basis : Type u}
    [RegEncoding Basis]
    (q : ℕ)
    (b : Basis) :
    RegEncoding.bit q b
      =
    Nat.testBit
      (RegEncoding.toNat (qubitReg q) b)
      0 := by
  let i : Fin (regSize (qubitReg q)) :=
    ⟨0, by simp⟩

  have hbit :=
    RegEncoding.bit_eq_testBit_toNat
      (qubitReg q)
      b
      i

  have hget :
      (qubitReg q).get i = q := by
    rfl

  simpa only [hget] using hbit

lemma hadamard_scale_sq :
    let a : ℂ :=
      (1 / Real.sqrt (2 : ℝ) : ℂ)

    (a * a) * 2 = 1 := by
  dsimp

  have hsqrt_ne_real :
      Real.sqrt (2 : ℝ) ≠ 0 := by
    positivity

  have hsqrt_ne :
      (Real.sqrt (2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hsqrt_ne_real

  field_simp [hsqrt_ne]

  have hsqrt_sq :
      ((Real.sqrt (2 : ℝ) : ℂ) ^ 2) = 2 := by
    exact_mod_cast
      (Real.sq_sqrt
        (by norm_num : (0 : ℝ) ≤ 2))

  simpa [sq] using hsqrt_sq.symm


lemma hadamard_plus_identity
    {M : Type*}
    [AddCommGroup M]
    [Module ℂ M]
    (a : ℂ)
    (ha : (a * a) * 2 = 1)
    (u v : M) :
    a •
        (a • (u + v) +
         a • (u - v))
      =
    u := by
  calc
    a •
        (a • (u + v) +
         a • (u - v))
        =
      ((a * a) * 2) • u := by
        module

    _ = u := by
      rw [ha]
      simp

lemma hadamard_minus_identity
    {M : Type*}
    [AddCommGroup M]
    [Module ℂ M]
    (a : ℂ)
    (ha : (a * a) * 2 = 1)
    (u v : M) :
    a •
        (a • (u + v) -
         a • (u - v))
      =
    v := by
  calc
    a •
        (a • (u + v) -
         a • (u - v))
        =
      ((a * a) * 2) • v := by
        module

    _ = v := by
      rw [ha]
      simp


private theorem eval_H_involutive_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (q : ℕ)
    (b : qs.Basis) :
    qs.eval (Gate.H q)
        (qs.eval (Gate.H q) (qs.ket b))
      =
    qs.ket b := by
  let r : Reg :=
    qubitReg q

  let a : ℂ :=
    (1 / Real.sqrt (2 : ℝ) : ℂ)

  let b0 : qs.Basis :=
    RegEncoding.writeNat r 0 b

  let b1 : qs.Basis :=
    RegEncoding.writeNat r 1 b

  have hnlt :
      RegEncoding.toNat r b < 2 := by
    have h :=
      RegEncoding.toNat_lt_ASize r b

    simpa [r, ASize] using h

  have hn :
      RegEncoding.toNat r b = 0
        ∨
      RegEncoding.toNat r b = 1 := by
    omega

  have hb0 :
      RegEncoding.bit q b0 = false := by
    dsimp only [b0, r]

    simpa using
      bit_writeNat_qubitReg
        q 0 b (by omega)

  have hb1 :
      RegEncoding.bit q b1 = true := by
    dsimp only [b1, r]

    simpa using
      bit_writeNat_qubitReg
        q 1 b (by omega)

  have h00 :
      RegEncoding.writeNat r 0 b0 = b0 := by
    dsimp only [b0]

    exact
      writeNat_writeNat_same
        r 0 0 b

  have h01 :
      RegEncoding.writeNat r 1 b0 = b1 := by
    dsimp only [b0, b1]

    exact
      writeNat_writeNat_same
        r 1 0 b

  have h10 :
      RegEncoding.writeNat r 0 b1 = b0 := by
    dsimp only [b0, b1]

    exact
      writeNat_writeNat_same
        r 0 1 b

  have h11 :
      RegEncoding.writeNat r 1 b1 = b1 := by
    dsimp only [b1]

    exact
      writeNat_writeNat_same
        r 1 1 b

  rw [
    HadamardSemantics.eval_H_ket,
    qs.eval_smul,
    qs.eval_add,
    qs.eval_smul,
    HadamardSemantics.eval_H_ket,
    HadamardSemantics.eval_H_ket
  ]

  change
    a •
      (
        a •
          (
            qs.ket
              (RegEncoding.writeNat r 0 b0)
              +
            (if RegEncoding.bit q b0
             then (-1 : ℂ)
             else 1) •
              qs.ket
                (RegEncoding.writeNat r 1 b0)
          )
          +
        (if RegEncoding.bit q b
         then (-1 : ℂ)
         else 1) •
          (
            a •
              (
                qs.ket
                  (RegEncoding.writeNat r 0 b1)
                  +
                (if RegEncoding.bit q b1
                 then (-1 : ℂ)
                 else 1) •
                  qs.ket
                    (RegEncoding.writeNat r 1 b1)
              )
          )
      )
      =
    qs.ket b

  rw [h00, h01, h10, h11, hb0, hb1]
  simp only [ite_true, neg_one_smul]

  rcases hn with hn | hn
  · have hb :
        RegEncoding.bit q b = false := by
      rw [
        bit_eq_testBit_toNat_qubitReg
          q b,
        hn
      ]
      decide

    have hbEq :
        b0 = b := by
      dsimp only [b0]
      simpa [hn] using
        (RegEncoding.writeNat_toNat r b)

    simpa [
      a,
      hb,
      hbEq,
      sub_eq_add_neg,
      add_assoc,
      add_comm,
      add_left_comm
    ] using
      hadamard_plus_identity
        a
        hadamard_scale_sq
        (qs.ket b0)
        (qs.ket b1)

  · have hb :
        RegEncoding.bit q b = true := by
      rw [
        bit_eq_testBit_toNat_qubitReg
          q b,
        hn
      ]
      decide

    have hbEq :
        b1 = b := by
      dsimp only [b1]
      simpa [hn] using
        (RegEncoding.writeNat_toNat r b)

    simpa [
      a,
      hb,
      hbEq,
      sub_eq_add_neg,
      add_assoc,
      add_comm,
      add_left_comm
    ] using
      hadamard_minus_identity
        a
        hadamard_scale_sq
        (qs.ket b0)
        (qs.ket b1)


private theorem eval_H_involutive
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (q : ℕ)
    (ψ : qs.State) :
    qs.eval (Gate.H q)
        (qs.eval (Gate.H q) ψ)
      =
    ψ := by
  refine
    qs.state_induction
      (P := fun φ =>
        qs.eval (Gate.H q)
            (qs.eval (Gate.H q) φ)
          =
        φ)
      ?_
      ?_
      ?_
      ?_
      ψ

  · change
      qs.eval (Gate.H q)
          (qs.eval (Gate.H q) 0)
        =
      0
    rw [qs.eval_zero, qs.eval_zero]

  · intro ψ₁ ψ₂ hψ₁ hψ₂
    calc
      qs.eval (Gate.H q)
          (qs.eval (Gate.H q) (ψ₁ + ψ₂))
          =
        qs.eval (Gate.H q)
          (qs.eval (Gate.H q) ψ₁ +
           qs.eval (Gate.H q) ψ₂) := by
          rw [qs.eval_add]
      _ =
        qs.eval (Gate.H q)
            (qs.eval (Gate.H q) ψ₁)
          +
        qs.eval (Gate.H q)
            (qs.eval (Gate.H q) ψ₂) := by
          rw [qs.eval_add]
      _ = ψ₁ + ψ₂ := by
          rw [hψ₁, hψ₂]

  · intro a ψ hψ
    calc
      qs.eval (Gate.H q)
          (qs.eval (Gate.H q) (a • ψ))
          =
        qs.eval (Gate.H q)
          (a • qs.eval (Gate.H q) ψ) := by
          rw [qs.eval_smul]
      _ =
        a •
          qs.eval (Gate.H q)
            (qs.eval (Gate.H q) ψ) := by
          rw [qs.eval_smul]
      _ = a • ψ := by
          rw [hψ]

  · intro b
    exact
      eval_H_involutive_ket
        qs q b


private theorem eval_adj_H_eq_eval_H
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (q : ℕ)
    (ψ : qs.State) :
    qs.eval (†(Gate.H q)) ψ
      =
    qs.eval (Gate.H q) ψ := by
  apply qeval_injective qs (Gate.H q)

  rw [
    qs.eval_apply_adj,
    eval_H_involutive
  ]


/-! =========================================================
    Locality of a single adjoint Hadamard
========================================================= -/

private theorem eval_H_preserves_threeRegsCleanState
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (q : ℕ)
    (r₁ r₂ r₃ : Reg)
    {ψ : qs.State}
    (h₁q :
      Disjoint r₁ (qubitReg q))
    (h₂q :
      Disjoint r₂ (qubitReg q))
    (h₃q :
      Disjoint r₃ (qubitReg q))
    (hclean :
      ThreeRegsCleanState
        qs r₁ r₂ r₃ ψ) :
    ThreeRegsCleanState
      qs r₁ r₂ r₃
      (qs.eval (Gate.H q) ψ) := by
  induction hclean with
  | zero =>
      rw [qs.eval_zero]
      exact ThreeRegsCleanState.zero

  | ket b h₁ h₂ h₃ =>
      rw [HadamardSemantics.eval_H_ket]

      apply ThreeRegsCleanState.smul
      apply ThreeRegsCleanState.add

      · apply ThreeRegsCleanState.ket

        · unfold FreshZero at h₁ ⊢
          rw [
            RegEncoding.toNat_left_write_right
              r₁
              (qubitReg q)
              h₁q
              b
              0
          ]
          exact h₁

        · unfold FreshZero at h₂ ⊢
          rw [
            RegEncoding.toNat_left_write_right
              r₂
              (qubitReg q)
              h₂q
              b
              0
          ]
          exact h₂

        · unfold FreshZero at h₃ ⊢
          rw [
            RegEncoding.toNat_left_write_right
              r₃
              (qubitReg q)
              h₃q
              b
              0
          ]
          exact h₃

      · apply ThreeRegsCleanState.smul
        apply ThreeRegsCleanState.ket

        · unfold FreshZero at h₁ ⊢
          rw [
            RegEncoding.toNat_left_write_right
              r₁
              (qubitReg q)
              h₁q
              b
              1
          ]
          exact h₁

        · unfold FreshZero at h₂ ⊢
          rw [
            RegEncoding.toNat_left_write_right
              r₂
              (qubitReg q)
              h₂q
              b
              1
          ]
          exact h₂

        · unfold FreshZero at h₃ ⊢
          rw [
            RegEncoding.toNat_left_write_right
              r₃
              (qubitReg q)
              h₃q
              b
              1
          ]
          exact h₃

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


private theorem eval_adj_H_preserves_threeRegsCleanState
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (q : ℕ)
    (r₁ r₂ r₃ : Reg)
    {ψ : qs.State}
    (h₁q :
      Disjoint r₁ (qubitReg q))
    (h₂q :
      Disjoint r₂ (qubitReg q))
    (h₃q :
      Disjoint r₃ (qubitReg q))
    (hclean :
      ThreeRegsCleanState
        qs r₁ r₂ r₃ ψ) :
    ThreeRegsCleanState
      qs r₁ r₂ r₃
      (qs.eval (†(Gate.H q)) ψ) := by
  rw [eval_adj_H_eq_eval_H]

  exact
    eval_H_preserves_threeRegsCleanState
      q
      r₁
      r₂
      r₃
      h₁q
      h₂q
      h₃q
      hclean

/-! =========================================================
    Adjoint register-Hadamard locality
========================================================= -/

private theorem
    eval_adj_hadamardFold_preserves_threeRegsCleanState
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (qubits : List ℕ)
    (acc : Gate)
    (r₁ r₂ r₃ : Reg)
    (hqubits :
      ∀ q,
        q ∈ qubits →
        Disjoint r₁ (qubitReg q)
          ∧
        Disjoint r₂ (qubitReg q)
          ∧
        Disjoint r₃ (qubitReg q))
    (hacc :
      ∀ φ : qs.State,
        ThreeRegsCleanState
            qs r₁ r₂ r₃ φ →
        ThreeRegsCleanState
          qs r₁ r₂ r₃
          (qs.eval (†acc) φ))
    (ψ : qs.State)
    (hclean :
      ThreeRegsCleanState
        qs r₁ r₂ r₃ ψ) :
    ThreeRegsCleanState
      qs r₁ r₂ r₃
      (qs.eval
        (†(qubits.foldl
          (fun acc q =>
            (Gate.H q) ;; acc)
          acc))
        ψ) := by
  induction qubits generalizing acc ψ with
  | nil =>
      simpa using hacc ψ hclean

  | cons q qubits ih =>
      simp only [List.foldl]

      apply ih
      · intro p hp
        exact hqubits p (by simp [hp])

      · intro φ hφ

        rw [eval_adj_seq_eq]

        have hAfterAcc :
            ThreeRegsCleanState
              qs r₁ r₂ r₃
              (qs.eval (†acc) φ) :=
          hacc φ hφ

        have hq :=
          hqubits q (by simp)

        exact
          eval_adj_H_preserves_threeRegsCleanState
            q
            r₁
            r₂
            r₃
            hq.1
            hq.2.1
            hq.2.2
            hAfterAcc

      · exact hclean


private theorem eval_adj_H_reg_work_preserves_full_clean
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (x data work : ExtReg)
    (hxWork :
      ExtReg.OwnedDisjoint x work)
    (hmod :
      ModMulCircuitWorkspaceOK data work)
    (ψ : qs.State)
    (hclean :
      ShorLoweringCleanState
        qs x data work ψ) :
    ShorLoweringCleanState
      qs x data work
      (qs.eval
        (†(H_reg work.active))
        ψ) := by
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

  have hqubits :
      ∀ q,
        q ∈ regQubits work.active →
        Disjoint x.reserve (qubitReg q)
          ∧
        Disjoint (data.reserve.drop 1) (qubitReg q)
          ∧
        Disjoint work.reserve (qubitReg q) := by
    intro q hq

    have hqActive :
        q ∈ work.active.qubits := by
      simpa [regQubits] using hq

    exact
      ⟨
        disjoint_qubitReg_of_mem_right
          hxWorkActive
          hqActive,
        disjoint_qubitReg_of_mem_right
          hdataWorkActive
          hqActive,
        disjoint_qubitReg_of_mem_right
          hworkWorkActive
          hqActive
      ⟩

  have hid :
      ∀ φ : qs.State,
        ThreeRegsCleanState
            qs
            x.reserve
            (data.reserve.drop 1)
            work.reserve
            φ →
        ThreeRegsCleanState
          qs
          x.reserve
          (data.reserve.drop 1)
          work.reserve
          (qs.eval (†Gate.id) φ) := by
    intro φ hφ

    have heval :
        qs.eval (†Gate.id) φ = φ := by
      have h :=
        qs.eval_apply_adj Gate.id φ

      simpa only [qs.eval_id] using h

    rw [heval]
    exact hφ

  unfold H_reg

  exact
    eval_adj_hadamardFold_preserves_threeRegsCleanState
      (qs := qs)
      (regQubits work.active)
      Gate.id
      x.reserve
      (data.reserve.drop 1)
      work.reserve
      hqubits
      hid
      ψ
      hclean



/-! =========================================================
    Semantic decomposition of the Step-5 adjoint
========================================================= -/

private theorem eval_adj_step5Forward_eq
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (k5val N ctrl : ℕ)
    (data work : ExtReg)
    (hmod :
      ModMulCircuitWorkspaceOK data work)
    (ψ : qs.State) :
    qs.eval
        (†(step5Forward
          k5val N ctrl data work hmod))
        ψ
      =
    qs.eval
      (†(H_reg work.active))
      (qs.eval
        (†(Gate.CPhaseProdUsing
          ctrl
          ((2 * Real.pi *
              ((k5val % N : ℕ) : ℝ)) /
            (N : ℝ))
          (data.grow 1).active
          work.active
          hmod.step5Workspace))
        (qs.eval
          (Gate.QFT
            hmod.step5Workspace.zExt)
          ψ)) := by
  unfold step5Forward
  dsimp

  rw [
    eval_adj_seq_eq,
    eval_adj_seq_eq
  ]

  simp only [IQFT]

  rw [eval_adj_adj_eq]


/-! =========================================================
    Main Step-5 adjoint preservation theorem
========================================================= -/

/--
Main semantic preservation theorem for the Step-5 adjoint block.

The high-level adjoint Step-5 circuit is decomposed into QFT, adjoint
controlled phase product, and adjoint Hadamards. Each component preserves
`ShorLoweringCleanState`, so the whole adjoint does as well.
-/
theorem eval_adj_step5Forward_preserves_full_clean
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (x data work : ExtReg)
    (k5val N ctrl : ℕ)
    (hxWork :
      ExtReg.OwnedDisjoint x work)
    (hmod :
      ModMulCircuitWorkspaceOK data work)
    (ψ : qs.State)
    (hclean :
      ShorLoweringCleanState
        qs x data work ψ) :
    ShorLoweringCleanState
      qs x data work
      (qs.eval
        (†(step5Forward
          k5val N ctrl data work hmod))
        ψ) := by
  let φ : ℝ :=
    (2 * Real.pi *
      ((k5val % N : ℕ) : ℝ)) /
    (N : ℝ)

  let ψQFT : qs.State :=
    qs.eval
      (Gate.QFT
        hmod.step5Workspace.zExt)
      ψ

  have hQFT :
      ShorLoweringCleanState
        qs x data work ψQFT := by
    dsimp only [ψQFT]

    exact
      eval_step5_QFT_preserves_full_clean
        qs
        x
        data
        work
        hxWork
        hmod
        ψ
        hclean

  let ψPhase : qs.State :=
    qs.eval
      (†(Gate.CPhaseProdUsing
        ctrl
        φ
        (data.grow 1).active
        work.active
        hmod.step5Workspace))
      ψQFT

  have hPhase :
      ShorLoweringCleanState
        qs x data work ψPhase := by
    dsimp only [ψPhase]

    exact
      eval_adj_step5_CPhaseProdUsing_preserves_full_clean
        qs
        x
        data
        work
        ctrl
        φ
        hmod
        ψQFT
        hQFT

  have hHadamard :
      ShorLoweringCleanState
        qs x data work
        (qs.eval
          (†(H_reg work.active))
          ψPhase) := by
    exact
      eval_adj_H_reg_work_preserves_full_clean
        qs
        x
        data
        work
        hxWork
        hmod
        ψPhase
        hPhase

  rw [
    eval_adj_step5Forward_eq
      qs
      k5val
      N
      ctrl
      data
      work
      hmod
      ψ
  ]

  simpa only [φ, ψQFT, ψPhase] using hHadamard

/--
Main lowered-readiness theorem for Step 5.

It packages Step 5's adjoint semantic preservation with the local lowering
workspace obligations, producing a `LoweredCleanResult` for the public
`step5` gate.
-/
theorem lowered_step5_ready_and_full_clean
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGateGateBridge qs]
    (lowering : ShorLoweringSetup)
    (x data work : ExtReg)
    (k5val N ctrl : ℕ)
    (hxData :
      ExtReg.OwnedDisjoint x data)
    (hxWork :
      ExtReg.OwnedDisjoint x work)
    (hmod :
      ModMulCircuitWorkspaceOK data work)
    (hworkspace :
      GateWorkspaceOK
        lowering.ops
        (step5
          (Basis := qs.Basis)
          k5val N ctrl data work hmod))
    (ψ : qs.State)
    (hclean :
      ShorLoweringCleanState
        qs x data work ψ) :
    LoweredCleanResult
      qs
      lowering
      (ShorLoweringCleanState
        qs x data work)
      (step5
        (Basis := qs.Basis)
        k5val N ctrl data work hmod)
      hworkspace
      ψ := by
  let U : Gate :=
    step5Forward
      k5val N ctrl data work hmod

  have hstep5 :
      step5
          (Basis := qs.Basis)
          k5val N ctrl data work hmod
        =
      †U := by
    rfl

  change
    LoweredCleanResult
      qs
      lowering
      (ShorLoweringCleanState
        qs x data work)
      (†U)
      hworkspace
      ψ

  have hpost :
      ShorLoweringCleanState
        qs x data work
        (qs.eval (†U) ψ) := by
    simpa only [U] using
      eval_adj_step5Forward_preserves_full_clean
        qs
        x
        data
        work
        k5val
        N
        ctrl
        hxWork
        hmod
        ψ
        hclean

  have hforward :
      LoweredCleanResult
        qs
        lowering
        (ShorLoweringCleanState
          qs x data work)
        U
        hworkspace
        (qs.eval (†U) ψ) := by
    simpa only [U] using
      lowered_step5Forward_ready_and_full_clean
        qs
        lowering
        x
        data
        work
        k5val
        N
        ctrl
        hxData
        hxWork
        hmod
        hworkspace
        (qs.eval (†U) ψ)
        hpost

  exact
    LoweredCleanResult.adj
      hpost
      hforward

private theorem
    threeRegsCleanState_to_QFTWorkspaceCleanState_first
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    {k : ℕ}
    (ops : Prog k)
    (r : ExtReg)
    {r₁ r₂ r₃ : Reg}
    (hreserve :
      r.reserve = r₁)
    {ψ : qs.State}
    (hclean :
      ThreeRegsCleanState
        qs r₁ r₂ r₃ ψ) :
    QFTWorkspaceCleanState
      qs
      (qftXWork ops r)
      (qftZWork ops r)
      ψ := by
  induction hclean with
  | zero =>
      exact QFTWorkspaceCleanState.zero

  | ket b h₁ h₂ h₃ =>
      apply QFTWorkspaceCleanState.ket b

      · exact
          FreshZero.of_subset
            (qftXWork ops r)
            r₁
            b
            (fun q hq => by
              simpa only [hreserve] using
                qftXWork_mem_reserve
                  ops r hq)
            h₁

      · exact
          FreshZero.of_subset
            (qftZWork ops r)
            r₁
            b
            (fun q hq => by
              simpa only [hreserve] using
                qftZWork_mem_reserve
                  ops r hq)
            h₁

  | add hψ hφ ihψ ihφ =>
      exact
        QFTWorkspaceCleanState.add
          ihψ
          ihφ

  | smul a hψ ihψ =>
      exact
        QFTWorkspaceCleanState.smul
          a
          ihψ

/-! =========================================================
    Section 9: Final inverse QFT readiness
========================================================= -/

private theorem lowered_IQFT_ready_and_full_clean
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGateGateBridge qs]
    (lowering : ShorLoweringSetup)
    (x data work : ExtReg)
    (hxData :
      ExtReg.OwnedDisjoint x data)
    (hxWork :
      ExtReg.OwnedDisjoint x work)
    (hworkspace :
      GateWorkspaceOK
        lowering.ops
        (IQFT x))
    (ψ : qs.State)
    (hclean :
      ShorLoweringCleanState
        qs x data work ψ) :
    LoweredCleanResult
      qs
      lowering
      (ShorLoweringCleanState
        qs x data work)
      (IQFT x)
      hworkspace
      ψ := by
  have hxReserveActive :
      Disjoint x.reserve x.active :=
    Disjoint.symm
      x.active_reserve_disjoint

  have hdataReserveActive :
      Disjoint (data.reserve.drop 1) x.active :=
    reserve_drop_active_disjoint_of_ownedDisjoint
      (ownedDisjoint_symm hxData)
      1

  have hworkReserveActive :
      Disjoint work.reserve x.active :=
    reserve_active_disjoint_of_ownedDisjoint
      (ownedDisjoint_symm hxWork)

  /-
  The high-level inverse QFT changes only `x.active`, so all three
  reserve registers remain zero.
  -/
  have hHighClean :
      ShorLoweringCleanState
        qs x data work
        (qs.eval (IQFT x) ψ) := by
    exact
      eval_IQFT_preserves_threeRegsCleanState
        x
        x.reserve
        (data.reserve.drop 1)
        work.reserve
        hxReserveActive
        hdataReserveActive
        hworkReserveActive
        hclean

  /-
  `GateWorkspaceCleanState` for an adjoint QFT asks for the QFT
  workspace to be clean after applying the inverse QFT.
  -/
  have hQFTWorkspaceClean :
      QFTWorkspaceCleanState
        qs
        (qftXWork lowering.ops x)
        (qftZWork lowering.ops x)
        (qs.eval (IQFT x) ψ) := by
    exact
      threeRegsCleanState_to_QFTWorkspaceCleanState_first
        lowering.ops
        x
        rfl
        hHighClean

  have hgateClean :
      GateWorkspaceCleanState
        qs
        lowering.k
        lowering.hk
        lowering.ops
        (IQFT x)
        hworkspace
        ψ := by
    simpa [
      IQFT,
      GateWorkspaceCleanState
    ] using hQFTWorkspaceClean

  constructor

  · exact hgateClean

  · rw [
      lowerGate_correctness
        qs
        lowering.k
        lowering.hk
        lowering.ops
        lowering.consumes
        lowering.returns
        (IQFT x)
        hworkspace
        ψ
        hgateClean
    ]

    exact hHighClean

/-! =========================================================
    Section 10: One modular-multiplication core
========================================================= -/

/--
Main theorem for one controlled modular-multiplication core.

It sequences Steps 1 through 5, threading `ShorLoweringCleanState` through the
lowered implementation and discharging each stage's local workspace-clean
obligation.
-/
theorem lowered_CmodMulInPlaceCore_ready_and_clean
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGateGateBridge qs]
    [ModMulPrimitiveGateSemantics qs]
    (lowering : ShorLoweringSetup)
    (x data work : ExtReg)
    (c N ctrl flag : ℕ)
    (hxData :
      ExtReg.OwnedDisjoint x data)
    (hxWork :
      ExtReg.OwnedDisjoint x work)
    (hmod :
      ModMulCircuitWorkspaceOK data work)
    (hflagX :
      flag ∉ x.ownedQubits)
    (hlayout :
      ModMulCoreLayout data work flag ctrl)
    (hworkspace :
      GateWorkspaceOK
        lowering.ops
        (CmodMulInPlaceCore
          (Basis := qs.Basis)
          c N ctrl data work flag hmod))
    (ψ : qs.State)
    (hclean :
      ShorLoweringCleanState
        qs x data work ψ) :
    LoweredCleanResult
      qs
      lowering
      (ShorLoweringCleanState
        qs x data work)
      (CmodMulInPlaceCore
        (Basis := qs.Basis)
        c N ctrl data work flag hmod)
      hworkspace
      ψ := by
  let U1 :=
    step1
      (Basis := qs.Basis)
      c N ctrl data work hmod

  let U2 :=
    step2
      (Basis := qs.Basis)
      N data work hmod

  let U3 :=
    step3 N (data.grow 1).active flag

  let U4 :=
    step4
      N
      (data.grow 1).active
      work.active
      flag

  let U5 :=
    step5
      (Basis := qs.Basis)
      (step5Constant c N)
      N ctrl data work hmod

  change
    GateWorkspaceOK lowering.ops U1
      ∧
    GateWorkspaceOK lowering.ops U2
      ∧
    GateWorkspaceOK lowering.ops U3
      ∧
    GateWorkspaceOK lowering.ops U4
      ∧
    GateWorkspaceOK lowering.ops U5
    at hworkspace

  have hworkspace45 :
      GateWorkspaceOK lowering.ops (U4 ;; U5) := by
    exact hworkspace.2.2.2

  have hworkspace345 :
      GateWorkspaceOK lowering.ops (U3 ;; U4 ;; U5) := by
    exact hworkspace.2.2

  have hworkspace2345 :
      GateWorkspaceOK lowering.ops (U2 ;; U3 ;; U4 ;; U5) := by
    exact hworkspace.2

  have hworkspace12345 :
      GateWorkspaceOK lowering.ops (U1 ;; U2 ;; U3 ;; U4 ;; U5) := by
    exact hworkspace

  let ψ1 :=
    LowerGateClass.evalL
      (qs := qs)
      (lowerGate
        (Basis := qs.Basis)
        lowering.k lowering.hk lowering.ops
        U1 hworkspace.1)
      ψ

  have h1 :
      LoweredCleanResult
        qs lowering
        (ShorLoweringCleanState
          qs x data work)
        U1 hworkspace.1 ψ :=
    lowered_step1_ready_and_full_clean
      qs lowering x data work
      c N ctrl
      hxWork
      hmod
      hworkspace.1 ψ hclean

  let ψ2 :=
    LowerGateClass.evalL
      (qs := qs)
      (lowerGate
        (Basis := qs.Basis)
        lowering.k lowering.hk lowering.ops
        U2 hworkspace.2.1)
      ψ1

  have h2 :
      LoweredCleanResult
        qs lowering
        (ShorLoweringCleanState
          qs x data work)
        U2 hworkspace.2.1 ψ1 :=
    lowered_step2_ready_and_carry_clean
      qs lowering x data work
      N
      hxData
      hmod
      hworkspace.2.1
      ψ1
      h1.2

  let ψ3 :=
    LowerGateClass.evalL
      (qs := qs)
      (lowerGate
        (Basis := qs.Basis)
        lowering.k lowering.hk lowering.ops
        U3 hworkspace.2.2.1)
      ψ2

  have h3 :
      LoweredCleanResult
        qs lowering
        (ShorLoweringCleanState
          qs x data work)
        U3 hworkspace.2.2.1 ψ2 :=
    lowered_step3_ready_and_clean
      lowering x data work N flag
      hxData
      hxWork
      hmod
      hflagX
      hlayout.2.1
      hlayout.2.2.1
      hworkspace.2.2.1
      ψ2
      h2.2

  let ψ4 :=
    LowerGateClass.evalL
      (qs := qs)
      (lowerGate
        (Basis := qs.Basis)
        lowering.k lowering.hk lowering.ops
        U4 hworkspace.2.2.2.1)
      ψ3

  have h4 :
      LoweredCleanResult
        qs lowering
        (ShorLoweringCleanState
          qs x data work)
        U4 hworkspace.2.2.2.1 ψ3 :=
    lowered_step4_ready_and_clean
      lowering
      x data work
      N flag
      hxData
      hxWork
      hmod
      hflagX
      hlayout.2.1
      hlayout.2.2.1
      hworkspace.2.2.2.1
      ψ3
      h3.2

  have h5 :
      LoweredCleanResult
        qs lowering
        (ShorLoweringCleanState
          qs x data work)
        U5 hworkspace.2.2.2.2 ψ4 :=
    lowered_step5_ready_and_full_clean
      qs lowering x data work
      (step5Constant c N)
      N ctrl
      hxData
      hxWork
      hmod
      hworkspace.2.2.2.2
      ψ4
      h4.2

  have h45 :
      LoweredCleanResult
        qs lowering
        (ShorLoweringCleanState
          qs x data work)
        (U4 ;; U5)
        hworkspace45
        ψ3 :=
    LoweredCleanResult.seq
      hworkspace45
      ψ3
      h4
      h5

  have h345 :
      LoweredCleanResult
        qs lowering
        (ShorLoweringCleanState
          qs x data work)
        (U3 ;; U4 ;; U5)
        hworkspace345
        ψ2 :=
    LoweredCleanResult.seq
      hworkspace345
      ψ2
      h3
      h45

  have h2345 :
      LoweredCleanResult
        qs lowering
        (ShorLoweringCleanState
          qs x data work)
        (U2 ;; U3 ;; U4 ;; U5)
        hworkspace2345
        ψ1 :=
    LoweredCleanResult.seq
      hworkspace2345
      ψ1
      h2
      h345

  have h12345 :
      LoweredCleanResult
        qs lowering
        (ShorLoweringCleanState
          qs x data work)
        (U1 ;; U2 ;; U3 ;; U4 ;; U5)
        hworkspace12345
        ψ :=
    LoweredCleanResult.seq
      hworkspace12345
      ψ
      h1
      h2345

  simpa [
    U1,
    U2,
    U3,
    U4,
    U5,
    CmodMulInPlaceCore
  ] using h12345

/-! =========================================================
    Section 11: Modular exponentiation loop
========================================================= -/

/--
Main theorem for the modular-exponentiation loop.

The theorem folds `lowered_CmodMulInPlaceCore_ready_and_clean` over the list of
control qubits, preserving the lowered Shor workspace invariant after every
controlled modular multiplication.
-/
theorem lowered_modExpApproxStepsValid_ready_and_clean
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGateGateBridge qs]
    [ModMulPrimitiveGateSemantics qs]
    (lowering : ShorLoweringSetup)
    (x data work : ExtReg)
    (a N flag e : ℕ)
    (ctrls : List ℕ)
    (hmod :
      ModMulCircuitWorkspaceOK data work)
    (hxData :
      ExtReg.OwnedDisjoint x data)
    (hxWork :
      ExtReg.OwnedDisjoint x work)
    (hflagX :
      flag ∉ x.ownedQubits)
    (hLayout :
      ∀ ctrl ∈ ctrls,
        ModMulCoreLayout data work flag ctrl)
    (hworkspace :
      GateWorkspaceOK
        lowering.ops
        (modExpApproxStepsValid
          (Basis := qs.Basis)
          a N data work flag hmod e ctrls))
    (ψ : qs.State)
    (hclean :
      ShorLoweringCleanState
        qs x data work ψ) :
    LoweredCleanResult
      qs
      lowering
      (ShorLoweringCleanState
        qs x data work)
      (modExpApproxStepsValid
        (Basis := qs.Basis)
        a N data work flag hmod e ctrls)
      hworkspace
      ψ := by
  induction ctrls generalizing e ψ with
  | nil =>
      constructor
      · simp [
          modExpApproxStepsValid,
          GateWorkspaceCleanState
        ]
      · simpa [
          LoweredCleanResult,
          modExpApproxStepsValid,
          LowerGateClass.evalL_id
        ] using hclean

  | cons ctrl ctrls ih =>
      let c := (a ^ (2 ^ e)) % N

      let U :=
        CmodMulInPlaceCore
          (Basis := qs.Basis)
          c N ctrl data work flag hmod

      let V :=
        modExpApproxStepsValid
          (Basis := qs.Basis)
          a N data work flag hmod
          (e + 1) ctrls

      change
        GateWorkspaceOK lowering.ops U
          ∧
        GateWorkspaceOK lowering.ops V
        at hworkspace

      have hHeadLayout :
          ModMulCoreLayout
            data work flag ctrl :=
        hLayout ctrl (by simp)

      have hTailLayout :
          ∀ q ∈ ctrls,
            ModMulCoreLayout
              data work flag q := by
        intro q hq
        exact hLayout q (by simp [hq])

      have hU :
          LoweredCleanResult
            qs lowering
            (ShorLoweringCleanState
              qs x data work)
            U hworkspace.1 ψ :=
        lowered_CmodMulInPlaceCore_ready_and_clean
          lowering
          x data work
          c N ctrl flag
          hxData
          hxWork
          hmod
          hflagX
          hHeadLayout
          hworkspace.1
          ψ
          hclean

      let ψ' :=
        LowerGateClass.evalL
          (qs := qs)
          (lowerGate
            (Basis := qs.Basis)
            lowering.k
            lowering.hk
            lowering.ops
            U
            hworkspace.1)
          ψ

      have hV :
          LoweredCleanResult
            qs lowering
            (ShorLoweringCleanState
              qs x data work)
            V hworkspace.2 ψ' :=
        ih
          (e := e + 1)
          (ψ := ψ')
          hTailLayout
          hworkspace.2
          hU.2

      have hseq :=
        LoweredCleanResult.seq
          hworkspace
          ψ
          hU
          hV

      simpa [
        U,
        V,
        c,
        modExpApproxStepsValid
      ] using hseq

/-! =========================================================
    Section 12: Full order-finding dynamic readiness
========================================================= -/

/--
Main dynamic theorem for approximate order finding.

It composes exponent Hadamards, data initialization, modular exponentiation,
and the final inverse QFT, proving the complete lowered circuit starts each
recursive sub-lowering with clean workspace and preserves
`ShorLoweringCleanState`.
-/
theorem lowered_orderFindingApprox_ready_and_full_clean
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGateGateBridge qs]
    [ModMulPrimitiveGateSemantics qs]
    (lowering : ShorLoweringSetup)
    (η : ℝ)
    (a N : ℕ)
    (x data work : ExtReg)
    (flag : ℕ)
    (b0 : qs.Basis)
    (hsetup :
      ShorApproxSetup
        qs η x data work flag b0)
    (_hlarge :
      ShorWorkspaceLargeEnough
        lowering.ops x data work)
    (hisolated :
      ShorWorkspaceIsolation x work flag)
    (hworkspace :
      GateWorkspaceOK
        lowering.ops
        (orderFindingApprox
          qs a N x data work flag
          hsetup.circuit_workspace))
    {ψ : qs.State}
    (hclean :
      ShorLoweringCleanState
        qs x data work ψ)
    (hLayout :
      ∀ ctrl ∈ x.active.qubits,
        ModMulCoreLayout data work flag ctrl) :
    LoweredCleanResult
      qs
      lowering
      (ShorLoweringCleanState
        qs x data work)
      (orderFindingApprox
        qs a N x data work flag
        hsetup.circuit_workspace)
      hworkspace
      ψ := by
  let U1 := H_reg x.active

  let U2 := initY1 data.active

  let U3 :=
    modExpApproxValid
      (Basis := qs.Basis)
      a N x.active data work flag
      hsetup.circuit_workspace

  let U4 := IQFT x

  change
    GateWorkspaceOK lowering.ops U1
      ∧
    GateWorkspaceOK lowering.ops U2
      ∧
    GateWorkspaceOK lowering.ops U3
      ∧
    GateWorkspaceOK lowering.ops U4
    at hworkspace

  have hworkspace34 :
      GateWorkspaceOK lowering.ops (U3 ;; U4) := by
    exact hworkspace.2.2

  have hworkspace234 :
      GateWorkspaceOK lowering.ops (U2 ;; U3 ;; U4) := by
    exact hworkspace.2

  have hworkspace1234 :
      GateWorkspaceOK lowering.ops (U1 ;; U2 ;; U3 ;; U4) := by
    exact hworkspace

  let ψ1 :=
    LowerGateClass.evalL
      (qs := qs)
      (lowerGate
        (Basis := qs.Basis)
        lowering.k lowering.hk lowering.ops
        U1 hworkspace.1)
      ψ

  have h1 :
      LoweredCleanResult
        qs lowering
        (ShorLoweringCleanState
          qs x data work)
        U1 hworkspace.1 ψ :=
    lowered_H_reg_ready_and_full_clean
      qs lowering x data work
      hsetup.exponent_data_disjoint
      hisolated.exponent_work_disjoint
      hworkspace.1
      ψ
      hclean

  let ψ2 :=
    LowerGateClass.evalL
      (qs := qs)
      (lowerGate
        (Basis := qs.Basis)
        lowering.k lowering.hk lowering.ops
        U2 hworkspace.2.1)
      ψ1

  have h2 :
      LoweredCleanResult
        qs lowering
        (ShorLoweringCleanState
          qs x data work)
        U2 hworkspace.2.1 ψ1 :=
    lowered_initY1_ready_and_full_clean
      qs lowering x data work
      hsetup.exponent_data_disjoint
      hsetup.circuit_workspace
      hworkspace.2.1
      ψ1
      h1.2

  let ψ3 :=
    LowerGateClass.evalL
      (qs := qs)
      (lowerGate
        (Basis := qs.Basis)
        lowering.k lowering.hk lowering.ops
        U3 hworkspace.2.2.1)
      ψ2

  have h3 :
      LoweredCleanResult
        qs lowering
        (ShorLoweringCleanState
          qs x data work)
        U3 hworkspace.2.2.1 ψ2 :=
    lowered_modExpApproxStepsValid_ready_and_clean
      lowering
      x data work
      a N flag 0
      x.active.qubits
      hsetup.circuit_workspace
      hsetup.exponent_data_disjoint
      hisolated.exponent_work_disjoint
      hisolated.flag_outside_exponent
      hLayout
      hworkspace.2.2.1
      ψ2
      h2.2

  have h4 :
      LoweredCleanResult
        qs lowering
        (ShorLoweringCleanState
          qs x data work)
        U4 hworkspace.2.2.2 ψ3 :=
    lowered_IQFT_ready_and_full_clean
      qs lowering x data work
      hsetup.exponent_data_disjoint
      hisolated.exponent_work_disjoint
      hworkspace.2.2.2
      ψ3
      h3.2

  have h34 :
      LoweredCleanResult
        qs lowering
        (ShorLoweringCleanState
          qs x data work)
        (U3 ;; U4)
        hworkspace34
        ψ2 :=
    LoweredCleanResult.seq
      hworkspace34
      ψ2
      h3
      h4

  have h234 :
      LoweredCleanResult
        qs lowering
        (ShorLoweringCleanState
          qs x data work)
        (U2 ;; U3 ;; U4)
        hworkspace234
        ψ1 :=
    LoweredCleanResult.seq
      hworkspace234
      ψ1
      h2
      h34

  have h1234 :
      LoweredCleanResult
        qs lowering
        (ShorLoweringCleanState
          qs x data work)
        (U1 ;; U2 ;; U3 ;; U4)
        hworkspace1234
        ψ :=
    LoweredCleanResult.seq
      hworkspace1234
      ψ
      h1
      h234

  simpa [
    U1,
    U2,
    U3,
    U4,
    orderFindingApprox,
    modExpApproxValid
  ] using h1234

/--
Main public clean-workspace theorem for the raw setup arguments.

Starting from an initially clean basis state, the full approximate order-finding
gate has clean local workspace everywhere the lowering procedure needs it.
-/
theorem gateWorkspaceCleanState_orderFindingApprox
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGateGateBridge qs]
    [ModMulPrimitiveGateSemantics qs]
    (lowering : ShorLoweringSetup)
    (η : ℝ)
    (a N : ℕ)
    (x data work : ExtReg)
    (flag : ℕ)
    (b0 : qs.Basis)
    (hsetup :
      ShorApproxSetup
        qs η x data work flag b0)
    (hlarge :
      ShorWorkspaceLargeEnough
        lowering.ops x data work)
    (hisolated :
      ShorWorkspaceIsolation x work flag)
    (hzero :
      ShorWorkspaceCleanInput
        x data work b0) :
    let hworkspace :=
      gateWorkspaceOK_orderFindingApprox
        (ops := lowering.ops)
        (η := η)
        (a := a)
        (N := N)
        (x := x)
        (data := data)
        (work := work)
        (flag := flag)
        (b0 := b0)
        hsetup
        hlarge

    GateWorkspaceCleanState
      qs
      lowering.k
      lowering.hk
      lowering.ops
      (orderFindingApprox
        qs a N x data work flag
        hsetup.circuit_workspace)
      hworkspace
      (qs.ket b0) := by
  let hworkspace :=
    gateWorkspaceOK_orderFindingApprox
      (ops := lowering.ops)
      (η := η)
      (a := a)
      (N := N)
      (x := x)
      (data := data)
      (work := work)
      (flag := flag)
      (b0 := b0)
      hsetup
      hlarge

  have hLayoutOfMem :
      ∀ ctrl ∈ x.active.qubits,
        ModMulCoreLayout
          data work flag ctrl := by
    intro ctrl hctrl

    rcases List.get_of_mem hctrl with
      ⟨j, hj⟩

    let i : Fin (regSize x.active) :=
      ⟨j.1, by
        simp [regSize, Reg.width]⟩

    have hget :
        x.active.get i = ctrl := by
      dsimp [i, Reg.get]
      simpa [regSize, Reg.width] using hj

    have hi :=
      hsetup.register_layout i

    simpa only [hget] using hi

  have hInitial :
      ShorLoweringCleanState
        qs x data work
        (qs.ket b0) :=
    shorLoweringCleanState_ket hzero

  have hResult :
      LoweredCleanResult
        qs
        lowering
        (ShorLoweringCleanState
          qs x data work)
        (orderFindingApprox
          qs a N x data work flag
          hsetup.circuit_workspace)
        hworkspace
        (qs.ket b0) := by
    -- Compose:
    --
    --   H_reg x.active
    --   initY1 data.active
    --   modExpApproxValid
    --   IQFT x
    --
    -- using the six non-primitive helper lemmas and
    -- `lowered_modExpApproxStepsValid_ready_and_clean`.
    exact
      lowered_orderFindingApprox_ready_and_full_clean
        lowering
        η
        a N
        x data work
        flag b0
        hsetup
        hlarge
        hisolated
        hworkspace
        hInitial
        hLayoutOfMem

  exact hResult.1


/-! =========================================================
    Section 13: Public final wrappers
========================================================= -/

/--
Static workspace theorem exposed through `LoweredShorReady`.
-/
theorem LoweredShorReady.workspace
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGateGateBridge qs]
    {lowering : ShorLoweringSetup}
    {η : ℝ}
    {a N : ℕ}
    {x y work : ExtReg}
    {flag : ℕ}
    {b0 : qs.Basis}
    (h :
      LoweredShorReady
        qs lowering η a N x y work flag b0) :
    GateWorkspaceOK lowering.ops
      (orderFindingApprox
        qs a N x y work flag
        (ShorApproxSetupMinimal.toShorApproxSetup h.approx).circuit_workspace) := by
  exact
    gateWorkspaceOK_orderFindingApprox
      (ops := lowering.ops)
      (η := η)
      (a := a)
      (N := N)
      (x := x)
      (data := y)
      (work := work)
      (flag := flag)
      (b0 := b0)
      (ShorApproxSetupMinimal.toShorApproxSetup h.approx)
      h.workspace_large_enough

/--
Final theorem of the workspace directory.

For a packaged `LoweredShorReady` assumption, the lowered approximate
order-finding circuit satisfies the dynamic `GateWorkspaceCleanState`
precondition needed by `lowerGate_correctness`.
-/
theorem LoweredShorReady.workspace_clean
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGateGateBridge qs]
    [ModMulPrimitiveGateSemantics qs]
    {lowering : ShorLoweringSetup}
    {η : ℝ}
    {a N : ℕ}
    {x y work : ExtReg}
    {flag : ℕ}
    {b0 : qs.Basis}
    (h :
      LoweredShorReady
        qs lowering η a N x y work flag b0) :
    GateWorkspaceCleanState
      qs
      lowering.k
      lowering.hk
      lowering.ops
      (orderFindingApprox
        qs a N x y work flag
        (ShorApproxSetupMinimal.toShorApproxSetup h.approx).circuit_workspace)
      h.workspace
      (qs.ket b0) := by
  exact
    gateWorkspaceCleanState_orderFindingApprox
      lowering
      η
      a
      N
      x
      y
      work
      flag
      b0
      (ShorApproxSetupMinimal.toShorApproxSetup h.approx)
      h.workspace_large_enough
      h.workspace_isolated
      h.workspace_initially_zero


end Shor
