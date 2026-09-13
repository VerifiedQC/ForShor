import FastMultiplication.ShorVerification.Implementation.Shor.Circuit.Workspace
import FastMultiplication.ShorVerification.Implementation.Shor.Circuit.OrderFinding
import FastMultiplication.ShorVerification.Implementation.Shor.Spec.Setup
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Budgets
import FastMultiplication.ShorVerification.Implementation.Compilation.Correctness
import FastMultiplication.ShorVerification.Implementation.QFT.Proofs.Lowering.Readiness
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Proofs.Core
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Proofs.ConstArithmetic
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Proofs.Algorithm1Expansion
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.Workspace
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.Steps
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.ModExp
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.CmpLtNW
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Lowering.ConstArithmetic
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Spec.Validity
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Workspace
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Gates.Macros
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Spec.Cleanliness
import FastMultiplication.ShorVerification.Implementation.Semantics.GateSemanticsLemmas
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.MacroSemantics
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Static Workspace Readiness

The public static readiness theorem `gateWorkspaceOK_orderFindingApprox`,
which expands the public Shor reserve budget (`ShorWorkspaceLargeEnough`)
into the per-stage `GateWorkspaceOK` facts required by lowering the full
approximate order-finding circuit, and its packaged form
`LoweredShorReady.workspace`.
-/

namespace Shor
open Gate
open Classical

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


private theorem constArithmeticWorkspace_of_cmpLtNWWorkspace
    (N : ℕ)
    (dataCarry work scratch : ExtReg)
    (flag : ℕ)
    (hstep4 :
      CmpLtNWWorkspace N dataCarry work scratch flag) :
    ConstArithmeticWorkspace N dataCarry scratch flag := by
  have hscratchWidth :
      scratch.width = cmpLtNWWidth N dataCarry.active work.active := by
    simpa [ExtReg.width] using hstep4.scratch_width
  have hscratchPositive : 0 < scratch.width := by
    rw [hscratchWidth]
    unfold cmpLtNWWidth
    omega
  have hmaxLeft :
      regSize dataCarry.active + regSize work.active ≤
        max
          (regSize dataCarry.active + regSize work.active)
          (Nat.log2 (N + 1) + 1 + regSize work.active) :=
    Nat.le_max_left _ _
  have hmaxRight :
      Nat.log2 (N + 1) + 1 + regSize work.active ≤
        max
          (regSize dataCarry.active + regSize work.active)
          (Nat.log2 (N + 1) + 1 + regSize work.active) :=
    Nat.le_max_right _ _
  refine
    {
      data_can_grow := hstep4.data_can_grow
      scratch_can_grow := ?_
      data_scratch_disjoint := hstep4.data_scratch_disjoint
      flag_not_data := hstep4.flag_not_data
      flag_not_scratch := hstep4.flag_not_scratch
      scratch_positive := hscratchPositive
      constant_fits := ?_
      data_width_fits := ?_
    }
  · change 1 ≤ regSize scratch.reserve
    rw [← hstep4.mul_zReserve_eq]
    exact hstep4.mulWorkspace.z_can_grow
  · have hlogWidth :
        Nat.log2 (N + 1) + 1 ≤ scratch.width - 1 := by
      rw [hscratchWidth]
      unfold cmpLtNWWidth
      omega
    have hN : N < 2 ^ (Nat.log2 (N + 1) + 1) := by
      exact lt_trans (Nat.lt_succ_self N) (Nat.lt_log2_self)
    exact
      lt_of_lt_of_le hN
        (Nat.pow_le_pow_right (by omega) hlogWidth)
  · rw [hscratchWidth]
    unfold cmpLtNWWidth
    simpa [ExtReg.width] using (show
      regSize dataCarry.active ≤
        2 + max
          (regSize dataCarry.active + regSize work.active)
          (Nat.log2 (N + 1) + 1 + regSize work.active) - 1 by
      omega)

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
    (x data work scratch : ExtReg)
    (flag : ℕ)
    (b0 : qs.Basis)
    (hsetup :
      ShorApproxSetup
        qs η N x data work scratch flag b0)
    (hlarge :
      ShorWorkspaceLargeEnough
        ops x data work scratch) :
    GateWorkspaceOK ops
      (orderFindingApprox a N x data work scratch flag
        hsetup.circuit_workspace hsetup.step4_workspace) := by
  let hmod : ModMulCircuitWorkspaceOK data work :=
    hsetup.circuit_workspace
  let hstep4 : CmpLtNWWorkspace N (data.grow 1) work scratch flag :=
    hsetup.step4_workspace
  have hConst :
      ConstArithmeticWorkspace N (data.grow 1) scratch flag :=
    constArithmeticWorkspace_of_cmpLtNWWorkspace
      N (data.grow 1) work scratch flag hstep4

  have hDataGrow : data.CanGrow 1 :=
    hmod.data_canGrow_one
  have hDataCarryGrow : (data.grow 1).CanGrow 1 :=
    hmod.dataCarry_canGrow_one
  have hWorkGrow : work.CanGrow 1 :=
    hmod.work_canGrow_one

  have hDataBounds := hlarge.data_large_enough
  have hWorkBounds := hlarge.auxiliary_large_enough
  have hScratchBounds := hlarge.scratch_large_enough
  dsimp [shorWorkspaceNeed] at hDataBounds hWorkBounds hScratchBounds
  simp only [max_le_iff] at hDataBounds hWorkBounds hScratchBounds
  rcases hDataBounds with
    ⟨hDataStep1, hDataQFT, hDataStep2, hDataStep5⟩
  rcases hWorkBounds with
    ⟨hWorkQFT, hWorkStep1, hWorkStep2, hWorkStep4, hWorkStep5⟩
  rcases hScratchBounds with
    ⟨hScratchQFT, hScratchStep4⟩

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
  have hStep4XExt : hstep4.mulWorkspace.xExt = work := by
    rw [
      Gate.PhaseProdWorkspace.xExt,
      ExtReg.withReserve,
      ExtReg.mk.injEq
    ]
    exact ⟨rfl, hstep4.mul_xReserve_eq⟩
  have hStep4ZExt : hstep4.mulWorkspace.zExt = scratch := by
    rw [
      Gate.PhaseProdWorkspace.zExt,
      ExtReg.withReserve,
      ExtReg.mk.injEq
    ]
    exact ⟨rfl, hstep4.mul_zReserve_eq⟩

  have hQFTScratch : QFTReserveOK ops scratch := by
    refine ⟨?_⟩
    simpa [qftReserveNeed] using hScratchQFT

  have hStep4Phase :
      SignedRecursiveWorkspaceOK
        ops
        (hstep4.mulWorkspace.xExt.grow 1)
        (hstep4.mulWorkspace.zExt.grow 1) := by
    rw [hStep4XExt, hStep4ZExt]
    refine
      {
        owned_disjoint := ?_
        x_reserve_sufficient := ?_
        z_reserve_sufficient := ?_
      }
    · simpa [
          ExtReg.OwnedDisjoint,
          ExtReg.ownedQubits_grow
        ] using hstep4.work_scratch_disjoint
    · rw [
          ExtReg.width_grow work 1 hWorkGrow,
          ExtReg.width_grow scratch 1
            (constArithmeticWorkspace_of_cmpLtNWWorkspace
              N (data.grow 1) work scratch flag hstep4).scratch_can_grow,
          ExtReg.capacity_grow work 1 hWorkGrow
        ]
      exact reserve_le_capacity_sub_one_of_succ_le hWorkStep4
    · rw [
          ExtReg.width_grow work 1 hWorkGrow,
          ExtReg.width_grow scratch 1
            (constArithmeticWorkspace_of_cmpLtNWWorkspace
              N (data.grow 1) work scratch flag hstep4).scratch_can_grow,
          ExtReg.capacity_grow scratch 1
            (constArithmeticWorkspace_of_cmpLtNWWorkspace
              N (data.grow 1) work scratch flag hstep4).scratch_can_grow
        ]
      exact reserve_le_capacity_sub_one_of_succ_le hScratchStep4

  have hStep4QFT :
      QFTReserveOK ops hstep4.mulWorkspace.zExt := by
    simpa only [hStep4ZExt] using hQFTScratch

  have hStep4OK :
      GateWorkspaceOK ops
        (step4 N (data.grow 1) work scratch flag hstep4) := by
    unfold step4 cmpLtNW fastConstMulInto cmpLtNWDifference
    simp [
      Gate.PhaseProdUsing,
      GateWorkspaceOK,
      hStep4Phase,
      hStep4QFT
    ]

  have hHWork : GateWorkspaceOK ops (H_reg work.active) :=
    gateWorkspaceOK_H_reg ops work.active

  have hCore :
      ∀ (c ctrl : ℕ),
        ModMulCoreLayout data work flag ctrl →
        GateWorkspaceOK ops
          (CmodMulInPlaceCore
            c N ctrl data work scratch flag hmod hstep4) := by
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
      GateWorkspaceOK,
      hConst,
      hStep4OK,
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
            a N data work scratch flag hmod hstep4 e ctrls) := by
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
          a N x.active data work scratch flag hmod hstep4) :=
    hSteps 0 x.active.qubits hLayoutOfMem

  have hFinalQFT :
      GateWorkspaceOK ops (IQFT x) := by
    simpa [IQFT, GateWorkspaceOK] using hQFTX

  have hAll :
      GateWorkspaceOK ops (H_reg x.active) ∧
      GateWorkspaceOK ops (initY1 data.active) ∧
      GateWorkspaceOK ops
        (modExpApproxValid
          a N x.active data work scratch flag hmod hstep4) ∧
      GateWorkspaceOK ops (IQFT x) :=
    ⟨hHExponent, hInit, hModExp, hFinalQFT⟩

  simpa [orderFindingApprox, GateWorkspaceOK, hmod, hstep4] using hAll


/--
Static workspace theorem exposed through `LoweredShorReady`.
-/
theorem LoweredShorReady.workspace
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    {lowering : ShorLoweringSetup}
    {η : ℝ}
    {a N : ℕ}
    {x y work scratch : ExtReg}
    {flag : ℕ}
    {b0 : qs.Basis}
    (h :
      LoweredShorReady
        qs lowering η a N x y work scratch flag b0) :
    GateWorkspaceOK lowering.ops
      (orderFindingApprox a N x y work scratch flag
        (ShorApproxSetupMinimal.toShorApproxSetup h.approx).circuit_workspace
        (ShorApproxSetupMinimal.toShorApproxSetup h.approx).step4_workspace) := by
  exact
    gateWorkspaceOK_orderFindingApprox
      (ops := lowering.ops)
      (η := η)
      (a := a)
      (N := N)
      (x := x)
      (data := y)
      (work := work)
      (scratch := scratch)
      (flag := flag)
      (b0 := b0)
      (ShorApproxSetupMinimal.toShorApproxSetup h.approx)
      h.workspace_large_enough

end Shor
